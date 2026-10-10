import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.Movement
noncomputable section
open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

lemma eigenvalue_le_weighted (A : Mat n) (hA : ∀ i j, 0 ≤ A i j)
    (z : Fin n → ℝ) (hz : ∀ i, 0 < z i) (q : ℝ)
    (hq : ∀ i, (A *ᵥ z) i ≤ q*z i)
    (v : Fin n → ℝ) (hv : v ≠ 0) (μ : ℝ) (hμ : A *ᵥ v = μ • v) : μ ≤ q := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by
    contrapose! hv
    ext i
    exact hv i
  have hn : (Finset.univ : Finset (Fin n)).Nonempty := ⟨j,Finset.mem_univ j⟩
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|/z i) hn
  have hm : ∀ k, |v k| ≤ (|v i|/z i)*z k := by
    intro k
    exact (div_le_iff₀ (hz k)).mp (hi k (Finset.mem_univ k))
  have hvi : 0 < |v i| := by
    have ht := hi j (Finset.mem_univ j)
    have hp : 0 < |v j|/z j := div_pos (abs_pos.mpr hj) (hz j)
    exact (div_pos_iff.mp (hp.trans_le ht)).resolve_right (by intro h; linarith [hz i]) |>.1
  have hs : |(A *ᵥ v) i| ≤ (|v i|/z i)*(A *ᵥ z) i := by
    calc
      |(A *ᵥ v) i| ≤ ∑ k, |A i k*v k| := by
        simpa only [Matrix.mulVec,dotProduct] using Finset.abs_sum_le_sum_abs (fun k => A i k*v k) Finset.univ
      _ = ∑ k, A i k*|v k| := by simp only [abs_mul,abs_of_nonneg (hA i _)]
      _ ≤ ∑ k, A i k*((|v i|/z i)*z k) := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hm k) (hA i k)
      _ = (|v i|/z i)*(A *ᵥ z) i := by
        simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have he := congrFun hμ i
  simp only [Pi.smul_apply,smul_eq_mul] at he
  rw [he,abs_mul] at hs
  have hfinal := hs.trans (mul_le_mul_of_nonneg_left (hq i) (div_nonneg (abs_nonneg _) (hz i).le))
  have hcancel : (|v i|/z i)*(q*z i) = q*|v i| := by field_simp [(hz i).ne']
  rw [hcancel] at hfinal
  nlinarith [le_abs_self μ]

lemma product_weighted_bound (A B : Mat n) (hA : ∀ i j, 0 ≤ A i j)
    (z w : Fin n → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (ha : ∀ i, (A *ᵥ w) i ≤ q*z i) (hb : ∀ i, (B *ᵥ z) i ≤ q*w i) (i : Fin n) :
    ((A*B) *ᵥ z) i ≤ q^2*z i := by
  rw [← Matrix.mulVec_mulVec]
  calc
    (A *ᵥ (B *ᵥ z)) i ≤ (A *ᵥ (q • w)) i := by
      change (∑ j, A i j*(B *ᵥ z) j) ≤ ∑ j, A i j*(q*w j)
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hb j) (hA i j)
    _ = q*(A *ᵥ w) i := by simp only [Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul]
    _ ≤ q*(q*z i) := mul_le_mul_of_nonneg_left (ha i) hq
    _ = q^2*z i := by ring

lemma sqrt_product_posSemidef (A B : Mat n) (hB : B.PosSemidef) :
    (CFC.sqrt A*B*CFC.sqrt A).PosSemidef := by
  have hh := hB.conjTranspose_mul_mul_same (CFC.sqrt A)
  simpa only [(CFC.sqrt_nonneg A).posSemidef.isHermitian.eq] using hh

lemma sqrt_product_eigen_bound (A B : Mat n) (hA : A.PosSemidef)
    (hAB : ∀ i j, 0 ≤ (A*B) i j)
    (z : Fin n → ℝ) (hz : ∀ i, 0 < z i) (q : ℝ) (hq : 0 ≤ q)
    (hbound : ∀ i, ((A*B) *ᵥ z) i ≤ q*z i)
    (v : Fin n → ℝ) (hv : v ≠ 0) (μ : ℝ)
    (he : (CFC.sqrt A*B*CFC.sqrt A) *ᵥ v = μ • v) : μ ≤ q := by
  by_cases hm : μ ≤ 0
  · exact hm.trans hq
  have hm' : μ ≠ 0 := ne_of_gt (lt_of_not_ge hm)
  let u := CFC.sqrt A *ᵥ v
  have hu : u ≠ 0 := by
    intro hu
    have hz' : (CFC.sqrt A*B*CFC.sqrt A) *ᵥ v = 0 := by
      rw [← Matrix.mulVec_mulVec,show CFC.sqrt A *ᵥ v = 0 from hu]
      simp
    rw [he] at hz'
    exact hv ((smul_eq_zero.mp hz').resolve_left hm')
  have hue : (A*B) *ᵥ u = μ • u := by
    have hh := congrArg (fun w => CFC.sqrt A *ᵥ w) he
    try dsimp only at hh
    rw [Matrix.mulVec_smul] at hh
    dsimp [u]
    convert hh using 1
    simp only [Matrix.mulVec_mulVec,mul_assoc]
    rw [← mul_assoc (CFC.sqrt A),CFC.sqrt_mul_sqrt_self A hA.nonneg]
  exact eigenvalue_le_weighted (A*B) hAB z hz q hbound u hu μ hue

lemma sqrt_product_norm_bound (A B : Mat n) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : ∀ i j, 0 ≤ (A*B) i j)
    (z : Fin n → ℝ) (hz : ∀ i, 0 < z i) (q : ℝ) (hq : 0 ≤ q)
    (hbound : ∀ i, ((A*B) *ᵥ z) i ≤ q*z i) :
    ‖CFC.sqrt A*B*CFC.sqrt A‖ ≤ q := by
  let C := CFC.sqrt A*B*CFC.sqrt A
  have hc : C.PosSemidef := sqrt_product_posSemidef A B hB
  have heig : ∀ i, ‖hc.isHermitian.eigenvalues i‖ ≤ q := by
    intro i
    rw [Real.norm_eq_abs,abs_of_nonneg (hc.eigenvalues_nonneg i)]
    apply sqrt_product_eigen_bound A B hA hAB z hz q hq hbound
      (hc.isHermitian.eigenvectorBasis i) ?_ _ (hc.isHermitian.mulVec_eigenvectorBasis i)
    exact (ofLp_eq_zero 2).ne.2 (hc.isHermitian.eigenvectorBasis.orthonormal.ne_zero i)
  have hdiag : ‖(Matrix.diagonal (hc.isHermitian.eigenvalues) : Mat n)‖ ≤ q := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hq).mpr heig
  calc
    ‖C‖ = ‖(Matrix.diagonal (hc.isHermitian.eigenvalues) : Mat n)‖ := by
      conv_lhs => rw [hc.isHermitian.spectral_theorem]
      simp only [Unitary.conjStarAlgAut_apply]
      rw [mul_assoc,CStarRing.norm_coe_unitary_mul,← Unitary.coe_star,CStarRing.norm_mul_coe_unitary]
      rfl
    _ ≤ q := hdiag

end
end CurrentKS.Movement

end OAI
