import OAI.Geometry.Convex.GeneralMahler.Matrix

namespace OAI
/-! Order and functional calculus for real symmetric matrices. -/
noncomputable section
open Set Filter Matrix Real
open scoped Topology ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator MatrixOrder
namespace GeneralMahler
variable {m : ℕ} {A B : Mat m}

lemma op_eigen (h : A.IsHermitian) (i : Fin m) :
    op A (h.eigenvectorBasis i) = h.eigenvalues i • (h.eigenvectorBasis i) := by
  apply WithLp.ofLp_injective
  rw [show op = _ from (rfl : op = Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)),
    Matrix.ofLp_toEuclideanCLM]
  exact h.mulVec_eigenvectorBasis i

theorem cfc_eigen' (f : ℝ → ℝ) (h : A.IsHermitian) (i : Fin m) :
    op (cfc f A) (h.eigenvectorBasis i) = (f (h.eigenvalues i)) • h.eigenvectorBasis i := by
  open Unitary in
    rw [Matrix.IsHermitian.cfc_eq h,Matrix.IsHermitian.cfc,conjStarAlgAut_apply]
    apply WithLp.ofLp_injective
    rw [show op = _ from (rfl : op = Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)),
      Matrix.ofLp_toEuclideanCLM]
    simp only [← mulVec_mulVec, h.star_eigenvectorUnitary_mulVec, Matrix.diagonal_mulVec_single,
      Function.comp_apply,mul_one]
    ext j; simp [dotProduct,mulVec, Pi.single_apply,mul_comm]

lemma neg_eigen {A : Mat m} (h : A.IsHermitian) (hn : ¬ 0 ≤ A) :
    ∃ v : Rn m, ∃ c : ℝ, c < 0 ∧ ‖v‖ = 1 ∧ op A v = c • v := by
  by_contra! hu
  apply hn; apply Matrix.PosSemidef.nonneg
  apply h.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  by_contra! he
  exact hu _ _ he (h.eigenvectorBasis.orthonormal.1 i) (op_eigen h i)

/-- Square root order, by testing an eigenvector of A-B. -/
lemma sq_order_cancel (ha : 0 ≤ A) (hb : 0 ≤ B)
    (hh : A*A ≤ B*B) : A ≤ B := by
  have ha' := ha.posSemidef
  have hb' := hb.posSemidef
  by_contra hn
  have hv : ¬ 0 ≤ B-A := by rwa [sub_nonneg]
  obtain ⟨v,c,hc,hv,he⟩ := neg_eigen (hb'.1.sub ha'.1) hv
  have hf (D : Mat m) (hd : D.IsHermitian) :
      (D*D).IsHermitian ∧ ⟪v,op (D*D) v⟫ = ‖op D v‖^2 := by
    constructor
    · change IsSelfAdjoint (D*D)
      show star (D*D)=D*D
      simp only [star_mul, (show star D = D from hd)]
    rw [_root_.map_mul,mul_apply_eq_comp, ← op_iff_hermitian.mp hd,
      real_inner_self_eq_norm_sq]
  obtain ⟨H,H'⟩ := hf _ ha'.1
  obtain ⟨G,G'⟩ := hf _ hb'.1
  have hm := (op_order_iff H G).mp hh v
  rw [H',G'] at hm
  rw [_root_.map_sub,_root_.sub_apply] at he
  have hh := (op_posSemidef_iff.mp hb').2 v
  have he : op A v = op B v + (-c) • v := by rw [neg_smul, ← he]; abel
  rw [he,norm_add_sq_real,real_inner_smul_right,real_inner_comm v,
    norm_smul,hv,Real.norm_eq_abs,abs_of_pos (neg_pos.mpr hc)] at hm
  nlinarith

lemma sqrt_monotone (ha : 0 ≤ A) (hb : 0 ≤ B) (hh:A ≤ B) :
    CFC.sqrt A ≤ CFC.sqrt B := by
  apply sq_order_cancel (CFC.sqrt_nonneg _) (CFC.sqrt_nonneg _)
  rwa [CFC.sqrt_mul_sqrt_self _ ha,CFC.sqrt_mul_sqrt_self _ hb]

variable {l r : ℝ}

abbrev scalar (m : ℕ) (l : ℝ) : Mat m := l • (1:Mat m)
lemma scalar_eq (m : ℕ) (l : ℝ) : scalar m l = algebraMap ℝ _ l := by rw [Algebra.algebraMap_eq_smul_one]
lemma scalar_sym (m : ℕ) (l : ℝ) : (scalar m l).IsHermitian :=
  isHermitian_one.smul (show IsSelfAdjoint l by simp [IsSelfAdjoint])

lemma cfc_herm (f : ℝ→ℝ) (A : Mat m) : (cfc f A).IsHermitian :=
  (cfc_predicate _ _ : IsSelfAdjoint _)

lemma scalar_cfc_order (f : ℝ→ℝ) (A : Mat m) (hA : A.IsHermitian) :
    (scalar m l ≤ cfc f A ↔ ∀ x∈spectrum ℝ A, l ≤ f x) ∧
    (cfc f A ≤ scalar m r ↔ ∀ x∈spectrum ℝ A, f x ≤ r) := by
  rw [scalar_eq,scalar_eq]
  have hi : IsSelfAdjoint A := hA
  have hf : ContinuousOn f (spectrum ℝ A) := A.finite_real_spectrum.continuousOn f
  exact ⟨algebraMap_le_cfc_iff .., cfc_le_algebraMap_iff ..⟩

lemma spectrum_order (A : Mat m) (hA:A.IsHermitian) :
    (scalar m l ≤ A ↔ ∀ x∈spectrum ℝ A, l ≤ x) ∧
    (A ≤ scalar m r ↔ ∀ x∈spectrum ℝ A, x ≤ r) := by
  have hi : IsSelfAdjoint A := hA
  have h := scalar_cfc_order (l := l) (r := r) id A hA
  rw [cfc_id ℝ A] at h
  exact h

lemma spectrum_norm_box {K : ℝ} (hk : 0 ≤ K) (ha : A.IsHermitian)
    (hb : scalar m (-K) ≤ A) (ht : A ≤ scalar m K) : ‖A‖ ≤ K := by
  have hi : IsSelfAdjoint A := ha
  conv_lhs => rw [← cfc_id ℝ A]
  apply norm_cfc_le hk
  intro x hx
  rw [Real.norm_eq_abs,abs_le]; exact ⟨(spectrum_order (l := -K) (r := K) _ ha).1.mp hb x hx,
    (spectrum_order (l := -K) (r := K) _ ha).2.mp ht x hx⟩

lemma spectrum_poly_le (f : ℝ → ℝ) {C : ℝ} {n : ℕ} (hc : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*(1+‖x‖)^n) (ha : A.IsHermitian) :
    ‖cfc f A‖ ≤ C*(1+‖A‖)^n := by
  have hi : IsSelfAdjoint A := ha
  apply norm_cfc_le (by positivity)
  intro x hx
  apply (hf _).trans
  have he := norm_apply_le_norm_cfc (id : ℝ → ℝ) A hx
  rw [cfc_id ℝ A] at he
  change ‖x‖ ≤ ‖A‖ at he
  gcongr

lemma cfc_continuous_herm (f : ℝ → ℝ) (hf : Continuous f) :
    ContinuousOn (cfc f) {x : Mat m | x.IsHermitian} :=
  (continuousOn_id.cfc_of_mem_nhdsSet (s := univ) f Filter.univ_mem
    (fun _ h => (h : IsSelfAdjoint _)) hf.continuousOn)

end GeneralMahler

end

end OAI
