import OAI.Probability.BenjaminiSchramm.ExponentialDecay

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq Classical.propDecidable

theorem exists_operator_of_weighted_schur
    (U : V → V → ℝ) (w : V → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ x, 0 < w x) (hU : ∀ x y, 0 ≤ U x y)
    (hsym : ∀ x y, U x y = U y x)
    (hrow : ∀ x (s : Finset V), ∑ y ∈ s, U x y * w y / w x ≤ C) :
    ∃ A : Hilbert V →L[ℂ] Hilbert V, ‖A‖ ≤ C ∧
      ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ) := by
  have hentry (x y : V) : U x y ≤ C * w y / w x := by
    have hh := hrow y {x}
    simp only [Finset.sum_singleton, ← hsym x y] at hh
    exact (le_div_iff₀ (hw x)).mpr ((div_le_iff₀ (hw y)).mp hh)
  have hcol (y : V) (s : Finset V) : ∑ x ∈ s, U x y * w x / w y ≤ C := by
    simpa only [hsym] using hrow y s
  have hcm (y : V) : Memℓp (fun x => (U x y : ℂ)) 2 := by
    apply (memℓp_gen_iff'' (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
    refine ⟨C ^ 2, sq_nonneg _, fun s => ?_⟩
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    have hs (x : V) : U x y ^ 2 ≤ C * (U x y * w x / w y) := by
      have hh := mul_le_mul_of_nonneg_right (hentry y x) (hU x y)
      rw [hsym y x] at hh
      nlinarith [show C * w x / w y * U x y = C * (U x y * w x / w y) by ring]
    calc
      ∑ x ∈ s, U x y ^ 2 ≤ ∑ x ∈ s, C * (U x y * w x / w y) :=
        Finset.sum_le_sum (fun x _ => hs x)
      _ = C * ∑ x ∈ s, U x y * w x / w y := by rw [Finset.mul_sum]
      _ ≤ C * C := mul_le_mul_of_nonneg_left (hcol y s) hC
      _ = C ^ 2 := by ring
  let col (y : V) : Hilbert V := ⟨fun x => (U x y : ℂ), hcm y⟩
  let L : (V →₀ ℂ) →ₗ[ℂ] Hilbert V := Finsupp.linearCombination ℂ col
  have hn (f : V →₀ ℂ) : ‖L f‖ ≤ C * ‖finiteEmbedding f‖ := by
    apply lp.norm_le_of_forall_sum_le (by norm_num) (mul_nonneg hC (norm_nonneg _))
    intro s
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have hpoint (x : V) : ‖L f x‖ ^ 2 ≤
        C * ∑ y ∈ f.support, ‖f y‖ ^ 2 * (U x y * w x / w y) := by
      have hn0 : 0 ≤ ∑ y ∈ f.support, ‖f y‖ * U x y :=
        Finset.sum_nonneg fun y _ => mul_nonneg (norm_nonneg _) (hU x y)
      have hn1 : ‖L f x‖ ≤ ∑ y ∈ f.support, ‖f y‖ * U x y := by
        simp only [L, Finsupp.linearCombination_apply, Finsupp.sum, lp.coeFn_sum,
          Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro y _
        simp [col, abs_of_nonneg (hU x y)]
      have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul f.support
        (f := fun y => U x y * w y / w x)
        (g := fun y => ‖f y‖ ^ 2 * (U x y * w x / w y))
        (r := fun y => ‖f y‖ * U x y)
        (fun y _ => div_nonneg (mul_nonneg (hU x y) (hw y).le) (hw x).le)
        (fun y _ => mul_nonneg (sq_nonneg _)
          (div_nonneg (mul_nonneg (hU x y) (hw x).le) (hw y).le))
        (fun y _ => by
          apply le_of_eq
          field_simp [(hw x).ne', (hw y).ne']
          )
      exact (sq_le_sq₀ (norm_nonneg _) hn0 |>.mpr hn1).trans
        (hcs.trans (mul_le_mul_of_nonneg_right (hrow x f.support)
          (Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _)
            (div_nonneg (mul_nonneg (hU x y) (hw x).le) (hw y).le))))
    calc
      ∑ x ∈ s, ‖L f x‖ ^ 2 ≤
          ∑ x ∈ s, C * ∑ y ∈ f.support, ‖f y‖ ^ 2 * (U x y * w x / w y) :=
        Finset.sum_le_sum fun x _ => hpoint x
      _ = C * ∑ y ∈ f.support, ‖f y‖ ^ 2 * ∑ x ∈ s, U x y * w x / w y := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
      _ ≤ C * ∑ y ∈ f.support, ‖f y‖ ^ 2 * C := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul_of_nonneg_left (hcol y s) (sq_nonneg _)
      _ = C ^ 2 * ∑ y ∈ f.support, ‖finiteEmbedding f y‖ ^ 2 := by
        simp only [finiteEmbedding_apply, ← Finset.sum_mul]
        ring
      _ ≤ C ^ 2 * ‖finiteEmbedding f‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ENNReal).toReal)
            (finiteEmbedding f) f.support
      _ = (C * ‖finiteEmbedding f‖) ^ 2 := by ring
  refine ⟨L.extendOfNorm finiteEmbedding,
    LinearMap.opNorm_extendOfNorm_le finiteEmbedding_dense hC hn, ?_⟩
  intro x y
  have he := LinearMap.extendOfNorm_eq (f := L) finiteEmbedding_dense ⟨C, hn⟩
    (Finsupp.single y (1 : ℂ))
  rw [finiteEmbedding_single] at he
  rw [he]
  simp [L, col]

theorem operatorBounded_of_weighted_susceptibility
    (G : BondGraph V E) (p : unitInterval) (w : V → ℝ) (C : ℝ)
    (hw : ∀ x, 0 < w x) (hC : 0 ≤ C)
    (hrow : ∀ x (s : Finset V), ∑ y ∈ s, twoPoint G p x y * w y / w x ≤ C) :
    OperatorBounded G p := by
  obtain ⟨A, _, hA⟩ := exists_operator_of_weighted_schur (twoPoint G p) w C hC hw
    (twoPoint_nonneg G p) (twoPoint_symm G p) hrow
  exact ⟨A, hA⟩

theorem pc_lt_ptwo_of_weighted_susceptibility
    (G : BondGraph V E) (q : unitInterval) (hq : pc G < q)
    (w : V → ℝ) (C : ℝ) (hw : ∀ x, 0 < w x) (hC : 0 ≤ C)
    (hrow : ∀ x (s : Finset V), ∑ y ∈ s, twoPoint G q x y * w y / w x ≤ C) :
    pc G < ptwo G :=
  hq.trans_le (le_sSup (operatorBounded_of_weighted_susceptibility G q w C hw hC hrow))

end Percolation.BenjaminiSchramm

end OAI
