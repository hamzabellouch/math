import OAI.NumberTheory.JointDickman.Amplification.MinorArcRate

namespace OAI

/-! # Smooth weights preserve the minor-arc partial-sum bound -/

namespace JointDickman
open Finset MeasureTheory

theorem complex_partial_summation_bound (c : ℕ → ℂ) (φ φ' : ℝ → ℂ)
    {a b D M N : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (_hD : 0 ≤ D) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hφ : ∀ t ∈ Set.Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ContinuousOn φ' (Set.Icc a b))
    (hvalue : ∀ t ∈ Set.Icc a b, ‖φ t‖ ≤ M)
    (hderiv : ∀ t ∈ Set.Icc a b, ‖φ' t‖ ≤ N)
    (hpartial : ∀ t ∈ Set.Icc a b, ‖∑ n ∈ Icc 0 ⌊t⌋₊, c n‖ ≤ D) :
    ‖∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ n*c n‖ ≤ D*(2*M+N*(b-a)) := by
  have hd : ContinuousOn (deriv φ) (Set.Icc a b) :=
    hφ'.congr (fun t ht => (hφ t ht).deriv)
  have he := sum_mul_eq_sub_sub_integral_mul (c := c) ha hab
    (fun t ht => (hφ t ht).differentiableAt) hd.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab] at he
  have hint : ‖∫ t in a..b, deriv φ t*(∑ n ∈ Icc 0 ⌊t⌋₊, c n)‖ ≤ N*D*(b-a) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun t => deriv φ t*(∑ n ∈ Icc 0 ⌊t⌋₊, c n))
      (C := N*D) (fun t ht => by
        have ht' : t ∈ Set.Icc a b := Set.uIcc_of_le hab ▸ Set.uIoc_subset_uIcc ht
        rw [(hφ t ht').deriv,norm_mul]
        exact mul_le_mul (hderiv t ht') (hpartial t ht') (norm_nonneg _) hN)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hh
  have hend (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ‖φ t*(∑ n ∈ Icc 0 ⌊t⌋₊, c n)‖ ≤ M*D := by
    rw [norm_mul]
    exact mul_le_mul (hvalue t ht) (hpartial t ht) (norm_nonneg _) hM
  rw [he]
  calc
    _ ≤ ‖φ b*(∑ n ∈ Icc 0 ⌊b⌋₊, c n)‖ +
        ‖φ a*(∑ n ∈ Icc 0 ⌊a⌋₊, c n)‖ +
        ‖∫ t in a..b, deriv φ t*(∑ n ∈ Icc 0 ⌊t⌋₊, c n)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ M*D+M*D+N*D*(b-a) :=
      add_le_add (add_le_add (hend b ⟨hab,le_rfl⟩) (hend a ⟨le_rfl,hab⟩)) hint
    _ = _ := by ring

end JointDickman

end OAI
