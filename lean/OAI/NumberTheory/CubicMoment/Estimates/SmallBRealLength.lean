import OAI.NumberTheory.CubicMoment.Estimates.CommonHeightCoefficient

namespace OAI

/-! Integer norms permit an exact floor cutoff after division by a
common factor. No rounding error is added to the coefficient support. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem smallB_coprime_height_real
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (v : Eisenstein → ℂ)
      (Z A T u : ℝ), 4 ≤ (⌊Z⌋₊:ℝ) → 16 ≤ (⌊Z⌋₊:ℝ)^(3/4:ℝ) →
      Z^(1/50:ℝ) ≤ T → Z^(3/2:ℝ) ≤ A →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t =>
        ‖coprimeGramForm S (fun b => v b*star (normTwist (u+t) b)) V A‖) T ≤
        K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ)*∑ b ∈ S, ‖v b‖^2 := by
  obtain ⟨K,hK,hbound⟩ := smallB_coprime_dispersion_height_power hMV hC hHuxley V hV hV'
  refine ⟨K,hK,?_⟩
  intro S v Z A T u hZ hlarge hT hA hS
  have hZ₀ : 0 ≤ Z := by
    by_contra h
    have hf : ⌊Z⌋₊ = 0 := Nat.floor_of_nonpos (le_of_not_ge h)
    simp only [hf,Nat.cast_zero] at hZ
    linarith
  have hf : (⌊Z⌋₊:ℝ) ≤ Z := Nat.floor_le hZ₀
  have hA₀ : 0 ≤ A := (Real.rpow_nonneg hZ₀ _).trans hA
  have hS' : ∀ b ∈ S, primary b ∧ Squarefree b ∧
      (⌊Z⌋₊:ℝ)/2 ≤ norm b ∧ norm b ≤ (⌊Z⌋₊:ℝ) := by
    intro b hb
    refine ⟨(hS b hb).1,(hS b hb).2.1,?_,?_⟩
    · linarith [(hS b hb).2.2.1]
    · have hh : normNat b ≤ ⌊Z⌋₊ := Nat.le_floor (by
        rw [normNat_cast]
        exact (hS b hb).2.2.2)
      have hr : (normNat b : ℝ) ≤ (⌊Z⌋₊:ℝ) := by exact_mod_cast hh
      rwa [normNat_cast] at hr
  have hh := hbound S (gramUntwist v) ⌊Z⌋₊ A T u hZ hlarge
    ((Real.rpow_le_rpow (by positivity) hf (by norm_num)).trans hT)
    ((Real.rpow_le_rpow (by positivity) hf (by norm_num)).trans hA) hS'
  have he (t : ℝ) := coprimeGramForm_height_eq S
    (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩) v (u+t) V A
  simp_rw [← he] at hh
  have henergy : (∑ b ∈ S, ‖gramUntwist v b‖^2) = ∑ b ∈ S, ‖v b‖^2 := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [gramUntwist_norm (hS b hb).1 (hS b hb).2.1]
  rw [henergy] at hh
  exact hh.trans (by
    gcongr)

end CubicFirstMoment

end

end OAI
