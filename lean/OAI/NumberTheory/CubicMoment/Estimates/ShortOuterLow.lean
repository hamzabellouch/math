import OAI.NumberTheory.CubicMoment.Estimates.TypeIProductFourier
import OAI.NumberTheory.CubicMoment.Estimates.TypeIMixedDyads
import OAI.NumberTheory.CubicMoment.Estimates.GeometricPrimeBins

namespace OAI

/-! Sum all short outer norm dyads in the central corrected kernel.
The dyad count costs one logarithm, and all weights and support are actual. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def shortOuterCount (Y : ℝ) : ℕ := geometricBinCount 2 (2*Y)

lemma shortOuterCount_covers {Y : ℝ} (hY : 0 < Y) : Y < (2:ℝ)^shortOuterCount Y := by
  have hl : Real.log (2*Y) ≤ Real.log ((2:ℝ)^shortOuterCount Y) := by
    rw [Real.log_pow]
    exact (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp (Nat.le_ceil _)
  have hh := (Real.log_le_log_iff (by positivity : 0 < 2*Y) (by positivity)).mp hl
  linarith

lemma shortOuterCount_scale {Y : ℝ} (hY : 0 < Y) {j : ℕ} (hj : j < shortOuterCount Y) :
    (2:ℝ)^j < 2*Y := by
  have hj' : (j:ℝ) < Real.log (2*Y)/Real.log 2 := Nat.lt_ceil.mp hj
  apply (Real.log_lt_log_iff (by positivity : (0:ℝ) < 2^j) (by positivity)).mp
  rw [Real.log_pow]
  exact (lt_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp hj'

theorem shortOuterCount_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y → (shortOuterCount Y:ℝ) ≤ C*(1+Real.log Y) := by
  obtain ⟨C,hC,hbound⟩ := geometricBinCount_log_bound (by norm_num : (1:ℝ) < 2)
  refine ⟨C*(1+Real.log 2),by positivity,?_⟩
  intro Y hY
  apply (hbound (2*Y) (by linarith)).trans
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by linarith : Y ≠ 0)]
  have hlog := Real.log_nonneg hY
  have htwo := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  calc
    C*(1+(Real.log 2+Real.log Y)) ≤ C*((1+Real.log 2)*(1+Real.log Y)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg htwo hlog]) hC.le
    _ = _ := by ring

theorem short_outer_low_bound
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {A : ℝ} (hA : 0 ≤ A) (k Ct : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X Y H X₀ : ℝ),
      2 ≤ X → 1 ≤ Real.log X → Real.exp hW.radius ≤ X →
      1 ≤ Y → 2*Y ≤ X^(51/100:ℝ) → 0 < H →
      (∀ r ∈ S, primary r) →
      (∀ r ∈ S, α r ≠ 0 → norm r ≤ Y) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      ‖∑ r ∈ S, α r*∑ u ∈ primaryElementBall (Real.exp hW.radius*X),
        if r*u ∈ squarefreeProductEnvelope (Real.exp hW.radius*X) then
          centeredHeightKernel ℓ (W (w r)) H ((1+Real.log X)^Ct) X X₀ (r*u) else 0‖ ≤
        K*(1+Real.log Y)*(1+Real.log X)^Ct*X^(5/6-1/100:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := typeI_product_low_integral hV hW ℓ hGamma hA k Ct
  obtain ⟨C,hC,hcount⟩ := shortOuterCount_log_bound
  refine ⟨C*K,by positivity,?_⟩
  intro w S α X Y H X₀ hX hlog hBX hY hYX hH hS hsize hα
  have hXp : 0 < X := by linarith
  have hL : 0 < 1+Real.log X := by linarith
  let S' := S.filter (fun r => α r ≠ 0)
  let F : Eisenstein → ℂ := fun r => α r*∑ u ∈ primaryElementBall (Real.exp hW.radius*X),
    if r*u ∈ squarefreeProductEnvelope (Real.exp hW.radius*X) then
      centeredHeightKernel ℓ (W (w r)) H ((1+Real.log X)^Ct) X X₀ (r*u) else 0
  have hre : (∑ r ∈ S, F r) = ∑ r ∈ S', F r := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : α r = 0 <;> simp [hr,F]
  have hS' (r : Eisenstein) (hr : r ∈ S') : primary r ∧ 1 ≤ norm r ∧ norm r ≤ Y := by
    obtain ⟨hr,hne⟩ := Finset.mem_filter.mp hr
    exact ⟨hS r hr,one_le_norm (primary_ne_zero (hS r hr)),hsize r hr hne⟩
  have hpart := typeIMixedDyad_partition S' (show (0:ℝ) < 1 by norm_num)
    (shortOuterCount_covers (zero_lt_one.trans_le hY))
    (fun r hr => by simpa only [one_mul,mul_one] using (hS' r hr).2) F
  change ‖∑ r ∈ S, F r‖ ≤ _
  rw [hre,hpart]
  calc
    _ ≤ ∑ j ∈ Finset.range (shortOuterCount Y), ‖∑ r ∈ typeIMixedDyad S' 1 j, F r‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (shortOuterCount Y), K*(1+Real.log X)^Ct*X^(5/6-1/100:ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      let R : ℝ := 2^j
      let U : ℝ := X/R
      let P := typeIMixedDyad S' 1 j
      have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
      have hRp : 0 < R := zero_lt_one.trans_le hR
      have hRhi : R ≤ X^(51/100:ℝ) :=
        (shortOuterCount_scale (zero_lt_one.trans_le hY) (Finset.mem_range.mp hj)).le.trans hYX
      have hRX : R ≤ X := hRhi.trans (by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
          (show (1:ℝ) ≤ X by linarith) (by norm_num : (51/100:ℝ) ≤ 1))
      have hU : 1 ≤ U := (le_div_iff₀ hRp).mpr (by simpa using hRX)
      have hRU : R*U = X := by dsimp [U]; field_simp
      have hP (r : Eisenstein) (hr : r ∈ P) : primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R := by
        obtain ⟨hrS,hrj⟩ := Finset.mem_filter.mp hr
        have hn := typeIMixedDyadIndex_bounds (show (0:ℝ) < 1 by norm_num) (hS' r hrS).2.1
        rw [hrj] at hn
        exact ⟨(hS' r hrS).1,by simpa only [one_mul] using hn.1,
          by simpa only [one_mul] using hn.2.le⟩
      have he : (∑ r ∈ P, F r) = productTypeILowIntegral w P α W ℓ
          (Real.exp hW.radius) X U H ((1+Real.log X)^Ct) X₀ := by
        rw [productTypeILowIntegral_fourier w P α W ℓ _ _ _ _ _ hH]
        apply Finset.sum_congr rfl
        intro r hr
        dsimp only [F]
        congr 1
        exact typeI_height_envelope_row ℓ (W (w r)) (Real.exp_pos _).le hR
          (zero_lt_one.trans_le hU) hRU (hW.upper_support (w r)) _ _ _ (hP r hr).1 (hP r hr).2.1
      rw [he]
      exact hbound w P α X R U H X₀ hX hlog hBX hR hU hRU hRhi hP
        (fun r hr => hα r (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1)
    _ = (shortOuterCount Y:ℝ)*(K*(1+Real.log X)^Ct*X^(5/6-1/100:ℝ)) := by simp
    _ ≤ (C*(1+Real.log Y))*(K*(1+Real.log X)^Ct*X^(5/6-1/100:ℝ)) :=
      mul_le_mul_of_nonneg_right (hcount Y hY) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
