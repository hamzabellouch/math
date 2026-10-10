import OAI.MathematicalPhysics.Boltzmann.Branching.PullbackRegularLimit
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI

section

/-! # A surjective derivative admits the complementary chart used in the pullback -/

noncomputable section

open Function MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
local notation "E" => P × Q

theorem exists_complementary_chart (L : E →L[ℝ] P) (hL : Surjective L) :
    ∃ π : E →L[ℝ] Q, ∃ A : E ≃L[ℝ] E, L.prod π = A.toContinuousLinearMap := by
  classical
  obtain ⟨R,hR⟩ := L.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hL)
  have hR' (y : P) : L (R y) = y := LinearMap.congr_fun hR y
  let κ : E →ₗ[ℝ] LinearMap.ker L.toLinearMap :=
    (LinearMap.id-R.comp L.toLinearMap).codRestrict _ (fun x => by
      change L (x-R (L x)) = 0
      rw [map_sub,hR',sub_self])
  let A₀ : E ≃ₗ[ℝ] P × LinearMap.ker L.toLinearMap :=
    { L.toLinearMap.prod κ with
      invFun := fun y => R y.1+y.2
      left_inv := by
        intro x
        change R (L x)+(x-R (L x)) = x
        abel
      right_inv := by
        rintro ⟨y,z⟩
        have hz : L (z : E) = 0 := z.property
        apply Prod.ext
        · change L (R y+z) = y
          rw [map_add,hR',hz,add_zero]
        · apply Subtype.ext
          change R y+z-R (L (R y+z)) = z
          rw [map_add,hR',hz,add_zero]
          abel }
  have hdim : Module.finrank ℝ (LinearMap.ker L.toLinearMap) = Module.finrank ℝ Q := by
    have h := L.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hL,finrank_top,Module.finrank_prod] at h
    omega
  let e : LinearMap.ker L.toLinearMap ≃ₗ[ℝ] Q := LinearEquiv.ofFinrankEq _ _ hdim
  let A : E ≃L[ℝ] E :=
    (A₀.trans (LinearEquiv.prodCongr (LinearEquiv.refl ℝ P) e)).toContinuousLinearEquiv
  let π : E →L[ℝ] Q := (ContinuousLinearMap.snd ℝ P Q).comp A.toContinuousLinearMap
  refine ⟨π,A,?_⟩
  apply ContinuousLinearMap.ext
  intro x
  apply Prod.ext <;> rfl

variable
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]
  [MeasureSpace Q] [BorelSpace Q] [Measure.IsAddHaarMeasure (volume : Measure Q)]

/-- The L1 form of the manuscript's uniform pullback estimate. -/
theorem compact_surjective_pullback_zero {O K Z : Set E} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) (hZ : ((volume : Measure P).prod volume) Z = 0)
    {Φ : ℕ → E → P} {Φ' : ℕ → E → E →L[ℝ] P} {φ' : E → E →L[ℝ] P}
    (hder : ∀ n, ∀ x ∈ O, HasFDerivAt (Φ n) (Φ' n x) x)
    (hcont : ∀ x ∈ O, ContinuousAt φ' x)
    (hreg : ∀ x ∈ K \ Z, Surjective (φ' x))
    (hconv : ∀ x ∈ O, ∀ r > 0, ball x r ⊆ O →
      TendstoUniformlyOn Φ' φ' atTop (ball x r))
    {g : ℕ → P → ℝ≥0∞} {ρ : ℕ → E → ℝ≥0∞} {B M : ℝ≥0∞}
    (hB : B ≠ ∞) (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hρ : ∀ n x, x ∈ O → ρ n x ≤ B) (hgM : ∀ n y, g n y ≤ M)
    (hL : Tendsto (fun n => ∫⁻ y, g n y) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in K, ρ n x*g n (Φ n x)
      ∂((volume : Measure P).prod volume)) atTop (𝓝 0) :=
  compact_submersion_pullback_zero hO hK hKO hZ hder hcont
    (fun x hx => exists_complementary_chart (φ' x) (hreg x hx))
    hconv hB hM hg hρ hgM hL

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Null preimages on compact sets for an almost-everywhere submersion -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.GainPullback

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]
  [MeasureSpace Q] [BorelSpace Q] [Measure.IsAddHaarMeasure (volume : Measure Q)]

theorem compact_submersion_null_preimage {O K Z : Set (P × Q)}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (hZ : ((volume : Measure P).prod volume) Z = 0)
    {φ : P × Q → P} {φ' : P × Q → (P × Q) →L[ℝ] P}
    (hm : Measurable φ) (hder : ∀ x ∈ O, HasFDerivAt φ (φ' x) x)
    (hcont : ∀ x ∈ O, ContinuousAt φ' x)
    (hreg : ∀ x ∈ K \ Z, Function.Surjective (φ' x))
    {N : Set P} (hN : MeasurableSet N) (hN0 : (volume : Measure P) N = 0) :
    (((volume : Measure P).prod volume).restrict K) (φ ⁻¹' N) = 0 := by
  let g : P → ℝ≥0∞ := N.indicator (fun _ => 1)
  have hg : Measurable g := measurable_const.indicator hN
  have hg1 : ∀ y, g y ≤ 1 := by
    intro y
    exact Set.indicator_le_self' (fun _ _ => zero_le) y
  have hg0 : ∫⁻ y, g y = 0 := by
    change (∫⁻ y, N.indicator (1 : P → ℝ≥0∞) y) = 0
    rw [lintegral_indicator_one hN,hN0]
  have hconstant : ∀ x ∈ O, ∀ r > 0, Metric.ball x r ⊆ O →
      TendstoUniformlyOn (fun _ : ℕ => φ') φ' atTop (Metric.ball x r) := by
    intro x hx r hr hsub
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Filter.Eventually.of_forall (fun _ _ _ => by simpa using hε)
  have hh := compact_surjective_pullback_zero hO hK hKO hZ
    (Φ := fun _ => φ) (Φ' := fun _ => φ') (φ' := φ')
    (fun _ => hder) hcont hreg
    hconstant
    (g := fun _ => g) (ρ := fun _ _ => 1) (B := 1) (M := 1)
    (by simp) (by simp) (fun _ => hg) (fun _ _ _ => le_rfl)
    (fun _ => hg1) (by simpa only [hg0] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (𝓝 0)))
  have he : (∫⁻ x in K, g (φ x) ∂(volume : Measure P).prod volume) = 0 := by
    exact tendsto_nhds_unique tendsto_const_nhds (by simpa only [one_mul] using hh)
  have hind : (fun x => g (φ x)) = (φ ⁻¹' N).indicator (fun _ => (1:ℝ≥0∞)) := by
    funext x
    classical
    by_cases hx : φ x ∈ N <;> simp [g,hx]
  rw [hind] at he
  change (∫⁻ x, (φ ⁻¹' N).indicator (1 : P × Q → ℝ≥0∞) x
    ∂((volume : Measure P).prod volume).restrict K) = 0 at he
  rw [lintegral_indicator_one (hN.preimage hm)] at he
  exact he

end BoltzmannNonuniqueness.GainPullback

end

end

end OAI
