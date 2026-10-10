import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledFixedTranslation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinTranslations
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DensityOccupationError
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BasisDynkinHaar
import OAI.GroupTheory.PolycyclicRecognition.Algebra.MappedBasisBrackets

namespace OAI

/-! # Density sampling under fixed moves in actual rescaled nilpotent groups -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Module LieModule Filter
open scoped Manifold Topology

/-- A fixed right move has vanishing error in a density-weighted average,
even when the bounded observable varies with scale. The coordinate laws,
their inverses, Haar invariance and their small-move limit are all derived
from the actual exponential and the positively weighted word basis. -/
theorem model_rescaled_density_occupation_error_tendsto_zero
    {E G L I ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [LieRing L] [LieAlgebra ℝ L]
    [Fintype I] [DecidableEq I]
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (X : I → L) {k c : ℕ} (hk : lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (s : I → ℝ) (hs : ∀ i, 0 < s i)
    {l : Filter ι} [l.IsCountablyGenerated]
    (scale : ι → ℝ) (hscale : Tendsto scale l atTop)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent s w) β.val)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (v : L) (ρ : (Fin (finrank ℝ L) → ℝ) → ℝ)
    (hc : Continuous ρ) (hi : Integrable ρ volume) (hp : ∀ x, 0 ≤ ρ x)
    (f : ι → (Fin (finrank ℝ L) → ℝ) → ℝ)
    (hf : ∀ r, AEStronglyMeasurable (f r) volume)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ r x, ‖f r x‖ ≤ C) :
    let b := fun r => exponentialRescaleBasis
      (WordBasisSelections.basis X (boundedBracketWords k) β)
      (fun j => bracketWordExponent s (β.val j)) (max (scale r) 0)
    Tendsto (fun r : ι =>
      (∫ x, ρ x * f r (dynkinProduct a (basisBracket (b r)) x ((b r).equivFun v))) -
        ∫ x, ρ x * f r x) l (𝓝 0) := by
  let b := fun r => exponentialRescaleBasis
    (WordBasisSelections.basis X (boundedBracketWords k) β)
    (fun j => bracketWordExponent s (β.val j)) (max (scale r) 0)
  let Exp₀ : L → G := Exp ∘ e
  obtain ⟨⟨chart, hchart⟩, _⟩ := haar.2 Exp hExp hnil
  have hinj : Function.Injective Exp₀ := by
    intro x y h
    change Exp (e x) = Exp (e y) at h
    apply e.injective
    apply chart.injective
    change chart (e x) = chart (e y)
    rw [hchart, hchart]
    exact h
  have hzero : Exp₀ 0 = 1 := by simp [Exp₀, hExp.map_zero]
  have hneg (x : L) : Exp₀ (-x) = (Exp₀ x)⁻¹ := by
    simpa only [Exp₀, Function.comp_apply, map_neg] using hExp.map_neg (e x)
  have hadd (x : L) (t u : ℝ) :
      Exp₀ ((t + u) • x) = Exp₀ (t • x) * Exp₀ (u • x) := by
    simpa only [Exp₀, Function.comp_apply, map_smul] using hExp.map_add_smul (e x) t u
  have hm₀ (x y : L) : Exp₀ (finiteDynkinPolynomial a ![x, y]) = Exp₀ x * Exp₀ y := by
    have he := congrArg Exp (finiteDynkinPolynomial_map e.toLieHom a ![x, y])
    have hv : (fun i => e.toLieHom (![x, y] i)) = ![e x, e y] := by
      funext i
      fin_cases i <;> rfl
    rw [hv] at he
    exact he.trans (hm (e x) (e y))
  have laws (r : ι) : PolynomialGroupLaws (dynkinProduct a (basisBracket (b r))) :=
    basis_polynomialGroupLaws (b r) Exp₀ hinj hzero hneg hadd a hm₀
  let T := fun r => (dynkinRightTranslation a (basisBracket (b r)) (laws r)
    ((b r).equivFun v)).toMeasurableEquiv
  have hpres (r : ι) : MeasurePreserving (T r) volume volume := by
    have hh := measurePreserving_basis_dynkin_right haar Exp hExp hnil
      ((b r).map e.toLinearEquiv) a hm ((b r).equivFun v)
    rw [basisBracket_map_lieEquiv] at hh
    exact hh
  have hlim (x : Fin (finrank ℝ L) → ℝ) :
      Tendsto (fun r => (T r).symm x) l (𝓝 x) := by
    have hh := rescaled_fixed_translation_tendsto X hk hletters b₀ s hs β hβ
      Exp₀ hinj hzero hneg hadd a hm₀ (-v)
    have hx := ((continuous_eval_const x).tendsto (ContinuousMap.id _) |>.comp hh).comp hscale
    change Tendsto (fun r => dynkinProduct a (basisBracket (b r)) x
      (-((b r).equivFun v))) l (𝓝 x)
    change Tendsto (fun r => dynkinProduct a (basisBracket (b r)) x
      ((b r).equivFun (-v))) l (𝓝 x) at hx
    simpa only [map_neg] using hx
  exact density_occupation_error_tendsto_zero volume ρ hc hi hp T hpres hlim f hf hC hb

end PolycyclicRecognition

end

end OAI
