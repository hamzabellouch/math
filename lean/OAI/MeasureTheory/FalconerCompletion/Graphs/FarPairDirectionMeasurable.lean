import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Graphs.EuclideanPairDirection
import OAI.MeasureTheory.FalconerCompletion.Graphs.NormIteratedFDerivSmoothStar
import OAI.MeasureTheory.FalconerCompletion.Shells.ShellEffectiveScale

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Topology ENNReal
variable {n : ℕ}

lemma actualFar_pairDirection_measurable :
    Measurable (@Attempt4FullFar.euclideanPairDirectionND n) := by
  exact (((measurable_fst.sub measurable_snd).norm).inv).smul
    (measurable_fst.sub measurable_snd)

lemma actualPairAmbientGood_radial_measurable
    (A : ℕ → ℝ) (N q a t : ℕ)
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ) :
    MeasurableSet {z | Attempt4FullFar.euclideanPairDirectionND z∈
      actualPairAmbientGood A N q a t ρ m sig C J i z} := by
  let F : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) →
      (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) × EuclideanSpace ℝ (Fin (n+1)) :=
    fun z => (z,Attempt4FullFar.euclideanPairDirectionND z)
  have hF : Measurable F := measurable_id.prodMk actualFar_pairDirection_measurable
  have hh := actualPairAmbientGood_measurable A N q a t ρ m sig C J i
  change MeasurableSet (F ⁻¹' {z | z.2∈actualPairAmbientGood A N q a t ρ m sig C J i z.1})
  exact hh.preimage hF

lemma actualFar_scale_eq (l : ℕ) (R sig : ℝ) :
    R^sig*sourceMaskScaleND l R sig = Attempt4FullFar.shellEffectiveScaleND l R sig := rfl

theorem actual_fullFar_symbol_package
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (M B total : ℕ) (hW : ∀ L∈W, L.length≤B)
    {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J)
    (Cq : ℝ) (hCq : 0≤Cq) :
    ∃ E : ℝ, 0≤E ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ],
      ∀ (A : ℕ → ℝ) (q a t : ℕ), 0<q → t≤N →
      ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (m : ℝ → ℝ) (C : ℝ) (i : ℕ)
        (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))),
      Measurable f → (∀ x, ‖f x‖≤1) →
      (∀ b∈policyDescriptorList A N q a t, L b∈W) →
      (∑ b∈policyDescriptorList A N q a t, (L b).length≤total) →
      (∀ j≤M, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
      let b := fun z => (actualPairSourceSymbol A N q a t L ρ m sig C J i f Q z).1
      let U := actualPairAmbientGood A N q a t ρ m sig C J (i+1)
      Measurable (Function.uncurry b) ∧
      MeasurableSet {z | Attempt4FullFar.euclideanPairDirectionND z∈U z} ∧
      ∀ z, ContDiff ℝ ∞ (b z) ∧ (∀ w∈U z, -w∈U z) ∧ tsupport (b z) ⊆ U z ∧
        (∀ j≤M, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b z) w‖≤
          E*(Attempt4FullFar.shellEffectiveScaleND
            ((policyDescriptorList A N q a t).sup descriptorLength) ((2:ℝ)^N) sig)^j) := by
  obtain ⟨E,hE,hder⟩ := uniform_actualPairSourceSymbol_derivatives W M B total hW sig hsig Cq hCq
  obtain ⟨N₀,hsup⟩ := uniform_actualPairSourceSymbol_support (d:=n+1) hsig hJ
  refine ⟨E,hE,?_⟩
  filter_upwards [hder,eventually_ge_atTop N₀] with N hder hN
  intro ρ hρ A q a t hq ht L m C i f Q hfm hf hL htotal hQ
  refine ⟨actualPairSourceSymbol_measurable A N q a t L ρ m sig C J i f hfm Q,
    actualPairAmbientGood_radial_measurable A N q a t ρ m sig C J (i+1),?_⟩
  intro z
  refine ⟨smoothFunctionND_contDiff _,fun w hw => actualPairAmbientGood_even A N q a t ρ m sig C J (i+1) z hw,?_,?_⟩
  · have hh := hsup N hN ρ hρ A q a t hq ht m C i L f Q 0 z
    have hz (v : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) :
        tsupport (iteratedFDeriv ℝ 0 v.1)=tsupport v.1 := by
      apply congrArg closure
      ext w
      simp only [Function.mem_support]
      rw [← norm_ne_zero_iff,norm_iteratedFDeriv_zero,norm_ne_zero_iff]
    rwa [hz] at hh
  · intro j hj w hw
    simpa only [actualFar_scale_eq] using hder A q a t hq L ρ m C J i f Q hL htotal hf hQ z j hj w hw

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
