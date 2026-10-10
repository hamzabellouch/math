import OAI.Analysis.KadisonKastler.BaireMeasureSection
import OAI.Analysis.KadisonKastler.PublishedBorelSelection

namespace OAI

/-! # Finite-measure unitary selection

The Borel relation is an analytic image of Baire space. Measurable prefix hulls
construct a section of its first coordinate for the given finite measure.
This is the finite-measure consequence of Kechris,
*Classical Descriptive Set Theory*, Theorems 18.1 and 21.10.
-/

namespace KadisonKastler

open MeasureTheory Set TopologicalSpace
open scoped Topology

noncomputable section

universe u v

theorem exists_finite_borel_selector
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    {Y : Type v} [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [Nonempty Y]
    (μ : Measure X) [IsFiniteMeasure μ] (R : Set (X × Y))
    (hR : MeasurableSet R) (hsec : ∀ᵐ x ∂μ, ∃ y, (x, y) ∈ R) :
    ∃ f : X → Y, AEMeasurable f μ ∧ ∀ᵐ x ∂μ, (x, f x) ∈ R := by
  classical
  by_cases hne : R.Nonempty
  · let := upgradeStandardBorel X
    let := TopologicalSpace.upgradeIsCompletelyMetrizable X
    have hA := hR.analyticSet
    rw [AnalyticSet] at hA
    obtain ⟨G, hG, hRange⟩ := hA.resolve_left hne.ne_empty
    have hsurj : ∀ᵐ x ∂μ, ∃ a, (G a).1 = x := by
      filter_upwards [hsec] with x hx
      obtain ⟨y, hy⟩ := hx
      have hm : (x, y) ∈ Set.range G := hRange.symm ▸ hy
      obtain ⟨a, ha⟩ := hm
      exact ⟨a, congrArg Prod.fst ha⟩
    obtain ⟨g, hg, hfg⟩ := exists_measurable_baire_section μ (fun a => (G a).1)
      (continuous_fst.comp hG) hsurj
    refine ⟨fun x => (G (g x)).2,
      ((continuous_snd.comp hG).measurable.comp hg).aemeasurable, ?_⟩
    filter_upwards [hfg] with x hx
    have hm : G (g x) ∈ R := hRange ▸ Set.mem_range_self (g x)
    have hp : (x, (G (g x)).2) = G (g x) := Prod.ext hx.symm rfl
    exact hp ▸ hm
  · refine ⟨fun _ => Classical.choice ‹Nonempty Y›, measurable_const.aemeasurable, ?_⟩
    filter_upwards [hsec] with x hx
    obtain ⟨y, hy⟩ := hx
    exact False.elim (hne ⟨(x, y), hy⟩)

/-- Finite-measure selection for a Borel relation with unitary fibers. -/
theorem publishedUnitaryBorelSelection : PublishedUnitaryBorelSelection.{u,v} := by
  intro X _ _ H _ _ _ _ _ _ ξ hξ μ _ R hR hsec
  let : PolishSpace (StrongUnitarySpace ξ) := strongUnitarySpace_polish ξ hξ
  let : Nonempty (StrongUnitarySpace ξ) := ⟨encodeStrongUnitary ξ 1⟩
  exact exists_finite_borel_selector μ R hR hsec

end

end KadisonKastler

end OAI
