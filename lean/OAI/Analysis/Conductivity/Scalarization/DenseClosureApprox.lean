import Mathlib
import OAI.Analysis.Conductivity.Scalarization.FineScalarSequence

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology

lemma dense_property_in_closure
    {X : Type*} [TopologicalSpace X] (S : Set X) (P : X → Prop)
    (h : ∀ x ∈ S, ∃ z : ℕ → X, Tendsto z atTop (𝓝 x) ∧
      (∀ n, z n ∈ S) ∧ ∀ᶠ n in atTop, P (z n)) :
    Dense {x : closure S | P x.val} := by
  rw [Subtype.dense_iff]
  apply closure_minimal _ isClosed_closure
  intro x hx
  obtain ⟨z,hz,hzS,hzP⟩ := h x hx
  apply mem_closure_of_tendsto hz
  filter_upwards [hzP] with n hn
  exact ⟨⟨z n,subset_closure (hzS n)⟩,hn,rfl⟩

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal

def finiteUpdatePairs
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (U : Set Coord3) (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U)) (a b : ℝ) :
    Set (Lp FieldVector 2 (μ.restrict U) × Lp FieldVector 2 (μ.restrict U)) :=
  {Z | ∃ R : CompactGlobalUpdate μ U u A,
    μ (U \ regularRegion (fun x => u x+R.du x) R.tensor U) = 0 ∧
    (∀ᵐ x ∂μ, x ∈ U → R.tensor x ∈ matrixFiniteLaminate a b) ∧
    Z = R.fieldPair μ hE hF}

lemma finiteUpdatePairs_nonempty
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (hAm : Measurable A)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U)) {a b : ℝ}
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b) :
    (finiteUpdatePairs μ U u A hE hF a b).Nonempty := by
  refine ⟨(CompactGlobalUpdate.refl μ U u A hAm).fieldPair μ hE hF,
    CompactGlobalUpdate.refl μ U u A hAm,?_,hgraph,rfl⟩
  simpa only [CompactGlobalUpdate.refl,Pi.zero_apply,add_zero] using hreg

lemma dense_ApproxScalar_in_finiteUpdateClosure
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U)
    [IsFiniteMeasure (μ.restrict U)] [(μ.restrict U).WeaklyRegular]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0) {ε : ℝ} (hε : 0 < ε) :
    Dense {z : closure (toWeakSpace ℝ _ '' finiteUpdatePairs μ U u A hE hF a b) |
      ApproxScalar (μ.restrict U) a b ε ((toWeakSpace ℝ _).symm z.val)} := by
  apply dense_property_in_closure
  rintro _ ⟨Z,⟨R,hregR,hgraphR,rfl⟩,rfl⟩
  obtain ⟨hER,hFR⟩ := R.fields_memLp μ hUm hreg hE hF
  obtain ⟨hintR,hdivR⟩ := R.preserves_harmonic μ hint hdiv
  obtain ⟨S,hregS,hgraphS,hw,happrox⟩ := exists_fine_scalar_sequence μ ha hab hUb hUm
    (fun x => u x+R.du x) R.tensor R.measurable_tensor hER hFR hintR hdivR hregR hgraphR
  have he : ∀ n, (R.trans μ (S n)).fieldPair μ hE hF = (S n).fieldPair μ hER hFR :=
    fun n => R.fieldPair_trans μ hUm (S n) hreg hregR hE hF hER hFR
  refine ⟨fun n => toWeakSpace ℝ _ ((R.trans μ (S n)).fieldPair μ hE hF),?_,?_,?_⟩
  · simpa only [he,R.fieldPair_eq μ hUm hreg hE hF hER hFR] using hw
  · intro n
    refine ⟨_,⟨R.trans μ (S n),?_,hgraphS n,rfl⟩,rfl⟩
    simpa only [CompactGlobalUpdate.trans,Pi.add_apply,add_assoc] using hregS n
  · filter_upwards [happrox ε hε] with n hn
    change ApproxScalar (μ.restrict U) a b ε ((R.trans μ (S n)).fieldPair μ hE hF)
    rwa [he n]

theorem exact_scalar_in_finiteUpdateClosure
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U)
    [IsFiniteMeasure (μ.restrict U)] [(μ.restrict U).WeaklyRegular]
    [SeparableSpace (Lp FieldVector 2 (μ.restrict U))]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b) :
    ∃ (Z : Lp FieldVector 2 (μ.restrict U) × Lp FieldVector 2 (μ.restrict U))
      (s : Coord3 → ℝ),
      toWeakSpace ℝ _ Z ∈ closure (toWeakSpace ℝ _ '' finiteUpdatePairs μ U u A hE hF a b) ∧
      Measurable s ∧ (∀ᵐ x ∂μ.restrict U, s x ∈ Icc a b ∧ Z.2 x = s x • Z.1 x) := by
  apply exact_scalar_of_weak_density (μ.restrict U) hab.le
  · apply isCompact_weak_closure_of_pair_bounds
    rintro Z ⟨R,hregR,hgraphR,rfl⟩
    exact R.fieldPair_energy_bound μ hUm hreg hE hF hint hdiv ha hab hgraphR
  · exact ((finiteUpdatePairs_nonempty μ hAm hE hF hreg hgraph).image _).closure
  · intro ε hε
    exact dense_ApproxScalar_in_finiteUpdateClosure μ ha hab hUb hUm u A hE hF hint hdiv hreg hε

end ScalarConductivity

end
end

end OAI
