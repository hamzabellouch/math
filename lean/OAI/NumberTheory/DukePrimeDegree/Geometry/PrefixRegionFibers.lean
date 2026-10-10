import OAI.NumberTheory.DukePrimeDegree.Geometry.PrefixExchangeMeasures
import OAI.NumberTheory.DukePrimeDegree.Geometry.ConjugationRestrictions

namespace OAI

/-! # Fibers of an exchanged physical rectangle -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain (insert q.root q.processed) D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

def nextTimeFiber (t : ℝ) :
    positiveRootGeneratedGroup (q.remaining.erase q.root) ≃ₜ c.Time :=
  (q.nextConjugationHomeomorph d t).trans (nextTimeCoordinates q c hf)

variable {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

lemma exchangedRectangleRegion_mem
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) (J : Set ℝ)
    (z : (UpperRootTransverse (d+1) × (T × ℝ)) × c.Time) :
    z ∈ C.exchangedRectangleRegion q g k c hf Q J ↔
      (z.1.1,z.1.2.1) ∈ Q.first ∧ z.1.2.2 ∈ J ∧
        z.2 ∈ nextTimeFiber q c hf z.1.2.2 '' Q.second := by
  constructor
  · rintro ⟨w,hw,he⟩
    change ((w.1.val.1,(w.1.val.2,w.2.2)),
      nextTimeCoordinates q c hf (q.nextConjugation d w.2.2 w.2.1.val)) = z at he
    subst z
    exact ⟨w.1.prop,hw.2.2,w.2.1.val,w.2.1.prop,rfl⟩
  · rintro ⟨hs,ht,w,hw,he⟩
    refine ⟨(⟨(z.1.1,z.1.2.1),hs⟩,(⟨w,hw⟩,z.1.2.2)),⟨mem_univ _,mem_univ _,ht⟩,?_⟩
    exact Prod.ext rfl he

lemma exchangedRectangleRegion_fiber
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) (J : Set ℝ)
    (b : UpperRootTransverse (d+1) × (T × ℝ))
    (hb : (b.1,b.2.1) ∈ Q.first) (ht : b.2.2 ∈ J) :
    Prod.mk b ⁻¹' C.exchangedRectangleRegion q g k c hf Q J =
      nextTimeFiber q c hf b.2.2 '' Q.second := by
  ext u
  change (b,u) ∈ C.exchangedRectangleRegion q g k c hf Q J ↔ _
  rw [exchangedRectangleRegion_mem (q := q) (c := c) (hf := hf) (C := C) (g := g) (k := k)]
  exact and_iff_right hb |>.trans (and_iff_right ht)

variable [MeasurableSpace T] [BorelSpace T]

theorem exchangedRectangleMeasure_conditional_region
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (J : Set ℝ) (hJ : MeasurableSet J)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ] :
    let σ := C.exchangedRectangleMeasure q g k c hf Q A J μ
    ∀ᵐ b ∂σ.fst, (b.1,b.2.1) ∈ Q.first ∧ b.2.2 ∈ J ∧
      ∀ᵐ u ∂σ.condKernel b, u ∈ nextTimeFiber q c hf b.2.2 '' Q.second := by
  intro σ
  have H : ∀ᵐ z ∂σ.fst ⊗ₘ σ.condKernel,
      (z.1.1,z.1.2.1) ∈ Q.first ∧ z.1.2.2 ∈ J ∧
        z.2 ∈ nextTimeFiber q c hf z.1.2.2 '' Q.second := by
    rw [Measure.disintegrate]
    exact (C.exchangedRectangleMeasure_ae_region q g k c hf Q A J hJ μ).mono
      (fun z hz => (exchangedRectangleRegion_mem
        (q := q) (c := c) (hf := hf) (C := C) (g := g) (k := k) Q J z).mp hz)
  filter_upwards [Measure.ae_ae_of_ae_compProd H] with b hb
  obtain ⟨u,hu⟩ := hb.exists
  exact ⟨hu.1,hu.2.1,hb.mono fun _ hz => hz.2.2⟩

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
