import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalIndependentBoxes
import OAI.NumberTheory.DukePrimeDegree.Entropy.PrefixRootConditionals

namespace OAI

/-! # Including an independent rectangle in the actual remaining subgroup -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]

def includeRootRectangle (d : ℕ) (q : InitialRootStep (d+1))
    (i : B → positiveRootGeneratedGroup (q.remaining.erase q.root))
    (z : S × (B × ℝ)) : S × (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) :=
  (z.1,(i z.2.1,z.2.2))

omit [StandardBorelSpace B] [Nonempty B] in
lemma measurable_includeRootRectangle (d : ℕ) (q : InitialRootStep (d+1))
    (i : B → positiveRootGeneratedGroup (q.remaining.erase q.root)) (hi : Measurable i) :
    Measurable (q.includeRootRectangle d (S := S) i) :=
  measurable_fst.prodMk ((hi.comp measurable_snd.fst).prodMk measurable_snd.snd)

theorem includeRootRectangle_conditional_independent (d : ℕ) (q : InitialRootStep (d+1))
    (i : B → positiveRootGeneratedGroup (q.remaining.erase q.root)) (hi : Measurable i)
    (ρ : Measure (S × (B × ℝ))) [IsFiniteMeasure ρ]
    (hprod : ∀ᵐ s ∂ρ.fst,
      ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd) :
    let σ := ρ.map (q.includeRootRectangle d i)
    ∀ᵐ s ∂σ.fst, σ.condKernel s = (σ.condKernel s).fst.prod (σ.condKernel s).snd := by
  intro σ
  let F : S × (B × ℝ) → positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ :=
    fun z => (i z.2.1,z.2.2)
  have hF : Measurable F := (hi.comp measurable_snd.fst).prodMk measurable_snd.snd
  have hs : σ.fst = ρ.fst := by
    have H := fst_map_fibers ρ (MeasurableEquiv.refl S) F hF
    change σ.fst = ρ.fst.map id at H
    simpa only [Measure.map_id] using H
  have hc : ∀ᵐ s ∂ρ.fst, σ.condKernel s = (ρ.condKernel s).map (Prod.map i id) :=
    conditional_map_fibers ρ (MeasurableEquiv.refl S) F hF
  rw [hs]
  filter_upwards [hprod,hc] with s hp hc
  have he : σ.condKernel s =
      ((ρ.condKernel s).fst.map i).prod (ρ.condKernel s).snd := by
    rw [hc]
    conv_lhs => rw [hp]
    rw [←Measure.map_prod_map _ _ hi measurable_id,Measure.map_id]
  exact probability_eq_prod_marginals_of_prod _ _ _ he

end InitialRootStep
end DukePrimeDegree

end

end OAI
