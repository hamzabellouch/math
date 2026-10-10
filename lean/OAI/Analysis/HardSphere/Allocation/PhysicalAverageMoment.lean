import Mathlib
import OAI.Analysis.HardSphere.Comparison.MixtureMoment
import OAI.Analysis.HardSphere.Allocation.LabelEncounterAverage

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def physicalAverageLikelihood {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y))
    (d : PhysicalDatum N K M G L) (w : Option J→C(Time,Point)) : ℝ≥0∞ :=
  ∫⁻c,physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,c) w
    ∂(ν.prod (physicalLabels hL g m t r R C S u particle)) d

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma physicalAverageLikelihood_measurable {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y))
    [IsSFiniteKernel ν] :
    Measurable (fun z : PhysicalDatum N K M G L×(Option J→C(Time,Point)) ↦
      physicalAverageLikelihood hL g m t r R C S u particle hxy b ν z.1 z.2) := by
  exact ((physicalRouteLikelihood_measurable hL g m t r R C S u particle hxy b).comp
    ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)).lintegral_kernel_prod_right'
      (κ:=(ν.prod (physicalLabels hL g m t r R C S u particle)).comap Prod.fst measurable_fst)

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma physicalAverageLikelihood_square {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y))
    [IsMarkovKernel ν] (d : PhysicalDatum N K M G L) :
    (∫⁻w,(physicalAverageLikelihood hL g m t r R C S u particle hxy b ν d w)^2
      ∂physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d)=
    ∫⁻p,∫⁻p',∫⁻z,∫⁻z',∫⁻w,
      physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,(p,z)) w *
      physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,(p',z')) w
      ∂physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d
      ∂physicalLabels hL g m t r R C S u particle d
      ∂physicalLabels hL g m t r R C S u particle d ∂ν d ∂ν d := by
  unfold physicalAverageLikelihood
  rw [mixed_likelihood_square _ _ (fun cw : PhysicalRouteCode x y J×(Option J→C(Time,Point)) ↦
    physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,cw.1) cw.2)
    ((physicalRouteLikelihood_measurable hL g m t r R C S u particle hxy b).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))]
  simp_rw [Kernel.prod_apply,lintegral_prod _ (measurable_of_countable _).aemeasurable]
  apply lintegral_congr
  intro p
  exact lintegral_lintegral_swap (measurable_of_countable _).aemeasurable

theorem physicalAverage_moment {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin N) (d : PhysicalDatum N K M G L) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (hM : 0<M)
    (hsupply : ∀ᵐp ∂ν d,∀v∈departureSites p,
      (M:ℝ)≤2*((branchAccessible hL g m t r R C S u particle v d).card:ℝ))
    (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (q : ℝ≥0∞) (δ B κ : ℝ) (hδ : 0<δ) (hB : 1≤B) (hBt : routeDensityBound t≤ENNReal.ofReal B)
    (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ≤κ)
    (hq : ∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p | TrialCollision r (projectCurve L f.val) p.val}≤q)
    (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) (b : Bool) :
    (∫⁻w,(physicalAverageLikelihood hL g m t r R C S u particle hxy b ν d w)^2
      ∂physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d)≤
      ENNReal.ofReal B*(∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d) := by
  rw [physicalAverageLikelihood_square]
  simp_rw [←lintegral_const_mul _ (measurable_of_countable _),←ENNReal.ofReal_mul (zero_le_one.trans hB)]
  apply lintegral_mono_ae
  filter_upwards [hsupply] with p hpSupply
  apply lintegral_mono_ae
  filter_upwards [hsupply] with p' hpSupply'
  apply physicalLabel_moment hL g m t r R C S ht hr u particle d hxy p p' hM _ hm hp q δ B κ hδ hB hBt hκ hq hsmall b
  intro v hv
  rcases Finset.mem_union.mp hv with h | h
  · exact hpSupply v h
  · exact hpSupply' v h

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def physicalGoodLikelihood {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y))
    (E : Set (PhysicalDatum N K M G L)) (z : PhysicalDatum N K M G L×(Option J→C(Time,Point))) : ℝ≥0∞ :=
  if z.1∈E then physicalAverageLikelihood hL g m t r R C S u particle hxy b ν z.1 z.2 else 0

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma physicalGoodLikelihood_measurable {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) [IsSFiniteKernel ν]
    (E : Set (PhysicalDatum N K M G L)) (hE : MeasurableSet E) :
    Measurable (physicalGoodLikelihood hL g m t r R C S u particle hxy b ν E) :=
  (physicalAverageLikelihood_measurable hL g m t r R C S u particle hxy b ν).ite
    (hE.preimage measurable_fst) measurable_const

theorem physicalGoodLikelihood_moment {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin N) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum N K M G L)) [SFinite μ]
    (E : Set (PhysicalDatum N K M G L)) (hE : MeasurableSet E)
    (hM : 0<M) (q : ℝ≥0∞) (δ B κ Cpath : ℝ) (hδ : 0<δ) (hB : 1≤B)
    (hBt : routeDensityBound t≤ENNReal.ofReal B)
    (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ≤κ)
    (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1)
    (hdata : ∀ᵐd ∂μ.restrict E,
      (∀ᵐp ∂ν d,∀v∈departureSites p,(M:ℝ)≤2*((branchAccessible hL g m t r R C S u particle v d).card:ℝ)) ∧
      (∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M) ∧
      (∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) ∧
      (∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
        physicalCollisionReference hL g m t r R C S u particle d j
          {p | TrialCollision r (projectCurve L f.val) p.val}≤q))
    (henc : (∫⁻d in E,∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d ∂μ)≤ENNReal.ofReal Cpath)
    (b : Bool) :
    (∫⁻z,(physicalGoodLikelihood hL g m t r R C S u particle hxy b ν E z)^2
      ∂μ ⊗ₘ physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)))≤
      ENNReal.ofReal B*ENNReal.ofReal Cpath := by
  rw [Measure.lintegral_compProd ((physicalGoodLikelihood_measurable hL g m t r R C S u particle hxy b ν E hE).pow_const 2)]
  have hind (d : PhysicalDatum N K M G L) :
      (∫⁻w,(physicalGoodLikelihood hL g m t r R C S u particle hxy b ν E (d,w))^2
        ∂physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d)=
      E.indicator (fun d ↦ ∫⁻w,(physicalAverageLikelihood hL g m t r R C S u particle hxy b ν d w)^2
        ∂physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d) d := by
    by_cases hd : d∈E <;> simp [physicalGoodLikelihood,hd]
  simp_rw [hind]
  rw [lintegral_indicator hE]
  calc
    _ ≤ ∫⁻d in E,ENNReal.ofReal B*(∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hdata] with d hd
      exact physicalAverage_moment hL g m t r R C S ht hr u particle d hxy ν hM hd.1 hd.2.1 hd.2.2.1
        q δ B κ hδ hB hBt hκ hd.2.2.2 hsmall b
    _ = ENNReal.ofReal B*(∫⁻d in E,∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d ∂μ) := by
      rw [lintegral_const_mul' _ _ (by simp)]
    _ ≤ _ := mul_le_mul' le_rfl henc

end HardSphere.Groups
end
end

end OAI
