import OAI.NumberTheory.DukePrimeDegree.Entropy.NeutralFiberNames

namespace OAI

/-! # Actual conditional measures on bilateral itinerary fibers -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Disintegration of the graph of a measurable map is concentrated on
the corresponding fibers. -/
theorem ae_graph_condKernel_fiber
    {S Y : Type*} [MeasurableSpace S] [MeasurableEq S]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : Y → S) (hf : Measurable f) :
    let ρ := μ.map (fun y => (f y,y))
    ∀ᵐ s ∂ρ.fst, ∀ᵐ y ∂ρ.condKernel s, f y=s := by
  let ρ := μ.map (fun y => (f y,y))
  have hg : ∀ᵐ z ∂ρ, f z.2=z.1 := by
    apply (ae_map_iff (hf.prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun (hf.comp measurable_snd) measurable_fst)).mpr
    exact Filter.Eventually.of_forall fun _ => rfl
  have hcomp : ∀ᵐ z ∂ρ.fst ⊗ₘ ρ.condKernel, f z.2=z.1 := by
    rwa [Measure.disintegrate]
  exact Measure.ae_ae_of_ae_compProd hcomp

theorem ae_condDistrib_self_fiber
    {S Y : Type*} [MeasurableSpace S] [MeasurableEq S]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : Y → S) (hf : Measurable f) :
    ∀ᵐ s ∂μ.map f, ∀ᵐ y ∂condDistrib id f μ s, f y=s := by
  have H := ae_graph_condKernel_fiber μ f hf
  change ∀ᵐ s ∂(μ.map (fun y => (f y,y))).fst,
    ∀ᵐ y ∂(μ.map (fun y => (f y,y))).condKernel s, f y=s at H
  have hm : (μ.map (fun y => (f y,y))).fst=μ.map f :=
    Measure.fst_map_prodMk hf measurable_id
  rw [hm] at H
  simpa only [condDistrib,id_eq] using H

def bilateralNameObservation {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (Q : X n → ℕ)
    (x : X n) : (ℕ → ℕ) × (ℕ → ℕ) :=
  (fun k => Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x),
   fun k => Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x))

theorem measurable_bilateralNameObservation {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q) :
    Measurable (bilateralNameObservation ell hell Q) := by
  have hT (t : ℝ) : Measurable (fun z : X n =>
      rightAction z (diagonalOneParameter ell hell t)) :=
    (continuous_rightAction _).measurable
  exact (measurable_pi_iff.mpr fun k => hQ.comp ((hT (-1)).iterate k)).prodMk
    (measurable_pi_iff.mpr fun k => hQ.comp ((hT 1).iterate k))

theorem bilateralNameObservation_eq_iff {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (x y : X n) :
    bilateralNameObservation ell hell Q y = bilateralNameObservation ell hell Q x ↔
      y ∈ bilateralNameFiber ell hell Q x := by
  simp only [bilateralNameObservation,Prod.mk.injEq,funext_iff,bilateralNameFiber,
    mem_ofPred_eq]

/-- Almost every conditional measure for the actual bilateral itinerary
law is supported on the geometric fiber of any representative. -/
theorem ae_bilateral_condKernel_fiber {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q)
    (μ : Measure (X n)) [IsProbabilityMeasure μ] :
    let F := bilateralNameObservation ell hell Q
    let ρ := μ.map (fun x => (F x,x))
    ∀ᵐ s ∂ρ.fst, ∀ x, F x=s →
      ∀ᵐ y ∂ρ.condKernel s, y ∈ bilateralNameFiber ell hell Q x := by
  have h := ae_graph_condKernel_fiber μ _ (measurable_bilateralNameObservation ell hell Q hQ)
  filter_upwards [h] with s hs
  intro x hx
  filter_upwards [hs] with y hy
  exact (bilateralNameObservation_eq_iff ell hell Q x y).mp (hy.trans hx.symm)

end DukePrimeDegree

end

end OAI
