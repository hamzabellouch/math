import OAI.GroupTheory.PolycyclicRecognition.Analysis.UniformProfileConcentration
import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineSheetAgreement

namespace OAI

/-! # Propagating a profile through a bounded number of interior switches

The individual switch theorem is applied to marginal laws. Compactness
then gives joint concentration of every intermediate profile near the
initial one. The number of switches is fixed; no simultaneous success
assumption about all probes is needed.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology

variable {V W : Type*} [TopologicalSpace V] [LocallyCompactSpace V]
  [NormedAddCommGroup W]

omit [LocallyCompactSpace V] in
/-- Equality of all adjacent marginal limits propagates through the
whole finite chain, on the actual compact set of profile coordinates. -/
theorem profile_chain_concentration
    (S : Set C(V, W)) [CompactSpace S] [MetrizableSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (Z : Set V) [CompactSpace Z] (n : ℕ)
    (μ : ℕ → ProbabilityMeasure (Fin (n + 1) → S))
    (hedge : ∀ i : Fin n, ∀ ι : ℕ → ℕ, StrictMono ι →
      ∀ ν : ProbabilityMeasure (S × S),
      Tendsto (fun k => ProbabilityMeasure.map (μ (ι k))
        (fun f => (f i.castSucc, f i.succ))) atTop (𝓝 ν) →
      ∀ f ∈ (ν : Measure (S × S)).support, ∀ z ∈ Z, f.1.val z = f.2.val z)
    (j : Fin (n + 1)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun k => (μ k : Measure (Fin (n + 1) → S))
      {f | η ≤ dist ((f j).val.restrict Z) ((f 0).val.restrict Z)}) atTop (𝓝 0) := by
  have hcoord (i : Fin (n + 1)) :
      Continuous (fun f : Fin (n + 1) → S => (f i).val.restrict Z) :=
    (ContinuousMap.continuous_restrict Z).comp
      (continuous_subtype_val.comp (continuous_apply i))
  apply measure_closed_tendsto_zero_of_all_supported_limits μ
    (isClosed_le continuous_const ((hcoord j).dist (hcoord 0)))
  intro ι hι ν hν f hf
  have hadj (i : Fin n) (z : V) (hz : z ∈ Z) :
      (f i.castSucc).val z = (f i.succ).val z := by
    let p : (Fin (n + 1) → S) → S × S := fun g => (g i.castSucc, g i.succ)
    have hp : Continuous p := (continuous_apply _).prodMk (continuous_apply _)
    have hmap : Tendsto (fun k => ProbabilityMeasure.map (μ (ι k)) p)
        atTop (𝓝 (ProbabilityMeasure.map ν p)) :=
      (ProbabilityMeasure.continuous_map hp).continuousAt.tendsto.comp hν
    exact hedge i ι hι (ProbabilityMeasure.map ν p) hmap (p f)
      (mem_support_map_of_continuous ν p hp hf) z hz
  have hall (i : Fin (n + 1)) : ∀ z ∈ Z, (f i).val z = (f 0).val z := by
    induction i using Fin.induction with
    | zero => intro z hz; rfl
    | succ i hi =>
      intro z hz
      exact (hadj i z hz).symm.trans (hi z hz)
  have heq : (f j).val.restrict Z = (f 0).val.restrict Z := by
    ext z
    exact hall j z.val z.property
  simpa only [mem_ofPred_eq, heq, dist_self, not_le] using hη

omit [LocallyCompactSpace V] in
/-- The finite-chain conclusion survives arbitrary independent probe laws.
Only adjacent deterministic marginal limits have to be identified. -/
theorem independent_profile_chain_concentration
    (S : Set C(V, W)) [CompactSpace S] [MetrizableSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (Z : Set V) [CompactSpace Z] (n : ℕ)
    {A K : ℕ → Type*} [∀ m, MeasurableSpace (A m)] [∀ m, MeasurableSpace (K m)]
    [∀ m, Nonempty (K m)]
    (μ : ∀ m, ProbabilityMeasure (A m)) (ν : ∀ m, ProbabilityMeasure (K m))
    (profile : ∀ m, A m × K m → Fin (n + 1) → S)
    (hp : ∀ m, Measurable (profile m))
    (hedge : ∀ k : ∀ m, K m, ∀ i : Fin n, ∀ ι : ℕ → ℕ, StrictMono ι →
      ∀ limitLaw : ProbabilityMeasure (S × S),
      Tendsto (fun m => ProbabilityMeasure.map
        (ProbabilityMeasure.map (μ (ι m)) (fun a => profile (ι m) (a, k (ι m))))
        (fun f => (f i.castSucc, f i.succ))) atTop (𝓝 limitLaw) →
      ∀ f ∈ (limitLaw : Measure (S × S)).support, ∀ z ∈ Z, f.1.val z = f.2.val z)
    (j : Fin (n + 1)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun m => (μ m : Measure (A m)).prod (ν m : Measure (K m))
      {p | η ≤ dist ((profile m p j).val.restrict Z)
        ((profile m p 0).val.restrict Z)}) atTop (𝓝 0) := by
  let B : Set (Fin (n + 1) → S) :=
    {f | η ≤ dist ((f j).val.restrict Z) ((f 0).val.restrict Z)}
  have hcoord (i : Fin (n + 1)) :
      Continuous (fun f : Fin (n + 1) → S => (f i).val.restrict Z) :=
    (ContinuousMap.continuous_restrict Z).comp
      (continuous_subtype_val.comp (continuous_apply i))
  have hB : MeasurableSet B :=
    (isClosed_le continuous_const ((hcoord j).dist (hcoord 0))).measurableSet
  apply independent_bad_probability_tendsto_zero μ ν
    (fun m => profile m ⁻¹' B) (fun m => hB.preimage (hp m))
  intro k
  have hk (m : ℕ) : Measurable (fun a => profile m (a, k m)) :=
    (hp m).comp (measurable_id.prodMk measurable_const)
  have hc := profile_chain_concentration S Z n
    (fun m => ProbabilityMeasure.map (μ m) (fun a => profile m (a, k m)))
    (hedge k) j hη
  convert hc using 1
  funext m
  exact (ProbabilityMeasure.map_apply' (μ m) (hk m).aemeasurable hB).symm

end PolycyclicRecognition

end

end OAI
