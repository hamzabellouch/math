import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ChartCostJets

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MixedContinuity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

local instance genericMixedProdNormedGroup : NormedAddCommGroup (F×E) := Prod.normedAddCommGroup
local instance genericMixedProdNormedSpace : NormedSpace ℝ (F×E) := Prod.normedSpace
local instance genericMixedDualNormedGroup : NormedAddCommGroup ((F×E) →L[ℝ] ℝ) := inferInstance
local instance genericMixedDualNormedSpace : NormedSpace ℝ ((F×E) →L[ℝ] ℝ) := inferInstance
end MixedContinuity

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance tangentFiniteTrivialization (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance mixedTrivProductNormedGroup (x y : M) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) :=
  Prod.normedAddCommGroup
local instance mixedTrivProductNormedSpace (x y : M) :
    NormedSpace ℝ (TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) := Prod.normedSpace
local instance mixedTrivDualNormedGroup (x y : M) :
    NormedAddCommGroup ((TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ) := inferInstance
local instance mixedTrivDualNormedSpace (x y : M) :
    NormedSpace ℝ ((TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ) := inferInstance
end WeakMTWTransport

end



noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
lemma compact_parameter_second_jet_on_graph {Q E : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set Q} (hK : IsCompact K) {v : Q → E} (hv : Continuous v)
    {F : (ℝ×Q) → E → ℝ} {t : ℝ}
    (hF : ∀ q∈K, ContDiffAt ℝ ∞ (Function.uncurry F) ((t,q),v q)) :
    ∃ B>0, ∀ᶠ s in 𝓝 t, ∀ q∈K,
      ContDiffAt ℝ 2 (F (s,q)) (v q) ∧
      ‖fderiv ℝ (fderiv ℝ (F (s,q))) (v q)‖≤B := by
  let H := fun z : ℝ×Q => fderiv ℝ (fderiv ℝ (F z)) (v z.2)
  have hc : Continuous (fun z : ℝ×Q => (z,v z.2)) := continuous_id.prodMk (hv.comp continuous_snd)
  have hH : ∀ q∈K, ContinuousAt H (t,q) := by
    intro q hq
    exact (ContDiffAt.partial_snd_fderiv_two (hF q hq)).continuousAt.comp
      (x := (t,q)) (f := fun z : ℝ×Q => (z,v z.2)) hc.continuousAt
  obtain ⟨B,hB,HB⟩ := compact_eventually_fiberwise_bound hK
    (f := fun _ : Q => ()) continuous_const (g := fun _ : ℝ => ())
    (continuousAt_const (x := t)) (h := H) (fun q hq _ => hH q hq)
  have HS : ∀ᶠ s in 𝓝 t, ∀ q∈K, ()=() → ContDiffAt ℝ 2 (F (s,q)) (v q) := by
    apply compact_eventually_fiberwise hK (f := fun _ : Q => ()) continuous_const
      (g := fun _ : ℝ => ()) (continuousAt_const (x := t))
    intro q hq _
    have He := ((hF q hq).of_le
      (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by simp)
    filter_upwards [(hc.continuousAt (x := (t,q))).tendsto.eventually He] with z hz
    exact hz.comp (v z.2) (contDiffAt_const.prodMk contDiffAt_id)
  refine ⟨B,hB,?_⟩
  filter_upwards [HB,HS] with s hb hs
  exact fun q hq => ⟨hs q hq rfl,hb q hq rfl⟩
end WeakMTWTransport

end

end OAI
