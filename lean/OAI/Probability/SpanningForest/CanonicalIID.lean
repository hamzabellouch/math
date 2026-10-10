import OAI.Probability.SpanningForest.LabelNoCollision
import OAI.Probability.SpanningForest.UniformSampler

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace Problem336.CanonicalIID

private theorem uniform_probability : IsProbabilityMeasure uniform01 := by
  rw [uniform01_eq_map_unitInterval]
  exact inferInstance

local instance : IsProbabilityMeasure uniform01 := uniform_probability

private theorem labels_probability : IsProbabilityMeasure privatePoolLaw := by
  unfold privatePoolLaw
  infer_instance

local instance : IsProbabilityMeasure privatePoolLaw := labels_probability

theorem map_labels {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {U : ℕ → Ω → ℝ} (h : IsVertexIID P U) :
    P.map (fun ω i => U i ω) = privatePoolLaw := by
  rw [iIndepFun.map_fun_eq_infinitePi_map h.1 (LabelNoCollision.independent h)]
  simp only [LabelNoCollision.map_marginal h]
  rfl

theorem canonical_isVertexIID :
    IsVertexIID privatePoolLaw (fun i U => U i) := by
  constructor
  · intro i
    exact measurable_pi_apply i
  · intro s A hA
    have hInd : iIndepFun (fun (i : ℕ) (U : ℕ → ℝ) => U i) privatePoolLaw :=
      iIndepFun_infinitePi (P := fun _ : ℕ => uniform01) (X := fun _ x => x)
        (fun _ => measurable_id)
    calc
      privatePoolLaw {U | ∀ i ∈ s, U i ∈ A i} =
          privatePoolLaw (⋂ i ∈ s, (fun U : ℕ → ℝ => U i) ⁻¹' A i) := by
        congr 1
        ext U
        simp
      _ = ∏ i ∈ s, privatePoolLaw ((fun U : ℕ → ℝ => U i) ⁻¹' A i) :=
        hInd.measure_inter_preimage_eq_mul s hA
      _ = ∏ i ∈ s, uniform01 (A i) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hm : privatePoolLaw.map (fun U : ℕ → ℝ => U i) = uniform01 :=
          Measure.infinitePi_map_eval (fun _ : ℕ => uniform01) i
        have heq := congrArg (fun μ : Measure ℝ => μ (A i)) hm
        rwa [Measure.map_apply (measurable_pi_apply i) (hA i hi)] at heq

theorem transfer_hasFUSFLaw {Ω : Type} [MeasurableSpace Ω]
    {G : GraphCode} {P : Measure Ω} {U : ℕ → Ω → ℝ}
    {X : (ℕ → ℝ) → EdgeConfiguration} (hU : IsVertexIID P U)
    (hX : HasFUSFLaw G privatePoolLaw X) :
    HasFUSFLaw G P (fun ω => X (fun i => U i ω)) := by
  have hlabels : Measurable (fun ω i => U i ω) := Measurable.of_eval hU.1
  constructor
  · intro e
    exact (hX.1 e).comp hlabels
  · intro H hH A B
    have hE : MeasurableSet {l : ℕ → ℝ |
        (∀ e ∈ A, X l e = true) ∧ (∀ e ∈ B, X l e = false)} := by
      exact ((Measurable.forall (fun e => measurable_const.imp ((hX.1 e).eq_const true))).and
        (Measurable.forall (fun e => measurable_const.imp ((hX.1 e).eq_const false)))).setOf
    have heq := congrArg (fun μ : Measure (ℕ → ℝ) => μ {l |
      (∀ e ∈ A, X l e = true) ∧ (∀ e ∈ B, X l e = false)}) (map_labels hU)
    rw [Measure.map_apply hlabels hE] at heq
    exact heq ▸ hX.2 H hH A B

theorem worksOnGraph_iff_canonical (Phi : FactorRule) (G : GraphCode) :
    WorksOnGraph Phi G ↔
      (GraphConnected G → GraphLocallyFinite G → HasFUSFLaw G privatePoolLaw (Phi G)) := by
  constructor
  · intro h hconn hfin
    exact h hconn hfin (ℕ → ℝ) privatePoolLaw (fun i U => U i) canonical_isVertexIID
  · intro h hconn hfin Ω _ P U hU
    exact transfer_hasFUSFLaw hU (h hconn hfin)

end Problem336.CanonicalIID

end

end OAI
