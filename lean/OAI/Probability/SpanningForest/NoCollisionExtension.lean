import OAI.Probability.SpanningForest.CanonicalIID
import OAI.Probability.SpanningForest.GraphBorel
import OAI.Probability.SpanningForest.RuleExtension

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336

def noCollisionRule (Phi : FactorRule) : FactorRule :=
  gatedRule (fun _ U => Function.Injective U) Phi

theorem injective_relabelLabels_iff (σ : Equiv ℕ ℕ) (U : ℕ → ℝ) :
    Function.Injective (relabelLabels σ U) ↔ Function.Injective U := by
  constructor
  · intro h u v huv
    have heq : relabelLabels σ U (σ u) = relabelLabels σ U (σ v) := by
      simpa [relabelLabels] using huv
    exact σ.injective (h heq)
  · intro h u v huv
    exact σ.symm.injective (h huv)

theorem RuleBorel.noCollision {Phi : FactorRule} (hPhi : RuleBorel Phi) :
    RuleBorel (noCollisionRule Phi) :=
  hPhi.gated (GraphBorel.measurable_injective_labels.comp measurable_snd)

theorem noCollisionRule_equivariant {Phi : FactorRule}
    (hPhi : ∀ (σ : Equiv ℕ ℕ) (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode),
      Function.Injective U →
      Phi (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) = Phi G U e) :
    RuleEquivariant (noCollisionRule Phi) := by
  classical
  intro σ G U e
  by_cases hU : Function.Injective U
  · simpa [noCollisionRule, gatedRule, hU, injective_relabelLabels_iff] using
      hPhi σ G U e hU
  · simp [noCollisionRule, gatedRule, hU, injective_relabelLabels_iff]

theorem RuleEquivariant.noCollision {Phi : FactorRule} (hPhi : RuleEquivariant Phi) :
    RuleEquivariant (noCollisionRule Phi) :=
  noCollisionRule_equivariant (fun σ G U e _ => hPhi σ G U e)

theorem noCollisionRule_ae_eq {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {U : ℕ → Ω → ℝ} (hU : IsVertexIID P U)
    (Phi : FactorRule) (G : GraphCode) :
    (fun ω => noCollisionRule Phi G (fun i => U i ω)) =ᵐ[P]
      (fun ω => Phi G (fun i => U i ω)) :=
  gatedRule_ae_eq (LabelNoCollision.ae_injective_labels hU)

theorem WorksOnGraph.noCollision {Phi : FactorRule} {G : GraphCode}
    (hWorks : WorksOnGraph Phi G) (hBorel : RuleBorel Phi) :
    WorksOnGraph (noCollisionRule Phi) G := by
  intro hconn hfin Ω _ P U hU
  apply (hWorks hconn hfin Ω P U hU).congr
  · intro e
    have hlabels : Measurable (fun ω i => U i ω) := Measurable.of_eval hU.1
    exact hBorel.noCollision.comp
      (measurable_const.prodMk (hlabels.prodMk measurable_const))
  · exact (noCollisionRule_ae_eq hU Phi G).symm

theorem factor_witness_of_collision_free {Phi : FactorRule}
    (hBorel : RuleBorel Phi)
    (hEquiv : ∀ (σ : Equiv ℕ ℕ) (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode),
      Function.Injective U →
      Phi (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) = Phi G U e)
    (hLaw : ∀ G : GraphCode, GraphConnected G → GraphLocallyFinite G →
      HasFUSFLaw G privatePoolLaw (Phi G)) :
    ∃ Psi : FactorRule, RuleBorel Psi ∧ RuleEquivariant Psi ∧
      ∀ G : GraphCode, WorksOnGraph Psi G := by
  refine ⟨noCollisionRule Phi, hBorel.noCollision, noCollisionRule_equivariant hEquiv, ?_⟩
  intro G
  exact ((CanonicalIID.worksOnGraph_iff_canonical Phi G).mpr (hLaw G)).noCollision hBorel

theorem IsVertexIID.comp_uniform {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {U : ℕ → Ω → ℝ} (hU : IsVertexIID P U)
    {κ : ℝ → ℝ} (hκ : Measurable κ) (hmap : uniform01.map κ = uniform01) :
    IsVertexIID P (fun i ω => κ (U i ω)) := by
  constructor
  · intro i
    exact hκ.comp (hU.1 i)
  · intro s A hA
    calc
      P {ω | ∀ i ∈ s, κ (U i ω) ∈ A i} =
          ∏ i ∈ s, uniform01 (κ ⁻¹' A i) :=
        hU.2 s (fun i => κ ⁻¹' A i) (fun i hi => hκ (hA i hi))
      _ = ∏ i ∈ s, uniform01 (A i) := by
        apply Finset.prod_congr rfl
        intro i hi
        have heq := congrArg (fun μ : Measure ℝ => μ (A i)) hmap
        rwa [Measure.map_apply hκ (hA i hi)] at heq

def keyCollisionRule (κ : ℝ → ℝ) (Phi : FactorRule) : FactorRule :=
  gatedRule (fun _ U => Function.Injective (fun i => κ (U i))) Phi

theorem injective_keys_relabel_iff (κ : ℝ → ℝ) (σ : Equiv ℕ ℕ) (U : ℕ → ℝ) :
    Function.Injective (fun i => κ (relabelLabels σ U i)) ↔
      Function.Injective (fun i => κ (U i)) :=
  injective_relabelLabels_iff σ (fun i => κ (U i))

theorem RuleBorel.keyCollision {Phi : FactorRule} (hPhi : RuleBorel Phi)
    {κ : ℝ → ℝ} (hκ : Measurable κ) : RuleBorel (keyCollisionRule κ Phi) := by
  apply hPhi.gated
  exact GraphBorel.measurable_injective_labels.comp
    (Measurable.of_eval (fun i => hκ.comp ((measurable_pi_apply i).comp measurable_snd)))

theorem keyCollisionRule_equivariant {Phi : FactorRule} {κ : ℝ → ℝ}
    (hPhi : ∀ (σ : Equiv ℕ ℕ) (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode),
      Function.Injective (fun i => κ (U i)) →
      Phi (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) = Phi G U e) :
    RuleEquivariant (keyCollisionRule κ Phi) := by
  classical
  intro σ G U e
  by_cases hU : Function.Injective (fun i => κ (U i))
  · simpa [keyCollisionRule, gatedRule, hU, injective_keys_relabel_iff] using
      hPhi σ G U e hU
  · simp [keyCollisionRule, gatedRule, hU, injective_keys_relabel_iff]

theorem keyCollisionRule_ae_eq {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {U : ℕ → Ω → ℝ} (hU : IsVertexIID P U)
    {κ : ℝ → ℝ} (hκ : Measurable κ) (hmap : uniform01.map κ = uniform01)
    (Phi : FactorRule) (G : GraphCode) :
    (fun ω => keyCollisionRule κ Phi G (fun i => U i ω)) =ᵐ[P]
      (fun ω => Phi G (fun i => U i ω)) :=
  gatedRule_ae_eq (LabelNoCollision.ae_injective_labels (hU.comp_uniform hκ hmap))

theorem WorksOnGraph.keyCollision {Phi : FactorRule} {G : GraphCode}
    (hWorks : WorksOnGraph Phi G) (hBorel : RuleBorel Phi)
    {κ : ℝ → ℝ} (hκ : Measurable κ) (hmap : uniform01.map κ = uniform01) :
    WorksOnGraph (keyCollisionRule κ Phi) G := by
  intro hconn hfin Ω _ P U hU
  apply (hWorks hconn hfin Ω P U hU).congr
  · intro e
    have hlabels : Measurable (fun ω i => U i ω) := Measurable.of_eval hU.1
    exact (hBorel.keyCollision hκ).comp
      (measurable_const.prodMk (hlabels.prodMk measurable_const))
  · exact (keyCollisionRule_ae_eq hU hκ hmap Phi G).symm

theorem map_splitVertexKey :
    uniform01.map (fun x => (splitVertexLabel x).1) = uniform01 := by
  let : IsProbabilityMeasure privatePoolLaw :=
    LabelNoCollision.probability CanonicalIID.canonical_isVertexIID
  change uniform01.map (Prod.fst ∘ splitVertexLabel) = uniform01
  rw [← Measure.map_map measurable_fst measurable_splitVertexLabel, map_splitVertexLabel]
  simp [keyPoolLaw]

theorem ae_injective_splitVertexKeys {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {U : ℕ → Ω → ℝ} (hU : IsVertexIID P U) :
    ∀ᵐ ω ∂P, Function.Injective (fun i => (splitVertexLabel (U i ω)).1) :=
  LabelNoCollision.ae_injective_labels
    (hU.comp_uniform measurable_splitVertexLabel.fst map_splitVertexKey)

theorem factor_witness_of_canonical_keys {Phi : FactorRule} {κ : ℝ → ℝ}
    (hκ : Measurable κ) (hmap : uniform01.map κ = uniform01)
    (hBorel : RuleBorel Phi)
    (hEquiv : ∀ (σ : Equiv ℕ ℕ) (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode),
      Function.Injective (fun i => κ (U i)) →
      Phi (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) = Phi G U e)
    (hLaw : ∀ G : GraphCode, GraphConnected G → GraphLocallyFinite G →
      HasFUSFLaw G privatePoolLaw (Phi G)) :
    ∃ Psi : FactorRule, RuleBorel Psi ∧ RuleEquivariant Psi ∧
      ∀ G : GraphCode, WorksOnGraph Psi G := by
  refine ⟨keyCollisionRule κ Phi, hBorel.keyCollision hκ,
    keyCollisionRule_equivariant hEquiv, ?_⟩
  intro G
  exact ((CanonicalIID.worksOnGraph_iff_canonical Phi G).mpr (hLaw G)).keyCollision
    hBorel hκ hmap

end Problem336

end

end OAI
