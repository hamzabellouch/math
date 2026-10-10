import OAI.Probability.SpanningForest.EdgeAction
import OAI.Probability.SpanningForest.Picard

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Problem336
namespace FactorAssembly

abbrev EdgeField := EdgeCode → ℝ
abbrev GraphDrift := GraphCode → ℝ → EdgeField → EdgeCode → ℝ
abbrev GraphNoise := GraphCode → (ℕ → ℝ) → EdgeCode → ℝ → ℝ

def DriftBorel (b : GraphDrift) : Prop :=
  ∀ e, Measurable (fun p : GraphCode × (ℝ × EdgeField) => b p.1 p.2.1 p.2.2 e)

def NoiseBorel (w : GraphNoise) : Prop :=
  ∀ e, Measurable (fun p : (GraphCode × (ℕ → ℝ)) × ℝ => w p.1.1 p.1.2 e p.2)

def DriftEquivariant (b : GraphDrift) : Prop :=
  ∀ (σ : Equiv ℕ ℕ) (G : GraphCode) (t : ℝ) (y : EdgeField) (e : EdgeCode),
    b (relabelGraph σ G) t (fun f => y (mapEdge σ.symm f)) (mapEdge σ e) = b G t y e

def NoiseEquivariant (w : GraphNoise) : Prop :=
  ∀ (σ : Equiv ℕ ℕ) (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode) (t : ℝ),
    w (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) t = w G U e t

def decodedSlope (b : GraphDrift) (w : GraphNoise)
    (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode) (n : ℕ) : ℝ :=
  Picard.decode (w G U) (b G) e (n : ℝ) / (n : ℝ)

def rule (b : GraphDrift) (w : GraphNoise) : FactorRule := by
  classical
  exact fun G U e =>
    if (1 / 2 : ℝ) < limsup (decodedSlope b w G U e) atTop then true else false

theorem measurable_decodedPath {b : GraphDrift} {w : GraphNoise}
    (hb : DriftBorel b) (hw : NoiseBorel w) (e : EdgeCode) :
    Measurable (fun p : (GraphCode × (ℕ → ℝ)) × ℝ =>
      Picard.decode (w p.1.1 p.1.2) (b p.1.1) e p.2) := by
  apply Picard.measurable_decode
    (w := fun p : GraphCode × (ℕ → ℝ) => w p.1 p.2)
    (b := fun p : GraphCode × (ℕ → ℝ) => b p.1) hw
  intro i
  exact (hb i).comp (measurable_fst.fst.prodMk measurable_snd)

theorem measurable_decodedSlope {b : GraphDrift} {w : GraphNoise}
    (hb : DriftBorel b) (hw : NoiseBorel w) (e : EdgeCode) (n : ℕ) :
    Measurable (fun p : GraphCode × (ℕ → ℝ) => decodedSlope b w p.1 p.2 e n) := by
  exact ((measurable_decodedPath hb hw e).comp
    (measurable_id.prodMk measurable_const)).div_const (n : ℝ)

theorem measurable_rule_edge {b : GraphDrift} {w : GraphNoise}
    (hb : DriftBorel b) (hw : NoiseBorel w) (e : EdgeCode) :
    Measurable (fun p : GraphCode × (ℕ → ℝ) => rule b w p.1 p.2 e) := by
  classical
  have hl : Measurable (fun p : GraphCode × (ℕ → ℝ) =>
      limsup (decodedSlope b w p.1 p.2 e) atTop) :=
    Measurable.limsup (fun n => measurable_decodedSlope hb hw e n)
  change Measurable (fun p : GraphCode × (ℕ → ℝ) =>
    if (1 / 2 : ℝ) < limsup (decodedSlope b w p.1 p.2 e) atTop then true else false)
  exact Measurable.ite (measurableSet_lt measurable_const hl) measurable_const measurable_const

theorem ruleBorel_of_coordinate_measurable (Phi : FactorRule)
    (hPhi : ∀ e, Measurable (fun p : GraphCode × (ℕ → ℝ) => Phi p.1 p.2 e)) :
    RuleBorel Phi := by
  have hall : Measurable (fun p : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      Phi p.1.1 p.1.2 p.2) :=
    measurable_from_prod_countable_left hPhi
  have hpair : Measurable (fun q : GraphCode × ((ℕ → ℝ) × EdgeCode) =>
      ((q.1, q.2.1), q.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  exact hall.comp hpair

theorem rule_borel {b : GraphDrift} {w : GraphNoise}
    (hb : DriftBorel b) (hw : NoiseBorel w) : RuleBorel (rule b w) :=
  ruleBorel_of_coordinate_measurable (rule b w) (measurable_rule_edge hb hw)

theorem decodedPath_relabel {b : GraphDrift} {w : GraphNoise}
    (hb : DriftEquivariant b) (hw : NoiseEquivariant w)
    (σ : Equiv ℕ ℕ) (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode) (t : ℝ) :
    Picard.decode (w (relabelGraph σ G) (relabelLabels σ U))
      (b (relabelGraph σ G)) (mapEdge σ e) t =
      Picard.decode (w G U) (b G) e t := by
  exact Picard.decode_relabel (edgeEquiv σ) (w G U)
    (w (relabelGraph σ G) (relabelLabels σ U)) (b G) (b (relabelGraph σ G))
    (hw σ G U) (hb σ G) e t

theorem rule_equivariant {b : GraphDrift} {w : GraphNoise}
    (hb : DriftEquivariant b) (hw : NoiseEquivariant w) :
    RuleEquivariant (rule b w) := by
  classical
  intro σ G U e
  have hs : decodedSlope b w (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) =
      decodedSlope b w G U e := by
    funext n
    exact congrArg (fun x : ℝ => x / (n : ℝ)) (decodedPath_relabel hb hw σ G U e n)
  simp only [rule, hs]

end FactorAssembly
end Problem336

end

end OAI
