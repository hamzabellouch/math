import OAI.Probability.SpanningForest.AllPairFactorAssembly
import OAI.Probability.SpanningForest.FactorAssembly

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Problem336.AllPairPicardDecoder
open FactorAssembly

def decoder {Y : Type*} (eval : Y → ℝ → ℝ) (b : GraphDrift)
    (G : GraphCode) (W : EdgeCode → Y) (e : EdgeCode) : Bool := by
  classical
  exact if (1 / 2 : ℝ) < limsup
    (fun n : ℕ => Picard.decode (fun f => eval (W f)) (b G) e (n : ℝ) / (n : ℝ))
    atTop then true else false

theorem measurable_decodedPath {Y : Type*} [MeasurableSpace Y]
    (eval : Y → ℝ → ℝ) (heval : Measurable (Function.uncurry eval))
    (b : GraphDrift) (hb : DriftBorel b) (e : EdgeCode) :
    Measurable (fun p : (GraphCode × (EdgeCode → Y)) × ℝ =>
      Picard.decode (fun f => eval (p.1.2 f)) (b p.1.1) e p.2) := by
  have hw (f : EdgeCode) :
      Measurable (fun p : (GraphCode × (EdgeCode → Y)) × ℝ => eval (p.1.2 f) p.2) := by
    have hm : Measurable (fun p : (GraphCode × (EdgeCode → Y)) × ℝ =>
        (p.1.2 f, p.2)) :=
      ((measurable_pi_apply f).comp measurable_fst.snd).prodMk measurable_snd
    exact heval.comp hm
  apply Picard.measurable_decode
    (w := fun p : GraphCode × (EdgeCode → Y) => fun f => eval (p.2 f))
    (b := fun p : GraphCode × (EdgeCode → Y) => b p.1) hw
  intro i
  exact (hb i).comp (measurable_fst.fst.prodMk measurable_snd)

theorem measurable_decoder_edge {Y : Type*} [MeasurableSpace Y]
    (eval : Y → ℝ → ℝ) (heval : Measurable (Function.uncurry eval))
    (b : GraphDrift) (hb : DriftBorel b) (e : EdgeCode) :
    Measurable (fun p : GraphCode × (EdgeCode → Y) => decoder eval b p.1 p.2 e) := by
  classical
  have hl : Measurable (fun p : GraphCode × (EdgeCode → Y) => limsup
      (fun n : ℕ => Picard.decode (fun f => eval (p.2 f)) (b p.1) e n / n) atTop) :=
    Measurable.limsup (fun n =>
      ((measurable_decodedPath eval heval b hb e).comp
        (measurable_id.prodMk measurable_const)).div_const (n : ℝ))
  change Measurable (fun p : GraphCode × (EdgeCode → Y) =>
    if (1 / 2 : ℝ) < limsup
      (fun n : ℕ => Picard.decode (fun f => eval (p.2 f)) (b p.1) e n / n) atTop
    then true else false)
  exact Measurable.ite (measurableSet_lt measurable_const hl) measurable_const measurable_const

private theorem joint_measurable_of_coordinates {A : Type*} [MeasurableSpace A]
    (F : GraphCode → A → EdgeConfiguration)
    (hF : ∀ e, Measurable (fun p : GraphCode × A => F p.1 p.2 e)) :
    Measurable (fun q : GraphCode × (A × EdgeCode) => F q.1 q.2.1 q.2.2) := by
  have hall : Measurable (fun q : (GraphCode × A) × EdgeCode => F q.1.1 q.1.2 q.2) :=
    measurable_from_prod_countable_left hF
  have hpair : Measurable (fun q : GraphCode × (A × EdgeCode) =>
      ((q.1, q.2.1), q.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  exact hall.comp hpair

theorem measurable_decoder {Y : Type*} [MeasurableSpace Y]
    (eval : Y → ℝ → ℝ) (heval : Measurable (Function.uncurry eval))
    (b : GraphDrift) (hb : DriftBorel b) :
    Measurable (fun q : GraphCode × ((EdgeCode → Y) × EdgeCode) =>
      decoder eval b q.1 q.2.1 q.2.2) :=
  joint_measurable_of_coordinates (decoder eval b) (measurable_decoder_edge eval heval b hb)

theorem decoder_equivariant {Y : Type*} (eval : Y → ℝ → ℝ)
    (b : GraphDrift) (hb : DriftEquivariant b)
    (σ : Equiv ℕ ℕ) (G : GraphCode) (W : EdgeCode → Y) (e : EdgeCode) :
    decoder eval b (relabelGraph σ G) (fun f => W (mapEdge σ.symm f)) (mapEdge σ e) =
      decoder eval b G W e := by
  classical
  have hp (t : ℝ) :
      Picard.decode (fun f => eval (W (mapEdge σ.symm f))) (b (relabelGraph σ G))
        (mapEdge σ e) t = Picard.decode (fun f => eval (W f)) (b G) e t := by
    apply Picard.decode_relabel (edgeEquiv σ) (fun f => eval (W f))
      (fun f => eval (W (mapEdge σ.symm f))) (b G) (b (relabelGraph σ G))
    · intro f s
      simp only [edgeEquiv_apply, mapEdge_symm_apply]
    · exact hb σ G
  simp only [decoder, hp]

theorem decoder_eq_rule {Y : Type*} (eval : Y → ℝ → ℝ) (b : GraphDrift)
    (Ψ : GraphCode → (ℕ → ℝ) → EdgeCode → Y) (G : GraphCode) (U : ℕ → ℝ) :
    decoder eval b G (Ψ G U) =
      FactorAssembly.rule b (fun G U e => eval (Ψ G U e)) G U := rfl

theorem exists_factor_of_decoder_law {Y : Type} [MeasurableSpace Y]
    [Nonempty Y] [StandardBorelSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    (eval : Y → ℝ → ℝ) (heval : Measurable (Function.uncurry eval))
    (b : GraphDrift) (hb : DriftBorel b) (heq : DriftEquivariant b)
    (hlaw : ∀ G : GraphCode, GraphConnected G → GraphLocallyFinite G →
      HasFUSFLaw G (Measure.infinitePi (fun _ : EdgeCode => ν)) (decoder eval b G)) :
    ∃ Phi : FactorRule, RuleBorel Phi ∧ RuleEquivariant Phi ∧
      ∀ G : GraphCode, WorksOnGraph Phi G :=
  factor_witness_of_all_pair_decoder ν (decoder eval b)
    (measurable_decoder eval heval b hb) (decoder_equivariant eval b heq) hlaw

end Problem336.AllPairPicardDecoder

end

end OAI
