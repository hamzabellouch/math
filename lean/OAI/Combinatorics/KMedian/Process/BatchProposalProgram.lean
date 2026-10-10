import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalBatchFacts
import OAI.Combinatorics.KMedian.Process.PhysicalBatchProgram
import OAI.Combinatorics.KMedian.Process.BatchOrdinalArrays

namespace OAI


                                            
section
namespace MetricKMedian.RationalBatchData.ProposalProgram
open Finset FixedBatch Binary Binary.PolyProgram
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
variable {C : Type} (I : C → Type) [∀ c, LinearOrder (I c)] [∀ c, Fintype (I c)]

structure Input where
  ctx : C
  n : ℕ
  enum : Fin n ≃o I ctx
  G : I ctx → Finset (I ctx)
  Δ : ℕ
  g : ℚ
  b : ℚ
  p : ℚ
  φ : ℚ
  hp : 0≤p
  hφ : 0≤φ
  hupper : (1+φ)*p≤1
variable {I}

def Input.raw (x : Input I) : GraphData.Raw :=
  (((x.g,x.b),(x.Δ,(x.p,x.φ))),Ordinal.graphView x.enum x.G)
abbrev Input.encode (x : Input I) := Binary.Automatic.enc x.raw

def Input.enumActions (x : Input I) := enumeration (graph x.G) (heavySet (graphMass x.G x.g) x.b)
def Input.batch (x : Input I) : SparsePhysicalBatch.Program.Input where
  n := Fintype.card (HeavyAction (graph x.G) (heavySet (graphMass x.G x.g) x.b))
  Z := (balanced (heavy (graph x.G) (heavySet (graphMass x.G x.g) x.b)) x.Δ).map x.enumActions.symm.toEmbedding
  C := fun i => (conflicts (heavy (graph x.G) (heavySet (graphMass x.G x.g) x.b)) x.Δ (x.enumActions i)).map x.enumActions.symm.toEmbedding
  p := x.p
  q := fun i => bias (graphMass x.G x.g) x.p x.φ (heavyParent (graph x.G) _ (x.enumActions i))
  hp := ⟨x.hp,by have h := mul_nonneg x.hp x.hφ; nlinarith only [h,x.hupper]⟩
  hq := fun _ => bias_probability (graphMass x.G x.g) x.hp x.hφ x.hupper _
def Input.law (x : Input I) := proposal x.G x.Δ x.g x.b x.p x.φ x.hp x.hφ x.hupper x.enumActions
def Input.result (x : Input I) : Data Row :=
  (((x.law).law.denominator,List.ofFn (x.law).law.numerator),
    x.law.states.toList.map (fun Z => setView (Z.map x.enumActions.symm.toEmbedding)))

 theorem data_input (x : Input I) : GraphData.data x.raw=x.batch.raw := by
  unfold GraphData.data Input.raw
  rw [Ordinal.prepare_graph,Ordinal.data_view]
  rfl
noncomputable def inputProgram : PolyProgram (Input.encode (I:=I)) SparsePhysicalBatch.Program.Input.encode Input.batch :=
  GraphData.data_poly.program.recode Input.raw (fun _ => rfl) (fun x => congrArg Binary.Automatic.enc (data_input x))

 theorem result_eq (x : Input I) : x.batch.result=x.result := by
  unfold Input.result Input.law proposal SparseEnumeratedBatch.law
  simp only [SparseIntegerLaw.map,Vector.toList_map,List.map_map,Function.comp_def]
  change x.batch.result=(((SparsePhysicalBatch.law x.batch.Z x.batch.C x.batch.p x.batch.q x.batch.hp x.batch.hq).law.denominator,
    List.ofFn (SparsePhysicalBatch.law x.batch.Z x.batch.C x.batch.p x.batch.q x.batch.hp x.batch.hq).law.numerator),_)
  unfold SparsePhysicalBatch.Program.Input.result
  congr 1
  apply List.map_congr_left
  intro Z hZ
  clear hZ
  dsimp only [Input.batch] at Z ⊢
  congr 1
  ext i
  simp only [mem_map_equiv,Equiv.symm_symm,Equiv.symm_apply_apply]

noncomputable def program : PolyProgram (Input.encode (I:=I)) (ed SparseGraph.ListOperation.er) Input.result :=
  (inputProgram.comp SparsePhysicalBatch.Program.program).congr _ (fun x => result_eq x)
end MetricKMedian.RationalBatchData.ProposalProgram
end

end OAI
