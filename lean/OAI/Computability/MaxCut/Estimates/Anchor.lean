import Mathlib
import OAI.Computability.MaxCut.Encoding.AdjacencyBits

namespace OAI

noncomputable section
namespace OptimalMaxCut
open scoped BigOperators
open LongCode.InstanceAdapter CounterMachine
attribute [local instance] Classical.propDecidable

@[simp] theorem nameBits_length_exact (n : ℕ) :
    (MaxCutGames.BinaryEncoding.nameBits n).length = 2*n.size+1 := by
  exact MaxCutGames.BinaryEncoding.nameBits_length n

theorem nameBits_getD (n i : ℕ) :
    ((MaxCutGames.BinaryEncoding.nameBits n)[i]?).getD false =
      decide (RawGrid.frameValue n i ≠ 0) := by
  have he (s : List Bool) : MaxCutGames.BinaryEncoding.frame s = CounterMachine.frame s := by
    induction s with
    | nil => rfl
    | cons b s ih => simp only [MaxCutGames.BinaryEncoding.frame,CounterMachine.frame,ih]
  unfold MaxCutGames.BinaryEncoding.nameBits
  rw [he]
  exact CounterMachine.frame_bits_get n i

@[simp] theorem Graph.table_length (G : Graph) :
    ((List.finRange G.vertices).flatMap (fun u =>
      (List.finRange G.vertices).map (fun v => G.adj u v))).length = G.vertices^2 := by
  simp [List.length_flatMap, pow_two]

theorem Graph.table_getD (G : Graph) (i j : ℕ) (hi : i<G.vertices) (hj : j<G.vertices) :
    (((List.finRange G.vertices).flatMap (fun u =>
      (List.finRange G.vertices).map (fun v => G.adj u v)))[i*G.vertices+j]?).getD false =
      G.adj ⟨i,hi⟩ ⟨j,hj⟩ := by
  have h := flatMap_getD (List.finRange G.vertices)
    (fun u => (List.finRange G.vertices).map (fun v => G.adj u v)) false G.vertices
    (by intros; simp) ⟨i,by simpa using hi⟩ j hj
  simpa [Fin.getElem_fin, List.getElem?_eq_getElem, hj] using h

@[simp] theorem ScaledGraph.bits_length_exact (G : ScaledGraph) :
    G.bits.length = (2*G.graph.vertices.size+1)+(2*G.scale.size+1)+G.graph.vertices^2 := by
  simp only [ScaledGraph.bits,List.length_append,nameBits_length_exact,Graph.table_length]

namespace LongCode.InstanceAdapter
open MaxCutGames.Foundations.Target

def anchor {q : ℕ} (g : Instance q) : Fin (g.vertices*2^q) :=
  vertexEquiv g.vertices q (g.constraints[0]'(g.constraintCount_positive) |>.source, fun _ => false)

noncomputable def gridGraph {q : ℕ} (g : Instance q) (t : ℚ)
    (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ) : ScaledGraph :=
  (ofInstance g).gridOutput t ht (vertexEquiv g.vertices q) (anchor g) K
end LongCode.InstanceAdapter

namespace RawGrid
open LongCode.InstanceAdapter MaxCutGames.Foundations.Target
@[simp] theorem size_bits {q : ℕ} (g : Instance q) (L : ℕ) :
    size q L (bits g) = g.vertices*2^q*(Unweighted.searchPrime (L*(g.vertices*2^q+1)^2))^6 := by
  simp [size,param]

 theorem graph_size {q : ℕ} (g : Instance q) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ) :
    (gridGraph g t ht K).graph.vertices = size q (K+1) (bits g) := by
  simp [gridGraph,LongCode.Game.gridOutput,Unweighted.deterministicOutput,
    Unweighted.blowupOutput,Unweighted.blowupGraph]

 theorem graph_scale {q : ℕ} (g : Instance q) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ) :
    (gridGraph g t ht K).scale = scale q (K+1) (bits g) := by
  simp [gridGraph,LongCode.Game.gridOutput,Unweighted.deterministicOutput,
    Unweighted.blowupOutput,scale,param]

 theorem bits_length {q : ℕ} (g : Instance q) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ) :
    (gridGraph g t ht K).bits.length = length q (K+1) (bits g) := by
  rw [ScaledGraph.bits_length_exact, graph_size, graph_scale]; rfl

 theorem graph_adj {q : ℕ} (g : Instance q) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ)
    (i j : Fin (gridGraph g t ht K).graph.vertices) :
    (gridGraph g t ht K).graph.adj i j =
      decide (adjacency q t ht K (K+1) (bits g) i.val j.val ≠ 0) :=
  adjacency_bits g t ht K (K+1) (anchor g) i j

 theorem bits_getD {q : ℕ} (g : Instance q) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ)
    (i : ℕ) (hi : i<length q (K+1) (bits g)) :
    (((gridGraph g t ht K).bits)[i]?).getD false =
      decide (entry q t ht K (K+1) (bits g) i ≠ 0) := by
  let G := gridGraph g t ht K
  let d := 2*(size q (K+1) (bits g)).size+1
  let e := 2*(scale q (K+1) (bits g)).size+1
  have hd : (MaxCutGames.BinaryEncoding.nameBits G.graph.vertices).length = d := by
    rw [nameBits_length_exact,graph_size]
  have he : (MaxCutGames.BinaryEncoding.nameBits G.scale).length = e := by
    rw [nameBits_length_exact,graph_scale]
  simp only [ScaledGraph.bits, List.append_assoc]
  unfold entry
  by_cases hid : i<d
  · rw [List.getElem?_append_left (by rwa [hd]), nameBits_getD, graph_size]
    simp only [show i<2*(size q (K+1) (bits g)).size+1 from hid,↓reduceIte]
  · rw [List.getElem?_append_right (by rw [hd]; omega),hd]
    by_cases hie : i<d+e
    · rw [List.getElem?_append_left (by rw [he]; omega),nameBits_getD,graph_scale]
      simp only [show ¬i<2*(size q (K+1) (bits g)).size+1 from hid,↓reduceIte,
        show i<(2*(size q (K+1) (bits g)).size+1)+(2*(scale q (K+1) (bits g)).size+1) from hie,↓reduceIte]
      rfl
    · rw [List.getElem?_append_right (by rw [he]; omega),he]
      simp only [show ¬i<2*(size q (K+1) (bits g)).size+1 from hid,↓reduceIte,
        show ¬i<(2*(size q (K+1) (bits g)).size+1)+(2*(scale q (K+1) (bits g)).size+1) from hie,↓reduceIte]
      have hlen : i-d-e < G.graph.vertices^2 := by
        rw [graph_size]; dsimp [length,d,e] at *; omega
      have hn : 0<G.graph.vertices := by nlinarith
      have hij : i-d-e < G.graph.vertices*G.graph.vertices := by simpa only [pow_two] using hlen
      have hrow := (Nat.div_lt_iff_lt_mul hn).mpr hij
      have hcol := Nat.mod_lt (i-d-e) hn
      have h := G.graph.table_getD ((i-d-e)/G.graph.vertices) ((i-d-e)%G.graph.vertices) hrow hcol
      rw [Nat.mul_comm ((i-d-e)/G.graph.vertices) _, Nat.div_add_mod] at h
      rw [h,graph_adj]
      simp only [G,graph_size,d,e]
end RawGrid
end OptimalMaxCut

end

end OAI
