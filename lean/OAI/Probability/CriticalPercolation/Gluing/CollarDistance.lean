import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def vertexCollar (B : Set V) (n : ℕ) : Set V := ⋃ b∈B, G.vertexBall b n

def distanceTo (B : Set V) (v : V) : ℕ :=
  if h : ∃ n, v∈G.vertexCollar B n then Nat.find h else 0

lemma vertexCollar_exists (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty) (v : V) :
    ∃ n, v∈G.vertexCollar B n := by
  obtain ⟨b,hb⟩ := hB
  obtain ⟨n,hn⟩ := G.reachable_mem_vertexBall (hc b v)
  exact ⟨n,Set.mem_iUnion₂.mpr ⟨b,hb,hn⟩⟩

lemma distanceTo_mem {B : Set V} {v : V} (h : ∃ n, v∈G.vertexCollar B n) :
    v∈G.vertexCollar B (G.distanceTo B v) := by
  simp only [distanceTo,dite_eq_left h]
  exact Nat.find_spec h

lemma distanceTo_le {B : Set V} {v : V} {n : ℕ} (h : v∈G.vertexCollar B n) :
    G.distanceTo B v ≤ n := by
  have he : ∃ k, v∈G.vertexCollar B k := ⟨n,h⟩
  simp only [distanceTo,dite_eq_left he]
  exact Nat.find_min' he h

lemma distanceTo_le_iff (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    (v : V) (n : ℕ) : G.distanceTo B v ≤ n ↔ v∈G.vertexCollar B n := by
  constructor
  · intro hn
    obtain ⟨b,hb,hv⟩ := Set.mem_iUnion₂.mp (G.distanceTo_mem (G.vertexCollar_exists hc hB v))
    have hmono : Monotone (G.vertexBall b) :=
      monotone_nat_of_le_succ fun _ => Set.subset_union_left
    exact Set.mem_iUnion₂.mpr ⟨b,hb,hmono hn hv⟩
  · exact G.distanceTo_le

lemma distanceTo_eq_zero_iff (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    (v : V) : G.distanceTo B v=0 ↔ v∈B := by
  rw [← Nat.le_zero,G.distanceTo_le_iff hc hB]
  simp [vertexCollar,vertexBall]

lemma distanceTo_adj (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    {v w : V} (hvw : G.fullGraph.Adj v w) : G.distanceTo B w ≤ G.distanceTo B v+1 := by
  obtain ⟨b,hb,hv⟩ := Set.mem_iUnion₂.mp (G.distanceTo_mem (G.vertexCollar_exists hc hB v))
  apply G.distanceTo_le
  exact Set.mem_iUnion₂.mpr ⟨b,hb,Or.inr (Set.mem_iUnion₂.mpr ⟨v,hv,hvw⟩)⟩

lemma distanceTo_ball (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    {v w : V} {n : ℕ} (hvw : w∈G.vertexBall v n) : G.distanceTo B w ≤ G.distanceTo B v+n := by
  induction n generalizing w with
  | zero =>
    have he : w=v := hvw
    subst w
    exact Nat.le_refl _
  | succ n ih =>
    rcases hvw with hvw|hvw
    · exact (ih hvw).trans (by omega)
    · obtain ⟨z,hz,hzw⟩ := Set.mem_iUnion₂.mp hvw
      have h1 := ih hz
      have h2 := G.distanceTo_adj hc hB hzw
      omega

lemma distanceTo_predecessor (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    (v : V) (hv : G.distanceTo B v≠0) :
    ∃ w, G.fullGraph.Adj v w ∧ G.distanceTo B w+1=G.distanceTo B v := by
  obtain ⟨n,heq⟩ := Nat.exists_eq_succ_of_ne_zero hv
  have hmem := G.distanceTo_mem (G.vertexCollar_exists hc hB v)
  rw [heq] at hmem
  obtain ⟨b,hb,hv⟩ := Set.mem_iUnion₂.mp hmem
  rcases hv with hv|hv
  · have hh : v∈G.vertexCollar B n := Set.mem_iUnion₂.mpr ⟨b,hb,hv⟩
    have := G.distanceTo_le hh
    omega
  · obtain ⟨w,hw,hwv⟩ := Set.mem_iUnion₂.mp hv
    have h1 := G.distanceTo_le (B := B) (Set.mem_iUnion₂.mpr ⟨b,hb,hw⟩)
    have h2 := G.distanceTo_adj hc hB hwv
    exact ⟨w,hwv.symm,by omega⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
