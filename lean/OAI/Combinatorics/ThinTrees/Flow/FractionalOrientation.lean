import Mathlib
import OAI.Combinatorics.ThinTrees.Flow.RootedRelaxation

namespace OAI

/-! Fractional orientation. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

def FlowPoint.Exact (G : MultiGraph n m) (c : Fin m → ℝ) (q : ℝ)
    (F : FlowPoint n m) : Prop :=
  (∀e, 0 ≤ F.x e ∧ F.x e ≤ c e) ∧
  (∀r e, 0 ≤ F.a r e ∧ 0 ≤ F.b r e ∧ F.x e = F.a r e+F.b r e) ∧
  (∀r v, out G (F.a r) (F.b r) v = if v=r then 0 else q) ∧
  (∑e, F.x e)=q*((n:ℝ)-1)

lemma out_sum {I : Type*} [Fintype I] (G : MultiGraph n m)
    (a b : I → Fin m → ℝ) (v : Fin n) :
    out G (fun e => ∑i, a i e) (fun e => ∑i, b i e) v = ∑i, out G (a i) (b i) v := by
  simp only [out]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  rw [sum_add_distrib]
  have hi (p : Prop) [Decidable p] (f : I → ℝ) : (if p then ∑i, f i else 0)=∑i, if p then f i else 0 := by
    split_ifs <;> simp
  rw [hi,hi]

lemma out_scale (G : MultiGraph n m) (a b : Fin m → ℝ) (α : ℝ) (v : Fin n) :
    out G (fun e => α*a e) (fun e => α*b e) v=α*out G a b v := by
  simp only [out,mul_sum,mul_add]
  apply sum_congr rfl
  intro e he
  split_ifs <;> ring

lemma FlowPoint.Exact.scale {G : MultiGraph n m} {c : Fin m → ℝ} {q : ℝ}
    {F : FlowPoint n m} (hF : F.Exact G c q) {α : ℝ} (hα : 0 ≤ α) :
    (FlowPoint.mk (fun e => α*F.x e) (fun r e => α*F.a r e) (fun r e => α*F.b r e)).Exact
      G (fun e => α*c e) (α*q) := by
  refine ⟨fun e => ⟨mul_nonneg hα (hF.1 e).1,mul_le_mul_of_nonneg_left (hF.1 e).2 hα⟩,
    fun r e => ⟨mul_nonneg hα (hF.2.1 r e).1,mul_nonneg hα (hF.2.1 r e).2.1,?_⟩,?_,?_⟩
  · simp only [(hF.2.1 r e).2.2,mul_add]
  · intro r v
    rw [out_scale,hF.2.2.1]
    split_ifs <;> simp
  · change (∑e, α*F.x e)=_
    rw [←mul_sum,hF.2.2.2]
    ring

lemma FlowPoint.Exact.mono {G : MultiGraph n m} {c d : Fin m → ℝ} {q : ℝ}
    {F : FlowPoint n m} (hF : F.Exact G c q) (hcd : ∀e, c e ≤ d e) : F.Exact G d q :=
  ⟨fun e => ⟨(hF.1 e).1, (hF.1 e).2.trans (hcd e)⟩,hF.2⟩

lemma packed_exact_flow (G : MultiGraph n m) (hn : 0 < n) {r : ℕ}
    (hpack : G.TreePackable univ r) :
    ∃F : FlowPoint n m, F.Exact G (fun _ => 1) r := by
  obtain ⟨T,hT,hdis⟩ := hpack
  let R (root : Fin n) (i : Fin r) : Rooted G (T i) root := Classical.choice (rooted_exists G (hT i).2 root)
  let F : FlowPoint n m := ⟨fun e => ∑i, if e ∈ T i then 1 else 0,
    fun root e => ∑i, (R root i).leftFlow e,
    fun root e => ∑i, (R root i).rightFlow e⟩
  refine ⟨F,?_,?_,?_,?_⟩
  · intro e
    constructor
    · change 0 ≤ ∑i : Fin r, if e ∈ T i then (1:ℝ) else 0
      exact sum_nonneg fun i _ => by split_ifs <;> norm_num
    · change (∑i, if e ∈ T i then (1:ℝ) else 0) ≤ 1
      rw [sum_boole]
      norm_cast
      apply card_le_one.mpr
      intro i hi j hj
      by_contra hij
      have h := disjoint_left.mp (hdis hij)
      exact h (mem_filter.mp hi).2 (mem_filter.mp hj).2
  · intro root e
    change 0 ≤ (∑i, (R root i).leftFlow e) ∧
      0 ≤ (∑i, (R root i).rightFlow e) ∧ _
    refine ⟨sum_nonneg fun i _ => (R root i).leftFlow_nonneg e,
      sum_nonneg fun i _ => (R root i).rightFlow_nonneg e,?_⟩
    change (∑i, if e ∈ T i then (1:ℝ) else 0)=(∑i, (R root i).leftFlow e)+(∑i, (R root i).rightFlow e)
    rw [←sum_add_distrib]
    exact sum_congr rfl fun i _ => ((R root i).edgeFlow e).symm
  · intro root v
    change out G (fun e => ∑i, (R root i).leftFlow e) (fun e => ∑i, (R root i).rightFlow e) v=_
    rw [out_sum]
    simp only [Rooted.out_eq]
    split_ifs <;> simp
  · change (∑e, ∑i, if e ∈ T i then (1:ℝ) else 0)=(r:ℝ)*((n:ℝ)-1)
    rw [sum_comm]
    have hs (i : Fin r) : (∑e, if e ∈ T i then (1:ℝ) else 0)=(n:ℝ)-1 := by
      rw [sum_boole,filter_mem_eq_inter,univ_inter,G.spanningTree_card hn (hT i).2]
      rw [Nat.cast_sub (show 1 ≤ n by omega),Nat.cast_one]
    simp only [hs,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]

def FlowPoint.push {M : ℕ} (π : Fin M → Fin m) (F : FlowPoint n M) : FlowPoint n m :=
  ⟨fun e => ∑f ∈ univ.filter (fun f => π f=e), F.x f,
    fun r e => ∑f ∈ univ.filter (fun f => π f=e), F.a r f,
    fun r e => ∑f ∈ univ.filter (fun f => π f=e), F.b r f⟩

lemma out_push {M : ℕ} (G : MultiGraph n m) (H : MultiGraph n M) (π : Fin M → Fin m)
    (hl : ∀e, G.left (π e)=H.left e) (hr : ∀e, G.right (π e)=H.right e)
    (F : FlowPoint n M) (root v : Fin n) :
    out G ((F.push π).a root) ((F.push π).b root) v=out H (F.a root) (F.b root) v := by
  have hi (p : Prop) [Decidable p] (s : Finset (Fin M)) (a : Fin M → ℝ) :
      (if p then ∑f ∈ s, a f else 0)=∑f ∈ s, if p then a f else 0 := by
    split_ifs <;> simp
  simp only [out,FlowPoint.push,hi,←sum_add_distrib]
  trans ∑e : Fin m, ∑f ∈ univ.filter (fun f => π f=e),
    ((if H.left f=v then F.a root f else 0)+(if H.right f=v then F.b root f else 0))
  · apply sum_congr rfl
    intro e he
    apply sum_congr rfl
    intro f hf
    have hfe := (mem_filter.mp hf).2
    rw [←hfe,hl,hr]
  · exact sum_fiberwise_of_maps_to (fun e _ => mem_univ (π e)) _

lemma FlowPoint.Exact.push {M : ℕ} (G : MultiGraph n m) (H : MultiGraph n M) (π : Fin M → Fin m)
    (hl : ∀e, G.left (π e)=H.left e) (hr : ∀e, G.right (π e)=H.right e)
    {c : Fin M → ℝ} {q : ℝ} {F : FlowPoint n M} (hF : F.Exact H c q) :
    (F.push π).Exact G (fun e => ∑f ∈ univ.filter (fun f => π f=e), c f) q := by
  refine ⟨?_,?_,?_,?_⟩
  · intro e
    change 0 ≤ (∑f ∈ univ.filter (fun f => π f=e), F.x f) ∧
      (∑f ∈ univ.filter (fun f => π f=e), F.x f) ≤ (∑f ∈ univ.filter (fun f => π f=e), c f)
    exact ⟨sum_nonneg fun f _ => (hF.1 f).1,sum_le_sum fun f _ => (hF.1 f).2⟩
  · intro r e
    change 0 ≤ (∑f ∈ univ.filter (fun f => π f=e), F.a r f) ∧
      0 ≤ (∑f ∈ univ.filter (fun f => π f=e), F.b r f) ∧ _
    refine ⟨sum_nonneg fun f _ => (hF.2.1 r f).1,
      sum_nonneg fun f _ => (hF.2.1 r f).2.1,?_⟩
    change (∑f ∈ univ.filter (fun f => π f=e), F.x f)=_
    simp only [FlowPoint.push,←sum_add_distrib]
    exact sum_congr rfl fun f _ => (hF.2.1 r f).2.2
  · intro r v
    rw [out_push G H π hl hr]
    exact hF.2.2.1 r v
  · change (∑e, ∑f ∈ univ.filter (fun f => π f=e), F.x f)=_
    rw [sum_fiberwise_of_maps_to (fun f _ => mem_univ (π f)),hF.2.2.2]

end
end AlgorithmicThinTrees.Orientations
end

end OAI
