import Mathlib
import OAI.Combinatorics.KMedian.Hardness.ProjectionInput
import OAI.Combinatorics.KMedian.Hardness.Sampling
import OAI.Combinatorics.KMedian.Projection.Repeat

namespace OAI

section Inline_PCPProjectionInput

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {u v d s a b : ℕ}
variable (G : BiProjection (Fin u) (Fin v) (Fin d) (Fin s) (Fin a) (Fin b))
def system : Coverage.ProjectionSystem (Fin u) (Fin v) (Fin s) (Fin a) (Fin b) where
  neighbor v s := (G.edge.symm (v,s)).1
  project v s := G.project (G.edge.symm (v,s))

lemma system_regular : G.system.LeftRegular d := by
  intro x
  change (univ.filter (fun p : Fin v × Fin s => (G.edge.symm p).1=x)).card=d
  rw [card_filter]
  calc
    _ = ∑ p : Fin u × Fin d, if p.1=x then 1 else 0 :=
      Equiv.sum_comp G.edge.symm (fun p : Fin u × Fin d => if p.1=x then (1:ℕ) else 0)
    _ = d := by
      simp only [Fintype.sum_prod_type]
      rw [sum_comm]
      simp
lemma system_consistent (h : G.Consistent) : G.system.DuplicateConsistent := by
  intro y i j he c
  let p := G.edge.symm (y,i)
  let q := G.edge.symm (y,j)
  have hp : G.edge p=(y,i) := G.edge.apply_symm_apply _
  have hq : G.edge q=(y,j) := G.edge.apply_symm_apply _
  have hx : p.1=q.1 := he
  have ht : (G.edge (p.1,p.2)).1=(G.edge (p.1,q.2)).1 := by
    have hq' : (p.1,q.2)=q := by rw [hx]
    simp only [Prod.eta,hq',hp,hq]
  change G.project p c=G.project q c
  have hh := h p.1 p.2 q.2 ht c
  have hq' : (p.1,q.2)=q := by rw [hx]
  simpa only [Prod.eta,hq'] using hh

noncomputable def input (hu : 0<u) (hv : 0<v) (hs : 0<s) (ha : 0<a) (hb : 0<b)
    (hc : G.Consistent) : Coverage.ProjectionInput s a b where
  u := u
  v := v
  u_pos := hu
  v_pos := hv
  r_pos := hs
  a_pos := ha
  b_pos := hb
  system := G.system
  degree := d
  regular := G.system_regular
  consistent := G.system_consistent hc

lemma input_perfect (hu : 0<u) (hv : 0<v) (hs : 0<s) (ha : 0<a) (hb : 0<b)
    (hc : G.Consistent) (h : G.Perfect) : (G.input hu hv hs ha hb hc).Perfect := by
  obtain ⟨left,right,h⟩ := h
  refine ⟨left,right,?_⟩
  intro y i
  have hh := h (G.edge.symm (y,i)).1 (G.edge.symm (y,i)).2
  simpa only [Prod.eta,Equiv.apply_symm_apply,input,system] using hh

variable [Nonempty (Fin u)] [Nonempty (Fin v)] [Nonempty (Fin d)] [Nonempty (Fin s)]
  [Nonempty (Fin a)] [Nonempty (Fin b)]
omit [Nonempty (Fin u)] [Nonempty (Fin v)] [Nonempty (Fin d)]
  [Nonempty (Fin s)] [Nonempty (Fin a)] [Nonempty (Fin b)] in
lemma system_score (left : Fin u → Fin a) (right : Fin v → Fin b) :
    ((G.system.satisfied left right).card : ℝ)/(v*s)=G.score left right := by
  have he := testRate_equiv G.edge.symm (fun p =>
    G.project p (left p.1)=right (G.edge p).1)
  simp only [Equiv.apply_symm_apply] at he
  have hl : testRate (fun p : Fin v × Fin s =>
      G.project (G.edge.symm p) (left (G.edge.symm p).1)=right p.1)=
      ((G.system.satisfied left right).card : ℝ)/(v*s) := by
    rw [testRate_eq_count]
    simp only [Coverage.ProjectionSystem.satisfied,system,Fintype.card_prod,
      Fintype.card_fin,Nat.cast_mul,Prod.eta]
    congr 2
  rw [hl] at he
  simpa only [testRate,expect_prod,score] using he
omit [Nonempty (Fin u)] [Nonempty (Fin v)] [Nonempty (Fin d)]
  [Nonempty (Fin s)] [Nonempty (Fin a)] [Nonempty (Fin b)] in
lemma input_sound (hu : 0<u) (hv : 0<v) (hs : 0<s) (ha : 0<a) (hb : 0<b)
    (hc : G.Consistent) {ε : ℝ} (h : G.Sound ε) : (G.input hu hv hs ha hb hc).Sound ε := by
  intro left right
  have hh := h left right
  rw [← G.system_score left right] at hh
  have hp : (0:ℝ)<v*s := mul_pos (Nat.cast_pos.mpr hv) (Nat.cast_pos.mpr hs)
  have hh' := (div_le_iff₀ hp).mp hh
  simpa only [input,mul_assoc] using hh'
end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionInput

end OAI
