import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PoweringMean
import OAI.Combinatorics.KMedian.Amplification.PoweringMoment
import OAI.Combinatorics.KMedian.PCP.AlphabetReduction

namespace OAI

section Inline_PCPPoweringConstruction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph.Walk
variable {V D : Type} {G : PortGraph V D}
@[simp] lemma cast_start {n m : ℕ} (h : n=m) (p : G.Walk n) :
    (p.cast h).vertex 0 = p.vertex 0 := by subst m; rfl
@[simp] lemma cast_end {n m : ℕ} (h : n=m) (p : G.Walk n) :
    (p.cast h).vertex (Fin.last m) = p.vertex (Fin.last n) := by subst m; rfl
lemma center_left_far (i j : ℕ) (p : G.Walk (i+(j+1))) :
    (ofWord (G := G) (centerEquiv i j p).1.1 (centerEquiv i j p).1.2).vertex (Fin.last i) =
      p.vertex 0 := by
  simpa only [Equiv.symm_apply_apply] using (center_left_end (G := G) i j (centerEquiv i j p)).symm
lemma center_right_far (i j : ℕ) (p : G.Walk (i+(j+1))) :
    (ofWord (G := G) (G.step (centerEquiv i j p).1.1 (centerEquiv i j p).2.1)
      (centerEquiv i j p).2.2).vertex (Fin.last j) = p.vertex (Fin.last (i+(j+1))) := by
  simpa only [Equiv.symm_apply_apply] using (center_right_end (G := G) i j (centerEquiv i j p)).symm
end PortGraph.Walk

namespace PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) {cap : ℕ}
open PortGraph

def CutAccept (i j : ℕ) (p : G.Walk (i+(j+1))) (b c : Advice D A cap) : Prop :=
  let z := Walk.centerEquiv i j p
  (b.get i (Walk.ofWord (G := G) z.1.1 z.1.2).reverse.port,
   c.get j (Walk.ofWord (G := G) (G.step z.1.1 z.2.1) z.2.2).reverse.port) ∈ C.allowed (z.1.1,z.2.1)

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] [DecidableEq A] in
lemma cutAccept_iff (a : V → Advice D A cap) (i j : ℕ) (p : G.Walk (i+(j+1))) :
    C.CutAccept i j p (a (p.vertex 0)) (a (p.vertex (Fin.last (i+(j+1))))) ↔
      (G.opinion a i (Walk.centerEquiv i j p).1.1 (Walk.centerEquiv i j p).1.2,
       G.opinion a j (G.step (Walk.centerEquiv i j p).1.1 (Walk.centerEquiv i j p).2.1)
          (Walk.centerEquiv i j p).2.2) ∈
        C.allowed ((Walk.centerEquiv i j p).1.1,(Walk.centerEquiv i j p).2.1) := by
  unfold CutAccept opinion
  rw [Walk.center_left_far,Walk.center_right_far]

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] in
lemma accepted_cut_zero (a : V → Advice D A cap) (x : V → A) (i j : ℕ)
    (p : G.Walk (i+(j+1)))
    (h : C.CutAccept i j p (a (p.vertex 0)) (a (p.vertex (Fin.last (i+(j+1)))))) :
    C.cutHit a x i j p = 0 := by
  classical
  have hh := (C.cutAccept_iff a i j p).mp h
  unfold cutHit rootHit
  split_ifs with hleft hright <;> simp only [mul_one,mul_zero]
  rw [hleft,hright] at hh
  have hn : ¬ C.Bad x ((Walk.centerEquiv i j p).1.1,(Walk.centerEquiv i j p).2.1) :=
    not_not.mpr hh
  exact ite_eq_right hn

def PathAccept (n : ℕ) (p : G.Walk n) (b c : Advice D A cap) : Prop :=
  ∀ i j : Fin (cap+1), ∀ h : n=i.val+(j.val+1), C.CutAccept i.val j.val (p.cast h) b c

noncomputable def stoppedPath (t : ℕ) (z : (Fin cap → Fin (t+1)) × G.Walk cap) :
    G.Walk (Stopped.length t cap z.1) :=
  z.2.segment 0 (Stopped.length t cap z.1) (by have := Stopped.length_le t cap z.1; omega)

abbrev PowerEdge (t cap : ℕ) := (Fin cap → Fin (t+1)) × G.Walk cap

noncomputable def powered (t : ℕ) : BinaryCSP V (PowerEdge (G := G) t cap) (Advice D A cap) := by
  classical
  exact {
    left z := (stoppedPath t z).vertex 0
    right z := (stoppedPath t z).vertex (Fin.last (Stopped.length t cap z.1))
    allowed z := univ.filter (fun bc => C.PathAccept _ (stoppedPath t z) bc.1 bc.2) }

omit [Fintype V] [Nonempty V] [Nonempty D] [DecidableEq A] in
@[simp] lemma powered_allowed (t : ℕ) (z : PowerEdge (G := G) t cap) (b c : Advice D A cap) :
    (b,c) ∈ (C.powered (cap := cap) t).allowed z ↔ C.PathAccept _ (stoppedPath t z) b c := by
  classical
  simp [powered]

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] [DecidableEq A] in
lemma honest_cut (x : V → A) (hx : C.Satisfies x) (i j : ℕ) (hi : i ≤ cap) (hj : j ≤ cap)
    (p : G.Walk (i+(j+1))) :
    C.CutAccept i j p ((G.honest x : V → Advice D A cap) (p.vertex 0))
      ((G.honest x : V → Advice D A cap) (p.vertex (Fin.last (i+(j+1))))) := by
  rw [cutAccept_iff, G.honest_opinion x i hi, G.honest_opinion x j hj]
  exact hx _ _

omit [Fintype V] [Nonempty V] [Nonempty D] [DecidableEq A] in
theorem powered_complete (x : V → A) (hx : C.Satisfies x) (t : ℕ) :
    (C.powered (cap := cap) t).Satisfies (G.honest x) := by
  intro z
  rw [powered_allowed]
  intro i j h
  have hi : i.val ≤ cap := by omega
  have hj : j.val ≤ cap := by omega
  have hh := C.honest_cut x hx i.val j.val hi hj ((stoppedPath t z).cast h)
  simpa only [powered,Walk.cast_start,Walk.cast_end] using hh

omit [Fintype V] [Nonempty V] [Nonempty D] in
lemma accepted_witness_zero (a : V → Advice D A cap) (x : V → A) (t L : ℕ)
    (hL : L ≤ cap) (z : PowerEdge (G := G) t cap)
    (hz : (a ((C.powered (cap := cap) t).left z),a ((C.powered (cap := cap) t).right z)) ∈
      (C.powered (cap := cap) t).allowed z) :
    C.stoppedWitness a x t L z = 0 := by
  have ha := (C.powered_allowed t z _ _).mp hz
  unfold stoppedWitness witness
  apply sum_eq_zero
  intro i hi
  apply sum_eq_zero
  intro j hj
  unfold diagHit
  split_ifs with h
  · have hic : i < cap+1 := by simp only [mem_range] at hi; omega
    have hjc : j < cap+1 := by simp only [mem_range] at hj; omega
    have hh := ha ⟨i,hic⟩ ⟨j,hjc⟩ h
    apply C.accepted_cut_zero a x i j _
    simpa only [powered,Walk.cast_start,Walk.cast_end,stoppedPath] using hh
  · rfl

omit [Nonempty V] [Nonempty D] in
theorem support_le_powered (a : V → Advice D A cap) (x : V → A) (t L : ℕ) (hL : L ≤ cap) :
    testRate (fun z => C.stoppedWitness a x t L z ≠ 0) ≤ (C.powered (cap := cap) t).rejection a := by
  apply testRate_mono
  intro z hz ha
  exact hz (C.accepted_witness_zero a x t L hL z ha)

theorem powered_sound (hG : G.Contracts (1/2)) (a : V → Advice D A cap)
    (t L : ℕ) (hcap : 2*L+1 < cap) :
    ((t:ℝ) * testRate (C.Bad (G.plurality a t L)) *
      (PortGraph.totalMass t L / Fintype.card A)^2)^2 ≤
    (C.powered (cap := cap) t).rejection a *
      (5*cap*testRate (C.Bad (G.plurality a t L)) +
        (cap:ℝ)^2*(testRate (C.Bad (G.plurality a t L)))^2) := by
  have h := C.witness_support_bound hG a t L hcap
  have hs := C.support_le_powered a (G.plurality a t L) t L (by omega)
  have hd := testRate_nonneg (C.Bad (G.plurality a t L))
  exact h.trans (mul_le_mul_of_nonneg_right hs (by positivity))

omit [Nonempty V] [Nonempty D] in
theorem powered_edges (t : ℕ) :
    Fintype.card (PowerEdge (G := G) t cap) =
      ((t+1)^cap * Fintype.card D ^ cap) * Fintype.card V := by
  rw [Fintype.card_prod,PortGraph.Walk.card]
  simp only [Fintype.card_fun,Fintype.card_fin]
  ring

end PortCSP
end MetricKMedian.PCP

end Inline_PCPPoweringConstruction

end OAI
