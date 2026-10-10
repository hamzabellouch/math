import Mathlib
import OAI.Combinatorics.Chromatic.Walls.ForwardChartMutation
import OAI.Combinatorics.Chromatic.Walls.PolynomialIncomingProbes

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits
open Classical
noncomputable section
variable {n:ℕ} {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (hnd:∀r≠0,∃m,Ω r m≠0)

def vertexDisplay (d:Fin (n+1) → M) (w:Cell n → M) : Vertex n (Cell n) → M := Sum.elim d w
omit [AddCommGroup M] in
lemma vertexDisplay_update (d:Fin (n+1) → M) (w:Cell n → M) (b:Cell n) (w':M) :
    vertexDisplay d (Function.update w b w')=Function.update (vertexDisplay d w) (.inr b) w' := by
  funext a
  cases a with
  | inl a => simp [vertexDisplay]
  | inr a => by_cases h:a=b <;> simp [vertexDisplay,h]

include hΩ he hS hcomp hnd in
lemma freeChart_polynomial_step (ch:FreeChart (I:=I) e) (is:List I)
    (his:is.Nodup) (hall:∀i,i∈is)
    (d:Fin (n+1) → M) (w:Cell n → M) (b:Cell n) (q:List (Cell n))
    (hb:b∉q) (hinv:(is.map (simpleRoot ch.roots)).Perm (forwardInventory d w (b::q)))
    (p:M) (hp:p=w b-d b.1.castSucc)
    (hd:∀j,Ω p (d j)=(if j=b.1.castSucc then 1 else 0)-(if j=b.1.succ then 1 else 0))
    (hw:∀c,Ω p (w c)=if c=b then 1 else 0)
    (hdd:Ω (d b.1.castSucc) (d b.1.succ)=0) {N:ℕ} (f:ElementaryExpr N) :
    ∃pc:I,simpleRoot ch.roots pc=p ∧
      (is.map (simpleRoot (ch.mutate Ω pc).roots)).Perm
        (forwardInventory d (Function.update w b (d b.1.succ+p)) (q++[b])) ∧
      ∀r,polynomialSectionIncoming Ω ch.roots ch.coord
          (f.eval LaurentRay.vUnit Ω (vertexDisplay d w)) r=
        polynomialSectionIncoming Ω (ch.mutate Ω pc).roots (ch.mutate Ω pc).coord
          (f.eval LaurentRay.vUnit Ω (vertexDisplay d (Function.update w b (d b.1.succ+p))))
          (mutationIncomingLabel Ω p r) := by
  obtain ⟨pc,hpc,hpi⟩:=freeChart_inventory_step Ω ch is his hall d w b q hb hinv p hp hd hw
  cases hpc
  refine ⟨pc,rfl,hpi,?_⟩
  have hF:PureInitialRelation Ω hΩ ch.roots ch.coord ch.retract pc
      (f.eval LaurentRay.vUnit Ω (vertexDisplay d w))
      (f.eval LaurentRay.vUnit Ω (vertexDisplay d (Function.update w b (d b.1.succ+simpleRoot ch.roots pc)))) := by
    unfold PureInitialRelation
    rw [vertexDisplay_update]
    symm
    apply ElementaryExpr.rotation LaurentRay.vUnit Ω hΩ _ (simpleRoot ch.roots pc) _ (vertexDisplay d w)
      (.inl b.1.castSucc) (.inr b) (.inl b.1.succ) (by simp) (by simp)
      (by simp [Fin.ext_iff]) _ _ _ hdd _ f
    · change w b=d b.1.castSucc+simpleRoot ch.roots pc
      rw [hp]; abel
    · change Ω (simpleRoot ch.roots pc) (d b.1.castSucc)=1
      rw [hd]; simp [Fin.ext_iff]
    · change Ω (simpleRoot ch.roots pc) (d b.1.succ)= -1
      rw [hd]; simp [Fin.ext_iff]
    · intro x hxa hxb hxc
      cases x with
      | inl a =>
        change Ω (simpleRoot ch.roots pc) (d a)=0
        rw [hd]
        have ha:a≠b.1.castSucc:=by simpa using hxa
        have hc:a≠b.1.succ:=by simpa using hxc
        simp [ha,hc]
      | inr c =>
        change Ω (simpleRoot ch.roots pc) (w c)=0
        rw [hw,ite_eq_right (by simpa using hxb)]
  obtain ⟨L,hL⟩:=rootDegreeCovector_exists ch.roots e ch.independent
  intro r
  have H:=polynomialSectionIncoming_mutation Ω hΩ ch.roots ch.coord ch.retract pc e he S hS hcomp
    L hL hnd ch.independent _ _ hF r
  simpa only [FreeChart.mutate] using H
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n:ℕ}

def periodBridge (L:ℕ) (c:Cell n) : Lattice n (Cell n) :=
  bridge c+(L:ℤ) • delta cellLevel c

def partialBridge (L:ℕ) (pre:List (Cell n)) (c:Cell n) : Lattice n (Cell n) :=
  bridge c+((L:ℤ)+(if c∈pre then 1 else 0)) • delta cellLevel c
@[simp] lemma partialBridge_nil (L:ℕ) : partialBridge (n:=n) L []=periodBridge L := by
  funext c
  simp [partialBridge,periodBridge]
@[simp] lemma partialBridge_cycle (L:ℕ) : partialBridge (n:=n) L (phaseCycle n)=periodBridge (L+1) := by
  funext c
  simp [partialBridge,periodBridge,Nat.cast_add]
lemma partialBridge_scheduled (L:ℕ) {pre post:List (Cell n)} {b:Cell n}
    (hc:phaseCycle n=pre++b::post) : partialBridge L pre=scheduledBridge L b := by
  funext c
  simp only [partialBridge,scheduledBridge,prefix_before hc]
lemma eventRoot_partial (L:ℕ) {pre post:List (Cell n)} {b:Cell n}
    (hc:phaseCycle n=pre++b::post) : eventRoot cellLevel L b=partialBridge L pre b-anchor b.1.castSucc := by
  rw [partialBridge_scheduled L hc,scheduledBridge_self]
  simp only [eventRoot,cellLevel]
  abel
lemma cycle_head_not_mem {pre post:List (Cell n)} {b:Cell n}
    (hc:phaseCycle n=pre++b::post) : b∉post++pre := by
  have hn:=phaseCycle_nodup (n:=n)
  rw [hc] at hn
  obtain ⟨hpre,hrest,hdis⟩:=List.nodup_append.mp hn
  have hpost: b∉post:=(List.nodup_cons.mp hrest).1
  have hp:b∉pre:=fun hb=>hdis b hb b (by simp) rfl
  simpa using And.intro hpost hp

lemma partialBridge_step (L:ℕ) (pre:List (Cell n)) (b:Cell n) (_hb:b∉pre) :
    partialBridge L (pre++[b])=
      Function.update (partialBridge L pre) b (anchor b.1.succ+eventRoot cellLevel L b) := by
  funext c
  by_cases hc:c=b
  · subst c
    simp only [partialBridge,List.mem_append,List.mem_singleton,or_true,ite_true,Function.update_self,
      eventRoot,delta,cellLevel,add_zsmul,one_zsmul]
    abel
  · simp only [partialBridge,List.mem_append,List.mem_singleton,hc,or_false,
      Function.update_of_ne hc]

lemma periodFunctional_anchor (i:Fin n) (L:ℕ) (a:Fin (n+1)) :
    periodFunctional cellLevel i L (anchor a)=if a.val≤ i.val then 1 else 0 := by
  change cutPrefix cellLevel i (anchor a)+(L:ℤ) • levelTotal cellLevel i (anchor a)=_
  rw [levelTotal_anchor,smul_zero,add_zero]
  exact cutPrefix_single cellLevel i (.inl a) 1
lemma periodFunctional_bridge (i:Fin n) (L:ℕ) (b:Cell n) :
    periodFunctional cellLevel i L (periodBridge L b)=if b.1.val≤ i.val then 1 else 0 := by
  have hb:eventRoot cellLevel L b=periodBridge L b-anchor b.1.castSucc:=by
    unfold eventRoot periodBridge cellLevel; abel
  have H:=periodFunctional_eventRoot cellLevel i L b
  rw [hb,map_sub,periodFunctional_anchor] at H
  simpa only [Fin.val_castSucc] using sub_eq_zero.mp H

lemma gaps_cut_nonpos {M:Type*} [AddCommGroup M] (ell:M →+ ℤ) (a c:M) (bs:List M) (K:ℤ)
    (ha:K≤ell a) (hc:ell c≤K) (hb:∀b∈bs,ell b=K) :
    ∀r∈ForwardChain.gaps a bs c,ell r≤0 := by
  induction bs generalizing a with
  | nil =>
    intro r hr
    have hr:r=c-a:=by simpa [ForwardChain.gaps] using hr
    rw [hr,map_sub]
    omega
  | cons b bs ih =>
    have hbb:=hb b (by simp)
    intro r hr
    rcases List.mem_cons.mp hr with hr|hr
    · rw [hr,map_sub,hbb]; omega
    · apply ih b (by omega) (fun x hx=>hb x (by simp [hx])) r hr

lemma periodInventory_cut_nonpos (i:Fin n) (L:ℕ) (q:List (Cell n)) :
    ∀r∈forwardInventory anchor (periodBridge L) q,periodFunctional cellLevel i L r≤0 := by
  intro r hr
  obtain ⟨j,_,hr⟩:=List.mem_flatMap.mp hr
  apply gaps_cut_nonpos (periodFunctional cellLevel i L) (anchor j.castSucc) (anchor j.succ)
    ((levelQueue q j).map (periodBridge L)) (if j.val≤ i.val then 1 else 0) _ _ _ r hr
  · rw [periodFunctional_anchor]; rfl
  · rw [periodFunctional_anchor]
    simp only [Fin.val_succ]
    split_ifs <;> omega
  · intro x hx
    obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hx
    have hbj: b.1=j:=(mem_levelQueue q j b).mp hb |>.2
    rw [periodFunctional_bridge,hbj]

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
