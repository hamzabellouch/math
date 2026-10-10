import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PolynomialSection
import OAI.Combinatorics.Chromatic.Walls.RealLatticeRealization
import OAI.Combinatorics.Chromatic.Walls.ForwardPolynomialMutation

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
variable (h:Lattice n (Cell n) →+ M) (hform:∀x y,Ω (h x) (h y)=triangularOmega n x y)

include hform in
lemma mutationIncomingLabel_map (p m:Lattice n (Cell n)) :
    mutationIncomingLabel Ω (h p) (h m)=h (mutationIncomingLabel (triangularOmega n) p m) := by
  simp only [mutationIncomingLabel,hform,map_add,map_zsmul]

include hΩ he hS hcomp hnd hform in
lemma partial_period_transport (is:List I) (his:is.Nodup) (hall:∀i,i∈is)
    (L:ℕ) (rest:List (Cell n)) (pre:List (Cell n))
    (hcycle:phaseCycle n=pre++rest) (ch:FreeChart (I:=I) e)
    (hinv:(is.map (simpleRoot ch.roots)).Perm
      (forwardInventory (h ∘ anchor) (h ∘ partialBridge L pre) (rest++pre)))
    {N:ℕ} (f:ElementaryExpr N) :
    ∃ch':FreeChart (I:=I) e,
      (is.map (simpleRoot ch'.roots)).Perm
        (forwardInventory (h ∘ anchor) (h ∘ periodBridge (L+1)) (phaseCycle n)) ∧
      ∀m,polynomialSectionIncoming Ω ch.roots ch.coord
          (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ partialBridge L pre))) (h m)=
        polynomialSectionIncoming Ω ch'.roots ch'.coord
          (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge (L+1))))
          (h (rest.foldl (rotate (triangularOmega n) cellLevel L) m)) := by
  induction rest generalizing pre ch with
  | nil =>
    have hpre:pre=phaseCycle n:=by simpa using hcycle.symm
    subst pre
    refine ⟨ch,?_,?_⟩
    · simpa only [List.nil_append,partialBridge_cycle] using hinv
    · intro m
      simp only [partialBridge_cycle,List.foldl_nil]
  | cons b post ih =>
    have hb:=cycle_head_not_mem hcycle
    have hbp:b∉pre:=fun hh=>hb (List.mem_append.mpr (Or.inr hh))
    have hp:h (eventRoot cellLevel L b)= (h ∘ partialBridge L pre) b - (h ∘ anchor) b.1.castSucc:=by
      rw [eventRoot_partial L hcycle,map_sub]
      rfl
    have hd:∀j,Ω (h (eventRoot cellLevel L b)) ((h ∘ anchor) j)=
        (if j=b.1.castSucc then 1 else 0)-(if j=b.1.succ then 1 else 0):=by
      intro j
      exact (hform _ _).trans (scheduledRoot_anchor L b j)
    have hw:∀c,Ω (h (eventRoot cellLevel L b)) ((h ∘ partialBridge L pre) c)=if c=b then 1 else 0:=by
      intro c
      change Ω (h (eventRoot cellLevel L b)) (h (partialBridge L pre c))=_
      rw [hform,partialBridge_scheduled L hcycle]
      exact scheduledRoot_bridge L b c
    have hdd:Ω ((h ∘ anchor) b.1.castSucc) ((h ∘ anchor) b.1.succ)=0:=by
      simp only [Function.comp_apply,hform,omega_anchors]
    have hiv:(is.map (simpleRoot ch.roots)).Perm
        (forwardInventory (h ∘ anchor) (h ∘ partialBridge L pre) (b::(post++pre))):=by
      simpa only [List.cons_append] using hinv
    obtain ⟨pc,hpc,hpi,hF⟩:=freeChart_polynomial_step Ω hΩ e he S hS hcomp hnd ch is his hall
      (h ∘ anchor) (h ∘ partialBridge L pre) b (post++pre) hb hiv
      (h (eventRoot cellLevel L b)) hp hd hw hdd f
    have hnew:Function.update (h ∘ partialBridge L pre) b
        ((h ∘ anchor) b.1.succ+h (eventRoot cellLevel L b))=h ∘ partialBridge L (pre++[b]):=by
      rw [partialBridge_step L pre b hbp,Function.comp_update,map_add]
      rfl
    rw [hnew] at hpi hF
    have hc':phaseCycle n=(pre++[b])++post:=by rw [hcycle]; simp only [List.append_assoc,List.singleton_append]
    have hi':(is.map (simpleRoot (ch.mutate Ω pc).roots)).Perm
        (forwardInventory (h ∘ anchor) (h ∘ partialBridge L (pre++[b])) (post++(pre++[b]))):=by
      simpa only [List.append_assoc] using hpi
    obtain ⟨ch',hfin,heq⟩:=ih (pre++[b]) hc' (ch.mutate Ω pc) hi'
    refine ⟨ch',hfin,?_⟩
    intro m
    rw [hF,mutationIncomingLabel_map Ω h hform]
    exact heq (rotate (triangularOmega n) cellLevel L m b)

include hΩ he hS hcomp hnd hform in
lemma full_period_transport (is:List I) (his:is.Nodup) (hall:∀i,i∈is)
    (L:ℕ) (ch:FreeChart (I:=I) e)
    (hinv:(is.map (simpleRoot ch.roots)).Perm
      (forwardInventory (h ∘ anchor) (h ∘ periodBridge L) (phaseCycle n)))
    {N:ℕ} (f:ElementaryExpr N) :
    ∃ch':FreeChart (I:=I) e,
      (is.map (simpleRoot ch'.roots)).Perm
        (forwardInventory (h ∘ anchor) (h ∘ periodBridge (L+1)) (phaseCycle n)) ∧
      ∀m,polynomialSectionIncoming Ω ch.roots ch.coord
          (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge L))) (h m)=
        polynomialSectionIncoming Ω ch'.roots ch'.coord
          (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge (L+1))))
          (h (period (triangularOmega n) cellLevel (phaseCycle n) L m)) := by
  have hi:(is.map (simpleRoot ch.roots)).Perm
      (forwardInventory (h ∘ anchor) (h ∘ partialBridge L []) (phaseCycle n++[])):=by
    simpa only [partialBridge_nil,List.append_nil] using hinv
  simpa only [partialBridge_nil,period] using partial_period_transport Ω hΩ e he S hS hcomp hnd h hform
    is his hall L (phaseCycle n) [] rfl ch hi f
end
end ElementaryPositivity.TriangularDynamics

end
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
variable (h:Lattice n (Cell n) →+ M) (hform:∀x y,Ω (h x) (h y)=triangularOmega n x y)
variable (retract:M →+ Lattice n (Cell n)) (hret:∀m,retract (h m)=m)

omit [FiniteDimensional ℝ E] in
include hΩ hret in
lemma periodIncoming_cut [FiniteDimensional ℝ E] (is:List I) (hall:∀i,i∈is)
    (L:ℕ) (ch:FreeChart (I:=I) e)
    (hinv:(is.map (simpleRoot ch.roots)).Perm
      (forwardInventory (h ∘ anchor) (h ∘ periodBridge L) (phaseCycle n)))
    {N:ℕ} (f:ElementaryExpr N) (m:Lattice n (Cell n))
    (hm:polynomialSectionIncoming Ω ch.roots ch.coord
      (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge L))) (h m)≠0) (i:Fin n) :
    periodFunctional cellLevel i L m≤(N:ℤ) := by
  let ell:M →+ ℤ:=(periodFunctional cellLevel i L).comp retract
  have hell (x:Lattice n (Cell n)):ell (h x)=periodFunctional cellLevel i L x:=by
    change periodFunctional cellLevel i L (retract (h x))=_
    rw [hret]
  have hc:∀j,ell (simpleRoot ch.roots j)≤0:=by
    intro j
    have H:=hinv.mem_iff.mp (List.mem_map.mpr ⟨j,hall j,rfl⟩)
    rw [forwardInventory_map] at H
    obtain ⟨r,hr,heq⟩:=List.mem_map.mp H
    rw [←heq,hell]
    exact periodInventory_cut_nonpos i L (phaseCycle n) r hr
  have hv:∀x,ell (vertexDisplay (h ∘ anchor) (h ∘ periodBridge L) x)≤1:=by
    intro x
    cases x with
    | inl a =>
      change ell (h (anchor a))≤1
      rw [hell,periodFunctional_anchor]
      split_ifs <;> omega
    | inr b =>
      change ell (h (periodBridge L b))≤1
      rw [hell,periodFunctional_bridge]
      split_ifs <;> omega
  have hf:=f.cutSupported LaurentRay.vUnit Ω ell (vertexDisplay (h ∘ anchor) (h ∘ periodBridge L)) hv
  have H:=polynomialIncoming_cut_bound Ω hΩ ch.roots ch.coord _ ell N hc hf (h m) hm
  rwa [hell] at H

include hΩ he hS hcomp hnd hform in
lemma complete_history_transport (is:List I) (his:is.Nodup) (hall:∀i,i∈is)
    (ch:FreeChart (I:=I) e)
    (hinv:(is.map (simpleRoot ch.roots)).Perm
      (forwardInventory (h ∘ anchor) (h ∘ periodBridge 0) (phaseCycle n)))
    {N:ℕ} (f:ElementaryExpr N) (m:Lattice n (Cell n)) (L:ℕ) :
    ∃ch':FreeChart (I:=I) e,
      (is.map (simpleRoot ch'.roots)).Perm
        (forwardInventory (h ∘ anchor) (h ∘ periodBridge L) (phaseCycle n)) ∧
      polynomialSectionIncoming Ω ch.roots ch.coord
          (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge 0))) (h m)=
        polynomialSectionIncoming Ω ch'.roots ch'.coord
          (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge L)))
          (h (history (triangularOmega n) cellLevel (phaseCycle n) m L)) := by
  induction L with
  | zero => exact ⟨ch,hinv,rfl⟩
  | succ L ih =>
    obtain ⟨ch',hi,heq⟩:=ih
    obtain ⟨ch'',hi',heq'⟩:=full_period_transport Ω hΩ e he S hS hcomp hnd h hform is his hall L ch' hi f
    exact ⟨ch'',hi',heq.trans (heq' _)⟩

include hΩ he hS hcomp hnd hform hret in
lemma genuine_history_cut_deficit (is:List I) (his:is.Nodup) (hall:∀i,i∈is)
    (ch:FreeChart (I:=I) e)
    (hinv:(is.map (simpleRoot ch.roots)).Perm
      (forwardInventory (h ∘ anchor) (h ∘ periodBridge 0) (phaseCycle n)))
    {N:ℕ} (f:ElementaryExpr N) (m:Lattice n (Cell n))
    (hm:polynomialSectionIncoming Ω ch.roots ch.coord
      (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge 0))) (h m)≠0)
    (L:ℕ) (i:Fin n) :
    0≤cutDeficit cellLevel i N L (history (triangularOmega n) cellLevel (phaseCycle n) m L) := by
  obtain ⟨ch',hi,heq⟩:=complete_history_transport Ω hΩ e he S hS hcomp hnd h hform is his hall ch hinv f m L
  have hm':polynomialSectionIncoming Ω ch'.roots ch'.coord
      (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge L)))
      (h (history (triangularOmega n) cellLevel (phaseCycle n) m L))≠0:=by rwa [←heq]
  have H:=periodIncoming_cut Ω hΩ e h retract hret is hall L ch' hi f _ hm' i
  unfold cutDeficit
  omega
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
