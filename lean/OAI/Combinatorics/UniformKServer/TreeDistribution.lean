import Mathlib
import OAI.Combinatorics.UniformKServer.RoundedMetricStep
import OAI.Combinatorics.UniformKServer.RoundedState
import OAI.Combinatorics.UniformKServer.LawKernel
import OAI.Combinatorics.UniformKServer.PositiveSupport

namespace OAI

                                       
section

/-! Initial and next rounded configurations live in one fixed finite alphabet;
conditional extension states are eliminated by exact finite push-forward. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset
open scoped Classical
variable {n k : ℕ} {S : Shape n}

def Law.finiteLaw (L : Law) : FiniteProbability.Law L.State := ⟨L.mass,L.nonneg,L.total⟩

def Distribution.supportLaw {a : Allocation S k} (P : Distribution a) : Law where
  State := PositiveSupport.Support P.law.weight
  finite := inferInstance
  mass s := P.law.weight s
  nonneg s := P.law.nonneg s
  total := PositiveSupport.total P.law.weight P.law.nonneg P.law.total

theorem Distribution.support_mean {a : Allocation S k} (P : Distribution a)
    (f : State S k→ℝ) : TreeRounding.mean P.supportLaw (fun s=>f s.val)=P.law.expect f :=
  PositiveSupport.weighted_sum P.law.weight P.law.nonneg f

theorem map_positive {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (P : FiniteProbability.Law Ω) (f : Ω→Γ) (y : Γ) (hy : 0<(P.map f).weight y) :
    ∃ x,f x=y ∧ 0<P.weight x := by
  by_contra he
  have hz (x : Ω) : (if f x=y then P.weight x else 0)=0 := by
    split_ifs with hx
    · exact le_antisymm (not_lt.mp (fun hp=>he ⟨x,hx,hp⟩)) (P.nonneg x)
    · rfl
  have hzero : (P.map f).weight y=0 := by simp only [FiniteProbability.Law.map,hz,sum_const_zero]
  linarith

theorem distribution_initial (a : Allocation S k) : Nonempty (Distribution a) := by
  obtain ⟨L,x,hx,hm⟩ := tree_initialization S a
  let R (s : L.State) := realize a (x s) (hx s)
  let f (s : L.State) := stateOf a (x s) (hx s) (R s)
  refine ⟨⟨L.finiteLaw.map f,?_,?_⟩⟩
  · intro y hy
    obtain ⟨s,rfl,_⟩ := map_positive L.finiteLaw f y hy
    simpa only [f,stateOf_value] using hx s
  · intro v
    rw [FiniteProbability.Law.expect_map]
    change mean L (fun s=>((f s).value v:ℝ))=a.amount v
    simpa only [f,stateOf_value] using hm v

variable {X : Type} [PseudoMetricSpace X]

def stateDistance (f g : Vertex n→X) (s t : State S k) : ℝ :=
  ∑ i,dist (f (s.realization.tuple i)) (g (t.realization.tuple i))

structure Coupling (a b : Allocation S k) (P : Distribution a) where
  joint : FiniteProbability.Law (State S k × State S k)
  first : ∀ F : State S k→ℝ,joint.expect (F ∘ Prod.fst)=P.law.expect F
  next : Distribution b
  second : ∀ F : State S k→ℝ,joint.expect (F ∘ Prod.snd)=next.law.expect F

theorem distribution_step (w : Vertex n→ℝ) (hw : ∀ v,0≤w v)
    (hsep : ∀ v,v≠0 → 22*w v≤w (S.parent v))
    (a b : Allocation S k) (f g : Vertex n→X) (G : ℝ) (hG : 0≤G)
    (hgeo : ∀ u v,0<park S a.amount u → 0<park S b.amount v → u≠v →
      dist (f u) (g v)≤G*TreeAncestry.pathCost (S:=S) w u v)
    (P : Distribution a) :
    ∃ C : Coupling a b P, C.joint.expect (fun st=>stateDistance f g st.1 st.2)≤
      G*132*variation w a b+∑ v,park S b.amount v*commonDistance a b f g v := by
  let L := P.supportLaw
  let x : L.State→Vertex n→ℤ := fun s=>s.val.value
  have hx (s : L.State) : Rounded a (x s) := P.rounded s.val s.property
  have hm (v : Vertex n) : mean L (fun s=>(x s v:ℝ))=a.amount v :=
    (P.support_mean _).trans (P.mean v)
  let R (s : L.State) := s.val.realization
  obtain ⟨E,he,hme,T,hcost⟩ := metric_step w hw hsep a b f g G hG hgeo L x hx hm R
  let new (s : E.law.State) := stateOf b (E.value s) (he s) (T s)
  let Q : Distribution b := {
    law := E.law.finiteLaw.map new
    rounded := by
      intro y hy
      obtain ⟨s,rfl,_⟩ := map_positive E.law.finiteLaw new y hy
      simpa only [new,stateOf_value] using he s
    mean := by
      intro v
      rw [FiniteProbability.Law.expect_map]
      change mean E.law (fun s=>((new s).value v:ℝ))=b.amount v
      simpa only [new,stateOf_value] using hme v }
  let pair (s : E.law.State) : State S k × State S k := ((E.original s).val,new s)
  let C : Coupling a b P := {
    joint := E.law.finiteLaw.map pair
    first := by
      intro F
      rw [FiniteProbability.Law.expect_map]
      change mean E.law ((fun s : L.State=>F s.val) ∘ E.original)=P.law.expect F
      rw [E.preserves,P.support_mean]
    next := Q
    second := by
      intro F
      change (E.law.finiteLaw.map pair).expect (F ∘ Prod.snd)=
        (E.law.finiteLaw.map new).expect F
      simp only [FiniteProbability.Law.expect_map]
      rfl }
  refine ⟨C,?_⟩
  change (E.law.finiteLaw.map pair).expect _≤_
  rw [FiniteProbability.Law.expect_map]
  change mean E.law (fun s=>∑ i,dist (f ((R (E.original s)).tuple i))
    (g (((new s).realization.tuple) i)))≤_
  simpa only [new,stateOf_tuple] using hcost

end UniformKServer.TreeRounding

end


end

end OAI
