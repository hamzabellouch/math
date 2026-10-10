import OAI.Combinatorics.HadwigerCounterexample.CutIntegralBounds
import OAI.Combinatorics.HadwigerCounterexample.ReferenceProductTests

namespace OAI

/-! # Unary Cell Comparisons -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset Function Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I J A : Type} [Fintype I] [DecidableEq I] [Fintype J]

namespace Template
variable (v : Template p I)

def curtain (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N)) :=
  fun x => ind (ownPart (p:=p) v.t q x)*U x
def propel (v : Template p I) (s : Script p I) (m : Mixer p n) :=
  fun z => ind ((v.draw z).reads s m)

abbrev Localist (v : Template p I) (N : ℕ) :=
  ∀ i,Wgt (AtomKey (p:=p) (v.t i) N)
def board (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N))
    (f : v.Localist N) :=
  avg unif (fun i=> curtain v q U i * prodW f i)
def shadowed (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N)) (ε : ℝ) :=
  ∀ f : v.Localist N,(∀ i j,|f i j|≤1)→ |board v q U f| ≤ ε

def astonish (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N))
    (s : Script p I) (m : Mixer p n) (w f : I→Wgt (Knobs p.g n)) (o) :=
  scene v (propel v s m) (curtain v q U) w f o
def exceeds (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N))
    (s : Script p I) (m : Mixer p n) (w : I→Wgt (Knobs p.g n)) (ε : ℝ)
    (o : UnitType p n N) :=
  blackout v (propel v s m) (curtain v q U) w ε o

theorem astonish_val (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N))
    (s : Script p I) (m : Mixer p n) (w f : I→Wgt (Knobs p.g n)) (o) :
    astonish v q U s m w f o=
      avg (prodW w) (fun i => ind (earns v s m q o i)*U (resultKey v o i)*prodW f i) := by
  unfold astonish earns scene protean curtain propel
  simp_rw [ind_and]; exact avg_congr fun i _=>by ring

structure Paint (v : Template p I) (N : ℕ) where
  coeff : ℝ
  flies : ∀ i,AtomKey (p:=p) (v.t i) N → Prop
def Paint.cost {v : Template p I} (w : Paint v N) (x : Keys (p:=p) v.t N) :=
  w.coeff * prodW (fun i j => ind (w.flies i j)) x
def mural (v : Template p I) (w : J → Paint v N) := fun x => ∑ i:J,(w i).cost x
def design (v : Template p I) (w : Wgt (Keys (p:=p) v.t N)) (M : ℝ) (r : ℕ) :=
  ∃ x:Fin r→Paint v N,w=mural v x∧ ∀ i,|(x i).coeff|≤M

def patched (v : Template p I) (x : I)
    (a : AtomKey (p:=p) (v.t x) N → A)
    (B : A → Wgt (Keys (p:=p) (v.beyond x).t N)) :=
  fun (i:Keys (p:=p) v.t N) => B (a (i x)) ((v.chairK x N i).2)

omit [DecidableEq I] in
theorem design_mono (v : Template p I) (w : Wgt (Keys (p:=p) v.t N))
    (M : ℝ) (r s : ℕ) (hM : 0 ≤ M) (h : r ≤ s) (hr : design v w M r) :
    design v w M s := by
  classical
  obtain ⟨f,hf,hg⟩ := hr
  let g (i : Fin s) : Paint v N := if h:i.val<r then f ⟨i.val,h⟩ else ⟨0,fun _ _=>True⟩
  let k := Fin.castLE h
  have hi i : g (k i)=f i := by unfold g k; simp
  refine ⟨g,funext fun x=>?_,fun i=>?_⟩
  · rw [hf]
    unfold mural
    have h1 :
        ∑ i:Fin r, (f i).cost x =∑ i∈ Finset.univ.image k,(g i).cost x := by
      rw [Finset.sum_image (Fin.castLE_injective h).injOn]
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun t=> t.cost x) (hi i).symm)
    rw [h1]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hh
    have hp : ¬i.val<r := fun he => hh (mem_image.mpr ⟨⟨i.val,he⟩,mem_univ _,rfl⟩)
    unfold g Paint.cost; simp only [dite_eq_right hp,zero_mul]
  unfold g; split
  next h => exact hg _
  next h => simpa using hM

noncomputable def paintJoin (v : Template p I) (x : I)
    (d : AtomKey (p:=p) (v.t x) N → Prop)
    (p' : Paint (v.beyond x) N) : Paint v N where
  coeff := p'.coeff
  flies i := if h:i=x then by subst x; exact d else p'.flies (⟨i,h⟩ : Aside x)

theorem join_cost (v : Template p I) (x : I) (d : AtomKey (p:=p) (v.t x) N → Prop)
    (w : Paint (v.beyond x) N) (k) :
    (paintJoin v x d w).cost k=ind (d (k x))*w.cost ((v.chairK x N k).2) := by
  classical
  unfold Paint.cost
  rw [chair_split _ _ x]
  let f := paintJoin v x d w
  have ht : f.flies x=d := by unfold f paintJoin; simp
  have hi (i:Aside x) : f.flies i.val=w.flies i :=
    dite_eq_right i.property
  rw [ht]
  have hh : prodW (fun i : Aside x => fun j => ind (f.flies i.val j))
      ((v.chairK x N k).2)=prodW (fun i j => ind (w.flies i j)) ((v.chairK x N k).2) :=
    Finset.prod_congr rfl (fun i _=>congrArg _ (congr_fun (hi i) _))
  change w.coeff* (_ * prodW (fun i : Aside x => fun j => ind (f.flies i.val j))
      ((v.chairK x N k).2))=_
  rw [hh]
  ring

set_option maxHeartbeats 600000 in
theorem design_patch (v : Template p I) (x : I) (r s : ℕ)
    (a : AtomKey (p:=p) (v.t x) N → Fin r)
    (B : Fin r → Wgt (Keys (p:=p) (v.beyond x).t N)) (M : ℝ)
    (h : ∀ i,design (v.beyond x) (B i) M s) :
    design v (patched v x a B) M (r*s) := by
  classical
  choose p' hg hp using h
  let g : Fin r × Fin s ≃ Fin (r*s) := Fintype.equivFinOfCardEq (by simp)
  let f (i : Fin r × Fin s) :=
    paintJoin v x (fun j=>a j=i.1) (p' i.1 i.2)
  refine ⟨f ∘ g.symm,?_,fun i => hp _ _⟩
  funext i; unfold patched mural
  rw [← Equiv.sum_comp g]
  simp_rw [Function.comp_apply,Equiv.symm_apply_apply,f,join_cost]
  rw [Fintype.sum_prod_type]; simp_rw [← Finset.mul_sum]
  rw [Finset.sum_eq_single (a (i x))]
  · rw [ind_one (show a (i x)=a (i x) from rfl),one_mul,hg]
    rfl
  · intro j _ hj; rw [ind_zero (Ne.symm hj),zero_mul]
  simp
end Template
end HadwigerCounterexample

end

end OAI
