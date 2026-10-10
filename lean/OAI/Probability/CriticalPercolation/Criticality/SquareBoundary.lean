import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.BalancedCycles

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.Boundary

abbrev Grid := ℤ×ℤ
abbrev Dir := Fin 4
abbrev Edge := Grid×Dir

def step : Dir → Grid := ![(1,0),(0,1),(-1,0),(0,-1)]
def leftOffset : Dir → Grid := ![(0,0),(-1,0),(-1,-1),(0,-1)]
def rightOffset : Dir → Grid := ![(0,-1),(0,0),(-1,0),(-1,-1)]
def tail (e : Edge) : Grid := e.1
def head (e : Edge) : Grid := e.1+step e.2
def leftSite (e : Edge) : Grid := e.1+leftOffset e.2
def rightSite (e : Edge) : Grid := e.1+rightOffset e.2

def squareBoundary (S : Set Grid) : Set Edge :=
  {e | leftSite e∈S ∧ rightSite e∉S}

lemma squareBoundary_finite {S : Set Grid} (hS : S.Finite) : (squareBoundary S).Finite := by
  apply Set.Finite.of_injOn (f := fun e : Edge => (leftSite e,e.2))
    (t := S×ˢ(Set.univ : Set Dir)) ?_ ?_ (hS.prod Set.finite_univ)
  · intro e he
    exact ⟨he.1,Set.mem_univ _⟩
  · rintro ⟨p,d⟩ _ ⟨q,c⟩ _ h
    have hd : d=c := congrArg Prod.snd h
    subst c
    have hp : p=q := add_right_cancel (congrArg Prod.fst h)
    exact Prod.ext hp rfl

def outgoingEquiv (S : Set Grid) (v : Grid) :
    {e : squareBoundary S // tail e=v} ≃ {d : Dir // (v,d)∈squareBoundary S} where
  toFun e := ⟨e.1.1.2,by
    have h := e.1.2
    have hv := e.2
    change e.1.1.1=v at hv
    change leftSite (e.1.1.1,e.1.1.2)∈S ∧ rightSite (e.1.1.1,e.1.1.2)∉S at h
    rwa [hv] at h⟩
  invFun d := ⟨⟨(v,d.1),d.2⟩,rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext e.2.symm rfl
  right_inv d := rfl

def incomingEquiv (S : Set Grid) (v : Grid) :
    {e : squareBoundary S // head e=v} ≃
      {d : Dir // (v-step d,d)∈squareBoundary S} where
  toFun e := ⟨e.1.1.2,by
    have hv : e.1.1.1=v-step e.1.1.2 := eq_sub_iff_add_eq.mpr e.2
    have h := e.1.2
    change leftSite (e.1.1.1,e.1.1.2)∈S ∧ rightSite (e.1.1.1,e.1.1.2)∉S at h
    rwa [hv] at h⟩
  invFun d := ⟨⟨(v-step d.1,d.1),d.2⟩,sub_add_cancel _ _⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    change (v-step e.1.1.2,e.1.1.2)=e.1.1
    exact Prod.ext (eq_sub_iff_add_eq.mpr e.2).symm rfl
  right_inv d := rfl

lemma squareBoundary_balanced (S : Set Grid) (v : Grid) :
    Fintype.card {d : Dir // (v-step d,d)∈squareBoundary S}=
      Fintype.card {d : Dir // (v,d)∈squareBoundary S} := by
  rcases v with ⟨x,y⟩
  rw [Fintype.card_subtype (fun d : Dir => ((x,y)-step d,d)∈squareBoundary S),
    Fintype.card_subtype (fun d : Dir => ((x,y),d)∈squareBoundary S)]
  simp only [Finset.card_filter,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  simp only [squareBoundary,Set.mem_ofPred_eq,leftSite,rightSite,step,leftOffset,rightOffset]
  simp only [Matrix.cons_val_zero,Prod.mk_add_mk,add_zero,sub_eq_add_neg]
  by_cases h1 : (x,y)∈S <;> by_cases h2 : (x+-1,y)∈S <;>
    by_cases h3 : (x+-1,y+-1)∈S <;> by_cases h4 : (x,y+-1)∈S <;>
    simp_all

theorem squareBoundary_closed_trail {S : Set Grid} (hS : S.Finite)
    (e₀ : Edge) (he₀ : e₀∈squareBoundary S) :
    ∃ n : ℕ, 0<n ∧ ∃ e : ℕ → Edge, e 0=e₀ ∧ e n=e₀ ∧
      (∀ i, e i∈squareBoundary S) ∧ (∀ i, head (e i)=tail (e (i+1))) ∧
      Set.InjOn e (Set.Iio n) := by
  let := (squareBoundary_finite hS).fintype
  have hb (v : Grid) : Fintype.card {e : squareBoundary S // head e=v}=
      Fintype.card {e : squareBoundary S // tail e=v} :=
    (Fintype.card_congr (incomingEquiv S v)).trans
      ((squareBoundary_balanced S v).trans (Fintype.card_congr (outgoingEquiv S v)).symm)
  obtain ⟨n,hn,e,h0,hn0,hchain,hinj⟩ := exists_closed_trail
    (fun e : squareBoundary S => tail e) (fun e : squareBoundary S => head e) (by intro v; simpa only [Fintype.card_eq_nat_card] using hb v) ⟨e₀,he₀⟩
  refine ⟨n,hn,(fun i => (e i).1),congrArg Subtype.val h0,congrArg Subtype.val hn0,
    fun i => (e i).2,hchain,?_⟩
  intro i hi j hj he
  exact hinj hi hj (Subtype.ext he)

lemma west_root_edge_mem (S : Set Grid) (hroot : (0,0)∈S)
    (hquad : ∀ v∈S, 0≤v.1 ∧ 0≤v.2) : ((0,1),3)∈squareBoundary S := by
  constructor
  · simpa [leftSite,leftOffset] using hroot
  · have hbad : (-1,0)∉S := by
      intro h
      have ht := (hquad _ h).1
      norm_num at ht
    simpa [rightSite,rightOffset] using hbad

end CriticalPercolation.Boundary
end
end
end

end OAI
