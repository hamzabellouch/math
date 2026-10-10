import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.SquareBoundary

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.Boundary

def forwardDir (d : Dir) : Prop := d=1 ∨ d=2

def forwardIndices (e : ℕ → Edge) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun i => forwardDir (e i).2)

def outsideSites (e : ℕ → Edge) (n : ℕ) : Finset Grid :=
  (forwardIndices e n).image (fun i => rightSite (e i))

lemma forward_step (d : Dir) : (step d).1-(step d).2=
    if forwardDir d then (-1 : ℤ) else 1 := by
  fin_cases d <;> norm_num [step,forwardDir,Fin.ext_iff]

lemma twice_forward_card (e : ℕ → Edge) (n : ℕ)
    (hchain : ∀ i, head (e i)=tail (e (i+1))) (hclose : e n=e 0) :
    2*(forwardIndices e n).card=n := by
  have hv (i : ℕ) : (e (i+1)).1=(e i).1+step (e i).2 := (hchain i).symm
  have hd (i : ℕ) :
      ((e (i+1)).1.1-(e (i+1)).1.2)-((e i).1.1-(e i).1.2)=
      if forwardDir (e i).2 then (-1 : ℤ) else 1 := by
    rw [hv]
    simpa only [Prod.fst_add,Prod.snd_add] using (by
      rw [← forward_step]
      ring : ((e i).1.1+(step (e i).2).1-((e i).1.2+(step (e i).2).2))-
        ((e i).1.1-(e i).1.2)=if forwardDir (e i).2 then (-1 : ℤ) else 1)
  have hz : (∑ i∈Finset.range n, (if forwardDir (e i).2 then (-1 : ℤ) else 1))=0 := by
    simp_rw [← hd]
    rw [Finset.sum_range_sub (fun i => (e i).1.1-(e i).1.2),hclose,sub_self]
  have hf : ∑ i∈Finset.range n, (if forwardDir (e i).2 then (1 : ℤ) else 0)=
      ((forwardIndices e n).card : ℤ) := by
    simp [forwardIndices,Finset.sum_boole]
  have he (i : ℕ) : (if forwardDir (e i).2 then (-1 : ℤ) else 1)=
      1-2*(if forwardDir (e i).2 then (1 : ℤ) else 0) := by split <;> norm_num
  simp_rw [he] at hz
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,hf] at hz
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hz
  omega

lemma rightSite_direction_injective :
    Function.Injective (fun e : Edge => (rightSite e,e.2)) := by
  rintro ⟨p,d⟩ ⟨q,c⟩ h
  have hd : d=c := congrArg Prod.snd h
  subst c
  have hp : p=q := add_right_cancel (congrArg Prod.fst h)
  exact Prod.ext hp rfl

lemma forward_card_le_twice_outside (e : ℕ → Edge) (n : ℕ)
    (hinj : Set.InjOn e (Set.Iio n)) :
    (forwardIndices e n).card≤2*(outsideSites e n).card := by
  have hb := Finset.card_le_card_of_injOn
    (s := forwardIndices e n) (t := outsideSites e n ×ˢ ({1,2} : Finset Dir))
    (f := fun i => (rightSite (e i),(e i).2))
    (by
      intro i hi
      refine Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨i,hi,rfl⟩,?_⟩
      simpa only [forwardDir,Finset.mem_insert,Finset.mem_singleton] using (Finset.mem_filter.mp hi).2)
    (by
      intro i hi j hj he
      exact hinj (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) (rightSite_direction_injective he))
  have hc : ({1,2} : Finset Dir).card=2 := by decide
  rw [Finset.card_product,hc] at hb
  omega

theorem length_le_four_outside (e : ℕ → Edge) (n : ℕ)
    (hchain : ∀ i, head (e i)=tail (e (i+1))) (hclose : e n=e 0)
    (hinj : Set.InjOn e (Set.Iio n)) : n≤4*(outsideSites e n).card := by
  have h := twice_forward_card e n hchain hclose
  have h' := forward_card_le_twice_outside e n hinj
  omega

lemma forward_child (e : Edge) (hdir : forwardDir e.2) :
    rightSite e=leftSite e+(1,0) ∨ rightSite e=leftSite e+(0,1) := by
  rcases e with ⟨⟨x,y⟩,d⟩
  rcases hdir with h|h
  · change d=1 at h
    subst d
    left
    simp [rightSite,leftSite,rightOffset,leftOffset]
  · change d=2 at h
    subst d
    right
    simp [rightSite,leftSite,rightOffset,leftOffset]

lemma outsideSites_failed_children (S : Set Grid) (e : ℕ → Edge) (n : ℕ)
    (hmem : ∀ i, e i∈squareBoundary S) :
    ∀ z∈outsideSites e n, z∉S ∧ ∃ y∈S, z=y+(1,0) ∨ z=y+(0,1) := by
  intro z hz
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
  exact ⟨(hmem i).2,leftSite (e i),(hmem i).1,
    forward_child (e i) (Finset.mem_filter.mp hi).2⟩

end CriticalPercolation.Boundary
end
end
end

end OAI
