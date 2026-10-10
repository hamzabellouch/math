import OAI.Combinatorics.HadwigerCounterexample.GreedyExposures

namespace OAI

/-! # Sum Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Finset
variable {A I : Type} [Fintype A] [Fintype I] [DecidableEq I]

def draws (I : Type) [Fintype I] (w : Wgt A) : Wgt (I→A) := prodW (fun _ : I => w)

theorem draws_law {w : Wgt A} (h : IsLaw w) :
    IsLaw (draws I w) := prodW_law (fun _ => h)

def refresh (J : Finset I) (x y : I → A) : I → A :=
  fun i => if i∈J then y i else x i

theorem fresh_avg (w : Wgt A) (hw : IsLaw w) (J : Finset I) (f : Wgt (I→A)) :
    avg (draws I w) f =
    avg (draws I w) (fun x => avg (draws I w) (fun y => f (refresh J x y))) := by
  classical
  let P := draws I w
  have hP : IsLaw P := draws_law hw
  let E := fun x : (I→A)×(I→A) => (refresh J x.1 x.2, refresh J x.2 x.1)
  have hE x : E (E x)=x := by
    apply Prod.ext
    · funext i; change refresh _ _ _ _=_; by_cases h : i∈J <;> simp [refresh,E,h]
    · funext i; change refresh _ _ _ _=_; by_cases h : i∈J <;> simp [refresh,E,h]
  let e : (I→A)×(I→A) ≃ _ := ⟨E,E,hE,hE⟩
  have he x : pairW P P (E x)=pairW P P x := by
    unfold pairW P draws prodW
    rw [←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only [E,refresh]
    split <;> ring
  have ht := avg_bij e (pairW P P) (fun x => f x.1)
  change avg (fun x => pairW P P (E x)) (fun x => f (E x).1)=_ at ht
  simp_rw [he] at ht
  rw [pairW_avg,pairW_avg] at ht
  simp_rw [hP.avg_const] at ht
  exact ht.symm

private theorem draws_all (w : Wgt A) (hw : IsLaw w) (J : Finset I) (p : A → Prop) :
    pr (draws I w) (fun x => ∀ i∈J,p (x i)) = pr w p ^ J.card := by
  let v : Wgt (I→A) := prodW (fun _ => w)
  have hh : pr v (fun x => ∀ i∈J,p (x i)) =
      ∏ i:I, pr w (fun x => i∈J → p x) := prodW_pr (fun _ : I => w) (fun i x => i∈J → p x)
  have ht (i : I) :
      pr w (fun x => i∈J → p x)=if i∈J then pr w p else 1 := by
    by_cases hi : i∈J <;> simp [hi,hw.total]
  change pr v _=_
  rw [hh]
  simp_rw [ht]
  rw [← Finset.prod_filter]
  simp

variable {p : Shape} {N : ℕ}

omit [Fintype A] [Fintype I] in
private theorem arrange_fresh (f : A→Ambient p N) (E J : Finset I)
    (h : Disjoint E J) (x y : I → A) :
    arrange p (f ∘ refresh J x y) E=arrange p (f ∘ x) E := by
  classical
  unfold arrange
  apply Finset.sup_congr rfl
  intro i hi
  have he : i∉J := Finset.disjoint_left.mp h hi
  simp [Function.comp_def,refresh,he]

/-- With s=2^m*(2b), not requiring s itself to be a power
of two. -/
theorem no_cover_rank (p : Shape) {N} (f : A→ Ambient p N) (w : Wgt A)
    (hw : IsLaw w) (m b r : ℕ) (hb : 1 ≤ b) (hr : 16*r<m)
    (hf : ∀ i,epoch p (f i)≤ r)
    (c : ℝ) (hc : 0 ≤ c)
    (he : ∀ S : Cov p N,(∀ i, cdSign p S i ≤ r*(2^m*(2*b))) →
      pr w (fun i => covered p S (f i)) ≤ c) :
    let s := 2^m*(2*b)
    pr (draws (Fin s) w) (fun x => 2*epoch p (∑ i,f (x i)) ≤ b) ≤
      ((2:ℝ)^s*(2:ℝ)^s)*c^b := by
  classical
  let s := 2^m*(2*b)
  let T := draws (Fin s) w
  have ht : IsLaw T := draws_law hw
  let Q (X : Finset (Fin s) × Finset (Fin s)) (x : Fin s→A) :=
    Disjoint X.1 X.2 ∧ X.2.card=b ∧ ∀ i∈X.2, covered p (arrange p (f ∘ x) X.1) (f (x i))
  have hg (x : Fin s → A) (h : 2*epoch p (∑ i,f (x i)) ≤ b) :
      ∃ X,Q X x := by
    obtain ⟨E,J,_,_,hi,hj,hX⟩ := sparse_covered (p:=p) (f ∘ x) Finset.univ m b r
      (by simp [s]) hb hr (fun i _ => hf _) h
    exact ⟨(E,J),hi,hj,hX⟩
  have hq (X : Finset (Fin s) × Finset (Fin s)) : pr T (Q X) ≤ c^b := by
    rcases X with ⟨E,J⟩
    by_cases h : Disjoint E J ∧ J.card=b
    · let P (x : Fin s→A) := fun i => covered p (arrange p (f ∘ x) E) (f i)
      have hp (x : Fin s→A) : pr w (P x) ≤ c := by
        apply he; intro i
        have hh := arrange_bound (p:=p) (f ∘ x) E r (fun _ _ => hf _) i
        have hi : E.card ≤ s := by simpa using card_le_card (Finset.subset_univ E)
        exact hh.trans ((Nat.mul_le_mul_right _ hi).trans_eq (Nat.mul_comm ..))
      unfold pr T
      rw [fresh_avg w hw J]
      refine ht.avg_le fun x => ?_
      have hx (y) :
          Q (E,J) (refresh J x y) ↔ ∀ i∈J,P x (y i) := by
        simp only [Q, h.1,h.2,true_and, arrange_fresh f E J h.1]
        constructor
        · intro hh i hi
          specialize hh i hi
          rwa [refresh,ite_eq_left hi] at hh
        intro hh i hi
        rw [refresh,ite_eq_left hi]; exact hh i hi
      simp_rw [hx]
      change pr T _ ≤ _
      rw [show pr T _ = pr w (P x)^J.card from draws_all w hw J _,h.2]
      gcongr
      · exact pr_nonneg hw.nz
      · exact hp x
    · have heq : Q (E,J) = fun _ => False := by
        funext x
        apply propext
        exact iff_false_intro (fun he => h ⟨he.1,he.2.1⟩)
      rw [heq,pr_false]; exact pow_nonneg hc _
  change pr T _ ≤ _
  refine ((pr_mono ht.nz hg).trans (pr_exists_le ht.nz Q)).trans ?_
  refine (Finset.sum_le_sum (g:=fun _ => c^b) fun i _ => hq i).trans_eq ?_
  simp [s]

end HadwigerCounterexample

end

end OAI
