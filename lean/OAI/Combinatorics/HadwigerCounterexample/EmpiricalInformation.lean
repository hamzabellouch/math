import OAI.Combinatorics.HadwigerCounterexample.MutualInformation
import OAI.Combinatorics.HadwigerCounterexample.SumRankBounds

namespace OAI

/-! # Empirical Information -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C J : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype J]
variable [DecidableEq J] {l : ℕ}

theorem draw_pick {p : Wgt B} (hp : IsLaw p) (i : J) :
    mapW (draws J p) (fun x => x i)=p := by
  funext b
  let f := fun (_ : Unit) => i
  let R := fun (_ : Unit) (j : B) => j=b
  have ht := prodW_pr_inj (f.injective_of_subsingleton) (w:=fun _ => p)
    (fun _ => hp) R
  unfold mapW
  simpa [f,R,draws] using ht
omit [Fintype B] [DecidableEq J] in
theorem draw_elem {p : Wgt B} (x : J→B) (i : J)
    (h : draws J p x≠0) : p (x i)≠0 := fun hx => h (prod_eq_zero (mem_univ _) hx)

theorem tension_traj (J : Type) [Fintype J] [DecidableEq J]
    (p q : Wgt B) (hp : IsLaw p) (h : lsupp p q) :
    tension (draws J p) (draws J q)=num J*tension p q := by
  let Q (x : J→B) :=
      ∑ i:J,(log (p (x i))-log (q (x i)))
  have he : tension (draws J p) (draws J q)=avg (draws J p) Q := by
    refine avg_congr fun i hi => ?_
    have hp (j) := draw_elem i j hi
    change log (∏ j:J,p (i j))-log (∏ j:J,q (i j))=_
    rw [log_prod (fun j _ => hp j),log_prod (fun j _ => h _ (hp j)), ← Finset.sum_sub_distrib]
  let r (j : J) := fun x : J→B => log (p (x j))-log (q (x j))
  rw [he, show avg _ Q= ∑ i:J,avg (draws J p) (r i) from avg_sum ..]
  have hr (i : J) :
      avg (draws J p) (r i)= tension p q := by
    unfold r
    rw [← mapW_avg (draws J p) (fun x => x i) (fun x => log (p x)-log (q x)), draw_pick hp i]
    rfl
  simp only [hr,Finset.sum_const, Finset.card_univ,nsmul_eq_mul,num]

abbrev Track (B : Type) (l : ℕ) := B→ Fin (l+1)
def traceTraj [DecidableEq B] (x : Fin l → B) :
    Track B l :=
  fun i => ⟨(univ.filter (fun j => x j=i)).card,
    Nat.lt_succ_of_le ((card_le_card (filter_subset ..)).trans_eq (by simp))⟩

theorem draws_trace [DecidableEq B] (p : Wgt B) (x : Fin l → B) :
    draws (Fin l) p x=∏ i:B,p i^(traceTraj x i).val := by
  classical
  have ht (i : B) : p i^(traceTraj x i).val =
      ∏ j:Fin l, if x j=i then p i else 1 := by
    unfold traceTraj; rw [←Finset.prod_filter]; simp
  simp_rw [ht]; rw [Finset.prod_comm]
  unfold draws prodW
  apply prod_congr rfl
  intro i _
  simp

theorem traj_charge (μ : Wgt A) (p : A→ Wgt B) (w : Wgt B)
    (hμ : IsLaw μ) (hp : ∀ i, IsLaw (p i))
    (h : ∀ i,lsupp (p i) w) :
    let f := fun i => draws (Fin l) (p i)
    let q := draws (Fin l) w
    (l:ℝ)*avg μ (fun i => tension (p i) w) ≤
      num B *log ((l:ℝ)+1) + tension (mixW μ f) q := by
  classical
  intro f q
  have he : ↑l*avg μ (fun i => tension (p i) w) =
      avg μ (fun i => tension (f i) q) := by
    unfold f q
    simp_rw [tension_traj _ _ _ (hp _) (h _),avg_mul']
    simp only [num,Fintype.card_fin]
  rw [he,tension_mix]
  refine add_le_add_left ?_ _
  have h0 : ∀ i,IsLaw (f i) := fun i => draws_law (hp i)
  refine (banded_overhead hμ h0 traceTraj (fun i j k ht => ?_)).trans_eq ?_
  · unfold f; rw [draws_trace,draws_trace,ht]
  simp only [Track,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Real.log_pow,Nat.cast_add,
    Nat.cast_one,num]

/-- If components are coarse with no tiny positive atoms,
    their repeat law has a corresponding cap cost for any submeasure. -/
theorem traj_cap (p : Wgt B) (hp : IsLaw p) (u : ℝ)
    (h : ∀ i, p i≠0 → bp (-u)≤p i) :
    ∀ x, draws (Fin l) p x≠0 → bp (-u*l) ≤ draws (Fin l) p x := by
  intro x hx
  have hpos (i : Fin l) : 0 < p (x i) :=
    lt_of_le_of_ne (hp.nz _) (Ne.symm (draw_elem _ i hx))
  rw [bp_mul_nat]
  refine le_trans ?_ (Finset.prod_le_prod₀ (fun i (_: i∈(univ:Finset (Fin l))) =>
    (bp_pos (-u)).le) fun i _ => h (x i) (hpos i).ne')
  simp
end HadwigerCounterexample

end

end OAI
