import OAI.Combinatorics.HadwigerCounterexample.AtomFlavors
import OAI.Combinatorics.HadwigerCounterexample.PhaseAlternativeSupport

namespace OAI

/-! # Tester Summary Mass -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Finset Function
open scoped BigOperators
variable {p : Shape} {r n : ℕ} {A I : Type} [Fintype A] [Fintype I]
variable [DecidableEq I]

theorem draws_unif :
    unif (α:=I → A)=draws I (unif : Wgt A) := by
  classical funext i
            simp [draws,prodW,unif_apply]

set_option maxHeartbeats 600000 in
theorem tested_fraction (r n : ℕ) (hr : 1≤r) (hn : 2*r≤n) (q : F) :
    1/4 ≤ pr unif (fun x : Vec (Fin n) => tested r x=q) := by
  classical
  let w := draws (Fin n) (unif (α:=F))
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  let Z : Finset (Fin n) := {a,b}
  have hh : pr unif (fun x : Vec (Fin n) => tested r x=q) =
      avg w (fun x => pr w (fun y => tested r (refresh Z x y)=q)) := by
    unfold pr; rw [draws_unif]
    exact fresh_avg _ unif_law _ _
  rw [hh]
  refine (draws_law unif_law).le_avg (fun v => ?_)
  let i0 : Fin r := ⟨0,hr⟩
  let S : Finset (Fin r) := Finset.univ.erase i0
  let h (y : Vec (Fin n)) (i : Fin r) := zget y (2*i.val)*zget y (2*i.val+1)
  let t := ∑ i∈S,h v i
  have hg (y) (ha : y a=1) (hb : y b=q-t) :
      tested r (refresh Z v y) = q := by
    have hu (i : Fin r) (hh : i∈ S) : h (refresh Z v y) i=h v i := by
      have hi := (mem_erase.mp hh).1
      have hi' : i.val ≠ 0 := fun h => hi (Fin.ext h)
      have heq (j : ℕ) (h : 1<j) : zget (refresh Z v y) j=zget v j := by
        by_cases hj : j<n
        · let x : Fin n := ⟨j,hj⟩
          have hr : x∉Z := by simp [x,Z,a,b]; omega
          simp only [zget,dite_eq_left hj,refresh,show (⟨j,hj⟩ : Fin n) ∉ Z from hr,ite_false]
        simp [zget,hj]
      unfold h
      rw [heq (2*i.val) (by omega),heq _ (by omega)]
    change ∑ i,h _ i=q
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
    change h _ i0 + ∑ i∈S, _=_
    rw [show (∑ i∈S,h (refresh Z v y) i)=t from sum_congr rfl hu]
    have h0 := a.isLt
    have h1 := b.isLt
    change 0<n at h0; change 1<n at h1
    have hx : h (refresh Z v y) i0=y a*y b := by
      simp only [h,i0,zget,Nat.mul_zero,Nat.zero_add,dite_eq_left h0,dite_eq_left h1,refresh]
      simp [a,b,Z]
    rw [hx,ha,hb,one_mul,sub_add_cancel]
  let f (i : Bool) := if i then a else b
  let P (i : Bool) (y : F) := y=if i then 1 else q-t
  have he : Injective f := by intro i j; cases i <;> cases j <;> simp [f,a,b]
  have hi : pr w (fun x => ∀ i,P i (x (f i)))=1/4 := by
    change pr (prodW _) _ = _
    rw [prodW_pr_inj he (fun _ => unif_law) P]
    simp only [Fintype.prod_bool,P,pr_point',unif_apply,F]
    norm_num [ZMod.card]
  rw [←hi]
  exact pr_mono (draws_law unif_law).nz (fun y h => hg _ (h true) (h false))

def scanPrice (p : Shape) : ℝ := (1/4)^Fintype.card (ProbeIdx p.g)

theorem scan_fraction (l : Tag p.g) (f : Flavor p.g) (x : Digest p.g)
    (hr : 1 ≤ p.r) (hn : 2*p.r ≤ n) (hx : x.feasible l f) :
    scanPrice p ≤ pr (spins p n) (fun y => scan p l f y=x) := by
  classical
  let P (i : ProbeIdx p.g) (v : Vec (Fin n)) :=
    (if f.keeps l (asBlock i) then tested p.r v else 0)=x i
  have h (i) : 1/4 ≤ pr unif (P i) := by
    by_cases h : f.keeps l (asBlock i)
    · simpa only [P,h,ite_true] using tested_fraction _ _ hr hn (x i)
    simp [P,h,hx _ h,unif_law.total]; norm_num
  have hi y : scan p l f y=x ↔ ∀ i,P i (y (asBlock i)) := funext_iff
  change _ ≤ pr (draws _ _) _
  simp_rw [hi]
  rw [draws,prodW_pr_inj asBlock_inj (fun _ => unif_law) P]
  refine le_trans ?_ (Finset.prod_le_prod₀ (fun i _ => ?_) fun i _ => h i)
  · simp [scanPrice]
  norm_num

def canDial (p : Shape) (l : Tag p.g) (f : Flavor p.g) (q : F) :=
  ∃ v : Digest p.g, v.feasible l f ∧ v.sumBit=q

theorem dial_fraction (p : Shape) (n : ℕ) (l) (f : Flavor p.g) (x : F)
    (hr : 1 ≤ p.r) (hn : 2*p.r ≤ n) (hx : canDial p l f x) :
    scanPrice p ≤ pr (spins p n) (fun y => dialed p l f y=x) := by
  obtain ⟨v,hv,h⟩ := hx
  exact (scan_fraction l f v hr hn hv).trans
    (pr_mono (spins_law p n).nz fun i hi => (congrArg Digest.sumBit hi).trans h)

theorem scanPrice_pos (p : Shape) : 0<scanPrice p := by unfold scanPrice; positivity

theorem dial_law (p : Shape) (n : ℕ) (l) (f : Flavor p.g) (x : F)
    (hr : 1 ≤ p.r) (hn : 2*p.r≤n) (hx : canDial p l f x) :
    IsLaw (scopedBit p n l f x) := on_law (spins_law p n).nz
      ((scanPrice_pos p).trans_le (dial_fraction p n _ _ _ hr hn hx))

theorem generic_summary (p : Shape) (hg : 3≤p.g) (l : Tag p.g) (q y : F) :
    ∃ v : Digest p.g, v.feasible l Flavor.full ∧ v.sumBit=q ∧ v.diagO=y := by
  classical
  have hi := card_allowed' l
  obtain ⟨i,hi⟩ := show ∃ i,allowed i l from by
    have ht : 0 < Fintype.card {i : Tag p.g // allowed i l} := by omega
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp ht
    exact ⟨x.val,x.property⟩
  let v : Digest p.g := Sum.elim (Pi.single (i,l) y) (fun _ => q-y)
  have hf : v.diagO=y := by
    unfold Digest.diagO; rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single l]
      · simp [v]
      · intro k _ hk; simp [v,hk]
      simp
    · intro k _ hk; simp [v,hk]
    simp
  refine ⟨v,?_,?_,hf⟩
  · rintro (⟨j,t⟩|_) hj
    · have h : (j,t) ≠ (i,l) := by
        rintro hk
        obtain rfl : j=i := congrArg Prod.fst hk
        exact hj hi
      exact Pi.single_eq_of_ne h _
    exact (hj trivial).elim
  unfold Digest.sumBit
  rw [hf]; change y+(q-y)=q
  rw [add_sub_cancel]

end HadwigerCounterexample

end

end OAI
