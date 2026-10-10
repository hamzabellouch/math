import OAI.Combinatorics.HadwigerCounterexample.LargeSetHits

namespace OAI

/-! # Superlevel Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
variable {A : Type} [Fintype A]

def cliff (u f : Wgt A) (t:ℝ) (x : A) := 2*t*u x ≤ f x

set_option maxHeartbeats 800000 in
theorem cliff_bounds (u f p : Wgt A) (t ε : ℝ) (ht : 0<t)
    (hu:IsLaw u) (h:varOne p f ≤ ε) :
    pr p (fun x=>¬cliff u f t x)≤ 2*t+ε ∧
    pr u (fun x=> cliff u f t x ∧ p x < t*u x)≤ ε/t := by
  classical
  let W:=cliff u f t
  let Q x:=¬ W x
  let L x:=W x ∧ p x < t*u x
  constructor
  · have hi : pr f Q≤2*t := by
      have hv i : f i * ind (Q i) ≤ u i*(2*t) := by
        by_cases h:Q i
        · rw [ind_one h,mul_one,mul_comm]; exact le_of_not_ge h
        rw [ind_zero h,mul_zero]; exact mul_nonneg (hu.nz _) (by linarith)
      exact (Finset.sum_le_sum (s:=univ) fun i _=>hv i).trans_eq (hu.avg_const _)
    have hh: pr p Q-pr f Q ≤ ε:= (var_pr p f Q).trans h
    linarith only [hh,hi]
  · refine (le_div_iff₀ ht).mpr ((le_trans ?_ h))
    change pr u L*_ ≤_
    unfold pr avg varOne; rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    dsimp only
    by_cases he:L i
    · rw [ind_one he,mul_one]
      have hh : 2*t*u i≤ f i := he.1
      have hv := he.2
      linarith [(abs_sub_comm (f i) (p i)),le_abs_self (f i-p i)]
    rw [ind_zero he,mul_zero,zero_mul]; exact abs_nonneg _

theorem cliff_thick (P: Wgt A→Prop) (x f u:Wgt A)
    (hu:IsLaw u) (hp:P x) (t δ:ℝ)
    (ht:0<t) (hs : smallSet P u δ t)
    (hw : varOne x f ≤ t) (h : 5*t ≤ tot x) :
    δ < pr u (cliff u f t) := by
  classical
  by_contra! hh
  have he := hs x hp _ hh
  have hg := (cliff_bounds u f x t t ht hu hw).1
  rw [pr_not] at hg
  linarith only [he,hg,h,ht]

set_option maxHeartbeats 700000 in
theorem cliff_score (P : Wgt A→Prop) (x y f u:Wgt A)
    (hx : SubLaw x) (hy:SubLaw y) (hu:IsLaw u)
    (hz : lsupp x u)
    (K t ε : ℝ) (ht:0<t)
    (h1 : P x) (hf : varOne y f ≤ ε)
    (h2 : smallSet P u (ε/t) K)
    (h : 2*K ≤ pr x (cliff u f t)) :
    t*K ≤ overlap u x y := by
  classical
  let W:=cliff u f t
  let Q i:= W i ∧ y i<t*u i
  let F:=fun x=> W x ∧ ¬Q x
  have he : pr x Q≤ K := h2 x h1 _ (cliff_bounds u f y t ε ht hu hf).2
  have hA : K≤ pr x F := by
    have hf i (hi: W i): Q i∨ F i := by unfold F; tauto
    have ha: pr x W≤pr x Q+pr x F:= (pr_mono hx.nz hf).trans (pr_or_le hx.nz)
    linarith only [ha,h,he]
  refine le_trans (mul_le_mul_of_nonneg_left hA ht.le) ?_
  unfold overlap pr avg; rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _=>?_
  dsimp only
  have h i : 0≤density u x i*density u y i := mul_nonneg (div_nonneg (hx.nz _) (hu.nz _))
    (div_nonneg (hy.nz _) (hu.nz _))
  by_cases ha:x i=0
  · rw [ha,zero_mul,mul_zero]
    exact mul_nonneg (hu.nz _) (h i)
  by_cases hg:F i
  · rw [ind_one hg,mul_one]
    have hb:=lt_of_le_of_ne (hu.nz i) (Ne.symm (hz i ha))
    have hv : t ≤ density u y i := (le_div_iff₀ hb).mpr
      (le_of_not_gt (fun h=>hg.2 ⟨hg.1,h⟩))
    calc
      t*x i ≤ density u y i*x i :=mul_le_mul_of_nonneg_right hv (hx.nz _)
      _ = _ := by unfold density; field_simp
  rw [ind_zero hg,mul_zero,mul_zero]
  exact mul_nonneg (hu.nz _) (h i)
end HadwigerCounterexample

end

end OAI
