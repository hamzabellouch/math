import OAI.Combinatorics.HadwigerCounterexample.SyntheticSliceComparison

namespace OAI

/-! # Gram Array Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter
open scoped BigOperators Topology
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}
def magazine (p : Shape) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (P : Display p I N→Prop) (a : I→ Tickets p) (o : Orient p n N) :=
  pr (sketchLaw p n a) (fun i => P (drill p (incision p l s f i) o))

set_option maxHeartbeats 1000000 in
theorem magazine_var (p : Shape) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (P : Display p I N → Prop) (a : I → Tickets p) (m : Mixer p n)
    (h : 2*num (Full p n)<N) (hj : 1≤p.j) (hn : 2*p.r≤n) (hN : 2*num I-(N:ℝ)≤ -1)
    (k : ℝ) (hk : num (Bool × Comp p.g × I)≤ k) (hK : 2*k-N≤ -1) :
    let g:= tied (drStage p I) Bool
    let V := displayLaw p I N (labGram p l f a)
    avg (raw m N) (fun i => (magazine p l s f P a i - pr V P)^2) ≤
      2 * netFact g * twinkle g k N + bp (num Bool*num I - n) := by
  classical
  let Z := labGram p l f a
  let W := sketchLaw p n a
  let μ := raw m N
  have hw : IsLaw W:= sketch_law p n a hn
  have hμ : IsLaw μ := raw_law m h
  have hs := display_law p Z N hN
  intro g V
  let U i := ind (P i)-pr V P
  have he : avg V U=0 := by unfold U; rw [avg_sub,hs.avg_const]; exact sub_self _
  have hh (i) : |U i| ≤1 := by
    have hl := pr_nonneg (p:=P) hs.nz; have ht := (pr_le_tot (p:=P) hs.nz).trans hs.total.le
    unfold U; rw [abs_le]; constructor <;> linarith only [ind_nonneg (P i),ind_le_one (P i),hl,ht]
  let A (x : I → Knobs p.g n) := incision p l s f x
  let F (i : Orient p n N) x := U (drill p (A x) i)
  have heq (i) :
      magazine p l s f P a i-pr V P = avg W (F i) := by
    unfold F U; rw [avg_sub,hw.avg_const]; rfl
  let w := draws Bool W; have hW : IsLaw w := draws_law hw
  let E := 2*netFact g * twinkle g k N
  have hp0 : 0 ≤ E := by
    have hg : 0<netFact g := netFact_pos
    have he : 0≤twinkle g k N := add_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num) (bp_pos _).le)) (bp_pos _).le
    exact mul_nonneg (by positivity) he
  have hi (x : Bool→I→Knobs p.g n) (hx : w x≠0) :
      avg μ (fun o => F o (x true)*F o (x false)) ≤ E+ind (¬bloom p x) := by
    by_cases ht : bloom p x
    · have ha (i : Bool) : avg μ (fun o=> F o (x i))=0 := by
        let M := incision p l s f (x i)
        have he' := drill_law p (bloom_incision p n x l s f ht i) m h
        rw [sketch_matrix p l s f m a hj _ (draw_elem x i hx)] at he'
        change avg μ (fun o=>U (drill p M o))=0
        rw [←mapW_avg]; exact (congrArg (fun w=>avg w U) he').trans he
      let D i:=drQuery (p:=p) (A (x i))
      let W i:=U (relay (Comp p.g) I N i)
      have hg := bloom_drill p n x l s f ht
      have hz := pooled_batch D D m h k (fun i=>(port_limit g i).trans hk) hK hg hg
        (fun i=>W) (fun i y=>hh _)
      simp_rw [Fintype.prod_bool] at hz
      have heq (i : Bool) :
         avg μ (fun o=> W (peekR p (drStage p I) (D i) (D i) o))=0 := by
        specialize ha i
        unfold F at ha; simp_rw [drill_view p] at ha; exact ha
      change |_ - (avg μ _ * avg μ _)|≤_ at hz
      rw [heq true,heq false,mul_zero,sub_zero] at hz
      unfold F
      simp_rw [drill_view p]
      rw [ind_zero (fun hg=>hg ht),add_zero]
      exact (le_abs_self _).trans hz
    rw [ind_one ht]
    refine (hμ.avg_le (b:=1) ?_).trans (le_add_of_nonneg_left hp0)
    intro i
    have ht (a b : ℝ) (ha : |a| ≤ 1) (hb : |b|≤1) :
        a*b ≤1 := (le_abs_self _).trans (by rw [abs_mul]; exact
      (mul_le_mul ha hb (abs_nonneg _) zero_le_one).trans_eq (by ring))
    exact ht _ _ (hh _) (hh _)
  simp_rw [heq,avg_cross_sq]; rw [avg_avg]
  have ht :
      avg w (fun i=> E+ind (¬bloom p i))=E+pr w (fun i=>¬bloom p i) := by rw [avg_add,hW.avg_const];
                                                                            rfl
  apply le_trans _ (add_le_add_right (buds p n (fun i=>rung p n (a i))
    (fun i=>ticketFlow n _ hn)) E)
  change _ ≤ E + pr w (fun i=>¬bloom p i)
  rw [←ht]; unfold avg
  refine Finset.sum_le_sum (fun i _=> ?_)
  by_cases hi' : w i=0
  · change w i*_ ≤ w i*_
    simp only [hi',zero_mul,le_refl]
  exact mul_le_mul_of_nonneg_left (hi i hi') (hW.nz _)
end HadwigerCounterexample

end

end OAI
