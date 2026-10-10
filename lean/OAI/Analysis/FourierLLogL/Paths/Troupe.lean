import OAI.Analysis.FourierLLogL.Paths.Checkpoint
import OAI.Analysis.FourierLLogL.Paths.Frost
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace Troupe

structure Grade where
  main : Bool
  i : ℕ
def stage (g : Grade) (m : ℕ) : Plot := ⟨g.main,g.i,m⟩
def grade (p : Plot) : Grade := ⟨p.main,p.ix⟩

/-- height parameter allowing very small mass static entries. -/
def amount (s : Scene M) (j : ℕ) := height j+max (-log s.norm) 0+2
def rose (g : Grade) (u : Grid M) : Run.Streak M := ⟨g.i,u⟩
def recital (g : Grade) (u : Grid M) (l : Path M) :=
    if g.main then (rose g u).sumbling none l else coldScore u (side g.i) l
lemma rec_one (g : Grade) (u : Grid M) (l : Path M) : 1 ≤ recital g u l := by
  unfold recital; split; exact Run.Streak.sumbling_one _ _ _; exact cold_one _ _ _
lemma amount_limits (s : Scene M) (j : ℕ) : 1 ≤ amount s j ∧ height j ≤ amount s j :=
    let H := d_pos j
    have hh : 0 ≤ max (-log s.norm) 0 := le_max_right _ _
    by unfold amount; constructor <;> linarith

def entitled (g : Grade) (s : Scene M) (j : ℕ) :=
    g.main=true → g.i ≤ mainIx j ∧ s.live=true
def cutBook (g : Grade) (s : Scene M) (j : ℕ) :=
    if g.main then kappa j (codeWeight capA) (g.i+1) else scLimit s g.i j
lemma cut_nonneg (g : Grade) (s : Scene M) (j : ℕ) : 0 ≤ cutBook g s j := by
  unfold cutBook scLimit; split
  · exact (kappa_pos _ (by unfold codeWeight;
                           unfold capA reserve; norm_num) j _).le
  · have he := d_pos j
    have hh := le_max_right (-log s.norm) 0
    positivity

lemma cover_limit (s : Scene M) (g : Grade) (j J : ℕ) (hs : s.Safe j J f)
    (hp : Climb s) (h : s.settled j) (hg : entitled g s j)
    (hF : ∀ i,f i ≤ exp (height j)):
    ((net s j g.i g.main).card:ℝ) ≤ exp (cutBook g s j) := by
  by_cases hx : g.main=true
  · rw [cutBook,ite_eq_left hx,hx]
    apply net_len_main _ _ _ _ h (hg hx).2
    have HH := (hg hx).1
    unfold testIx; omega
  unfold cutBook; rw [ite_eq_right hx]
  rw [show g.main=false from Bool.eq_false_iff.mpr hx]
  exact net_len_scalar _ _ hp.fit.ready hp.deep hp.fit.pos hp.tight (fun i => (hs.sub i).trans (hF i))

open Plot

def boom (p : Plot) (c : Board M) (s : Scene M) := cardStep p (p.turn c s)
def burst (p : Plot) (s : Scene M) (j : ℕ) (l : Path M) :=
    ∑ x∈ net s j p.ix p.main, recital (grade p) x l
def showScore (p : Plot) (c : Board M) (j : ℕ) : Path M → ℝ
| [] => 1
| b::l => if boom p c b.post then
    (if freshAt p c b.post then burst p b.post j (b::l) else 0)+showScore p (p.turn c b.post) j l else 1

lemma burst_pos (p : Plot) (s : Scene M) (j : ℕ) (l : Path M) :
    0 ≤ burst p s j l :=
  Finset.sum_nonneg fun i _ => le_trans (by norm_num) (rec_one (grade p) i l)
lemma show_one (p : Plot) (c : Board M) (j : ℕ) (l : Path M) :
    1 ≤ showScore p c j l := by
  induction l generalizing c with
  | nil => exact le_rfl
  | cons b l ih =>
    rw [showScore]
    split; exact le_trans (ih _) (le_add_of_nonneg_left (by split; apply burst_pos; norm_num))
    exact le_rfl

def sticker (s : Scene M) (g : Grade) (j : ℕ) :=
    10^30*(amount s j)^3 * exp (cutBook g s j)

/-- summing conditional estimate-envelope costs over births. -/
lemma paint_birth :
    ∀ᶠ j : ℕ in atTop, ∀ (M J : ℕ) (s : Scene M)
      (t : Thread M s) (f : Grid M → ℝ) (p : Plot),
      Following j J f t → Fit s → entitled (grade p) s j →
      (∀ x, f x ≤ exp (height j)) → ∀ c : Board M,
        stats t (showScore p c j) ≤ 1+sticker s (grade p) j*stats t (minted p c) := by
  filter_upwards [Run.Streak.expected_bling] with j hB M J s t f p h hh hG hF c
  let g := grade p
  induction t generalizing c with
  | blank s =>
    rw [stats_nil,stats_nil]
    change (1:ℝ) ≤ 1+_*0; ring_nf; exact le_rfl
  | ran s q k ih =>
    let t := ran s q k
    let v := turn p c q
    let R := sticker s g j
    let h₀ := h
    have hK := jump_ideal h hh.lift
    have hC : cutBook g q j=cutBook g s j := by unfold cutBook scLimit; rw [hK.lower.flat]
    have HE : amount q j=amount s j := by unfold amount; rw [hK.lower.flat]
    have hR (b : Bool) : sticker (q.smaller b) g j=R := by change sticker q g j=R; unfold R sticker; rw [hC, HE]
    have hz : entitled g q j := fun hi => ⟨(hG hi).1,hK.lower.mode.trans (hG hi).2⟩
    obtain ⟨ha,hb,hc,hd,ht,hk⟩ := h
    let x := amount s j; let C (l : Path M) := burst p q j l
    have Hc : stats t C ≤ R := by
      let e := net q j p.ix p.main
      have HX : (e.card:ℝ) ≤ exp (cutBook g s j) := hC ▸ cover_limit q g j J hc hK.climb ht hz hF
      have Hi (u) : stats t (recital g u) ≤ 10^30*x^3 := by
        have h1 : 1 ≤ x ∧ height j ≤ x := amount_limits s j
        have h3 : 1 ≤ x^3 := one_le_pow₀ h1.1
        unfold recital
        by_cases H : g.main=true
        · simp_rw [ite_eq_left H]
          apply le_trans (hB M J s q f k h₀ hh (hz H).2 hF (rose g u) (hG H).1)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (d_pos j).le h1.2 _) (by norm_num)
        simp_rw [ite_eq_right H]
        exact le_trans (cold_mean _ _ t h₀) (by linarith)
      calc
        _ = ∑ y∈e, stats t (recital g y) := Ex_finset_sum _ _ _
        _ ≤ ∑ _y∈e, (10:ℝ)^30*x^3 := Finset.sum_le_sum fun y _ => Hi y
        _ ≤ _ := by
          simp only [Finset.sum_const,nsmul_eq_mul]
          unfold R sticker; change (e.card:ℝ)*_ ≤ 10^30*x^3*_
          rw [mul_comm (10^30*x^3)]
          apply mul_le_mul_of_nonneg_right HX
          have h1 : 1 ≤ x := (amount_limits s j).1; positivity
    have HV := stats_cons h₀
    rw [stats_cons h₀,stats_cons h₀]
    have HI (b : Bool) : stats (k b) (showScore p v j) ≤ 1+R*stats (k b) (minted p v) :=
      let H := ih b (hk b) (hK.climb.child b) (show entitled g _ j from hz) v
      hR b ▸ H
    let U := uniform Bool
    have H := U.Ex_mono HI
    rw [Ex_add (f:=fun _ => _),Ex_const,Ex_lmul] at H
    change stats (ran s q k) C ≤ R at Hc
    rw [stats_cons h₀] at Hc
    by_cases HA : cardStep p (turn p c q) <;> by_cases HP : freshAt p c q
    all_goals
      simp_rw [showScore, boom, minted]
      simp only [HA,HP,birth,ite_false,ite_true]
      unfold t v R C U at *
      unfold stats at *
      try simp_rw [Ex_add]
      simp_rw [Ex_const]
      unfold g grade at *
      linarith

end Troupe


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
