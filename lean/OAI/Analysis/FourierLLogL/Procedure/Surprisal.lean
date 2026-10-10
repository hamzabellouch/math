import OAI.Analysis.FourierLLogL.Procedure.Road
/-! # Increments in the input model -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Journal Event
variable {M J j : ℕ} {s : Scene M}
open scoped Classical

namespace Event
def surprise (v : Turn j s) (b : Bool) := -log (v.fork.probs b)
def failFee (q : Event j M) : ℝ := match q with
    | .march _ (.ask u) false => surprise (.ask u) false
    | _ => 0
def winFee (q : Event j M) : ℝ := match q with
    | .march _ (.ask u) true => surprise (.ask u) true
    | _ => 0
def memFee (q : Event j M) := winFee q + failFee q
def count (q : Event j M) : ℝ := match q with
    | .march _ (.ask _) true => 1
    | _ => 0
def tried (q : Event j M) : ℝ := match q with
    | .march _ (.ask _) _ => 1
    | _ => 0
def likelihood (q : Event j M) : ℝ := match q with
    | .march s .move b => log (2*(step s).probs b)
    | _ => 0

lemma surprise_nonneg (v : Turn j s) (b : Bool) : 0 ≤ surprise v b :=
    neg_nonneg.mpr (Real.log_nonpos (v.fork.probs.nonneg b) (v.fork.probs.le_one b))
lemma fee_bounds (q : Event j M) : 0 ≤ failFee q ∧ 0 ≤ winFee q ∧ 0 ≤ tried q := by
  cases q with
  | pace _ _ => exact ⟨le_rfl,le_rfl,le_rfl⟩
  | march s v b =>
    cases v with
    | move => exact ⟨le_rfl,le_rfl,le_rfl⟩
    | ask u => cases b
               · exact ⟨surprise_nonneg _ _,le_rfl, zero_le_one⟩
               · exact ⟨le_rfl,surprise_nonneg _ _,zero_le_one⟩

lemma price_space (v : Turn j s) (b : Bool) (h : v.fork.TrueLaw) (hm : 0 < s.mass)
    (hh : 0 < v.fork.probs b) :
    likelihood (.march s v b) =
      log (v.fork.dst b).mass - log s.mass + memFee (.march s v b) := by
  cases v with
  | move =>
    change log _ = log (s.smaller b).mass-log s.mass+(0+0)
    change 0 < (step s).probs b at hh
    rw [step_mass h b,log_mul (mul_pos (by norm_num : (0:ℝ)<2) hh).ne' hm.ne']
    simp
  | ask u =>
    have he (b) :
        memFee (.march s (.ask u) b) = -log ((toss s u).probs b) := by
      cases b <;> simp [memFee,failFee,winFee,surprise,Turn.fork]
    rw [he]
    change 0 = log ((toss s u).dst b).mass - log s.mass + -log ((toss s u).probs b)
    change 0 < (toss s u).probs b at hh
    rw [toss_mass h b,Real.log_mul hh.ne' hm.ne']; ring

lemma surprisal_cost (s : Scene M) (u : Update j M s.here)
    (h : u.Good capA s.fund.mood s.actor) :
    surprise (.ask u) true ≤
      2000000*H j/height j * u.credit := by
  let c := surprise (.ask u) true
  let p := (toss s u).probs true
  let i := u.ix
  have hp : beta i /2 ≤ p := by unfold p; rw [success_prob]; exact h.bias
  have hc : c ≤ 200 * (1+i) := by
    have h1 := log_le_log (div_pos (beta_pos i) (by norm_num)) hp
    rw [log_div (beta_pos _).ne' (by norm_num)] at h1
    change -log p ≤ _
    linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),beta_log i,
      Nat.cast_nonneg (α:=ℝ) i]
  have he := h.duration
  let d := height j
  let a := H j
  have hD : 0 < d := d_pos j
  have ha : 0 < a := H_pos j
  calc
    _ ≤ _ := hc
    _ ≤ (2000000*a/d) * (eps * u.encoded capA) := by
      change (200:ℝ)* (1+i) ≤ (2000000*a/d) * ((1/10000)*(codeWeight capA*d/a*(1+i)))
      have hW := code_ge cap_ok
      field_simp
      nlinarith [show 0 < (1:ℝ)+i by positivity]
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2000000*a/d)

end Event

namespace Journal
def membership (z : Journal j M) := z.fee memFee
def creditSum (z : Journal j M) := z.fee winFee
def debit (z : Journal j M) := z.fee failFee
def like (z : Journal j M) := z.fee likelihood

lemma mem_parts (l : Journal j M) : membership l = creditSum l+debit l := by
  unfold membership creditSum debit fee
  suffices HH : ∀ l : List (Event j M),
      (l.map memFee).sum=(l.map winFee).sum+(l.map failFee).sum from HH _
  intro l; induction l with
  | nil => simp
  | cons i t ih => simp only [List.map_cons,List.sum_cons,ih,memFee]; ring
lemma positive_fee (l : Journal j M) (f : Event j M → ℝ) (h : ∀ i, 0 ≤ f i) : 0 ≤ l.fee f := by
  unfold fee; apply List.sum_nonneg; simpa using fun i (_ : i∈l.events) => h i
lemma positive_mem (l : Journal j M) : 0 ≤ membership l :=
  l.positive_fee memFee (fun i => add_nonneg (fee_bounds i).2.1 (fee_bounds i).1)

end Journal

namespace Road

lemma final_sound {t : Road j M s} {f : Grid M → ℝ} (h : t.Trusted J f)
    (hm : 0 < s.mass) {x : Grid M} (hx : 0 < s.actor x) :
    let l := hike t x
    l.done.Safe j J f ∧ (l.froze=true → l.done.retire j) ∧ 0 < l.done.mass ∧
      l.like = log l.done.mass-log s.mass+l.membership ∧
      (s.fund.uses:ℝ)+l.fee count=l.done.fund.uses ∧
      l.creditSum ≤ 2000000*H j/height j * (l.done.fund.spend-s.fund.spend) := by
  classical
  let a := 2000000*H j/height j
  intro l
  let g := fun (s : Scene M) (l : Journal j M) => l.done.Safe j J f ∧
    (l.froze=true → l.done.retire j) ∧ 0 < l.done.mass ∧
      l.like = log l.done.mass-log s.mass+l.membership ∧
      (s.fund.uses:ℝ)+l.fee count=l.done.fund.uses ∧
      l.creditSum ≤ a*(l.done.fund.spend-s.fund.spend)
  change g s l
  refine travel (good:=g) ?_ ?_ ?_ t h hm hx
  · intro s b h hb hm
    refine ⟨h,fun hi => ?_,hm,?_⟩
    · change b=true at hi; rw [ite_eq_left hi] at hb; exact hb.2
    simp [creditSum,membership,like,fee]
  · intro s v h hb hv l H
    rcases H with ⟨H₁,H₂,H₃,H₄,H₅,H₆⟩
    refine ⟨H₁,H₂,H₃,?_⟩
    rw [pace_mass] at H₄
    have he : (s.pace v).fund=s.fund := by cases v <;> rfl
    rw [he] at H₅ H₆
    simp only [like,membership,creditSum] at *
    rw [fee_pre,fee_pre,fee_pre,fee_pre]
    dsimp only [likelihood,memFee,Event.count,winFee,failFee,prepend]
    simp only [zero_add,add_zero]
    exact ⟨H₄,H₅,H₆⟩

  · intro s v h he hl hv b hh l H
    obtain ⟨Hx,Hy,Hz,H₁,H₂,H₃⟩ := H
    refine ⟨Hx,Hy,Hz,?_,?_⟩
    · unfold like membership
      rw [fee_pre,fee_pre]
      have Hi := price_space v b hv he.1.2.2 hh
      unfold like membership at H₁
      dsimp only [prepend]
      linarith
    unfold creditSum; rw [fee_pre,fee_pre]; unfold creditSum at H₃
    dsimp only [prepend]
    cases v with
    | move =>
      change (s.fund.uses:ℝ)+(0+l.fee count)=_ ∧ 0 + _ ≤ _
      rw [zero_add,zero_add]
      exact ⟨H₂,H₃⟩
    | ask u =>
      have HH : surprise (Turn.ask (j:=j) u) true ≤ a*u.credit :=
        surprisal_cost s u hl.2
      cases b
      · change (s.fund.uses:ℝ)+(0+l.fee count)=_ ∧ 0+_ ≤ _
        rw [zero_add,zero_add]; exact ⟨H₂,H₃⟩
      · change ((s.fund.uses+1:ℕ):ℝ)+l.fee count= _ at H₂
        change l.fee winFee ≤ a * (_-(s.fund.spend+u.credit)) at H₃
        change _+(1+_)=_ ∧ surprise (.ask u) _+_ ≤ _
        push_cast at *
        constructor; linarith; linarith

/-- Positive exponential fee supported on path prefixes. -/
lemma capital_bound {s : Scene M} (F : Event j M → ℝ)
    (hp : ∀ s : Scene M, ∀ v : Pace, F (Event.pace s v)=0)
    (hf : ∀ s : Scene M, ∀ v : Turn j s,
      v.fork.probs.Ex (fun b => exp (F (.march s v b))) ≤ 1)
    (t : Road j M s) {f : Grid M → ℝ} (h : t.Trusted J f) (hm : 0 < s.mass) :
    t.expHike (fun l _x => exp (l.fee F)) ≤ 1 := by
  induction t with
  | finish s b => simp [expHike,hike, fee,Ex_const]
  | push s v t ih =>
    rw [Ex_hike_push]
    simp_rw [fee_pre,hp,zero_add]
    exact ih h.2.2.2 (by rw [pace_mass]; exact hm)
  | fork s v t ih =>
    rw [Ex_hike_fork h]; simp_rw [fee_pre, exp_add,expHike,Ex_lmul]
    apply le_trans _ (hf s v)
    apply Ex_mono_mem; intro b hb
    have hi := ih b (h.2.2.2 b) ((true_mass (branchTrusted h)).mp hb)
    exact mul_le_of_le_one_right (exp_nonneg _) hi

end Road
end FourierLLogL.Dyadic.Procedure

end OAI
