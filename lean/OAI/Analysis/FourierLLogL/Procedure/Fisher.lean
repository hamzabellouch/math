import OAI.Analysis.FourierLLogL.Procedure.Addition
import OAI.Analysis.FourierLLogL.Procedure.Counts

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal

variable {J M j : ℕ} {s : Scene M} {f : Grid M → ℝ}
open scoped Classical

/-- locally charge entropy to height. useful for static. -/
lemma local_deficit_dry (s : Scene M) {α : Type} [Fintype α] (P : Law α)
    (hp : s.here.ok M) (hh : 0 ≤ s.wage) (hm : 0 < s.mass)
    (d : ℝ) (h : ∀ x, s.wage x ≤ exp d) :
    deficit s (fun _ => P) ≤ d-log s.mass := by
  rw [deficit,privateH_const]
  let q := s.actor
  suffices H : levels s + q.Ex (fun x => log (q x)) ≤ d-log s.mass by
    change levels s - entropy q ≤ _
    unfold entropy crossE; rw [Ex_neg]; linarith
  rcases s with ⟨p,f,c,e,n⟩
  let s : Scene M := ⟨p,f,c,e,n⟩
  change levels s + _ ≤ _
  conv_lhs => lhs; rw [← Ex_const q (levels s)]
  rw [← Ex_add]
  refine le_trans (b:=q.Ex (fun _ => d-log s.mass)) (Ex_mono_mem _ fun x hx => ?_) (by rw [Ex_const])
  have hi := actor_def (s:=s) hp hh hm
  have ht : x ∈ p.block M := piece_support hp hi x hx
  have H (x' : Grid M) (hx' : x'∈p.block M) :
      log (p.dice M x') = -levels s := by
    have H1 : p.lev ≤ M := hp.2
    rw [dice_apply hp,ite_eq_left hx',
      log_mul (side_pos _).ne' (inv_pos.mpr p.len_pos).ne',levels,len]
    simp_rw [log_inv,side_pow_two, Real.log_inv,log_pow]
    dsimp [s]; rw [Nat.cast_sub H1]; ring
  have he : q x ≤ p.dice M x * exp d / s.mass := by
    rw [show q x = _ from hi x]
    unfold wt
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (h _) ((p.dice M).nonneg _)) hm.le
  have hi' : 0 < p.dice M x := (dice_positive hp).mpr ht
  have hc' := log_le_log hx he
  rw [log_div (mul_pos hi' (exp_pos _)).ne' hm.ne',log_mul hi'.ne' (exp_pos _).ne',
    log_exp,H _ ht] at hc'
  change levels s+log (q x) ≤ _
  linarith

lemma no_label (x : Grid M) : channel (0:Form M) x = uniform _ := by
  apply Law.ext; intro i
  rw [ch_K,K_eq,F_zero,form_zero,sub_zero,exp_zero,uniform_side,mul_one]

def givenD (s : Scene M) := deficit s (channel s.fund.mood)

def massInfo (s : Scene M) :=
    1/4*(s.norm/s.mass)*fisher s (channel s.fund.mood)

namespace Event
def infoFee (e : Event j M) := match e with
    | .march s .move _ => massInfo s
    | _ => 0
end Event

namespace Road

lemma one_split_price :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ, ∀ v : Turn j s,
      ∀ t : (b : Bool) → Road j M (v.fork.dst b), Trusted J f (.fork s v t) →

      v.fork.probs.Ex (fun b =>
        givenD (v.fork.dst b) - 500*(v.fork.dst b).fund.spend +
        infoFee (.march s v b) - memFee (.march s v b)) ≤
          givenD s - 500*s.fund.spend := by
  filter_upwards [priced_change] with j hj M J s f v t h
  have hb := branchTrusted h
  obtain ⟨ha,hh,he,h⟩ := h
  have hL := hh.1.2.2
  let k := channel s.fund.mood
  cases v with
  | move =>
    have hx : s.here.lev < M := (rootSafe (h false)).within.2
    have hZ := space_deficit s k ha.within.1 hx ha.positive hL (by
      by_contra! hv; exact hh.2.2 (show enter s from by unfold enter; linarith))
    change (step s).probs.Ex (fun b => deficit (s.smaller b) k -
      500*s.fund.spend + _ - (0+0)) ≤ _
    simp only [add_zero,sub_zero,infoFee]
    rw [Ex_add,Ex_sub,Ex_const,Ex_const]
    unfold massInfo givenD k at *; linarith
  | ask u =>
    let v := toss s u
    let d (b : Bool) := deficit (v.dst b) k
    have hX (b : Bool) (hv : 0 < v.probs b) :
      givenD (v.dst b) - 500*(v.dst b).fund.spend ≤ d b - 500*s.fund.spend := by
      cases b with
      | false => exact le_rfl
      | true =>
        have hh := hj M J s f u ha (rootSafe (h true)) ((true_mass hb).mp hv) he.2
        change deficit (s.win u) (channel (u.next s.fund.mood)) -500*(s.fund.spend+u.credit) ≤
          deficit (s.win u) (channel s.fund.mood) - 500*s.fund.spend
        linarith
    let Q := v.probs
    have ht : Q.Ex (fun b => memFee (.march s (.ask u) b)) = Q.entropy := by
      unfold entropy crossE; congr 1
      funext b; cases b <;> simp [memFee,failFee,winFee,surprise] <;> rfl
    have hv := member_deficit s k u hb
    change Q.Ex (fun b => givenD (v.dst b) - 500*(v.dst b).fund.spend + infoFee (.march s (.ask u) b) - memFee (.march s (.ask u) b)) ≤ _
    rw [Ex_sub,Ex_add,ht]
    simp only [infoFee,Ex_const,add_zero]
    have HE := Q.Ex_mono_mem hX
    rw [Ex_sub (g:=fun _ => _)] at HE
    unfold Q at *; change _ ≤ deficit s k - _
    change v.probs.Ex d ≤ _ at hv
    rw [Ex_const] at HE; change v.probs.Ex d ≤ deficit s k + v.probs.entropy at hv
    linarith

lemma fisher_bound :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ f : Grid M → ℝ,
      (∀ x, f x ≤ exp (height j)) →
      let s := beginPlay f true
      ∀ t : Road j M s, Trusted J f t → 1/Thermal.H j ≤ s.mass →
        t.flatFee infoFee ≤ limitC* height j := by
  filter_upwards [one_split_price,Fund.fund_est,mem_budget,hpoly limitC 1,Fund.envelope_scale]
    with j he hg hs hC ha M J f hF s t ht hm
  let a := Thermal.H j; let d := height j; let V := (10:ℝ)^19*d
  have HI (s : Scene M) (t : Road j M s) (h : t.Trusted J f) (hM : 0 < s.mass) :
      t.flatFee infoFee - t.flatFee memFee ≤ givenD s - 500*s.fund.spend + 500*V := by
    induction t with
    | finish s b =>
      have hh := h.1
      have hf := ((hg M).2 _ _ hh.capital).1
      simp_rw [flat_finish]
      have h1 : 0 ≤ givenD s := deficit_nonneg _ hh.within hh.positive hM _
      have h2 := hh.capital.solvent
      unfold reserve capA at h2
      unfold V d
      have he : 1 ≤ height j := ha.2.2.1
      linarith
    | push s v t ih =>
      have hi := ih h.2.2.2 (by rw [pace_mass]; exact hM)
      rw [flat_push,flat_push]
      simp only [infoFee,memFee, failFee,winFee,zero_add]
      cases v <;> exact hi
    | fork s v t ih =>
      let Q := v.fork.probs
      let F := fun b => givenD (v.fork.dst b)-500*(v.fork.dst b).fund.spend
      have hX (b : Bool) (hb : 0 < Q b) := ih b (h.2.2.2 b) ((true_mass (branchTrusted h)).mp hb)
      have hi := Q.Ex_mono_mem hX
      have hv := he M J s f v t h
      simp_rw [flat_fork _ _ h, Ex_add]
      change Q.Ex (fun b => F b + _ - _) ≤ _ at hv
      change Q.Ex _ ≤ Q.Ex (fun b => F b + _) at hi
      rw [Ex_sub _,Ex_add _ (g:=fun _ => _)] at hi
      rw [Ex_const] at hi
      rw [Ex_sub,Ex_add] at hv
      unfold Q at *; linarith
  have hp : 0 < a := H_pos _
  have hC' : limitC*a ≤ d := by simpa only [pow_one] using hC
  have hm' : 0 < s.mass := lt_of_lt_of_le (by positivity : 0<1/a) hm
  have hf := rootSafe ht
  have Ht : givenD s ≤ d+a := by
    change deficit s (channel 0) ≤ d+a
    rw [funext no_label]
    apply le_trans (local_deficit_dry s (uniform (Grid M)) hf.within hf.positive hm' d hF)
    have he := log_le_log (by positivity : 0<1/a) hm
    rw [one_div,log_inv] at he
    linarith [log_le_sub_one_of_pos hp]
  have HZ := HI _ _ ht hm'
  have hx := (hs M J s f t ht hm').2
  change t.flatFee memFee ≤ limitC*a at hx
  change _ ≤ _-500*0+_ at HZ
  change _ ≤ limitC*d
  unfold limitC V at *
  nlinarith

end Road
end FourierLLogL.Dyadic.Procedure

end OAI
