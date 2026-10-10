import OAI.Analysis.FourierLLogL.Paths.Ticket
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

def chooseCap (g : Grade) (l : Path M) := Nat.log 2 (broadMass l g)+1
lemma choice_bounds (g : Grade) (l : Path M) :
    let x := chooseCap g l
    x ≤ M+2 ∧ broadMass l g ≤ rangeIx x ∧ scaleC x ≤ 2*((broadMass l g:ℝ)+1) := by
  intro x
  let n := broadMass l g
  have hx : 2^x ≤ 2*(n+1) := (by
    change 2^(Nat.log 2 n+1) ≤ _
    have H := Nat.pow_log_le_add_one 2 n
    rw [pow_add]; omega)
  have H : n ≤ 2^M := by
    apply le_trans (Finset.card_le_univ _) (by rw [ZMod.card])
  refine ⟨?_,(Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) _).le,?_⟩
  · by_contra! hh
    have HI : 2^(M+2) < 2^x := Nat.pow_lt_pow_right (by omega) hh
    have HF : 0 < 2^M := by positivity
    rw [pow_add] at HI
    norm_num at HI; omega
  · unfold scaleC
    change (2:ℝ)^x ≤ 2*((n:ℝ)+1)
    exact_mod_cast hx

def heartP (s : Scene M) (g : Grade) (j : ℕ) :=
    10^82*(scaleC g.i)^14 * (amount s j)^4 * exp (cutBook g s j)

lemma booking :
    ∀ᶠ j : ℕ in atTop,
      ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ, ∀ t : Thread M s,
        t.Following j J f → Fit s → entry s →
        (∀ x,f x ≤ exp (height j)) →
        ∀ g : Grade, entitled g s j → ∀ m : ℕ,
          stats t (showScore (stage g m) (vacant M) j) ≤ heartP s g j* scaleC m^4 := by
  filter_upwards [paint_birth,prelude] with j h₁ h₂ M J s f t h hh he hf g hg m
  apply (h₁ M J _ _ f (stage g m) h hh hg hf _).trans
  let x := scaleC g.i; let y := scaleC m; let L := amount s j; let z := exp (cutBook g s j)
  have hx : 1 ≤ x := scale_one _; have hy : 1 ≤ y := scale_one _
  have hL : 1 ≤ L := (amount_limits _ _).1
  have hz : 1 ≤ z := one_le_exp (cut_nonneg _ _ _)
  have HV := (h₂ M J s f t h hh he hf (stage g m)).1
  change stats t _ ≤ 10^50*x^14*L*y^4 at HV
  change 1+10^30*L^3*z*_ ≤ 10^82*x^14*L^4*z*y^4
  apply le_trans (add_le_add_right (mul_le_mul_of_nonneg_left HV (by positivity : 0 ≤ 10^30*L^3*z)) 1)
  let r : ℝ := x^14*L^4*z*y^4
  have hR : 1 ≤ r := by
    unfold r
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx) (one_le_pow₀ hL)) hz) (one_le_pow₀ hy)
  nlinarith [show r=x^14*L^4*z*y^4 from rfl]

def hush (g : Grade) (j : ℕ) (m : ℕ) (l : Path M) :=
    showScore (stage g m) (vacant M) j l / scaleC m^5

def spillScore (g : Grade) (j : ℕ) (l : Path M) :=
    1 + ∑ m∈Finset.range (M+3),hush g j m l

lemma hush_pos (g : Grade) (j m : ℕ) (l : Path M) :
    0 < hush g j m l := div_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
      (show_one _ _ _ _)) (pow_pos (scale_pos _) _)
lemma spill_share (g : Grade) (j : ℕ) (l : Path M) :
    let k := chooseCap g l
    let S := spillScore g j l
    1 ≤ S ∧ showScore (stage g k) (vacant M) j l ≤ S*scaleC k^5 := by
  intro k S
  have ha : ∀ m, 0 ≤ hush g j m l := fun _ => (hush_pos _ _ _ _).le
  constructor
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => ha _))
  · apply (div_le_iff₀ (pow_pos (scale_pos k) _)).mp
    change hush g j k l ≤ _
    unfold S spillScore
    have h := (choice_bounds g l).1
    have he : k∈Finset.range (M+3) := Finset.mem_range.mpr (by unfold k; omega)
    exact le_trans (Finset.single_le_sum (f:=fun i => hush g j i l) (fun _ _ => ha _) he) (le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1))

lemma spill_bound :
    ∀ᶠ j : ℕ in atTop,
      ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ, ∀ t : Thread M s,
        t.Following j J f → Fit s → entry s →
        (∀ x,f x ≤ exp (height j)) →
        ∀ g : Grade, entitled g s j → stats t (spillScore g j) ≤ 4*heartP s g j := by
  filter_upwards [booking] with j hj M J s f t h hh he hf g hg
  let x := heartP s g j
  have HI : 1 ≤ x := by
    unfold x heartP
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (scale_one _))) (one_le_pow₀ (amount_limits _ _).1)) (one_le_exp (cut_nonneg _ _ _))
  have HA (m) : stats t (hush g j m) ≤ x * side m := by
    let B := scaleC m
    have HE := hj M J s f t h hh he hf g hg m
    have hp : 0 < B := scale_pos _
    calc
      _ = stats t (showScore (stage g m) _ j) / B^5 := by
        unfold hush stats B; simp_rw [div_eq_mul_inv,Ex_mul]
      _ ≤ x * B^4 / B^5 := div_le_div_of_nonneg_right HE (pow_nonneg hp.le _)
      _ = x * side m := by rw [scale_side]; unfold B; have := scale_pos m; field_simp
  let R := Finset.range (M+3)
  have H (k : ℕ) : ∑ i∈Finset.range k, side i ≤ 2 := by
    have h₁ := geom_sum_mul_neg ((1:ℝ)/2) k
    unfold side; nlinarith [pow_nonneg (show (0:ℝ) ≤ 1/2 by norm_num) k]
  calc
    _ = 1+∑ i∈R,stats t (hush g j i) := by
      unfold stats spillScore; rw [Ex_add (f:=fun _ => 1),Ex_const,Ex_finset_sum]
    _ ≤ 1+∑ i∈R,x*side i := by apply add_le_add_right; exact Finset.sum_le_sum fun i _ => HA i
    _ ≤ _ := by rw [← Finset.mul_sum]; unfold R; change _ ≤ 4*x; nlinarith [H (M+3)]

def timex (g : Grade) (j : ℕ) (l : Path M) :=
    let v := scaleC (chooseCap g l)
    2*(log (spillScore g j l)+5*log v)

lemma timex_scores (g : Grade) (j : ℕ) (l : Path M) :
    0 ≤ timex g j l ∧
      2*log (showScore (stage g (chooseCap g l)) (vacant M) j l) ≤ timex g j l := by
  let v := scaleC (chooseCap g l)
  have hp : 1 ≤ v := scale_one _
  obtain ⟨h₁,h₂⟩ := spill_share g j l
  let a := spillScore g j l
  change 1 ≤ a at h₁
  let p := stage g (chooseCap g l)
  let s := showScore p (vacant M) j l
  change s ≤ a*v^5 at h₂
  have Hs : 0 < s := lt_of_lt_of_le (by norm_num) (show_one _ _ _ _)
  have hi := log_le_log Hs h₂
  rw [log_mul (by positivity) (by positivity), log_pow] at hi; push_cast at hi
  change 0 ≤ 2*(log a+_) ∧ 2*log s ≤ 2*(log a+5*log v)
  constructor
  · apply mul_nonneg (by norm_num); exact add_nonneg (log_nonneg h₁) (mul_nonneg (by norm_num) (log_nonneg hp))
  linarith

lemma stat_jensen (t : Thread M s) (f : Path M→ℝ) (hp : ∀ l, 0 < f l)
    (x : ℝ) (hh : 0 < x) (h : stats t f ≤ x) :
    stats t (fun l => log (f l)) ≤ log x := by
  let P := s.here.dice M
  have HE (l) : log (f l) ≤ log x + (x⁻¹ * f l-1) := by
    have H := log_le_sub_one_of_pos (div_pos (hp l) hh)
    rw [log_div (hp l).ne' hh.ne',div_eq_inv_mul] at H; linarith
  have HC := P.Ex_mono (fun x => HE (t.stream x))
  rw [Ex_add _ (f:=fun _ => _),Ex_sub,Ex_const,Ex_lmul,Ex_const] at HC
  change _ ≤ log x +(x⁻¹*stats t f-1) at HC
  apply HC.trans; nlinarith [inv_pos.2 hh,inv_mul_cancel₀ hh.ne']

def dBase (g : Grade) (s : Scene M) (j : ℕ) :=
    1+log (amount s j)+g.i

lemma paid_levels :
    ∀ᶠ j : ℕ in atTop,
      ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ, ∀ t : Thread M s,
        t.Following j J f → Fit s → entry s →
        (∀ x,f x ≤ exp (height j)) →
        ∀ g : Grade, entitled g s j →
          stats t (timex g j) ≤ 10^7*(dBase g s j+cutBook g s j) ∧
          stats t (fun l => (chooseCap g l:ℝ)) ≤ 10^6*dBase g s j := by
  filter_upwards [spill_bound,prelude] with j h₁ h₂ M J s f t h hh he hf g hg
  let x := amount s j; let y := scaleC g.i; let z := cutBook g s j
  let B := spillScore (M:=M) g j; let Q (l : Path M) := scaleC (chooseCap g l)
  have hx : 1 ≤ x := (amount_limits _ _).1; have hy : 1 ≤ y := scale_one _
  have hz : 0 ≤ z := cut_nonneg _ _ _
  have hH := (h₂ M J s f t h hh he hf (stage g 0)).2
  change stats t (fun l => (broadMass l g:ℝ)) ≤ 10^31*y^6*x at hH
  have he₁ : stats t Q ≤ 10^33*y^6*x := by
    let C (l : Path M) := (broadMass l g:ℝ)
    calc
      _ ≤ stats t (fun l => 2*(C l+1)) := by
        apply Ex_mono; intro i; exact (choice_bounds g (t.stream i)).2.2
      _ = 2*(stats t C+1) := by unfold stats; rw [Ex_lmul,Ex_add,Ex_const]
      _ ≤ _ := by unfold C; nlinarith [one_le_pow₀ hy (n:=6)]
  let T := dBase g s j
  have hi : log y ≤ g.i := by
    unfold y scaleC; rw [log_pow]
    have Hx : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    exact mul_le_of_le_one_right (by positivity) Hx
  have HI : 1 ≤ T := by unfold T dBase; linarith [log_nonneg hx,Nat.cast_nonneg (α:=ℝ) g.i]
  have hQ : stats t (fun l => log (Q l)) ≤ 10000*T := by
    apply (stat_jensen t Q (fun _ => scale_pos _) _ (by positivity) he₁).trans
    rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_pow,log_pow]; push_cast
    change _ ≤ 10000*(1+log x+_)
    linarith [log_nonneg hx,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10),Nat.cast_nonneg (α:=ℝ) g.i]
  have HR : stats t (fun l => log (B l)) ≤ z+10000*T := by
    have hh' := h₁ M J s f t h hh he hf g hg
    change stats t B ≤ 4*(10^82*y^14*x^4*exp z) at hh'
    apply (stat_jensen t B (fun l => lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (spill_share g j l).1)
      _ (by positivity) hh').trans
    rw [log_mul (by positivity) (by positivity),log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by positivity),log_mul (by positivity) (by positivity),
      log_pow,log_pow,log_pow,log_exp]; push_cast
    change _ ≤ z+10000*(1+log x+_)
    linarith [log_nonneg hx,Nat.cast_nonneg (α:=ℝ) g.i, log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4),log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10)]
  constructor
  · change stats t (fun l => 2*(log (B l)+5*log (Q l))) ≤ 10^7*(T+z)
    unfold stats at *; rw [Ex_lmul,Ex_add,Ex_lmul]; linarith
  have HB (l : Path M) : (chooseCap g l:ℝ) ≤ 2*log (Q l) := by
    unfold Q scaleC; rw [log_pow]
    nlinarith [log_two_gt_d9,Nat.cast_nonneg (α:=ℝ) (chooseCap g l)]
  apply le_trans (b:=stats t (fun l => 2*log (Q l))) (Ex_mono _ (fun i => HB (t.stream i)))
  unfold stats at *; rw [Ex_lmul]; change _ ≤ 10^6*T; linarith

end Troupe


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
