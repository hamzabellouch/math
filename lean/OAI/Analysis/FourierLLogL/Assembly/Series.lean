import OAI.Analysis.FourierLLogL.Assembly.Festival
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
open Plot

def miniStage (j i : ℕ) (L : Path M) :=
    20000*scalarSticker i j L+
      4*side i*(billWait (tagL i) j L:ℝ)
def rooms (c : Bool) (j : ℕ) (L : Path M) :=
    1+ ∑ i∈playsL j M c, miniStage j i L

def nakedStage (i j : ℕ) (L : Path M) :=
    (1+fullKills L)/depthRate i + depthRate i*timex (tagM i) j L+
      (billWait (tagM (i-1)) j L:ℝ)
def palaces (j : ℕ) (L : Path M) :=
    4*(billWait (tagM (mainIx j)) j L:ℝ)+
      10^20* ∑ i∈Finset.Ico 0 (mainIx j+1), nakedStage i j L

lemma decayed (n : ℕ) : depthRate (n+1) ≤ 3/4*depthRate n := by
  let x := depthRate (n+1); let y := depthRate n
  have h := rate_easy (n+1); have hv := rate_easy n
  obtain ⟨ha,hb,hc⟩ := h
  rw [side_succ] at hc
  nlinarith

lemma weight_decay (x : ℝ) (hx : 0 ≤ x) (n m : ℕ) (h : n ≤ m) :
    ∑ i∈Finset.Ico n m, depthRate i*(x+1+i) ≤ 10*depthRate n*(x+10+n) := by
  suffices hh : ∀ k n : ℕ, n+k=m →
      ∑ i∈Finset.Ico n m, depthRate i*(x+1+i) ≤ 10*depthRate n*(x+10+n) from hh (m-n) n (by omega)
  intro k; induction k with
  | zero =>
    intro n he; simp only [Nat.add_zero] at he
    rw [he]; simp only [Finset.Ico_self,Finset.sum_empty]
    have := (rate_easy m).1; positivity
  | succ k ih =>
    intro n he
    rw [start_ico _ n (by omega)]
    apply le_trans (add_le_add_right (ih (n+1) (by omega)) (depthRate n*(x+1+n)))
    push_cast
    have H := decayed n; have hp := (rate_easy n).1
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]

lemma waiting_fee {g : Grade} {t : Thread M s} {j : ℕ}
    (h : stats t (fun l => (chooseCap g l:ℝ)) ≤ 10^6*dBase g s j) :
    stats t (fun l => (billWait g j l:ℝ)) ≤ 10^10*(dBase g s j+Thermal.H j) := by
  let U := s.here.dice M; let f (x : Grid M) := (↑(chooseCap g (t.stream x)):ℝ)
  have HE : stats t (fun l => (billWait g j l:ℝ)) =
      1000*(1+U.Ex f+g.i+(ell j:ℝ)) := by
    unfold stats billWait latency
    push_cast
    simp_rw [heroPlot,stage]
    rw [Ex_lmul,Ex_add,Ex_add,Ex_add (f:=fun _ => 1)]
    simp only [Ex_const]
    rfl
  rw [HE]
  change U.Ex f ≤ _ at h
  have Hi : (ell j:ℝ) ≤ Thermal.H j := by unfold Thermal.H; exact_mod_cast ell_le_h j
  have H := log_nonneg (amount_limits s j).1
  unfold dBase at *; linarith [H_pos j,Nat.cast_nonneg (α:=ℝ) g.i]

lemma size_stat {t : Thread M s} (h : t.Following j J f) (hh : Fit s) (hv : entry s) :
    stats t fullKills ≤ 1 :=
  le_trans (deaths t h hh.pos) (entry_share hh hv).le

lemma rooms_fee :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ, ∀ t : Thread M s,
      t.Following j J f → Fit s → entry s →
        (∀ x, f x ≤ exp (height j)) →
       ∀ c : Bool, stats t (rooms c j) ≤ 1 + 10^30*depthRate (lowI j c)*amount s j := by
  filter_upwards [paid_levels,hpoly 20 1] with j hj hv M J s f t h hh hx hf c
  let n := lowI j c; let m := highI j M c
  let A := amount s j
  have hP : 1 ≤ A ∧ height j ≤ A := amount_limits _ _
  have hz : 20*Thermal.H j ≤ height j := by rw [pow_one] at hv; exact hv
  have H (i : ℕ) : stats t (miniStage j i) ≤ 10^20*depthRate i*(A+1+i) := by
    let g := tagL i; let a := depthRate i
    let H := dBase g s j
    have hi := hj M J s f t h hh hx hf g (fun x => Bool.noConfusion x)
    obtain ⟨h₁,h₂⟩ := hi
    have HC : H ≤ 2*(A+1+i) := by
      change 1+log A+(i:ℝ) ≤ _
      linarith [Real.log_le_sub_one_of_pos (by linarith : 0<A),Nat.cast_nonneg (α:=ℝ) i]
    have HT : cutBook g s j ≤ 1000*(A+1+i) := by
      unfold g cutBook tagL scLimit
      simp only [↓reduceIte,Bool.false_eq_true]
      unfold A amount; linarith
    have HE : stats t (timex g j) ≤ 10^11*(A+1+i) := by
      change stats t _ ≤ _*(H+_) at h₁
      linarith [Nat.cast_nonneg (α:=ℝ) i]
    have HR := waiting_fee h₂
    change stats t _ ≤ 10^10*(H+_) at HR
    let f (l : Path M) := ((billWait g j l):ℝ)
    have HJ : stats t f ≤ 10^11*(A+1+i) := by
      apply HR.trans
      linarith [Nat.cast_nonneg (α:=ℝ) i]
    have hE : stats t (miniStage j i) =
        20000*(a*(1+stats t fullKills+stats t (timex g j)))+(4*side i)*stats t f := by
      change stats t (fun L => 20000*(a*(1+_+_)) +4*side i * _) = _
      unfold stats
      rw [Ex_add _ (f:=fun l => _),Ex_lmul,Ex_lmul,Ex_lmul,Ex_add,Ex_add (f:=fun l=>1),Ex_const]
    rw [hE]
    have ha : 0 < a ∧ a ≤ 1 ∧ a^2=side i := rate_easy _
    have HA : side i ≤ a := by nlinarith
    have hv := size_stat h hh hx
    have HL : side i * stats t f ≤ a*(10^11*(A+1+i)) :=
      (mul_le_mul_of_nonneg_left HJ (side_pos i).le).trans
        (mul_le_mul_of_nonneg_right HA (by have hh := le_trans (by norm_num : (0:ℝ)≤1) hP.1; positivity))
    change _ ≤ 10^20*a*_
    nlinarith [mul_le_mul_of_nonneg_left HE ha.1.le,Nat.cast_nonneg (α:=ℝ) i,
      mul_nonneg ha.1.le (Nat.cast_nonneg (α:=ℝ) i)]
  have Hn : (n:ℝ) ≤ 19*Thermal.H j := by
    unfold n lowI
    split
    · exact (main_bounds j (Nat.le_add_right _ 3)).2.1
    · simp only [Nat.cast_zero]; have := H_pos j; positivity
  calc
    _ = 1+∑ i∈Finset.Ico n m, stats t (miniStage j i) := by
      unfold stats rooms; rw [Ex_add (f:=fun _ => 1),Ex_const,Ex_finset_sum]
      rfl
    _ ≤ 1+∑ i∈Finset.Ico n m, (10^20*depthRate i*(A+1+i)) :=
      add_le_add_right (Finset.sum_le_sum (fun i _ => H i)) _
    _ ≤ _ := by
      simp_rw [mul_assoc (a:=(10:ℝ)^20) (b:=depthRate _),
        ← Finset.mul_sum]
      have HC := weight_decay A (by linarith) n m (by unfold m highI n; omega)
      have H : A+10+n ≤ 1000*A := by linarith
      change _ ≤ 1+10^30*depthRate n*A
      nlinarith [mul_le_mul_of_nonneg_left H (rate_easy n).1.le,show
        0 ≤ depthRate n*A by apply mul_nonneg (rate_easy n).1.le; linarith]

lemma depth_at_main (j : ℕ) : depthRate (mainIx j) = 1/(Thermal.H j)^8 := by
  unfold depthRate; rw [bottom_level]
  rw [show 1/Thermal.H j^16=(1/Thermal.H j^8)^2 by ring]; rw [Real.sqrt_sq (by positivity)]

lemma palaces_fee :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ, ∀ t : Thread M s,
      t.Following j J f → Fit s → entry s →
        s.live=true → exp (-height j) ≤ s.norm →
        (∀ x, f x ≤ exp (height j)) →
       stats t (palaces j) ≤ 10^120*height j/Thermal.H j := by
  filter_upwards [paid_levels,hpoly_mix 1 11 1,eventually_ge_atTop 1] with j hj hT Hj
    M J s f t h hh hx he hhx hf
  let d := height j; let v := Thermal.H j; let k := mainIx j+1
  have hd : 1 ≤ d := one_le_pow₀ (by norm_num)
  have hV : 1 ≤ v := H_ge j
  have hv : 0 < v := by linarith
  have hk : (k:ℝ) ≤ 20*v := by
    unfold k; push_cast
    linarith [(main_bounds j (Nat.le_add_right (mainIx j) 3)).2.1,show Thermal.H j=v from rfl]
  let A := amount s j
  have hl : A ≤ 4*d := by
    have H := log_le_log (exp_pos _) hhx
    rw [log_exp] at H
    change d+max _ 0 + 2 ≤ _
    have he' : max (-log s.norm) 0 ≤ d := max_le (by unfold d; linarith) (by linarith)
    linarith
  let m := (j:ℝ)
  have hm : 1 ≤ m := by unfold m; exact_mod_cast Hj
  have HP : v^11*m ≤ d := by simpa only [pow_one,one_mul] using hT
  have hA : log A ≤ 4+m := by
    have Hx : 1 ≤ A := (amount_limits _ _).1
    apply (log_le_log (show 0 < A by linarith) hl).trans
    unfold d; rw [log_mul (by positivity) (d_pos j).ne',height, log_pow]
    unfold m
    have hU : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
    nlinarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4),Nat.cast_nonneg (α:=ℝ) j]
  have hP (i : ℕ) (hK : i < k) := hj M J s f t h hh hx hf (tagM i) (fun _ =>
    ⟨(by change i ≤ mainIx j; unfold k at hK; omega),he⟩)
  have HR (i : ℕ) (hi : i<k) :
      stats t (fun l => (billWait (tagM i) j l:ℝ)) ≤ 10^12*(v+m) := by
    apply (waiting_fee (hP i hi).2).trans
    change (10:ℝ)^10*(1+log A+(i:ℝ)+v) ≤ _
    have HH : (i:ℝ) ≤ k := Nat.cast_le.mpr hi.le
    linarith
  have HX : m ≤ d/v := (le_div_iff₀ hv).mpr (by
    have HL : v ≤ v^11 := by simpa using pow_le_pow_right₀ hV (by omega : 1 ≤ 11)
    nlinarith)
  have HU (i : ℕ) (hi : i<k) :
      stats t (timex (tagM i) j) ≤ 10^35*(d/v)*(1+(i:ℝ)) := by
    apply (hP i hi).1.trans
    let y := (i:ℝ); let W := codeWeight capA
    have HH : 1 ≤ W ∧ W ≤ 10^25 := by unfold W codeWeight capA reserve; norm_num
    have HE : cutBook (tagM i) s j = W*(d/v)*(2+y) := by
      unfold cutBook kappa
      simp only [tagM,↓reduceIte]
      push_cast; unfold W d v y; ring
    rw [HE]
    change _ *(1+log A+y+W*(d/v)*(2+y)) ≤ _*(d/v)*(1+y)
    have hY : 0 ≤ y := by unfold y; positivity
    nlinarith [show W*(d/v)*(2+y) ≤ 10^25*((d/v)*(2+y)) by
      rw [mul_assoc]; gcongr; linarith, mul_le_mul_of_nonneg_right HX hY]
  have hcost (i : ℕ) (hi : i < k) :
      stats t (nakedStage i j) ≤
        2*v^8 + 10^12*(v+m) + 10^35*(d/v)*(depthRate i * (1+(i:ℝ))) := by
    let a := depthRate i
    have ha := (rate_easy i).1
    have HE : stats t (nakedStage i j) =
        (1+stats t fullKills)/a+a*stats t (timex (tagM i) j)+
          stats t (fun L => (↑(billWait (tagM (i-1)) j L):ℝ)) := by
      unfold stats nakedStage
      simp_rw [Ex_add,Ex_lmul,div_eq_mul_inv,Ex_mul,
        Ex_add (f:=fun _ => 1),Ex_const]
      rfl
    have hb : 1/a ≤ v^8 := by
      have hn : i ≤ mainIx j := by unfold k at hi; omega
      have HH : depthRate (mainIx j) ≤ a := sqrt_le_sqrt (side_ant _ _ hn)
      rw [depth_at_main] at HH
      apply (div_le_iff₀ ha).mpr
      have H' := (div_le_iff₀ (show 0 < v^8 by positivity)).mp HH
      linarith
    rw [HE]
    have HH : (1+stats t fullKills)/a ≤ 2/a := div_le_div_of_nonneg_right (by linarith [size_stat h hh hx]) ha.le
    have ht := HR (i-1) (by omega)
    unfold a at *; linarith [mul_le_mul_of_nonneg_left (HU i hi) ha.le,show
      (2:ℝ)/depthRate i=2*(1/depthRate i) by ring]
  let F (i) := depthRate i*(1+(i:ℝ))
  let V := 2*v^8+10^12*(v+m); let S := 10^35*(d/v)
  have HS : 0 ≤ S := by unfold S; positivity
  let R := Finset.Ico 0 k
  have HI : ∑ i∈R,stats t (nakedStage i j) ≤ k*V+100*S := by
    have H : ∑ i∈R,F i ≤ 100 := by
      have HI := weight_decay 0 le_rfl 0 k (by omega)
      unfold F R
      norm_num [depthRate,side] at HI ⊢; exact HI
    calc
      _ ≤ ∑ i∈R,(V+S*F i) := Finset.sum_le_sum fun i hi => hcost i (Finset.mem_Ico.mp hi).2
      _ ≤ _ := by
        unfold R; rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Nat.card_Ico,nsmul_eq_mul,Nat.sub_zero]
        unfold R at H; nlinarith
  have hΦ : (v:ℝ)^10 *m ≤ d/v := (le_div_iff₀ hv).mpr (by apply le_trans _ HP; exact le_of_eq (by ring))
  have HQ : k*V ≤ 10^16*(d/v) := by
    have he' : v^9 ≤ v^10*m := le_trans (pow_le_pow_right₀ hV (by omega))
      (le_mul_of_one_le_right (by positivity) hm)
    have ht' : v^2 ≤ v^9 := pow_le_pow_right₀ hV (by omega)
    have hh' : v*m ≤ v^10*m := mul_le_mul_of_nonneg_right
      (by simpa using pow_le_pow_right₀ hV (by omega : 1 ≤ 10)) (by linarith)
    have hv' : 0 ≤ V := by unfold V; positivity
    apply (mul_le_mul_of_nonneg_right hk hv').trans
    unfold V; nlinarith
  have H₁ : stats t (fun l => (billWait (tagM (mainIx j)) j l:ℝ)) ≤ 10^14*(d/v) := by
    apply (HR (mainIx j) (by unfold k; omega)).trans
    have HH : v ≤ d/v := le_trans (by
      have HE : v ≤ v^10 := by simpa using pow_le_pow_right₀ hV (by omega : 1 ≤ 10)
      exact le_trans HE (le_mul_of_one_le_right (by positivity) hm)) hΦ
    linarith
  have HHH : stats t (palaces j) =
      4*stats t (fun l => (billWait (tagM (mainIx j)) j l:ℝ))+
      10^20*∑ i∈R,stats t (nakedStage i j) := by
    unfold stats palaces; rw [Ex_add _ (f:=fun _ => _),Ex_lmul,Ex_lmul,Ex_finset_sum]
  rw [HHH]
  apply le_trans (add_le_add (mul_le_mul_of_nonneg_left H₁ (by norm_num)) (mul_le_mul_of_nonneg_left HI (by norm_num)))
  change _ ≤10^120*d/v
  unfold S at *; nlinarith [show 10^120*d/v=10^120*(d/v) by ring]

end Troupe


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
