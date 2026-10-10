import Mathlib
import OAI.Combinatorics.KServer.AllocationMovement
import OAI.Combinatorics.KServer.Hierarchy

namespace OAI

/-! Hysteresis switch budget with signed filtering before every reset test.
The only costs are actual rank drifts, actual flag changes, held-scale
variation, and the new potential at literal wholesale resets. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.RuleSchedule
attribute [local instance] Classical.propDecidable
open RankTracking
variable {Ω R : Type} [Fintype Ω] [Fintype R] {w : Ω→ℝ}

def S (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool) (t : ℕ) (ω : Ω) : ℝ :=
  core (flags t ω) (fun r=>(P r).p t ω)

def potential (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool)
    (marked reset : ℕ→Ω→Bool) (D : ℕ→Ω→ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  value (marked t ω) (run marked reset (S P flags) D t ω) (S P flags t ω) (D t ω)

def J (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool)
    (marked reset : ℕ→Ω→Bool) (D : ℕ→Ω→ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  charge (marked (t+1) ω) (reset (t+1) ω) (run marked reset (S P flags) D t ω)
    (S P flags (t+1) ω) (D (t+1) ω)

def expense (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool)
    (reset : ℕ→Ω→Bool) (D : ℕ→Ω→ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (∑ r,if flags t ω r=flags (t+1) ω r then (0:ℝ) else 1)+|D (t+1) ω-D t ω|+
    if reset (t+1) ω then S P flags (t+1) ω+D (t+1) ω else 0

lemma S_nonneg (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool) (t : ℕ) (ω : Ω) :
    0≤S P flags t ω :=core_nonneg _ (fun r=>((P r).range t ω).1)

lemma editing (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool)
    (marked reset : ℕ→Ω→Bool) (D : ℕ→Ω→ℝ) (hD : ∀ t ω,0≤D t ω)
    (hm : ∀ t ω,reset (t+1) ω=false→marked (t+1) ω=marked t ω) (t : ℕ) (ω : Ω) :
    J P flags marked reset D t ω/2+potential P flags marked reset D (t+1) ω≤
      value (marked t ω) (run marked reset (S P flags) D t ω)
        (core (flags t ω) (fun r=>(P r).p (t+1) ω)) (D t ω)+expense P flags reset D t ω := by
  let old:=run marked reset (S P flags) D t ω
  have hmid:=value_nonneg (core_nonneg (flags t ω) (fun r=>((P r).range (t+1) ω).1))
    (hD t ω) (marked t ω) old
  cases he:reset (t+1) ω with
  | true=>
    have hv:=value_upper (S_nonneg P flags (t+1) ω) (hD (t+1) ω) (marked (t+1) ω)
      (run marked reset (S P flags) D (t+1) ω)
    have hf:0≤∑ r,if flags t ω r=flags (t+1) ω r then (0:ℝ) else 1:=
      sum_nonneg fun _ _=>by positivity
    simp only [J,charge,he,ite_true,zero_div,zero_add,potential,expense] at ⊢
    dsimp only [old] at hmid
    linarith [abs_nonneg (D (t+1) ω-D t ω)]
  | false=>
    have hc:=ordinary_credit (S P flags (t+1) ω) (D (t+1) ω) (marked (t+1) ω) old
    have hd:=data_change (marked t ω) old (flags t ω) (flags (t+1) ω)
      (fun r=>(P r).p (t+1) ω) (D:=D t ω) (E:=D (t+1) ω) (fun r=>(P r).range (t+1) ω)
    rw [hm t ω he] at hc
    change value (marked t ω) old (S P flags (t+1) ω) (D (t+1) ω) -
      value (marked t ω) old (core (flags t ω) (fun r=>(P r).p (t+1) ω)) (D t ω)≤_ at hd
    simp only [J,potential,run,he,expense,Bool.false_eq_true,ite_false,add_zero,hm t ω he]
    change charge (marked t ω) false old _ _/2+value (marked t ω)
      (step (marked t ω) false _ _ old) _ _≤_
    linarith

lemma run_adapted (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool)
    (marked reset : ℕ→Ω→Bool) (D : ℕ→Ω→ℝ) (H : ℕ→Ω→ℕ)
    (hH : ∀ r t ω,(P r).history t ω=H t ω)
    (href : ∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hf : ∀ t ω z,H t ω=H t z→flags t ω=flags t z)
    (hm : ∀ t ω z,H t ω=H t z→marked t ω=marked t z)
    (hr : ∀ t ω z,H t ω=H t z→ reset t ω=reset t z)
    (hD : ∀ t ω z,H t ω=H t z→D t ω=D t z) (t : ℕ) (ω z : Ω) (he:H t ω=H t z) :
    run marked reset (S P flags) D t ω=run marked reset (S P flags) D t z := by
  have hh s (hs:s≤t):H s ω=H s z:=StarSimplex.history_prefix H href hs he
  apply run_congr marked reset (S P flags) D t ω z
  · exact fun s hs=>hm s ω z (hh s hs)
  · exact fun s hs=>hr s ω z (hh s hs)
  · intro s hs
    unfold S
    rw [hf s ω z (hh s hs)]
    congr 1
    funext r
    exact (P r).adapted s ω z (by simpa only [hH] using hh s hs)
  · exact fun s hs=>hD s ω z (hh s hs)

lemma filtering_zero (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool)
    (marked reset : ℕ→Ω→Bool) (D : ℕ→Ω→ℝ) (H : ℕ→Ω→ℕ)
    (hH : ∀ r t ω,(P r).history t ω=H t ω)
    (href : ∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hf : ∀ t ω z,H t ω=H t z→flags t ω=flags t z)
    (hm : ∀ t ω z,H t ω=H t z→marked t ω=marked t z)
    (hr : ∀ t ω z,H t ω=H t z→ reset t ω=reset t z)
    (hD : ∀ t ω z,H t ω=H t z→D t ω=D t z) (t : ℕ) :
    avg w (fun ω=>value (marked t ω) (run marked reset (S P flags) D t ω)
      (core (flags t ω) (fun r=>(P r).before (t+1) ω)) (D t ω)-
      potential P flags marked reset D t ω)=0 := by
  simp_rw [potential,S,input_difference,avg_sum]
  apply sum_eq_zero
  intro r _
  apply filtering_affine (P r) t
  intro ω z he
  have hh:H t ω=H t z:=by simpa only [hH] using he
  dsimp only
  rw [hm t ω z hh,run_adapted P flags marked reset D H hH href hf hm hr hD t ω z hh,hf t ω z hh]

lemma payment_step (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool)
    (marked reset : ℕ→Ω→Bool) (D : ℕ→Ω→ℝ) (H : ℕ→Ω→ℕ)
    (hw : ∀ ω,0≤w ω) (hDn : ∀ t ω,0≤D t ω)
    (hreset : ∀ t ω,reset (t+1) ω=false→marked (t+1) ω=marked t ω)
    (hH : ∀ r t ω,(P r).history t ω=H t ω)
    (href : ∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hf : ∀ t ω z,H t ω=H t z→flags t ω=flags t z)
    (hm : ∀ t ω z,H t ω=H t z→marked t ω=marked t z)
    (hr : ∀ t ω z,H t ω=H t z→ reset t ω=reset t z)
    (hD : ∀ t ω z,H t ω=H t z→D t ω=D t z) (t : ℕ) :
    avg w (J P flags marked reset D t)/2+avg w (potential P flags marked reset D (t+1))≤
      avg w (potential P flags marked reset D t)+
      (∑ r,avg w (fun ω=>|(P r).p (t+1) ω-(P r).before (t+1) ω|))+
      avg w (expense P flags reset D t) := by
  have hp (ω:Ω):J P flags marked reset D t ω/2+potential P flags marked reset D (t+1) ω≤
      value (marked t ω) (run marked reset (S P flags) D t ω)
        (core (flags t ω) (fun r=>(P r).before (t+1) ω)) (D t ω)+
      (∑ r,|(P r).p (t+1) ω-(P r).before (t+1) ω|)+expense P flags reset D t ω := by
    have he:=editing P flags marked reset D hDn hreset t ω
    have hd:=(le_abs_self _).trans (input_lipschitz (marked t ω)
      (run marked reset (S P flags) D t ω) (flags t ω)
      (fun r=>(P r).p (t+1) ω) (fun r=>(P r).before (t+1) ω) (D t ω))
    linarith
  have ha:=avg_mono hw hp
  simp only [avg_add,avg_sum] at ha
  have hdiv:avg w (fun ω=>J P flags marked reset D t ω/2)=avg w (J P flags marked reset D t)/2:=by
    simp only [avg,←mul_div_assoc,sum_div]
  rw [hdiv] at ha
  have hzero:=filtering_zero P flags marked reset D H hH href hf hm hr hD t
  rw [avg_sub] at hzero
  linarith

lemma payment (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool)
    (marked reset : ℕ→Ω→Bool) (D : ℕ→Ω→ℝ) (H : ℕ→Ω→ℕ)
    (hw : ∀ ω,0≤w ω) (hDn : ∀ t ω,0≤D t ω)
    (hreset : ∀ t ω,reset (t+1) ω=false→ marked (t+1) ω=marked t ω)
    (hH : ∀ r t ω,(P r).history t ω=H t ω)
    (href : ∀ t ω z,H (t+1) ω=H (t+1) z→ H t ω=H t z)
    (hf : ∀ t ω z,H t ω=H t z→ flags t ω=flags t z)
    (hm : ∀ t ω z,H t ω=H t z→ marked t ω=marked t z)
    (hr : ∀ t ω z,H t ω=H t z→ reset t ω=reset t z)
    (hD : ∀ t ω z,H t ω=H t z→ D t ω=D t z) (n : ℕ) :
    (∑ t∈range n,avg w (J P flags marked reset D t))≤
      2*(avg w (potential P flags marked reset D 0)+
        (∑ t∈range n,∑ r,avg w (fun ω=>|(P r).p (t+1) ω-(P r).before (t+1) ω|))+
        ∑ t∈range n,avg w (expense P flags reset D t)) := by
  have hh:(∑ t∈range n,avg w (J P flags marked reset D t))/2+
      avg w (potential P flags marked reset D n)≤
      avg w (potential P flags marked reset D 0)+
        (∑ t∈range n,∑ r,avg w (fun ω=>|(P r).p (t+1) ω-(P r).before (t+1) ω|))+
        ∑ t∈range n,avg w (expense P flags reset D t) := by
    induction n with
    | zero=>simp
    | succ n ih=>
      simp only [sum_range_succ]
      have hp:=payment_step P flags marked reset D H hw hDn hreset hH href hf hm hr hD n
      linarith
  have hn:0≤avg w (potential P flags marked reset D n):=
    sum_nonneg fun ω _=>mul_nonneg (hw ω)
      (value_nonneg (S_nonneg P flags n ω) (hDn n ω) _ _)
  linarith

end KServer.RuleSchedule

end


/-! Predictability of the *actual* star schedule and regime, for the common
observation history. In particular none of the filtering coefficients uses
the new reset event. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma key_adapted (Q:R→ FilteredRanks w) (H:ℕ→Ω→ℕ)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→ H t ω=H t z)
    (t:ℕ) (ω z:Ω) (he:H t ω=H t z):key Q t ω=key Q t z:=
  parent_adapted cutoff dp Q H hQ hr t ω z he
lemma b_adapted (k:ℝ) (Q:R→ FilteredRanks w) (H:ℕ→Ω→ℕ)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→ H t ω=H t z)
    (t:ℕ) (ω z:Ω) (he:H t ω=H t z):b k Q t ω=b k Q t z:=by
  unfold b
  rw [key_adapted Q H hQ hr t ω z he]

section
variable (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (H:ℕ→Ω→ℕ)
    (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→ H t ω=H t z)
include hP hQ hr
omit [Fintype J] in
lemma schedule_prefix (t:ℕ) (ω z:Ω) (he:H t ω=H t z):
    ScheduleCausality.PrefixEq t (vector cutoff ds P ω) (vector cutoff ds P z) ∧
    ScheduleCausality.PrefixEq t (fun s=> key Q s ω) (fun s=> key Q s z):=by
  constructor
  · exact fun s hs=> vector_adapted ds P H hP hr s ω z (StarSimplex.history_prefix H hr hs he)
  · exact fun s hs=> key_adapted Q H hQ hr s ω z (StarSimplex.history_prefix H hr hs he)
lemma mark_adapted (t:ℕ) (ω z:Ω) (he:H t ω=H t z):mark P Q t ω=mark P Q t z:=by
  have hd:=schedule_prefix P Q H hP hQ hr t ω z he
  exact congrArg EpochSchedule.dominant (ScheduleCausality.run_prefix _ _ _ _ t hd.1 hd.2)
lemma marked_adapted (t:ℕ) (ω z:Ω) (he:H t ω=H t z):marked P Q t ω=marked P Q t z:=
  congrArg Option.isSome (mark_adapted P Q H hP hQ hr t ω z he)
lemma reset_adapted (t:ℕ) (ω z:Ω) (he:H t ω=H t z):reset P Q t ω=reset P Q t z:=by
  have hd:=schedule_prefix P Q H hP hQ hr t ω z he
  have ht:t-1≤ t:=Nat.sub_le _ _
  simp only [reset,hd.1 t le_rfl,hd.1 (t-1) ht,hd.2 t le_rfl,hd.2 (t-1) ht,
    ScheduleCausality.run_prefix _ _ _ _ (t-1) (hd.1.mono ht) (hd.2.mono ht)]
lemma D_adapted (t:ℕ) (ω z:Ω) (he:H t ω=H t z):D P Q t ω=D P Q t z:=by
  have hm:=mark_adapted P Q H hP hQ hr t ω z he
  change (match mark P Q t ω with | none=>0 | some o=> StarSide.coarseFlex ds (P o) t ω)=
    (match mark P Q t z with | none=>0 | some o=> StarSide.coarseFlex ds (P o) t z)
  rw [hm]
  cases mark P Q t z with
  | none=> rfl
  | some o=> exact StarSide.coarseFlex_adapted ds (P o) H (hP o) t ω z he
end

def ruleFlags (P:J→ R→ FilteredRanks w) (t:ℕ) (ω:Ω) (ir:J×R):Bool:=CoreFlags.flag (P ir.1 ir.2) t ω
lemma rule_S (P:J→ R→ FilteredRanks w) (t:ℕ) (ω:Ω):
    RuleSchedule.S (fun ir:J×R=> P ir.1 ir.2) (ruleFlags P) t ω=S P t ω:=by
  simp only [RuleSchedule.S,RuleSchedule.core,ruleFlags,S,B,TrackedCaps.core,Fintype.sum_prod_type]
  rfl
omit [Fintype J] [Fintype R] in
lemma flags_adapted (P:J→ R→ FilteredRanks w) (H:ℕ→Ω→ℕ)
    (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (t:ℕ) (ω z:Ω) (he:H t ω=H t z):ruleFlags P t ω=ruleFlags P t z:=by
  funext ir
  exact CoreFlags.flag_adapted (P ir.1 ir.2) t (by rw [hP,hP,he])
lemma rule_adapted (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (H:ℕ→Ω→ℕ)
    (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→ H t ω=H t z)
    (t:ℕ) (ω z:Ω) (he:H t ω=H t z):rule P Q t ω=rule P Q t z:=by
  have hh:=RuleSchedule.run_adapted (fun ir:J×R=> P ir.1 ir.2) (ruleFlags P)
    (marked P Q) (reset P Q) (D P Q) H (fun ir=> hP ir.1 ir.2) hr
    (flags_adapted P H hP) (marked_adapted P Q H hP hQ hr)
    (reset_adapted P Q H hP hQ hr) (D_adapted P Q H hP hQ hr) t ω z he
  have hs : RuleSchedule.S (fun ir:J×R=> P ir.1 ir.2) (ruleFlags P)=S P:=by
    funext s u
    exact rule_S P s u
  simpa only [hs,rule] using hh
end KServer.ActualOutput

end


/-! Uniform affine slope and endpoint bounds for the literal marked-side
family; logarithmic cancellation removes dependence on the number of children. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SideProfile
attribute [local instance] Classical.propDecidable
open SideTracker SideFamilies
variable {J R : Type} [Fintype J] [DecidableEq J] [Fintype R]

lemma B_bound {cw ell b h a:ℝ} (hcw:0<cw) (hel:1≤ell) (hh:1≤h)
    (hb:0≤b) (hM:b+cw*h/ell≤5) (ha:a∈Set.Icc 0 16) :
    Bcoef 40 b (cw*h/ell) (Real.exp (1-h)/h) a≤3600/cw*ell := by
  have hp:0<ell:=lt_of_lt_of_le zero_lt_one hel
  have hz:0<Real.exp (1-h)/h:=div_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one hh)
  have ht:0≤cw*h/ell:=by positivity
  have hl:=side_log_bound hh (by norm_num : (0:ℝ)≤16) ha
  have hlog:Real.log (1+(16:ℝ))+2≤18 := by
    have h:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1+16)
    linarith
  have hm:=mul_le_mul_of_nonneg_right hlog (le_trans zero_le_one hh)
  have h:=Bcoef_bound (by norm_num : (0:ℝ)≤40) hb hz ha.1 hcw hp
    (lt_of_lt_of_le zero_lt_one hh) rfl (show b+(cw*h/ell)/2≤5 by linarith)
    (show Real.log (1+a/(Real.exp (1-h)/h))≤18*h from hl.trans hm)
  norm_num at h
  exact h

omit [DecidableEq J] in
lemma coefficient_bound {cw ell b D:ℝ} (hcw:0<cw) (hel:1≤ell)
    (A:Finset J) (f:J→R→Bool) (h:J→ℝ) (hh:∀ i,1≤h i)
    (hb:0≤b) (hM:∀ i,b+cw*h i/ell≤5) (a:J→ℝ)
    (ha:a∈ChangingDomains.sideDomain A 16) (ir:J×R) :
    let d:=fromLog A f 16 b D cw ell h (by norm_num) hcw
      (lt_of_lt_of_le zero_lt_one hel) hh
    |(family 40).coefficient d a ir|≤3600/cw*ell := by
  intro d
  have hw:a ir.1∈Set.Icc 0 16:=⟨ha.1 _,(single_le_sum (fun i _=>ha.1 i) (mem_univ _)).trans ha.2.1⟩
  have hbnd:=B_bound hcw hel (hh ir.1) hb (hM ir.1) hw
  have hn:0≤Bcoef 40 b (cw*h ir.1/ell) (Real.exp (1-h ir.1)/h ir.1) (a ir.1):=
    (coefficients_nonneg (by norm_num) hb
      (by have he:=lt_of_lt_of_le zero_lt_one hel; have hi:=lt_of_lt_of_le zero_lt_one (hh ir.1); positivity)
      (div_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (hh ir.1))) hw.1).2
  change |if f ir.1 ir.2 then -Bcoef 40 b (cw*h ir.1/ell) (Real.exp (1-h ir.1)/h ir.1) (a ir.1) else 0|≤_
  split_ifs
  · simpa only [abs_neg,abs_of_nonneg hn] using hbnd
  · simp only [abs_zero]
    positivity

omit [DecidableEq J] in
lemma endpoint {cw ell b D:ℝ} (hcw:0<cw) (hel:1≤ell)
    (A:Finset J) (f:J→R→Bool) (h:J→ℝ) (hh:∀ i,1≤h i)
    (hb:0≤b) (hM:∀ i,b+cw*h i/ell≤5) (hD:0≤D)
    (p:J×R→ℝ) (hp:∀ ir,0≤p ir) (a:J→ℝ)
    (ha:a∈ChangingDomains.sideDomain A 16) :
    let d:=fromLog A f 16 b D cw ell h (by norm_num) hcw
      (lt_of_lt_of_le zero_lt_one hel) hh
    |(family 40).value d p a|≤640*(1/cw+1)*ell*D+
      (3600/cw*ell)*(∑ i,core d p i) := by
  intro d
  have hB (i:J):0≤core d p i:=sum_nonneg fun r _=>by split_ifs; exact hp _; rfl
  have he (i:J):|primitive 40 b (cw*h i/ell) (Real.exp (1-h i)/h i) (core d p i) D (a i)|≤
      40*(1/cw+1)*ell*(D*a i)+(3600/cw*ell)*core d p i := by
    have hw:a i∈Set.Icc 0 16:=⟨ha.1 _,(single_le_sum (fun i _=>ha.1 i) (mem_univ _)).trans ha.2.1⟩
    have hz:0<Real.exp (1-h i)/h i:=div_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (hh i))
    have hn:=coefficients_nonneg (by norm_num : (0:ℝ)≤40) hb
      (show 0<cw*h i/ell by have he:=lt_of_lt_of_le zero_lt_one hel; have hi:=lt_of_lt_of_le zero_lt_one (hh i); positivity) hz hw.1
    rw [primitive_coefficients]
    calc _≤|Dcoef 40 (cw*h i/ell) (Real.exp (1-h i)/h i) (a i)*D|+
        |Bcoef 40 b (cw*h i/ell) (Real.exp (1-h i)/h i) (a i)*core d p i|:=abs_sub _ _
         _=Dcoef 40 (cw*h i/ell) (Real.exp (1-h i)/h i) (a i)*D+
          Bcoef 40 b (cw*h i/ell) (Real.exp (1-h i)/h i) (a i)*core d p i := by
            rw [abs_of_nonneg (mul_nonneg hn.1 hD),abs_of_nonneg (mul_nonneg hn.2 (hB i))]
         _≤(40*(1/cw+1)*ell*a i)*D+(3600/cw*ell)*core d p i:=
          add_le_add (mul_le_mul_of_nonneg_right (Dcoef_bound (by norm_num) hz hw.1 hcw hel (hh i) rfl) hD)
            (mul_le_mul_of_nonneg_right (B_bound hcw hel (hh i) hb (hM i) hw) (hB i))
         _= _:=by ring
  rw [value_eq]
  change |∑ i,primitive 40 b (cw*h i/ell) (Real.exp (1-h i)/h i) (core d p i) D (a i)|≤_
  calc _≤∑ i,|primitive 40 b (cw*h i/ell) (Real.exp (1-h i)/h i) (core d p i) D (a i)|:=abs_sum_le_sum_abs _ _
       _≤∑ i,(40*(1/cw+1)*ell*(D*a i)+(3600/cw*ell)*core d p i):=sum_le_sum fun i _=>he i
       _=40*(1/cw+1)*ell*D*(∑ i,a i)+(3600/cw*ell)*(∑ i,core d p i):=by
          simp only [sum_add_distrib,←mul_sum]; ring
       _≤640*(1/cw+1)*ell*D+(3600/cw*ell)*(∑ i,core d p i):=by
          have hc:0≤40*(1/cw+1)*ell*D:=by positivity
          have hm:=mul_le_mul_of_nonneg_left ha.2.1 hc
          nlinarith

end KServer.SideProfile

end


/-! Literal synthetic-flag preparation and selective held-log parameter edits
for the marked-side minimizers of the constructed star. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SideEdits
attribute [local instance] Classical.propDecidable
open SideTracker SideFamilies
variable {J R : Type} [Fintype J] [DecidableEq J] [Fintype R]

def L (cw ell:ℝ):ℝ:=640*(1/cw+1)*ell
def Q (cw ell:ℝ):ℝ:=200*(Real.log 17+2)/cw*ell
def K (cw ell:ℝ):ℝ:=2*(200*(1/cw+1)+200*(Real.log 17+2)/cw)*ell

lemma Q_nonneg {cw ell:ℝ} (hcw:0<cw) (hel:0≤ell):0≤Q cw ell:=by
  have hl:=Real.log_nonneg (by norm_num : (1:ℝ)≤17)
  unfold Q; positivity

lemma pre_edit {cw ell b D E:ℝ} (hcw:0<cw) (hel:1≤ell)
    (A B:Finset J) (f g:J→R→Bool) (h h':J→ℝ) (hh:∀ i,1≤h i) (hh':∀ i,1≤h' i)
    (hb:0≤b) (hM:∀ i,b+cw*h i/ell≤5)
    (p:J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1)
    (hf:∀ i∉A,∀ r,f i r=false) (hg:∀ i∉B,∀ r,g i r=false)
    (a:J→ℝ) (ha:a∈ChangingDomains.sideDomain A 16) :
    let old:=fromLog A f 16 b D cw ell h (by norm_num) hcw (lt_of_lt_of_le zero_lt_one hel) hh
    let new:=fromLog B g 16 b E cw ell h' (by norm_num) hcw (lt_of_lt_of_le zero_lt_one hel) hh'
    |(family 40).value (prepareData old new) p a-(family 40).value old p a|≤
      L cw ell*|E-D|+Q cw ell*ChangingDomains.changedFlags f g := by
  intro old new
  have hi:=fromLog_input_bound (R:=R) f h (by norm_num : (0:ℝ)≤16) hcw hel hh
    (by norm_num : (0:ℝ)≤40) hb hM (D:=E) (D':=D)
    (B:=core (prepareData old new) p) (B':=core old p) ha
  have hs:ChangingDomains.variation (core (prepareData old new) p) (core old p)≤
      ChangingDomains.changedFlags f g:=by
    have he:=(ChangingDomains.synthetic_errors (fun i r=>hp (i,r)) hf hg).1
    change ChangingDomains.variation (ChangingDomains.core (ChangingDomains.syntheticFlags A B g) (fun i r=>p (i,r)))
      (ChangingDomains.core f (fun i r=>p (i,r)))≤_
    simpa only [ChangingDomains.variation,abs_sub_comm] using he
  have hm:=mul_le_mul_of_nonneg_left hs (Q_nonneg hcw (le_trans zero_le_one hel))
  rw [value_eq,value_eq]
  change |potential 40 b (fun i=>cw*h i/ell) (fun i=>Real.exp (1-h i)/h i)
    (core (prepareData old new) p) E a-potential 40 b (fun i=>cw*h i/ell) (fun i=>Real.exp (1-h i)/h i)
    (core old p) D a|≤_
  calc _≤40*(1/cw+1)*ell*16*|E-D|+
      40*5*(Real.log (1+16)+2)/cw*ell*ChangingDomains.variation (core (prepareData old new) p) (core old p):=hi
       _≤L cw ell*|E-D|+Q cw ell*ChangingDomains.changedFlags f g:=by
        norm_num only at *
        unfold L Q at *
        linarith

lemma post_edit {cw ell b D E:ℝ} (hcw:0<cw) (hel:1≤ell)
    (A B:Finset J) (f g:J→R→Bool) (h h':J→ℝ) (hh:∀ i,1≤h i) (hh':∀ i,1≤h' i)
    (hb:1≤b) (hM:∀ i,b+cw*h i/ell≤5) (hM':∀ i,b+cw*h' i/ell≤5) (hE:0≤E)
    (p:J×R→ℝ) (hp:∀ ir,0≤p ir)
    (a:J→ℝ) (ha:a∈ChangingDomains.sideDomain A 16) :
    let old:=fromLog A f 16 b D cw ell h (by norm_num) hcw (lt_of_lt_of_le zero_lt_one hel) hh
    let new:=fromLog B g 16 b E cw ell h' (by norm_num) hcw (lt_of_lt_of_le zero_lt_one hel) hh'
    let z:=SideFamilies.transport 40 old new p a
    |(family 40).value new p z-(family 40).value (prepareData old new) p z|≤
      K cw ell*(∑ i,if h i=h' i then 0 else core (prepareData old new) p i) := by
  intro old new z
  have hz:z∈ChangingDomains.sideDomain B 16:=SideFamilies.transport_mem 40 old new p a rfl
  have hprep:=SideFamilies.update_feasible (prepareData old new) (M:=5) hb hE
    (fun i _=>hM i) (by norm_num : 2*(5:ℝ)<16) p hp
    (fun i hi r=>by
      change i∉A at hi
      change (if i∈A∩B then g i r else false)=false
      simp only [mem_inter,hi,false_and,ite_false]) a ha
  norm_num only at hprep
  have hcap:∀ i,E*z i≤5*core (prepareData old new) p i:=by
    intro i
    by_cases hi:i∈B
    · have hm:=mul_le_mul_of_nonneg_right (hM i)
        (show 0≤core (prepareData old new) p i from sum_nonneg fun r _=>by split_ifs; exact hp _; rfl)
      have ht:=hprep.1 i
      change E*SideFamilies.prepare 40 old new p a i≤(b+cw*h i/ell)*core (prepareData old new) p i at ht
      change E*ChangingDomains.transposeSide B (SideFamilies.prepare 40 old new p a) i≤_
      simp only [ChangingDomains.transposeSide,ite_eq_left hi]
      exact ht.trans hm
    · have he:z i=0:=hz.2.2 i hi
      rw [he,mul_zero]
      exact mul_nonneg (by norm_num) (sum_nonneg fun r _=>by split_ifs; exact hp _; rfl)
  have hew:potential 40 b (fun i=>cw*h' i/ell) (fun i=>Real.exp (1-h' i)/h' i) (core new p) E z=
      potential 40 b (fun i=>cw*h' i/ell) (fun i=>Real.exp (1-h' i)/h' i) (core (prepareData old new) p) E z:=by
    apply sum_congr rfl
    intro i _
    by_cases hi:i∈A∩B
    · have hc:core new p i=core (prepareData old new) p i:=by
        unfold core
        simp only [new,old,fromLog,prepareData,ChangingDomains.syntheticFlags,ite_eq_left hi]
      rw [hc]
    · have hz0:z i=0:=by
        by_cases hiB:i∈B
        · have hiA:i∉A:=fun h=>hi (mem_inter.mpr ⟨h,hiB⟩)
          have hp0:(SideFamilies.prepare 40 old new p a) i=0:=
            (SideFamilies.prepare_mem 40 old new p a).2.2 i hiA
          change ChangingDomains.transposeSide B (SideFamilies.prepare 40 old new p a) i=0
          simp only [ChangingDomains.transposeSide,ite_eq_left hiB,hp0]
        · exact hz.2.2 i hiB
      simp only [hz0,primitive,zero_div,add_zero,Real.log_one,mul_zero,sub_zero ]
  have he:=SideFamilies.parameter_jump (by norm_num : (0:ℝ)≤16) hcw hel hh hh'
    (by norm_num : (0:ℝ)≤40) (show 0≤b by linarith) hE
    (fun i=>show 0≤core (prepareData old new) p i from sum_nonneg fun r _=>by split_ifs; exact hp _; rfl)
    hM hM' ⟨hz.1,hz.2.1⟩ hcap
  rw [value_eq,value_eq]
  change |potential 40 b (fun i=>cw*h' i/ell) (fun i=>Real.exp (1-h' i)/h' i) (core new p) E z-
    potential 40 b (fun i=>cw*h i/ell) (fun i=>Real.exp (1-h i)/h i) (core (prepareData old new) p) E z|≤_
  rw [hew]
  norm_num only at he
  convert he using 1
  dsimp [K]
  ring

end KServer.SideEdits

end


/-! Every side edit is charged to the literal rank-flag and coarse-coordinate
schedule. No cardinality factor or charge to an unchanged dominant child. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SideActualEdits
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseProcess CoarseEpoch AllocationSchedule StarProfile StarSide
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w:Ω→ℝ}

omit [DecidableEq J] in
lemma ordinary_key (x:ℕ→J→ℝ) (key:ℕ→K) (t:ℕ)
    (he:epoch x key t=epoch x key (t+1)) : key t=key (t+1):=by
  have hn:=(epoch_same_iff x key t).mp he
  exact Classical.not_not.mp ((not_or.mp hn).1)

lemma flags_supported (δ:ℝ) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (t:ℕ) (ω:Ω) :
    ∀ i∉sides δ P key t ω,∀ r,sideFlags δ P key t ω i r=false:=by
  intro i hi r
  simp only [sideFlags,ite_eq_right hi]

lemma flags_marked {δ:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (t:ℕ) (ω:Ω) (o i:J) (r:R)
    (ho:mark δ P key t ω=some o) :
    sideFlags δ P key t ω i r=if i=o then false else CoreFlags.flag (P i r) t ω := by
  by_cases hi:i=o
  · subst i
    simp [sideFlags,sides,ho]
  · by_cases hA:i∈activeSet (vector cutoff δ P ω t)
    · simp [sideFlags,sides,ho,hi,hA]
    · have hf:=StarProfile.flags_supported hδ hδu P t ω i hA r
      change CoreFlags.flag (P i r) t ω=false at hf
      simp [sideFlags,sides,ho,hA,hi,hf]

lemma flags_change {δ:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (t:ℕ) (ω:Ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) :
    ChangingDomains.changedFlags (sideFlags δ P key t ω) (sideFlags δ P key (t+1) ω)≤
      ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1)) := by
  have hm:mark δ P key (t+1) ω=mark δ P key t ω:=ScheduleEdits.ordinary_mark _ _ _ he
  cases ho:mark δ P key t ω with
  | none=>
    have hn:sideFlags δ P key t ω=fun _ _=>false:=by funext i r; simp [sideFlags,sides,ho]
    have hn':sideFlags δ P key (t+1) ω=fun _ _=>false:=by funext i r; simp [sideFlags,sides,hm,ho]
    rw [hn,hn']
    simp only [ChangingDomains.changedFlags,ite_true,sum_const_zero]
    exact sum_nonneg fun _ _=>sum_nonneg fun _ _=>by positivity
  | some o=>
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro r _
    rw [flags_marked hδ hδu P key t ω o i r ho,
      flags_marked hδ hδu P key (t+1) ω o i r (hm.trans ho)]
    by_cases hi:i=o
    · simp only [ite_eq_left hi,ite_true]
      split_ifs <;> norm_num
    · simp only [ite_eq_right hi,StarSimplex.flags]
      exact le_rfl

lemma prepared_core_bound {δ cw ell:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hcw:0<cw) (hel:0<ell) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (t:ℕ) (ω:Ω) (p:J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1) (i:J) :
    let d:=input hcw hel δ P key b
    SideFamilies.core (SideFamilies.prepareData (d t ω).data (d (t+1) ω).data) p i≤
      40*vector cutoff δ P ω (t+1) i := by
  intro d
  apply le_trans _ (ScheduleEdits.raw_core_bound hδ hδu (P i) (t+1) ω (fun r=>p (i,r)) (fun r=>hp (i,r)))
  apply sum_le_sum
  intro r _
  change (if ChangingDomains.syntheticFlags (sides δ P key t ω) (sides δ P key (t+1) ω)
      (sideFlags δ P key (t+1) ω) i r then p (i,r) else 0)≤
      (if CoreFlags.flag (P i r) (t+1) ω then p (i,r) else 0)
  by_cases hf:CoreFlags.flag (P i r) (t+1) ω=true
  · simp only [ChangingDomains.syntheticFlags,sideFlags,hf]
    split_ifs <;> first | exact (hp (i,r)).1 | exact le_rfl
  · simp [ChangingDomains.syntheticFlags,sideFlags,hf]

lemma logs_charge {δ cw ell:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hcw:0<cw) (hel:0<ell) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (t:ℕ) (ω:Ω) (p:J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) :
    let d:=input hcw hel δ P key b
    (∑ i,if logs δ P key t ω i=logs δ P key (t+1) ω i then 0 else
      SideFamilies.core (SideFamilies.prepareData (d t ω).data (d (t+1) ω).data) p i)≤
      40*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1))) := by
  intro d
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  have hn:0≤CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)):=
    charge_nonneg (active_valid _ _ _ _ _) (active_valid _ _ _ _ _)
  split_ifs with hlog
  · linarith
  · by_cases hi:mark δ P key t ω=some i
    · have hc:SideFamilies.core (SideFamilies.prepareData (d t ω).data (d (t+1) ω).data) p i=0:=by
        apply SideFamilies.prepared_core_zero
        change i∉sides δ P key t ω∩sides δ P key (t+1) ω
        simp [sides,hi]
      rw [hc]
      linarith
    · have hx:(active cutoff δ (P i) ω t).value≠(active cutoff δ (P i) ω (t+1)).value:=by
        intro hv
        exact hlog (congrArg (max 1) (ScheduleEdits.ordinary_weight δ _ _ t he i hi hv))
      rw [CoarseSchedule.charge,ite_eq_right hx]
      have hbnd:=prepared_core_bound hδ hδu hcw hel P key b t ω p hp i
      change _≤40*(active cutoff δ (P i) ω (t+1)).value at hbnd
      linarith [(active_valid cutoff δ (P i) ω t).1]

lemma theta_bound {δ k cw:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k)
    (hcw:0<cw) (hcwu:cw*20002≤1) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω) (i:J) :
    cw*logs δ P key t ω i/(1+Real.log (k+1))≤1 := by
  have hel:0<1+Real.log (k+1):=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); linarith
  apply (div_le_iff₀ hel).mpr
  have hh:=mul_le_mul_of_nonneg_left (logs_upper hδ hδu hk P key hs t ω i) hcw.le
  have hg:=mul_le_mul_of_nonneg_right hcwu hel.le
  nlinarith

end KServer.SideActualEdits

end


/-! The non-wholesale cap variation of the literal output. All endpoint
trackers are charged over all times before selecting the ordinary steps. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar OutputDynamics
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def capScale (k:ℝ) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (t:ℕ) (ω:Ω) (i:J):ℝ:=if mark P Q t ω=some i then 1+lb/ActualCaps.ell k else 1-lb/ActualCaps.ell k

lemma capScale_range {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (t:ℕ) (ω:Ω) (i:J):capScale k P Q t ω i∈Set.Icc 0 2:=by
  have h:=(ActualCaps.scalar_errors hk).2
  dsimp only [capScale]
  split_ifs <;> constructor <;> linarith [h.1,h.2.1]

lemma cap_sum (k:ℝ) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω) (i:J):
    d k P Q t ω i=∑ r,FineCaps.capTerm (rho/ActualCaps.ell k) (ActualCaps.a k Q t ω)
      (capScale k P Q t ω i) (P i r) t ω:=by
  rw [←TrackedCaps.cap,TrackedCaps.cap_eq]
  simp only [d,n,flexcap,ActualCaps.flexCap,decide_eq_true_eq,capScale]

lemma cap_parameters_held (k:ℝ) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (t:ℕ) (ω:Ω) (he:reset P Q (t+1) ω=false) (i:J):
    ActualCaps.a k Q (t+1) ω=ActualCaps.a k Q t ω ∧
      capScale k P Q (t+1) ω i=capScale k P Q t ω i:=by
  have hm:=ordinary_mark P Q t ω he
  have hkey:=SideActualEdits.ordinary_key (vector cutoff ds P ω) (fun s=> key Q s ω) t
    ((reset_iff P Q t ω).mp he)
  constructor
  · change 100*(CoarseParameters.upperBeta k cutoff cb (ActualCaps.ell k) dp (key Q (t+1) ω)-3)=_
    rw [←hkey]
    rfl
  · simp only [capScale,hm]

lemma fine_step (k:ℝ) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):
    (if reset P Q (t+1) ω then 0 else variation (d k P Q (t+1) ω) (d k P Q t ω))≤
      ∑ ir:J×R,FineCaps.fineVariation (rho/ActualCaps.ell k) (ActualCaps.a k Q)
        (fun s z=> capScale k P Q s z ir.1) (fun s z=> reset P Q (s+1) z) (P ir.1 ir.2) t ω:=by
  cases he:reset P Q (t+1) ω with
  | true=> simp only [he,ite_true,FineCaps.fineVariation,sum_const_zero,le_refl]
  | false=>
    simp only [he,Bool.false_eq_true,ite_false,FineCaps.fineVariation,Fintype.sum_prod_type]
    apply sum_le_sum
    intro i _
    change |d k P Q (t+1) ω i-d k P Q t ω i|≤_
    rw [cap_sum,cap_sum,←sum_sub_distrib]
    exact abs_sum_le_sum_abs _ _

lemma fine_budget {k:ℝ} (hk:1≤ k) (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1)
    (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (hq:∀ t ω,size Q t ω≤ k) (N:ℕ):
    (∑ t∈range N,avg w (fun ω=> if reset P Q (t+1) ω then 0 else
      variation (d k P Q (t+1) ω) (d k P Q t ω)))≤
      2*(160/(rho/ActualCaps.ell k)+(CoreFlags.tolerance^2)⁻¹)*
        ((∑ t∈range N,avg w (fun ω=>∑ ir:J×R,|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|))+
          Fintype.card (J×R)):=by
  have hξ:0< rho/ActualCaps.ell k:=(ActualCaps.scalar_errors hk).1
  have hξh:rho/ActualCaps.ell k<1/2:=by
    have h1:=ActualCaps.ell_ge_one hk
    have hr:rho<1/2:=by norm_num [rho,lb,cb]
    apply (div_lt_iff₀ (ActualCaps.ell_pos hk)).mpr
    linarith
  have hh:=FineCaps.fine_cap_budget (J:=J×R) hw hw1 hξ hξh
    (fun _=> ActualCaps.a k Q) (fun ir s z=> capScale k P Q s z ir.1)
    (fun _ s z=> reset P Q (s+1) z)
    (fun _ s z=>(ActualCaps.ranges hk Q s z (hq s z)).2.1)
    (fun ir s z=> capScale_range hk P Q s z ir.1)
    (fun ir s z he=> cap_parameters_held k P Q s z he ir.1)
    (fun ir=> P ir.1 ir.2) N
  exact (sum_le_sum fun t _=> avg_mono hw (fine_step k P Q t)).trans hh

end KServer.ActualOutput

end


/-! Every coordinate of the actual feasible star output depends only on
observed history and on the supplied parent quota. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}
variable (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (H:ℕ→Ω→ℕ)
    (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
include hP hQ hr
lemma d_adapted (k:ℝ) (t:ℕ) (ω z:Ω) (he:H t ω=H t z):d k P Q t ω=d k P Q t z:=by
  have hk:=key_adapted Q H hQ hr t ω z he
  have ha:ActualCaps.a k Q t ω=ActualCaps.a k Q t z:=by
    change 100*(CoarseParameters.upperBeta k cutoff cb (ActualCaps.ell k) dp (key Q t ω)-3)=_
    rw [hk]; rfl
  have hm:=mark_adapted P Q H hP hQ hr t ω z he
  have hs i:capScale k P Q t ω i=capScale k P Q t z i:=by unfold capScale; rw [hm]
  funext i
  rw [cap_sum,cap_sum,ha,hs]
  exact TrackedCaps.cap_adapted (P i) _ _ _ t (fun r=>by rw [hP,hP,he])
lemma α_adapted (k:ℝ) (t:ℕ) (ω z:Ω) (he:H t ω=H t z):α k P Q t ω=α k P Q t z:=
  StarSimplex.proportion_adapted (δ:=ds) (by norm_num [ds]) (by norm_num [ds]) C (ActualCaps.ell k) ct
    P (key Q) H hP hr (key_adapted Q H hQ hr) t ω z he
lemma side_adapted {k:ℝ} (hk:1≤k) (t:ℕ) (ω z:Ω) (he:H t ω=H t z):side hk P Q t ω=side hk P Q t z:=
  StarSide.proportion_adapted positive.2.2.2.1 (ActualCaps.ell_pos hk) ds P (key Q) (b k Q)
    H hP hr (key_adapted Q H hQ hr) (b_adapted k Q H hQ hr) t ω z he
lemma out_adapted {k:ℝ} (hk:1≤k) (t:ℕ) (ω z:Ω) (he:H t ω=H t z) (q:ℝ):
    out hk P Q t ω q=out hk P Q t z q:=by
  have hd:=d_adapted P Q H hP hQ hr k t ω z he
  have ha:=α_adapted P Q H hP hQ hr k t ω z he
  have hside:=side_adapted P Q H hP hQ hr hk t ω z he
  have hD:=D_adapted P Q H hP hQ hr t ω z he
  have hm:=mark_adapted P Q H hP hQ hr t ω z he
  have hreg:=rule_adapted P Q H hP hQ hr t ω z he
  simp only [out,hm,hreg]
  cases hmz:mark P Q t z with
  | none=>simp only [outI,hd,ha]
  | some o=>
    cases hrz:rule P Q t z with
    | false=>simp only [Bool.false_eq_true,ite_false,outI,hd,ha]
    | true=>
      simp only [ite_true]
      funext i
      simp only [outII,sideOut,hd,hside,hD]
end KServer.ActualOutput

end


/-! The literal recursive allocation is adapted to the request filtration.
No adaptedness of the hidden offline configurations is asserted or required. -/
noncomputable section
namespace KServer.HierarchicalQuota
variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)
lemma quota_adapted (hk:1≤(k:ℝ)) (d:ℕ) (word:Fin d→A) (t:ℕ) (ω ρ:Ω)
    (he:H t ω=H t ρ):quota hw H hr maps q hk d word t ω=quota hw H hr maps q hk d word t ρ:=by
  induction d with
  | zero=>rfl
  | succ d ih=>
    simp only [quota,ih]
    exact congrFun (ActualOutput.out_adapted (children hw H hr maps q (Fin.init word))
      (parent hw H hr maps q (Fin.init word)) H (fun _ _ _ _=>rfl) (fun _ _ _=>rfl)
      hr hk t ω ρ he _) _
end KServer.HierarchicalQuota

end

end OAI
