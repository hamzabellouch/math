import Mathlib
import OAI.Combinatorics.KServer.ScheduleBudget

namespace OAI

/-! True-prefix filtering followed by paid literal profile edits.  In particular
no event chosen at the new history is allowed to select a filtering term. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduledFiltering
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule
open SimplexFamilies AdaptiveAllocation AdaptiveMinimization
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω→ℝ}

lemma filtering_zero {δ:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (C ell ct:ℝ)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (H:ℕ→Ω→ℕ)
    (hH:∀ i r t ω,(P i r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z) (t:ℕ) :
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    avg w (fun ω=>(family C ell).value (d t ω).data (fun ir=>(P ir.1 ir.2).before (t+1) ω) (a t ω)-
      (family C ell).value (d t ω).data (d t ω).ranks (a t ω))=0 := by
  intro d a
  simp_rw [(family C ell).input_difference]
  rw [avg_sum_any]
  apply sum_eq_zero
  intro ir _
  apply filtering_affine (P ir.1 ir.2)
  intro ω z he
  rw [hH,hH] at he
  have hd:=congrArg CausalSimplex.Input.data (StarSimplex.input_adapted hδ hδu C ell ct P key H hH hr hkey t ω z he)
  have ha:=StarSimplex.proportion_adapted hδ hδu C ell ct P key H hH hr hkey t ω z he
  change (family C ell).coefficient (d t ω).data (a t ω) ir=(family C ell).coefficient (d t z).data (a t z) ir
  change (d t ω).data=(d t z).data at hd
  change a t ω=a t z at ha
  rw [hd,ha]

lemma payment_step {δ C ct k:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hC:0<C) (hct:0<ct) (hctu:ct*20002≤1) (hgap:700<C*ct) (hk:1≤k)
    (hw:∀ ω,0≤w ω) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (H:ℕ→Ω→ℕ)
    (hH:∀ i r t ω,(P i r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z) (t:ℕ) :
    let ell:=1+Real.log (k+1)
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    avg w (fun ω=>CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω))≤
      avg w (fun ω=>(family C ell).value (d t ω).data (d t ω).ranks (a t ω))-
      avg w (fun ω=>(family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω))+
      13*C*ell*(∑ ir:J×R,avg w (fun ω=>|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|))+
      avg w (ScheduledPayment.expense C ell δ P key t) := by
  intro ell d a
  have hpoint (ω:Ω) : CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      ((family C ell).value (d t ω).data (d t ω).ranks (a t ω)-
      (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω))+
      ((family C ell).value (d t ω).data (fun ir=>(P ir.1 ir.2).before (t+1) ω) (a t ω)-
      (family C ell).value (d t ω).data (d t ω).ranks (a t ω))+
      13*C*ell*(∑ ir:J×R,|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|)+
      ScheduledPayment.expense C ell δ P key t ω := by
    have hp:=ScheduledPayment.payment hδ hδu hC hct hctu hgap hk P key hs t ω
    have ha:=StarSimplex.proportion_mem hδ hδu C ell ct P key t ω
    have hl:=ScheduledSlope.actual_bound hδ hδu hC.le hct.le hctu hk P key hs t ω _ ha
    have hd: (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
        (family C ell).value (d t ω).data (fun ir=>(P ir.1 ir.2).before (t+1) ω) (a t ω)≤
        13*C*ell*(∑ ir:J×R,|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|) :=
      (le_abs_self _).trans ((family C ell).input_lipschitz (d t ω).data _ _ (a t ω) hl)
    change _≤(family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+_ at hp
    linarith
  have he:=avg_mono hw hpoint
  simp only [avg_add,avg_sub,avg_mul,avg_sum_any] at he
  have hf:=filtering_zero hδ hδu C ell ct P key H hH hr hkey t
  dsimp only at hf
  rw [avg_sub] at hf
  change avg w (fun ω=>(family C ell).value (d t ω).data (fun ir=>(P ir.1 ir.2).before (t+1) ω) (a t ω))-
    avg w (fun ω=>(family C ell).value (d t ω).data (d t ω).ranks (a t ω))=0 at hf
  rw [hf,add_zero] at he
  exact he

lemma payment {δ C ct k:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hC:0<C) (hct:0<ct) (hctu:ct*20002≤1) (hgap:700<C*ct) (hk:1≤k)
    (hw:∀ ω,0≤w ω) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (H:ℕ→Ω→ℕ)
    (hH:∀ i r t ω,(P i r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z) (n:ℕ) :
    let ell:=1+Real.log (k+1)
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    (∑ t∈range n,avg w (fun ω=>CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)))≤
      avg w (fun ω=>(family C ell).value (d 0 ω).data (d 0 ω).ranks (a 0 ω))-
      avg w (fun ω=>(family C ell).value (d n ω).data (d n ω).ranks (a n ω))+
      13*C*ell*(∑ t∈range n,∑ ir:J×R,avg w (fun ω=>|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|))+
      ∑ t∈range n,avg w (ScheduledPayment.expense C ell δ P key t) := by
  intro ell d a
  induction n with
  | zero=>simp
  | succ n ih=>
    simp only [sum_range_succ]
    have hp:=payment_step hδ hδu hC hct hctu hgap hk hw P key hs H hH hr hkey n
    change avg w (fun ω=>CausalSimplex.mass (d (n+1) ω)*ChangingDomains.variation (a (n+1) ω) (a n ω))≤
      avg w (fun ω=>(family C ell).value (d n ω).data (d n ω).ranks (a n ω))-
      avg w (fun ω=>(family C ell).value (d (n+1) ω).data (d (n+1) ω).ranks (a (n+1) ω))+_+_ at hp
    linarith

lemma bounded_endpoint {δ C ct k:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hC:0≤C) (hct:0≤ct) (hctu:ct*20002≤1) (hk:1≤k)
    (hw:∀ ω,0≤w ω) (hw1:∑ ω,w ω=1) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) :
    let ell:=1+Real.log (k+1)
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    |avg w (fun ω=>(family C ell).value (d t ω).data (d t ω).ranks (a t ω))|≤572*C*ell*k := by
  intro ell d a
  have hel:0≤ell:=by dsimp [ell]; have h:=Real.log_nonneg (show 1≤k+1 by linarith); linarith
  calc _≤avg w (fun ω=>|(family C ell).value (d t ω).data (d t ω).ranks (a t ω)|) := by
        unfold avg
        exact (abs_sum_le_sum_abs _ _).trans_eq (by
          congr 1; funext ω; rw [abs_mul,abs_of_nonneg (hw ω)])
       _≤avg w (fun _=>572*C*ell*k) := by
        apply avg_mono hw
        intro ω
        have h:=ScheduledEndpoint.actual_bound hδ hδu hC hct hctu hk P key hs t ω
          (d t ω).ranks (fun ir=>(P ir.1 ir.2).range t ω) (a t ω)
          (StarSimplex.proportion_mem hδ hδu C ell ct P key t ω)
        have ht:=StarProfile.vector_total hδ hδu P t ω (hs t ω)
        have hm:=mul_le_mul_of_nonneg_left ht (show 0≤520*C*ell by positivity)
        change |(family C ell).value (d t ω).data (d t ω).ranks (a t ω)|≤520*C*ell*EpochSchedule.total (vector cutoff δ P ω t) at h
        change (∑ i,vector cutoff δ P ω t i)≤_ at ht
        unfold EpochSchedule.total at h hm
        nlinarith
       _= _ :=avg_const w hw1 _

end KServer.ScheduledFiltering

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SideFiltering
attribute [local instance] Classical.propDecidable Classical.decEq
open AdaptiveMinimization RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule StarSide SideFamilies
variable {Ω J R K : Type} [Fintype Ω] [Fintype J]  [Fintype R]
variable {w:Ω→ℝ}

lemma filtering_zero {cw ell:ℝ} (hcw:0<cw) (hel:0<ell) (δ:ℝ)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ) (H:ℕ→Ω→ℕ)
    (hH:∀ i r t ω,(P i r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z)
    (hb:∀ t ω z,H t ω=H t z→b t ω=b t z) (t:ℕ) :
    let d:=input hcw hel δ P key b
    let a:=proportion hcw hel δ P key b
    avg w (fun ω=>(family 40).value (d t ω).data (fun ir=>(P ir.1 ir.2).before (t+1) ω) (a t ω)-
      (family 40).value (d t ω).data (d t ω).ranks (a t ω))=0 := by
  intro d a
  simp_rw [(family 40).input_difference]
  rw [avg_sum_any]
  apply sum_eq_zero
  intro ir _
  apply filtering_affine (P ir.1 ir.2)
  intro ω z he
  rw [hH,hH] at he
  have hd:=congrArg CausalSide.Input.data (input_adapted hcw hel δ P key b H hH hr hkey hb t ω z he)
  have ha:=proportion_adapted hcw hel δ P key b H hH hr hkey hb t ω z he
  change (family 40).coefficient (d t ω).data (a t ω) ir=(family 40).coefficient (d t z).data (a t z) ir
  change (d t ω).data=(d t z).data at hd
  change a t ω=a t z at ha
  rw [hd,ha]

lemma slope {δ k cw:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k)
    (hcw:0<cw) (hcwu:cw*20002≤1) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω) (hb:0≤b t ω) (hbu:b t ω≤4) :
    let ell:=1+Real.log (k+1)
    let hel:0<ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
    let d:=input hcw hel δ P key b
    let a:=proportion hcw hel δ P key b
    ∀ ir,|(family 40).coefficient (d t ω).data (a t ω) ir|≤3600/cw*ell := by
  intro ell hel d a ir
  have hell:1≤ell:=by dsimp [ell]; linarith [Real.log_nonneg (show 1≤k+1 by linarith)]
  have hM (i:J):b t ω+cw*logs δ P key t ω i/ell≤5:=by
    have h:=SideActualEdits.theta_bound hδ hδu hk hcw hcwu P key hs t ω i
    change cw*logs δ P key t ω i/ell≤1 at h
    linarith
  exact SideProfile.coefficient_bound hcw hell (sides δ P key t ω) (sideFlags δ P key t ω)
    (logs δ P key t ω) (fun i=>le_max_left _ _) hb hM (a t ω) (proportion_mem hcw hel δ P key b t ω) ir

lemma payment_step {δ k cw:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k)
    (hcw:0<cw) (hcwu:cw*20002≤1) (hw:∀ ω,0≤w ω)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k)
    (hb:∀ t ω,1≤b t ω) (hbu:∀ t ω,b t ω≤4)
    (hbe:∀ t ω,key t ω=key (t+1) ω→b t ω=b (t+1) ω)
    (H:ℕ→Ω→ℕ) (hH:∀ i r t ω,(P i r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z)
    (hbad:∀ t ω z,H t ω=H t z→b t ω=b t z) (t:ℕ) :
    let ell:=1+Real.log (k+1)
    let hel:0<ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
    let d:=input hcw hel δ P key b
    let a:=proportion hcw hel δ P key b
    avg w (fun ω=>scale δ P key (t+1) ω*ChangingDomains.variation (a (t+1) ω) (a t ω))≤
      avg w (fun ω=>(family 40).value (d t ω).data (d t ω).ranks (a t ω))-
      avg w (fun ω=>(family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω))+
      3600/cw*ell*(∑ ir:J×R,avg w (fun ω=>|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|))+
      avg w (SidePayment.expense cw ell δ P key t) := by
  intro ell hel d a
  have hpoint (ω:Ω) : scale δ P key (t+1) ω*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      ((family 40).value (d t ω).data (d t ω).ranks (a t ω)-
      (family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω))+
      ((family 40).value (d t ω).data (fun ir=>(P ir.1 ir.2).before (t+1) ω) (a t ω)-
      (family 40).value (d t ω).data (d t ω).ranks (a t ω))+
      3600/cw*ell*(∑ ir:J×R,|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|)+
      SidePayment.expense cw ell δ P key t ω := by
    have hp:=SidePayment.payment hδ hδu hk hcw hcwu P key b hs t ω (fun s=>hb s ω) (fun s=>hbu s ω) (hbe t ω)
    have hl:=slope hδ hδu hk hcw hcwu P key b hs t ω (by linarith [hb t ω]) (hbu t ω)
    have hd: (family 40).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
        (family 40).value (d t ω).data (fun ir=>(P ir.1 ir.2).before (t+1) ω) (a t ω)≤
        3600/cw*ell*(∑ ir:J×R,|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|) :=
      (le_abs_self _).trans ((family 40).input_lipschitz (d t ω).data _ _ (a t ω) hl)
    change _≤(family 40).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+_ at hp
    linarith
  have he:=avg_mono hw hpoint
  simp only [avg_add,avg_sub,avg_mul,avg_sum_any] at he
  have hf:=filtering_zero hcw hel δ P key b H hH hr hkey hbad t
  dsimp only at hf
  rw [avg_sub] at hf
  change avg w (fun ω=>(family 40).value (d t ω).data (fun ir=>(P ir.1 ir.2).before (t+1) ω) (a t ω))-
    avg w (fun ω=>(family 40).value (d t ω).data (d t ω).ranks (a t ω))=0 at hf
  rw [hf,add_zero] at he
  exact he

lemma payment {δ k cw:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k)
    (hcw:0<cw) (hcwu:cw*20002≤1) (hw:∀ ω,0≤w ω)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k)
    (hb:∀ t ω,1≤b t ω) (hbu:∀ t ω,b t ω≤4)
    (hbe:∀ t ω,key t ω=key (t+1) ω→b t ω=b (t+1) ω)
    (H:ℕ→Ω→ℕ) (hH:∀ i r t ω,(P i r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z)
    (hbad:∀ t ω z,H t ω=H t z→b t ω=b t z) (n:ℕ) :
    let ell:=1+Real.log (k+1)
    let hel:0<ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
    let d:=input hcw hel δ P key b
    let a:=proportion hcw hel δ P key b
    (∑ t∈range n,avg w (fun ω=>scale δ P key (t+1) ω*ChangingDomains.variation (a (t+1) ω) (a t ω)))≤
      avg w (fun ω=>(family 40).value (d 0 ω).data (d 0 ω).ranks (a 0 ω))-
      avg w (fun ω=>(family 40).value (d n ω).data (d n ω).ranks (a n ω))+
      3600/cw*ell*(∑ t∈range n,∑ ir:J×R,avg w (fun ω=>|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|))+
      ∑ t∈range n,avg w (SidePayment.expense cw ell δ P key t) := by
  intro ell hel d a
  induction n with
  | zero=>simp
  | succ n ih=>
    simp only [sum_range_succ]
    have hp:=payment_step hδ hδu hk hcw hcwu hw P key b hs hb hbu hbe H hH hr hkey hbad n
    change avg w (fun ω=>scale δ P key (n+1) ω*ChangingDomains.variation (a (n+1) ω) (a n ω))≤
      avg w (fun ω=>(family 40).value (d n ω).data (d n ω).ranks (a n ω))-
      avg w (fun ω=>(family 40).value (d (n+1) ω).data (d (n+1) ω).ranks (a (n+1) ω))+_+_ at hp
    linarith

end KServer.SideFiltering

end


/-! Expected movement of the literal minimizers, with uniform endpoint bills. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar ActualOutput
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma drift_le_stock (hw:∀ ω,0≤w ω) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (N:ℕ):
    drift (flat P) N≤ stock P Q N:=
  (le_add_of_nonneg_right (Nat.cast_nonneg (Fintype.card (J×R)))).trans (inventory_child_le hw P Q N)
lemma raw_drift_eq (P:J→R→FilteredRanks w) (N:ℕ):
    (∑ t∈range N,∑ ir:J×R,avg w (fun ω=>|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|))=
      drift (flat P) N:=by simp only [drift,flat,avg_sum]

lemma simplex_mass (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):
    CausalSimplex.mass (StarSimplex.input (δ:=ds) (by norm_num [ds]) (by norm_num [ds])
      C (ActualCaps.ell k) ct P (key Q) t ω)=S P t ω:=by
  simp only [CausalSimplex.mass,StarSimplex.input_core]
  rfl

lemma simplex_movement {k:ℝ} (hk:1≤k) (hw:∀ ω,0≤w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (H:ℕ→Ω→ℕ) (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z) (N:ℕ):
    total w N (fun t ω=>S P (t+1) ω*ChangingDomains.variation (α k P Q (t+1) ω) (α k P Q t ω))≤
      1144*C*ActualCaps.ell k*k+(13*C+simplexConstant)*ActualCaps.ell k*stock P Q N:=by
  have hs' t ω: (∑ i,size (P i) t ω)≤k:=(hs t ω).trans (hq t ω)
  have hp:=ScheduledFiltering.payment (δ:=ds) (by norm_num [ds]) (by norm_num [ds])
    positive.2.2.2.2.1 positive.2.2.1 small.1 small.2.2.1 hk hw P (key Q) hs' H hP hr
    (key_adapted Q H hQ hr) N
  have he t:=ScheduledFiltering.bounded_endpoint (δ:=ds) (by norm_num [ds]) (by norm_num [ds])
    positive.2.2.2.2.1.le positive.2.2.1.le small.1 hk hw hw1 P (key Q) hs' t
  dsimp only at hp he
  have hl:(1+Real.log (k+1))=ActualCaps.ell k:=rfl
  simp only [hl,simplex_mass,raw_drift_eq] at hp he
  change total w N (fun t ω=>S P (t+1) ω*ChangingDomains.variation (α k P Q (t+1) ω) (α k P Q t ω))≤_ at hp
  have he0:=(abs_le.mp (he 0)).2
  have heN:=(abs_le.mp (he N)).1
  have hx:=simplex_expense hw hw1 (ActualCaps.ell_ge_one hk) P Q hs N
  have hd:=mul_le_mul_of_nonneg_left (drift_le_stock hw P Q N)
    (show 0≤13*C*ActualCaps.ell k by have hc:=positive.2.2.2.2.1; have he:=ActualCaps.ell_pos hk; positivity)
  dsimp only [total] at hx
  linarith only [hp,he0,heN,hx,hd]

lemma side_endpoint {k:ℝ} (hk:1≤k) (hw:∀ ω,0≤w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k) (t:ℕ):
    |avg w (fun ω=>(SideFamilies.family 40).value (sideData hk P Q t ω).data
      (sideData hk P Q t ω).ranks (side hk P Q t ω))|≤220000*(1/cw+1)*ActualCaps.ell k*k:=by
  have hc:0<cw:=positive.2.2.2.1
  have hel:0<ActualCaps.ell k:=ActualCaps.ell_pos hk
  calc _≤avg w (fun ω=>|(SideFamilies.family 40).value (sideData hk P Q t ω).data
        (sideData hk P Q t ω).ranks (side hk P Q t ω)|):=by
          unfold avg
          exact (abs_sum_le_sum_abs _ _).trans_eq (by
            congr 1; funext ω; rw [abs_mul,abs_of_nonneg (hw ω)])
       _≤avg w (fun _=>220000*(1/cw+1)*ActualCaps.ell k*k):=by
          apply avg_mono hw
          intro ω
          have hp:=SideActualBounds.endpoint (δ:=ds) (by norm_num [ds]) (by norm_num [ds]) hk hc small.2.1
            P (key Q) (b k Q) (fun s z=>(hs s z).trans (hq s z)) t ω
            (by linarith [(b_range hk Q t ω (hq t ω)).1]) (b_range hk Q t ω (hq t ω)).2
            (sideData hk P Q t ω).ranks (fun ir=>(P ir.1 ir.2).range t ω)
          change |(SideFamilies.family 40).value (sideData hk P Q t ω).data
            (sideData hk P Q t ω).ranks (side hk P Q t ω)|≤_ at hp
          have ht:=StarProfile.vector_total (δ:=ds) (by norm_num [ds]) (by norm_num [ds]) P t ω ((hs t ω).trans (hq t ω))
          have hm:=mul_le_mul_of_nonneg_left ht (show 0≤200000*(1/cw+1)*ActualCaps.ell k by positivity)
          dsimp only [EpochSchedule.total,ActualCaps.ell] at hp hm ⊢
          nlinarith only [hp,hm]
       _= _:=avg_const w hw1 _

lemma side_movement {k:ℝ} (hk:1≤k) (hw:∀ ω,0≤w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (H:ℕ→Ω→ℕ) (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z) (N:ℕ):
    total w N (fun t ω=>D P Q (t+1) ω*ChangingDomains.variation (side hk P Q (t+1) ω) (side hk P Q t ω))≤
      440000*(1/cw+1)*ActualCaps.ell k*k+(3600/cw+sideConstant)*ActualCaps.ell k*stock P Q N:=by
  have hc:0<cw:=positive.2.2.2.1
  have hel:0<ActualCaps.ell k:=ActualCaps.ell_pos hk
  have hp:=SideFiltering.payment (δ:=ds) (by norm_num [ds]) (by norm_num [ds]) hk hc small.2.1 hw
    P (key Q) (b k Q) (fun s z=>(hs s z).trans (hq s z))
    (fun t ω=>by linarith [(b_range hk Q t ω (hq t ω)).1])
    (fun t ω=>(b_range hk Q t ω (hq t ω)).2)
    (fun t ω he=>by unfold b; rw [he]) H hP hr
    (key_adapted Q H hQ hr) (b_adapted k Q H hQ hr) N
  dsimp only at hp
  have hl:(1+Real.log (k+1))=ActualCaps.ell k:=rfl
  simp only [hl,raw_drift_eq] at hp
  change total w N (fun t ω=>D P Q (t+1) ω*ChangingDomains.variation (side hk P Q (t+1) ω) (side hk P Q t ω))≤
    avg w (fun ω=>(SideFamilies.family 40).value (sideData hk P Q 0 ω).data (sideData hk P Q 0 ω).ranks (side hk P Q 0 ω))-
    avg w (fun ω=>(SideFamilies.family 40).value (sideData hk P Q N ω).data (sideData hk P Q N ω).ranks (side hk P Q N ω))+
    3600/cw*ActualCaps.ell k*drift (flat P) N+total w N (SidePayment.expense cw (ActualCaps.ell k) ds P (key Q)) at hp
  have he0:=(abs_le.mp (side_endpoint hk hw hw1 P Q hs hq 0)).2
  have heN:=(abs_le.mp (side_endpoint hk hw hw1 P Q hs hq N)).1
  have hx:=side_expense hw hw1 hel.le P Q hs N
  have hd:=mul_le_mul_of_nonneg_left (drift_le_stock hw P Q N) (show 0≤3600/cw*ActualCaps.ell k by positivity)
  linarith
end KServer.ActualCharges

end


/-! Switch charges from the actual regime recursion, including uniform
initialization and literal wholesale bills. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar ActualOutput
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def ruleConstant:ℝ:=flagConstant+scaleConstant+81*wholesaleConstant
lemma ruleConstant_nonneg:0≤ ruleConstant:=by
  have hf:=constants_nonneg.2.2
  have hh:=more_constants_nonneg.1
  have hs:=more_constants_nonneg.2.1
  dsimp [ruleConstant]; positivity

lemma core_coarse (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω):
    S P t ω≤40*EpochSchedule.total (vector cutoff ds P ω t):=by
  unfold S EpochSchedule.total
  rw [mul_sum]
  exact sum_le_sum fun i _=>ScheduleEdits.raw_core_bound (δ:=ds) (by norm_num [ds])
    (by norm_num [ds]) (P i) t ω (fun r=>(P i r).p t ω) (fun r=>(P i r).range t ω)
lemma joint_coarse (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):
    S P t ω+D P Q t ω≤81*EpochSchedule.total (vector cutoff ds P ω t):=by
  have h:=SideActualBounds.scale_bound (δ:=ds) (by norm_num [ds]) (by norm_num [ds]) P (key Q) t ω
  change D P Q t ω≤_ at h
  linarith [core_coarse P t ω]
lemma ruleS_eq (P:J→R→FilteredRanks w):RuleSchedule.S (flat P) (ruleFlags P)=S P:=by
  funext t ω; exact rule_S P t ω
lemma ruleJ_eq (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w):
    RuleSchedule.J (flat P) (ruleFlags P) (marked P Q) (reset P Q) (D P Q)=switchCharge P Q:=by
  funext t ω
  simp only [RuleSchedule.J,ruleS_eq,switchCharge,rule]
lemma rule_expense_step (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):
    RuleSchedule.expense (flat P) (ruleFlags P) (reset P Q) (D P Q) t ω≤
      flags P t ω+|D P Q (t+1) ω-D P Q t ω|+81*wholesale P Q t ω:=by
  have hf:(∑ ir:J×R,if ruleFlags P t ω ir=ruleFlags P (t+1) ω ir then (0:ℝ) else 1)=flags P t ω:=by
    rw [flags_eq]
    apply sum_congr rfl
    intro ir _
    unfold ruleFlags CoreFlags.change
    by_cases h : CoreFlags.flag (P ir.1 ir.2) t ω=CoreFlags.flag (P ir.1 ir.2) (t+1) ω
    · simp only [ite_eq_left h,ite_eq_left h.symm]
    · simp only [ite_eq_right h,ite_eq_right (Ne.symm h)]
  simp only [RuleSchedule.expense,ruleS_eq,hf]
  apply add_le_add le_rfl
  cases he:reset P Q (t+1) ω with
  | false=>simp only [Bool.false_eq_true,ite_false]; exact mul_nonneg (by norm_num) (wholesale_nonneg P Q t ω)
  | true=>
    simp only [ite_true]
    have hr:EpochSchedule.reset (vector cutoff ds P ω t) (vector cutoff ds P ω (t+1))
      (key Q t ω) (key Q (t+1) ω) (EpochSchedule.run (vector cutoff ds P ω) (fun s=>key Q s ω) t):=by
        simpa only [reset,Nat.add_sub_cancel,decide_eq_true_eq] using he
    rw [wholesale,EpochSchedule.wholesale,ite_eq_left hr]
    have h:=joint_coarse P Q (t+1) ω
    linarith [EpochSchedule.total_nonneg (vector_nonneg cutoff ds P ω t)]
lemma rule_expense (hw:∀ ω,0≤w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (N:ℕ):
    total w N (RuleSchedule.expense (flat P) (ruleFlags P) (reset P Q) (D P Q))≤ ruleConstant*stock P Q N:=by
  have h:=total_mono hw (N:=N) (rule_expense_step P Q)
  rw [total_add,total_add,total_mul] at h
  have hf:=flags_bound hw hw1 P Q N
  have hd:=scale_bound hw hw1 P Q hs N
  have hh:=wholesale_bound hw hw1 P Q hs N
  dsimp only [ruleConstant]
  linarith
lemma rule_initial {k:ℝ} (hk:1≤k) (hw:∀ ω,0≤w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k):
    avg w (RuleSchedule.potential (flat P) (ruleFlags P) (marked P Q) (reset P Q) (D P Q) 0)≤90*k:=by
  calc _≤avg w (fun _=>90*k):=by
        apply avg_mono hw
        intro ω
        have hv:=RuleSchedule.value_upper (S_nonneg P 0 ω) (D_nonneg P Q 0 ω) (marked P Q 0 ω) (rule P Q 0 ω)
        have hj:=joint_coarse P Q 0 ω
        have ht:=StarProfile.vector_total (δ:=ds) (by norm_num [ds]) (by norm_num [ds]) P 0 ω ((hs 0 ω).trans (hq 0 ω))
        simp only [RuleSchedule.potential,ruleS_eq]
        change RuleSchedule.value (marked P Q 0 ω) (rule P Q 0 ω) (S P 0 ω) (D P Q 0 ω)≤_
        unfold EpochSchedule.total at hj ht
        linarith
       _= _:=avg_const w hw1 _
lemma switch_movement {k:ℝ} (hk:1≤k) (hw:∀ ω,0≤w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (H:ℕ→Ω→ℕ) (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z) (N:ℕ):
    total w N (switchCharge P Q)≤180*k+2*(1+ruleConstant)*stock P Q N:=by
  have hp:=RuleSchedule.payment (flat P) (ruleFlags P) (marked P Q) (reset P Q) (D P Q) H hw
    (D_nonneg P Q) (fun t ω he=>congrArg Option.isSome (ordinary_mark P Q t ω he))
    (fun ir=> hP ir.1 ir.2) hr (flags_adapted P H hP) (marked_adapted P Q H hP hQ hr)
    (reset_adapted P Q H hP hQ hr) (D_adapted P Q H hP hQ hr) N
  simp only [ruleJ_eq,flat,raw_drift_eq] at hp
  have hi:=rule_initial hk hw hw1 P Q hs hq
  have he:=rule_expense hw hw1 P Q hs N
  have hd:=drift_le_stock hw P Q N
  change total w N (switchCharge P Q)≤2*(_+drift (flat P) N+_) at hp
  dsimp only [total] at he
  linarith only [hp,hi,he,hd]

end KServer.ActualCharges
end


/-! All-step output charging, including wholesale jumps without a charge per
child or per epoch. The parent variation retains coefficient exactly one. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar OutputDynamics
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma coarse_output {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤ k)
    (t:ℕ) (ω:Ω) (q:ℝ)
    (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤ q) (i:J):
    out hk P Q t ω q i≤80*vector cutoff ds P ω t i:=by
  have hd:=output_domination hk P Q hs hq t ω q hp i
  by_cases hi:i∈ActualStar.active P t ω
  · have hl:0<(CoarseProcess.active cutoff ds (P i) ω t).value:=by
      exact (AllocationSchedule.mem_activeSet (vector cutoff ds P ω t) i).mp hi
    have ha:=(active_accuracy (by norm_num [cutoff]:0<cutoff) (by norm_num [ds]:0<ds)
      (by norm_num [ds]:ds≤1/1000) (P i) ω t).1
      ((live_iff (by norm_num [ds]) (by norm_num [ds]) (P i) t ω).mp hl)
    change _≤80*(CoarseProcess.active cutoff ds (P i) ω t).value
    linarith [ha.1]
  · have hf:=(out_feasible hk P Q hs hq t ω q hp).1 i
    rw [inactive_d hk P Q t ω (hq t ω) hi] at hf
    exact hf.2.trans (mul_nonneg (by norm_num) (vector_nonneg cutoff ds P ω t i))

lemma wholesale_output {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤ k)
    (t:ℕ) (ω:Ω) (q q':ℝ)
    (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤ q)
    (hp':(∑ i,(n P (t+1) ω i-β k Q (t+1) ω*B P (t+1) ω i+f k P Q (t+1) ω i))≤ q')
    (he:reset P Q (t+1) ω=true):
    variation (out hk P Q (t+1) ω q') (out hk P Q t ω q)≤80*ActualCharges.wholesale P Q t ω:=by
  have hr:EpochSchedule.reset (vector cutoff ds P ω t) (vector cutoff ds P ω (t+1))
      (key Q t ω) (key Q (t+1) ω) (EpochSchedule.run (vector cutoff ds P ω) (fun s=>key Q s ω) t):=by
    simpa only [reset,Nat.add_sub_cancel,decide_eq_true_eq] using he
  rw [ActualCharges.wholesale,EpochSchedule.wholesale,ite_eq_left hr]
  calc _≤∑ i,(out hk P Q (t+1) ω q' i+out hk P Q t ω q i):=by
        apply sum_le_sum
        intro i _
        exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (output_domination hk P Q hs hq (t+1) ω q' hp' i).1,
          abs_of_nonneg (output_domination hk P Q hs hq t ω q hp i).1])
       _≤∑ i,(80*vector cutoff ds P ω (t+1) i+80*vector cutoff ds P ω t i):=
        sum_le_sum fun i _=>add_le_add (coarse_output hk P Q hs hq (t+1) ω q' hp' i)
          (coarse_output hk P Q hs hq t ω q hp i)
       _= _:=by simp only [sum_add_distrib,←mul_sum,EpochSchedule.total]; ring

lemma all_movement {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤ k)
    (t:ℕ) (ω:Ω) (q q':ℝ)
    (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤ q)
    (hp':(∑ i,(n P (t+1) ω i-β k Q (t+1) ω*B P (t+1) ω i+f k P Q (t+1) ω i))≤ q'):
    variation (out hk P Q (t+1) ω q') (out hk P Q t ω q)≤
      |q'-q|+2*(if reset P Q (t+1) ω then 0 else variation (d k P Q (t+1) ω) (d k P Q t ω))+
      40*(S P (t+1) ω*variation (α k P Q (t+1) ω) (α k P Q t ω)+
        D P Q (t+1) ω*variation (side hk P Q (t+1) ω) (side hk P Q t ω)+
        |D P Q (t+1) ω-D P Q t ω|+switchCharge P Q t ω)+80*ActualCharges.wholesale P Q t ω:=by
  cases he:reset P Q (t+1) ω with
  | false=>
    simp only [Bool.false_eq_true,ite_false]
    exact (ordinary_movement hk P Q hs t ω (hq (t+1) ω) q q' hp' he).trans
      (le_add_of_nonneg_right (mul_nonneg (by norm_num) (ActualCharges.wholesale_nonneg P Q t ω)))
  | true=>
    have hh:=wholesale_output hk P Q hs hq t ω q q' hp hp' he
    simp only [ite_true,mul_zero,add_zero]
    have hS:=mul_nonneg (S_nonneg P (t+1) ω) (variation_nonneg (α k P Q (t+1) ω) (α k P Q t ω))
    have hD:=mul_nonneg (D_nonneg P Q (t+1) ω) (variation_nonneg (side hk P Q (t+1) ω) (side hk P Q t ω))
    linarith [abs_nonneg (q'-q),abs_nonneg (D P Q (t+1) ω-D P Q t ω),switchCharge_nonneg P Q t ω]
end KServer.ActualOutput

end


/-! The unconditional local allocation movement theorem for the
literal output already constructed. Its parent coefficient is exactly one;
all other costs are true drift and a fixed, law/horizon-independent inventory. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar ActualOutput
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def fineConstant:ℝ:=2*(160/rho+flagConstant)
def movementConstant:ℝ:=2*fineConstant+40*(13*C+simplexConstant+3600/cw+sideConstant+
  scaleConstant+2*(1+ruleConstant))+80*wholesaleConstant
def endpointConstant:ℝ:=40*(1144*C+440000*(1/cw+1)+180)
def localConstant:ℝ:=movementConstant+endpointConstant+1
lemma output_constants_nonneg:0≤ fineConstant ∧ 0≤ movementConstant ∧ 0≤ endpointConstant ∧ 0<localConstant:=by
  have hc:=positive.2.2.2.2.1
  have hw:=positive.2.2.2.1
  have hr:=positive.2.2.2.2.2.2.2.1
  have hf:=constants_nonneg.2.2
  have hh:=more_constants_nonneg.1
  have hs:=more_constants_nonneg.2.1
  have he:=edit_constants_nonneg.1
  have he2:=edit_constants_nonneg.2
  have hb:=ruleConstant_nonneg
  have hfi:0≤ fineConstant:=by dsimp [fineConstant]; positivity
  have hm:0≤ movementConstant:=by dsimp only [movementConstant]; positivity
  have hep:0≤ endpointConstant:=by dsimp only [endpointConstant]; positivity
  refine ⟨hfi,hm,hep,?_⟩
  dsimp only [localConstant]; linarith

lemma fine_movement {k:ℝ} (hk:1≤ k) (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (hq:∀ t ω,size Q t ω≤ k) (N:ℕ):
    total w N (fun t ω=>if reset P Q (t+1) ω then 0 else
      ChangingDomains.variation (d k P Q (t+1) ω) (d k P Q t ω))≤ fineConstant*ActualCaps.ell k*stock P Q N:=by
  have hp:=fine_budget hk hw hw1 P Q hq N
  change total w N (fun t ω=>if reset P Q (t+1) ω then 0 else
    ChangingDomains.variation (d k P Q (t+1) ω) (d k P Q t ω))≤
      2*(160/(rho/ActualCaps.ell k)+flagConstant)*inventory (flat P) N at hp
  have hc:0≤ 2*(160/(rho/ActualCaps.ell k)+flagConstant):=by
    have hr:=positive.2.2.2.2.2.2.2.1; have he:=ActualCaps.ell_pos hk; have hf:=constants_nonneg.2.2
    positivity
  have hu:=mul_le_mul_of_nonneg_left (inventory_child_le hw P Q N) hc
  have hell:=ActualCaps.ell_ge_one hk
  have hf:=mul_nonneg constants_nonneg.2.2 (stock_nonneg hw P Q N)
  have herr:=mul_nonneg (sub_nonneg.mpr hell) hf
  rw [div_div_eq_mul_div] at hp hu
  simp only [fineConstant,div_eq_mul_inv] at hp hu ⊢
  nlinarith only [hp,hu,herr]

lemma output_movement {k:ℝ} (hk:1≤ k) (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤ k)
    (H:ℕ→Ω→ℕ) (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (q:ℕ→Ω→ℝ)
    (hp:∀ t ω,(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤ q t ω) (N:ℕ):
    total w N (fun t ω=>ChangingDomains.variation (out hk P Q (t+1) ω (q (t+1) ω)) (out hk P Q t ω (q t ω)))≤
      total w N (fun t ω=>|q (t+1) ω-q t ω|)+
        movementConstant*ActualCaps.ell k*stock P Q N+endpointConstant*ActualCaps.ell k*k:=by
  have h:=total_mono hw (N:=N) (fun t ω=>all_movement hk P Q hs hq t ω (q t ω) (q (t+1) ω) (hp t ω) (hp (t+1) ω))
  simp only [total_add,total_mul] at h
  simp only [OutputDynamics.variation,ChangingDomains.variation] at h ⊢
  have hf:=fine_movement hk hw hw1 P Q hq N
  have ha:=simplex_movement hk hw hw1 P Q hs hq H hP hQ hr N
  have hb:=side_movement hk hw hw1 P Q hs hq H hP hQ hr N
  have hd:=scale_bound hw hw1 P Q hs N
  have hc:=switch_movement hk hw hw1 P Q hs hq H hP hQ hr N
  have hh:=wholesale_bound hw hw1 P Q hs N
  simp only [ChangingDomains.variation] at hf ha hb
  have hel:=ActualCaps.ell_ge_one hk
  have hst:=stock_nonneg hw P Q N
  have h1:=mul_nonneg (sub_nonneg.mpr hel) (mul_nonneg more_constants_nonneg.2.1 hst)
  have h2:=mul_nonneg (sub_nonneg.mpr hel) (mul_nonneg more_constants_nonneg.1 hst)
  have h3:=mul_nonneg (sub_nonneg.mpr hel) (mul_nonneg (add_nonneg zero_le_one ruleConstant_nonneg) hst)
  have h4:=mul_nonneg (sub_nonneg.mpr hel) (show 0≤ k by linarith)
  dsimp only [movementConstant,endpointConstant]
  nlinarith only [h,hf,ha,hb,hd,hc,hh,h1,h2,h3,h4]

lemma local_movement {k:ℝ} (hk:1≤ k) (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤ k)
    (H:ℕ→Ω→ℕ) (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (q:ℕ→Ω→ℝ)
    (hp:∀ t ω,(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤ q t ω) (N:ℕ):
    total w N (fun t ω=>ChangingDomains.variation (out hk P Q (t+1) ω (q (t+1) ω)) (out hk P Q t ω (q t ω)))≤
      total w N (fun t ω=>|q (t+1) ω-q t ω|)+
        localConstant*ActualCaps.ell k*(drift (flat P) N+drift Q N+(Fintype.card (J×R):ℝ)+Fintype.card R+k):=by
  have h:=output_movement hk hw hw1 P Q hs hq H hP hQ hr q hp N
  have hs0:=stock_nonneg hw P Q N
  have hek:=mul_nonneg (ActualCaps.ell_pos hk).le (show 0≤ k by linarith)
  have hes:=mul_nonneg (ActualCaps.ell_pos hk).le hs0
  have hm:=output_constants_nonneg.2.1
  have he:=output_constants_nonneg.2.2.1
  have hstock : drift (flat P) N+drift Q N+(Fintype.card (J×R):ℝ)+Fintype.card R+k=stock P Q N+k:=by
    dsimp only [stock,inventory]; ring
  rw [hstock]
  dsimp only [localConstant]
  nlinarith only [h,hes,hek,mul_nonneg hm hek,mul_nonneg he hes]
end KServer.ActualCharges

end


/-! The actual top-down allocation, summed over the fixed complete-prefix
hierarchy. All initialization costs depend only on the fixed label inventory. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalQuota
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking ActualCharges
variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}

lemma sum_snoc {d:ℕ} (f:(Fin (d+1)→A)→ℝ):
    (∑ word,f word)=∑ word:Fin d→A,∑ a:A,f (Fin.snoc word a):=by
  calc _ = ∑ p:A×(Fin d→A),f (Fin.snoc p.2 p.1):=
          (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (d+1)=>A)) _ _ (fun _=>rfl)).symm
       _ = _:=by rw [Fintype.sum_prod_type,sum_comm]

lemma total_sum {I:Type} [Fintype I] (w:Ω→ℝ) (N:ℕ) (f:I→ℕ→Ω→ℝ):
    total w N (fun t ω=>∑ i,f i t ω)=∑ i,total w N (f i):=by
  unfold total
  simp_rw [avg_sum]
  exact sum_comm

lemma drift_flat {R:Type} [Fintype R] (P:A→R→FilteredRanks w) (N:ℕ):
    drift (flat P) N=∑ a,drift (P a) N:=by
  unfold drift flat
  simp_rw [Fintype.sum_prod_type,avg_sum]
  rw [sum_comm]

variable (hw:∀ ω,0 ≤ w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

def nodeMove (hk:1 ≤ (k:ℝ)) {d:ℕ} (word:Fin d→A) (N:ℕ):ℝ:=
  total w N (fun t ω=>|quota hw H hr maps q hk d word (t+1) ω-quota hw H hr maps q hk d word t ω|)
def levelMove (hk:1 ≤ (k:ℝ)) (d N:ℕ):ℝ:=∑ word:Fin d→A,nodeMove hw H hr maps q hk word N
def levelDrift (d N:ℕ):ℝ:=∑ word:Fin d→A,drift (parent hw H hr maps q word) N

def levelInventory (A:Type) [Fintype A] (k d:ℕ):ℝ:=
  Fintype.card (Fin d→A)*((Fintype.card (A×Fin k):ℝ)+Fintype.card (Fin k)+(k:ℝ))

lemma levelMove_nonneg (hk:1 ≤ (k:ℝ)) (d N:ℕ):0 ≤ levelMove hw H hr maps q hk d N:=by
  unfold levelMove nodeMove total
  exact sum_nonneg fun _ _=>sum_nonneg fun _ _=>sum_nonneg fun ω _=>mul_nonneg (hw ω) (abs_nonneg _)
lemma levelDrift_nonneg (d N:ℕ):0 ≤ levelDrift hw H hr maps q d N:=by
  unfold levelDrift drift
  exact sum_nonneg fun _ _=>sum_nonneg fun _ _=>sum_nonneg fun ω _=>mul_nonneg (hw ω) (sum_nonneg fun _ _=>abs_nonneg _)
lemma levelMove_zero (hk:1 ≤ (k:ℝ)) (N:ℕ):levelMove hw H hr maps q hk 0 N=0:=by
  simp [levelMove,nodeMove,quota,total,avg]
lemma levelDrift_zero (N:ℕ):levelDrift hw H hr maps q 0 N=0:=by
  unfold levelDrift drift
  apply sum_eq_zero
  intro word _
  apply sum_eq_zero
  intro t _
  unfold avg
  apply sum_eq_zero
  intro ω _
  have he:∀ a:Fin k,(parent hw H hr maps q word a).p (t+1) ω=0:=fun a=>
    HierarchicalRanks.family_root hw H hr maps q word a (t+1) ω
  have hb:∀ a:Fin k,(parent hw H hr maps q word a).before (t+1) ω=0:=by
    intro a
    change PosteriorRanks.posterior w (H (t+1)) (PosteriorRanks.rank
      (fun ρ=>HierarchyCounts.count (maps t ρ) word (q t ρ)) a.val) ω=0
    have hz:PosteriorRanks.rank (fun ρ=>HierarchyCounts.count (maps t ρ) word (q t ρ)) a.val=fun _=>0:=by
      funext ρ
      simp only [PosteriorRanks.rank,HierarchyCounts.count_zero]
      exact ite_eq_right (by omega)
    rw [hz]
    simp [PosteriorRanks.posterior,PosteriorRanks.numerator]
  simp only [he,hb,sub_self,abs_zero,sum_const_zero,mul_zero]

lemma level_movement (hk:1 ≤ (k:ℝ)) (hw1:∑ ω,w ω=1) (hwpos:∀ ω,0<w ω) (d N:ℕ):
    levelMove hw H hr maps q hk (d+1) N ≤ levelMove hw H hr maps q hk d N+
      localConstant*ActualCaps.ell k*(levelDrift hw H hr maps q d N+
        levelDrift hw H hr maps q (d+1) N+levelInventory A k d):=by
  have h word:=local_movement hk hw hw1 (children hw H hr maps q word) (parent hw H hr maps q word)
    (sizes hw H hr maps q word hwpos) (size_bound hw H hr maps q word) H
    (fun _ _ _ _=>rfl) (fun _ _ _=>rfl) hr (quota hw H hr maps q hk d word)
    (fun t ω=>parent_budget hw H hr maps q hk word hwpos t ω _
      (quota_bounds hw H hr maps q hk hwpos d word t ω).1) N
  have hs:=sum_le_sum (s:=univ) (fun word _=>h word)
  simp only [ChangingDomains.variation,total_sum,←quota_snoc,drift_flat] at hs
  change (∑ word:Fin d→A,∑ a:A,nodeMove hw H hr maps q hk (Fin.snoc word a) N) ≤ _ at hs
  rw [←sum_snoc (fun word=>nodeMove hw H hr maps q hk word N)] at hs
  simp only [sum_add_distrib,←mul_sum] at hs
  change levelMove hw H hr maps q hk (d+1) N ≤ levelMove hw H hr maps q hk d N+_ at hs
  have he:(∑ word:Fin d→A,∑ a:A,drift (children hw H hr maps q word a) N)=levelDrift hw H hr maps q (d+1) N:=by
    rw [levelDrift,sum_snoc (fun word=>drift (parent hw H hr maps q word) N)]
    rfl
  rw [he] at hs
  simp only [sum_const,nsmul_eq_mul,card_univ] at hs
  convert hs using 1; simp only [levelDrift,levelInventory]; ring
end KServer.HierarchicalQuota

end


/-! Geometric absorption with the literal parent coefficient one. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalQuota

lemma weighted_shift (r m:ℕ→ℝ) (hr:∀ d,0 ≤ r d) (hm:∀ d,0 ≤ m d)
    (hroot:m 0=0) (hhalf:∀ d,r (d+1) ≤ r d/2) (L:ℕ):
    (∑ d∈range L,r d*m d) ≤ (1/2:ℝ)*∑ d∈range L,r d*m (d+1):=by
  cases L with
  | zero=>simp
  | succ L=>
    rw [sum_range_succ',hroot,mul_zero,add_zero]
    calc _ ≤ ∑ d∈range L,(1/2:ℝ)*(r d*m (d+1)):=by
            apply sum_le_sum
            intro d _
            have h:=mul_le_mul_of_nonneg_right (hhalf d) (hm (d+1))
            linarith
         _ = (1/2:ℝ)*∑ d∈range L,r d*m (d+1):=by rw [mul_sum]
         _ ≤ (1/2:ℝ)*∑ d∈range (L+1),r d*m (d+1):=by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            rw [sum_range_succ]
            exact le_add_of_nonneg_right (mul_nonneg (hr L) (hm (L+1)))

variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0 ≤ w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

open ActualCharges

def treeMove (hk:1 ≤ (k:ℝ)) (r:ℕ→ℝ) (L N:ℕ):ℝ:=
  ∑ d∈range L,r d*levelMove hw H hr maps q hk (d+1) N
def treeDrift (r:ℕ→ℝ) (L N:ℕ):ℝ:=
  ∑ d∈range L,r d*(levelDrift hw H hr maps q d N+levelDrift hw H hr maps q (d+1) N)
def treeInventory (A:Type) [Fintype A] (k:ℕ) (r:ℕ→ℝ) (L:ℕ):ℝ:=
  ∑ d∈range L,r d*levelInventory A k d
lemma treeInventory_nonneg (A:Type) [Fintype A] (k:ℕ) (r:ℕ→ℝ) (hr:∀ d,0 ≤ r d) (L:ℕ):
    0 ≤ treeInventory A k r L:=by
  unfold treeInventory levelInventory
  exact sum_nonneg fun d _=>mul_nonneg (hr d) (by positivity)

theorem allocation_absorption (hk:1 ≤ (k:ℝ)) (hw1:∑ ω,w ω=1) (hwpos:∀ ω,0<w ω)
    (r:ℕ→ℝ) (hrad:∀ d,0 ≤ r d) (hhalf:∀ d,r (d+1) ≤ r d/2) (L N:ℕ):
    treeMove hw H hr maps q hk r L N ≤
      2*localConstant*ActualCaps.ell k*(treeDrift hw H hr maps q r L N+treeInventory A k r L):=by
  have hp:=weighted_shift r (fun d=>levelMove hw H hr maps q hk d N) hrad
    (fun d=>levelMove_nonneg hw H hr maps q hk d N) (levelMove_zero hw H hr maps q hk N) hhalf L
  have he:(∑ d∈range L,r d*(localConstant*ActualCaps.ell k*
      (levelDrift hw H hr maps q d N+levelDrift hw H hr maps q (d+1) N+levelInventory A k d)))=
      localConstant*ActualCaps.ell k*(treeDrift hw H hr maps q r L N+treeInventory A k r L):=by
    unfold treeDrift treeInventory
    rw [←sum_add_distrib,mul_sum]
    apply sum_congr rfl
    intro d _
    ring
  have hs':treeMove hw H hr maps q hk r L N ≤
      (∑ d∈range L,r d*levelMove hw H hr maps q hk d N)+
      localConstant*ActualCaps.ell k*(treeDrift hw H hr maps q r L N+treeInventory A k r L):=by
    have hh:=sum_le_sum (s:=range L) (fun d _=>
      mul_le_mul_of_nonneg_left (level_movement hw H hr maps q hk hw1 hwpos d N) (hrad d))
    simp only [mul_add,sum_add_distrib] at hh
    rw [←he]
    simpa only [mul_add,sum_add_distrib,treeMove] using hh
  change _ ≤ (1/2:ℝ)*treeMove hw H hr maps q hk r L N at hp
  linarith
end KServer.HierarchicalQuota

end


/-! Conditional-drift coupling for literal fixed-prefix occupancies. The
right side is movement of the hidden labeled configurations, not observation
noise or a hypothesized allocation cost. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalQuota
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking ActualCharges HierarchyCounts

lemma histogram_distance {I B:Type} [Fintype I] [Fintype B] [DecidableEq B] (f g:I→B):
    (∑ b:B,|(∑ i:I,if f i=b then (1:ℝ) else 0)-(∑ i:I,if g i=b then (1:ℝ) else 0)|) ≤
      2*∑ i:I,if f i=g i then (0:ℝ) else 1:=by
  calc _ ≤ ∑ b:B,∑ i:I,|((if f i=b then (1:ℝ) else 0)-(if g i=b then (1:ℝ) else 0))|:=by
            apply sum_le_sum
            intro b _
            rw [←sum_sub_distrib]
            exact abs_sum_le_sum_abs _ _
       _ = ∑ i:I,∑ b:B,|((if f i=b then (1:ℝ) else 0)-(if g i=b then (1:ℝ) else 0))|:=sum_comm
       _ = _:=by
            rw [mul_sum]
            apply sum_congr rfl
            intro i _
            by_cases h:f i=g i
            · simp [h]
            · have hp:∀ b:B,|((if f i=b then (1:ℝ) else 0)-(if g i=b then (1:ℝ) else 0))|=
                (if b=f i then 1 else 0)+(if b=g i then 1 else 0):=by
                intro b
                by_cases hf:b=f i <;> by_cases hg:b=g i
                · exact False.elim (h (hf.symm.trans hg))
                · simp [hf,Ne.symm h,h]
                · simp [hg,Ne.symm h,h]
                · simp [Ne.symm hf,Ne.symm hg,hf,hg]
              simp only [hp,sum_add_distrib]
              norm_num [h]

variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0 ≤ w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

def address (d:ℕ) (t:ℕ) (ω:Ω) (l:Fin k):Fin d→A:=fun i=>maps t ω i.val (q t ω l)
def prefixCross (d:ℕ) (t:ℕ) (ω:Ω):ℝ:=
  ∑ l:Fin k,if address maps q d (t+1) ω l=address maps q d t ω l then 0 else 1

def levelHidden (d N:ℕ):ℝ:=total w N (fun t ω=>∑ word:Fin d→A,
  |(count (maps (t+1) ω) word (q (t+1) ω):ℝ)-count (maps t ω) word (q t ω)|)

omit [Fintype Ω] [Fintype A] in
lemma count_histogram {d:ℕ} (word:Fin d→A) (t:ℕ) (ω:Ω):
    (count (maps t ω) word (q t ω):ℝ)=∑ l:Fin k,if address maps q d t ω l=word then (1:ℝ) else 0:=by
  simp only [count,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply sum_congr rfl
  intro l _
  have he:hit (maps t ω) word (q t ω l)↔address maps q d t ω l=word:=by
    exact ⟨fun h=>funext h,fun h i=>congrFun h i⟩
  simp only [he]

lemma level_drift_count (d N:ℕ):levelDrift hw H hr maps q d N ≤ levelHidden (w:=w) maps q d N:=by
  unfold levelDrift drift levelHidden total
  rw [sum_comm]
  apply sum_le_sum
  intro t _
  rw [avg_sum]
  apply sum_le_sum
  intro word _
  rw [avg_sum]
  exact PosteriorRanks.rankProcess_drift hw H hr
    (fun t ω=>count (maps t ω) word (q t ω)) (fun t ω=>count_le _ _ _) t

include hw in
lemma level_count_cross (d N:ℕ):levelHidden (w:=w) maps q d N ≤ 2*total w N (prefixCross maps q d):=by
  unfold levelHidden
  rw [←total_mul]
  apply total_mono hw
  intro t ω
  simp only [count_histogram maps q]
  unfold prefixCross
  exact (histogram_distance (I:=Fin k) (B:=Fin d→A) (address maps q d (t+1) ω) (address maps q d t ω))

omit [Fintype Ω] [Fintype A] in
lemma prefixCross_nonneg (d t:ℕ) (ω:Ω):0 ≤ prefixCross maps q d t ω:=by
  unfold prefixCross
  exact sum_nonneg fun _ _=>by split_ifs <;> norm_num

end KServer.HierarchicalQuota

end

end OAI
