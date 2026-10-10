import Mathlib
import OAI.Combinatorics.KServer.Caps

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma inactive_flexcap {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (hq:size Q t ω≤k) {i:J} (hi:i∉ActualStar.active P t ω):flexcap k P Q t ω i=0:=by
  have hd:=inactive_d hk P Q t ω hq hi
  have hn:=TrackedCaps.count_nonneg (P i) t ω
  have hb:=ActualCaps.flexCap_nonneg hk Q (P i) (decide (mark P Q t ω=some i)) t ω hq
  change 0≤flexcap k P Q t ω i at hb
  change n P t ω i+flexcap k P Q t ω i=0 at hd
  change 0≤n P t ω i at hn
  linarith
lemma regular_upper {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤k)
    (i:J) (ho:mark P Q t ω≠some i):flexcap k P Q t ω i≤f k P Q t ω i:=by
  by_cases hi:i∈ActualStar.active P t ω
  · exact (regular_caps hk P Q hs t ω hq i hi ho).2
  · rw [inactive_flexcap hk P Q t ω hq hi,inactive_f k P Q t ω hi]
lemma own_flex_le {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (i:J)
    (hi:i∈ActualStar.active P t ω):fc k P t ω i≤f k P Q t ω i:=by
  have hg:=parameter_gap hk P Q hs t ω i hi
  have hn:0≤cg*h P Q t ω i/ActualCaps.ell k:=
    div_nonneg (mul_nonneg positive.2.1.le (h_nonneg P Q t ω i)) (ActualCaps.ell_pos hk).le
  apply TrackedCaps.flex_antitone (P i) t ω
  dsimp only [β] at hg
  linarith
lemma cap_lower {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤k)
    (i:J):fc k P t ω i≤flexcap k P Q t ω i:=by
  by_cases hi:i∈ActualStar.active P t ω
  · by_cases ho:mark P Q t ω=some i
    · exact (own_flex_le hk P Q hs t ω i hi).trans (dominant_caps hk P Q t ω hq ho).1
    · exact (regular_caps hk P Q hs t ω hq i hi ho).1
  · have hh:=inactive_f k P (P i) t ω hi
    change fc k P t ω i=0 at hh
    rw [hh,inactive_flexcap hk P Q t ω hq hi]
lemma error_sum {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤k):
    (∑ i,(flexcap k P Q t ω i-f k P Q t ω i))≤e k P Q t ω:=by
  cases ho:mark P Q t ω with
  | none=>
    simp only [e,ho]
    exact sum_nonpos fun i _=>sub_nonpos.mpr (regular_upper hk P Q hs t ω hq i (by simp [ho]))
  | some o=>
    calc
      _≤∑ i,(if i=o then flexcap k P Q t ω o-f k P Q t ω o else 0):=by
        apply sum_le_sum
        intro i _
        by_cases hi:i=o
        · subst i; simp only [ite_true,le_refl]
        · rw [ite_eq_right hi]
          exact sub_nonpos.mpr (regular_upper hk P Q hs t ω hq i (by simpa [ho,eq_comm] using hi))
      _=e k P Q t ω:=by simp only [sum_ite_eq',mem_univ,ite_true,e,ho]
lemma dominant_slack {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤k)
    (i:J) (hi:i∈ActualStar.active P t ω):
    (cg*h P Q t ω i/ActualCaps.ell k)/96*f k P Q t ω i≤
      (n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i)-lower k (P i) t ω:=by
  have hg:=parameter_gap hk P Q hs t ω i hi
  have hn:0≤cg*h P Q t ω i/ActualCaps.ell k:=
    div_nonneg (mul_nonneg positive.2.1.le (h_nonneg P Q t ω i)) (ActualCaps.ell_pos hk).le
  have hzz:ActualCaps.z k Q t ω≤ActualCaps.z k (P i) t ω:=by dsimp only [β] at hg; linarith
  have hf:=TrackedCaps.flex_slack (P i) (ActualCaps.ranges hk Q t ω hq).1 hzz t ω
  have hb:=mul_nonneg (sub_nonneg.mpr hzz) (TrackedCaps.core_nonneg (P i) t ω)
  have hfn:=TrackedCaps.flex_nonneg (P i) (ActualCaps.ranges hk Q t ω hq).1 t ω
  have hmul:=mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hg (by norm_num : (0:ℝ)≤96)) hfn
  rw [lower_decomposition]
  dsimp only [f,fc,B,β] at *
  linarith only [hf,hb,hmul]
end KServer.ActualOutput

end


/-! Rule I applied to the actual scheduled proportions and caps. Its only
external numeric input is a parent allocation covering the sum of the child
lower envelopes at the parent's parameter (the rank superadditivity premise). -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def outI (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) (q:ℝ):J→ℝ:=
  OutputDynamics.outputI (d k P Q t ω) q (α k P Q t ω)

lemma ruleI_T {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (hq:size Q t ω≤k)
    (hr:∀ o,mark P Q t ω=some o→D P Q t ω/2≤S P t ω):T k P Q t ω≤4*S P t ω:=by
  cases ho:mark P Q t ω with
  | none=>simp only [T,ho]; linarith [S_nonneg P t ω]
  | some o=>linarith [(DT_compare hk P Q t ω hq).1,hr o ho]

lemma outI_feasible {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (t:ℕ) (ω:Ω) (q:ℝ)
    (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤q)
    (hr:∀ o,mark P Q t ω=some o→D P Q t ω/2≤S P t ω) :
    (∀ i,lower k (P i) t ω≤outI k P Q t ω q i ∧ outI k P Q t ω q i≤d k P Q t ω i) ∧
      (∑ i,outI k P Q t ω q i)≤q := by
  have hps:∀ s z,(∑ i,size (P i) s z)≤k:=fun s z=>(hs s z).trans (hq s z)
  have ha:=α_mem k P Q t ω
  have hprop:=α_feasible hk P Q hps t ω
  have hb:=beta_range hk Q t ω (hq t ω)
  have he:=e_bounds hk P Q t ω (hq t ω)
  have hT:=ruleI_T hk P Q t ω (hq t ω) hr
  have hS:=S_nonneg P t ω
  have hTn:=T_nonneg hk P Q t ω (hq t ω)
  have hzero:S P t ω=0→e k P Q t ω=0:=by
    intro hz
    have ht:T k P Q t ω=0:=by linarith
    rw [ht,mul_zero] at he
    exact le_antisymm he.2 he.1
  have hcaps:=error_sum hk P Q hs t ω (hq t ω)
  have hout (i:J):lower k (P i) t ω≤outI k P Q t ω q i ∧ outI k P Q t ω q i≤d k P Q t ω i:=by
    by_cases hi:i∈ActualStar.active P t ω
    · have hbi:=beta_range hk (P i) t ω ((child_size P t ω i).trans (hps t ω))
      have hg:=parameter_gap hk P Q hs t ω i hi
      by_cases hm:mark P Q t ω=some i
      · have hsum:∑ j,α k P Q t ω j=1:=by
          simpa only [ite_eq_left (show (ActualStar.active P t ω).Nonempty from ⟨i,hi⟩)] using ha.2.1
        have hroom:=OutputConstants.dominant_room hb.2 (h_nonneg P Q t ω i) (ActualCaps.ell_pos hk) hg
        have hfc:fc k P t ω i≤flexcap k P Q t ω i-e k P Q t ω:=by
          have hf:=own_flex_le hk P Q hs t ω i hi
          simp only [e,hm]
          linarith
        have hh:=OutputDynamics.outputI_dominant (βi:=fun j=>β k (P j) t ω) hp hcaps (by linarith : 0≤β k Q t ω) he.1
          (fun j=>TrackedCaps.core_nonneg (P j) t ω) ha.1 hsum hprop i hroom (fc k P t ω i) hfc
        rw [lower_decomposition]
        exact hh
      · have hroom:=OutputConstants.regular_room hS he.1 hT (h_one P Q t ω i hm)
          (h_upper hk P Q hps t ω i) (ActualCaps.ell_pos hk) hb.2 he.2 hg
        have hh:=OutputDynamics.outputI_regular (βi:=fun j=>β k (P j) t ω) hp hcaps (by linarith : 0≤β k Q t ω) he.1
          (fun j=>TrackedCaps.core_nonneg (P j) t ω) ha.1 hprop hzero i (by linarith : 0≤β k (P i) t ω)
          (by linarith [OutputConstants.eta_nonneg (h_nonneg P Q t ω i) (ActualCaps.ell_pos hk)]:0≤1+ct*h P Q t ω i/ActualCaps.ell k)
          hroom (fc k P t ω i) (cap_lower hk P Q hs t ω (hq t ω) i)
        rw [lower_decomposition]
        exact hh
    · have hd:=inactive_d hk P Q t ω (hq t ω) hi
      have hl:=inactive_lower k P t ω hi
      have haz:=ha.2.2 i hi
      simp only [outI,OutputDynamics.outputI,OutputDynamics.holesI,hd,haz,hl,mul_zero,sub_zero,le_refl,and_self]
  refine ⟨hout,?_⟩
  by_cases hn:(ActualStar.active P t ω).Nonempty
  · have hsum:∑ j,α k P Q t ω j=1:=by simpa only [ite_eq_left hn] using ha.2.1
    exact (OutputDynamics.outputI_budget hsum (d k P Q t ω) q).le.trans (min_le_right _ _)
  · have hz:∀ i,d k P Q t ω i=0:=fun i=>inactive_d hk P Q t ω (hq t ω) (fun hi=>hn ⟨i,hi⟩)
    have houtz:∀ i,outI k P Q t ω q i=0:=by
      intro i
      have hl:0≤lower k (P i) t ω:=lower_nonneg hk (P i) t ω ((child_size P t ω i).trans (hps t ω))
      have h:=hout i
      rw [hz i] at h
      linarith
    have hparentzero:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))=0:=by
      apply sum_eq_zero
      intro i _
      have hh:=inactive_lower_zero (by norm_num [ds]) (by norm_num [ds]) (P i)
        (inactive P t ω (fun hi=>hn ⟨i,hi⟩)) (ActualCaps.z k Q t ω)
      rw [TrackedCaps.decomposition] at hh
      exact hh
    simp only [houtz,sum_const_zero]
    rwa [hparentzero] at hp
end KServer.ActualOutput

end


/-! Literal side minimizer bounds at the fixed absolute constants. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def sides (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w):ℕ→Ω→Finset J:=StarSide.sides ds P (key Q)
def sideData {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) : ℕ→Ω→CausalSide.Input J R:=
  StarSide.input positive.2.2.2.1 (ActualCaps.ell_pos hk) ds P (key Q) (ActualStar.b k Q)
def side {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w):ℕ→Ω→J→ℝ:=
  StarSide.proportion positive.2.2.2.1 (ActualCaps.ell_pos hk) ds P (key Q) (ActualStar.b k Q)
def slack {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):J→ℝ:=
  fun i=>if i∈sides P Q t ω then (sideData hk P Q t ω).data.θ i*(sideData hk P Q t ω).data.z i else 0

lemma sides_eq (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω)
    {o:J} (ho:mark P Q t ω=some o):sides P Q t ω=(ActualStar.active P t ω).erase o:=by
  change (match mark P Q t ω with | none=>∅ | some o=>(ActualStar.active P t ω).erase o)=_
  rw [ho]
lemma side_mem {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):
    side hk P Q t ω∈ChangingDomains.sideDomain (sides P Q t ω) 16:=
  StarSide.proportion_mem _ _ _ _ _ _ _ _
lemma side_core {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) (i:J):
    SideFamilies.core (sideData hk P Q t ω).data (sideData hk P Q t ω).ranks i=
      if i∈sides P Q t ω then B P t ω i else 0:=by
  change (∑ r,if (if i∈sides P Q t ω then CoreFlags.flag (P i r) t ω else false) then (P i r).p t ω else 0)=_
  by_cases hi:i∈sides P Q t ω
  · rw [ite_eq_left hi]
    simp only [ite_eq_left hi]
    rfl
  · rw [ite_eq_right hi]
    simp only [ite_eq_right hi,Bool.false_eq_true,ite_false,sum_const_zero]
lemma side_core_total {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):
    (∑ i,SideFamilies.core (sideData hk P Q t ω).data (sideData hk P Q t ω).ranks i)≤S P t ω:=by
  apply sum_le_sum
  intro i _
  rw [side_core]
  split_ifs
  · rfl
  · exact TrackedCaps.core_nonneg (P i) t ω
lemma side_logs (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω)
    {o i:J} (ho:mark P Q t ω=some o) (hi:i≠o):StarSide.logs ds P (key Q) t ω i=h P Q t ω i:=by
  apply max_eq_right
  exact h_one P Q t ω i (by simpa [ho,eq_comm] using hi)
lemma side_upper {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (t:ℕ) (ω:Ω) {o i:J} (ho:mark P Q t ω=some o) (hi:i∈sides P Q t ω):
    D P Q t ω*side hk P Q t ω i≤β k (P i) t ω*B P t ω i:=by
  have hr:=mem_erase.mp ((sides_eq P Q t ω ho) ▸ hi)
  have hb:=b_range hk Q t ω (hq t ω)
  have hf:=StarSide.feasible (δ:=ds) (cw:=cw) (by norm_num [ds]) (by norm_num [ds]) hk
    positive.2.2.2.1 small.2.1 P (key Q) (ActualStar.b k Q) (fun s z=>(hs s z).trans (hq s z)) t ω
    (by linarith : 1≤ActualStar.b k Q t ω) hb.2
  dsimp only at hf
  have hf0:=hf.1 i
  change D P Q t ω*side hk P Q t ω i≤(ActualStar.b k Q t ω+cw*StarSide.logs ds P (key Q) t ω i/ActualCaps.ell k)*
    SideFamilies.core (sideData hk P Q t ω).data (sideData hk P Q t ω).ranks i at hf0
  rw [side_core,ite_eq_left hi,side_logs P Q t ω ho hr.1] at hf0
  have hroom:=OutputConstants.side_room (h_one P Q t ω i (by simpa [ho,eq_comm] using hr.1))
    (ActualCaps.ell_pos hk) (b_error hk Q t ω).2 (parameter_gap hk P Q hs t ω i hr.2)
  exact hf0.trans (mul_le_mul_of_nonneg_right hroom (TrackedCaps.core_nonneg (P i) t ω))
lemma side_lower {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (t:ℕ) (ω:Ω) (hS:S P t ω≤2*D P Q t ω) {i:J} (hi:i∈sides P Q t ω):
    β k Q t ω*B P t ω i-D P Q t ω*slack hk P Q t ω i≤D P Q t ω*side hk P Q t ω i:=by
  have hb:=b_range hk Q t ω (hq t ω)
  have hf:=StarSide.feasible (δ:=ds) (cw:=cw) (by norm_num [ds]) (by norm_num [ds]) hk
    positive.2.2.2.1 small.2.1 P (key Q) (ActualStar.b k Q) (fun s z=>(hs s z).trans (hq s z)) t ω
    (by linarith : 1≤ActualStar.b k Q t ω) hb.2
  dsimp only at hf
  have ht:(∑ j,SideFamilies.core (sideData hk P Q t ω).data (sideData hk P Q t ω).ranks j)≤2*(sideData hk P Q t ω).data.D:=
    (side_core_total hk P Q t ω).trans hS
  have hf0:=hf.2 ht i
  change ActualStar.b k Q t ω*SideFamilies.core (sideData hk P Q t ω).data (sideData hk P Q t ω).ranks i-
    (sideData hk P Q t ω).data.θ i*(sideData hk P Q t ω).data.z i*D P Q t ω≤D P Q t ω*side hk P Q t ω i at hf0
  rw [side_core,ite_eq_left hi] at hf0
  have hm:=mul_le_mul_of_nonneg_right (b_error hk Q t ω).1 (TrackedCaps.core_nonneg (P i) t ω)
  change β k Q t ω*B P t ω i≤ActualStar.b k Q t ω*B P t ω i at hm
  simp only [slack,ite_eq_left hi]
  nlinarith only [hf0,hm]
end KServer.ActualOutput

end


/-! Side slack for the actual held logarithms, including zero and empty side
mass. This is a proved inequality, not an assumed output feasibility interface. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma slack_nonneg {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (i:J):0 ≤ slack hk P Q t ω i:=by
  unfold slack
  split_ifs
  · exact mul_nonneg ((sideData hk P Q t ω).data.θ_pos i).le ((sideData hk P Q t ω).data.z_pos i).le
  · rfl
lemma slack_exp {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) {o i:J} (ho:mark P Q t ω=some o) (hi:i∈sides P Q t ω):
    slack hk P Q t ω i=(cw/ActualCaps.ell k*Real.exp 1)*Real.exp (-h P Q t ω i):=by
  have hio:=(mem_erase.mp ((sides_eq P Q t ω ho) ▸ hi)).1
  have hh:=h_one P Q t ω i (by simpa [ho,eq_comm] using hio)
  have hh0:h P Q t ω i≠0:=ne_of_gt (by linarith)
  rw [slack,ite_eq_left hi]
  change cw*StarSide.logs ds P (key Q) t ω i/ActualCaps.ell k*
    (Real.exp (1-StarSide.logs ds P (key Q) t ω i)/StarSide.logs ds P (key Q) t ω i)=_
  rw [side_logs P Q t ω ho hio,sub_eq_add_neg,Real.exp_add]
  field_simp
lemma slack_sum {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) {o:J} (ho:mark P Q t ω=some o):
    (∑ i,slack hk P Q t ω i)≤128*cw*h P Q t ω o/ActualCaps.ell k:=by
  have hsum:=side_exp_sum (δ:=ds) (by norm_num [ds]) (by norm_num [ds])
    (vector cutoff ds P ω) (fun s=>key Q s ω) (vector_nonneg cutoff ds P ω) t ho
  have hu:h P Q t ω o=sideRatio ds (vector cutoff ds P ω) (fun s=>key Q s ω) t:=
    marked_weight ds _ _ t o ho
  have hn:=h_nonneg P Q t ω o
  have hc:0≤cw/ActualCaps.ell k:=div_nonneg positive.2.2.2.1.le (ActualCaps.ell_pos hk).le
  have he:(∑ i,slack hk P Q t ω i)=(cw/ActualCaps.ell k*Real.exp 1)*
      ∑ i∈sides P Q t ω,Real.exp (-h P Q t ω i):=by
    calc
      _=∑ i∈sides P Q t ω,slack hk P Q t ω i:=by
        symm
        apply sum_subset (subset_univ _)
        intro i _ hi
        simp only [slack,ite_eq_right hi]
      _=_:=by rw [mul_sum]; exact sum_congr rfl fun i hi=>slack_exp hk P Q t ω ho hi
  have hbound:(∑ i∈sides P Q t ω,Real.exp (-h P Q t ω i))≤2*h P Q t ω o:=by
    rw [hu]
    simpa only [sides_eq P Q t ω ho,h,ActualStar.active] using hsum
  have hm:=mul_le_mul_of_nonneg_left hbound (mul_nonneg hc (Real.exp_pos 1).le)
  have h2:=mul_le_mul_of_nonneg_right (le_of_lt Real.exp_one_lt_three) (mul_nonneg hc hn)
  rw [he]
  simp only [div_eq_mul_inv] at hm h2 hc ⊢
  nlinarith only [hm,h2,mul_nonneg hc hn]
lemma side_slack_paid {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤k)
    {o:J} (ho:mark P Q t ω=some o):
    D P Q t ω*(∑ i,slack hk P Q t ω i)≤
      (n P t ω o-β k Q t ω*B P t ω o+f k P Q t ω o)-lower k (P o) t ω:=by
  have hm:=mul_le_mul_of_nonneg_left (slack_sum hk P Q t ω ho) (D_nonneg P Q t ω)
  have hroom:=OutputConstants.residual_room (h_nonneg P Q t ω o) (T_nonneg hk P Q t ω hq)
    (DT_compare hk P Q t ω hq).2 (ActualCaps.ell_pos hk)
  simp only [T,ho] at hroom
  exact (hm.trans hroom).trans (dominant_slack hk P Q hs t ω hq o (mark_active P Q t ω ho))
end KServer.ActualOutput

end


/-! The residual Rule II formula and its feasibility for the actual side
minimizer and marked flex scale. Empty side sets require no separate assumption. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def sideOut {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):J→ℝ:=
  fun i=>d k P Q t ω i-D P Q t ω*side hk P Q t ω i
def outII {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) (o:J) (q:ℝ):J→ℝ:=
  fun i=>if i=o then min (d k P Q t ω o) (q-∑ j∈univ.erase o,sideOut hk P Q t ω j) else sideOut hk P Q t ω i

lemma sideOut_feasible {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (t:ℕ) (ω:Ω) {o i:J} (ho:mark P Q t ω=some o) (hi:i≠o):
    lower k (P i) t ω≤ sideOut hk P Q t ω i ∧ sideOut hk P Q t ω i≤d k P Q t ω i:=by
  have hmem:=side_mem hk P Q t ω
  have hn:=mul_nonneg (D_nonneg P Q t ω) (hmem.1 i)
  by_cases ha:i∈ActualStar.active P t ω
  · have his:i∈sides P Q t ω:=by rw [sides_eq P Q t ω ho]; exact mem_erase.mpr ⟨hi,ha⟩
    have hu:=side_upper hk P Q hs hq t ω ho his
    have hf:=cap_lower hk P Q hs t ω (hq t ω) i
    rw [lower_decomposition]
    dsimp only [sideOut,d]
    constructor <;> linarith
  · have his:i∉sides P Q t ω:=by rw [sides_eq P Q t ω ho]; exact fun h=>ha (mem_erase.mp h).2
    have hw:=hmem.2.2 i his
    simp only [sideOut,inactive_d hk P Q t ω (hq t ω) ha,inactive_lower k P t ω ha,hw,mul_zero,sub_zero,le_refl,and_self]
lemma sideOut_parent {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (t:ℕ) (ω:Ω) (hS:S P t ω≤2*D P Q t ω) {o i:J} (ho:mark P Q t ω=some o) (hi:i≠o):
    sideOut hk P Q t ω i≤n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i+D P Q t ω*slack hk P Q t ω i:=by
  by_cases ha:i∈ActualStar.active P t ω
  · have his:i∈sides P Q t ω:=by rw [sides_eq P Q t ω ho]; exact mem_erase.mpr ⟨hi,ha⟩
    have hl:=side_lower hk P Q hs hq t ω hS his
    have hf:=regular_upper hk P Q hs t ω (hq t ω) i (by simpa [ho,eq_comm] using hi)
    dsimp only [sideOut,d]
    linarith
  · have his:i∉sides P Q t ω:=by rw [sides_eq P Q t ω ho]; exact fun h=>ha (mem_erase.mp h).2
    have hw:=(side_mem hk P Q t ω).2.2 i his
    have hp:=inactive_lower_zero (by norm_num [ds]) (by norm_num [ds]) (P i)
      (inactive P t ω ha) (ActualCaps.z k Q t ω)
    rw [TrackedCaps.decomposition] at hp
    change n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i=0 at hp
    simp only [sideOut,inactive_d hk P Q t ω (hq t ω) ha,hw,mul_zero,sub_zero,hp,zero_add]
    exact mul_nonneg (D_nonneg P Q t ω) (slack_nonneg hk P Q t ω i)

lemma outII_feasible {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (t:ℕ) (ω:Ω) {o:J} (ho:mark P Q t ω=some o) (q:ℝ)
    (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤q)
    (hS:S P t ω≤2*D P Q t ω) :
    (∀ i,lower k (P i) t ω≤outII hk P Q t ω o q i ∧ outII hk P Q t ω o q i≤d k P Q t ω i) ∧
      (∑ i,outII hk P Q t ω o q i)≤q := by
  let L:J→ℝ:=fun i=>n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i
  have hpaid:=side_slack_paid hk P Q hs t ω (hq t ω) ho
  change D P Q t ω*(∑ i,slack hk P Q t ω i)≤L o-lower k (P o) t ω at hpaid
  have he: (∑ i∈univ.erase o,L i)+L o=∑ i,L i:=sum_erase_add univ L (mem_univ o)
  have hsides:(∑ i∈univ.erase o,sideOut hk P Q t ω i)≤
      (∑ i∈univ.erase o,L i)+D P Q t ω*(∑ i,slack hk P Q t ω i):=by
    calc
      _≤∑ i∈univ.erase o,(L i+D P Q t ω*slack hk P Q t ω i):=
        sum_le_sum fun i hi=>sideOut_parent hk P Q hs hq t ω hS ho (mem_erase.mp hi).1
      _=(∑ i∈univ.erase o,L i)+D P Q t ω*(∑ i∈univ.erase o,slack hk P Q t ω i):=by rw [sum_add_distrib,mul_sum]
      _≤_:=add_le_add_right (mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun i _ _=>slack_nonneg hk P Q t ω i))
        (D_nonneg P Q t ω)) _
  have hrem:lower k (P o) t ω≤q-∑ i∈univ.erase o,sideOut hk P Q t ω i:=by
    change (∑ i,L i)≤q at hp
    linarith
  have hcap:lower k (P o) t ω≤d k P Q t ω o:=by
    have hc:=cap_lower hk P Q hs t ω (hq t ω) o
    have hb:=beta_range hk (P o) t ω ((child_size P t ω o).trans ((hs t ω).trans (hq t ω)))
    have hm:=mul_nonneg (show 0≤β k (P o) t ω by linarith) (TrackedCaps.core_nonneg (P o) t ω)
    change 0≤β k (P o) t ω*B P t ω o at hm
    rw [lower_decomposition]
    dsimp only [d]
    linarith
  refine ⟨?_,?_⟩
  · intro i
    by_cases hi:i=o
    · subst i
      simp only [outII,ite_true]
      exact ⟨le_min hcap hrem,min_le_left _ _⟩
    · simpa only [outII,ite_eq_right hi] using sideOut_feasible hk P Q hs hq t ω ho hi
  · have hout:(∑ i∈univ.erase o,outII hk P Q t ω o q i)=(∑ i∈univ.erase o,sideOut hk P Q t ω i):=by
      apply sum_congr rfl
      intro i hi
      exact ite_eq_right (mem_erase.mp hi).1
    rw [←sum_erase_add univ _ (mem_univ o),hout]
    have hm:=min_le_right (d k P Q t ω o) (q-∑ i∈univ.erase o,sideOut hk P Q t ω i)
    simp only [outII,ite_true]
    linarith
end KServer.ActualOutput

end


/-! Literal two-regime rule schedule of §05. The rule is decided without
using the parent allocation. Ordinary switches earn potential drops; the
filtering increment is retained on every history, before the tests. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.RuleSchedule
attribute [local instance] Classical.propDecidable

/-- `true` is rule II. Ties select I at a restart. -/
def choose (S D : ℝ) : Bool := decide (S < D/2)
def update (S D : ℝ) (old : Bool) : Bool :=
  if old then decide (S ≤ 2*D) else choose S D
def step (marked reset : Bool) (S D : ℝ) (old : Bool) : Bool :=
  if marked then if reset then choose S D else update S D old else false

def run {Ω : Type*} (marked reset : ℕ → Ω → Bool) (S D : ℕ → Ω → ℝ) : ℕ → Ω → Bool
  | 0, ω => step (marked 0 ω) true (S 0 ω) (D 0 ω) false
  | t+1, ω => step (marked (t+1) ω) (reset (t+1) ω) (S (t+1) ω) (D (t+1) ω)
      (run marked reset S D t ω)

def allowed (marked rule : Bool) (S D : ℝ) : Prop :=
  (marked=false → rule=false) ∧
  (marked=true → if rule then S≤2*D else D/2≤S)

lemma choose_allowed {S D : ℝ} (hD : 0≤D) :
    if choose S D then S≤2*D else D/2≤S := by
  unfold choose
  split_ifs with h
  · simp only [decide_eq_true_eq] at h
    linarith
  · simp only [decide_eq_true_eq,not_lt] at h
    exact h

lemma step_allowed {S D : ℝ} (hD : 0≤D) (marked reset old : Bool) :
    allowed marked (step marked reset S D old) S D := by
  cases marked with
  | false => simp [allowed,step]
  | true =>
    refine ⟨(by intro h; cases h), ?_⟩
    intro _
    change (if (if reset then choose S D else update S D old) then S≤2*D else D/2≤S)
    cases reset with
    | true => simpa using choose_allowed hD
    | false =>
      cases old with
      | false => simpa [update] using choose_allowed hD
      | true =>
        simp only [update,Bool.false_eq_true,ite_false,ite_true]
        split_ifs with h
        · exact of_decide_eq_true h
        · have h' : 2*D<S := by simpa only [decide_eq_true_eq,not_le] using h
          linarith

lemma run_allowed {Ω : Type*} (marked reset : ℕ → Ω → Bool) (S D : ℕ → Ω → ℝ)
    (hD : ∀ t ω,0≤D t ω) (t : ℕ) (ω : Ω) :
    allowed (marked t ω) (run marked reset S D t ω) (S t ω) (D t ω) := by
  cases t <;> exact step_allowed (hD _ _) _ _ _

def value (marked rule : Bool) (S D : ℝ) : ℝ :=
  if marked then if rule then S else D else 0

def charge (marked reset old : Bool) (S D : ℝ) : ℝ :=
  if reset then 0 else if marked then
    if update S D old=old then 0 else if update S D old then D else S
  else 0

lemma value_nonneg {S D : ℝ} (hS : 0≤S) (hD : 0≤D) (marked rule : Bool) :
    0≤value marked rule S D := by
  cases marked <;> cases rule <;> simp [value,hS,hD]
lemma value_upper {S D : ℝ} (hS : 0≤S) (hD : 0≤D) (marked rule : Bool) :
    value marked rule S D≤S+D := by
  cases marked <;> cases rule <;> simp only [value,Bool.false_eq_true,ite_true,ite_false] <;> linarith
lemma charge_nonneg {S D : ℝ} (hS : 0≤S) (hD : 0≤D) (marked reset old : Bool) :
    0≤charge marked reset old S D := by
  unfold charge
  split_ifs <;> first | assumption | rfl

lemma ordinary_credit (S D : ℝ) (marked old : Bool) :
    charge marked false old S D/2+value marked (step marked false S D old) S D≤
      value marked old S D := by
  cases marked with
  | false => simp [charge,value]
  | true =>
    cases old with
    | false =>
      by_cases h:S<D/2
      · simp [charge,value,step,update,choose,h]
        linarith
      · simp [charge,value,step,update,choose,h]
    | true =>
      by_cases h:S≤2*D
      · simp [charge,value,step,update,h]
      · simp [charge,value,step,update,h]
        linarith

variable {Ω R : Type*} [Fintype Ω] [Fintype R]
open RankTracking

def core (f : R → Bool) (p : R → ℝ) : ℝ := ∑ r,if f r then p r else 0

def coefficient (marked rule : Bool) (f : R → Bool) (r : R) : ℝ :=
  if marked && rule && f r then 1 else 0

omit [Fintype Ω] in
lemma input_difference (marked rule : Bool) (f : R → Bool) (p q : R → ℝ) (D : ℝ) :
    value marked rule (core f p) D-value marked rule (core f q) D=
      ∑ r,coefficient marked rule f r*(p r-q r) := by
  cases marked <;> cases rule <;> simp [value,core,coefficient,←sum_sub_distrib]
  apply sum_congr rfl
  intro r _
  split_ifs <;> simp

omit [Fintype Ω] in
lemma core_nonneg (f : R → Bool) {p : R → ℝ} (hp : ∀ r,0≤p r) : 0≤core f p := by
  exact sum_nonneg fun r _=>by split_ifs; exact hp r; rfl

omit [Fintype Ω] in
lemma input_lipschitz (marked rule : Bool) (f : R → Bool) (p q : R → ℝ) (D : ℝ) :
    |value marked rule (core f p) D-value marked rule (core f q) D|≤∑ r,|p r-q r| := by
  rw [input_difference]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro r _
  unfold coefficient
  split_ifs <;> simp

omit [Fintype Ω] in
lemma data_change (marked rule : Bool) (f g : R → Bool) (p : R → ℝ) {D E : ℝ}
    (hp : ∀ r,p r∈Set.Icc 0 1) :
    value marked rule (core g p) E-value marked rule (core f p) D≤
      (∑ r,if f r=g r then (0:ℝ) else 1)+|E-D| := by
  have hn:0≤∑ r,if f r=g r then (0:ℝ) else 1:=sum_nonneg fun _ _=>by positivity
  have hc:core g p-core f p≤∑ r,if f r=g r then (0:ℝ) else 1 := by
    rw [core,core,←sum_sub_distrib]
    apply sum_le_sum
    intro r _
    cases hf:f r <;> cases hg:g r <;> simp <;> linarith [(hp r).1,(hp r).2]
  cases marked <;> cases rule <;> simp only [value,Bool.false_eq_true,ite_true,ite_false] <;>
    linarith [abs_nonneg (E-D),le_abs_self (E-D)]

omit [Fintype Ω] in
lemma run_congr (marked reset : ℕ → Ω → Bool) (S D : ℕ → Ω → ℝ) (t : ℕ) (ω z : Ω)
    (hm : ∀ s≤t,marked s ω=marked s z) (hr : ∀ s≤t,reset s ω=reset s z)
    (hS : ∀ s≤t,S s ω=S s z) (hD : ∀ s≤t,D s ω=D s z) :
    run marked reset S D t ω=run marked reset S D t z := by
  induction t with
  | zero => simp only [run,hm 0 le_rfl,hS 0 le_rfl,hD 0 le_rfl]
  | succ t ih =>
    simp only [run,hm _ le_rfl,hr _ le_rfl,hS _ le_rfl,hD _ le_rfl]
    rw [ih (fun s hs=>hm s (hs.trans (Nat.le_succ t)))
      (fun s hs=>hr s (hs.trans (Nat.le_succ t)))
      (fun s hs=>hS s (hs.trans (Nat.le_succ t)))
      (fun s hs=>hD s (hs.trans (Nat.le_succ t)))]

end KServer.RuleSchedule

end


/-! The literal causal-regime output of a star: true hysteresis, both formulas,
and feasibility, uniformly in empty and vanishing-core cases. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def marked (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):Bool:=
  (mark P Q t ω).isSome
def reset (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):Bool:=
  decide (EpochSchedule.reset (vector cutoff ds P ω (t-1)) (vector cutoff ds P ω t)
    (key Q (t-1) ω) (key Q t ω) (EpochSchedule.run (vector cutoff ds P ω) (fun s=>key Q s ω) (t-1)))
def rule (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w):ℕ→Ω→Bool:=
  RuleSchedule.run (marked P Q) (reset P Q) (S P) (D P Q)
def out {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (q:ℝ):J→ℝ:=
  match mark P Q t ω with
  | none=>outI k P Q t ω q
  | some o=>if rule P Q t ω then outII hk P Q t ω o q else outI k P Q t ω q

lemma rule_allowed (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):
  RuleSchedule.allowed (marked P Q t ω) (rule P Q t ω) (S P t ω) (D P Q t ω):=
  RuleSchedule.run_allowed _ _ _ _ (D_nonneg P Q) t ω
lemma out_feasible {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (t:ℕ) (ω:Ω) (q:ℝ)
    (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤q):
    (∀ i,lower k (P i) t ω≤out hk P Q t ω q i ∧ out hk P Q t ω q i≤d k P Q t ω i) ∧
      (∑ i,out hk P Q t ω q i)≤q:=by
  have hr:=rule_allowed P Q t ω
  cases ho:mark P Q t ω with
  | none=>
    simp only [out,ho]
    exact outI_feasible hk P Q hs hq t ω q hp (fun o h=>by rw [ho] at h; cases h)
  | some o=>
    have hm:marked P Q t ω=true:=by simp [marked,ho]
    have hreg:=hr.2 hm
    cases hb:rule P Q t ω with
    | false=>
      simp only [out,ho,hb,Bool.false_eq_true,ite_false]
      simp only [hb,Bool.false_eq_true,ite_false] at hreg
      exact outI_feasible hk P Q hs hq t ω q hp (fun _ _=>hreg)
    | true=>
      simp only [out,ho,hb,ite_true]
      simp only [hb,ite_true] at hreg
      exact outII_feasible hk P Q hs hq t ω ho q hp hreg

lemma output_domination {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (t:ℕ) (ω:Ω) (q:ℝ)
    (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤q) (i:J):
    0≤out hk P Q t ω q i ∧ out hk P Q t ω q i≤72*size (P i) t ω:=by
  have h:=out_feasible hk P Q hs hq t ω q hp
  exact ⟨(lower_nonneg hk (P i) t ω ((child_size P t ω i).trans ((hs t ω).trans (hq t ω)))).trans (h.1 i).1,
    (h.1 i).2.trans (d_bounds hk P Q t ω (hq t ω) i).2⟩
end KServer.ActualOutput

end

end OAI
