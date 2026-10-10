import Mathlib
import OAI.Combinatorics.KServer.AllocationSchedule

namespace OAI

/-! The actual rankwise caps used by the star construction: core flags and
both endpoint trackers run for the full history, not only at output times. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TrackedCaps
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoreFlags
variable {Ω R : Type} [Fintype Ω] [Fintype R] {w : Ω → ℝ}

def count (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ r, if flag (P r) t ω then 1 else 0

def core (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ r, if flag (P r) t ω then (P r).p t ω else 0

def flex (P : R → FilteredRanks w) (z : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ r, if flag (P r) t ω then 0 else rank z ((P r).p t ω)

def estimate (P : R → FilteredRanks w) (ξ a : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ r, if flag (P r) t ω then 0 else FineCaps.interpolated ξ a (P r) t ω

def cap (P : R → FilteredRanks w) (ξ a κ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ r,FineCaps.capTerm ξ a κ (P r) t ω

lemma cap_eq (P : R → FilteredRanks w) (ξ a κ : ℝ) (t : ℕ) (ω : Ω) :
    cap P ξ a κ t ω=count P t ω+κ*estimate P ξ a t ω := by
  unfold cap count estimate
  rw [mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro r _
  unfold FineCaps.capTerm
  split_ifs <;> ring

lemma count_nonneg (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : 0≤count P t ω := by
  exact sum_nonneg fun r _=>by split_ifs <;> norm_num

lemma core_nonneg (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : 0≤core P t ω := by
  exact sum_nonneg fun r _=>by split_ifs; exact ((P r).range t ω).1; rfl

lemma flex_nonneg (P : R → FilteredRanks w) {z : ℝ} (hz : z∈Set.Icc 0 (1/100:ℝ))
    (t : ℕ) (ω : Ω) : 0≤flex P z t ω := by
  exact sum_nonneg fun r _=>by split_ifs; rfl; exact rank_nonneg hz _

lemma decomposition (P : R → FilteredRanks w) (z : ℝ) (t : ℕ) (ω : Ω) :
    (∑ r,rank z ((P r).p t ω))=count P t ω-(3+z)*core P t ω+flex P z t ω := by
  unfold count core flex
  rw [mul_sum,←sum_sub_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro r _
  cases hf : flag (P r) t ω with
  | false => simp
  | true =>
    have h:=core_upper (P r) hf
    have hp : (P r).p t ω≤pstar := by norm_num [pstar] at *; linarith
    simp only [ite_true,add_zero,rank,ite_eq_left hp]

lemma domination (P : R → FilteredRanks w) {z : ℝ} (hz : z∈Set.Icc 0 (1/100:ℝ))
    (t : ℕ) (ω : Ω) : count P t ω+flex P z t ω≤36*CoarseProcess.size P t ω := by
  unfold count flex CoarseProcess.size
  rw [←sum_add_distrib,mul_sum]
  apply sum_le_sum
  intro r _
  cases hf : flag (P r) t ω with
  | false => simpa using CoarseScale.rank_size hz ((P r).range t ω).1
  | true =>
    have hp : (P r).p t ω ≤ sstar := by
      have h:=core_upper (P r) hf
      norm_num [sstar] at *
      linarith
    have h:=CompatibleBounds.sizeRank_below_cutoff hp
    simp only [ite_true,add_zero]
    linarith

lemma flex_antitone (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    Antitone (fun z=>flex P z t ω) := by
  intro z z' h
  apply sum_le_sum
  intro r _
  split_ifs
  · rfl
  · exact rank_parameter_antitone ((P r).range t ω).1 h

lemma flex_slack (P : R → FilteredRanks w) {z z' : ℝ}
    (hz : z∈Set.Icc 0 (1/100:ℝ)) (hzz : z≤z') (t : ℕ) (ω : Ω) :
    (z'-z)/96*flex P z t ω≤flex P z t ω-flex P z' t ω := by
  unfold flex
  rw [mul_sum,←sum_sub_distrib]
  apply sum_le_sum
  intro r _
  cases hf : flag (P r) t ω with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    have hp : pstar/4≤(P r).p t ω := by
      have h:=noncore_lower (P r) hf
      norm_num [pstar] at *
      linarith
    have h:=mul_le_mul_of_nonneg_left (parameterSlope_compare hz hp).1 (sub_nonneg.mpr hzz)
    rw [rank_parameter_affine z,rank_parameter_affine z']
    rw [rank_parameter_affine z] at h
    nlinarith

lemma estimate_error (P : R → FilteredRanks w) {ξ a z ε : ℝ}
    (hξ : 0<ξ) (ha : a∈Set.Icc 0 1) (hz : z∈Set.Icc 0 (1/100:ℝ))
    (hza : z≤a/100) (hea : a/100-z≤ε) (t : ℕ) (ω : Ω) :
    |estimate P ξ a t ω-flex P z t ω|≤(ξ+ε)*flex P z t ω := by
  unfold estimate flex
  rw [←sum_sub_distrib,mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro r _
  cases hf : flag (P r) t ω with
  | true => simp
  | false =>
    simpa using FineCaps.noncore_interpolation_error hξ ha hz hza hea (P r) t ω hf

lemma scaled_bounds (P : R → FilteredRanks w) {ξ a z z' ε l g b : ℝ}
    (hξ : 0<ξ) (ha : a∈Set.Icc 0 1) (hz : z∈Set.Icc 0 (1/100:ℝ))
    (hza : z≤a/100) (hea : a/100-z≤ε) (hε : 0≤ε)
    (hl : 0<l) (hls : l≤1/4) (hel : ξ+ε≤l/4)
    (hg : 4*l≤g) (hb : 4*l≤b) (hzz : z≤z') (hgap : g≤(z'-z)/96)
    (t : ℕ) (ω : Ω) :
    (flex P z' t ω≤(1-l)*estimate P ξ a t ω ∧ (1-l)*estimate P ξ a t ω≤flex P z t ω) ∧
    (flex P z t ω≤(1+l)*estimate P ξ a t ω ∧ (1+l)*estimate P ξ a t ω≤(1+b)*flex P z t ω) := by
  have hn:=flex_nonneg P hz t ω
  have hs:=flex_slack P hz hzz t ω
  have hfc : flex P z' t ω≤(1-g)*flex P z t ω := by
    have h:=mul_le_mul_of_nonneg_right hgap hn
    nlinarith
  exact FineCaps.cap_scaling hn (estimate_error P hξ ha hz hza hea t ω)
    (add_nonneg hξ.le hε) hl hls hel hg hb hfc

omit [Fintype R] in
lemma endpoint_adapted (P : FilteredRanks w) (ξ z : ℝ) (t : ℕ) {ω ρ : Ω}
    (h : P.history t ω=P.history t ρ) :
    FineCaps.estimate ξ z P t ω=FineCaps.estimate ξ z P t ρ := by
  unfold FineCaps.estimate
  congr 1
  exact held_adapted _ P t ω ρ h

lemma cap_adapted (P : R → FilteredRanks w) (ξ a κ : ℝ) (t : ℕ) {ω ρ : Ω}
    (h : ∀ r,(P r).history t ω=(P r).history t ρ) :
    cap P ξ a κ t ω=cap P ξ a κ t ρ := by
  apply sum_congr rfl
  intro r _
  unfold FineCaps.capTerm FineCaps.interpolated
  rw [flag_adapted (P r) t (h r),endpoint_adapted _ _ _ _ (h r),endpoint_adapted _ _ _ _ (h r)]

end KServer.TrackedCaps

end


/-! Literal side process at a filtered star. The scale is the independently
running coarse tracker of the marked child's noncore rank values, as in
( dominant-scale-definition ), not a retrospectively selected comparator. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.StarSide
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseProcess CoarseEpoch AllocationSchedule StarProfile
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω → ℝ}

def mark (δ : ℝ) (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (t : ℕ) (ω : Ω) : Option J :=
  EpochSchedule.dominant (EpochSchedule.run (vector cutoff δ P ω) (fun s=>key s ω) t)

def sides (δ : ℝ) (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (t : ℕ) (ω : Ω) : Finset J :=
  match mark δ P key t ω with
  | none=>∅
  | some o=>(activeSet (vector cutoff δ P ω t)).erase o

def coarseFlex (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ r,if CoreFlags.flag (P r) t ω then 0 else FineCaps.estimate δ 0 (P r) t ω

def scale (δ : ℝ) (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (t : ℕ) (ω : Ω) : ℝ :=
  match mark δ P key t ω with
  | none=>0
  | some o=>coarseFlex δ (P o) t ω

def sideFlags (δ : ℝ) (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (t : ℕ) (ω : Ω) : J → R → Bool :=
  fun i r=>if i∈sides δ P key t ω then CoreFlags.flag (P i r) t ω else false

def logs (δ : ℝ) (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (t : ℕ) (ω : Ω) : J → ℝ :=
  fun i=>max 1 (weight δ (vector cutoff δ P ω) (fun s=>key s ω) t i)

def input {cw ell : ℝ} (hcw : 0<cw) (hel : 0<ell) (δ : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (b : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : CausalSide.Input J R :=
  ⟨SideFamilies.fromLog (sides δ P key t ω) (sideFlags δ P key t ω)
    16 (b t ω) (scale δ P key t ω) cw ell (logs δ P key t ω)
    (by norm_num) hcw hel (fun i=>le_max_left _ _),
    fun ir=>(P ir.1 ir.2).p t ω,
    epoch (vector cutoff δ P ω) (fun s=>key s ω) t⟩

def proportion {cw ell : ℝ} (hcw : 0<cw) (hel : 0<ell) (δ : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (b : ℕ → Ω → ℝ) : ℕ → Ω → J → ℝ :=
  CausalSide.run 40 (input hcw hel δ P key b)

lemma coarseFlex_nonneg (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    0≤coarseFlex δ P t ω := by
  apply sum_nonneg
  intro r _
  split_ifs
  · rfl
  · exact (FineCaps.estimate_range (by norm_num : (0:ℝ)∈Set.Icc 0 (1/100:ℝ)) (P r) t ω).1

omit [DecidableEq J] in
lemma scale_nonneg (δ : ℝ) (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (t : ℕ) (ω : Ω) : 0 ≤ scale δ P key t ω := by
  unfold scale
  split
  · rfl
  · exact coarseFlex_nonneg _ _ _ _

lemma proportion_mem {cw ell : ℝ} (hcw : 0<cw) (hel : 0<ell) (δ : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (b : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : proportion hcw hel δ P key b t ω∈ChangingDomains.sideDomain (sides δ P key t ω) 16 :=
  CausalSide.run_mem 40 (input hcw hel δ P key b) t ω

lemma logs_upper {δ k : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (hk : 1≤k)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (hs : ∀ t ω,(∑ i,size (P i) t ω)≤k) (t : ℕ) (ω : Ω) (i : J) :
    logs δ P key t ω i≤20002*(1+Real.log (k+1)) := by
  apply max_le
  · have hl:=Real.log_nonneg (show 1≤k+1 by linarith)
    nlinarith
  · exact weight_upper hδ hδu hk (vector cutoff δ P ω) (fun s=>key s ω)
      (vector_nonneg cutoff δ P ω) (fun s=>vector_total hδ hδu P s ω (hs s ω))
      (fun s i hi=>vector_floor hδ hδu P s ω i hi) t i

lemma feasible {δ k cw : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (hk : 1≤k)
    (hcw : 0<cw) (hcwu : cw*20002≤1)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (b : ℕ → Ω → ℝ)
    (hs : ∀ t ω,(∑ i,size (P i) t ω)≤k) (t : ℕ) (ω : Ω)
    (hb : 1≤b t ω) (hbu : b t ω≤4) :
    let ell:=1+Real.log (k+1)
    let hel:0<ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
    let d:=input hcw hel δ P key b t ω
    let a:=proportion hcw hel δ P key b t ω
    (∀ i,d.data.D*a i≤(d.data.b+d.data.θ i)*SideFamilies.core d.data d.ranks i) ∧
    ((∑ i,SideFamilies.core d.data d.ranks i)≤2*d.data.D → ∀ i,
      d.data.b*SideFamilies.core d.data d.ranks i-d.data.θ i*d.data.z i*d.data.D≤d.data.D*a i) := by
  intro ell hel d a
  have hM : ∀ i∈d.data.active,d.data.b+d.data.θ i≤5 := by
    intro i _
    change b t ω+cw*logs δ P key t ω i/ell≤5
    have hl:=logs_upper hδ hδu hk P key hs t ω i
    have hh:=mul_le_mul_of_nonneg_left hl hcw.le
    have he:=mul_le_mul_of_nonneg_right hcwu hel.le
    have hu : cw*logs δ P key t ω i/ell≤1 := by
      apply (div_le_iff₀ hel).mpr
      dsimp [ell] at *
      nlinarith
    linarith
  have hW : 2*(5:ℝ)<d.data.W := by norm_num [d,input,SideFamilies.fromLog]
  have hp : ∀ ir,0≤d.ranks ir := fun ir=>((P ir.1 ir.2).range t ω).1
  have hf : ∀ i∉d.data.active,∀ r,d.data.flags i r=false := by
    intro i hi r
    change i∉sides δ P key t ω at hi
    change sideFlags δ P key t ω i r=false
    simp only [sideFlags,ite_eq_right hi]
  have h:=CausalSide.run_feasible (input hcw hel δ P key b) (M:=5) t ω hb
    (scale_nonneg δ P key t ω) hM hW hp hf
  dsimp only [a,proportion,d]
  simpa only [show (8:ℝ)*5=40 by norm_num] using h

lemma coarseFlex_adapted (δ : ℝ) (P : R → FilteredRanks w) (H : ℕ → Ω → ℕ)
    (hH : ∀ r t ω,(P r).history t ω=H t ω) (t : ℕ) (ω z : Ω) (he : H t ω=H t z) :
    coarseFlex δ P t ω=coarseFlex δ P t z := by
  apply sum_congr rfl
  intro r _
  have hh:(P r).history t ω=(P r).history t z := by rw[hH,hH,he]
  rw [CoreFlags.flag_adapted (P r) t hh,TrackedCaps.endpoint_adapted (P r) δ 0 t hh]

lemma input_adapted {cw ell : ℝ} (hcw : 0<cw) (hel : 0<ell) (δ : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (b : ℕ → Ω → ℝ) (H:ℕ→Ω→ℕ)
    (hH : ∀ i r t ω,(P i r).history t ω=H t ω)
    (hr : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z)
    (hb:∀ t ω z,H t ω=H t z→b t ω=b t z) (t : ℕ) (ω z : Ω) (he:H t ω=H t z) :
    input hcw hel δ P key b t ω=input hcw hel δ P key b t z := by
  have hx:ScheduleCausality.PrefixEq t (vector cutoff δ P ω) (vector cutoff δ P z) :=
    fun s hs=>vector_adapted δ P H hH hr s ω z (StarSimplex.history_prefix H hr hs he)
  have hk:ScheduleCausality.PrefixEq t (fun s=>key s ω) (fun s=>key s z) :=
    fun s hs=>hkey s ω z (StarSimplex.history_prefix H hr hs he)
  have hm:mark δ P key t ω=mark δ P key t z :=
    congrArg EpochSchedule.dominant (ScheduleCausality.run_prefix _ _ _ _ t hx hk)
  have hA:sides δ P key t ω=sides δ P key t z := by simp only [sides,hm,hx t le_rfl]
  have hD:scale δ P key t ω=scale δ P key t z := by
    simp only [scale,hm]
    split
    · rfl
    · exact coarseFlex_adapted δ _ H (hH _) t ω z he
  have hf:sideFlags δ P key t ω=sideFlags δ P key t z := by
    funext i r
    have hh:(P i r).history t ω=(P i r).history t z := by rw[hH,hH,he]
    simp only [sideFlags,hA,CoreFlags.flag_adapted (P i r) t hh]
  have hh:logs δ P key t ω=logs δ P key t z := by
    funext i
    exact congrArg (fun h:J→ℝ=>max 1 (h i)) (ScheduleCausality.weight_prefix δ _ _ _ _ t hx hk)
  have hp:(fun ir:J×R=>(P ir.1 ir.2).p t ω)=(fun ir=>(P ir.1 ir.2).p t z) := by
    funext ir
    exact (P ir.1 ir.2).adapted t ω z (by rw[hH,hH,he])
  unfold input SideFamilies.fromLog
  simp only [hA,hf,hD,hh,hp,hb t ω z he,ScheduleCausality.epoch_prefix _ _ _ _ t hx hk]

lemma proportion_adapted {cw ell : ℝ} (hcw : 0<cw) (hel : 0<ell) (δ : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (b : ℕ → Ω → ℝ) (H:ℕ→Ω→ℕ)
    (hH : ∀ i r t ω,(P i r).history t ω=H t ω)
    (hr : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z)
    (hb:∀ t ω z,H t ω=H t z→b t ω=b t z) (t : ℕ) (ω z : Ω) (he:H t ω=H t z) :
    proportion hcw hel δ P key b t ω=proportion hcw hel δ P key b t z :=
  CausalSide.run_adapted 40 _ H hr (input_adapted hcw hel δ P key b H hH hr hkey hb) t ω z he

end KServer.StarSide

end


/-! The literal held dominant noncore scale is uniformly comparable to the
current parameterized flex mass; zeros coincide without a positive-mass
assumption. This is (dominant-scale-definition) / (D-comparison) in §03. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CoarseFineBridge
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile StarSide CoreFlags
variable {Ω R:Type} [Fintype Ω] [Fintype R] {w:Ω→ℝ}

lemma base_compare (P:R→FilteredRanks w) {z:ℝ} (hz:z∈Set.Icc 0 (1/100:ℝ))
    (t:ℕ) (ω:Ω) :
    TrackedCaps.flex P z t ω≤TrackedCaps.flex P 0 t ω ∧
    TrackedCaps.flex P 0 t ω≤(1+z)*TrackedCaps.flex P z t ω := by
  refine ⟨TrackedCaps.flex_antitone P t ω hz.1,?_⟩
  unfold TrackedCaps.flex
  rw [mul_sum]
  apply sum_le_sum
  intro r _
  cases hf:flag (P r) t ω with
  | true=>simp
  | false=>
    simp only [Bool.false_eq_true,ite_false]
    have hp:pstar/4≤(P r).p t ω:=by
      have h:=noncore_lower (P r) hf
      norm_num [pstar] at *
      linarith
    have hg:parameterSlope ((P r).p t ω)≤rank z ((P r).p t ω):=(parameterSlope_compare hz hp).2
    have hm:=mul_le_mul_of_nonneg_left hg hz.1
    rw [rank_parameter_affine z] at hm ⊢
    nlinarith

lemma estimate_compare {δ:ℝ} (hδ:0<δ) (P:R→FilteredRanks w) (t:ℕ) (ω:Ω) :
    (1+δ)⁻¹*TrackedCaps.flex P 0 t ω≤coarseFlex δ P t ω ∧
    coarseFlex δ P t ω≤(1+δ)*TrackedCaps.flex P 0 t ω := by
  constructor <;> unfold TrackedCaps.flex coarseFlex
  · rw [mul_sum]
    apply sum_le_sum
    intro r _
    split_ifs
    · simp
    · exact (FineCaps.estimate_accuracy hδ (by norm_num) (P r) t ω).1
  · rw [mul_sum]
    apply sum_le_sum
    intro r _
    split_ifs
    · simp
    · exact (FineCaps.estimate_accuracy hδ (by norm_num) (P r) t ω).2

lemma compare {δ z:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hz:z∈Set.Icc 0 (1/100:ℝ))
    (P:R→FilteredRanks w) (t:ℕ) (ω:Ω) :
    (1/2:ℝ)*TrackedCaps.flex P z t ω≤coarseFlex δ P t ω ∧
    coarseFlex δ P t ω≤2*TrackedCaps.flex P z t ω := by
  have h:=estimate_compare hδ P t ω
  have hb:=base_compare P hz t ω
  have hF:=TrackedCaps.flex_nonneg P hz t ω
  have hD:=coarseFlex_nonneg δ P t ω
  have hpos:0<1+δ:=by linarith
  have hh:=mul_le_mul_of_nonneg_left h.1 hpos.le
  rw [←mul_assoc,mul_inv_cancel₀ (ne_of_gt hpos),one_mul] at hh
  have hhalf:=mul_le_mul_of_nonneg_left hδu hD
  have hzF:=mul_le_mul_of_nonneg_right hz.2 hF
  have hbase:=mul_le_mul_of_nonneg_left hb.2 hpos.le
  have hδF:=mul_le_mul_of_nonneg_left hδu hF
  have hδz:=mul_le_mul_of_nonneg_left hzF hδ.le
  constructor <;> nlinarith only [h.2,hb.1,hbase,hhalf,hh,hzF,hδF,hδz]

lemma zero_iff {δ z:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hz:z∈Set.Icc 0 (1/100:ℝ))
    (P:R→FilteredRanks w) (t:ℕ) (ω:Ω) :
    coarseFlex δ P t ω=0↔TrackedCaps.flex P z t ω=0 := by
  have h:=compare hδ hδu hz P t ω
  have hn:=coarseFlex_nonneg δ P t ω
  have hf:=TrackedCaps.flex_nonneg P hz t ω
  constructor <;> intro he <;> linarith

end KServer.CoarseFineBridge

end


/-! One fixed absolute choice in the order required by §05; neither the
separation ratio nor any finite input parameter enters these constants. -/
noncomputable section
namespace KServer.LocalConstants
def cb:ℝ:=1/100000000
def cg:ℝ:=cb/20
def ct:ℝ:=cb/1000000
def cw:ℝ:=cb/1000000000
def C:ℝ:=1000/ct
def eb:ℝ:=cb/1000000
def lb:ℝ:=cb/100000000
def rho:ℝ:=lb/16
def dp:ℝ:=lb/(64*cb)
def ds:ℝ:=1/1000

lemma positive : 0<cb ∧ 0<cg ∧ 0<ct ∧ 0<cw ∧ 0<C ∧ 0<eb ∧ 0<lb ∧ 0<rho ∧ 0<dp ∧ 0<ds := by
  norm_num [cb,cg,ct,cw,C,eb,lb,rho,dp,ds]
lemma small : ct*20002≤1 ∧ cw*20002≤1 ∧ 700<C*ct ∧
    10000*cb+4*cb*dp≤1/100 ∧ lb≤1/4 ∧ rho+4*cb*dp≤lb/4 ∧
    4*lb≤cg/96 ∧ 4*lb≤eb ∧ 4*ct≤cg/4 ∧ 8*eb≤cg/4 ∧ 4*cb*dp+cw≤cg/2 ∧
    256*cw≤cg/192 := by
  norm_num [cb,cg,ct,cw,C,eb,lb,rho,dp]
end KServer.LocalConstants

end


/-! Endpoint-only fine caps with the actual held parent parameter. These
estimates are run for every rank and time, not just during output epochs. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCaps
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile CoarseParameters
open LocalConstants
variable {Ω R:Type} [Fintype Ω] [Fintype R] {w:Ω→ℝ}

def ell (k:ℝ):ℝ:=1+Real.log (k+1)
def z (k:ℝ) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=beta k cutoff cb (ell k) (size Q t ω)-3
def a (k:ℝ) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  100*(upperBeta k cutoff cb (ell k) dp (parent cutoff dp Q t ω)-3)
def flexCap (k:ℝ) (Q P:R→FilteredRanks w) (dominant:Bool) (t:ℕ) (ω:Ω):ℝ:=
  (if dominant then 1+lb/ell k else 1-lb/ell k)*TrackedCaps.estimate P (rho/ell k) (a k Q t ω) t ω

def cap (k:ℝ) (Q P:R→FilteredRanks w) (dominant:Bool) (t:ℕ) (ω:Ω):ℝ:=
  TrackedCaps.count P t ω+flexCap k Q P dominant t ω

lemma ell_ge_one {k:ℝ} (hk:1≤k):1≤ell k:=by
  unfold ell
  linarith [Real.log_nonneg (show 1≤k+1 by linarith)]
lemma ell_pos {k:ℝ} (hk:1≤k):0<ell k:=lt_of_lt_of_le zero_lt_one (ell_ge_one hk)

lemma ranges {k:ℝ} (hk:1≤k) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) (hs:size Q t ω≤k):
    z k Q t ω∈Set.Icc 0 (1/100:ℝ) ∧ a k Q t ω∈Set.Icc 0 1 ∧
      z k Q t ω≤a k Q t ω/100 ∧ a k Q t ω/100-z k Q t ω≤4*cb*dp/ell k := by
  have h:=ActualParameters.beta_bounds hk hs positive.1.le
  have he:=ActualParameters.held_error positive.2.2.2.2.2.2.2.2.1 hk positive.1.le Q t ω
  have hell:=ell_ge_one hk
  have herr:4*cb*dp/ell k≤4*cb*dp:=by
    apply (div_le_iff₀ (ell_pos hk)).mpr
    have hp:0≤4*cb*dp:=by norm_num [cb,dp,lb]
    nlinarith
  have hc:10000*cb+4*cb*dp≤1/100:=small.2.2.2.1
  unfold z a ell at *
  constructor
  · constructor <;> nlinarith [he.1,he.2,h.1,h.2]
  · refine ⟨?_,?_,?_⟩
    · constructor <;> nlinarith [he.1,he.2,h.1,h.2]
    · linarith [he.1]
    · linarith [he.2]

lemma scalar_errors {k:ℝ} (hk:1≤k):
    0<rho/ell k ∧ 0<lb/ell k ∧ lb/ell k≤1/4 ∧
    rho/ell k+4*cb*dp/ell k≤(lb/ell k)/4 ∧
    4*(lb/ell k)≤(cg/ell k)/96 ∧ 4*(lb/ell k)≤eb/ell k := by
  have hel:=ell_pos hk
  have he1:=ell_ge_one hk
  have hl:0<lb:=by norm_num [lb,cb]
  have hr:0<rho:=by norm_num [rho,lb,cb]
  have hvals:=small
  refine ⟨div_pos hr hel,div_pos hl hel,?_,?_,?_,?_⟩
  · apply (div_le_iff₀ hel).mpr
    have hh:lb≤1/4:=hvals.2.2.2.2.1
    nlinarith
  · rw [←add_div,div_right_comm]
    exact div_le_div_of_nonneg_right hvals.2.2.2.2.2.1 hel.le
  · rw [←mul_div_assoc,div_right_comm]
    exact (div_le_div_iff_of_pos_right hel).mpr hvals.2.2.2.2.2.2.1
  · rw [←mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hel).mpr hvals.2.2.2.2.2.2.2.1

lemma regular_bounds {k:ℝ} (hk:1≤k) (Q P:R→FilteredRanks w) (t:ℕ) (ω:Ω)
    (hs:size Q t ω≤k) (hg:cg/ell k≤z k P t ω-z k Q t ω) :
    TrackedCaps.flex P (z k P t ω) t ω≤flexCap k Q P false t ω ∧
      flexCap k Q P false t ω≤TrackedCaps.flex P (z k Q t ω) t ω := by
  have hp:=ranges hk Q t ω hs
  have he:=scalar_errors hk
  have hgap:0≤cg/ell k:=div_nonneg (by norm_num [cg,cb]) (ell_pos hk).le
  have hzz:z k Q t ω≤z k P t ω:=by linarith
  have hε:0≤4*cb*dp/ell k:=div_nonneg (by norm_num [cb,dp,lb]) (ell_pos hk).le
  exact (TrackedCaps.scaled_bounds P he.1 hp.2.1 hp.1 hp.2.2.1 hp.2.2.2 hε
    he.2.1 he.2.2.1 he.2.2.2.1 he.2.2.2.2.1 he.2.2.2.2.2 hzz
    (div_le_div_of_nonneg_right hg (by norm_num)) t ω).1

lemma dominant_bounds {k:ℝ} (hk:1≤k) (Q P:R→FilteredRanks w) (t:ℕ) (ω:Ω)
    (hs:size Q t ω≤k) :
    TrackedCaps.flex P (z k Q t ω) t ω≤flexCap k Q P true t ω ∧
      flexCap k Q P true t ω≤(1+eb/ell k)*TrackedCaps.flex P (z k Q t ω) t ω := by
  have hp:=ranges hk Q t ω hs
  have he:=scalar_errors hk
  have hF:=TrackedCaps.flex_nonneg P hp.1 t ω
  have herror:=TrackedCaps.estimate_error P he.1 hp.2.1 hp.1 hp.2.2.1 hp.2.2.2 t ω
  have hε:0≤4*cb*dp/ell k:=div_nonneg (by norm_num [cb,dp,lb]) (ell_pos hk).le
  have hfc:0≤(1-4*(lb/ell k))*TrackedCaps.flex P (z k Q t ω) t ω:=
    mul_nonneg (by linarith [he.2.2.1]) hF
  exact (FineCaps.cap_scaling hF herror (add_nonneg he.1.le hε) he.2.1 he.2.2.1 he.2.2.2.1
    le_rfl he.2.2.2.2.2 hfc).2

end KServer.ActualCaps

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCaps
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile CoarseParameters LocalConstants
variable {Ω R:Type} [Fintype Ω] [Fintype R] {w:Ω→ℝ}

lemma estimate_nonneg {ξ a:ℝ} (ha:a∈Set.Icc 0 1) (P:R→FilteredRanks w) (t:ℕ) (ω:Ω) :
    0≤TrackedCaps.estimate P ξ a t ω := by
  unfold TrackedCaps.estimate
  apply sum_nonneg
  intro r _
  split_ifs
  · rfl
  · exact (FineCaps.interpolated_range ha (P r) t ω).1

lemma flexCap_nonneg {k:ℝ} (hk:1≤k) (Q P:R→FilteredRanks w) (d:Bool) (t:ℕ) (ω:Ω)
    (hs:size Q t ω≤k) : 0≤flexCap k Q P d t ω := by
  have he:=scalar_errors hk
  have ha:=(ranges hk Q t ω hs).2.1
  unfold flexCap
  apply mul_nonneg _ (estimate_nonneg ha P t ω)
  cases d <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linarith [he.2.1,he.2.2.1]

lemma flexCap_upper {k:ℝ} (hk:1≤k) (Q P:R→FilteredRanks w) (d:Bool) (t:ℕ) (ω:Ω)
    (hs:size Q t ω≤k) : flexCap k Q P d t ω≤2*TrackedCaps.flex P (z k Q t ω) t ω := by
  have he:=scalar_errors hk
  have hh:=dominant_bounds hk Q P t ω hs
  have hz:=(ranges hk Q t ω hs).1
  have hf:=TrackedCaps.flex_nonneg P hz t ω
  have hb:eb/ell k≤1:=by
    apply (div_le_iff₀ (ell_pos hk)).mpr
    have hb:eb≤1:=by norm_num [eb,cb]
    linarith [ell_ge_one hk]
  have hu:(1+eb/ell k)*TrackedCaps.flex P (z k Q t ω) t ω≤2*TrackedCaps.flex P (z k Q t ω) t ω:=by
    have hm:=mul_le_mul_of_nonneg_right hb hf
    nlinarith
  apply le_trans _ (hh.2.trans hu)
  cases d with
  | true=>rfl
  | false=>
    unfold flexCap
    simp only [Bool.false_eq_true,ite_false,ite_true]
    exact mul_le_mul_of_nonneg_right (by linarith [he.2.1]) (estimate_nonneg (ranges hk Q t ω hs).2.1 P t ω)

lemma cap_bounds {k:ℝ} (hk:1≤k) (Q P:R→FilteredRanks w) (d:Bool) (t:ℕ) (ω:Ω)
    (hs:size Q t ω≤k) : 0≤cap k Q P d t ω ∧ cap k Q P d t ω≤72*size P t ω := by
  have hn:=TrackedCaps.count_nonneg P t ω
  have hf:=flexCap_nonneg hk Q P d t ω hs
  have hu:=flexCap_upper hk Q P d t ω hs
  have hm:=TrackedCaps.domination P (ranges hk Q t ω hs).1 t ω
  dsimp [cap]
  constructor <;> linarith

lemma inactive_cap {δ k:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k)
    (Q P:R→FilteredRanks w) (d:Bool) (t:ℕ) (ω:Ω) (hs:size Q t ω≤k)
    (hi:¬0<(active cutoff δ P ω t).value) : cap k Q P d t ω=0 := by
  have ha:=(ranges hk Q t ω hs).2.1
  have hp:0<rho/ell k:=(scalar_errors hk).1
  have hcount:TrackedCaps.count P t ω=0:=by
    apply sum_eq_zero
    intro r _
    simp only [inactive_flag_false hδ hδu P hi r,Bool.false_eq_true,ite_false]
  have he:TrackedCaps.estimate P (rho/ell k) (a k Q t ω) t ω=0:=by
    apply sum_eq_zero
    intro r _
    rw [inactive_flag_false hδ hδu P hi r]
    simp only [Bool.false_eq_true,ite_false]
    have h:=FineCaps.interpolated_accuracy hp ha (P r) t ω
    have hz:=rank_cutoff (a k Q t ω/100) (inactive_rank_cutoff hδ hδu P hi r).le
    rw [hz,sub_zero,mul_zero] at h
    exact abs_nonpos_iff.mp h
  simp only [cap,flexCap,hcount,he,mul_zero,add_zero]

lemma held_beta_bounds {k:ℝ} (hk:1≤k) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω)
    (hs:size Q t ω≤k) :
    3≤upperBeta k cutoff cb (ell k) dp (parent cutoff dp Q t ω) ∧
    upperBeta k cutoff cb (ell k) dp (parent cutoff dp Q t ω)≤301/100 := by
  have hh:=(ranges hk Q t ω hs).2.1
  unfold a at hh
  constructor <;> linarith [hh.1,hh.2]

end KServer.ActualCaps

end


/-! Binding the local numerical choices to the literal star processes. The
only input relation is conservation/superadditivity of the parent's rank size. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualStar
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule LocalConstants
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def key (Q:R→FilteredRanks w) : ℕ→Ω→ℝ := parent cutoff dp Q

def b (k:ℝ) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  CoarseParameters.upperBeta k cutoff cb (ActualCaps.ell k) dp (key Q t ω)

def β (k:ℝ) (P:R→FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=3+ActualCaps.z k P t ω

def h (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) (i:J):ℝ:=
  weight ds (vector cutoff ds P ω) (fun s=>key Q s ω) t i

def active (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω):Finset J:=activeSet (vector cutoff ds P ω t)
def mark (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):Option J:=
  StarSide.mark ds P (key Q) t ω

def α (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) : ℕ→Ω→J→ℝ:=
  StarSimplex.proportion (δ:=ds) (by norm_num [ds]) (by norm_num [ds]) C (ActualCaps.ell k) ct P (key Q)

lemma h_nonneg (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) (i:J):0≤h P Q t ω i:=
  weight_nonneg ds _ _ (vector_nonneg cutoff ds P ω) t i
lemma h_one (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) (i:J)
    (hi:mark P Q t ω≠some i):1≤h P Q t ω i:=
  weight_regular_one ds _ _ t i hi
lemma h_upper {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω) (i:J):
    h P Q t ω i≤20002*ActualCaps.ell k:=
  weight_upper (by norm_num [ds]) (by norm_num [ds]) hk _ _ (vector_nonneg cutoff ds P ω)
    (fun s=>vector_total (by norm_num [ds]) (by norm_num [ds]) P s ω (hs s ω))
    (fun s j hj=>vector_floor (by norm_num [ds]) (by norm_num [ds]) P s ω j hj) t i
lemma beta_range {k:ℝ} (hk:1≤k) (P:R→FilteredRanks w) (t:ℕ) (ω:Ω) (hs:size P t ω≤k):
    3≤β k P t ω ∧ β k P t ω≤4 := by
  have hr:=(ActualCaps.ranges hk P t ω hs).1
  unfold β
  constructor <;> linarith [hr.1,hr.2]
lemma b_range {k:ℝ} (hk:1≤k) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) (hs:size Q t ω≤k):
    3≤b k Q t ω ∧ b k Q t ω≤4 := by
  have hr:=ActualCaps.held_beta_bounds hk Q t ω hs
  exact ⟨hr.1,hr.2.trans (by norm_num)⟩
lemma b_error {k:ℝ} (hk:1≤k) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):
    β k Q t ω≤b k Q t ω ∧ b k Q t ω-β k Q t ω≤4*cb*dp/ActualCaps.ell k := by
  have hh:=ActualParameters.held_error (δ:=dp) (cb:=cb) (by norm_num [dp,lb,cb]) hk (by norm_num [cb]) Q t ω
  dsimp only [β,ActualCaps.z,b,key,ActualCaps.ell]
  constructor <;> linarith [hh.1,hh.2]
lemma parameter_gap {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (i:J) (hi:i∈active P t ω):
    cg*h P Q t ω i/ActualCaps.ell k≤β k (P i) t ω-β k Q t ω := by
  have hh:=ActualParameters.gap (δ:=ds) (cb:=cb) (by norm_num [ds]) (by norm_num [ds]) hk (by norm_num [cb])
    P (key Q) (size Q) hs t ω i hi
  dsimp only [β,ActualCaps.z,ActualCaps.ell,h,cg]
  linarith only [hh]
lemma α_mem (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):
    α k P Q t ω∈ChangingDomains.simplex (active P t ω):=
  StarSimplex.proportion_mem _ _ _ _ _ _ _ _ _
lemma α_feasible {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω) (i:J):
    (∑ j,TrackedCaps.core (P j) t ω)*α k P Q t ω i≤
      (1+ct*h P Q t ω i/ActualCaps.ell k)*TrackedCaps.core (P i) t ω:=
  StarSimplex.feasible (δ:=ds) (by norm_num [ds]) (by norm_num [ds]) positive.2.2.2.2.1 positive.2.2.1
    small.1 small.2.2.1 hk P (key Q) hs t ω i
end KServer.ActualStar

end


/-! Scalar constant choices used when the genuine minimizer proportions are
converted to allocations. All constants are the fixed absolute choices, not
parameters fitted to the finite law. -/
noncomputable section
namespace KServer.OutputConstants
open LocalConstants

lemma eta_nonneg {h ell:ℝ} (hh:0≤h) (hel:0<ell) : 0≤ct*h/ell := by
  exact div_nonneg (mul_nonneg positive.2.2.1.le hh) hel.le
lemma eta_upper {h ell:ℝ} (hh:h≤20002*ell) (hel:0<ell) : ct*h/ell≤1 := by
  apply (div_le_iff₀ hel).mpr
  have h1:=mul_le_mul_of_nonneg_left hh positive.2.2.1.le
  have h2:=mul_le_mul_of_nonneg_right small.1 hel.le
  nlinarith
lemma beta_eta {β h ell:ℝ} (hβ:β≤4) (hh:0≤h) (hel:0<ell) :
    β*(ct*h/ell)≤(cg*h/ell)/2 := by
  have hn:=div_nonneg hh hel.le
  have hc:4*ct≤cg/2:=by norm_num [ct,cg,cb]
  have h1:=mul_le_mul_of_nonneg_right hβ (eta_nonneg hh hel)
  have h2:=mul_le_mul_of_nonneg_right hc hn
  calc
    β*(ct*h/ell)≤4*(ct*h/ell):=h1
    _≤(cg*h/ell)/2:=by simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h2
lemma dominant_room {β βi h ell:ℝ} (hβ:β≤4) (hh:0≤h) (hel:0<ell)
    (hg:cg*h/ell≤βi-β) : β*(1+ct*h/ell)≤βi := by
  have hη:=beta_eta hβ hh hel
  have hn:0≤cg*h/ell:=div_nonneg (mul_nonneg positive.2.1.le hh) hel.le
  nlinarith
lemma regular_error {S T e h ell:ℝ} (hS:0≤S) (hT:T≤4*S)
    (hh:1≤h) (hel:0<ell) (he:e≤eb/ell*T) : 4*e≤(cg*h/ell)*S := by
  have hb:0≤eb/ell:=div_nonneg positive.2.2.2.2.2.1.le hel.le
  have h1:=mul_le_mul_of_nonneg_left hT hb
  have hc:16*eb≤cg:=by norm_num [eb,cg,cb]
  have h2:=mul_le_mul_of_nonneg_left hh positive.2.1.le
  rw [mul_one] at h2
  have h3:16*eb/ell≤cg*h/ell:=div_le_div_of_nonneg_right (hc.trans h2) hel.le
  have h4:=mul_le_mul_of_nonneg_right h3 hS
  simp only [div_eq_mul_inv] at he h1 h4 ⊢
  nlinarith only [he,h1,h4]
lemma regular_room {S T e β βi h ell:ℝ} (hS:0≤S) (he:0≤e) (hT:T≤4*S)
    (hh:1≤h) (hhu:h≤20002*ell) (hel:0<ell) (hβ:β≤4)
    (herr:e≤eb/ell*T) (hg:cg*h/ell≤βi-β) :
    (β*S+e)*(1+ct*h/ell)≤βi*S := by
  exact OutputDynamics.regular_parameter_room hS he (eta_upper hhu hel)
    (by linarith) (beta_eta hβ (by linarith) hel) (regular_error hS hT hh hel herr)
lemma side_room {β βi b h ell:ℝ} (hh:1≤h) (hel:0<ell)
    (hb:b-β≤4*cb*dp/ell) (hg:cg*h/ell≤βi-β) : b+cw*h/ell≤βi := by
  have hc:4*cb*dp+cw≤cg:=by norm_num [cb,dp,lb,cw,cg]
  have hcn:0≤4*cb*dp:=by norm_num [cb,dp,lb]
  have h1:=mul_le_mul_of_nonneg_left hh hcn
  have h2:=mul_le_mul_of_nonneg_right hc (show 0≤h by linarith)
  have h3:4*cb*dp/ell+cw*h/ell≤cg*h/ell:=by
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ hel.le
    nlinarith only [h1,h2]
  linarith
lemma residual_room {u T D ell:ℝ} (hu:0≤u) (hT:0≤T) (hD:D≤2*T) (hel:0<ell) :
    D*(128*cw*u/ell)≤(cg*u/ell)/96*T := by
  have hc:256*cw≤cg/96:=by norm_num [cw,cg,cb]
  have h0:0≤128*cw*u/ell:=by have hcw:=positive.2.2.2.1; positivity
  have h1:=mul_le_mul_of_nonneg_right hD h0
  have h2:=mul_le_mul_of_nonneg_right hc (div_nonneg hu hel.le)
  have h3:=mul_le_mul_of_nonneg_right h2 hT
  simp only [div_eq_mul_inv] at h1 h3 ⊢
  nlinarith only [h1,h3]
end KServer.OutputConstants

end


/-! The actual cap vector, lower envelopes, and single dominant error used by
§05. No aggregate cap or parameter inequalities are assumed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def B (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω) : J→ℝ := fun i=>TrackedCaps.core (P i) t ω
def n (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω) : J→ℝ := fun i=>TrackedCaps.count (P i) t ω
def S (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=∑ i,B P t ω i
def f (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) : J→ℝ :=
  fun i=>TrackedCaps.flex (P i) (ActualCaps.z k Q t ω) t ω
def fc (k:ℝ) (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω) : J→ℝ :=
  fun i=>TrackedCaps.flex (P i) (ActualCaps.z k (P i) t ω) t ω
def flexcap (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) : J→ℝ :=
  fun i=>ActualCaps.flexCap k Q (P i) (decide (mark P Q t ω=some i)) t ω
def d (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) : J→ℝ :=
  fun i=>n P t ω i+flexcap k P Q t ω i
def lower (k:ℝ) (P:R→FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  ∑ r,rank (ActualCaps.z k P t ω) ((P r).p t ω)
def T (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  match mark P Q t ω with | none=>0 | some o=>f k P Q t ω o
def e (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  match mark P Q t ω with | none=>0 | some o=>flexcap k P Q t ω o-f k P Q t ω o
def D (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) : ℕ→Ω→ℝ:=
  StarSide.scale ds P (key Q)

lemma S_nonneg (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω):0≤S P t ω:=
  sum_nonneg fun i _=>TrackedCaps.core_nonneg (P i) t ω
lemma D_nonneg (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):0≤D P Q t ω:=
  StarSide.scale_nonneg ds P (key Q) t ω
lemma mark_active (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω)
    {o:J} (ho:mark P Q t ω=some o):o∈ActualStar.active P t ω:=
  marked_active _ _ (vector_nonneg cutoff ds P ω) t ho
lemma inactive (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω) {i:J}
    (hi:i∉ActualStar.active P t ω):¬0<(CoarseProcess.active cutoff ds (P i) ω t).value:=by
  exact fun hh=>hi ((AllocationSchedule.mem_activeSet _ _).mpr hh)
lemma inactive_lower (k:ℝ) (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω) {i:J}
    (hi:i∉ActualStar.active P t ω):lower k (P i) t ω=0:=
  inactive_lower_zero (by norm_num [ds]) (by norm_num [ds]) (P i) (inactive P t ω hi) _
lemma inactive_f (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) {i:J}
    (hi:i∉ActualStar.active P t ω):f k P Q t ω i=0:=by
  apply sum_eq_zero
  intro r _
  rw [inactive_flag_false (by norm_num [ds]) (by norm_num [ds]) (P i) (inactive P t ω hi) r]
  simp only [Bool.false_eq_true,ite_false]
  exact rank_cutoff _ (inactive_rank_cutoff (by norm_num [ds]) (by norm_num [ds]) (P i) (inactive P t ω hi) r).le
omit [Fintype J] in
lemma lower_decomposition (k:ℝ) (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω) (i:J):
    lower k (P i) t ω=n P t ω i-β k (P i) t ω*B P t ω i+fc k P t ω i:=
  TrackedCaps.decomposition (P i) _ t ω
lemma child_size (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω) (i:J):
    size (P i) t ω≤∑ j,size (P j) t ω:=
  single_le_sum (fun j _=>size_nonneg (P j) t ω) (mem_univ i)
lemma lower_nonneg {k:ℝ} (hk:1≤k) (P:R→FilteredRanks w) (t:ℕ) (ω:Ω) (hs:size P t ω≤k):
    0≤lower k P t ω:=sum_nonneg fun _ _=>rank_nonneg (ActualCaps.ranges hk P t ω hs).1 _
lemma d_bounds {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (hs:size Q t ω≤k) (i:J):0≤d k P Q t ω i ∧ d k P Q t ω i≤72*size (P i) t ω:=
  ActualCaps.cap_bounds hk Q (P i) _ t ω hs
lemma inactive_d {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (hs:size Q t ω≤k) {i:J} (hi:i∉ActualStar.active P t ω):d k P Q t ω i=0:=
  ActualCaps.inactive_cap (by norm_num [ds]) (by norm_num [ds]) hk Q (P i) _ t ω hs (inactive P t ω hi)

lemma regular_caps {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤k)
    (i:J) (hi:i∈ActualStar.active P t ω) (ho:mark P Q t ω≠some i):
    fc k P t ω i≤flexcap k P Q t ω i ∧ flexcap k P Q t ω i≤f k P Q t ω i:=by
  have hg:=parameter_gap hk P Q hs t ω i hi
  have hh:=h_one P Q t ω i ho
  have hcg:0≤cg/ActualCaps.ell k:=div_nonneg positive.2.1.le (ActualCaps.ell_pos hk).le
  have hmul:=mul_le_mul_of_nonneg_left hh hcg
  have hgap:cg/ActualCaps.ell k≤ActualCaps.z k (P i) t ω-ActualCaps.z k Q t ω:=by
    dsimp only [β] at hg
    simp only [div_eq_mul_inv] at hg hmul ⊢
    nlinarith only [hg,hmul]
  simpa only [fc,flexcap,f,decide_eq_false ho] using ActualCaps.regular_bounds hk Q (P i) t ω hq hgap
lemma dominant_caps {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (hq:size Q t ω≤k) {o:J} (ho:mark P Q t ω=some o):
    f k P Q t ω o≤flexcap k P Q t ω o ∧
      flexcap k P Q t ω o≤(1+eb/ActualCaps.ell k)*f k P Q t ω o:=by
  simpa only [f,flexcap,ho,decide_true] using ActualCaps.dominant_bounds hk Q (P o) t ω hq
lemma T_nonneg {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (hq:size Q t ω≤k):0≤T k P Q t ω:=by
  unfold T
  split
  · rfl
  · exact TrackedCaps.flex_nonneg _ (ActualCaps.ranges hk Q t ω hq).1 t ω
lemma e_bounds {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (hq:size Q t ω≤k):0≤e k P Q t ω ∧ e k P Q t ω≤eb/ActualCaps.ell k*T k P Q t ω:=by
  cases ho:mark P Q t ω with
  | none=>simp only [e,T,ho,mul_zero,le_refl,and_self]
  | some o=>
    have hh:=dominant_caps hk P Q t ω hq ho
    simp only [e,T,ho]
    constructor <;> nlinarith [hh.1,hh.2]
lemma DT_compare {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (hq:size Q t ω≤k):T k P Q t ω/2≤D P Q t ω ∧ D P Q t ω≤2*T k P Q t ω:=by
  have hmark:StarSide.mark ds P (key Q) t ω=mark P Q t ω:=rfl
  cases ho:mark P Q t ω with
  | none=>simp only [D,StarSide.scale,hmark,ho,T,zero_div,mul_zero,le_refl,and_self]
  | some o=>
    have hh:=CoarseFineBridge.compare (δ:=ds) (by norm_num [ds]) (by norm_num [ds])
      (ActualCaps.ranges hk Q t ω hq).1 (P o) t ω
    simp only [D,StarSide.scale,hmark,ho,T,f]
    constructor <;> linarith [hh.1,hh.2]
end KServer.ActualOutput

end

end OAI
