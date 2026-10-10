import Mathlib
import OAI.Combinatorics.KServer.Coarse
import OAI.Combinatorics.KServer.OutputDynamics

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AllocationSchedule
local instance (p : Prop) : Decidable p := Classical.propDecidable p
open EpochSchedule
variable {J K : Type} [Fintype J] [DecidableEq J]

/-- Active domain and literal held epoch mass, rather than a bound supplied to
an allocation interface. -/
def activeSet (x : J → ℝ) : Finset J := univ.filter fun i => 0<x i

def mass (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) : ℝ := total (run x key t).reference

def sideHeld (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K) : ℕ → ℝ :=
  CoarseSide.held δ (CoarseSide.sideInput x key) (CoarseSide.epochReset x key)

def sideRatio (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) : ℝ :=
  sideHeld δ x key t/mass x key t

def weight (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) (i : J) : ℝ :=
  if dominant (run x key t)=some i then sideRatio δ x key t
  else HeldWeights.regular (mass x key t) (x t i)

omit [DecidableEq J] in
lemma mem_activeSet (x : J → ℝ) (i : J) : i∈activeSet x ↔ 0<x i := by simp [activeSet]

omit [DecidableEq J] in
lemma sum_activeSet {x : J → ℝ} (hx : ∀ i, 0 ≤ x i) : (∑ i∈activeSet x,x i)=total x := by
  apply sum_subset (by simp [activeSet])
  intro i _ hi
  have hh : ¬0<x i := by simpa [activeSet] using hi
  exact le_antisymm (le_of_not_gt hh) (hx i)

omit [DecidableEq J] in
lemma mass_nonneg (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) :
    0 ≤ mass x key t := total_nonneg (run_valid x key hx t).1

omit [DecidableEq J] in
lemma mass_accuracy (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) :
    (99/100:ℝ)*mass x key t ≤ total (x t) ∧ total (x t) ≤ (101/100:ℝ)*mass x key t :=
  valid_total (run_valid x key hx t)

omit [DecidableEq J] in
lemma dominant_mass_pos {s : State J} {o : J} (ho : dominant s=some o) :
    0<total s.reference := by
  unfold dominant at ho
  split_ifs at ho with h
  exact h.choose_spec.1

omit [DecidableEq J] in
lemma marked_active (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i)
    (t : ℕ) {o : J} (ho : dominant (run x key t)=some o) : o∈activeSet (x t) := by
  rw [mem_activeSet]
  have hA := dominant_mass_pos ho
  have hm := dominant_large (run_valid x key hx t) ho
  linarith

lemma side_eq_erase (x : J → ℝ) (s : State J) {o : J} (ho : dominant s=some o) :
    CoarseSide.side x s=∑ i∈univ.erase o,x i := by
  unfold CoarseSide.side
  simp only [ho,Option.isSome_some,ite_true,Option.some.injEq]
  rw [sum_ite]
  simp only [sum_const_zero,zero_add]
  congr 1
  ext i
  simp [eq_comm]

omit [DecidableEq J] in
lemma side_held_nonneg (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K)
    (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) : 0 ≤ sideHeld δ x key t :=
  CoarseSide.held_nonneg δ _ _ (fun t => CoarseSide.side_nonneg (hx t) _) t

omit [DecidableEq J] in
lemma side_held_accuracy {δ : ℝ} (hδ : 0<δ) (x : ℕ → J → ℝ) (key : ℕ → K)
    (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) :
    CoarseSide.sideInput x key t ≤ (1+δ)*sideHeld δ x key t ∧
      sideHeld δ x key t ≤ (1+δ)*CoarseSide.sideInput x key t :=
  CoarseSide.held_accuracy hδ _ _ (fun t => CoarseSide.side_nonneg (hx t) _) t

omit [DecidableEq J] in
lemma side_ratio_nonneg (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K)
    (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) : 0 ≤ sideRatio δ x key t :=
  div_nonneg (side_held_nonneg δ x key hx t) (mass_nonneg x key hx t)

lemma side_ratio_upper {δ : ℝ} (hδ : 0<δ) (hδu : δ ≤ 1/1000)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i)
    (t : ℕ) {o : J} (ho : dominant (run x key t)=some o) : sideRatio δ x key t ≤ 1/4 := by
  have hA := dominant_mass_pos ho
  have hs := side_total (run_valid x key hx t) ho
  have hU := (side_held_accuracy hδ x key hx t).2
  change sideHeld δ x key t ≤ (1+δ)*CoarseSide.side (x t) (run x key t) at hU
  rw [side_eq_erase _ _ ho] at hU
  have he : (1+δ)*((16/100:ℝ)*mass x key t)  ≤  mass x key t/4 := by
    dsimp [mass]
    nlinarith [mul_nonneg hA.le (show 0 ≤ 1/1000-δ by linarith)]
  apply (div_le_iff₀ hA).mpr
  exact (hU.trans (mul_le_mul_of_nonneg_left hs (by linarith))).trans (by simpa [mass,div_eq_mul_inv,mul_comm] using he)

omit [DecidableEq J] in
lemma side_zero_iff {δ : ℝ} (hδ : 0<δ) (x : ℕ → J → ℝ) (key : ℕ → K)
    (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) {o : J} (ho : dominant (run x key t)=some o) :
    sideRatio δ x key t=0 ↔ CoarseSide.sideInput x key t=0 := by
  have hA := dominant_mass_pos ho
  have hU := side_held_accuracy hδ x key hx t
  have hN := side_held_nonneg δ x key hx t
  have hT := CoarseSide.side_nonneg (hx t) (run x key t)
  change 0 ≤ CoarseSide.sideInput x key t at hT
  rw [sideRatio,div_eq_zero_iff]
  have hm : mass x key t≠0 := ne_of_gt hA
  simp only [hm,or_false]
  constructor <;> intro hz
  · rw [hz,mul_zero] at hU
    exact le_antisymm hU.1 hT
  · rw [hz,mul_zero] at hU
    exact le_antisymm hU.2 hN

lemma marked_zero_singleton {δ : ℝ} (hδ : 0<δ) (x : ℕ → J → ℝ) (key : ℕ → K)
    (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) {o : J} (ho : dominant (run x key t)=some o)
    (hu : sideRatio δ x key t=0) : activeSet (x t)={o} := by
  have hz := (side_zero_iff hδ x key hx t ho).mp hu
  change CoarseSide.side (x t) (run x key t)=0 at hz
  rw [side_eq_erase _ _ ho] at hz
  ext i
  simp only [mem_singleton]
  constructor
  · intro hi
    by_contra hn
    have hb := single_le_sum (fun j _ => hx t j) (show i∈univ.erase o by simp [hn])
    rw [hz] at hb
    exact (not_lt_of_ge hb) ((mem_activeSet _ _).mp hi)
  · intro hi
    subst i
    exact marked_active x key hx t ho

/-- On the true active sides, held logarithmic weights satisfy the special
marked profile condition used in the decrement-gap argument. -/
lemma weight_side_lower {δ : ℝ} (hδ : 0<δ) (hδu : δ ≤ 1/1000)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i)
    (t : ℕ) {o i : J} (ho : dominant (run x key t)=some o)
    (hi : i∈activeSet (x t)) (hio : i≠o) (hu : 0<sideRatio δ x key t) :
    (1/2:ℝ)*(1+Real.log (1/sideRatio δ x key t)) ≤ weight δ x key t i := by
  have hA := dominant_mass_pos ho
  have hf : dominant (run x key t)≠some i := by rw [ho]; simpa [eq_comm] using hio
  rw [weight,ite_eq_right hf]
  apply HeldWeights.side_lower hA ((mem_activeSet _ _).mp hi) hu (side_ratio_upper hδ hδu x key hx t ho)
  have hb := single_le_sum (fun j _ => hx t j) (show i∈univ.erase o by simp [hio])
  have hU := (side_held_accuracy hδ x key hx t).1
  change CoarseSide.side (x t) (run x key t) ≤ (1+δ)*sideHeld δ x key t at hU
  rw [side_eq_erase _ _ ho] at hU
  have hN := side_held_nonneg δ x key hx t
  have he : 2*sideRatio δ x key t*mass x key t=2*sideHeld δ x key t := by
    unfold sideRatio
    have hm : mass x key t≠0 := ne_of_gt hA
    field_simp [hm]
  change x t i ≤ 2*sideRatio δ x key t*mass x key t
  rw [he]
  nlinarith [mul_nonneg hN (show 0 ≤ 1-δ by linarith)]

end KServer.AllocationSchedule

namespace KServer.AllocationSchedule
local instance (p : Prop) : Decidable p := Classical.propDecidable p
open EpochSchedule
variable {J K : Type} [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
lemma mass_upper (x : ℕ → J → ℝ) (key : ℕ → K) {b : ℝ}
    (hb : ∀ t, total (x t) ≤ b) (t : ℕ) : mass x key t ≤ b := by
  induction t with
  | zero => exact hb 0
  | succ t ih =>
    change total (update _ _ _ _ _).reference ≤ b
    unfold update
    split_ifs
    · exact hb (t+1)
    · exact ih

lemma regular_weight (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) (i : J)
    (hi : dominant (run x key t)≠some i) :
    weight δ x key t i=HeldWeights.regular (mass x key t) (x t i) := ite_eq_right hi

lemma marked_weight (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) (i : J)
    (hi : dominant (run x key t)=some i) :
    weight δ x key t i=sideRatio δ x key t := ite_eq_left hi

lemma weight_regular_one (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) (i : J)
    (hi : dominant (run x key t)≠some i) : 1 ≤ weight δ x key t i := by
  rw [regular_weight δ x key t i hi]
  exact HeldWeights.regular_one _ _

lemma weight_nonneg (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K)
    (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) (i : J) : 0 ≤ weight δ x key t i := by
  unfold weight
  split_ifs
  · exact side_ratio_nonneg δ x key hx t
  · exact (by norm_num : (0:ℝ) ≤ 1).trans (HeldWeights.regular_one _ _)

lemma weight_upper {δ k : ℝ} (hδ : 0<δ) (hδu : δ ≤ 1/1000) (hk : 1 ≤ k)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i)
    (hxk : ∀ t, total (x t) ≤ (11/10)*k)
    (hfloor : ∀ t i, 0<x t i → (9/100000:ℝ) ≤ x t i) (t : ℕ) (i : J) :
    weight δ x key t i ≤ 20002*(1+Real.log (k+1)) := by
  have hl : 0 ≤ Real.log (k+1) := Real.log_nonneg (by linarith)
  by_cases ho : dominant (run x key t)=some i
  · rw [marked_weight δ x key t i ho]
    linarith [side_ratio_upper hδ hδu x key hx t ho]
  · rw [regular_weight δ x key t i ho]
    by_cases hi : 0<x t i
    · exact HeldWeights.regular_upper hk (mass_nonneg x key hx t) (mass_upper x key hxk t) (hfloor t i hi)
    · have hz : x t i=0 := le_antisymm (le_of_not_gt hi) (hx t i)
      simp only [HeldWeights.regular,hz,div_zero,Real.log_zero,max_self]
      linarith

lemma regular_exp_sum (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K)
    (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) (hA : 0 < mass x key t)
    (ho : dominant (run x key t)=none) :
    (∑ i∈activeSet (x t),Real.exp (-weight δ x key t i)) ≤ 2 := by
  have hw (i : J) : weight δ x key t i=HeldWeights.regular (mass x key t) (x t i) :=
    regular_weight δ x key t i (by simp [ho])
  simp_rw [hw]
  apply HeldWeights.exp_sum _ hA (fun i hi => (mem_activeSet _ _).mp hi)
  rw [sum_activeSet (hx t)]
  exact (mass_accuracy x key hx t).2

lemma side_exp_sum {δ : ℝ} (hδ : 0<δ) (hδu : δ ≤ 1/1000)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i)
    (t : ℕ) {o : J} (ho : dominant (run x key t)=some o) :
    (∑ i∈(activeSet (x t)).erase o, Real.exp (-weight δ x key t i)) ≤ 2*sideRatio δ x key t := by
  have hA := dominant_mass_pos ho
  have he : (∑ i∈(activeSet (x t)).erase o, Real.exp (-weight δ x key t i))=
      ∑ i∈(activeSet (x t)).erase o, Real.exp (-HeldWeights.regular (mass x key t) (x t i)) := by
    apply sum_congr rfl
    intro i hi
    rw [regular_weight δ x key t i (by rw [ho]; simpa [eq_comm] using (mem_erase.mp hi).1)]
  rw [he]
  apply HeldWeights.side_exp_sum _ hA (fun i hi => (mem_activeSet _ _).mp (mem_erase.mp hi).2)
  have hs : (∑ i∈(activeSet (x t)).erase o,x t i) ≤ ∑ i∈univ.erase o,x t i :=
    sum_le_sum_of_subset_of_nonneg (erase_subset_erase o (subset_univ _)) (fun i _ _ => hx t i)
  have hU := (side_held_accuracy hδ x key hx t).1
  change CoarseSide.side (x t) (run x key t) ≤ (1+δ)*sideHeld δ x key t at hU
  rw [side_eq_erase _ _ ho] at hU
  have hN := side_held_nonneg δ x key hx t
  nlinarith [mul_nonneg hN (show 0 ≤ 1-δ by linarith)]

/-- Epoch labels record the actual wholesale test. -/
def epoch (x : ℕ → J → ℝ) (key : ℕ → K) : ℕ → ℕ
  | 0 => 0
  | t+1 => if CoarseSide.epochReset x key t then epoch x key t+1 else epoch x key t

omit [DecidableEq J] in
lemma epoch_same_iff (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) :
    epoch x key t=epoch x key (t+1) ↔ ¬CoarseSide.epochReset x key t := by
  classical
  rw [epoch]
  split_ifs <;> simp_all

variable {R : Type} [Fintype R]

/-- Empty and genuinely side-free marked domains have the source's zero
potential. The dummy regular kernel is never evaluated by that potential. -/
def zeroData (A : Finset J) (flags : J → R → Bool) : SimplexFamilies.Data J R :=
  { SimplexFamilies.regular A flags (fun _ => 1) (fun _ => 0) (fun _ => le_rfl) with zeroPotential := true }

def data {δ : ℝ} (hδ : 0<δ) (hδu : δ ≤ 1/1000) (_C ell ct : ℝ)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i)
    (flags : ℕ → J → R → Bool) (t : ℕ) : SimplexFamilies.Data J R := by
  classical
  let A := activeSet (x t)
  let h := weight δ x key t
  exact if A.Nonempty then
    match ho : dominant (run x key t) with
    | none => SimplexFamilies.regular A (flags t) h (fun i => ct*h i/ell)
        (fun i => weight_regular_one δ x key t i (by simp [ho]))
    | some o => if hu : 0<sideRatio δ x key t then
        SimplexFamilies.marked A (flags t) o h (fun i => ct*h i/ell) (sideRatio δ x key t) hu
          (by linarith [side_ratio_upper hδ hδu x key hx t ho])
          (fun i hi => weight_regular_one δ x key t i (by rw [ho]; simpa [eq_comm] using hi))
      else zeroData A (flags t)
  else zeroData A (flags t)

omit [Fintype R] in
lemma data_active {δ : ℝ} (hδ : 0<δ) (hδu : δ ≤ 1/1000) (C ell ct : ℝ)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i)
    (flags : ℕ → J → R → Bool) (t : ℕ) :
    (data hδ hδu C ell ct x key hx flags t).active=activeSet (x t) := by
  unfold data
  dsimp only
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

omit [Fintype R] in
lemma data_flags {δ : ℝ} (hδ : 0<δ) (hδu : δ ≤ 1/1000) (C ell ct : ℝ)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i)
    (flags : ℕ → J → R → Bool) (t : ℕ) :
    (data hδ hδu C ell ct x key hx flags t).flags=flags t := by
  unfold data
  dsimp only
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

end KServer.AllocationSchedule

end

/-! Binding the literal filtered-rank size schedule to the live child domain.
In particular no core or positive lower-envelope rank is silently discarded
when the coarse active state turns off. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.StarProfile
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch AllocationSchedule
variable {Ω J R : Type} [Fintype Ω] [Fintype J] [Fintype R] {w : Ω → ℝ}

def cutoff : ℝ := 1/10000

lemma live_iff {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    0<(active cutoff δ P ω t).value ↔ (active cutoff δ P ω t).active=true := by
  have hv:=active_valid cutoff δ P ω t
  have ha:=active_accuracy (by norm_num [cutoff] : 0<cutoff) hδ hδu P ω t
  constructor
  · intro h
    cases hh : (active cutoff δ P ω t).active with
    | false => have hz:=hv.2 hh; linarith
    | true => rfl
  · intro h
    obtain ⟨hl,_,hf⟩:=ha.1 h
    have hc : 0<cutoff := by norm_num [cutoff]
    nlinarith

lemma too_small_inactive {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : R → FilteredRanks w) {t : ℕ} {ω : Ω}
    (hn : ¬0<(active cutoff δ P ω t).value) : size P t ω<10*cutoff := by
  by_contra! h
  have ha:=(active_accuracy (by norm_num [cutoff] : 0<cutoff) hδ hδu P ω t).2 h
  exact hn ((live_iff hδ hδu P t ω).mpr ha)

lemma inactive_rank_cutoff {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : R → FilteredRanks w) {t : ℕ} {ω : Ω}
    (hn : ¬0<(active cutoff δ P ω t).value) (r : R) : sstar<(P r).p t ω := by
  have hs:=too_small_inactive hδ hδu P hn
  by_contra! h
  have hr:=CompatibleBounds.sizeRank_below_cutoff h
  have ht : sizeRank ((P r).p t ω)≤ size P t ω :=
    single_le_sum (fun a _=>sizeRank_nonneg ((P a).p t ω)) (mem_univ r)
  norm_num [cutoff] at hs
  linarith

lemma inactive_lower_zero {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : R → FilteredRanks w) {t : ℕ} {ω : Ω}
    (hn : ¬0<(active cutoff δ P ω t).value) (z : ℝ) :
    (∑ r,rank z ((P r).p t ω))=0 := by
  exact sum_eq_zero fun r _=>rank_cutoff z (inactive_rank_cutoff hδ hδu P hn r).le

lemma inactive_flag_false {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : R → FilteredRanks w) {t : ℕ} {ω : Ω}
    (hn : ¬0<(active cutoff δ P ω t).value) (r : R) : CoreFlags.flag (P r) t ω=false := by
  cases hf : CoreFlags.flag (P r) t ω with
  | false => rfl
  | true =>
    have hl:=inactive_rank_cutoff hδ hδu P hn r
    have hu:=CoreFlags.core_upper (P r) hf
    norm_num [sstar] at hl
    linarith

omit [Fintype J] in
lemma vector_floor {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : J → R → FilteredRanks w) (t : ℕ) (ω : Ω) (i : J)
    (hi : 0<vector cutoff δ P ω t i) : (9/100000:ℝ)≤vector cutoff δ P ω t i := by
  have hl:=(live_iff hδ hδu (P i) t ω).mp hi
  obtain ⟨hb,_,hc⟩:=(active_accuracy (by norm_num [cutoff] : 0<cutoff) hδ hδu (P i) ω t).1 hl
  change (9/100000:ℝ)≤(active cutoff δ (P i) ω t).value
  norm_num [cutoff] at hc
  linarith

lemma vector_total {δ k : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : J → R → FilteredRanks w) (t : ℕ) (ω : Ω)
    (hk : (∑ i,size (P i) t ω)≤k) :
    EpochSchedule.total (vector cutoff δ P ω t)≤(11/10)*k := by
  calc _ ≤ ∑ i,(11/10:ℝ)*size (P i) t ω :=
        sum_le_sum fun i _=>value_bound (by norm_num [cutoff]) hδ hδu (P i) ω t
       _ = (11/10:ℝ)*(∑ i,size (P i) t ω) := (mul_sum _ _ _).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left hk (by norm_num)

lemma flags_supported {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : J → R → FilteredRanks w) (t : ℕ) (ω : Ω)
    (i : J) (hi : i∉activeSet (vector cutoff δ P ω t)) (r : R) :
    CoreFlags.flag (P i r) t ω=false :=
  inactive_flag_false hδ hδu (P i) (fun h=>hi ((mem_activeSet _ _).mpr h)) r

omit [Fintype J] in
lemma vector_adapted (δ : ℝ) (P : J → R → FilteredRanks w) (H : ℕ → Ω → ℕ)
    (hH : ∀ i r t ω,(P i r).history t ω=H t ω)
    (hr : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    (t : ℕ) (ω z : Ω) (he : H t ω=H t z) :
    vector cutoff δ P ω t=vector cutoff δ P z t := by
  funext i
  exact congrArg CoarseSchedule.State.value (active_adapted cutoff δ (P i) H (hH i) hr t ω z he)

lemma parent_adapted (c δ : ℝ) (P : R → FilteredRanks w) (H : ℕ → Ω → ℕ)
    (hH : ∀ r t ω,(P r).history t ω=H t ω)
    (hr : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    (t : ℕ) (ω z : Ω) (he : H t ω=H t z) : parent c δ P t ω=parent c δ P t z := by
  induction t with
  | zero => exact congrArg (max c) (estimate_adapted δ P H hH 0 ω z he)
  | succ t ih =>
    have hh:=estimate_adapted δ P H hH (t+1) ω z he
    have hp:=ih (hr t ω z he)
    change (if factorTest id δ (clipped c δ P (t+1) ω) (parent c δ P t ω)
      then clipped c δ P (t+1) ω else parent c δ P t ω)=_
    simp only [clipped,hh,hp]
    rfl

end KServer.StarProfile

end


/-! Feasibility of the literal held-size scheduler's minimizing simplex law,
including empty and side-free marked epochs. Constants are uniform in degree. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduledSimplex
attribute [local instance] Classical.propDecidable
open AllocationSchedule EpochSchedule SimplexFamilies AdaptiveAllocation
variable {J R K : Type} [Fintype J] [DecidableEq J] [Fintype R]

lemma singleton_feasible {o : J} {B a : J → ℝ}
    (hB : ∀ i,i≠o → B i=0) (ha : a∈ChangingDomains.simplex {o}) (i : J) :
    (∑ j,B j)*a i=B i := by
  classical
  have hs : (∑ j,B j)=B o := by
    apply sum_eq_single o
    · intro j _ hj; exact hB j hj
    · intro h; exact (h (mem_univ o)).elim
  rw [hs]
  by_cases hi : i=o
  · subst i
    have hsum : (∑ j,a j)=a o := by
      apply sum_eq_single o
      · intro j _ hj; exact ha.2.2 j (by simpa using hj)
      · intro h; exact (h (mem_univ o)).elim
    have hh : a o=1 := by simpa only [hsum,singleton_nonempty,ite_true] using ha.2.1
    rw [hh,mul_one]
  · rw [ha.2.2 i (by simpa [eq_comm] using hi),mul_zero,hB i hi]

omit [DecidableEq J] in
lemma nonempty_mass (x : ℕ → J → ℝ) (key : ℕ → K)
    (hx : ∀ t i,0≤x t i) (t : ℕ) (hn : (activeSet (x t)).Nonempty) :
    0 < mass x key t := by
  classical
  obtain ⟨i,hi⟩:=hn
  have hp: 0<x t i := (mem_activeSet _ _).mp hi
  have hs : x t i≤total (x t) := single_le_sum (fun j _=>hx t j) (mem_univ i)
  have hU: total (x t)≤(101/100:ℝ)*mass x key t := (mass_accuracy x key hx t).2
  linarith

lemma update_feasible {δ C ell ct : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (hC : 0<C) (hel : 0<ell) (hct : 0<ct) (hgap : 700<C*ct)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i,0≤x t i)
    (flags : ℕ → J → R → Bool) (t : ℕ)
    (hmax : ∀ i∈activeSet (x t),ct*weight δ x key t i/ell≤1)
    (p : J × R → ℝ) (hp : ∀ ir,0≤p ir)
    (hf : ∀ i∉activeSet (x t),∀ r,flags t i r=false)
    (a : J → ℝ) (ha : a∈ChangingDomains.simplex (activeSet (x t))) :
    let d:=data hδ hδu C ell ct x key hx flags t
    let B:=core d p
    let a':=(family C ell).update d p (∑ i,B i) a
    ∀ i,(∑ j,B j)*a' i≤(1+ct*weight δ x key t i/ell)*B i := by
  classical
  intro d B a'
  have hB : ∀ i,0≤B i := fun i=>ChangingDomains.core_nonneg (fun i r=>hp (i,r)) i
  have hz : ∀ i∉activeSet (x t),B i=0 := by
    intro i hi
    simp only [B,core,d,data_flags,hf i hi,Bool.false_eq_true,ite_false,sum_const_zero]
  have ha' : a'∈ChangingDomains.simplex (activeSet (x t)) := by
    have h:=(family C ell).update_mem d p (∑ i,B i) a
    change a'∈ChangingDomains.simplex d.active at h
    simpa only [d,data_active] using h
  by_cases hn : (activeSet (x t)).Nonempty
  · cases ho : dominant (run x key t) with
    | none =>
      have hh : ∀ i,1≤weight δ x key t i := fun i=>
        weight_regular_one δ x key t i (by simp [ho])
      have hd : d=regular (activeSet (x t)) (flags t) (weight δ x key t)
          (fun i=>ct*weight δ x key t i/ell) hh := by
        unfold d data
        dsimp only
        rw [ite_eq_left hn]
        split <;> simp_all
      have ht:=regular_exp_sum δ x key hx t (nonempty_mass x key hx t hn) ho
      have hg : 2*(25+32*(2:ℝ))*(1+1)<C*ct := by linarith
      simpa only [a',B,hd] using regular_update_feasible hn (flags t) (weight δ x key t)
        hh hC hel hct hmax (by norm_num : (0:ℝ)≤2) ht hg p hp hf a ha
    | some o =>
      by_cases hu : 0<sideRatio δ x key t
      · have hh : ∀ i≠o,1≤weight δ x key t i := fun i hi=>
          weight_regular_one δ x key t i (by rw [ho]; simpa [eq_comm] using hi)
        have hum : sideRatio δ x key t≤1 := by linarith [side_ratio_upper hδ hδu x key hx t ho]
        have hd : d=marked (activeSet (x t)) (flags t) o (weight δ x key t)
            (fun i=>ct*weight δ x key t i/ell) (sideRatio δ x key t) hu hum hh := by
          unfold d data
          dsimp only
          rw [ite_eq_left hn]
          split <;> simp_all
        have hg : 2*((25*(1/2:ℝ)+2+32*2)/(1/2))*(1+1)<C*ct := by linarith
        simpa only [a',B,hd] using marked_update_feasible (marked_active x key hx t ho)
          (flags t) (weight δ x key t) hu hum (marked_weight δ x key t o ho) hh
          hC hel hct hmax (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)<1/2)
          (by norm_num : (1/2:ℝ)≤1)
          (fun i hi hio=>weight_side_lower hδ hδu x key hx t ho hi hio hu)
          (side_exp_sum hδ hδu x key hx t ho) hg p hp hf a ha
      · have hu0 : sideRatio δ x key t=0 := le_antisymm (le_of_not_gt hu) (side_ratio_nonneg δ x key hx t)
        have hA:=marked_zero_singleton hδ x key hx t ho hu0
        intro i
        have he:=singleton_feasible (fun j hj=>hz j (by simpa [hA] using hj)) (hA ▸ ha') i
        rw [he]
        have he0 : 0≤ct*weight δ x key t i/ell :=
          div_nonneg (mul_nonneg hct.le (weight_nonneg δ x key hx t i)) hel.le
        nlinarith [mul_nonneg he0 (hB i)]
  · have he : activeSet (x t)=∅ := not_nonempty_iff_eq_empty.mp hn
    have hzero : ∀ i,B i=0 := fun i=>hz i (by simp [he])
    intro i
    simp [hzero]

end KServer.ScheduledSimplex

end


/-! Actual true and held beta parameters. Their gaps follow from the true
parent/child size relation and the literal coarse epoch, not an output oracle. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualParameters
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule
open CoarseParameters
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω→ℝ}

omit [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R] in
lemma log_bound {k M:ℝ} (hk:1≤k) (hM:M≤k) :
    0≤Real.log (k/max M cutoff) ∧ Real.log (k/max M cutoff)≤10000*(1+Real.log (k+1)) := by
  have hc:0<cutoff:=by norm_num [cutoff]
  have hck:cutoff≤k:=by norm_num [cutoff]; linarith
  have hm:0 < max M cutoff:=hc.trans_le (le_max_right _ _)
  have hmk:max M cutoff≤k:=max_le hM hck
  have hkn:0<k:=by linarith
  have hl:0≤Real.log (k+1):=Real.log_nonneg (by linarith)
  refine ⟨Real.log_nonneg ((one_le_div hm).mpr hmk),?_⟩
  have hq:k/max M cutoff≤10000*(k+1) := by
    apply (div_le_iff₀ hm).mpr
    have h:=mul_le_mul_of_nonneg_left (le_max_right M cutoff) (show 0≤10000*(k+1) by positivity)
    change 10000*(k+1)*(1/10000)≤10000*(k+1)*max M cutoff at h
    linarith
  have hs:=Real.log_le_log (div_pos hkn hm) hq
  rw [Real.log_mul (by norm_num : (10000:ℝ)≠0) (by positivity : k+1≠0)] at hs
  have hh:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10000)
  nlinarith

omit [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R] in
lemma beta_bounds {k M cb:ℝ} (hk:1≤k) (hM:M≤k) (hcb:0≤cb) :
    3≤beta k cutoff cb (1+Real.log (k+1)) M ∧
      beta k cutoff cb (1+Real.log (k+1)) M≤3+10000*cb := by
  have hel:0<1+Real.log (k+1):=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); linarith
  have h:=log_bound hk hM
  have hfac:0≤cb/(1+Real.log (k+1)):=div_nonneg hcb hel.le
  have hm:=mul_le_mul_of_nonneg_left h.2 hfac
  have he:cb/(1+Real.log (k+1))*(10000*(1+Real.log (k+1)))=10000*cb:=by field_simp
  rw [he] at hm
  unfold beta
  constructor
  · linarith [mul_nonneg hfac h.1]
  · linarith

lemma gap {δ k cb:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k) (hcb:0≤cb)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (V:ℕ→Ω→ℝ)
    (hV:∀ t ω,(∑ i,size (P i) t ω)≤V t ω) (t:ℕ) (ω:Ω) (i:J)
    (hi:i∈activeSet (vector cutoff δ P ω t)) :
    cb/20*weight δ (vector cutoff δ P ω) (fun s=>key s ω) t i/(1+Real.log (k+1))≤
      beta k cutoff cb (1+Real.log (k+1)) (size (P i) t ω)-
      beta k cutoff cb (1+Real.log (k+1)) (V t ω) := by
  let x:=vector cutoff δ P ω
  let ky:=fun s=>key s ω
  let M:=fun j=>size (P j) t ω
  have hx:=vector_nonneg cutoff δ P ω
  have hc:0<cutoff:=by norm_num [cutoff]
  have hip:0<x t i:=(mem_activeSet _ _).mp hi
  have ha:=(active_accuracy hc hδ hδu (P i) ω t).1 ((live_iff hδ hδu (P i) t ω).mp hip)
  have hMi:0<M i:=hc.trans_le ha.2.2
  have hMn:∀ j,0≤M j:=fun j=>size_nonneg (P j) t ω
  have hMV:M i≤V t ω:=(single_le_sum (fun j _=>hMn j) (mem_univ i)).trans (hV t ω)
  have hupper:∀ j,x t j≤(11/10)*M j:=fun j=>value_bound hc hδ hδu (P j) ω t
  have hel:0<1+Real.log (k+1):=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); linarith
  rw [beta_difference (by linarith : 0<k) hc ha.2.2 hMV]
  have hfac:0≤cb/(1+Real.log (k+1)):=div_nonneg hcb hel.le
  have hg:(1/20:ℝ)*weight δ x ky t i≤Real.log (V t ω/M i) := by
    by_cases ho:EpochSchedule.dominant (EpochSchedule.run x ky t)=some i
    · rw [marked_weight δ x ky t i ho]
      have hA:0 < mass x ky t:=ScheduledSimplex.nonempty_mass x ky hx t ⟨i,hi⟩
      have hxi:x t i≤(101/100)*mass x ky t:=
        (single_le_sum (fun j _=>hx t j) (mem_univ i)).trans (mass_accuracy x ky hx t).2
      have hUn:0 ≤ sideHeld δ x ky t:=side_held_nonneg δ x ky hx t
      have hUs:sideHeld δ x ky t≤(1001/1000)*((∑ j,x t j)-x t i) := by
        have h:=(side_held_accuracy hδ x ky hx t).2
        change sideHeld δ x ky t≤(1+δ)*CoarseSide.side (x t) (EpochSchedule.run x ky t) at h
        rw [side_eq_erase _ _ ho,sum_erase_eq_sub (mem_univ i)] at h
        have hn:0≤(∑ j,x t j)-x t i:=sub_nonneg.mpr (single_le_sum (fun j _=>hx t j) (mem_univ i))
        nlinarith
      exact dominant_gap hMn (hx t) hupper (hV t ω) i hMi hip ha.1 hA hxi hUn hUs
        (side_ratio_upper hδ hδu x ky hx t ho)
    · rw [regular_weight δ x ky t i ho]
      have hs:=EpochSchedule.regular_small (EpochSchedule.run_valid x ky hx t) ho
      change x t i≤(86/100:ℝ)*mass x ky t at hs
      have hA:0 ≤ mass x ky t:=mass_nonneg x ky hx t
      rw [HeldWeights.regular_eq hip (by linarith)]
      exact regular_gap hMn (hx t) hupper (hV t ω) i hMi hip ha.1 (mass_accuracy x ky hx t).1 hs
  have h:=mul_le_mul_of_nonneg_left hg hfac
  calc _ = cb/(1+Real.log (k+1))*((1/20)*weight δ x ky t i) := by dsimp [x,ky]; ring
       _ ≤ _ := h

omit [Fintype J] [DecidableEq J] in
lemma held_error {δ k cb:ℝ} (hδ:0<δ) (hk:1≤k) (hcb:0≤cb)
    (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) :
    beta k cutoff cb (1+Real.log (k+1)) (size Q t ω)≤
      upperBeta k cutoff cb (1+Real.log (k+1)) δ (parent cutoff δ Q t ω) ∧
      upperBeta k cutoff cb (1+Real.log (k+1)) δ (parent cutoff δ Q t ω)≤
      beta k cutoff cb (1+Real.log (k+1)) (size Q t ω)+4*cb*δ/(1+Real.log (k+1)) := by
  have hc:0<cutoff:=by norm_num [cutoff]
  have hel:0<1+Real.log (k+1):=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); linarith
  have ha:=parent_accuracy hc.le hδ Q t ω
  have h:=beta_upper_error (by linarith : 0<k) hc hcb hel hδ
    (le_max_left cutoff (size Q t ω)) (parent_nonneg hc.le δ Q t ω) ha.1 ha.2
  have he:max (max cutoff (size Q t ω)) cutoff=max cutoff (size Q t ω) := max_eq_left (le_max_left _ _)
  simp only [beta] at h ⊢
  rw [he] at h
  simpa only [max_comm cutoff (size Q t ω)] using h

end KServer.ActualParameters

end


/-! Prefix causality of the literal epoch, mark, side-total, log-size and
simplex-data recurrences. These equalities use the real input prefix; there
is no reinitialization at a fictitious conditional prefix. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduleCausality
attribute [local instance] Classical.propDecidable
open AllocationSchedule EpochSchedule
variable {J K R : Type} [Fintype J] [DecidableEq J] [Fintype R]

def PrefixEq {A : Type*} (t : ℕ) (a b : ℕ → A) : Prop := ∀ s≤t,a s=b s

lemma PrefixEq.mono {A : Type*} {t s : ℕ} {a b : ℕ → A}
    (h : PrefixEq t a b) (hs : s≤t) : PrefixEq s a b := fun j hj=>h j (hj.trans hs)

omit [DecidableEq J] in
lemma run_prefix (x y : ℕ → J → ℝ) (key key' : ℕ → K) (t : ℕ)
    (hx : PrefixEq t x y) (hk : PrefixEq t key key') : run x key t=run y key' t := by
  induction t with
  | zero => simp only [run,hx 0 le_rfl]
  | succ t ih =>
    have ht : t≤t+1 := Nat.le_succ t
    simp only [run,hx t ht,hx (t+1) le_rfl,hk t ht,hk (t+1) le_rfl,
      ih (hx.mono ht) (hk.mono ht)]

omit [DecidableEq J] in
lemma mass_prefix (x y : ℕ → J → ℝ) (key key' : ℕ → K) (t : ℕ)
    (hx : PrefixEq t x y) (hk : PrefixEq t key key') : mass x key t=mass y key' t :=
  congrArg (fun s:State J=>total s.reference) (run_prefix x y key key' t hx hk)

omit [DecidableEq J] in
lemma side_prefix (x y : ℕ → J → ℝ) (key key' : ℕ → K) (t : ℕ)
    (hx : PrefixEq t x y) (hk : PrefixEq t key key') :
    CoarseSide.sideInput x key t=CoarseSide.sideInput y key' t := by
  simp only [CoarseSide.sideInput,hx t le_rfl,run_prefix x y key key' t hx hk]

omit [DecidableEq J] in
lemma reset_prefix (x y : ℕ → J → ℝ) (key key' : ℕ → K) (t : ℕ)
    (hx : PrefixEq (t+1) x y) (hk : PrefixEq (t+1) key key') :
    CoarseSide.epochReset x key t=CoarseSide.epochReset y key' t := by
  have ht : t≤t+1 := Nat.le_succ t
  simp only [CoarseSide.epochReset,hx t ht,hx (t+1) le_rfl,hk t ht,hk (t+1) le_rfl,
    run_prefix x y key key' t (hx.mono ht) (hk.mono ht)]

omit [DecidableEq J] in
lemma sideHeld_prefix (δ : ℝ) (x y : ℕ → J → ℝ) (key key' : ℕ → K) (t : ℕ)
    (hx : PrefixEq t x y) (hk : PrefixEq t key key') : sideHeld δ x key t=sideHeld δ y key' t := by
  induction t with
  | zero => exact side_prefix x y key key' 0 hx hk
  | succ t ih =>
    change (if CoarseSide.epochReset x key t ∨ RankTracking.factorTest id δ
      (CoarseSide.sideInput x key (t+1)) (sideHeld δ x key t)
      then CoarseSide.sideInput x key (t+1) else sideHeld δ x key t)=_
    rw [reset_prefix x y key key' t hx hk,side_prefix x y key key' (t+1) hx hk,
      ih (hx.mono (Nat.le_succ t)) (hk.mono (Nat.le_succ t))]
    rfl

omit [DecidableEq J] in
lemma ratio_prefix (δ : ℝ) (x y : ℕ → J → ℝ) (key key' : ℕ → K) (t : ℕ)
    (hx : PrefixEq t x y) (hk : PrefixEq t key key') : sideRatio δ x key t=sideRatio δ y key' t := by
  rw [sideRatio,sideRatio,sideHeld_prefix δ x y key key' t hx hk,mass_prefix x y key key' t hx hk]

lemma weight_prefix (δ : ℝ) (x y : ℕ → J → ℝ) (key key' : ℕ → K) (t : ℕ)
    (hx : PrefixEq t x y) (hk : PrefixEq t key key') : weight δ x key t=weight δ y key' t := by
  funext i
  simp only [weight,run_prefix x y key key' t hx hk,ratio_prefix δ x y key key' t hx hk,
    hx t le_rfl,mass_prefix x y key key' t hx hk]

omit [DecidableEq J] in
lemma epoch_prefix (x y : ℕ → J → ℝ) (key key' : ℕ → K) (t : ℕ)
    (hx : PrefixEq t x y) (hk : PrefixEq t key key') : epoch x key t=epoch y key' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [epoch,reset_prefix x y key key' t hx hk,
      ih (hx.mono (Nat.le_succ t)) (hk.mono (Nat.le_succ t))]

omit [Fintype R] in
lemma data_prefix {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct : ℝ)
    (x y : ℕ → J → ℝ) (key key' : ℕ → K)
    (hxn : ∀ t i,0≤x t i) (hyn : ∀ t i,0≤y t i)
    (flags flags' : ℕ → J → R → Bool) (t : ℕ)
    (hx : PrefixEq t x y) (hk : PrefixEq t key key') (hf : flags t=flags' t) :
    data hδ hδu C ell ct x key hxn flags t=data hδ hδu C ell ct y key' hyn flags' t := by
  have he:=run_prefix x y key key' t hx hk
  have hw:=weight_prefix δ x y key key' t hx hk
  have hu:=ratio_prefix δ x y key key' t hx hk
  unfold data
  dsimp only
  congr 1
  · exact congrArg (fun v=> (activeSet v).Nonempty) (hx t le_rfl)
  · simp only [hx t le_rfl,hf,hw,hu]
    have hd := congrArg dominant he
    clear he
    split
    · rename_i hl
      have hh : dominant (run y key' t)=none := hd.symm.trans hl
      split
      · rfl
      · rename_i o hr
        have hf := hh.symm.trans hr
        cases hf
    · rename_i o hl
      have hh : dominant (run y key' t)=some o := hd.symm.trans hl
      split
      · rename_i hc
        split
        · rename_i hr
          have hf := hh.symm.trans hr
          cases hf
        · rename_i j hr
          have hj : o=j := Option.some.inj (hh.symm.trans hr)
          subst j
          rfl
      · rename_i hc
        split
        · rename_i hr
          have hf := hh.symm.trans hr
          cases hf
        · rfl
  · simp only [hx t le_rfl,hf]

end KServer.ScheduleCausality

end


/-! The actual held-profile simplex proportion process, tied to the filtered
child ranks. Inactive coordinates are proved harmless, and feasibility holds
for its actual state at every time, including initialization and wholesale
restarts. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.StarSimplex
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseProcess CoarseEpoch
open AllocationSchedule StarProfile
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω → ℝ}

def flags (P : J → R → FilteredRanks w) (ω : Ω) (t : ℕ) : J → R → Bool :=
  fun i r=>CoreFlags.flag (P i r) t ω

def input {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (t : ℕ) (ω : Ω) : CausalSimplex.Input J R :=
  ⟨data hδ hδu C ell ct (vector cutoff δ P ω) (fun s=>key s ω)
      (vector_nonneg cutoff δ P ω) (flags P ω) t,
    fun ir=>(P ir.1 ir.2).p t ω,
    epoch (vector cutoff δ P ω) (fun s=>key s ω) t⟩

def proportion {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) : ℕ → Ω → J → ℝ :=
  CausalSimplex.run C ell (input hδ hδu C ell ct P key)

lemma proportion_mem {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (t : ℕ) (ω : Ω) :
    proportion hδ hδu C ell ct P key t ω ∈ ChangingDomains.simplex (activeSet (vector cutoff δ P ω t)) := by
  have h:=CausalSimplex.run_mem C ell (input hδ hδu C ell ct P key) t ω
  simpa only [proportion,input,data_active] using h

lemma input_core {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (t : ℕ) (ω : Ω) :
    SimplexFamilies.core (input hδ hδu C ell ct P key t ω).data
      (input hδ hδu C ell ct P key t ω).ranks =
      fun i=>∑ r,if CoreFlags.flag (P i r) t ω then (P i r).p t ω else 0 := by
  funext i
  simp only [input,SimplexFamilies.core,data_flags,flags]

lemma feasible {δ C ct k : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (hC : 0<C) (hct : 0<ct) (hctu : ct*20002≤1) (hgap : 700<C*ct) (hk : 1≤k)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (hs : ∀ t ω,(∑ i,size (P i) t ω)≤k) (t : ℕ) (ω : Ω) :
    let ell:=1+Real.log (k+1)
    let B:=fun i=>∑ r,if CoreFlags.flag (P i r) t ω then (P i r).p t ω else 0
    ∀ i,(∑ j,B j)*proportion hδ hδu C ell ct P key t ω i ≤
      (1+ct*weight δ (vector cutoff δ P ω) (fun s=>key s ω) t i/ell)*B i := by
  let ell:=1+Real.log (k+1)
  let d:=input hδ hδu C ell ct P key
  have hel : 0<ell := by
    have h:=Real.log_nonneg (show 1≤k+1 by linarith)
    dsimp [ell]; linarith
  have hm (i:J) (_hi:i∈activeSet (vector cutoff δ P ω t)) :
      ct*weight δ (vector cutoff δ P ω) (fun s=>key s ω) t i/ell≤1 := by
    apply (div_le_iff₀ hel).mpr
    have h:=weight_upper hδ hδu hk (vector cutoff δ P ω) (fun s=>key s ω)
      (vector_nonneg cutoff δ P ω) (fun s=>vector_total hδ hδu P s ω (hs s ω))
      (fun s i hi=>vector_floor hδ hδu P s ω i hi) t i
    have hmul:=mul_le_mul_of_nonneg_left h hct.le
    have hmul2:=mul_le_mul_of_nonneg_right hctu hel.le
    change _≤20002*ell at h
    nlinarith
  have hstep (a:J→ℝ) (ha:a∈ChangingDomains.simplex (activeSet (vector cutoff δ P ω t))) :=
    ScheduledSimplex.update_feasible hδ hδu hC hel hct hgap
      (vector cutoff δ P ω) (fun s=>key s ω) (vector_nonneg cutoff δ P ω)
      (flags P ω) t hm (d t ω).ranks (fun ir=>(P ir.1 ir.2).range t ω|>.1)
      (fun i hi r=>flags_supported hδ hδu P t ω i hi r) a ha
  have hu (a:J→ℝ) (ha:a∈ChangingDomains.simplex (activeSet (vector cutoff δ P ω t))) :
      ∀ i,(∑ j,∑ r,if CoreFlags.flag (P j r) t ω then (P j r).p t ω else 0)*
        (SimplexFamilies.family C ell).update (d t ω).data (d t ω).ranks
          (CausalSimplex.mass (d t ω)) a i≤
        (1+ct*weight δ (vector cutoff δ P ω) (fun s=>key s ω) t i/ell)*
          (∑ r,if CoreFlags.flag (P i r) t ω then (P i r).p t ω else 0) := by
    simpa only [d,input,CausalSimplex.mass,SimplexFamilies.core,data_flags,flags] using hstep a ha
  change ∀ i,(∑ j,∑ r,if CoreFlags.flag (P j r) t ω then (P j r).p t ω else 0)*
    CausalSimplex.run C ell d t ω i≤
    (1+ct*weight δ (vector cutoff δ P ω) (fun s=>key s ω) t i/ell)*
      (∑ r,if CoreFlags.flag (P i r) t ω then (P i r).p t ω else 0)
  cases t with
  | zero =>
    rw [CausalSimplex.run_initial]
    have hm : ChangingDomains.canonical (d 0 ω).data.active∈
        ChangingDomains.simplex (activeSet (vector cutoff δ P ω 0)) := by
      simpa only [d,input,data_active] using ChangingDomains.canonical_mem (d 0 ω).data.active
    exact hu _ hm
  | succ t =>
    rw [CausalSimplex.run_successor]
    have hm:=CausalSimplex.move_mem C ell (d t ω) (d (t+1) ω) (d (t+1) ω).ranks
      (CausalSimplex.run C ell d t ω)
    have hm':CausalSimplex.move C ell (d t ω) (d (t+1) ω) (d (t+1) ω).ranks
        (CausalSimplex.run C ell d t ω)∈ChangingDomains.simplex (activeSet (vector cutoff δ P ω (t+1))) := by
      simpa only [d,input,data_active] using hm
    exact hu _ hm'

omit [Fintype Ω] in
lemma history_prefix (H : ℕ → Ω → ℕ)
    (hr : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    {t s : ℕ} (hs : s≤t) {ω z : Ω} (he : H t ω=H t z) : H s ω=H s z := by
  induction t with
  | zero => exact (Nat.eq_zero_of_le_zero hs) ▸ he
  | succ t ih =>
    rcases Nat.eq_or_lt_of_le hs with h|h
    · exact h ▸ he
    · exact ih (Nat.le_of_lt_succ h) (hr t ω z he)

lemma input_adapted {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (H:ℕ→Ω→ℕ)
    (hH : ∀ i r t ω,(P i r).history t ω=H t ω)
    (hr : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z) (t : ℕ) (ω z : Ω) (he:H t ω=H t z) :
    input hδ hδu C ell ct P key t ω=input hδ hδu C ell ct P key t z := by
  have hx:ScheduleCausality.PrefixEq t (vector cutoff δ P ω) (vector cutoff δ P z) :=
    fun s hs=>vector_adapted δ P H hH hr s ω z (history_prefix H hr hs he)
  have hk:ScheduleCausality.PrefixEq t (fun s=>key s ω) (fun s=>key s z) :=
    fun s hs=>hkey s ω z (history_prefix H hr hs he)
  have hh (i:J) (r:R):(P i r).history t ω=(P i r).history t z := by rw[hH,hH,he]
  have hf:flags P ω t=flags P z t := by
    funext i r
    exact CoreFlags.flag_adapted (P i r) t (hh i r)
  have hp:(fun ir:J×R=>(P ir.1 ir.2).p t ω)=(fun ir=>(P ir.1 ir.2).p t z) := by
    funext ir
    exact (P ir.1 ir.2).adapted t ω z (hh _ _)
  unfold input
  congr 1
  · exact ScheduleCausality.data_prefix hδ hδu C ell ct _ _ _ _ _ _ _ _ t hx hk hf
  · exact ScheduleCausality.epoch_prefix _ _ _ _ t hx hk

lemma proportion_adapted {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (H:ℕ→Ω→ℕ)
    (hH : ∀ i r t ω,(P i r).history t ω=H t ω)
    (hr : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z) (t : ℕ) (ω z : Ω) (he:H t ω=H t z) :
    proportion hδ hδu C ell ct P key t ω=proportion hδ hδu C ell ct P key t z :=
  CausalSimplex.run_adapted C ell _ H hr (input_adapted hδ hδu C ell ct P key H hH hr hkey) t ω z he

end KServer.StarSimplex

end


/-! Literal causal side minimizers, including pre-minimization, zero deletion,
wholesale restart, and minimization on the new domain. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CausalSide
open AdaptiveMinimization SideFamilies
attribute [local instance] Classical.propDecidable Classical.decEq
variable {J R Ω : Type} [Fintype J] [Fintype R]

structure Input (J R : Type) where
  data : SideFamilies.Data J R
  ranks : J × R → ℝ
  epoch : ℕ

def move (c : ℝ) (old new : Input J R) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  if old.epoch=new.epoch ∧ old.data.W=new.data.W then
    SideFamilies.transport c old.data new.data p a else fun _=>0

omit [Fintype R] in
lemma zero_mem (d : SideFamilies.Data J R) :
    (fun _=>0)∈ChangingDomains.sideDomain d.active d.W :=
  ⟨fun _=>le_rfl,by simpa using d.W_nonneg,fun _ _=>rfl⟩

lemma move_mem (c : ℝ) (old new : Input J R) (p : J × R → ℝ) (a : J → ℝ) :
    move c old new p a∈ChangingDomains.sideDomain new.data.active new.data.W := by
  unfold move
  split_ifs with h
  · exact SideFamilies.transport_mem c old.data new.data p a h.2
  · exact zero_mem new.data

def model (c : ℝ) : Family (Input J R) (J × R) J where
  domain d := ChangingDomains.sideDomain d.data.active d.data.W
  compact _ := SideSupported.sideDomain_compact _ _
  seed d := ⟨(SideFamilies.family c).update d.data d.ranks d.data.D (fun _=>0),
    (SideFamilies.family c).update_mem _ _ _ _⟩
  offset d := SideFamilies.offset c d.data
  coefficient d := SideFamilies.coefficient c d.data
  offset_continuous d := SideFamilies.offset_continuous c d.data
  coefficient_continuous d := SideFamilies.coefficient_continuous c d.data

lemma model_value (c : ℝ) (d : Input J R) (p : J × R → ℝ) (a : J → ℝ) :
    (model c).value d p a=(SideFamilies.family c).value d.data p a := rfl

lemma model_update (c : ℝ) (d : Input J R) (p : J × R → ℝ) (D : ℝ) (a : J → ℝ) :
    (model c).update d p D a=(SideFamilies.family c).update d.data p D a := rfl

def transport (c : ℝ) : Transport (model (J:=J) (R:=R) c) where
  map := move c
  mem old new p a _ := move_mem c old new p a

def run (c : ℝ) (d : ℕ → Ω → Input J R) : ℕ → Ω → J → ℝ :=
  state (model c) (transport c) d (fun t ω=>(d t ω).ranks) (fun t ω=>(d t ω).data.D)

lemma run_mem (c : ℝ) (d : ℕ → Ω → Input J R) (t : ℕ) (ω : Ω) :
    run c d t ω∈ChangingDomains.sideDomain (d t ω).data.active (d t ω).data.W :=
  state_mem (model c) (transport c) d (fun t ω=>(d t ω).ranks)
    (fun t ω=>(d t ω).data.D) t ω

lemma run_initial (c : ℝ) (d : ℕ → Ω → Input J R) (ω : Ω) :
    run c d 0 ω=(SideFamilies.family c).update (d 0 ω).data (d 0 ω).ranks
      (d 0 ω).data.D (fun _=>0) := rfl

lemma run_successor (c : ℝ) (d : ℕ → Ω → Input J R) (t : ℕ) (ω : Ω) :
    run c d (t+1) ω=(SideFamilies.family c).update (d (t+1) ω).data (d (t+1) ω).ranks
      (d (t+1) ω).data.D (move c (d t ω) (d (t+1) ω) (d (t+1) ω).ranks (run c d t ω)) := rfl

lemma run_adapted (c : ℝ) (d : ℕ → Ω → Input J R) (H : ℕ → Ω → ℕ)
    (href : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hd : ∀ t ω z,H t ω=H t z → d t ω=d t z) (t : ℕ) (ω z : Ω)
    (he : H t ω=H t z) : run c d t ω=run c d t z :=
  state_adapted _ _ _ _ _ H href hd
    (fun t ω z h=>congrArg Input.ranks (hd t ω z h))
    (fun t ω z h=>congrArg (fun d:Input J R=>d.data.D) (hd t ω z h)) t ω z he

lemma ordinary_successor (c : ℝ) (d : ℕ → Ω → Input J R) (t : ℕ) (ω : Ω)
    (he : (d t ω).epoch=(d (t+1) ω).epoch)
    (hW : (d t ω).data.W=(d (t+1) ω).data.W) :
    run c d (t+1) ω=SideFamilies.step c (d t ω).data (d (t+1) ω).data
      (d (t+1) ω).ranks (run c d t ω) := by
  rw [run_successor,move,ite_eq_left ⟨he,hW⟩]
  rfl

lemma wholesale_successor (c : ℝ) (d : ℕ → Ω → Input J R) (t : ℕ) (ω : Ω)
    (he : (d t ω).epoch≠(d (t+1) ω).epoch) :
    run c d (t+1) ω=(SideFamilies.family c).update (d (t+1) ω).data
      (d (t+1) ω).ranks (d (t+1) ω).data.D (fun _=>0) := by
  rw [run_successor,move,ite_eq_right (fun h=>he h.1)]

lemma run_feasible (d : ℕ → Ω → Input J R) {M : ℝ} (t : ℕ) (ω : Ω)
    (hb : 1≤(d t ω).data.b) (hD : 0≤(d t ω).data.D)
    (hM : ∀ i∈(d t ω).data.active,(d t ω).data.b+(d t ω).data.θ i≤M)
    (hW : 2*M<(d t ω).data.W) (hp : ∀ ir,0≤(d t ω).ranks ir)
    (hf : ∀ i∉(d t ω).data.active,∀ r,(d t ω).data.flags i r=false) :
    (∀ i,(d t ω).data.D*run (8*M) d t ω i≤
      ((d t ω).data.b+(d t ω).data.θ i)*core (d t ω).data (d t ω).ranks i) ∧
    ((∑ i,core (d t ω).data (d t ω).ranks i)≤2*(d t ω).data.D → ∀ i,
      (d t ω).data.b*core (d t ω).data (d t ω).ranks i-
        (d t ω).data.θ i*(d t ω).data.z i*(d t ω).data.D≤(d t ω).data.D*run (8*M) d t ω i) := by
  cases t with
  | zero => exact update_feasible _ hb hD hM hW _ hp hf _ (zero_mem _)
  | succ t => exact update_feasible _ hb hD hM hW _ hp hf _ (move_mem _ _ _ _ _)

lemma ordinary_payment (d : ℕ → Ω → Input J R) {M : ℝ} (t : ℕ) (ω : Ω)
    (he : (d t ω).epoch=(d (t+1) ω).epoch)
    (hWW : (d t ω).data.W=(d (t+1) ω).data.W)
    (hb : 1≤(d t ω).data.b) (hD : 0≤(d (t+1) ω).data.D)
    (hM : ∀ i∈(d t ω).data.active,(d t ω).data.b+(d t ω).data.θ i≤M)
    (hW : 2*M<(d t ω).data.W) (hp : ∀ ir,0≤(d (t+1) ω).ranks ir) :
    let old:=(d t ω).data
    let new:=(d (t+1) ω).data
    let p:=(d (t+1) ω).ranks
    let a:=run (8*M) d t ω
    new.D*ChangingDomains.variation (run (8*M) d (t+1) ω) a ≤
      (SideFamilies.family (8*M)).value old p a-
      (SideFamilies.family (8*M)).value new p (run (8*M) d (t+1) ω)+
      |(SideFamilies.family (8*M)).value (prepareData old new) p a-
        (SideFamilies.family (8*M)).value old p a|+
      |(SideFamilies.family (8*M)).value new p (SideFamilies.transport (8*M) old new p a)-
        (SideFamilies.family (8*M)).value (prepareData old new) p
          (SideFamilies.transport (8*M) old new p a)| := by
  dsimp only
  rw [ordinary_successor _ _ _ _ he hWW]
  exact step_payment _ _ hb hD hM hW _ hp _ (run_mem _ _ _ _) hWW

end KServer.CausalSide

end

end OAI
