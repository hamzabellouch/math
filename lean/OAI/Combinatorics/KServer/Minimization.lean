import Mathlib
import OAI.Combinatorics.KServer.Ranks

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AdaptiveMinimization
open Finset KServer.RankTracking
variable {I J Θ : Type*} [Fintype I] [Fintype J]

lemma avg_sum_any {Ω : Type} [Fintype Ω] (w : Ω → ℝ) {ι : Type*} [Fintype ι] (f : ι → Ω → ℝ) :
    avg w (fun ω => ∑ i, f i ω)=∑ i, avg w (f i) := by
  simp only [avg,mul_sum]; rw [sum_comm]

/-- The source primitives are affine in the rank inputs when the held parameters
and the state are fixed.  Both simplex and side domains are compact. -/
structure Family (Θ : Type*) (I J : Type*) [Fintype I] [Fintype J] where
  domain : Θ → Set (J → ℝ)
  compact : ∀ θ, IsCompact (domain θ)
  seed : ∀ θ, {a // a ∈ domain θ}
  offset : Θ → (J → ℝ) → ℝ
  coefficient : Θ → (J → ℝ) → I → ℝ
  offset_continuous : ∀ θ, ContinuousOn (offset θ) (domain θ)
  coefficient_continuous : ∀ θ i, ContinuousOn (fun a => coefficient θ a i) (domain θ)

def Family.value (F : Family Θ I J) (θ : Θ) (p : I → ℝ) (a : J → ℝ) : ℝ :=
  F.offset θ a + ∑ i, F.coefficient θ a i*p i

def movement (a b : J → ℝ) : ℝ := ∑ j, |a j-b j|

lemma movement_nonneg (a b : J → ℝ) : 0 ≤ movement a b :=
  sum_nonneg fun _ _ => abs_nonneg _

lemma movement_self (a : J → ℝ) : movement a a=0 := by simp [movement]

lemma movement_triangle (a b c : J → ℝ) : movement a c ≤ movement a b+movement b c := by
  unfold movement
  rw [← sum_add_distrib]
  exact sum_le_sum fun j _ => abs_sub_le (a j) (b j) (c j)

lemma Family.value_continuous (F : Family Θ I J) (θ : Θ) (p : I → ℝ) :
    ContinuousOn (F.value θ p) (F.domain θ) := by
  apply (F.offset_continuous θ).add
  exact continuousOn_finsetSum _ fun i _ => (F.coefficient_continuous θ i).mul_const _

lemma movement_continuous (b : J → ℝ) : Continuous (fun a => movement a b) :=
  continuous_finsetSum _ fun j _ => ((continuous_apply j).sub continuous_const).abs

lemma Family.exists_update (F : Family Θ I J) (θ : Θ) (p : I → ℝ)
    (c : ℝ) (a : J → ℝ) :
    ∃ b ∈ F.domain θ, IsMinOn (fun b => F.value θ p b+c*movement b a) (F.domain θ) b := by
  exact (F.compact θ).exists_isMinOn ⟨(F.seed θ).val,(F.seed θ).property⟩
    ((F.value_continuous θ p).add ((movement_continuous a).continuousOn.const_mul c))

/-- A fixed noncomputable selection, only from the currently supplied data. -/
def Family.update (F : Family Θ I J) (θ : Θ) (p : I → ℝ) (c : ℝ) (a : J → ℝ) : J → ℝ :=
  (F.exists_update θ p c a).choose

lemma Family.update_mem (F : Family Θ I J) (θ : Θ) (p : I → ℝ) (c : ℝ) (a : J → ℝ) :
    F.update θ p c a ∈ F.domain θ := (F.exists_update θ p c a).choose_spec.1

lemma Family.update_payment (F : Family Θ I J) (θ : Θ) (p : I → ℝ) (c : ℝ)
    {a : J → ℝ} (ha : a ∈ F.domain θ) :
    c*movement (F.update θ p c a) a ≤ F.value θ p a-F.value θ p (F.update θ p c a) := by
  have h := (F.exists_update θ p c a).choose_spec.2 ha
  change F.value θ p (F.update θ p c a)+c*movement (F.update θ p c a) a ≤
    F.value θ p a+c*movement a a at h
  rw [movement_self,mul_zero,add_zero] at h
  linarith

lemma Family.input_difference (F : Family Θ I J) (θ : Θ) (p q : I → ℝ) (a : J → ℝ) :
    F.value θ p a-F.value θ q a=∑ i, F.coefficient θ a i*(p i-q i) := by
  simp only [Family.value,mul_sub,sum_sub_distrib]
  ring

lemma Family.input_lipschitz (F : Family Θ I J) (θ : Θ) (p q : I → ℝ)
    (a : J → ℝ) {L : ℝ} (hL : ∀ i, |F.coefficient θ a i| ≤ L) :
    |F.value θ p a-F.value θ q a| ≤ L*∑ i, |p i-q i| := by
  rw [F.input_difference,mul_sum]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hL i) (abs_nonneg _))

variable {Ω : Type} [Fintype Ω]

/-- Domain transport is computed from old/new held parameters and new rank
inputs. For the manuscript it is the prepared update followed by deletion and
zero insertion. It is not permitted to depend on the unrealized future. -/
structure Transport (F : Family Θ I J) where
  map : Θ → Θ → (I → ℝ) → (J → ℝ) → (J → ℝ)
  mem : ∀ θ θ' p a, a ∈ F.domain θ → map θ θ' p a ∈ F.domain θ'

def state (F : Family Θ I J) (T : Transport F) (θ : ℕ → Ω → Θ)
    (p : ℕ → Ω → I → ℝ) (c : ℕ → Ω → ℝ) : ℕ → Ω → J → ℝ
  | 0, ω => (F.seed (θ 0 ω)).val
  | t+1, ω => F.update (θ (t+1) ω) (p (t+1) ω) (c (t+1) ω)
      (T.map (θ t ω) (θ (t+1) ω) (p (t+1) ω) (state F T θ p c t ω))

omit [Fintype Ω] in
lemma state_mem (F : Family Θ I J) (T : Transport F) (θ : ℕ → Ω → Θ)
    (p : ℕ → Ω → I → ℝ) (c : ℕ → Ω → ℝ) :
    ∀ t ω, state F T θ p c t ω ∈ F.domain (θ t ω) := by
  intro t ω
  cases t with
  | zero => exact (F.seed _).property
  | succ t => exact F.update_mem _ _ _ _

omit [Fintype Ω] in
/-- Causality is proved from the recursion (not a fictitious prefix interface). -/
lemma state_adapted (F : Family Θ I J) (T : Transport F) (θ : ℕ → Ω → Θ)
    (p : ℕ → Ω → I → ℝ) (c : ℕ → Ω → ℝ) (H : ℕ → Ω → ℕ)
    (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hθ : ∀ t ω z, H t ω=H t z → θ t ω=θ t z)
    (hp : ∀ t ω z, H t ω=H t z → p t ω=p t z)
    (hc : ∀ t, Adapted (H t) (c t)) :
    ∀ t ω z, H t ω=H t z → state F T θ p c t ω=state F T θ p c t z := by
  intro t
  induction t with
  | zero =>
      intro ω z hz
      exact congrArg (fun u => (F.seed u).val) (hθ 0 ω z hz)
  | succ t ih =>
      intro ω z hz
      have hprev := hr t ω z hz
      simp only [state,hθ (t+1) ω z hz,hp (t+1) ω z hz,hc (t+1) ω z hz,
        hθ t ω z hprev,ih ω z hprev]

/-- The signed editing charge, evaluated after filtering and drift but before
the final minimizing update. Preparation payments are allowed to lower it. -/
def edit (F : Family Θ I J) (T : Transport F) (θ : ℕ → Ω → Θ)
    (p : ℕ → Ω → I → ℝ) (c : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  let a := state F T θ p c t ω
  let b := T.map (θ t ω) (θ (t+1) ω) (p (t+1) ω) a
  F.value (θ (t+1) ω) (p (t+1) ω) b-F.value (θ t ω) (p (t+1) ω) a+
    c (t+1) ω*movement b a

omit [Fintype Ω] in
lemma state_payment (F : Family Θ I J) (T : Transport F) (θ : ℕ → Ω → Θ)
    (p : ℕ → Ω → I → ℝ) (c : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω)
    (hc : 0 ≤ c (t+1) ω) :
    c (t+1) ω*movement (state F T θ p c (t+1) ω) (state F T θ p c t ω) ≤
      F.value (θ t ω) (p (t+1) ω) (state F T θ p c t ω)-
      F.value (θ (t+1) ω) (p (t+1) ω) (state F T θ p c (t+1) ω)+
      edit F T θ p c t ω := by
  let a := state F T θ p c t ω
  let b := T.map (θ t ω) (θ (t+1) ω) (p (t+1) ω) a
  have hb : b ∈ F.domain (θ (t+1) ω) := T.mem _ _ _ _ (state_mem F T θ p c t ω)
  have hu := F.update_payment (θ (t+1) ω) (p (t+1) ω) (c (t+1) ω) hb
  have ht := mul_le_mul_of_nonneg_left
    (movement_triangle (state F T θ p c (t+1) ω) b a) hc
  change c (t+1) ω*movement (state F T θ p c (t+1) ω) b ≤
    F.value (θ (t+1) ω) (p (t+1) ω) b -
    F.value (θ (t+1) ω) (p (t+1) ω) (state F T θ p c (t+1) ω) at hu
  calc
    _ ≤ c (t+1) ω * (movement (state F T θ p c (t+1) ω) b + movement b a) := ht
    _ ≤ (F.value (θ (t+1) ω) (p (t+1) ω) b -
        F.value (θ (t+1) ω) (p (t+1) ω) (state F T θ p c (t+1) ω)) +
        c (t+1) ω * movement b a := by nlinarith [hu]
    _ = _ := by dsimp only [edit,a,b]; ring

/-- All ranks are taken under the same true observed history. -/
def rankVector {w : Ω → ℝ} (R : I → FilteredRanks w) (t : ℕ) (ω : Ω) : I → ℝ :=
  fun i => (R i).p t ω

def beforeVector {w : Ω → ℝ} (R : I → FilteredRanks w) (t : ℕ) (ω : Ω) : I → ℝ :=
  fun i => (R i).before t ω

omit [Fintype I] in
lemma rankVector_adapted {w : Ω → ℝ} (R : I → FilteredRanks w) (H : ℕ → Ω → ℕ)
    (hH : ∀ i, (R i).history=H) (t : ℕ) (ω z : Ω) (hz : H t ω=H t z) :
    rankVector R t ω=rankVector R t z := by
  funext i
  apply (R i).adapted t ω z
  simpa only [hH i] using hz

/-- Filtering is used on every step with the old held coefficients, before
selecting any ordinary/wholesale event measurable at the new history. -/
lemma filtering_zero (F : Family Θ I J) (T : Transport F) {w : Ω → ℝ}
    (R : I → FilteredRanks w) (θ : ℕ → Ω → Θ) (c : ℕ → Ω → ℝ)
    (H : ℕ → Ω → ℕ) (hH : ∀ i, (R i).history=H)
    (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hθ : ∀ t ω z, H t ω=H t z → θ t ω=θ t z)
    (hc : ∀ t, Adapted (H t) (c t)) (t : ℕ) :
    avg w (fun ω =>
      F.value (θ t ω) (beforeVector R (t+1) ω) (state F T θ (rankVector R) c t ω)-
      F.value (θ t ω) (rankVector R t ω) (state F T θ (rankVector R) c t ω))=0 := by
  simp_rw [F.input_difference]
  rw [avg_sum_any]
  apply sum_eq_zero
  intro i _
  apply filtering_affine (R i)
  intro ω z hz
  rw [hH i] at hz
  have hs := state_adapted F T θ (rankVector R) c H hr hθ
    (rankVector_adapted R H hH) hc t ω z hz
  dsimp only
  rw [hθ t ω z hz,hs]

lemma expected_payment_step (F : Family Θ I J) (T : Transport F) {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (R : I → FilteredRanks w)
    (θ : ℕ → Ω → Θ) (c : ℕ → Ω → ℝ)
    (H : ℕ → Ω → ℕ) (hH : ∀ i, (R i).history=H)
    (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hθ : ∀ t ω z, H t ω=H t z → θ t ω=θ t z)
    (hc : ∀ t, Adapted (H t) (c t)) (hcn : ∀ t ω, 0 ≤ c t ω)
    {L : ℝ} (hL : ∀ θ a, a ∈ F.domain θ → ∀ i, |F.coefficient θ a i| ≤ L)
    (t : ℕ) :
    avg w (fun ω => c (t+1) ω*movement (state F T θ (rankVector R) c (t+1) ω)
      (state F T θ (rankVector R) c t ω)) ≤
    avg w (fun ω => F.value (θ t ω) (rankVector R t ω) (state F T θ (rankVector R) c t ω))-
    avg w (fun ω => F.value (θ (t+1) ω) (rankVector R (t+1) ω)
      (state F T θ (rankVector R) c (t+1) ω)) +
    L*(∑ i, avg w (fun ω => |(R i).p (t+1) ω-(R i).before (t+1) ω|))+
    avg w (edit F T θ (rankVector R) c t) := by
  let a := state F T θ (rankVector R) c
  have hpoint (ω : Ω) : c (t+1) ω*movement (a (t+1) ω) (a t ω) ≤
      (F.value (θ t ω) (rankVector R t ω) (a t ω)-
        F.value (θ (t+1) ω) (rankVector R (t+1) ω) (a (t+1) ω))+
      (F.value (θ t ω) (beforeVector R (t+1) ω) (a t ω)-
        F.value (θ t ω) (rankVector R t ω) (a t ω))+
      L*(∑ i, |(R i).p (t+1) ω-(R i).before (t+1) ω|)+
      edit F T θ (rankVector R) c t ω := by
    have hm := state_payment F T θ (rankVector R) c t ω (hcn (t+1) ω)
    have hd := (le_abs_self (F.value (θ t ω) (rankVector R (t+1) ω) (a t ω)-
      F.value (θ t ω) (beforeVector R (t+1) ω) (a t ω))).trans
      (F.input_lipschitz (θ t ω) (rankVector R (t+1) ω) (beforeVector R (t+1) ω)
        (a t ω) (hL _ _ (state_mem F T θ (rankVector R) c t ω)))
    change _ ≤ L*(∑ i, |(R i).p (t+1) ω-(R i).before (t+1) ω|) at hd
    change c (t+1) ω*movement (a (t+1) ω) (a t ω) ≤
      F.value (θ t ω) (rankVector R (t+1) ω) (a t ω)-
      F.value (θ (t+1) ω) (rankVector R (t+1) ω) (a (t+1) ω)+
      edit F T θ (rankVector R) c t ω at hm
    linarith
  have he := avg_mono hw hpoint
  simp only [avg_add,avg_sub,avg_mul,avg_sum_any] at he
  have hf := filtering_zero F T R θ c H hH hr hθ hc t
  rw [avg_sub] at hf
  change avg w (fun ω => F.value (θ t ω) (beforeVector R (t+1) ω) (a t ω))-
    avg w (fun ω => F.value (θ t ω) (rankVector R t ω) (a t ω))=0 at hf
  rw [hf,add_zero] at he
  exact he

/-- The full causal minimizer telescope. The computed signed edit term must be
bounded from the actual coordinate preparation/deletion and coarse schedules;
there is no asserted policy or asserted coarse-budget estimate here. -/
theorem expected_payment (F : Family Θ I J) (T : Transport F) {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (R : I → FilteredRanks w)
    (θ : ℕ → Ω → Θ) (c : ℕ → Ω → ℝ)
    (H : ℕ → Ω → ℕ) (hH : ∀ i, (R i).history=H)
    (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hθ : ∀ t ω z, H t ω=H t z → θ t ω=θ t z)
    (hc : ∀ t, Adapted (H t) (c t)) (hcn : ∀ t ω, 0 ≤ c t ω)
    {L : ℝ} (hL : ∀ θ a, a ∈ F.domain θ → ∀ i, |F.coefficient θ a i| ≤ L)
    (n : ℕ) :
    (∑ t ∈ range n, avg w (fun ω => c (t+1) ω*movement
      (state F T θ (rankVector R) c (t+1) ω) (state F T θ (rankVector R) c t ω))) ≤
    avg w (fun ω => F.value (θ 0 ω) (rankVector R 0 ω) (state F T θ (rankVector R) c 0 ω))-
    avg w (fun ω => F.value (θ n ω) (rankVector R n ω) (state F T θ (rankVector R) c n ω))+
    L*(∑ t ∈ range n, ∑ i, avg w (fun ω => |(R i).p (t+1) ω-(R i).before (t+1) ω|))+
    ∑ t ∈ range n, avg w (edit F T θ (rankVector R) c t) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [sum_range_succ]
      have hs := expected_payment_step F T hw R θ c H hH hr hθ hc hcn hL n
      linarith

/-- Uniform endpoint removal: a bound depending only on the fixed finite
family, not on the horizon or its law, contributes at most twice that bound. -/
theorem expected_payment_bounded (F : Family Θ I J) (T : Transport F) {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1) (R : I → FilteredRanks w)
    (θ : ℕ → Ω → Θ) (c : ℕ → Ω → ℝ)
    (H : ℕ → Ω → ℕ) (hH : ∀ i, (R i).history=H)
    (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hθ : ∀ t ω z, H t ω=H t z → θ t ω=θ t z)
    (hc : ∀ t, Adapted (H t) (c t)) (hcn : ∀ t ω, 0 ≤ c t ω)
    {L B : ℝ} (hL : ∀ θ a, a ∈ F.domain θ → ∀ i, |F.coefficient θ a i| ≤ L)
    (hB : ∀ θ p a, a ∈ F.domain θ → (∀ i, p i ∈ Set.Icc 0 1) → |F.value θ p a| ≤ B)
    (n : ℕ) :
    (∑ t ∈ range n, avg w (fun ω => c (t+1) ω*movement
      (state F T θ (rankVector R) c (t+1) ω) (state F T θ (rankVector R) c t ω))) ≤
    L*(∑ t ∈ range n, ∑ i, avg w (fun ω => |(R i).p (t+1) ω-(R i).before (t+1) ω|))+
    (∑ t ∈ range n, avg w (edit F T θ (rankVector R) c t))+2*B := by
  have hb (t : ℕ) (ω : Ω) := hB (θ t ω) (rankVector R t ω)
    (state F T θ (rankVector R) c t ω) (state_mem F T θ (rankVector R) c t ω)
    (fun i => (R i).range t ω)
  have htop := avg_mono hw (fun ω => (abs_le.mp (hb 0 ω)).2)
  have hbot := avg_mono hw (fun ω => (abs_le.mp (hb n ω)).1)
  rw [avg_const w hw1] at htop hbot
  have he := expected_payment F T hw R θ c H hH hr hθ hc hcn hL n
  linarith

/-- The rank inputs of the recursion can be instantiated directly from the
actual finite hidden counts, not from a postulated martingale interface. -/
def countRanks {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (H : ℕ → Ω → ℕ)
    (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    {k : ℕ} (N : ℕ → Ω → J → ℕ) : J × Fin k → FilteredRanks w :=
  fun ja => PosteriorRanks.rankProcess hw H hr (fun t ω => N t ω ja.1) ja.2.val

omit [Fintype J] in
lemma countRanks_history {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (H : ℕ → Ω → ℕ)
    (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    {k : ℕ} (N : ℕ → Ω → J → ℕ) (ja : J × Fin k) :
    (countRanks hw H hr N ja).history=H := rfl

lemma countRanks_drift {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (H : ℕ → Ω → ℕ)
    (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    {k : ℕ} (N : ℕ → Ω → J → ℕ) (hN : ∀ t ω j, N t ω j ≤ k) (t : ℕ) :
    (∑ ja : J × Fin k, avg w (fun ω => |(countRanks hw H hr N ja).p (t+1) ω-
      (countRanks hw H hr N ja).before (t+1) ω|)) ≤
      avg w (fun ω => ∑ j, |(N (t+1) ω j : ℝ)-N t ω j|) := by
  rw [Fintype.sum_prod_type,avg_sum_any]
  exact sum_le_sum fun j _ => PosteriorRanks.rankProcess_drift hw H hr
    (fun t ω => N t ω j) (fun t ω => hN t ω j) t

/-- Hidden-count variation is controlled by the explicit edit expression. -/


theorem hidden_count_payment {k : ℕ} (F : Family Θ (J × Fin k) J) (T : Transport F)
    {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1)
    (H : ℕ → Ω → ℕ) (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    (N : ℕ → Ω → J → ℕ) (hN : ∀ t ω j, N t ω j ≤ k)
    (θ : ℕ → Ω → Θ) (c : ℕ → Ω → ℝ)
    (hθ : ∀ t ω z, H t ω=H t z → θ t ω=θ t z)
    (hc : ∀ t, Adapted (H t) (c t)) (hcn : ∀ t ω, 0 ≤ c t ω)
    {L B : ℝ} (hLn : 0 ≤ L)
    (hL : ∀ θ a, a ∈ F.domain θ → ∀ i, |F.coefficient θ a i| ≤ L)
    (hB : ∀ θ p a, a ∈ F.domain θ → (∀ i, p i ∈ Set.Icc 0 1) → |F.value θ p a| ≤ B)
    (n : ℕ) :
    let R := countRanks hw H hr N
    (∑ t ∈ range n, avg w (fun ω => c (t+1) ω*movement
      (state F T θ (rankVector R) c (t+1) ω) (state F T θ (rankVector R) c t ω))) ≤
    L*(∑ t ∈ range n, avg w (fun ω => ∑ j, |(N (t+1) ω j : ℝ)-N t ω j|))+
    (∑ t ∈ range n, avg w (edit F T θ (rankVector R) c t))+2*B := by
  dsimp only
  have he := expected_payment_bounded F T hw hw1 (countRanks hw H hr N) θ c H
    (countRanks_history hw H hr N) hr hθ hc hcn hL hB n
  apply he.trans
  gcongr
  exact countRanks_drift hw H hr N hN _

end KServer.AdaptiveMinimization


/-! Actual zero-extension and synthetic-input operations in §04.  In particular
zero weight and singleton transitions are included, not divided away. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ChangingDomains
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

def variation (a b : J → ℝ) : ℝ := ∑ i, |a i-b i|

omit [DecidableEq J] in
lemma variation_self (a : J → ℝ) : variation a a=0 := by simp [variation]
omit [DecidableEq J] in
lemma variation_nonneg (a b : J → ℝ) : 0 ≤ variation a b :=
  sum_nonneg fun _ _ => abs_nonneg _
omit [DecidableEq J] in
lemma variation_triangle (a b c : J → ℝ) : variation a c ≤ variation a b+variation b c := by
  rw [variation,variation,variation,←sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le _ _ _

def simplex (A : Finset J) : Set (J → ℝ) :=
  {a | (∀ i, 0 ≤ a i) ∧ (∑ i, a i)=(if A.Nonempty then 1 else 0) ∧ ∀ i ∉ A, a i=0}

def canonical (A : Finset J) : J → ℝ :=
  if h : A.Nonempty then fun i => if i=h.choose then 1 else 0 else fun _ => 0

lemma canonical_mem (A : Finset J) : canonical A ∈ simplex A := by
  classical
  by_cases h : A.Nonempty
  · unfold canonical simplex
    rw [dite_eq_left h]
    refine ⟨fun i => by dsimp only; split_ifs <;> norm_num,?_,?_⟩
    · simp [h]
    · intro i hi
      have hn : i≠h.choose := by intro he; subst i; exact hi h.choose_spec
      simp [hn]
  · simp [canonical,simplex,h]

omit [DecidableEq J] in
lemma simplex_coordinate {A : Finset J} {a : J → ℝ} (ha : a ∈ simplex A) (i : J) :
    a i ∈ Set.Icc 0 1 := by
  refine ⟨ha.1 i,?_⟩
  have hh := single_le_sum (fun j _ => ha.1 j) (mem_univ i)
  rw [ha.2.1] at hh
  split_ifs at hh <;> linarith

omit [DecidableEq J] in
lemma simplex_compact (A : Finset J) : IsCompact (simplex A) := by
  have hc : IsClosed (simplex A) := by
    change IsClosed ({a : J → ℝ | ∀ i, 0 ≤ a i} ∩
      ({a : J → ℝ | ∑ i, a i=(if A.Nonempty then 1 else 0)} ∩
      {a : J → ℝ | ∀ i ∉ A, a i=0}))
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply i) continuous_const
  apply (isCompact_pi_infinite fun _ : J => isCompact_Icc (a := (0:ℝ)) (b := 1)).of_isClosed_subset hc
  intro a ha i
  exact simplex_coordinate ha i

omit [DecidableEq J] in
lemma simplex_variation {A B : Finset J} {a b : J → ℝ}
    (ha : a ∈ simplex A) (hb : b ∈ simplex B) : variation a b ≤ 2 := by
  calc _ ≤ ∑ i, (a i+b i) := sum_le_sum fun i _ => by
        calc |a i-b i| ≤ |a i|+|b i| := abs_sub _ _
             _ = _ := by rw [abs_of_nonneg (ha.1 i),abs_of_nonneg (hb.1 i)]
       _ ≤ 2 := by
        rw [sum_add_distrib,ha.2.1,hb.2.1]
        split_ifs <;> norm_num

/-- Deletion plus zero insertion. At zero synthetic total choose a fresh
canonical vector; this has exactly zero synthetic weighted movement. -/
def transposeSimplex (A : Finset J) (S : ℝ) (a : J → ℝ) : J → ℝ :=
  if S=0 then canonical A else a

lemma transposeSimplex_mem {A B : Finset J} {S : ℝ} {a v γ : J → ℝ}
    (hA : A.Nonempty) (hB : B.Nonempty) (ha : a ∈ simplex A) (hS : 0 ≤ S)
    (hc : ∀ i, S*a i ≤ γ i*v i) (hv : ∀ i ∉ B, v i=0) :
    transposeSimplex B S a ∈ simplex B := by
  by_cases hs : S=0
  · simpa [transposeSimplex,hs] using canonical_mem B
  · have hsp : 0 < S := lt_of_le_of_ne hS (Ne.symm hs)
    simp only [transposeSimplex,ite_eq_right hs]
    refine ⟨ha.1,?_,?_⟩
    · simpa only [ite_eq_left hA,ite_eq_left hB] using ha.2.1
    · intro i hi
      have hh := hc i
      rw [hv i hi,mul_zero] at hh
      nlinarith [ha.1 i]

lemma transposeSimplex_payment (A : Finset J) (S : ℝ) (a : J → ℝ) :
    S*variation (transposeSimplex A S a) a=0 := by
  by_cases h : S=0
  · simp [h]
  · simp [transposeSimplex,h,variation_self]

omit [DecidableEq J] in
/-- Literal §04 weight comparison for the prepared and final minimizers. -/
lemma prepared_weight_comparison {A₀ A₁ A₂ : Finset J} {a₀ a₁ a₂ a₃ : J → ℝ}
    (ha₀ : a₀ ∈ simplex A₀) (ha₁ : a₁ ∈ simplex A₁)
    (ha₂ : a₂ ∈ simplex A₂)
    {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (hzero : S*variation a₂ a₁=0) :
    T*variation a₃ a₀ ≤ S*variation a₁ a₀+T*variation a₃ a₂+4*(T-S) := by
  have ht := variation_triangle a₃ a₂ a₀
  have ht' := variation_triangle a₂ a₁ a₀
  have hd₁ := simplex_variation ha₁ ha₀
  have hd₂ := simplex_variation ha₂ ha₁
  have htn : 0 ≤ T := hS.trans hST
  have hp := mul_le_mul_of_nonneg_left ht htn
  have hp' := mul_le_mul_of_nonneg_left ht' htn
  have hδ : 0 ≤ T-S := sub_nonneg.mpr hST
  have h₁ := mul_le_mul_of_nonneg_left hd₁ hδ
  have h₂ := mul_le_mul_of_nonneg_left hd₂ hδ
  nlinarith

def sideDomain (A : Finset J) (W : ℝ) : Set (J → ℝ) :=
  {a | (∀ i, 0 ≤ a i) ∧ (∑ i, a i) ≤ W ∧ ∀ i ∉ A, a i=0}

def transposeSide (A : Finset J) (a : J → ℝ) : J → ℝ := fun i => if i∈A then a i else 0

lemma transposeSide_mem {A B : Finset J} {W : ℝ} {a : J → ℝ}
    (ha : a ∈ sideDomain A W) : transposeSide B a ∈ sideDomain B W := by
  refine ⟨?_,?_,?_⟩
  · intro i
    simp only [transposeSide]
    split_ifs
    · exact ha.1 i
    · exact le_rfl
  · apply le_trans _ ha.2.1
    exact sum_le_sum fun i _ => by simp only [transposeSide]; split_ifs; rfl; exact ha.1 i
  · intro i hi; simp [transposeSide,hi]

lemma transposeSide_payment {B : Finset J} {D : ℝ} {a v γ : J → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hD : 0 ≤ D)
    (hc : ∀ i, D*a i ≤ γ i*v i) (hv : ∀ i ∉ B, v i=0) :
    D*variation (transposeSide B a) a=0 := by
  by_cases hd : D=0
  · simp [hd]
  · have hdp : 0 < D := lt_of_le_of_ne hD (Ne.symm hd)
    have he : transposeSide B a=a := by
      funext i
      by_cases hi : i∈B
      · simp [transposeSide,hi]
      · have hh := hc i
        rw [hv i hi,mul_zero] at hh
        have haz : a i=0 := by nlinarith [ha i]
        simp [transposeSide,hi,haz]
    simp [he,variation_self]

def core (f : J → R → Bool) (p : J → R → ℝ) (i : J) : ℝ :=
  ∑ a, if f i a then p i a else 0

def syntheticFlags (A B : Finset J) (f : J → R → Bool) : J → R → Bool :=
  fun i a => if i∈A∩B then f i a else false

def changedFlags (f g : J → R → Bool) : ℝ :=
  ∑ i, ∑ a, if f i a=g i a then 0 else 1

omit [Fintype J] [DecidableEq J] in
lemma core_nonneg {f : J → R → Bool} {p : J → R → ℝ} (hp : ∀ i a, 0 ≤ p i a) (i : J) :
    0 ≤ core f p i := by
  apply sum_nonneg
  intro a _
  split_ifs
  · exact hp i a
  · rfl

omit [Fintype J] in
lemma synthetic_zero {A B : Finset J} (f : J → R → Bool) (p : J → R → ℝ)
    {i : J} (hi : i∉A∩B) : core (syntheticFlags A B f) p i=0 := by
  simp [core,syntheticFlags,hi]

omit [Fintype J] [Fintype R] in
lemma synthetic_error_terms {A B : Finset J} {f g : J → R → Bool}
    {p : J → R → ℝ} (hp : ∀ i a, p i a ∈ Set.Icc 0 1)
    (hf : ∀ i ∉ A, ∀ a, f i a=false) (hg : ∀ i ∉ B, ∀ a, g i a=false)
    (i : J) (a : R) :
    |(if f i a then p i a else 0)-(if syntheticFlags A B g i a then p i a else 0)| ≤
      (if f i a=g i a then (0:ℝ) else 1) ∧
    |(if g i a then p i a else 0)-(if syntheticFlags A B g i a then p i a else 0)| ≤
      (if f i a=g i a then (0:ℝ) else 1) := by
  have hn := (hp i a).1
  have hu := (hp i a).2
  by_cases hi : i∈A <;> by_cases hj : i∈B
  · cases hfi : f i a <;> cases hgi : g i a <;>
      simp [syntheticFlags,hi,hj,hgi,abs_of_nonneg hn,abs_of_nonpos (neg_nonpos.mpr hn),hu]
  · have hgi := hg i hj a
    cases hfi : f i a <;>
      simp [syntheticFlags,hi,hj,hgi,abs_of_nonneg hn,hu]
  · have hfi := hf i hi a
    cases hgi : g i a <;>
      simp [syntheticFlags,hi,hj,hfi,abs_of_nonneg hn,hu]
  · have hfi := hf i hi a
    have hgi := hg i hj a
    simp [syntheticFlags,hi,hj,hfi,hgi]

/-- Both synthetic-core discrepancies are paid by the actual number of flags
that changed, even when the observed rank probabilities changed drastically. -/
theorem synthetic_errors {A B : Finset J} {f g : J → R → Bool}
    {p : J → R → ℝ} (hp : ∀ i a, p i a ∈ Set.Icc 0 1)
    (hf : ∀ i ∉ A, ∀ a, f i a=false) (hg : ∀ i ∉ B, ∀ a, g i a=false) :
    variation (core f p) (core (syntheticFlags A B g) p) ≤ changedFlags f g ∧
    variation (core g p) (core (syntheticFlags A B g) p) ≤ changedFlags f g := by
  constructor
  all_goals
    apply sum_le_sum
    intro i _
    unfold core
    rw [←sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro a _
  · exact (synthetic_error_terms hp hf hg i a).1
  · exact (synthetic_error_terms hp hf hg i a).2

lemma synthetic_total {A B : Finset J} {g : J → R → Bool} {p : J → R → ℝ}
    (hp : ∀ i a, 0 ≤ p i a) :
    0 ≤ (∑ i, core g p i)-(∑ i, core (syntheticFlags A B g) p i) := by
  apply sub_nonneg.mpr
  apply sum_le_sum
  intro i _
  by_cases hi : i∈A∩B
  · simp [core,syntheticFlags,hi]
  · rw [synthetic_zero g p hi]
    exact core_nonneg hp i

end KServer.ChangingDomains

end
end

end OAI
