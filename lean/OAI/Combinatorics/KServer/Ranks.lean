import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.RankTracking

variable {Ω : Type*} [Fintype Ω]

def avg (w : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, w ω*f ω

lemma avg_add (w f g : Ω → ℝ) : avg w (fun ω => f ω+g ω)=avg w f+avg w g := by
  simp [avg,mul_add,sum_add_distrib]
lemma avg_sub (w f g : Ω → ℝ) : avg w (fun ω => f ω-g ω)=avg w f-avg w g := by
  simp [avg,mul_sub,sum_sub_distrib]
lemma avg_mul (w f : Ω → ℝ) (c : ℝ) : avg w (fun ω => c*f ω)=c*avg w f := by
  simp only [avg,mul_sum,mul_left_comm (w _) c]
lemma avg_sum (w : Ω → ℝ) {ι : Type*} [Fintype ι] (f : ι → Ω → ℝ) :
    avg w (fun ω => ∑ i, f i ω)=∑ i, avg w (f i) := by
  simp only [avg,mul_sum]; rw [sum_comm]
lemma avg_mono {w f g : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (h : ∀ ω, f ω ≤ g ω) :
    avg w f ≤ avg w g := sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hw ω)
lemma avg_const (w : Ω → ℝ) (hw : ∑ ω, w ω=1) (c : ℝ) : avg w (fun _ => c)=c := by
  simp [avg,←sum_mul,hw]

/-- Functions known from the observed finite history label. -/
def Adapted (H : Ω → ℕ) (f : Ω → ℝ) : Prop := ∀ ω ω', H ω=H ω' → f ω=f ω'

/-- Increasing history information, adapted ranks, and the literal finite
conditional tower relation for old counts under the new observation. -/
structure FilteredRanks (w : Ω → ℝ) where
  history : ℕ → Ω → ℕ
  refines : ∀ t ω ω', history (t+1) ω=history (t+1) ω' → history t ω=history t ω'
  p : ℕ → Ω → ℝ
  before : ℕ → Ω → ℝ
  range : ∀ t ω, p t ω ∈ Set.Icc 0 1
  before_range : ∀ t ω, before t ω ∈ Set.Icc 0 1
  adapted : ∀ t, Adapted (history t) (p t)
  filtering : ∀ t h, ∑ ω ∈ Finset.univ.filter (fun ω => history t ω=h),
    w ω*(before (t+1) ω-p t ω)=0

lemma fiber_weighted_zero (H : Ω → ℕ) (f g : Ω → ℝ)
    (hf : Adapted H f) (hg : ∀ h, ∑ ω ∈ Finset.univ.filter (fun ω => H ω=h), g ω=0) :
    ∑ ω, f ω*g ω=0 := by
  classical
  let c : ℕ → ℝ := fun h => if hh : ∃ ω, H ω=h then f hh.choose else 0
  have hc : ∀ ω, f ω=c (H ω) := by
    intro ω
    dsimp [c]
    rw [dite_eq_left ⟨ω,rfl⟩]
    exact hf ω _ (Exists.choose_spec (show ∃ ω', H ω'=H ω from ⟨ω,rfl⟩)).symm
  have hs : (∑ ω, f ω*g ω) =
      ∑ h ∈ Finset.univ.image H, ∑ ω ∈ Finset.univ.filter (fun ω => H ω=h), f ω*g ω := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (by intro ω _; exact Finset.mem_image.mpr ⟨ω,Finset.mem_univ _,rfl⟩) _
  rw [hs]
  apply sum_eq_zero
  intro h _
  calc _ = c h*(∑ ω ∈ Finset.univ.filter (fun ω => H ω=h), g ω) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro ω hω
        rw [hc ω,(Finset.mem_filter.mp hω).2]
       _ = 0 := by rw [hg,mul_zero]

lemma filtering_affine {w : Ω → ℝ} (R : FilteredRanks w) (t : ℕ) (f : Ω → ℝ)
    (hf : Adapted (R.history t) f) :
    avg w (fun ω => f ω*(R.before (t+1) ω-R.p t ω))=0 := by
  unfold avg
  simp_rw [mul_left_comm (w _) (f _)]
  exact fiber_weighted_zero (R.history t) f _ hf (R.filtering t)

end KServer.RankTracking

/-! Construction of the rank martingales from the actual finite hidden law.
No filtering identity is postulated in the construction below. -/
namespace KServer.PosteriorRanks
open Finset
open RankTracking
variable {Ω : Type*} [Fintype Ω]

def fiber (H : Ω → ℕ) (h : ℕ) : Finset Ω := univ.filter (fun ω => H ω=h)
def mass (w : Ω → ℝ) (H : Ω → ℕ) (h : ℕ) : ℝ := ∑ ω ∈ fiber H h, w ω
def numerator (w : Ω → ℝ) (H : Ω → ℕ) (f : Ω → ℝ) (h : ℕ) : ℝ :=
  ∑ ω ∈ fiber H h, w ω*f ω

def posterior (w : Ω → ℝ) (H : Ω → ℕ) (f : Ω → ℝ) (ω : Ω) : ℝ :=
  numerator w H f (H ω) / mass w H (H ω)

lemma mass_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (H h) : 0 ≤ mass w H h :=
  sum_nonneg fun ω _ => hw ω

lemma numerator_zero {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {H h}
    (hm : mass w H h=0) (f : Ω → ℝ) : numerator w H f h=0 := by
  have hzero : ∀ ω ∈ fiber H h, w ω=0 :=
    (sum_eq_zero_iff_of_nonneg (fun ω _ => hw ω)).mp hm
  exact sum_eq_zero fun ω hω => by rw [hzero ω hω,zero_mul]

lemma posterior_adapted (w : Ω → ℝ) (H : Ω → ℕ) (f : Ω → ℝ) :
    Adapted H (posterior w H f) := by
  intro ω ω' hh
  simp only [posterior,hh]

lemma posterior_range {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : Ω → ℕ) {f : Ω → ℝ} (hf : ∀ ω, f ω ∈ Set.Icc 0 1) (ω : Ω) :
    posterior w H f ω ∈ Set.Icc 0 1 := by
  have hm := mass_nonneg hw H (H ω)
  have hn : 0 ≤ numerator w H f (H ω) := sum_nonneg fun z _ => mul_nonneg (hw z) (hf z).1
  have hnle : numerator w H f (H ω) ≤ mass w H (H ω) := by
    apply sum_le_sum
    intro z _
    exact mul_le_of_le_one_right (hw z) (hf z).2
  constructor
  · exact div_nonneg hn hm
  · by_cases hz : mass w H (H ω)=0
    · simp [posterior,hz]
    · exact (div_le_one (lt_of_le_of_ne hm (Ne.symm hz))).mpr hnle

lemma fiber_posterior {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : Ω → ℕ) (f : Ω → ℝ) (h : ℕ) :
    ∑ ω ∈ fiber H h, w ω*posterior w H f ω = numerator w H f h := by
  calc _ = mass w H h*(numerator w H f h/mass w H h) := by
        unfold mass
        rw [sum_mul]
        apply sum_congr rfl
        intro ω hω
        simp only [fiber,mem_filter,mem_univ,true_and] at hω
        rw [posterior,hω]
        rfl
       _ = numerator w H f h := by
        by_cases hm : mass w H h=0
        · rw [hm,numerator_zero hw hm f]; norm_num
        · field_simp

lemma fiber_difference {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : Ω → ℕ) (f : Ω → ℝ) (h : ℕ) :
    ∑ ω ∈ fiber H h, w ω*(posterior w H f ω-f ω)=0 := by
  simp only [mul_sub,sum_sub_distrib,fiber_posterior hw,numerator,sub_self]

lemma weighted_posterior {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : Ω → ℕ) (f g : Ω → ℝ) (hg : Adapted H g) :
    avg w (fun ω => g ω*posterior w H f ω)=avg w (fun ω => g ω*f ω) := by
  have hh := fiber_weighted_zero H g (fun ω => w ω*(posterior w H f ω-f ω)) hg
    (fiber_difference hw H f)
  simp only [mul_sub,mul_left_comm (g _) (w _),sum_sub_distrib] at hh
  exact sub_eq_zero.mp hh

lemma posterior_avg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (H : Ω → ℕ) (f : Ω → ℝ) :
    avg w (posterior w H f)=avg w f := by
  simpa only [one_mul] using weighted_posterior hw H f (fun _ => 1) (by intro _ _ _; rfl)

lemma filtered_fiber {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (H H' : Ω → ℕ)
    (hr : ∀ ω ω', H' ω=H' ω' → H ω=H ω') (f : Ω → ℝ) (h : ℕ) :
    ∑ ω ∈ fiber H h, w ω*(posterior w H' f ω-posterior w H f ω)=0 := by
  let g := fun ω => if H ω=h then (1:ℝ) else 0
  have hga : Adapted H g := by intro ω z hz; simp [g,hz]
  have hgb : Adapted H' g := by intro ω z hz; simp [g,hr ω z hz]
  have ha := weighted_posterior hw H f g hga
  have hb := weighted_posterior hw H' f g hgb
  have hh : avg w (fun ω => g ω*posterior w H' f ω)-
      avg w (fun ω => g ω*posterior w H f ω)=0 := by rw [ha,hb,sub_self]
  rw [←avg_sub] at hh
  unfold avg at hh
  simpa only [fiber,sum_filter,g,ite_mul,one_mul,zero_mul,ite_sub_ite,sub_zero,
    mul_ite,mul_zero] using hh

/-- The true post-filtering, post-drift ranks and the filtered old ranks on an
arbitrary finite experiment with increasing observations. -/
def rank (N : Ω → ℕ) (a : ℕ) (ω : Ω) : ℝ := if N ω ≤ a then 1 else 0
omit [Fintype Ω] in
lemma rank_range (N : Ω → ℕ) (a : ℕ) (ω : Ω) : rank N a ω ∈ Set.Icc 0 1 := by
  unfold rank; split_ifs <;> norm_num

def rankProcess {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : ℕ → Ω → ℕ) (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    (N : ℕ → Ω → ℕ) (a : ℕ) : FilteredRanks w where
  history := H
  refines := hr
  p := fun t => posterior w (H t) (rank (N t) a)
  before := fun t => posterior w (H t) (rank (N (t-1)) a)
  range := fun t ω => posterior_range hw (H t) (rank_range (N t) a) ω
  before_range := fun t ω => posterior_range hw (H t) (rank_range (N (t-1)) a) ω
  adapted := fun t => posterior_adapted w (H t) (rank (N t) a)
  filtering := by
    intro t h
    simp only [Nat.add_sub_cancel]
    exact filtered_fiber hw (H t) (H (t+1)) (hr t) (rank (N t) a) h

lemma posterior_sub (w : Ω → ℝ) (H : Ω → ℕ) (f g : Ω → ℝ) (ω : Ω) :
    posterior w H (fun z => f z-g z) ω = posterior w H f ω-posterior w H g ω := by
  simp only [posterior,numerator,mul_sub,sum_sub_distrib,sub_div]

lemma abs_posterior_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : Ω → ℕ) (f : Ω → ℝ) (ω : Ω) :
    |posterior w H f ω| ≤ posterior w H (fun z => |f z|) ω := by
  have hn : |numerator w H f (H ω)| ≤ numerator w H (fun z => |f z|) (H ω) := by
    unfold numerator
    calc _ ≤ ∑ z ∈ fiber H (H ω), |w z*f z| := abs_sum_le_sum_abs _ _
         _ = _ := by apply sum_congr rfl; intro z _; rw [abs_mul,abs_of_nonneg (hw z)]
  unfold posterior
  rw [abs_div,abs_of_nonneg (mass_nonneg hw H (H ω))]
  exact div_le_div_of_nonneg_right hn (mass_nonneg hw H (H ω))

/-- Conditional averaging cannot increase the drift, even at zero-mass
histories, where the quotient convention simply chooses zero. -/
theorem posterior_drift {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : Ω → ℕ) (f g : Ω → ℝ) :
    avg w (fun ω => |posterior w H f ω-posterior w H g ω|) ≤
      avg w (fun ω => |f ω-g ω|) := by
  calc _ = avg w (fun ω => |posterior w H (fun z => f z-g z) ω|) := by simp only [posterior_sub]
       _ ≤ avg w (posterior w H (fun z => |f z-g z|)) :=
        avg_mono hw (abs_posterior_le hw H (fun z => f z-g z))
       _ = _ := posterior_avg hw H _

lemma sum_below {k N : ℕ} (hN : N ≤ k) :
    (∑ a : Fin k, if a.val < N then (1 : ℝ) else 0) = N := by
  rw [Fin.sum_univ_eq_sum_range (fun a => if a < N then (1 : ℝ) else 0), ← sum_filter]
  have h : (range k).filter (fun a => a < N) = range N := by
    ext a
    simp only [mem_filter, mem_range]
    omega
  rw [h]
  simp

lemma sum_above {k N : ℕ} (hN : N ≤ k) :
    (∑ a : Fin k, if N ≤ a.val then (1 : ℝ) else 0) = (k:ℝ)-N := by
  have hsum : (∑ a : Fin k, if N ≤ a.val then (1 : ℝ) else 0)+
      (∑ a : Fin k, if a.val < N then (1 : ℝ) else 0) = k := by
    rw [←sum_add_distrib]
    have hterm (a : Fin k) : (if N ≤ a.val then (1:ℝ) else 0)+(if a.val < N then (1:ℝ) else 0)=1 := by
      split_ifs <;> first | (exfalso; omega) | norm_num
    simp_rw [hterm]
    simp
  rw [sum_below hN] at hsum
  linarith

lemma indicator_count_distance {k n m : ℕ} (hn : n ≤ k) (hm : m ≤ k) :
    (∑ a : Fin k, |(if n ≤ a.val then (1:ℝ) else 0)-(if m ≤ a.val then (1:ℝ) else 0)|) =
      |(n:ℝ)-m| := by
  wlog hnm : n ≤ m generalizing n m
  · rw [abs_sub_comm (n:ℝ) m]
    rw [←this hm hn (le_of_not_ge hnm)]
    exact sum_congr rfl fun a _ => abs_sub_comm _ _
  have hnmR : (n:ℝ) ≤ m := by exact_mod_cast hnm
  calc _ = ∑ a : Fin k, ((if n ≤ a.val then (1:ℝ) else 0)-(if m ≤ a.val then (1:ℝ) else 0)) := by
        apply sum_congr rfl
        intro a _
        apply abs_of_nonneg
        split_ifs <;> first | (exfalso; omega) | norm_num
       _ = (m:ℝ)-n := by rw [sum_sub_distrib,sum_above hn,sum_above hm]; ring
       _ = |(n:ℝ)-m| := by rw [abs_of_nonpos (sub_nonpos.mpr hnmR)]; ring

/-- The exact §03 all-rank drift budget, derived from the finite hidden count
process rather than assumed as an interface. -/
theorem rank_drift_count {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : Ω → ℕ) {k : ℕ} (N M : Ω → ℕ) (hN : ∀ ω, N ω ≤ k) (hM : ∀ ω, M ω ≤ k) :
    (∑ a : Fin k, avg w (fun ω => |posterior w H (rank N a.val) ω-
      posterior w H (rank M a.val) ω|)) ≤ avg w (fun ω => |(N ω:ℝ)-M ω|) := by
  calc _ ≤ ∑ a : Fin k, avg w (fun ω => |rank N a.val ω-rank M a.val ω|) :=
          sum_le_sum fun a _ => posterior_drift hw H _ _
       _ = avg w (fun ω => ∑ a : Fin k, |rank N a.val ω-rank M a.val ω|) :=
          (avg_sum w _).symm
       _ = _ := by
          congr 1
          funext ω
          exact indicator_count_distance (hN ω) (hM ω)

/-- The instantiated process defined above obeys the source estimate with
actual one-step hidden-count motion on its right-hand side. -/
theorem rankProcess_drift {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : ℕ → Ω → ℕ) (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    {k : ℕ} (N : ℕ → Ω → ℕ) (hN : ∀ t ω, N t ω ≤ k) (t : ℕ) :
    (∑ a : Fin k, avg w (fun ω => |(rankProcess hw H hr N a.val).p (t+1) ω-
      (rankProcess hw H hr N a.val).before (t+1) ω|)) ≤
      avg w (fun ω => |(N (t+1) ω:ℝ)-N t ω|) := by
  simpa only [rankProcess,Nat.add_sub_cancel] using
    rank_drift_count hw (H (t+1)) (N (t+1)) (N t) (hN (t+1)) (hN t)

end KServer.PosteriorRanks


/-! ## The actual finite hidden experiment of §02

The input is drawn once. Its selected optimum is hidden, whereas a finite
independent partition tape and the true request prefix are observed. No
conditioning on rounding outcomes enters this experiment. -/
namespace KServer.PosteriorRanks
variable {Ω : Type*} [Fintype Ω]

lemma mass_pos_of_weight {w : Ω → ℝ} (hw : ∀ ω, 0≤w ω) (H : Ω → ℕ)
    (ω : Ω) (hω : 0<w ω) : 0 < mass w H (H ω) := by
  apply hω.trans_le
  exact single_le_sum (fun z _ => hw z) (by simp [fiber])

lemma posterior_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0≤w ω) (H : Ω → ℕ)
    {f : Ω → ℝ} (hf : ∀ ω, 0≤f ω) (ω : Ω) : 0≤posterior w H f ω :=
  div_nonneg (sum_nonneg fun z _ => mul_nonneg (hw z) (hf z)) (mass_nonneg hw H _)

lemma posterior_sum {I : Type*} [Fintype I] (w : Ω → ℝ) (H : Ω → ℕ)
    (f : I → Ω → ℝ) (ω : Ω) :
    posterior w H (fun z => ∑ i,f i z) ω=∑ i,posterior w H (f i) ω := by
  simp only [posterior,numerator,mul_sum,sum_div]
  rw [sum_comm]

lemma posterior_fiber_const {w : Ω → ℝ} {H : Ω → ℕ} {f : Ω → ℝ}
    (ω : Ω) {c : ℝ} (hf : ∀ z,H z=H ω → f z=c) (hm : mass w H (H ω)≠0) :
    posterior w H f ω=c := by
  have hn : numerator w H f (H ω)=mass w H (H ω)*c := by
    unfold numerator mass
    rw [sum_mul]
    apply sum_congr rfl
    intro z hz
    rw [hf z (mem_filter.mp hz).2]
  rw [posterior,hn,mul_div_cancel_left₀ _ hm]

lemma posterior_mono_fiber {w : Ω → ℝ} (hw : ∀ ω,0≤w ω) {H : Ω → ℕ}
    {f g : Ω → ℝ} (ω : Ω) (hfg : ∀ z,H z=H ω → f z≤g z) :
    posterior w H f ω≤posterior w H g ω := by
  apply div_le_div_of_nonneg_right _ (mass_nonneg hw H _)
  apply sum_le_sum
  intro z hz
  exact mul_le_mul_of_nonneg_left (hfg z (mem_filter.mp hz).2) (hw z)

lemma posterior_add (w : Ω → ℝ) (H : Ω → ℕ) (f g : Ω → ℝ) (ω : Ω) :
    posterior w H (fun z => f z+g z) ω=posterior w H f ω+posterior w H g ω := by
  simp [posterior,numerator,mul_add,sum_add_distrib,add_div]

lemma posterior_mul (w : Ω → ℝ) (H : Ω → ℕ) (f : Ω → ℝ) (c : ℝ) (ω : Ω) :
    posterior w H (fun z => f z*c) ω=posterior w H f ω*c := by
  simp only [posterior,numerator,←mul_assoc,←sum_mul]
  ring

end KServer.PosteriorRanks

end

end OAI
