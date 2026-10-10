import Mathlib
import OAI.Probability.SKFluctuations.NonnegativeProfileValueStep

namespace OAI

/-! Scalar Source Jet. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

noncomputable def scalarSourceJet (steps : List (GaussianStep (Fin 1))) : ℕ → ℝ → ℝ
  | 0,x => gaussianHierarchy (fun _ : Bool => (1/2:ℝ)) scalarFeature steps (fun _ => x)
  | k+1,x => ReplicaTree.sourceJet (fun _ : Bool => (1/2:ℝ)) scalarFeature 0
      (List.replicate k (fun _ => (1:ℝ))) (ReplicaTree.single steps)
      (fun σ => scalarFeature (ReplicaTree.singleEquiv (S := Bool) steps σ) (fun _ => 1)) (fun _ => x)

theorem scalarFeature_one_abs (σ : Bool) :
    |scalarFeature σ (fun _ => 1)| = 1 := by
  cases σ <;> norm_num [scalarFeature]

theorem scalarSourceJet_hasDerivAt {steps : List (GaussianStep (Fin 1))}
    (ha : OrderedSteps 0 steps) (k : ℕ) (x : ℝ) :
    HasDerivAt (scalarSourceJet steps k) (scalarSourceJet steps (k+1) x) x := by
  have hw (σ : Bool) : (0:ℝ) < 1/2 := by norm_num
  have he (s : ℝ) : (0 : Fin 1 → ℝ)+s • (fun _ => (1:ℝ)) = (fun _ => s) := by
    ext i
    simp
  change HasDerivAt (fun y => scalarSourceJet steps k y) (scalarSourceJet steps (k+1) x) x
  cases k with
  | zero =>
    have h := gaussianHierarchy_hasDerivAt hw scalarFeature steps ha 0 (fun _ => 1) x
    change HasDerivAt (fun s => gaussianHierarchy (fun _ : Bool => (1/2:ℝ)) scalarFeature steps (fun _ => s))
      ((ReplicaTree.single steps).expect (fun _ : Bool => (1/2:ℝ)) scalarFeature
        (fun σ => scalarFeature (ReplicaTree.singleEquiv (S := Bool) steps σ) (fun _ => 1)) (fun _ => x)) x
    rw [ReplicaTree.single_expect hw scalarFeature steps ha (fun σ => scalarFeature σ (fun _ => 1))]
    simpa only [he] using h
  | succ k =>
    have h := ReplicaTree.sourceJet_hasDerivAt hw scalarFeature
      (List.replicate k (fun _ => (1:ℝ))) (ReplicaTree.single steps) ha
      (fun σ => scalarFeature (ReplicaTree.singleEquiv (S := Bool) steps σ) (fun _ => 1))
      (fun _ => 1) 0 x
    simpa only [he,scalarSourceJet,List.replicate_succ'] using h

theorem scalarSourceJet_bound {steps : List (GaussianStep (Fin 1))}
    (ha : OrderedSteps 0 steps) (k : ℕ) (x : ℝ) :
    |scalarSourceJet steps (k+1) x| ≤ (ReplicaTree.attachmentCount 1 k:ℝ) := by
  have hw (σ : Bool) : (0:ℝ) < 1/2 := by norm_num
  have hp (σ : (ReplicaTree.single (S := Bool) steps).Assignment) :
      |scalarFeature (ReplicaTree.singleEquiv (S := Bool) steps σ) (fun _ => 1)| ≤ 1 :=
    (scalarFeature_one_abs _).le
  have h := ReplicaTree.sourceJet_abs_le hw scalarFeature (List.replicate k (fun _ => (1:ℝ)))
    (ReplicaTree.single steps) ha (r := 1) (by rw [ReplicaTree.single_leaves])
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1) hp
    (fun v hv σ => by rw [List.eq_of_mem_replicate hv]; exact (scalarFeature_one_abs σ).le) (fun _ => x)
  simpa only [scalarSourceJet,List.length_replicate,one_pow,mul_one] using h

 
def heatSteps {ι : Type*} (cs : List HeatClock) : List (GaussianStep ι) :=
  cs.map (fun c => (c.mass,fun _ => c.time))

theorem scalar_schedule_eq_hierarchy (cs : List HeatClock) (x : Fin 1 → ℝ) :
    (scalarTerminal.schedule cs).F x =
      gaussianHierarchy (fun _ : Bool => (1/2:ℝ)) scalarFeature (heatSteps cs) x := by
  induction cs generalizing x with
  | nil =>
    change spinLogPartition (fun _ : Bool => (1/2:ℝ)) scalarFeature (0+x) = _
    rw [zero_add]
    rfl
  | cons c cs ih =>
    change clockContinuation c.mass (scalarTerminal.schedule cs).F c.time x = _
    unfold clockContinuation
    rw [funext ih]
    simp only [Real.toNNReal_coe]
    rfl

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

variable {ι : Type*}

theorem OrderedSteps.lower {a b : ℝ} {steps : List (GaussianStep ι)}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : OrderedSteps b steps) : OrderedSteps a steps := by
  cases steps with
  | nil => exact ⟨ha,hab.trans hb.2⟩
  | cons st tail => exact ⟨ha,hab.trans hb.2.1,hb.2.2⟩

theorem OrderedSteps.append_bound {a b : ℝ} {xs ys : List (GaussianStep ι)}
    (hx : OrderedSteps a xs) (hab : a ≤ b) (hxb : ∀ st ∈ xs, st.1 ≤ b)
    (hy : OrderedSteps b ys) : OrderedSteps a (xs++ys) := by
  induction xs generalizing a with
  | nil => exact hy.lower hx.1 hab
  | cons st xs ih =>
    exact ⟨hx.1,hx.2.1,hx.2.2.1,ih hx.2.2.2 (hxb st (List.mem_cons_self ..))
      (fun t ht => hxb t (List.mem_cons_of_mem st ht))⟩

theorem PositiveMassProfile.grid_mass_bounds (α : PositiveMassProfile)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) {c : HeatClock} (hc : c ∈ α.grid l t k) :
    α.mass l ≤ c.mass ∧ c.mass ≤ α.mass (l+t) := by
  induction k generalizing l t with
  | zero =>
    simp only [PositiveMassProfile.grid,List.mem_singleton] at hc
    subst c
    exact ⟨le_rfl,α.monotone (le_add_of_nonneg_right t.coe_nonneg)⟩
  | succ k ih =>
    simp only [PositiveMassProfile.grid,List.mem_append] at hc
    have hm : l ≤ l+(t:ℝ)/2 := by linarith [t.coe_nonneg]
    have he : l+(t:ℝ)/2 ≤ l+t := by linarith [t.coe_nonneg]
    have heq : l+(t:ℝ)/2+((t/2:ℝ≥0):ℝ) = l+t := by
      simp only [NNReal.coe_div,NNReal.coe_ofNat]
      ring
    rcases hc with hc|hc
    · have h := ih l (t/2) hc
      exact ⟨h.1,h.2.trans (α.monotone he)⟩
    · have h := ih (l+(t:ℝ)/2) (t/2) hc
      rw [heq] at h
      exact ⟨(α.monotone hm).trans h.1,h.2⟩

theorem PositiveMassProfile.grid_ordered (α : PositiveMassProfile)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) {a : ℝ} (ha : 0 ≤ a) (hal : a ≤ α.mass l)
    (h1 : α.mass (l+t) ≤ 1) : OrderedSteps a (heatSteps (ι := ι) (α.grid l t k)) := by
  induction k generalizing a l t with
  | zero =>
    exact ⟨ha,hal,α.positive l,(α.positive l).le,
      (α.monotone (le_add_of_nonneg_right t.coe_nonneg)).trans h1⟩
  | succ k ih =>
    have hm : l ≤ l+(t:ℝ)/2 := by linarith [t.coe_nonneg]
    have he : l+(t:ℝ)/2 ≤ l+t := by linarith [t.coe_nonneg]
    have heq : l+(t:ℝ)/2+((t/2:ℝ≥0):ℝ) = l+t := by
      simp only [NNReal.coe_div,NNReal.coe_ofNat]
      ring
    change OrderedSteps a ((α.grid l (t/2) k ++ α.grid (l+(t:ℝ)/2) (t/2) k).map _)
    rw [List.map_append]
    apply OrderedSteps.append_bound (b := α.mass (l+(t:ℝ)/2))
      (ih l (t/2) ha hal ((α.monotone he).trans h1)) (hal.trans (α.monotone hm))
    · intro st hst
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hst
      exact (α.grid_mass_bounds l (t/2) k hc).2
    · apply ih (l+(t:ℝ)/2) (t/2) (α.positive _).le le_rfl
      rwa [heq]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

noncomputable def NonnegativeMassProfile.cappedApprox (α : NonnegativeMassProfile) (k : ℕ) : PositiveMassProfile where
  mass s := max (α.mass s) ((1/2:ℝ)^k)
  positive s := lt_of_lt_of_le (by positivity : (0:ℝ) < (1/2)^k) (le_max_right _ _)
  monotone := α.monotone.max monotone_const

theorem NonnegativeMassProfile.cappedApprox_le_one (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (k : ℕ) (s : ℝ) : (α.cappedApprox k).mass s ≤ 1 := by
  exact max_le (hα s) (pow_le_one₀ (by norm_num) (by norm_num))

theorem NonnegativeMassProfile.cappedApprox_error (α : NonnegativeMassProfile)
    (k j : ℕ) (s : ℝ) :
    |(α.cappedApprox k).mass s-(α.positiveApprox j).mass s| ≤ (1/2:ℝ)^k+(1/2:ℝ)^j := by
  dsimp [cappedApprox,positiveApprox]
  have hk : 0 ≤ (1/2:ℝ)^k := by positivity
  have hj : 0 ≤ (1/2:ℝ)^j := by positivity
  have ha := α.nonneg s
  rcases le_total ((1/2:ℝ)^k) (α.mass s) with h|h
  · rw [max_eq_left h]
    apply abs_le.mpr
    constructor <;> linarith
  · rw [max_eq_right h]
    apply abs_le.mpr
    constructor <;> linarith

theorem scalar_capped_profile_error (α : NonnegativeMassProfile)
    (k : ℕ) (l : ℝ) (t : ℝ≥0) (x : Fin 1 → ℝ) :
    |scalarTerminal.profileValue (α.cappedApprox k) l t x-
      scalarTerminal.nonnegativeProfileValue α l t x| ≤ (t:ℝ)/2*(1/2:ℝ)^k := by
  have hp : Tendsto (fun j : ℕ => (1/2:ℝ)^j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hh (j : ℕ) := scalarTerminal.profileValue_comparison (fun _ => 1)
    scalarTerminal_G_bound (α.cappedApprox k) (α.positiveApprox j)
    (α.cappedApprox_error k j) l t x
  have h := le_of_tendsto_of_tendsto
    (tendsto_const_nhds.sub (scalarTerminal.regularized_tendsto α l t x)).abs
    ((tendsto_const_nhds.add hp).mul_const (t:ℝ) |>.const_mul ((∑ _ : Fin 1, (1:ℝ)^2)/2))
    (Eventually.of_forall hh)
  apply h.trans_eq
  simp only [Fin.sum_univ_one,one_pow,add_zero]
  ring

theorem scalar_capped_grid_error (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (k : ℕ) (l : ℝ) (t : ℝ≥0) (x : Fin 1 → ℝ) :
    |(scalarTerminal.schedule ((α.cappedApprox k).grid l t k)).F x-
      scalarTerminal.nonnegativeProfileValue α l t x| ≤ (t:ℝ)*(1/2:ℝ)^k := by
  have hg := scalarTerminal.grid_error (fun _ => 1) scalarTerminal_G_bound
    (α.cappedApprox k) l t x k
  simp only [one_pow] at hg
  have hm : (α.cappedApprox k).mass (l+t)-(α.cappedApprox k).mass l ≤ 1 := by
    linarith [(α.cappedApprox k).positive l,α.cappedApprox_le_one hα k (l+t)]
  have hn : 0 ≤ (t:ℝ)/2*(1/2:ℝ)^k := by positivity
  have hg' : |(scalarTerminal.schedule ((α.cappedApprox k).grid l t k)).F x-
      scalarTerminal.profileValue (α.cappedApprox k) l t x| ≤ (t:ℝ)/2*(1/2:ℝ)^k := by
    apply hg.trans
    have hb := mul_le_mul_of_nonneg_left hm hn
    nlinarith
  have hh := abs_sub_le ((scalarTerminal.schedule ((α.cappedApprox k).grid l t k)).F x)
    (scalarTerminal.profileValue (α.cappedApprox k) l t x)
    (scalarTerminal.nonnegativeProfileValue α l t x)
  linarith [scalar_capped_profile_error α k l t x]

theorem scalar_capped_grid_tendstoUniformly (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) :
    TendstoUniformly (fun k (x : ℝ) =>
      (scalarTerminal.schedule ((α.cappedApprox k).grid l t k)).F (fun _ => x))
      (fun x => scalarTerminal.nonnegativeProfileValue α l t (fun _ => x)) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hp : Tendsto (fun k : ℕ => (t:ℝ)*(1/2:ℝ)^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul (t:ℝ)
  filter_upwards [hp.eventually (gt_mem_nhds hε)] with k hk x
  rw [Real.dist_eq,abs_sub_comm]
  exact (scalar_capped_grid_error α hα k l t (fun _ => x)).trans_lt hk

end SKFluctuations.Hierarchy

namespace SKFluctuations.Scalar
open Filter Set
open scoped Topology

 

theorem deriv_abs_le_secant {f g h : ℝ → ℝ} {δ M r : ℝ}
    (hd : ∀ x, HasDerivAt f (g x) x) (hdd : ∀ x, HasDerivAt g (h x) x)
    (hf : ∀ x, |f x| ≤ δ) (hh : ∀ x, |h x| ≤ M) (hr : 0 < r) (x : ℝ) :
    |g x| ≤ M*r+2*δ/r := by
  have hM : 0 ≤ M := (abs_nonneg (h 0)).trans (hh 0)
  obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope f g (show x < x+r by linarith)
    (fun y _ => (hd y).continuousAt.continuousWithinAt) (fun y _ => hd y)
  have hl := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y _ => (hdd y).hasDerivWithinAt) (fun y _ => by simpa only [Real.norm_eq_abs] using hh y)
    (mem_univ c) (mem_univ x)
  have hcx : |x-c| ≤ r := by rw [abs_of_nonpos (by linarith [hc.1] : x-c ≤ 0)]; linarith [hc.2]
  have h1 : |g x-g c| ≤ M*r := by
    simpa only [Real.norm_eq_abs] using hl.trans (mul_le_mul_of_nonneg_left hcx hM)
  have h2 : |g c| ≤ 2*δ/r := by
    rw [he,show x+r-x = r by ring,abs_div,abs_of_pos hr]
    apply div_le_div_of_nonneg_right _ hr.le
    exact (abs_sub (f (x+r)) (f x)).trans (by linarith [hf (x+r),hf x])
  calc
    |g x| = |(g x-g c)+g c| := by congr 1; ring
    _ ≤ |g x-g c|+|g c| := abs_add_le _ _
    _ ≤ M*r+2*δ/r := add_le_add h1 h2

 

theorem uniformCauchySeqOn_derivative {f g h : ℕ → ℝ → ℝ} {M : ℝ}
    (hd : ∀ n x, HasDerivAt (f n) (g n x) x)
    (hdd : ∀ n x, HasDerivAt (g n) (h n x) x)
    (hh : ∀ n x, |h n x| ≤ M)
    (hf : UniformCauchySeqOn f atTop univ) : UniformCauchySeqOn g atTop univ := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hh 0 0)
  rw [Metric.uniformCauchySeqOn_iff] at hf ⊢
  intro ε hε
  let r := ε/(8*(M+1))
  have hr : 0 < r := div_pos hε (by positivity)
  let δ := ε*r/8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N,hN⟩ := hf δ hδ
  refine ⟨N,fun m hm n hn x _ => ?_⟩
  have hb (y : ℝ) : |f m y-f n y| ≤ δ := by
    simpa only [Real.dist_eq] using (hN m hm n hn y (mem_univ y)).le
  have hb2 (y : ℝ) : |h m y-h n y| ≤ 2*M :=
    (abs_sub _ _).trans (by linarith [hh m y,hh n y])
  have h := deriv_abs_le_secant (fun y => (hd m y).sub (hd n y))
    (fun y => (hdd m y).sub (hdd n y)) hb hb2 hr x
  have he : 2*δ/r = ε/4 := by dsimp [δ]; field_simp; ring
  have hmr : 2*M*r < ε/4 := by
    have hm1 : 0 < M+1 := by linarith
    have ht : M/(M+1) < 1 := (div_lt_one hm1).2 (by linarith)
    have hp := mul_lt_mul_of_pos_left ht (show 0 < ε/4 by positivity)
    calc
      2*M*r = (ε/4)*(M/(M+1)) := by dsimp [r]; field_simp; ring
      _ < (ε/4)*1 := hp
      _ = ε/4 := mul_one _
  rw [Real.dist_eq]
  exact h.trans_lt (by rw [he]; linarith)

 
noncomputable def jetLimit (J : ℕ → ℕ → ℝ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  limUnder atTop (fun n => J n k x)

theorem jet_uniformCauchy (J : ℕ → ℕ → ℝ → ℝ)
    (hd : ∀ n k x, HasDerivAt (J n k) (J n (k+1) x) x)
    (hb : ∀ k, ∃ M : ℝ, ∀ n x, |J n (k+1) x| ≤ M)
    (h0 : UniformCauchySeqOn (fun n => J n 0) atTop univ) (k : ℕ) :
    UniformCauchySeqOn (fun n => J n k) atTop univ := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    obtain ⟨M,hM⟩ := hb (k+1)
    exact uniformCauchySeqOn_derivative (fun n x => hd n k x)
      (fun n x => hd n (k+1) x) hM ih

theorem jet_tendstoUniformly (J : ℕ → ℕ → ℝ → ℝ)
    (hd : ∀ n k x, HasDerivAt (J n k) (J n (k+1) x) x)
    (hb : ∀ k, ∃ M : ℝ, ∀ n x, |J n (k+1) x| ≤ M)
    (h0 : UniformCauchySeqOn (fun n => J n 0) atTop univ) (k : ℕ) :
    TendstoUniformly (fun n => J n k) (jetLimit J k) atTop := by
  have hc := jet_uniformCauchy J hd hb h0 k
  rw [← tendstoUniformlyOn_univ]
  exact hc.tendstoUniformlyOn_of_tendsto (fun x _ =>
    (hc.cauchySeq (mem_univ x)).tendsto_limUnder)

theorem jetLimit_hasDerivAt (J : ℕ → ℕ → ℝ → ℝ)
    (hd : ∀ n k x, HasDerivAt (J n k) (J n (k+1) x) x)
    (hb : ∀ k, ∃ M : ℝ, ∀ n x, |J n (k+1) x| ≤ M)
    (h0 : UniformCauchySeqOn (fun n => J n 0) atTop univ) (k : ℕ) (x : ℝ) :
    HasDerivAt (jetLimit J k) (jetLimit J (k+1) x) x :=
  hasDerivAt_of_tendstoUniformly (jet_tendstoUniformly J hd hb h0 (k+1))
    (Eventually.of_forall (fun n x => hd n k x))
    (fun y => (jet_tendstoUniformly J hd hb h0 k).tendsto_at y) x

theorem jetLimit_bound (J : ℕ → ℕ → ℝ → ℝ)
    (hd : ∀ n k x, HasDerivAt (J n k) (J n (k+1) x) x)
    (hb : ∀ k, ∃ M : ℝ, ∀ n x, |J n (k+1) x| ≤ M)
    (h0 : UniformCauchySeqOn (fun n => J n 0) atTop univ)
    {k : ℕ} {M : ℝ} (hM : ∀ n x, |J n k x| ≤ M) (x : ℝ) :
    |jetLimit J k x| ≤ M :=
  le_of_tendsto ((jet_tendstoUniformly J hd hb h0 k).tendsto_at x).abs
    (Eventually.of_forall (fun n => hM n x))

end SKFluctuations.Scalar

namespace SKFluctuations.Scalar
open Filter Set
open scoped Topology ContDiff

 

theorem contDiff_of_derivative_chain (J : ℕ → ℝ → ℝ)
    (hd : ∀ k x, HasDerivAt (J k) (J (k+1) x) x) (k : ℕ) (r : ℕ) :
    ContDiff ℝ r (J k) := by
  induction r generalizing k with
  | zero =>
    simp only [Nat.cast_zero,contDiff_zero]
    exact continuous_iff_continuousAt.mpr (fun x => (hd k x).continuousAt)
  | succ r ih =>
    rw [show (↑(r+1) : ℕ∞ω) = (r:ℕ∞ω)+1 by simp only [Nat.cast_add,Nat.cast_one],
      contDiff_succ_iff_deriv]
    refine ⟨fun x => (hd k x).differentiableAt,by simp,?_⟩
    have he : deriv (J k) = J (k+1) := funext (fun x => (hd k x).deriv)
    rw [he]
    exact ih (k+1)

theorem jetLimit_contDiff (J : ℕ → ℕ → ℝ → ℝ)
    (hd : ∀ n k x, HasDerivAt (J n k) (J n (k+1) x) x)
    (hb : ∀ k, ∃ M : ℝ, ∀ n x, |J n (k+1) x| ≤ M)
    (h0 : UniformCauchySeqOn (fun n => J n 0) atTop univ) (k r : ℕ) :
    ContDiff ℝ r (jetLimit J k) :=
  contDiff_of_derivative_chain (jetLimit J) (jetLimit_hasDerivAt J hd hb h0) k r

theorem jetLimit_iterated_deriv (J : ℕ → ℕ → ℝ → ℝ)
    (hd : ∀ n k x, HasDerivAt (J n k) (J n (k+1) x) x)
    (hb : ∀ k, ∃ M : ℝ, ∀ n x, |J n (k+1) x| ≤ M)
    (h0 : UniformCauchySeqOn (fun n => J n 0) atTop univ) (k : ℕ) :
    (deriv^[k]) (jetLimit J 0) = jetLimit J k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih]
    exact funext (fun x => (jetLimit_hasDerivAt J hd hb h0 k x).deriv)

end SKFluctuations.Scalar

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators ContDiff

noncomputable def scalarCappedJets (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0)
    (n k : ℕ) (x : ℝ) : ℝ :=
  scalarSourceJet (heatSteps ((α.cappedApprox n).grid l t n)) k x

noncomputable def scalarProfileJet (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0)
    (k : ℕ) (x : ℝ) : ℝ := Scalar.jetLimit (scalarCappedJets α l t) k x

theorem scalarCappedJets_ordered (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (n : ℕ) :
    OrderedSteps 0 (heatSteps (ι := Fin 1) ((α.cappedApprox n).grid l t n)) :=
  (α.cappedApprox n).grid_ordered l t n le_rfl (α.cappedApprox n |>.positive l).le
    (α.cappedApprox_le_one hα n (l+t))

theorem scalarCappedJets_hasDerivAt (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (n k : ℕ) (x : ℝ) :
    HasDerivAt (scalarCappedJets α l t n k) (scalarCappedJets α l t n (k+1) x) x :=
  scalarSourceJet_hasDerivAt (scalarCappedJets_ordered α hα l t n) k x

theorem scalarCappedJets_bound (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) : ∀ n x,
    |scalarCappedJets α l t n (k+1) x| ≤ (ReplicaTree.attachmentCount 1 k:ℝ) :=
  fun n x => scalarSourceJet_bound (scalarCappedJets_ordered α hα l t n) k x

theorem scalarCappedJets_zero_tendsto (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) :
    TendstoUniformly (fun n => scalarCappedJets α l t n 0)
      (fun x => scalarTerminal.nonnegativeProfileValue α l t (fun _ => x)) atTop := by
  change TendstoUniformly (fun n x => scalarCappedJets α l t n 0 x)
    (fun x => scalarTerminal.nonnegativeProfileValue α l t (fun _ => x)) atTop
  simpa only [scalar_schedule_eq_hierarchy,scalarCappedJets,scalarSourceJet] using
    scalar_capped_grid_tendstoUniformly α hα l t

theorem scalarCappedJets_zero_cauchy (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) :
    UniformCauchySeqOn (fun n => scalarCappedJets α l t n 0) atTop univ :=
  (scalarCappedJets_zero_tendsto α hα l t).tendstoUniformlyOn.uniformCauchySeqOn

theorem scalarProfileJet_tendstoUniformly (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    TendstoUniformly (fun n => scalarCappedJets α l t n k) (scalarProfileJet α l t k) atTop :=
  Scalar.jet_tendstoUniformly _ (scalarCappedJets_hasDerivAt α hα l t)
    (fun r => ⟨_,scalarCappedJets_bound α hα l t r⟩) (scalarCappedJets_zero_cauchy α hα l t) k

theorem scalarProfileJet_zero (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : ℝ) :
    scalarProfileJet α l t 0 x = scalarTerminal.nonnegativeProfileValue α l t (fun _ => x) :=
  tendsto_nhds_unique ((scalarProfileJet_tendstoUniformly α hα l t 0).tendsto_at x)
    ((scalarCappedJets_zero_tendsto α hα l t).tendsto_at x)

theorem scalarProfileJet_hasDerivAt (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) (x : ℝ) :
    HasDerivAt (scalarProfileJet α l t k) (scalarProfileJet α l t (k+1) x) x :=
  Scalar.jetLimit_hasDerivAt _ (scalarCappedJets_hasDerivAt α hα l t)
    (fun r => ⟨_,scalarCappedJets_bound α hα l t r⟩) (scalarCappedJets_zero_cauchy α hα l t) k x

theorem scalarProfileJet_bound (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) (x : ℝ) :
    |scalarProfileJet α l t (k+1) x| ≤ (ReplicaTree.attachmentCount 1 k:ℝ) :=
  Scalar.jetLimit_bound _ (scalarCappedJets_hasDerivAt α hα l t)
    (fun r => ⟨_,scalarCappedJets_bound α hα l t r⟩) (scalarCappedJets_zero_cauchy α hα l t)
    (scalarCappedJets_bound α hα l t k) x

 

theorem scalarProfile_contDiff (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (r : ℕ) :
    ContDiff ℝ r (fun x => scalarTerminal.nonnegativeProfileValue α l t (fun _ => x)) := by
  rw [← funext (scalarProfileJet_zero α hα l t)]
  exact Scalar.contDiff_of_derivative_chain _ (scalarProfileJet_hasDerivAt α hα l t) 0 r

theorem scalarProfile_iterated_deriv (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    (deriv^[k]) (fun x => scalarTerminal.nonnegativeProfileValue α l t (fun _ => x)) =
      scalarProfileJet α l t k := by
  rw [← funext (scalarProfileJet_zero α hα l t)]
  exact Scalar.jetLimit_iterated_deriv _ (scalarCappedJets_hasDerivAt α hα l t)
    (fun r => ⟨_,scalarCappedJets_bound α hα l t r⟩) (scalarCappedJets_zero_cauchy α hα l t) k

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators ContDiff

theorem scalarProfileJet_bddSmooth (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    BddSmooth 0 (fun x : Fin 1 → ℝ => scalarProfileJet α l t (k+1) (x 0)) := by
  refine ⟨?_,(ReplicaTree.attachmentCount 1 k:ℝ),by positivity,?_⟩
  · exact (continuous_iff_continuousAt.mpr (fun x =>
      (scalarProfileJet_hasDerivAt α hα l t (k+1) x).continuousAt)).comp (continuous_apply 0)
  · exact fun x => scalarProfileJet_bound α hα l t k (x 0)

theorem scalarProfileJet_lipschitz (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) : LipschitzWith 1 (scalarProfileJet α l t 0) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (scalarProfileJet_hasDerivAt α hα l t 0 x).differentiableAt)
  intro x
  rw [(scalarProfileJet_hasDerivAt α hα l t 0 x).deriv]
  change |scalarProfileJet α l t 1 x| ≤ 1
  simpa only [ReplicaTree.attachmentCount,Nat.cast_one] using scalarProfileJet_bound α hα l t 0 x

theorem scalarProfileJet_line (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) (x v : Fin 1 → ℝ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => scalarProfileJet α l t k ((x+r • v) 0))
      (∑ i : Fin 1, v i*scalarProfileJet α l t (k+1) ((x+s • v) 0)) s := by
  have hc := (hasDerivAt_const s (x 0)).add ((hasDerivAt_id s).mul_const (v 0))
  have hd := (scalarProfileJet_hasDerivAt α hα l t k (x 0+s*v 0)).comp s hc
  convert! hd using 1
  simp only [Fin.sum_univ_one,Pi.add_apply,Pi.smul_apply,smul_eq_mul,zero_add,one_mul]
  ring

theorem scalarProfileJet_coord (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) (i : Fin 1) (x : Fin 1 → ℝ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => scalarProfileJet α l t k ((x+r • (Pi.single i (1:ℝ) : Fin 1 → ℝ)) 0))
      (scalarProfileJet α l t (k+1) ((x+s • (Pi.single i (1:ℝ) : Fin 1 → ℝ)) 0)) s := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simpa only [Fin.sum_univ_one,Pi.single_eq_same,one_mul] using
    scalarProfileJet_line α hα l t k x (Pi.single 0 1) s

 

noncomputable def scalarProfileHeatJet (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) : HeatJet 0 where
  F x := scalarProfileJet α l t 0 (x 0)
  A x := scalarProfileJet α l t 1 (x 0)
  G _ x := scalarProfileJet α l t 1 (x 0)
  H _ x := scalarProfileJet α l t 2 (x 0)
  A₁ _ x := scalarProfileJet α l t 2 (x 0)
  A₂ _ x := scalarProfileJet α l t 3 (x 0)
  C := 1
  lipschitz := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    calc
      dist (scalarProfileJet α l t 0 (x 0)) (scalarProfileJet α l t 0 (y 0)) ≤
          1*dist (x 0) (y 0) := (scalarProfileJet_lipschitz α hα l t).dist_le_mul _ _
      _ ≤ 1*dist x y := mul_le_mul_of_nonneg_left (dist_le_pi_dist x y 0) zero_le_one
  smoothA := scalarProfileJet_bddSmooth α hα l t 0
  smoothG _ := scalarProfileJet_bddSmooth α hα l t 0
  smoothH _ := scalarProfileJet_bddSmooth α hα l t 1
  smoothA₁ _ := scalarProfileJet_bddSmooth α hα l t 1
  smoothA₂ _ := scalarProfileJet_bddSmooth α hα l t 2
  derivF := scalarProfileJet_line α hα l t 0
  derivG i := scalarProfileJet_coord α hα l t 1 i
  derivA := scalarProfileJet_line α hα l t 1
  derivA₁ i := scalarProfileJet_coord α hα l t 2 i

theorem scalarProfileHeatJet_F (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin 1 → ℝ) :
    (scalarProfileHeatJet α hα l t).F x = scalarTerminal.nonnegativeProfileValue α l t x := by
  change scalarProfileJet α l t 0 (x 0) = _
  rw [scalarProfileJet_zero α hα l t]
  congr 1
  ext i
  exact congrArg x (Subsingleton.elim _ _)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

variable {n : ℕ}

theorem HeatJet.capped_profile_error (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : NonnegativeMassProfile)
    (k : ℕ) (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    |J.profileValue (α.cappedApprox k) l t x-J.nonnegativeProfileValue α l t x| ≤
      (∑ i, (D i)^2)/2*(t:ℝ)*(1/2:ℝ)^k := by
  have hp : Tendsto (fun j : ℕ => (1/2:ℝ)^j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hh (j : ℕ) := J.profileValue_comparison D hD (α.cappedApprox k) (α.positiveApprox j)
    (α.cappedApprox_error k j) l t x
  have h := le_of_tendsto_of_tendsto
    (tendsto_const_nhds.sub (J.regularized_tendsto α l t x)).abs
    ((tendsto_const_nhds.add hp).mul_const (t:ℝ) |>.const_mul ((∑ i, (D i)^2)/2))
    (Eventually.of_forall hh)
  apply h.trans_eq
  simp only [add_zero]
  ring

theorem HeatJet.capped_grid_error (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (k j : ℕ) (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    |(J.schedule ((α.cappedApprox k).grid l t j)).F x-J.nonnegativeProfileValue α l t x| ≤
      (∑ i, (D i)^2)/2*(t:ℝ)*((1/2:ℝ)^k+(1/2:ℝ)^j) := by
  have hg := J.grid_error D hD (α.cappedApprox k) l t x j
  have hm : (α.cappedApprox k).mass (l+t)-(α.cappedApprox k).mass l ≤ 1 := by
    linarith [(α.cappedApprox k).positive l,α.cappedApprox_le_one hα k (l+t)]
  have hn : 0 ≤ (∑ i, (D i)^2)/2*(t:ℝ)*(1/2:ℝ)^j := by positivity
  have hg' : |(J.schedule ((α.cappedApprox k).grid l t j)).F x-
      J.profileValue (α.cappedApprox k) l t x| ≤ (∑ i, (D i)^2)/2*(t:ℝ)*(1/2:ℝ)^j := by
    apply hg.trans
    have hb := mul_le_mul_of_nonneg_left hm hn
    nlinarith
  have hh := abs_sub_le ((J.schedule ((α.cappedApprox k).grid l t j)).F x)
    (J.profileValue (α.cappedApprox k) l t x) (J.nonnegativeProfileValue α l t x)
  have he := J.capped_profile_error D hD α k l t x
  nlinarith

theorem HeatJet.capped_grid_tendsto (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (r : ℕ) (x : Fin (n+1) → ℝ) :
    Tendsto (fun k => (J.schedule ((α.cappedApprox k).grid l t (k+r))).F x) atTop
      (𝓝 (J.nonnegativeProfileValue α l t x)) := by
  have hp : Tendsto (fun k : ℕ => (1/2:ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun k => dist_nonneg)
    (fun k => by simpa only [Real.dist_eq] using J.capped_grid_error D hD α hα k (k+r) l t x)
  have hh := (((hp.add (hp.comp (tendsto_add_atTop_nat r))).const_mul (t:ℝ)).const_mul
    ((∑ i, (D i)^2)/2))
  simpa only [Function.comp_apply,zero_add,mul_zero,mul_assoc] using hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

theorem scalarProfileHeatJet_G_bound (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (i : Fin 1) (x : Fin 1 → ℝ) :
    |(scalarProfileHeatJet α hα l t).G i x| ≤ 1 := by
  change |scalarProfileJet α l t 1 (x 0)| ≤ 1
  simpa only [ReplicaTree.attachmentCount,Nat.cast_one] using scalarProfileJet_bound α hα l t 0 (x 0)

 

theorem scalarProfile_midpoint (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin 1 → ℝ) :
    scalarTerminal.nonnegativeProfileValue α l t x =
      (scalarProfileHeatJet α hα (l+(t:ℝ)/2) (t/2)).nonnegativeProfileValue α l (t/2) x := by
  let R := scalarProfileHeatJet α hα (l+(t:ℝ)/2) (t/2)
  have hA := scalarTerminal.capped_grid_tendsto (fun _ => 1) scalarTerminal_G_bound α hα l t 1 x
  have hB := R.capped_grid_tendsto (fun _ => 1)
    (scalarProfileHeatJet_G_bound α hα _ _) α hα l (t/2) 0 x
  simp only [Nat.add_zero] at hB
  have hd (k : ℕ) :
      dist ((R.schedule ((α.cappedApprox k).grid l (t/2) k)).F x)
        ((scalarTerminal.schedule ((α.cappedApprox k).grid l t (k+1))).F x) ≤
      ((t/2:ℝ≥0):ℝ)*(1/2:ℝ)^k := by
    rw [PositiveMassProfile.grid,scalarTerminal.schedule_append,Real.dist_eq,abs_sub_comm]
    apply HeatJet.schedule_nonexpansive _ R
    intro y
    rw [show R.F y = scalarTerminal.nonnegativeProfileValue α (l+(t:ℝ)/2) (t/2) y from
      scalarProfileHeatJet_F α hα _ _ y]
    exact scalar_capped_grid_error α hα k _ _ y
  have hp : Tendsto (fun k : ℕ => ((t/2:ℝ≥0):ℝ)*(1/2:ℝ)^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul ((t/2:ℝ≥0):ℝ)
  have hz := squeeze_zero (fun k => dist_nonneg) hd hp
  exact tendsto_nhds_unique hA (hB.congr_dist hz)

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal

 theorem ExpBounded.const (a : ℝ) : ExpBounded (fun _ : ℝ => a) := by
  refine ⟨continuous_const, |a|, 0, abs_nonneg _, le_rfl, ?_⟩
  simp

 theorem ExpBounded.id : ExpBounded (fun x : ℝ => x) :=
  ExpBounded.of_lipschitz LipschitzWith.id

 theorem ExpBounded.neg {f : ℝ → ℝ} (hf : ExpBounded f) : ExpBounded (fun x => -f x) := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  exact ⟨hf.1.neg, C,c,hC,hc, fun x => by simpa using hb x⟩

 theorem ExpBounded.add {f g : ℝ → ℝ} (hf : ExpBounded f) (hg : ExpBounded g) :
    ExpBounded (fun x => f x + g x) := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  obtain ⟨D,d,hD,hd,he⟩ := hg.2
  refine ⟨hf.1.add hg.1, C+D,c+d,add_nonneg hC hD,add_nonneg hc hd,fun x => ?_⟩
  have hf' : |f x| ≤ C * Real.exp ((c+d)*|x|) := (hb x).trans (by gcongr; nlinarith [abs_nonneg x])
  have hg' : |g x| ≤ D * Real.exp ((c+d)*|x|) := (he x).trans (by gcongr; nlinarith [abs_nonneg x])
  calc
    |f x+g x| ≤ |f x|+|g x| := abs_add_le _ _
    _ ≤ C * Real.exp ((c+d)*|x|) + D * Real.exp ((c+d)*|x|) := add_le_add hf' hg'
    _ = _ := by ring

 theorem ExpBounded.sub {f g : ℝ → ℝ} (hf : ExpBounded f) (hg : ExpBounded g) :
    ExpBounded (fun x => f x - g x) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

 theorem ExpBounded.mul {f g : ℝ → ℝ} (hf : ExpBounded f) (hg : ExpBounded g) :
    ExpBounded (fun x => f x*g x) := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  obtain ⟨D,d,hD,hd,he⟩ := hg.2
  refine ⟨hf.1.mul hg.1,C*D,c+d,mul_nonneg hC hD,add_nonneg hc hd,fun x => ?_⟩
  calc
    |f x*g x| = |f x| * |g x| := abs_mul _ _
    _ ≤ (C*Real.exp (c*|x|))*(D*Real.exp (d*|x|)) :=
      mul_le_mul (hb x) (he x) (abs_nonneg _) (mul_nonneg hC (Real.exp_nonneg _))
    _ = C*D*Real.exp ((c+d)*|x|) := by rw [add_mul,Real.exp_add]; ring

 theorem ExpBounded.const_mul {f : ℝ → ℝ} (hf : ExpBounded f) (a : ℝ) :
    ExpBounded (fun x => a*f x) := (ExpBounded.const a).mul hf

 theorem ExpBounded.pow {f : ℝ → ℝ} (hf : ExpBounded f) (k : ℕ) :
    ExpBounded (fun x => f x^k) := by
  induction k with
  | zero => simpa using ExpBounded.const 1
  | succ k ih => simpa only [pow_succ] using ih.mul hf

 theorem ExpBounded.integrable {f : ℝ → ℝ} (hf : ExpBounded f) :
    Integrable f (gaussianReal 0 1) := by
  simpa only [zero_add,one_mul] using hf.affine_integrable 0 1

 theorem ExpBounded.of_bddSmooth {f : ℝ → ℝ} (hf : BddSmooth 0 f) : ExpBounded f := by
  simpa using (ExpBounded.const 1).bdd_mul hf

end SKFluctuations.GaussianCalculus

end

end OAI
