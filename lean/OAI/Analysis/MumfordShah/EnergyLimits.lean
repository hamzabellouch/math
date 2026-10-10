import Mathlib
import OAI.Analysis.MumfordShah.TestablePotential
import OAI.Analysis.MumfordShah.Cutoffs

namespace OAI

/-! MumfordShah energy limits. -/

noncomputable section
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
namespace MumfordShah
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter
open scoped ContDiff
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff

open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff

lemma integral_norm_ball_geometric_bound {G : ℂ → ℂ} {C R : ℝ}
    (hG : ∀ S : ℝ, 0 < S → MemLp G 2 (volume.restrict (ball 0 S)))
    (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hgrowth : ∀ S : ℝ, 1 ≤ S → (∫ x in ball (0 : ℂ) S, ‖G x‖^2) ≤ C*(1+S))
    (n : ℕ) :
    (∫ x in ball (0 : ℂ) ((4:ℝ)^(n+1)*R), ‖G x‖) ≤
      Real.sqrt (2*Real.pi*C*R^3) * (8:ℝ)^(n+1) := by
  let S := (4:ℝ)^(n+1)*R
  have hp : 1 ≤ (4:ℝ)^(n+1) := one_le_pow₀ (by norm_num)
  have hS : 1 ≤ S := by dsimp [S]; nlinarith
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one hS
  let : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) S)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hL := (hG S hSp).norm
  have hb := sq_integral_le_mass_mul_integral_sq hL
  have hmass : (volume.restrict (ball (0 : ℂ) S)).real univ = S^2 * Real.pi := by
    simp only [measureReal_restrict_apply MeasurableSet.univ, univ_inter, measureReal_def,
      Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hSp.le,
      ENNReal.coe_toReal, NNReal.coe_real_pi]
  rw [hmass] at hb
  have he := hgrowth S hS
  have hsq : (∫ x in ball (0 : ℂ) S, ‖G x‖)^2 ≤ 2*Real.pi*C*S^3 := by
    have hm : 0 ≤ S^2 * Real.pi := by positivity
    have hh := mul_le_mul_of_nonneg_left he hm
    have hh' : S^2 * Real.pi * (C*(1+S)) ≤ 2*Real.pi*C*S^3 := by
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg S) Real.pi_pos.le)
        (mul_nonneg hC (sub_nonneg.mpr hS))]
    exact hb.trans (hh.trans hh')
  have heq : (Real.sqrt (2*Real.pi*C*R^3) * (8:ℝ)^(n+1))^2 =
      2*Real.pi*C*S^3 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    dsimp [S]
    rw [mul_pow]
    have hpow : ((8:ℝ)^(n+1))^2 = ((4:ℝ)^(n+1))^3 := by
      calc
        ((8:ℝ)^(n+1))^2 = ((8:ℝ)^2)^(n+1) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ = ((4:ℝ)^3)^(n+1) := by norm_num
        _ = ((4:ℝ)^(n+1))^3 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hpow]
    ring
  exact le_of_sq_le_sq (heq.symm ▸ hsq) (by positivity)

lemma interaction_annulus_bound {G q : ℂ → ℂ} {C D R : ℝ}
    (hG : ∀ S : ℝ, 0 < S → MemLp G 2 (volume.restrict (ball 0 S)))
    (hq : MemLp q 2 volume) (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 1 ≤ R)
    (hgrowth : ∀ S : ℝ, 1 ≤ S → (∫ x in ball (0 : ℂ) S, ‖G x‖^2) ≤ C*(1+S))
    (hdecay : ∀ᵐ x ∂volume, R ≤ ‖x‖ → ‖q x‖ ≤ D / ‖x‖^2) (n : ℕ) :
    (∫ x in ball (0 : ℂ) ((4:ℝ)^(n+1)*R) \ ball (0 : ℂ) ((4:ℝ)^n*R),
      ‖inner ℝ (G x) (q x)‖) ≤
      (8*D*Real.sqrt (2*Real.pi*C*R^3)/R^2) * (1/2:ℝ)^n := by
  let r := (4:ℝ)^n*R
  let S := (4:ℝ)^(n+1)*R
  let A := ball (0 : ℂ) S \ ball (0 : ℂ) r
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hrp : 0 < r := by dsimp [r]; positivity
  have hSp : 0 < S := by dsimp [S]; positivity
  have hRr : R ≤ r := by
    dsimp [r]
    nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4) (n := n)]
  have hi : IntegrableOn (fun x => inner ℝ (G x) (q x)) A :=
    integrable_inner_memLp_measure ((hG S hSp).mono_measure (Measure.restrict_mono sdiff_subset le_rfl)) (hq.restrict A)
  have hGA : IntegrableOn (fun x => ‖G x‖) A := by
    let : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) S)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact ((hG S hSp).norm.integrable (by norm_num)).mono_measure (Measure.restrict_mono sdiff_subset le_rfl)
  have hb : (∫ x in A, ‖inner ℝ (G x) (q x)‖) ≤
      (D/r^2)*(∫ x in A, ‖G x‖) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hi.norm (hGA.const_mul _)
    filter_upwards [ae_restrict_of_ae hdecay, ae_restrict_mem (isOpen_ball.measurableSet.diff isOpen_ball.measurableSet)] with x hx hxA
    have hrx : r ≤ ‖x‖ := by
      simpa only [A, Set.mem_sdiff, mem_ball, dist_zero_right, not_lt] using hxA.2
    have hxr : 0 < ‖x‖ := lt_of_lt_of_le hrp hrx
    have hqbound : ‖q x‖ ≤ D/r^2 := (hx (hRr.trans hrx)).trans
      (div_le_div_of_nonneg_left hD (sq_pos_of_pos hrp) (by nlinarith))
    calc
      ‖inner ℝ (G x) (q x)‖ ≤ ‖G x‖*‖q x‖ := norm_inner_le_norm _ _
      _ ≤ ‖G x‖*(D/r^2) := mul_le_mul_of_nonneg_left hqbound (norm_nonneg _)
      _ = (D/r^2)*‖G x‖ := mul_comm _ _
  have hball : (∫ x in A, ‖G x‖) ≤ ∫ x in ball (0 : ℂ) S, ‖G x‖ := by
    let : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) S)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact integral_mono_measure (Measure.restrict_mono sdiff_subset le_rfl)
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      ((hG S hSp).norm.integrable (by norm_num))
  have hfinal := hb.trans (mul_le_mul_of_nonneg_left
    (hball.trans (integral_norm_ball_geometric_bound hG hC hR hgrowth n)) (by positivity))
  have heq : D/r^2 * (Real.sqrt (2*Real.pi*C*R^3) * (8:ℝ)^(n+1)) =
      (8*D*Real.sqrt (2*Real.pi*C*R^3)/R^2) * (1/2:ℝ)^n := by
    dsimp [r]
    rw [mul_pow, pow_succ (8:ℝ) n]
    have hp : ((4:ℝ)^n)^2 = (16:ℝ)^n := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    rw [hp]
    have hratio : (8:ℝ)^n / (16:ℝ)^n = (1/2:ℝ)^n := by rw [← div_pow]; norm_num
    rw [← hratio]
    ring
  exact heq ▸ hfinal

theorem integrable_interaction_of_growth_decay {G q : ℂ → ℂ} {C D R : ℝ}
    (hG : ∀ S : ℝ, 0 < S → MemLp G 2 (volume.restrict (ball 0 S)))
    (hq : MemLp q 2 volume) (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 1 ≤ R)
    (hgrowth : ∀ S : ℝ, 1 ≤ S → (∫ x in ball (0 : ℂ) S, ‖G x‖^2) ≤ C*(1+S))
    (hdecay : ∀ᵐ x ∂volume, R ≤ ‖x‖ → ‖q x‖ ≤ D / ‖x‖^2) :
    Integrable (fun x => inner ℝ (G x) (q x)) volume := by
  let A := fun n : ℕ => ball (0 : ℂ) ((4:ℝ)^(n+1)*R) \ ball (0 : ℂ) ((4:ℝ)^n*R)
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hA : ∀ n, IntegrableOn (fun x => inner ℝ (G x) (q x)) (A n) := by
    intro n
    exact integrable_inner_memLp_measure
      ((hG ((4:ℝ)^(n+1)*R) (by positivity)).mono_measure (Measure.restrict_mono sdiff_subset le_rfl)) (hq.restrict _)
  have hsum : Summable (fun n => ∫ x in A n, ‖inner ℝ (G x) (q x)‖) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _))
      (fun n => interaction_annulus_bound hG hq hC hD hR hgrowth hdecay n)
    exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).mul_left _
  have hi := integrableOn_iUnion_of_summable_integral_norm hA hsum
  have hbase : IntegrableOn (fun x => inner ℝ (G x) (q x)) (ball (0 : ℂ) R) :=
    integrable_inner_memLp_measure (hG R hRp) (hq.restrict _)
  have hcover : ball (0 : ℂ) R ∪ ⋃ n, A n = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : ‖x‖ < R
    · exact Or.inl (by simpa using hx)
    · right
      obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near ((le_div_iff₀ hRp).mpr (by simpa using le_of_not_gt hx))
        (by norm_num : (1:ℝ) < 4)
      apply mem_iUnion.mpr ⟨n,?_⟩
      change x ∈ ball (0 : ℂ) ((4:ℝ)^(n+1)*R) \ ball (0 : ℂ) ((4:ℝ)^n*R)
      simp only [Set.mem_sdiff, mem_ball, dist_zero_right, not_lt]
      exact ⟨(div_lt_iff₀ hRp).mp hn', (le_div_iff₀ hRp).mp hn⟩
  simpa only [hcover, integrableOn_univ] using hbase.union hi

lemma integrable_local_scalar_inner_test {φ : ℂ → ℝ} {G : ℂ → ℂ}
    (hφ : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp φ 2 (volume.restrict S))
    (hG : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp G 2 (volume.restrict S))
    {χ : ℂ → ℝ} (hs : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    Integrable (fun x => φ x * inner ℝ (G x) (gradient χ x)) volume := by
  let S := tsupport χ
  have hGi := local_memLp_on_bounded hG hc.isBounded
  have hdG := memLp_inner_test hGi
    ((continuous_gradient_of_smooth hs).memLp_of_hasCompactSupport (compactSupport_gradient hc))
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := S)
  · exact (local_memLp_on_bounded hφ hc.isBounded).integrable_mul hdG
  · intro x hx
    simp [gradient, fderiv_of_notMem_tsupport ℝ hx]

lemma cutoff_boundary_interaction_bound {φ χ : ℂ → ℝ} {G : ℂ → ℂ} {C D M R : ℝ}
    (hφ : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp φ 2 (volume.restrict S))
    (hG : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp G 2 (volume.restrict S))
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hM : 0 ≤ M) (hR : 1 ≤ R)
    (hgrowth : ∀ T : ℝ, 1 ≤ T → (∫ x in ball (0:ℂ) T, ‖G x‖^2) ≤ C*(1+T))
    (hdecay : ∀ᵐ x ∂volume, R ≤ ‖x‖ → |φ x| ≤ D/‖x‖)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (n : ℕ)
    (hgrad : ∀ x, ‖gradient χ x‖ ≤ M/((4:ℝ)^n*R))
    (hzero : ∀ x, (‖x‖ ≤ (4:ℝ)^n*R ∨ 2*((4:ℝ)^n*R) ≤ ‖x‖) → gradient χ x = 0) :
    ‖∫ x : ℂ, φ x * inner ℝ (G x) (gradient χ x)‖ ≤
      (8*(D*M)*Real.sqrt (2*Real.pi*C*R^3)/R^2) * (1/2:ℝ)^n := by
  let r := (4:ℝ)^n*R
  let T := (4:ℝ)^(n+1)*R
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hrp : 0 < r := by dsimp [r]; positivity
  have hTp : 0 < T := by dsimp [T]; positivity
  have hRr : R ≤ r := by
    dsimp [r]
    nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4) (n := n)]
  have h2r : 2*r ≤ T := by dsimp [r,T]; rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ)<4) n]
  have hi := integrable_local_scalar_inner_test hφ hG hχ hc
  have houtside (x : ℂ) (hx : x ∉ ball (0:ℂ) T) : φ x * inner ℝ (G x) (gradient χ x) = 0 := by
    have hTx : T ≤ ‖x‖ := by simpa [mem_ball, dist_zero_right] using hx
    simp [hzero x (Or.inr (h2r.trans hTx))]
  have hGi : IntegrableOn (fun x => ‖G x‖) (ball (0:ℂ) T) := by
    let : IsFiniteMeasure (volume.restrict (ball (0:ℂ) T)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact (hG _ isOpen_ball isBounded_ball).norm.integrable (by norm_num)
  have hb : (∫ x in ball (0:ℂ) T, ‖φ x * inner ℝ (G x) (gradient χ x)‖) ≤
      (D*M/r^2)*(∫ x in ball (0:ℂ) T, ‖G x‖) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hi.norm.restrict (hGi.const_mul _)
    filter_upwards [ae_restrict_of_ae hdecay] with x hx
    by_cases hxr : ‖x‖ ≤ r
    · simp only [hzero x (Or.inl hxr), inner_zero_right, mul_zero, norm_zero]
      positivity
    · have hrx := le_of_lt (lt_of_not_ge hxr)
      have hp : |φ x| ≤ D/r := (hx (hRr.trans hrx)).trans
        (div_le_div_of_nonneg_left hD hrp hrx)
      calc
        ‖φ x * inner ℝ (G x) (gradient χ x)‖ = |φ x| * ‖inner ℝ (G x) (gradient χ x)‖ := by rw [norm_mul, Real.norm_eq_abs]
        _ ≤ (D/r) * (‖G x‖ * (M/r)) := mul_le_mul hp
          ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hgrad x) (norm_nonneg _)))
          (norm_nonneg _) (by positivity)
        _ = (D*M/r^2)*‖G x‖ := by ring
  have hnorm : ‖∫ x : ℂ, φ x * inner ℝ (G x) (gradient χ x)‖ ≤
      (D*M/r^2) * (Real.sqrt (2*Real.pi*C*R^3)*(8:ℝ)^(n+1)) := by
    calc
      _ ≤ ∫ x : ℂ, ‖φ x * inner ℝ (G x) (gradient χ x)‖ := norm_integral_le_integral_norm _
      _ = ∫ x in ball (0:ℂ) T, ‖φ x * inner ℝ (G x) (gradient χ x)‖ := by
        apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
        intro x hx
        rw [houtside x hx, norm_zero]
      _ ≤ _ := hb.trans (mul_le_mul_of_nonneg_left
        (integral_norm_ball_geometric_bound (fun S _ => hG _ isOpen_ball isBounded_ball)
          hC hR hgrowth n) (by positivity))
  have heq : (D*M/r^2) * (Real.sqrt (2*Real.pi*C*R^3)*(8:ℝ)^(n+1)) =
      (8*(D*M)*Real.sqrt (2*Real.pi*C*R^3)/R^2) * (1/2:ℝ)^n := by
    dsimp [r]
    rw [mul_pow, pow_succ (8:ℝ) n]
    have hp : ((4:ℝ)^n)^2 = (16:ℝ)^n := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    rw [hp]
    have hratio : (8:ℝ)^n/(16:ℝ)^n = (1/2:ℝ)^n := by rw [← div_pow]; norm_num
    rw [← hratio]
    ring
  rwa [heq] at hnorm

theorem divergence_pairing_zero_of_decay {φ : ℂ → ℝ} {w : PlaneL2} {G : ℂ → ℂ}
    (htest : CompactDivergenceTestable φ w)
    (hφ : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp φ 2 (volume.restrict S))
    (hG : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp G 2 (volume.restrict S))
    (hdiv : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : ℂ, inner ℝ (G x) (gradient ψ x)) = 0)
    {C D E R : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hR : 1 ≤ R)
    (hgrowth : ∀ T : ℝ, 1 ≤ T → (∫ x in ball (0:ℂ) T, ‖G x‖^2) ≤ C*(1+T))
    (hdecay : ∀ᵐ x ∂volume, R ≤ ‖x‖ → |φ x| ≤ D/‖x‖)
    (hwdecay : ∀ᵐ x ∂volume, R ≤ ‖x‖ → ‖w x‖ ≤ E/‖x‖^2) :
    (∫ x : ℂ, inner ℝ (G x) (w x)) = 0 := by
  obtain ⟨χ,M,hM,hχ,hfamily⟩ := exists_scaled_cutoff_family
  let r (n : ℕ) := (4:ℝ)^n*R
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  let θ (n : ℕ) := scaledCutoff χ (r n)
  have hθ (n : ℕ) := hfamily (r n) (hr n)
  have hθs (n : ℕ) : ContDiff ℝ ∞ (θ n) := scaledCutoff_smooth hχ _
  have hi := integrable_interaction_of_growth_decay
    (fun S _ => hG _ isOpen_ball isBounded_ball) (Lp.memLp w) hC hE hR hgrowth hwdecay
  have hconv : Tendsto (fun n => ∫ x : ℂ, θ n x * inner ℝ (G x) (w x))
      atTop (𝓝 (∫ x : ℂ, inner ℝ (G x) (w x))) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖inner ℝ (G x) (w x)‖)
    · intro n
      exact (hθs n).continuous.aestronglyMeasurable.mul hi.aestronglyMeasurable
    · exact hi.norm
    · intro n
      filter_upwards with x
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (((hθ n).2.1 x).1)]
      exact mul_le_of_le_one_left (norm_nonneg _) ((hθ n).2.1 x).2
    · filter_upwards with x
      have ht : Tendsto r atTop atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<4)).atTop_mul_const (lt_of_lt_of_le zero_lt_one hR)
      apply tendsto_const_nhds.congr'
      filter_upwards [(tendsto_atTop.mp ht) ‖x‖] with n hn
      dsimp [θ]
      rw [(hθ n).2.2.1 x hn, one_mul]
  have hbound (n : ℕ) : ‖∫ x : ℂ, φ x * inner ℝ (G x) (gradient (θ n) x)‖ ≤
      (8*(D*M)*Real.sqrt (2*Real.pi*C*R^3)/R^2)*(1/2:ℝ)^n :=
    cutoff_boundary_interaction_bound hφ hG hC hD hM hR hgrowth hdecay (hθs n)
      (hθ n).1 n (hθ n).2.2.2.1 (hθ n).2.2.2.2.1
  have hc0 : Tendsto (fun n => ∫ x : ℂ, φ x * inner ℝ (G x) (gradient (θ n) x)) atTop (𝓝 0) := by
    apply squeeze_zero_norm hbound
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ)<1)).const_mul (8*(D*M)*Real.sqrt (2*Real.pi*C*R^3)/R^2)
  have hzero : Tendsto (fun n => ∫ x : ℂ, θ n x * inner ℝ (G x) (w x)) atTop (𝓝 0) := by
    simpa only [htest G hG hdiv _ (hθs _) (hθ _).1, neg_zero] using hc0.neg
  exact tendsto_nhds_unique hconv hzero

lemma memLp_local_scalar_gradient_test {a χ : ℂ → ℝ}
    (ha : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp a 2 (volume.restrict S))
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    MemLp (fun x => a x • gradient χ x) 2 volume := by
  have hal : MemLp ((tsupport χ).indicator a) 2 volume :=
    (memLp_indicator_iff_restrict (isClosed_tsupport χ).measurableSet).mpr
      (local_memLp_on_bounded ha hc.isBounded)
  have hg : MemLp (gradient χ) ∞ volume :=
    (continuous_gradient_of_smooth hχ).memLp_of_hasCompactSupport (compactSupport_gradient hc)
  apply (hal.smul hg).ae_eq
  filter_upwards with x
  by_cases hx : x ∈ tsupport χ
  · simp [hx]
  · simp [hx,gradient,fderiv_of_notMem_tsupport ℝ hx]

lemma cutoff_boundary_L2_sq_bound {a χ : ℂ → ℝ} {D M R r : ℝ}
    (ha : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp a 2 (volume.restrict S))
    (hD : 0 ≤ D) (_hM : 0 ≤ M) (hr : 0 < r) (hRr : R ≤ r)
    (haD : ∀ᵐ x ∂volume, R ≤ ‖x‖ → |a x| ≤ D/‖x‖)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hgrad : ∀ x, ‖gradient χ x‖ ≤ M/r)
    (hzero : ∀ x, (‖x‖ ≤ r ∨ 2*r ≤ ‖x‖) → gradient χ x = 0) :
    (∫ x : ℂ, ‖a x • gradient χ x‖^2) ≤ 4*Real.pi*(D*M)^2/r^2 := by
  have hi := (memLp_local_scalar_gradient_test ha hχ hc).integrable_norm_pow
    (show 2 ≠ 0 by norm_num)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := ball (0:ℂ) (2*r)) (f := fun x => ‖a x • gradient χ x‖^2) (by
      intro x hx
      have hx' : 2*r ≤ ‖x‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hx
      simp [hzero x (Or.inr hx')])]
  have hle : (∫ x in ball (0:ℂ) (2*r), ‖a x • gradient χ x‖^2) ≤
      (∫ _ in ball (0:ℂ) (2*r), (D*M/r^2)^2) := by
    apply integral_mono_ae hi.restrict (integrableOn_const (by finiteness) (by finiteness))
    filter_upwards [ae_restrict_of_ae haD] with x hx
    by_cases hxr : ‖x‖ ≤ r
    · simpa [hzero x (Or.inl hxr)] using sq_nonneg (D*M/r^2)
    · have hrx := le_of_lt (lt_of_not_ge hxr)
      have hd : |a x| ≤ D/r := (hx (hRr.trans hrx)).trans
        (div_le_div_of_nonneg_left hD hr hrx)
      have hn : ‖a x • gradient χ x‖ ≤ D*M/r^2 := by
        rw [norm_smul,Real.norm_eq_abs]
        calc
          _ ≤ (D/r)*(M/r) := mul_le_mul hd (hgrad x) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  apply hle.trans_eq
  rw [integral_const,Measure.real,Measure.restrict_apply_univ,Complex.volume_ball,
    ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*r)]
  change ((2*r)^2*Real.pi)*(D*M/r^2)^2 = 4*Real.pi*(D*M)^2/r^2
  field_simp
  ring

lemma tendsto_L2_zero_of_integral_sq {f : ℕ → ℂ → ℂ} (hf : ∀ n, MemLp (f n) 2 volume)
    (ht : Tendsto (fun n => ∫ x : ℂ, ‖f n x‖^2) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 0) := by
  have he (n : ℕ) : ‖(hf n).toLp (f n)‖^2 = ∫ x : ℂ, ‖f n x‖^2 := by
    rw [lp_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [(hf n).coeFn_toLp] with x hx
    rw [hx]
  have ht' : Tendsto (fun n => ‖(hf n).toLp (f n)‖^2) atTop (𝓝 0) := by
    simpa only [he] using ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using ht'.sqrt

theorem cutoff_field_tendsto_L2 {p q : ℂ → ℂ} (hp : MemLp p 2 volume) (hq : MemLp q 2 volume)
    {a : ℂ → ℝ}
    (ha : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp a 2 (volume.restrict S))
    {D R : ℝ} (hD : 0 ≤ D) (hR : 1 ≤ R)
    (haD : ∀ᵐ x ∂volume, R ≤ ‖x‖ → |a x| ≤ D/‖x‖)
    {χ : ℕ → ℂ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hχ : ∀ n, ContDiff ℝ ∞ (χ n)) (hc : ∀ n, HasCompactSupport (χ n))
    (hrange : ∀ n x, χ n x ∈ Icc (0:ℝ) 1)
    (hone : ∀ n x, ‖x‖ ≤ (4:ℝ)^n*R → χ n x = 1)
    (hgrad : ∀ n x, ‖gradient (χ n) x‖ ≤ M/((4:ℝ)^n*R))
    (hzero : ∀ n x, (‖x‖ ≤ (4:ℝ)^n*R ∨ 2*((4:ℝ)^n*R) ≤ ‖x‖) → gradient (χ n) x = 0) :
    ∃ hr : ∀ n, MemLp (fun x => (1-χ n x) • p x + χ n x • q x + a x • gradient (χ n) x) 2 volume,
      Tendsto (fun n => (hr n).toLp _) atTop (𝓝 (hq.toLp q)) := by
  let b (n : ℕ) (x : ℂ) := (1-χ n x) • (p x-q x)
  let c (n : ℕ) (x : ℂ) := a x • gradient (χ n) x
  have hb (n : ℕ) : MemLp (b n) 2 volume := by
    have hh : MemLp (fun x => 1-χ n x) ∞ volume :=
      (memLp_top_const (1:ℝ)).sub ((hχ n).continuous.memLp_of_hasCompactSupport (hc n))
    exact hh.smul (hp.sub hq)
  have hcl (n : ℕ) : MemLp (c n) 2 volume := memLp_local_scalar_gradient_test ha (hχ n) (hc n)
  have hbt : Tendsto (fun n => (hb n).toLp (b n)) atTop (𝓝 0) := by
    apply tendsto_L2_zero_of_integral_sq hb
    have hh : Tendsto (fun n => ∫ x : ℂ, ‖b n x‖^2) atTop (𝓝 (∫ _ : ℂ, (0:ℝ))) := by
      apply tendsto_integral_of_dominated_convergence (fun x => ‖p x-q x‖^2)
      · exact fun n => (hb n).aestronglyMeasurable.norm.pow 2
      · exact (hp.sub hq).integrable_norm_pow (by norm_num)
      · intro n
        filter_upwards with x
        have h01 := hrange n x
        have hu : |1-χ n x| ≤ 1 := (abs_le.mpr ⟨by linarith [h01.2],by linarith [h01.1]⟩)
        have hnorm : ‖b n x‖ ≤ ‖p x-q x‖ := by
          change ‖(1-χ n x) • (p x-q x)‖ ≤ ‖p x-q x‖
          rw [norm_smul,Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg _) hu
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      · filter_upwards with x
        have hrT : Tendsto (fun n : ℕ => (4:ℝ)^n*R) atTop atTop :=
          (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<4)).atTop_mul_const
            (lt_of_lt_of_le zero_lt_one hR)
        apply tendsto_const_nhds.congr'
        filter_upwards [(tendsto_atTop.mp hrT) ‖x‖] with n hn
        simp [b,hone n x hn]
    simpa using hh
  have hct : Tendsto (fun n => (hcl n).toLp (c n)) atTop (𝓝 0) := by
    apply tendsto_L2_zero_of_integral_sq hcl
    have hbound (n : ℕ) : (∫ x : ℂ, ‖c n x‖^2) ≤
        (4*Real.pi*(D*M)^2/R^2)*(1/16:ℝ)^n := by
      have hr : 0 < (4:ℝ)^n*R := mul_pos (pow_pos (by norm_num) _) (lt_of_lt_of_le zero_lt_one hR)
      have hRr : R ≤ (4:ℝ)^n*R := le_mul_of_one_le_left (le_trans zero_le_one hR)
        (one_le_pow₀ (by norm_num : (1:ℝ)≤4))
      have hh := cutoff_boundary_L2_sq_bound ha hD hM hr hRr haD (hχ n) (hc n) (hgrad n) (hzero n)
      apply hh.trans_eq
      rw [mul_pow ((4:ℝ)^n) R]
      have hp : ((4:ℝ)^n)^2 = (16:ℝ)^n := by rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
      rw [hp]
      have hi : (1/16:ℝ)^n = 1/(16:ℝ)^n := by rw [div_pow,one_pow]
      rw [hi]
      ring
    apply squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _)) hbound
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/16)
      (by norm_num : (1/16:ℝ)<1)).const_mul (4*Real.pi*(D*M)^2/R^2)
  have hr (n : ℕ) : MemLp (fun x => (1-χ n x) • p x+χ n x • q x+a x • gradient (χ n) x) 2 volume := by
    apply ((hq.add (hb n)).add (hcl n)).ae_eq
    filter_upwards with x
    change q x+(1-χ n x) • (p x-q x)+a x • gradient (χ n) x =
      (1-χ n x) • p x+χ n x • q x+a x • gradient (χ n) x
    simp only [sub_smul,smul_sub,one_smul]
    abel
  refine ⟨hr,?_⟩
  have he (n : ℕ) : (hr n).toLp _ = hq.toLp q+(hb n).toLp (b n)+(hcl n).toLp (c n) := by
    apply Lp.ext
    filter_upwards [(hr n).coeFn_toLp,hq.coeFn_toLp,(hb n).coeFn_toLp,(hcl n).coeFn_toLp,
      Lp.coeFn_add (hq.toLp q) ((hb n).toLp (b n)),
      Lp.coeFn_add (hq.toLp q+(hb n).toLp (b n)) ((hcl n).toLp (c n))] with x hrx hqx hbx hcx hax hdx
    simp only [hrx,hdx,hax,hqx,hbx,hcx,Pi.add_apply,b,c]
    simp only [sub_smul,smul_sub,one_smul]
    abel
  simpa only [he,add_zero] using (tendsto_const_nhds.add hbt).add hct

lemma cutoff_integral_tendsto {F : ℂ → ℝ} (hF : Integrable F volume)
    {χ : ℕ → ℂ → ℝ} (hχ : ∀ n, ContDiff ℝ ∞ (χ n))
    (_hc : ∀ n, HasCompactSupport (χ n))
    (hrange : ∀ n x, χ n x ∈ Icc (0:ℝ) 1)
    {R : ℝ} (hR : 0 < R)
    (hone : ∀ n x, ‖x‖ ≤ (4:ℝ)^n*R → χ n x = 1) :
    Tendsto (fun n => ∫ x : ℂ, χ n x * F x) atTop (𝓝 (∫ x : ℂ, F x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖F x‖)
  · intro n
    exact (hχ n).continuous.aestronglyMeasurable.mul hF.aestronglyMeasurable
  · exact hF.norm
  · intro n
    filter_upwards with x
    rw [norm_mul, Real.norm_eq_abs,abs_of_nonneg (hrange n x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hrange n x).2
  · filter_upwards with x
    have hrT : Tendsto (fun n : ℕ => (4:ℝ)^n*R) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<4)).atTop_mul_const hR
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_atTop.mp hrT) ‖x‖] with n hn
    simp [hone n x hn]

lemma cutoff_mul_integrable {F χ : ℂ → ℝ} (hF : Integrable F volume)
    (hχ : ContDiff ℝ ∞ χ) (hrange : ∀ x, χ x ∈ Icc (0:ℝ) 1) :
    Integrable (fun x => χ x*F x) volume := by
  apply hF.norm.mono' (hχ.continuous.aestronglyMeasurable.mul hF.aestronglyMeasurable)
  filter_upwards with x
  change ‖χ x*F x‖ ≤ ‖F x‖
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hrange x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (hrange x).2

theorem cutoff_field_interaction_limit {p q G : ℂ → ℂ} {a : ℂ → ℝ}
    (hip : Integrable (fun x => inner ℝ (G x) (p x)) volume)
    (hiq : Integrable (fun x => inner ℝ (G x) (q x)) volume)
    (ha : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp a 2 (volume.restrict S))
    (hG : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp G 2 (volume.restrict S))
    {C D R : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 1 ≤ R)
    (hgrowth : ∀ T : ℝ, 1 ≤ T → (∫ x in ball (0:ℂ) T, ‖G x‖^2) ≤ C*(1+T))
    (haD : ∀ᵐ x ∂volume, R ≤ ‖x‖ → |a x| ≤ D/‖x‖)
    {χ : ℕ → ℂ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hχ : ∀ n, ContDiff ℝ ∞ (χ n)) (hc : ∀ n, HasCompactSupport (χ n))
    (hrange : ∀ n x, χ n x ∈ Icc (0:ℝ) 1)
    (hone : ∀ n x, ‖x‖ ≤ (4:ℝ)^n*R → χ n x = 1)
    (hgrad : ∀ n x, ‖gradient (χ n) x‖ ≤ M/((4:ℝ)^n*R))
    (hzero : ∀ n x, (‖x‖ ≤ (4:ℝ)^n*R ∨ 2*((4:ℝ)^n*R) ≤ ‖x‖) → gradient (χ n) x = 0) :
    (∀ n, Integrable (fun x => inner ℝ (G x)
      ((1-χ n x) • p x+χ n x • q x+a x • gradient (χ n) x)) volume) ∧
    Tendsto (fun n => ∫ x : ℂ, inner ℝ (G x)
      ((1-χ n x) • p x+χ n x • q x+a x • gradient (χ n) x)) atTop
      (𝓝 (∫ x : ℂ, inner ℝ (G x) (q x))) := by
  have hcI (n : ℕ) := integrable_local_scalar_inner_test ha hG (hχ n) (hc n)
  have hpI (n : ℕ) := cutoff_mul_integrable hip (hχ n) (hrange n)
  have hqI (n : ℕ) := cutoff_mul_integrable hiq (hχ n) (hrange n)
  have he (n : ℕ) (x : ℂ) : inner ℝ (G x)
      ((1-χ n x) • p x+χ n x • q x+a x • gradient (χ n) x) =
      inner ℝ (G x) (p x)-χ n x*inner ℝ (G x) (p x)+
      χ n x*inner ℝ (G x) (q x)+a x*inner ℝ (G x) (gradient (χ n) x) := by
    simp only [inner_add_right,inner_smul_right]
    ring
  refine ⟨fun n => by simpa only [he,Pi.add_apply,Pi.sub_apply] using ((hip.sub' (hpI n)).fun_add (hqI n)).fun_add (hcI n), ?_⟩
  have hcT : Tendsto (fun n => ∫ x : ℂ, a x*inner ℝ (G x) (gradient (χ n) x)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => cutoff_boundary_interaction_bound ha hG hC hD hM hR
      hgrowth haD (hχ n) (hc n) n (hgrad n) (hzero n))
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ)<1)).const_mul (8*(D*M)*Real.sqrt (2*Real.pi*C*R^3)/R^2)
  have hpT := cutoff_integral_tendsto hip hχ hc hrange (lt_of_lt_of_le zero_lt_one hR) hone
  have hqT := cutoff_integral_tendsto hiq hχ hc hrange (lt_of_lt_of_le zero_lt_one hR) hone
  have ht := ((tendsto_const_nhds (x := ∫ x : ℂ, inner ℝ (G x) (p x))).sub hpT).add hqT |>.add hcT
  have hEqI (n : ℕ) : (∫ x : ℂ, inner ℝ (G x)
      ((1-χ n x) • p x+χ n x • q x+a x • gradient (χ n) x)) =
      (∫ x : ℂ, inner ℝ (G x) (p x))-(∫ x : ℂ, χ n x*inner ℝ (G x) (p x))+
      (∫ x : ℂ, χ n x*inner ℝ (G x) (q x))+(∫ x : ℂ, a x*inner ℝ (G x) (gradient (χ n) x)) := by
    simp_rw [he]
    rw [integral_add ((hip.sub' (hpI n)).fun_add (hqI n)) (hcI n),
      integral_add (hip.sub' (hpI n)) (hqI n),integral_sub hip (hpI n)]
  simpa only [hEqI,sub_self,zero_add,add_zero] using ht

lemma norm_sq_energy_difference (G p q : ℂ) :
    ‖G+q‖^2-‖G+p‖^2 = 2*(inner ℝ G q-inner ℝ G p)+‖q‖^2-‖p‖^2 := by
  rw [norm_add_sq_real,norm_add_sq_real]
  ring

lemma integral_finite_energy_difference {G p q : ℂ → ℂ}
    (hp : MemLp p 2 volume) (hq : MemLp q 2 volume)
    (hGp : Integrable (fun x => inner ℝ (G x) (p x)) volume)
    (hGq : Integrable (fun x => inner ℝ (G x) (q x)) volume)
    {R : ℝ} (hG : MemLp G 2 (volume.restrict (ball (0:ℂ) R)))
    (hcompact : ∀ᵐ x ∂volume, x ∉ ball (0:ℂ) R → q x = p x) :
    (∫ x in ball (0:ℂ) R, ‖G x+q x‖^2) - (∫ x in ball (0:ℂ) R, ‖G x+p x‖^2) =
      2*((∫ x : ℂ, inner ℝ (G x) (q x))-(∫ x : ℂ, inner ℝ (G x) (p x)))+
      (∫ x : ℂ, ‖q x‖^2)-(∫ x : ℂ, ‖p x‖^2) := by
  have hpI := hp.integrable_norm_pow (show 2 ≠ 0 by norm_num)
  have hqI := hq.integrable_norm_pow (show 2 ≠ 0 by norm_num)
  have hD : Integrable (fun x => 2*(inner ℝ (G x) (q x)-inner ℝ (G x) (p x))+
      ‖q x‖^2-‖p x‖^2) volume :=
    (((hGq.sub' hGp).const_mul 2).fun_add hqI).sub' hpI
  have hD0 : ∀ᵐ x ∂volume, x ∉ ball (0:ℂ) R →
      2*(inner ℝ (G x) (q x)-inner ℝ (G x) (p x))+‖q x‖^2-‖p x‖^2 = 0 := by
    filter_upwards [hcompact] with x hx hn
    simp [hx hn]
  have hGIq : Integrable (fun x => ‖G x+q x‖^2) (volume.restrict (ball (0:ℂ) R)) := by
    simpa only [Pi.add_apply] using (hG.add (hq.restrict _)).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hGIp : Integrable (fun x => ‖G x+p x‖^2) (volume.restrict (ball (0:ℂ) R)) := by
    simpa only [Pi.add_apply] using (hG.add (hp.restrict _)).integrable_norm_pow (by norm_num : 2 ≠ 0)
  rw [← integral_sub hGIq hGIp]
  simp_rw [norm_sq_energy_difference]
  rw [setIntegral_eq_integral_of_ae_compl_eq_zero hD0,
    integral_sub (((hGq.sub' hGp).const_mul 2).fun_add hqI) hpI,
    integral_add ((hGq.sub' hGp).const_mul 2) hqI,integral_const_mul,
    integral_sub hGq hGp]

theorem finite_energy_limit_inequality {G p q : ℂ → ℂ} {r : ℕ → ℂ → ℂ}
    (hp : MemLp p 2 volume) (hq : MemLp q 2 volume)
    (hr : ∀ n, MemLp (r n) 2 volume)
    (hL2 : Tendsto (fun n => (hr n).toLp (r n)) atTop (𝓝 (hq.toLp q)))
    (hG : ∀ R : ℝ, MemLp G 2 (volume.restrict (ball (0:ℂ) R)))
    (hGp : Integrable (fun x => inner ℝ (G x) (p x)) volume)
    (hGr : ∀ n, Integrable (fun x => inner ℝ (G x) (r n x)) volume)
    (hI : Tendsto (fun n => ∫ x : ℂ, inner ℝ (G x) (r n x)) atTop
      (𝓝 (∫ x : ℂ, inner ℝ (G x) (q x))))
    (hcomp : ∀ n, ∃ R : ℝ,
      (∀ᵐ x ∂volume, x ∉ ball (0:ℂ) R → r n x = p x) ∧
      (∫ x in ball (0:ℂ) R, ‖G x+p x‖^2) ≤ ∫ x in ball (0:ℂ) R, ‖G x+r n x‖^2) :
    0 ≤ 2*((∫ x : ℂ, inner ℝ (G x) (q x))-(∫ x : ℂ, inner ℝ (G x) (p x)))+
      (∫ x : ℂ, ‖q x‖^2)-(∫ x : ℂ, ‖p x‖^2) := by
  have he {g : ℂ → ℂ} (hg : MemLp g 2 volume) : ‖hg.toLp g‖^2 = ∫ x : ℂ, ‖g x‖^2 := by
    rw [lp_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]
  have hqT : Tendsto (fun n => ∫ x : ℂ, ‖r n x‖^2) atTop (𝓝 (∫ x : ℂ, ‖q x‖^2)) := by
    simpa only [he] using hL2.norm.pow 2
  have hT := (((hI.sub_const (∫ x : ℂ, inner ℝ (G x) (p x))).const_mul 2).add hqT).sub_const
    (∫ x : ℂ, ‖p x‖^2)
  apply ge_of_tendsto hT
  filter_upwards with n
  obtain ⟨R,hRc,hRe⟩ := hcomp n
  rw [← integral_finite_energy_difference hp (hr n) hGp (hGr n) (hG R) hRc]
  exact sub_nonneg.mpr hRe

end MumfordShah
end

end OAI
