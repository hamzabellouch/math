import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.MomentumBall

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators

theorem phase_bathtub {f : Space → ℝ}
    (hf0 : 0 ≤ᵐ[volume] f) (hf2 : f ≤ᵐ[volume] fun _ => 2*coherentFactor)
    (hf : Integrable f) (hk : Integrable (fun p => ‖p‖^2*f p)) :
    tfKinetic*(∫ p, f p)^(5/3:ℝ) ≤ (1/2:ℝ)*∫ p, ‖p‖^2*f p := by
  let M := ∫ p, f p
  have hM : 0 ≤ M := integral_nonneg_of_ae hf0
  let R := fermiRadius (fun _ => M) 0
  have hR : 0 ≤ R := fermiRadius_nonneg (fun _ => hM) _
  let F : Space → ℝ := (ball 0 R).indicator (fun _ => 2*coherentFactor)
  have hF : Integrable F := by
    apply (integrable_indicator_iff measurableSet_ball).2
    exact integrableOn_const measure_ball_lt_top.ne
  have hFK : Integrable (fun p => ‖p‖^2*F p) := by
    have hc : IntegrableOn (fun p : Space => ‖p‖^2*(2*coherentFactor)) (ball 0 R) :=
      (by fun_prop : Continuous (fun p : Space => ‖p‖^2*(2*coherentFactor))).continuousOn.integrableOn_compact
        (isCompact_closedBall (0:Space) R) |>.mono_set ball_subset_closedBall
    have hh : Integrable ((ball 0 R).indicator (fun p : Space => ‖p‖^2*(2*coherentFactor))) :=
      (integrable_indicator_iff measurableSet_ball).2 hc
    exact hh.congr (Filter.Eventually.of_forall (fun p =>
      Set.indicator_mul_right _ (fun p : Space => ‖p‖^2) (fun _ => 2*coherentFactor)))
  have hmass : (∫ p, F p) = M := by
    rw [integral_indicator measurableSet_ball,integral_const]
    simpa only [smul_eq_mul,Measure.real,Measure.restrict_apply_univ,mul_comm,R] using fermiRadius_ball_mass (fun _ => hM) (0:Space)
  have hkin : (1/2:ℝ)*(∫ p, ‖p‖^2*F p) = tfKinetic*M^(5/3:ℝ) := by
    have heq : (fun p => ‖p‖^2*F p) = (ball 0 R).indicator (fun p => ‖p‖^2*(2*coherentFactor)) := by
      ext p
      exact (Set.indicator_mul_right _ (fun p : Space => ‖p‖^2) (fun _ => 2*coherentFactor)).symm
    rw [heq]
    rw [integral_indicator measurableSet_ball,integral_mul_const]
    have he := fermiRadius_ball_kinetic (fun _ => hM) (0:Space)
    change coherentFactor*(∫ p : Space in ball 0 R, ‖p‖^2) = _ at he
    nlinarith
  have hi : (∫ p, (‖p‖^2-R^2)*F p) ≤ ∫ p, (‖p‖^2-R^2)*f p := by
    have hiF : Integrable (fun p => (‖p‖^2-R^2)*F p) := by
      convert hFK.sub (hF.const_mul (R^2)) using 1
      ext p
      change (‖p‖^2-R^2)*F p = ‖p‖^2*F p-R^2*F p
      ring
    have hif : Integrable (fun p => (‖p‖^2-R^2)*f p) := by
      convert hk.sub (hf.const_mul (R^2)) using 1
      ext p
      change (‖p‖^2-R^2)*f p = ‖p‖^2*f p-R^2*f p
      ring
    apply integral_mono_ae hiF hif
    filter_upwards [hf0,hf2] with p hp0 hp2
    by_cases hp : p ∈ ball (0:Space) R
    · have hn : ‖p‖ < R := by simpa only [mem_ball,dist_zero_right] using hp
      have hsq : ‖p‖^2-R^2 ≤ 0 := sub_nonpos.mpr (pow_le_pow_left₀ (norm_nonneg _) hn.le 2)
      simpa only [F,Set.indicator_of_mem hp] using mul_le_mul_of_nonpos_left hp2 hsq
    · have hn : R ≤ ‖p‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hp
      have hsq : 0 ≤ ‖p‖^2-R^2 := sub_nonneg.mpr (pow_le_pow_left₀ hR hn 2)
      simpa only [F,Set.indicator_of_notMem hp,mul_zero] using mul_nonneg hsq hp0
  simp only [sub_mul] at hi
  rw [integral_sub hFK (hF.const_mul _),integral_sub hk (hf.const_mul _),
    integral_const_mul,integral_const_mul,hmass] at hi
  change (∫ p, ‖p‖^2*F p)-R^2*M ≤ (∫ p, ‖p‖^2*f p)-R^2*M at hi
  linarith

open MeasureTheory Set Metric
open scoped BigOperators ENNReal

def momentumInterval (n : ℕ) : Set ℝ :=
  Ioo (-Real.pi*(n+1)) (-Real.pi*n) ∪ Ioo (Real.pi*n) (Real.pi*(n+1))

lemma measurableSet_momentumInterval (n : ℕ) : MeasurableSet (momentumInterval n) :=
  measurableSet_Ioo.union measurableSet_Ioo

lemma momentumInterval_abs {n : ℕ} {x : ℝ} (hx : x ∈ momentumInterval n) :
    Real.pi*n < |x| ∧ |x| < Real.pi*(n+1) := by
  have hp := Real.pi_pos
  rcases hx with hx | hx
  · rw [abs_of_neg (by nlinarith [hx.2,mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)] : x < 0)]
    constructor <;> nlinarith [hx.1,hx.2]
  · rw [abs_of_pos (by nlinarith [hx.1,mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)] : 0 < x)]
    exact hx

lemma momentumInterval_disjoint {m n : ℕ} (h : m ≠ n) :
    Disjoint (momentumInterval m) (momentumInterval n) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hh := momentumInterval_abs hx
  have hk := momentumInterval_abs hy
  rcases lt_or_gt_of_ne h with hmn | hnm
  · have hc : (m:ℝ)+1 ≤ n := by exact_mod_cast hmn
    nlinarith [Real.pi_pos]
  · have hc : (n:ℝ)+1 ≤ m := by exact_mod_cast hnm
    nlinarith [Real.pi_pos]

lemma volume_momentumInterval (n : ℕ) : volume (momentumInterval n) = ENNReal.ofReal (2*Real.pi) := by
  unfold momentumInterval
  have hd : Disjoint (Ioo (-Real.pi*(n+1)) (-Real.pi*n)) (Ioo (Real.pi*n) (Real.pi*(n+1))) := by
    rw [Set.disjoint_left]
    intro x hx hy
    nlinarith [hx.2,hy.1,Real.pi_pos]
  rw [measure_union hd measurableSet_Ioo,Real.volume_Ioo,Real.volume_Ioo]
  have h1 : -Real.pi*(n:ℝ)-(-Real.pi*(n+1)) = Real.pi := by ring
  have h2 : Real.pi*((n:ℝ)+1)-Real.pi*n = Real.pi := by ring
  rw [h1,h2,←ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

def momentumCell (n : Fin 3 → ℕ) : Set Space :=
  {p | ∀ i, p i ∈ momentumInterval (n i)}

lemma measurableSet_momentumCell (n : Fin 3 → ℕ) : MeasurableSet (momentumCell n) := by
  simp only [momentumCell,Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => (measurableSet_momentumInterval _).preimage (by fun_prop)

lemma volume_momentumCell (n : Fin 3 → ℕ) :
    volume (momentumCell n) = ENNReal.ofReal ((2*Real.pi)^3) := by
  have he : momentumCell n = (WithLp.ofLp : Space → Fin 3 → ℝ) ⁻¹'
      (Set.pi univ (fun i => momentumInterval (n i))) := by ext p; simp [momentumCell]
  rw [he,(PiLp.volume_preserving_ofLp (ι := Fin 3)).measure_preimage ((MeasurableSet.pi (Set.to_countable _) (fun i _ => measurableSet_momentumInterval (n i))).nullMeasurableSet),volume_pi_pi]
  simp only [volume_momentumInterval,Finset.prod_const,Finset.card_fin]
  rw [←ENNReal.ofReal_pow (by positivity)]

lemma momentumCell_disjoint {m n : Fin 3 → ℕ} (h : m ≠ n) :
    Disjoint (momentumCell m) (momentumCell n) := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp h
  rw [Set.disjoint_left]
  intro x hx hy
  exact Set.disjoint_left.mp (momentumInterval_disjoint hi) (hx i) (hy i)

lemma momentumCell_norm_sq {n : Fin 3 → ℕ} {p : Space} (hp : p ∈ momentumCell n) :
    ‖p‖^2 ≤ Real.pi^2*∑ i, ((n i:ℝ)+1)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := (momentumInterval_abs (hp i)).2.le
  calc (p i)^2 = |p i|^2 := (sq_abs _).symm
    _ ≤ (Real.pi*((n i:ℝ)+1))^2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := by ring

end CoulombAtom

end

end OAI
