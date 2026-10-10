import OAI.MathematicalPhysics.Boltzmann.Branching.RawPairCompactness
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityPolynomialBounds
import Mathlib.Topology.UrysohnsLemma

namespace OAI

section

/-! # Linear hard-sphere tails controlled by the product Gaussian moment -/

noncomputable section

open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.CollisionCompactness

theorem pair_rate_le_gaussian_tail {R : ℝ} (hR : 1 ≤ R) (v w : Velocity)
    (htail : R ≤ ‖v‖ ∨ R ≤ ‖w‖) :
    R*(1+‖v‖+‖w‖) ≤ 6*(weight v*weight w) := by
  let M := max ‖v‖ ‖w‖
  have hv : ‖v‖ ≤ M := le_max_left _ _
  have hw : ‖w‖ ≤ M := le_max_right _ _
  have hRM : R ≤ M := htail.elim (fun h => h.trans hv) (fun h => h.trans hw)
  have hM : 0 ≤ M := (norm_nonneg v).trans hv
  have hvw : ‖v‖^2/2 ≤ weight v := by
    have h := Real.add_one_le_exp (‖v‖^2/2)
    change _ ≤ Real.exp _
    linarith
  have hww : ‖w‖^2/2 ≤ weight w := by
    have h := Real.add_one_le_exp (‖w‖^2/2)
    change _ ≤ Real.exp _
    linarith
  have hp : M^2/2 ≤ weight v*weight w := by
    rcases le_total ‖v‖ ‖w‖ with h | h
    · rw [show M = ‖w‖ from max_eq_right h]
      exact hww.trans (le_mul_of_one_le_left (weight_pos w).le (weight_one_le v))
    · rw [show M = ‖v‖ from max_eq_left h]
      exact hvw.trans (le_mul_of_one_le_right (weight_pos v).le (weight_one_le w))
  calc
    R*(1+‖v‖+‖w‖) ≤ M*(1+‖v‖+‖w‖) := mul_le_mul_of_nonneg_right hRM (by positivity)
    _ ≤ M*(3*M) := mul_le_mul_of_nonneg_left (by linarith) hM
    _ ≤ 6*(weight v*weight w) := by nlinarith

theorem pair_tail_le_gaussian {R : ℝ} (hR : 1 ≤ R) (p : Velocity × Velocity) :
    (if R ≤ ‖p.1‖ ∨ R ≤ ‖p.2‖ then 1+‖p.1‖+‖p.2‖ else 0) ≤
      (6/R)*(weight p.1*weight p.2) := by
  have hpos : 0 < R := zero_lt_one.trans_le hR
  split_ifs with hp
  · calc
      _ ≤ (6*(weight p.1*weight p.2))/R := (le_div_iff₀ hpos).mpr (by
        simpa only [mul_comm R] using pair_rate_le_gaussian_tail hR p.1 p.2 hp)
      _ = _ := by ring
  · exact mul_nonneg (div_nonneg (by norm_num) hpos.le)
      (mul_nonneg (weight_pos _).le (weight_pos _).le)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Compact approximation of linearly growing collision tests in Gaussian norm -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.CollisionCompactness

theorem exists_compact_gaussian_approximation (f : C(Velocity × Velocity, ℝ))
    {L : ℝ} (hL : 0 ≤ L) (hf : ∀ p, |f p| ≤ L*(1+‖p.1‖+‖p.2‖))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : C(Velocity × Velocity, ℝ), HasCompactSupport g ∧
      ∀ p, |g p-f p| ≤ δ*(weight p.1*weight p.2) := by
  let R := max 1 (6*L/δ)
  have hR : 1 ≤ R := le_max_left _ _
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hδR : 6*L/R ≤ δ := (div_le_iff₀ hRp).mpr (by
    have hb : 6*L/δ ≤ R := le_max_right _ _
    have hc := (div_le_iff₀ hδ).mp hb
    nlinarith)
  obtain ⟨β,hβone,hβc,_,hβ⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (isCompact_closedBall (0 : Velocity × Velocity) R) isOpen_univ (subset_univ _)
  refine ⟨β*f,(show HasCompactSupport β from hβc).mul_right,fun p => ?_⟩
  by_cases hp : p ∈ Metric.closedBall (0 : Velocity × Velocity) R
  · have he : β p = 1 := hβone hp
    simp only [ContinuousMap.mul_apply,he,one_mul,sub_self,abs_zero]
    exact mul_nonneg hδ.le (mul_nonneg (weight_pos _).le (weight_pos _).le)
  · have hn : ¬ max ‖p.1‖ ‖p.2‖ ≤ R := by
      simp only [Metric.mem_closedBall,dist_zero_right] at hp
      exact hp
    have ht : R ≤ ‖p.1‖ ∨ R ≤ ‖p.2‖ :=
      (lt_max_iff.mp (lt_of_not_ge hn)).imp le_of_lt le_of_lt
    have hb : |β p-1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [(hβ p).1,(hβ p).2]
    calc
      |(β*f) p-f p| = |β p-1| *|f p| := by
        rw [ContinuousMap.mul_apply,← abs_mul]
        congr 1
        ring
      _ ≤ |f p| := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (abs_nonneg (f p))
      _ ≤ L*(1+‖p.1‖+‖p.2‖) := hf p
      _ ≤ L*((6/R)*(weight p.1*weight p.2)) := by
        apply mul_le_mul_of_nonneg_left _ hL
        have hb := pair_tail_le_gaussian hR p
        simpa only [ite_eq_left ht] using hb
      _ = (6*L/R)*(weight p.1*weight p.2) := by ring
      _ ≤ δ*(weight p.1*weight p.2) := mul_le_mul_of_nonneg_right hδR
        (mul_nonneg (weight_pos _).le (weight_pos _).le)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Pair products depend only on the almost-everywhere density representative -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem pairProduct_congr {μ : Measure X} [SFinite μ] {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (he : f =ᵐ[μ.prod volume] g) :
    pairProduct f =ᵐ[μ.prod (volume : Measure (Velocity × Velocity))] pairProduct g := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (pairProduct_measurable hfm) (pairProduct_measurable hgm))).mpr
  filter_upwards [Measure.ae_ae_of_ae_prod he] with x hx
  have hl : ∀ᵐ (y : Velocity × Velocity) ∂((volume : Measure Velocity).prod (volume : Measure Velocity)), f (x,y.1) = g (x,y.1) :=
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Velocity))
      (ν := (volume : Measure Velocity))).ae hx
  have hr : ∀ᵐ (y : Velocity × Velocity) ∂((volume : Measure Velocity).prod (volume : Measure Velocity)), f (x,y.2) = g (x,y.2) :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Velocity))
      (ν := (volume : Measure Velocity))).ae hx
  rw [Measure.volume_eq_prod]
  filter_upwards [hl,hr] with y hy hz
  simp only [pairProduct,hy,hz]

theorem pairDensity_congr {μ : Measure X} [SFinite μ] {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (he : f =ᵐ[μ.prod volume] g) :
    pairDensity f =ᵐ[μ.prod (volume : Measure (Velocity × Velocity))] pairDensity g := by
  filter_upwards [pairProduct_congr hfm hgm he] with z hz
  change f (z.1,z.2.1)*f (z.1,z.2.2) = g (z.1,z.2.1)*g (z.1,z.2.2) at hz
  simp only [pairDensity,mul_assoc]
  rw [hz]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
