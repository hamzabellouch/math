import OAI.MathematicalPhysics.Boltzmann.Collision.VelocitySmoothingError
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongPairMoment

namespace OAI

section

/-! # Four vanishing error terms have a vanishing nonnegative L1 sum -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem real_eLpNorm_abs {f : X → ℝ} (hf : Measurable f) :
    eLpNorm (fun x => |f x|) 1 μ = eLpNorm f 1 μ := by
  simpa only [Real.norm_eq_abs] using eLpNorm_norm f hf.aestronglyMeasurable

theorem strongL1_sub_of_common_limit {f g : ℕ → X → ℝ} {h : X → ℝ}
    (hf : Tendsto (fun n => eLpNorm (fun x => f n x-h x) 1 μ) atTop (𝓝 0))
    (hg : Tendsto (fun n => eLpNorm (fun x => g n x-h x) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => f n x-g n x) 1 μ) atTop (𝓝 0) := by
  have ht := hf.add hg
  simp only [zero_add] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  have he : (fun x => f n x-g n x) = (fun x => f n x-h x)+(fun x => h x-g n x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  dsimp only
  rw [he]
  exact (eLpNorm_add_le (by norm_num)).trans_eq
    (congrArg (fun t => eLpNorm (fun x => f n x-h x) 1 μ+t) (eLpNorm_sub_comm h (g n) 1 μ))

theorem strongL1_abs_sum_four {a b c d : ℕ → X → ℝ}
    (ham : ∀ n, Measurable (a n)) (hbm : ∀ n, Measurable (b n))
    (hcm : ∀ n, Measurable (c n)) (hdm : ∀ n, Measurable (d n))
    (ha : Tendsto (fun n => eLpNorm (a n) 1 μ) atTop (𝓝 0))
    (hb : Tendsto (fun n => eLpNorm (b n) 1 μ) atTop (𝓝 0))
    (hc : Tendsto (fun n => eLpNorm (c n) 1 μ) atTop (𝓝 0))
    (hd : Tendsto (fun n => eLpNorm (d n) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => |a n x|+|b n x|+|c n x|+|d n x|) 1 μ) atTop (𝓝 0) := by
  have ht := ((ha.add hb).add hc).add hd
  simp only [zero_add] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  have he : (fun x => |a n x|+|b n x|+|c n x|+|d n x|) =
      ((fun x => |a n x|)+(fun x => |b n x|))+(fun x => |c n x|)+(fun x => |d n x|) := rfl
  dsimp only
  rw [he]
  calc
    _ ≤ (eLpNorm ((fun x => |a n x|)+(fun x => |b n x|)) 1 μ+
        eLpNorm (fun x => |c n x|) 1 μ)+eLpNorm (fun x => |d n x|) 1 μ :=
      (eLpNorm_add_le (by norm_num)).trans
        (add_le_add (eLpNorm_add_le (by norm_num)) le_rfl)
    _ ≤ ((eLpNorm (fun x => |a n x|) 1 μ+eLpNorm (fun x => |b n x|) 1 μ)+
        eLpNorm (fun x => |c n x|) 1 μ)+eLpNorm (fun x => |d n x|) 1 μ :=
      add_le_add (add_le_add (eLpNorm_add_le (by norm_num)) le_rfl) le_rfl
    _ = _ := by rw [real_eLpNorm_abs (ham n),real_eLpNorm_abs (hbm n),
      real_eLpNorm_abs (hcm n),real_eLpNorm_abs (hdm n)]

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Passing velocity translation continuity through uniform L1 approximation -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem velocityTranslation_compare {F H : X × Velocity → ℝ}
    (hF : Integrable F (μ.prod volume)) (hH : Integrable H (μ.prod volume)) (a : Velocity) :
    (∫ p, |F (p.1,p.2+a)-F p| ∂μ.prod volume) ≤
      2*(∫ p, |F p-H p| ∂μ.prod volume)+
        (∫ p, |H (p.1,p.2+a)-H p| ∂μ.prod volume) := by
  have hFs := (velocityShift_preserving μ a).integrable_comp_of_integrable hF
  have hHs := (velocityShift_preserving μ a).integrable_comp_of_integrable hH
  have hA : Integrable (fun p => |F (p.1,p.2+a)-H (p.1,p.2+a)|) (μ.prod volume) :=
    (hFs.sub hHs).abs
  have hB : Integrable (fun p => |H (p.1,p.2+a)-H p|) (μ.prod volume) := (hHs.sub hH).abs
  have hC : Integrable (fun p => |F p-H p|) (μ.prod volume) := (hF.sub hH).abs
  have hs := (velocityShift_preserving μ a).integral_comp (velocityShift a).measurableEmbedding
    (fun p => |F p-H p|)
  calc
    _ ≤ ∫ p, (|F (p.1,p.2+a)-H (p.1,p.2+a)|+|H (p.1,p.2+a)-H p|)+|F p-H p|
        ∂μ.prod volume := by
      apply integral_mono (hFs.sub hF).abs ((hA.add hB).add hC)
      intro p
      change |F (p.1,p.2+a)-F p| ≤
        (|F (p.1,p.2+a)-H (p.1,p.2+a)|+|H (p.1,p.2+a)-H p|)+|F p-H p|
      have h1 := abs_sub_le (F (p.1,p.2+a)) (H (p.1,p.2+a)) (H p)
      have h2 := abs_sub_le (F (p.1,p.2+a)) (H p) (F p)
      rw [abs_sub_comm (H p) (F p)] at h2
      linarith
    _ = (∫ p, |F (p.1,p.2+a)-H (p.1,p.2+a)|+|H (p.1,p.2+a)-H p| ∂μ.prod volume)+
        (∫ p, |F p-H p| ∂μ.prod volume) := integral_add (hA.add hB) hC
    _ = ((∫ p, |F (p.1,p.2+a)-H (p.1,p.2+a)| ∂μ.prod volume)+
        (∫ p, |H (p.1,p.2+a)-H p| ∂μ.prod volume))+
        (∫ p, |F p-H p| ∂μ.prod volume) :=
      congrArg (fun r => r+(∫ p, |F p-H p| ∂μ.prod volume)) (integral_add hA hB)
    _ = _ := by
      change (∫ p, |F (velocityShift a p)-H (velocityShift a p)| ∂μ.prod volume)+
        (∫ p, |H (p.1,p.2+a)-H p| ∂μ.prod volume)+(∫ p, |F p-H p| ∂μ.prod volume) = _
      rw [hs]
      ring

theorem velocityTranslation_of_uniform_L1_approximation
    {F : ℕ → X × Velocity → ℝ} (hF : ∀ n, Integrable (F n) (μ.prod volume))
    {a : ℕ → Velocity}
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ H : ℕ → X × Velocity → ℝ,
      (∀ n, Integrable (H n) (μ.prod volume)) ∧
      (∀ n, (∫ p, |F n p-H n p| ∂μ.prod volume) ≤ ε) ∧
      Tendsto (fun n => ∫ p, |H n (p.1,p.2+a n)-H n p| ∂μ.prod volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p, |F n (p.1,p.2+a n)-F n p| ∂μ.prod volume) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨H,hHi,hHe,hHt⟩ := happrox (ε/4) (by positivity)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hHt (ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hnn := hN n hn
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg (fun p => abs_nonneg _))] at hnn ⊢
  have hc := velocityTranslation_compare (hF n) (hHi n) (a n)
  linarith [hHe n]

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
