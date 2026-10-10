import OAI.MathematicalPhysics.Boltzmann.Branching.GainEntropyTail
import OAI.MathematicalPhysics.Boltzmann.Branching.MarginalUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Branching.PublishedInputs
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWeakMarginals
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

section

/-! # Uniformly integrable families admit bounded truncations without spatial tightness -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem uniform_value_truncation (f : ℕ → X → ℂ) (hf : ∀ n, Measurable (f n))
    (hui : UniformIntegrable f 1 μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∃ u : ℕ → X → ℂ,
      (∀ n, Measurable (u n)) ∧ (∀ n x, ‖u n x‖ ≤ C) ∧
      (∀ n x, f n x = 0 → u n x = 0) ∧
      (∀ n x, ‖u n x‖ ≤ ‖f n x‖) ∧
      (∀ n, eLpNorm (f n-u n) 1 μ ≤ ε) := by
  obtain ⟨C,hC⟩ := hui.spec (by norm_num) (by norm_num) hε
  let u (n : ℕ) : X → ℂ := {x | ‖f n x‖₊ < C}.indicator (f n)
  have hm n : MeasurableSet {x | ‖f n x‖₊ < C} :=
    measurableSet_lt (hf n).nnnorm measurable_const
  refine ⟨C,u,fun n => (hf n).indicator (hm n),?_,?_,?_,?_⟩
  · intro n x
    by_cases hx : ‖f n x‖₊ < C
    · simpa [u,hx] using (show ‖f n x‖ ≤ (C:ℝ) by exact_mod_cast le_of_lt hx)
    · simp [u,hx]
  · intro n x hx
    simp [u,hx]
  · intro n x
    by_cases ht : ‖f n x‖₊ < C <;> simp [u,ht]
  · intro n
    have he : f n-u n = {x | C ≤ ‖f n x‖₊}.indicator (f n) := by
      funext x
      by_cases ht : ‖f n x‖₊ < C
      · simp [u,ht,not_le.mpr ht]
      · simp [u,ht,le_of_not_gt ht]
    rw [he]
    exact hC n

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Finite-measure bounded truncations of a uniformly integrable tight family -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem uniform_L1_bounded_truncation (f : ℕ → X → ℝ)
    (hf : ∀ n, Measurable (f n)) (hui : UniformIntegrable f 1 μ)
    (ht : UnifTight f 1 μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (S : Set X) (C : ℝ≥0) (u : ℕ → X → ℝ),
      MeasurableSet S ∧ μ S < ∞ ∧
      (∀ n, Measurable (u n)) ∧ (∀ n x, ‖u n x‖ ≤ C) ∧
      (∀ n x, x ∉ S → u n x = 0) ∧
      ∀ n, eLpNorm (f n-u n) 1 μ ≤ ε+ε := by
  classical
  obtain ⟨S,hS,hμS,hSerr⟩ := ht.exists_measurableSet_indicator hε.ne'
  obtain ⟨C,hCerr⟩ := hui.spec (by norm_num) (by norm_num) hε
  let A : ℕ → Set X := fun n => {x | C ≤ ‖f n x‖₊}
  have hA n : MeasurableSet (A n) := measurableSet_le measurable_const (hf n).nnnorm
  let u : ℕ → X → ℝ := fun n => (S ∩ (A n)ᶜ).indicator (f n)
  refine ⟨S,C,u,hS,hμS,?_,?_,?_,?_⟩
  · intro n
    exact (hf n).indicator (hS.inter (hA n).compl)
  · intro n x
    by_cases hx : x ∈ S ∩ (A n)ᶜ
    · rw [show u n x = f n x from indicator_of_mem hx _]
      exact le_of_lt (by exact_mod_cast (lt_of_not_ge hx.2 : ‖f n x‖₊ < C))
    · simp [u,indicator_of_notMem hx,C.coe_nonneg]
  · intro n x hx
    exact indicator_of_notMem (fun h => hx h.1) _
  · intro n
    have he : f n-u n = Sᶜ.indicator (f n) + S.indicator ((A n).indicator (f n)) := by
      funext x
      by_cases hx : x ∈ S <;> by_cases ha : x ∈ A n <;> simp [u,hx,ha]
    rw [he]
    exact (eLpNorm_add_le (by norm_num)).trans
      (add_le_add (hSerr n) ((eLpNorm_indicator_le _ hS).trans (hCerr n)))

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Uniform integrability of marginals with fixed finite-measure velocity support -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem uniformIntegrable_integral_of_support {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {s : Set Y} [IsFiniteMeasure (ν.restrict s)]
    (hs : MeasurableSet s) {f : ℕ → X × Y → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hui : UniformIntegrable f 1 (μ.prod ν))
    (hf : ∀ n x y, y ∉ s → f n (x,y) = 0) :
    UniformIntegrable (fun n x => ∫ y, f n (x,y) ∂ν) 1 μ := by
  have hu := uniformIntegrable_restrict hui (univ ×ˢ s)
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hu
  have h := uniformIntegrable_integral hfm hu
  have he (n : ℕ) (x : X) : (∫ y in s, f n (x,y) ∂ν) = ∫ y, f n (x,y) ∂ν := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ s
    · exact indicator_of_mem hy _
    · rw [indicator_of_notMem hy,hf n x y hy]
  simpa only [he] using h

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # A vanishing logarithmic gain tail gives uniform integrability -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem uniformIntegrable_of_logarithmic_tail {G L : ℕ → X → ℝ} {B : ℝ≥0∞}
    (hGm : ∀ n, Measurable (G n)) (hLm : ∀ n, Measurable (L n))
    (hG : ∀ n x, 0 ≤ G n x) (hL : ∀ n x, 0 ≤ L n x)
    (hLi : UniformIntegrable L 1 μ) (hB : B < ⊤)
    (htail : ∀ R : ℝ, 2 ≤ R → ∀ n,
      (∫⁻ x, ENNReal.ofReal (G n x-R*L n x) ∂μ) ≤ ENNReal.ofReal (2/Real.log R)*B) :
    UniformIntegrable G 1 μ := by
  let R : ℕ → ℝ := fun j => (j:ℝ)+2
  have hR j : 2 ≤ R j := by
    dsimp [R]
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  let u : ℕ → ℕ → X → ℝ := fun j n x => min (G n x) (R j*L n x)
  have hum j n : Measurable (u j n) := (hGm n).min (measurable_const.mul (hLm n))
  apply uniformIntegrable_of_approximation (g := u)
  · intro j
    let C : ℝ≥0 := ⟨R j,by linarith [hR j]⟩
    have hC : ∀ x : X, |R j| ≤ C := fun _ => by
      change |R j| ≤ R j
      rw [abs_of_nonneg (by linarith [hR j])]
    have hs := uniformIntegrable_of_bounded_multiplier hLi (a := fun _ => R j) measurable_const C hC
    apply CollisionCompactness.uniformIntegrable_mono_nonneg hs (fun n => (hum j n).aestronglyMeasurable)
    · exact fun n => ae_of_all _ (fun x => le_min (hG n x) (mul_nonneg (by linarith [hR j]) (hL n x)))
    · exact fun n => ae_of_all _ (fun x => min_le_right _ _)
  · intro ε hε
    have hRt : Tendsto R atTop atTop := tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have hc : Tendsto (fun j => ENNReal.ofReal (2/Real.log (R j))) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero,Function.comp_def] using ENNReal.tendsto_ofReal (scaled_entropy_cost_tendsto.comp hRt)
    have hcB := ENNReal.Tendsto.mul_const hc (Or.inr hB.ne)
    simp only [zero_mul] at hcB
    obtain ⟨j,hj⟩ := (hcB.eventually (gt_mem_nhds hε)).exists
    refine ⟨j,fun n => ?_⟩
    have hme : Measurable (fun x => G n x-u j n x) := (hGm n).sub (hum j n)
    rw [eLpNorm_one_eq_lintegral_enorm hme.aestronglyMeasurable]
    have he (x : X) : ‖G n x-u j n x‖ₑ = ENNReal.ofReal (G n x-R j*L n x) := by
      change ‖G n x-min (G n x) (R j*L n x)‖ₑ = _
      rw [Real.enorm_eq_ofReal (sub_nonneg.mpr (min_le_left _ _))]
      by_cases hx : G n x ≤ R j*L n x
      · simp only [min_eq_left hx,sub_self,ENNReal.ofReal_zero,
          ENNReal.ofReal_of_nonpos (sub_nonpos.mpr hx)]
      · rw [min_eq_right (le_of_not_ge hx)]
    simp only [he]
    exact (htail (R j) (hR j) n).trans hj.le

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
