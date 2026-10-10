import Mathlib
import OAI.Analysis.CoulombIonization.Localization.SubGaussianMoments

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_WeightedMoments_scope

open MeasureTheory Finset
open scoped BigOperators

lemma weighted_pow_sum_le {ι : Type*} [Fintype ι] (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i) (k : ℕ) :
    (∑ i, w i * x i) ^ (k+1) ≤ (∑ i, w i) ^ k * ∑ i, w i * x i ^ (k+1) := by
  classical
  let W := ∑ i, w i
  have hW : 0 ≤ W := sum_nonneg (fun i _ => hw i)
  by_cases hzero : W = 0
  · have hwz : ∀ i, w i = 0 := by
      intro i
      have hh : w i ≤ W := single_le_sum (fun j _ => hw j) (mem_univ i)
      linarith [hw i]
    simp [hwz]
  have hWp : 0 < W := lt_of_le_of_ne hW (Ne.symm hzero)
  have hj := (convexOn_pow (𝕜 := ℝ) (k+1)).map_sum_le
    (t := univ) (w := fun i => w i / W) (p := x)
    (fun i _ => div_nonneg (hw i) hW)
    (by rw [← sum_div]; exact div_self hzero)
    (fun i _ => hx i)
  simp only [smul_eq_mul] at hj
  have he (y : ι → ℝ) : (∑ i, w i / W * y i) = (∑ i, w i * y i) / W := by
    rw [sum_div]
    congr 1
    funext i
    ring
  rw [he x, he (fun i => x i ^ (k+1)), div_pow] at hj
  have hj' := (div_le_div_iff₀ (pow_pos hWp (k+1)) hWp).mp hj
  rw [pow_succ W] at hj'
  apply (mul_le_mul_iff_left₀ hWp).mp
  calc
    _ ≤ (∑ i, w i * x i ^ (k + 1)) * (W ^ k * W) := hj'
    _ = _ := by dsimp [W]; ring

lemma integral_weighted_pow_sum_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} (w : ι → ℝ) (X : ι → Ω → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hX : ∀ i sample, 0 ≤ X i sample) (k : ℕ)
    (hi : Integrable (fun sample => (∑ i, w i * X i sample) ^ (k+1)) μ)
    (hXi : ∀ i, Integrable (fun sample => X i sample ^ (k+1)) μ) :
    (∫ sample, (∑ i, w i * X i sample) ^ (k+1) ∂μ) ≤
      (∑ i, w i) ^ k * ∑ i, w i * (∫ sample, X i sample ^ (k+1) ∂μ) := by
  have hs := integrable_finsetSum univ (fun i _ => (hXi i).const_mul (w i))
  have hh := integral_mono hi (hs.const_mul ((∑ i, w i)^k))
    (fun sample => weighted_pow_sum_le w (fun i => X i sample) hw (fun i => hX i sample) k)
  simpa only [integral_const_mul, integral_finsetSum _ (fun i _ =>
    (hXi i).const_mul (w i))] using hh

end Work_WeightedMoments_scope

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal BigOperators

def signFlip (b : Bool) : ℝ ≃ᵐ ℝ :=
  if b then MeasurableEquiv.refl ℝ else MeasurableEquiv.neg ℝ

def signFlipPi {ι : Type*} (ε : ι → Bool) : (ι → ℝ) ≃ᵐ (ι → ℝ) :=
  MeasurableEquiv.piCongrRight (fun i => signFlip (ε i))

lemma signFlip_preserving {μ : Measure ℝ} (hneg : MeasurePreserving Neg.neg μ μ)
    (b : Bool) : MeasurePreserving (signFlip b) μ μ := by
  cases b
  · exact hneg
  · exact MeasurePreserving.id μ

lemma signFlipPi_preserving {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hneg : ∀ i, MeasurePreserving Neg.neg (μ i) (μ i))
    (ε : ι → Bool) :
    MeasurePreserving (signFlipPi ε) (Measure.pi μ) (Measure.pi μ) :=
  measurePreserving_pi μ μ (fun i => signFlip_preserving (hneg i) (ε i))

lemma odd_signFlip {X : ℝ → ℝ} (hodd : Function.Odd X) (b : Bool) (x : ℝ) :
    X (signFlip b x) = observationSign b * X x := by
  cases b <;> simp [signFlip, observationSign, hodd x]

lemma even_moment_integrable_of_memLp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {k : ℕ} (hk : 0 < k)
    (h : MemLp X (2*k : ℕ) μ) : Integrable (fun sample => X sample ^ (2*k)) μ := by
  have hi := h.integrable_norm_pow (show 2*k ≠ 0 by omega)
  simpa only [Real.norm_eq_abs, pow_mul, sq_abs] using hi

lemma coordinate_sum_even_integrable {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (X : ι → ℝ → ℝ) (a : ι → ℝ)
    {k : ℕ} (hk : 0 < k) (hi : ∀ i, MemLp (X i) (2*k : ℕ) (μ i)) :
    Integrable (fun x => (∑ i, a i * X i (x i)) ^ (2*k)) (Measure.pi μ) := by
  apply even_moment_integrable_of_memLp hk
  exact memLp_finsetSum univ (fun i _ =>
    ((hi i).comp_measurePreserving (measurePreserving_eval μ i)).const_mul (a i))

lemma odd_coordinate_sum_moment_invariant {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hneg : ∀ i, MeasurePreserving Neg.neg (μ i) (μ i))
    (X : ι → ℝ → ℝ) (hodd : ∀ i, Function.Odd (X i))
    (a : ι → ℝ) (ε : ι → Bool) (k : ℕ) :
    (∫ x, (∑ i, (a i * X i (x i)) * observationSign (ε i)) ^ (2*k) ∂Measure.pi μ) =
      ∫ x, (∑ i, a i * X i (x i)) ^ (2*k) ∂Measure.pi μ := by
  have hp := signFlipPi_preserving μ hneg ε
  have he := hp.integral_comp' (fun x => (∑ i, a i * X i (x i)) ^ (2*k))
  convert he using 1
  congr 1
  ext x
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change a i * X i (x i) * observationSign (ε i) = a i * X i (signFlip (ε i) (x i))
  rw [odd_signFlip (hodd i)]
  ring

lemma integral_finite_swap {Ω β : Type*} [MeasurableSpace Ω]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {μ : Measure Ω} {ν : Measure β} [IsFiniteMeasure ν]
    (F : β → Ω → ℝ) (hi : ∀ b, Integrable (F b) μ) :
    (∫ x, (∫ b, F b x ∂ν) ∂μ) = ∫ b, (∫ x, F b x ∂μ) ∂ν := by
  simp_rw [integral_fintype (μ := ν) Integrable.of_finite]
  simp only [smul_eq_mul]
  rw [integral_finsetSum univ (fun b _ => (hi b).const_mul (ν.real {b}))]
  simp only [integral_const_mul]

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal BigOperators

lemma integral_comp_preserving_of_measurable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {f : α → β} (hf : MeasurePreserving f μ ν) {g : β → ℝ} (hg : Measurable g) :
    (∫ x, g (f x) ∂μ) = ∫ y, g y ∂ν := by
  calc
    _ = ∫ y, g y ∂μ.map f := (integral_map hf.aemeasurable hg.aestronglyMeasurable).symm
    _ = _ := by rw [hf.map_eq]

theorem symmetric_directional_moment_le {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hneg : ∀ i, MeasurePreserving Neg.neg (μ i) (μ i))
    (X : ι → ℝ → ℝ) (hX : ∀ i, Measurable (X i))
    (hodd : ∀ i, Function.Odd (X i)) (a : ι → ℝ) {k : ℕ} (hk : 0 < k)
    (hMem : ∀ i, MemLp (X i) (2*k : ℕ) (μ i))
    (M : ℝ) (hMom : ∀ i, (∫ u, X i u ^ (2*k) ∂μ i) ≤ M^(2*k)) :
    (∫ x, (∑ i, a i * X i (x i)) ^ (2*k) ∂Measure.pi μ) ≤
      (8 * Real.exp 1 * k)^k * (∑ i, a i^2)^k * M^(2*k) := by
  classical
  obtain ⟨l, rfl⟩ : ∃ l, k = l+1 := ⟨k-1, by omega⟩
  let A : ℝ := ∑ i, a i^2
  let Y : (ι → ℝ) → ℝ := fun x => ∑ i, a i^2 * X i (x i)^2
  let L : ℝ := 8 * Real.exp 1 * (l+1)
  let F : (ι → Bool) → (ι → ℝ) → ℝ :=
    fun ε x => (∑ i, (a i * X i (x i)) * observationSign (ε i)) ^ (2*(l+1))
  have hA : 0 ≤ A := sum_nonneg (fun i _ => sq_nonneg (a i))
  have hY : ∀ x, 0 ≤ Y x := fun x =>
    sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hmY : Measurable Y := by
    apply Finset.measurable_sum
    intro i _
    exact ((hX i).comp (measurable_pi_apply i) |>.pow_const 2).const_mul _
  have hXi (i : ι) : Integrable (fun x : ι → ℝ => (X i (x i)^2)^(l+1)) (Measure.pi μ) := by
    have hh := even_moment_integrable_of_memLp hk
      ((hMem i).comp_measurePreserving (measurePreserving_eval μ i))
    simpa only [Function.comp_apply, pow_mul] using hh
  have hJ (x : ι → ℝ) : Y x ^ (l+1) ≤
      A^l * ∑ i, a i^2 * (X i (x i)^2)^(l+1) :=
    weighted_pow_sum_le (fun i => a i^2) (fun i => X i (x i)^2)
      (fun i => sq_nonneg _) (fun i => sq_nonneg _) l
  have hB : Integrable (fun x : ι → ℝ => A^l * ∑ i, a i^2 *
      (X i (x i)^2)^(l+1)) (Measure.pi μ) :=
    (integrable_finsetSum univ (fun i _ => (hXi i).const_mul (a i^2))).const_mul _
  have hiY : Integrable (fun x => Y x^(l+1)) (Measure.pi μ) := by
    refine hB.mono' (hmY.pow_const _).aestronglyMeasurable (ae_of_all _ ?_)
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hY x) _)]
    exact hJ x
  have hiF (ε : ι → Bool) : Integrable (F ε) (Measure.pi μ) := by
    have hh := coordinate_sum_even_integrable μ X
      (fun i => a i * observationSign (ε i)) hk hMem
    convert hh using 1
    ext x
    dsimp [F]
    congr 1
    apply sum_congr rfl
    intro i _
    ring
  have hiAvg : Integrable (fun x => ∫ ε, F ε x ∂signProduct ι) (Measure.pi μ) := by
    simp_rw [integral_fintype (μ := signProduct ι) Integrable.of_finite]
    simp only [smul_eq_mul]
    exact integrable_finsetSum univ (fun ε _ => (hiF ε).const_mul ((signProduct ι).real {ε}))
  have havg : (∫ x, (∫ ε, F ε x ∂signProduct ι) ∂Measure.pi μ) =
      ∫ x, (∑ i, a i * X i (x i)) ^ (2*(l+1)) ∂Measure.pi μ := by
    rw [integral_finite_swap F hiF]
    have hh (ε : ι → Bool) : (∫ x, F ε x ∂Measure.pi μ) =
        ∫ x, (∑ i, a i * X i (x i)) ^ (2*(l+1)) ∂Measure.pi μ :=
      odd_coordinate_sum_moment_invariant μ hneg X hodd a ε (l+1)
    simp_rw [hh]
    simp
  have hpoint (x : ι → ℝ) : (∫ ε, F ε x ∂signProduct ι) ≤ L^(l+1) * Y x^(l+1) := by
    have hh := sign_sum_even_moment_le (fun i => a i * X i (x i)) hk
    simpa only [F, Y, L, mul_pow, Nat.cast_add, Nat.cast_one] using hh
  have hAvg := integral_mono hiAvg (hiY.const_mul (L^(l+1))) hpoint
  rw [havg, integral_const_mul] at hAvg
  have hYbound : (∫ x, Y x^(l+1) ∂Measure.pi μ) ≤ A^(l+1) * M^(2*(l+1)) := by
    have hh := integral_weighted_pow_sum_le (fun i => a i^2)
      (fun (i : ι) (x : ι → ℝ) => X i (x i)^2) (fun i => sq_nonneg _)
      (fun i x => sq_nonneg _) l hiY hXi
    have hscalar (i : ι) : (∫ x : ι → ℝ, (X i (x i)^2)^(l+1) ∂Measure.pi μ) ≤
        M^(2*(l+1)) := by
      simp_rw [← pow_mul]
      rw [integral_comp_preserving_of_measurable (measurePreserving_eval μ i)
        ((hX i).pow_const (2*(l+1)))]
      exact hMom i
    calc
      _ ≤ A^l * ∑ i, a i^2 * (∫ x : ι → ℝ, (X i (x i)^2)^(l+1) ∂Measure.pi μ) := hh
      _ ≤ A^l * ∑ i, a i^2 * M^(2*(l+1)) := by
        gcongr with i
        exact hscalar i
      _ = _ := by rw [← sum_mul]; dsimp [A]; ring
  calc
    _ ≤ L^(l+1) * (∫ x, Y x^(l+1) ∂Measure.pi μ) := hAvg
    _ ≤ L^(l+1) * (A^(l+1) * M^(2*(l+1))) :=
      mul_le_mul_of_nonneg_left hYbound (by dsimp [L]; positivity)
    _ = _ := by dsimp [L, A]; push_cast; ring

end CoulombObservation

end

end OAI
