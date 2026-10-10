import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.HighProjection
import OAI.Analysis.CoulombRadii.Localization.DyadicTailPartial

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb

lemma FermionicCoefficients.weighted_eq {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f)
    (w : α → ℝ) (i j : Fin n) :
    (∑' b, w (b i) * ‖f b‖^2) = ∑' b, w (b j) * ‖f b‖^2 := by
  classical
  let p := Equiv.swap i j
  have he := (coefficientPermEquiv (α := α) p).tsum_eq
    (fun b => w (b i) * ‖f b‖^2)
  change (∑' b, w ((b ∘ p) i) * ‖f (b ∘ p)‖^2) = _ at he
  simp only [Function.comp_apply, p, Equiv.swap_apply_left, hf.norm_permute] at he
  exact he.symm

lemma FermionicCoefficients.weighted_summable {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} {w : α → ℝ} (hw : ∀ a, 0 ≤ w a)
    (hs : Summable (fun b => (∑ j, w (b j)) * ‖f b‖^2)) (i : Fin n) :
    Summable (fun b => w (b i) * ‖f b‖^2) := by
  apply Summable.of_nonneg_of_le (fun b => mul_nonneg (hw _) (sq_nonneg _)) _ hs
  intro b
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hw (b j)) (Finset.mem_univ i)) (sq_nonneg _)

lemma FermionicCoefficients.weighted_sum {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f)
    {w : α → ℝ} (hw : ∀ a, 0 ≤ w a)
    (hs : Summable (fun b => (∑ j, w (b j)) * ‖f b‖^2)) (i : Fin n) :
    (n : ℝ) * (∑' b, w (b i) * ‖f b‖^2) =
      ∑' b, (∑ j, w (b j)) * ‖f b‖^2 := by
  simp_rw [Finset.sum_mul]
  rw [Summable.tsum_finsetSum (fun j _ => weighted_summable hw hs j)]
  simp_rw [hf.weighted_eq w _ i]
  simp

end Coulomb
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb

lemma nonneg_integrable_series {A ι : Type*} [MeasurableSpace A] [Countable ι]
    {μ : Measure A} (F : ι → A → ℝ) (hF0 : ∀ i x, 0 ≤ F i x)
    (hFi : ∀ i, Integrable (F i) μ) (hs : Summable (fun i => ∫ x, F i x ∂μ)) :
    (∀ᵐ x ∂μ, Summable (fun i => F i x)) ∧
    Integrable (fun x => ∑' i, F i x) μ ∧
    (∫ x, ∑' i, F i x ∂μ) = ∑' i, ∫ x, F i x ∂μ := by
  have hm (i : ι) : AEMeasurable (fun x => ENNReal.ofReal (F i x)) μ :=
    (hFi i).1.aemeasurable.ennreal_ofReal
  have he (i : ι) : eLpNorm (F i) 1 μ = ENNReal.ofReal (∫ x, F i x ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hFi i).1]
    simp_rw [Real.enorm_of_nonneg (hF0 i _)]
    exact (ofReal_integral_eq_lintegral_ofReal (hFi i) (ae_of_all μ (hF0 i))).symm
  have hfin : (∑' i, eLpNorm (F i) 1 μ) ≠ ∞ := by
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg (hF0 i)) hs]
    exact ENNReal.ofReal_ne_top
  have has : ∀ᵐ x ∂μ, Summable (fun i => F i x) := by
    have H := summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl hfin
    simpa only [Real.norm_of_nonneg (hF0 _ _)] using H
  have hsum : (∫⁻ x, ∑' i, ENNReal.ofReal (F i x) ∂μ) ≠ ∞ := by
    rw [lintegral_tsum hm]
    convert hfin using 2
    funext i
    rw [eLpNorm_one_eq_lintegral_enorm (hFi i).1]
    simp only [Real.enorm_of_nonneg (hF0 _ _)]
  have ht := integrable_toReal_of_lintegral_ne_top (AEMeasurable.tsum hm) hsum
  have hti : Integrable (fun x => ∑' i, F i x) μ := by
    apply ht.congr
    filter_upwards [has] with x hx
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hF0 i x) hx,
      ENNReal.toReal_ofReal (tsum_nonneg (fun i => hF0 i x))]
  refine ⟨has, hti, ?_⟩
  exact (integral_tsum_of_summable_integral_norm hFi
    (by simpa only [Real.norm_of_nonneg (hF0 _ _)] using hs)).symm

noncomputable def firstParticleDensity {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {n : ℕ} (f : (Fin (n+1) → A) → ℂ) (x : A) : ℝ :=
  ((n+1:ℕ):ℝ)*(∫ y : Fin n → A, ‖firstFiber f (y,x)‖^2 ∂(Measure.pi fun _ => μ))

noncomputable def highParticleDensity {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} {n : ℕ} (v : ι → A → ℂ) (s : Finset ι)
    (f : (Fin (n+1) → A) → ℂ) (x : A) : ℝ :=
  ((n+1:ℕ):ℝ)*(∫ y : Fin n → A,
    ‖highProjection (μ := μ) v s (firstFiber f) (y,x)‖^2 ∂(Measure.pi fun _ => μ))

lemma firstParticleDensity_integrable {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ)) :
    Integrable (firstParticleDensity (μ := μ) f) μ :=
  (firstFiber_memLp hf).norm.integrable_sq.integral_prod_right.const_mul _

lemma highParticleDensity_integrable {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ) (s : Finset ι) :
    Integrable (highParticleDensity (μ := μ) v s f) μ :=
  (highProjection_memLp v hv s (firstFiber_memLp hf)).norm.integrable_sq.integral_prod_right.const_mul _

lemma highParticleDensity_integral {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [Countable ι] {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) (s : Finset ι) :
    (∫ x, highParticleDensity (μ := μ) v s f x ∂μ) =
      ((n+1:ℕ):ℝ)*(∑' b, if b 0 ∈ s then 0 else ‖scalarCoefficient (μ := μ) f v b‖^2) := by
  simp only [highParticleDensity]
  rw [integral_const_mul, ← integral_prod_symm _
    (highProjection_memLp v hv s (firstFiber_memLp hf)).norm.integrable_sq,
      highProjection_norm_spectrum v hv ho hc hf s]

lemma high_density_spectral_series {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [Countable ι] {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ)) (ha : ProductAntisymmetric (μ := μ) f)
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) (s : ℕ → Finset ι) (w : ι → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hcut : ∀ k a, a ∉ s k → (4:ℝ)^k < w a)
    (hs : Summable (fun b : Fin (n+1) → ι => (∑ j, w (b j))*
      ‖scalarCoefficient (μ := μ) f v b‖^2)) :
    Summable (fun k : ℕ => (4:ℝ)^k * ∫ x, highParticleDensity (μ := μ) v (s k) f x ∂μ) ∧
    (∑' k : ℕ, (4:ℝ)^k * ∫ x, highParticleDensity (μ := μ) v (s k) f x ∂μ) ≤
      (4/3:ℝ)*(∑' b : Fin (n+1) → ι, (∑ j, w (b j))*
        ‖scalarCoefficient (μ := μ) f v b‖^2) := by
  classical
  let c := scalarCoefficient (μ := μ) f v
  have hc2 : Summable (fun b => ‖c b‖^2) := scalarCoefficient_summable f hf v hv ho
  have hsingle := FermionicCoefficients.weighted_summable hw hs (0 : Fin (n+1))
  have H := dyadic_spectral_tail_bound (fun b : Fin (n+1) → ι => w (b 0))
    (fun b => ‖c b‖^2) (fun b => hw (b 0)) (fun b => sq_nonneg _) hsingle
  have hsum (k : ℕ) : Summable (fun b : Fin (n+1) → ι =>
      if (4:ℝ)^k < w (b 0) then ‖c b‖^2 else 0) :=
    Summable.of_nonneg_of_le (fun b => by positivity)
      (fun b => by split_ifs <;> simp) hc2
  have hcomp (k : ℕ) : (∫ x, highParticleDensity (μ := μ) v (s k) f x ∂μ) ≤
      ((n+1:ℕ):ℝ)*(∑' b : Fin (n+1) → ι, if (4:ℝ)^k < w (b 0) then ‖c b‖^2 else 0) := by
    rw [highParticleDensity_integral hf v hv ho hc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Summable.tsum_le_tsum _ _ (hsum k)
    · intro b
      by_cases hb : b 0 ∈ s k
      · simp only [hb, ite_true]; positivity
      · simp only [hb, ite_false, hcut k (b 0) hb, ite_true]
        exact le_rfl
    · change Summable (fun b => if b 0 ∈ s k then 0 else ‖c b‖^2)
      exact Summable.of_nonneg_of_le (fun b => by positivity)
        (fun b => by split_ifs <;> simp) hc2
  have hl (k : ℕ) : 0 ≤ (4:ℝ)^k * ∫ x, highParticleDensity (μ := μ) v (s k) f x ∂μ := by
    apply mul_nonneg (by positivity)
    exact integral_nonneg (fun x => mul_nonneg (by positivity) (integral_nonneg (fun y => sq_nonneg _)))
  have hb (k : ℕ) : (4:ℝ)^k * ∫ x, highParticleDensity (μ := μ) v (s k) f x ∂μ ≤
      ((n+1:ℕ):ℝ)*((4:ℝ)^k * ∑' b : Fin (n+1) → ι,
        if (4:ℝ)^k < w (b 0) then ‖c b‖^2 else 0) := by
    simpa only [mul_left_comm ((4:ℝ)^k)] using mul_le_mul_of_nonneg_left (hcomp k) (by positivity : 0 ≤ (4:ℝ)^k)
  have hs' := Summable.of_nonneg_of_le hl hb (H.1.mul_left ((n+1:ℕ):ℝ))
  refine ⟨hs', ?_⟩
  calc
    _ ≤ ((n+1:ℕ):ℝ)*(∑' k : ℕ, (4:ℝ)^k * ∑' b : Fin (n+1) → ι,
        if (4:ℝ)^k < w (b 0) then ‖c b‖^2 else 0) := by
      simpa only [tsum_mul_left] using hs'.tsum_le_tsum hb (H.1.mul_left ((n+1:ℕ):ℝ))
    _ ≤ ((n+1:ℕ):ℝ)*((4/3:ℝ)*(∑' b : Fin (n+1) → ι, w (b 0)*‖c b‖^2)) :=
      mul_le_mul_of_nonneg_left H.2 (by positivity)
    _ = _ := by
      rw [mul_left_comm, (scalarCoefficient_antisymmetric ha v).weighted_sum hw hs]

end Coulomb

end OAI
