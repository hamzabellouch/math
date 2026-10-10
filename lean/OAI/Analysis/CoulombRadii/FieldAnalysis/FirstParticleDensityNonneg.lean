import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.SpinMode
import OAI.Analysis.CoulombRadii.FieldAnalysis.Weighted

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb

lemma firstParticleDensity_nonneg {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {n : ℕ} (f : (Fin (n+1) → A) → ℂ) (x : A) :
    0 ≤ firstParticleDensity (μ := μ) f x :=
  mul_nonneg (by positivity) (integral_nonneg (fun y => sq_nonneg _))

lemma highParticleDensity_nonneg {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} {n : ℕ} (v : ι → A → ℂ) (s : Finset ι)
    (f : (Fin (n+1) → A) → ℂ) (x : A) :
    0 ≤ highParticleDensity (μ := μ) v s f x :=
  mul_nonneg (by positivity) (integral_nonneg (fun y => sq_nonneg _))

lemma firstParticleDensity_integral {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ)) :
    (∫ x, firstParticleDensity (μ := μ) f x ∂μ) =
      ((n+1:ℕ):ℝ)*(∫ z, ‖f z‖^2 ∂(Measure.pi fun _ => μ)) := by
  simp only [firstParticleDensity]
  rw [integral_const_mul, ← integral_prod_symm _ (firstFiber_memLp hf).norm.integrable_sq,
    ← firstUnfiber_norm_sq]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by simp [firstUnfiber, firstFiber, Fin.cons_self_tail])

lemma memLp_fiber_right_ae {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]
    {f : B × A → ℂ} (hf : MemLp f 2 (ν.prod μ)) :
    ∀ᵐ x ∂μ, MemLp (fun y => f (y,x)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_right, hf.norm.integrable_sq.prod_left_ae] with x hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).2 hi

lemma first_density_low_high_cap {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [SecondCountableTopology (Lp ℂ 2 μ)] {n : ℕ}
    {f : (Fin (n+1) → A) → ℂ} (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (ha : ProductAntisymmetric (μ := μ) f)
    (hn : (∫ z, ‖f z‖^2 ∂(Measure.pi fun _ => μ)) ≤ 1)
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (s : ℕ → Finset ι) {B : ℝ}
    (hdiag : ∀ k x, (∑ i ∈ s k, ‖v i x‖^2) ≤ B*(8:ℝ)^k) :
    ∀ᵐ x ∂μ, ∀ k, firstParticleDensity (μ := μ) f x ≤ 2*B*(8:ℝ)^k +
      2*highParticleDensity (μ := μ) v (s k) f x := by
  filter_upwards [memLp_fiber_right_ae (firstFiber_memLp hf)] with x hx k
  have hp := lowProjection_density_pauli f hf ha v hv ho (s k) x
  have hp' : ((n+1:ℕ):ℝ) * (∫ y : Fin n → A,
      ‖lowProjection (μ := μ) v (s k) (firstFiber f) (y,x)‖^2 ∂(Measure.pi fun _ => μ)) ≤
      ∑ i ∈ s k, ‖v i x‖^2 := by
    apply hp.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn
      (Finset.sum_nonneg (fun i _ => sq_nonneg (‖v i x‖)))
  have hh := fiber_norm_sq_split hx (lowProjection_tail_memLp v hv (s k) (firstFiber_memLp hf) x)
  have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ ((n+1:ℕ):ℝ))
  have hd := hdiag k x
  dsimp only [firstParticleDensity, highParticleDensity, highProjection, Pi.sub_apply]
  nlinarith only [hh', hp', hd]

lemma continuum_rumin_bound {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [Countable ι] [SecondCountableTopology (Lp ℂ 2 μ)]
    {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ)) (ha : ProductAntisymmetric (μ := μ) f)
    (hn : (∫ z, ‖f z‖^2 ∂(Measure.pi fun _ => μ)) ≤ 1)
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) (s : ℕ → Finset ι) (w : ι → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hcut : ∀ k a, a ∉ s k → (4:ℝ)^k < w a)
    {B : ℝ} (hB : 0 < B) (hdiag : ∀ k x, (∑ i ∈ s k, ‖v i x‖^2) ≤ B*(8:ℝ)^k)
    (hs : Summable (fun b : Fin (n+1) → ι => (∑ j, w (b j))*
      ‖scalarCoefficient (μ := μ) f v b‖^2)) :
    Integrable (fun x => (firstParticleDensity (μ := μ) f x)^(5/3:ℝ)) μ ∧
    (∫ x, (firstParticleDensity (μ := μ) f x)^(5/3:ℝ) ∂μ) ≤
      (32*B)^(2/3:ℝ)*((n+1:ℕ):ℝ) + (16/3:ℝ)*(32*B)^(2/3:ℝ) *
        (∑' b : Fin (n+1) → ι, (∑ j, w (b j))*‖scalarCoefficient (μ := μ) f v b‖^2) := by
  let r := firstParticleDensity (μ := μ) f
  let h (k : ℕ) := highParticleDensity (μ := μ) v (s k) f
  let C := (32*B)^(2/3:ℝ)
  have hC : 0 ≤ C := Real.rpow_nonneg (by positivity) _
  have hr0 (x : A) : 0 ≤ r x := firstParticleDensity_nonneg f x
  have hh0 (k : ℕ) (x : A) : 0 ≤ h k x := highParticleDensity_nonneg v (s k) f x
  have hri : Integrable r μ := firstParticleDensity_integrable hf
  have hhi (k : ℕ) : Integrable (h k) μ := highParticleDensity_integrable hf v hv (s k)
  have hspec := high_density_spectral_series hf ha v hv ho hc s w hw hcut hs
  have hser := nonneg_integrable_series (fun k x => (4:ℝ)^k*h k x)
    (fun k x => mul_nonneg (by positivity) (hh0 k x))
    (fun k => (hhi k).const_mul ((4:ℝ)^k))
    (by simpa only [integral_const_mul] using hspec.1)
  have hcap := first_density_low_high_cap hf ha hn v hv ho s hdiag
  have hbound : ∀ᵐ x ∂μ, (r x)^(5/3:ℝ) ≤ C*r x + (4*C)*(∑' k, (4:ℝ)^k*h k x) := by
    filter_upwards [hser.1, hcap] with x hx hc'
    exact dyadic_density_bound hB (hr0 x) (fun k => h k x) (fun k => hh0 k x) hx hc'
  have hright : Integrable (fun x => C*r x+(4*C)*(∑' k, (4:ℝ)^k*h k x)) μ :=
    (hri.const_mul C).add (hser.2.1.const_mul (4*C))
  have hl : Integrable (fun x => (r x)^(5/3:ℝ)) μ := by
    apply hright.mono' ((hri.1.aemeasurable.pow_const (5/3:ℝ)).aestronglyMeasurable)
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (hr0 x) _)] using hx
  refine ⟨hl, ?_⟩
  have H := integral_mono_ae hl hright hbound
  rw [integral_add (hri.const_mul C) (hser.2.1.const_mul (4*C)),
    integral_const_mul, integral_const_mul, hser.2.2] at H
  simp_rw [integral_const_mul] at H
  have hm : (∫ x, r x ∂μ) ≤ ((n+1:ℕ):ℝ) := by
    rw [firstParticleDensity_integral hf]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ ((n+1:ℕ):ℝ))
  have hm' := mul_le_mul_of_nonneg_left hm hC
  have he := mul_le_mul_of_nonneg_left hspec.2 (by positivity : 0 ≤ 4*C)
  dsimp only [C] at H he hm'
  nlinarith only [H, he, hm']

lemma neumannMode_sq_bound {b : ℝ} (hb : 0 < b) (q : ℕ) (x : ℝ) :
    ‖neumannMode b q x‖^2 ≤ 2/b := by
  have hw : 0 < cosineWeight b q := by unfold cosineWeight; split_ifs <;> positivity
  have he : ‖neumannMode b q x‖^2 =
      (Real.cos ((q : ℝ)*Real.pi*x/b))^2 / cosineWeight b q := by
    change ‖(((Real.sqrt (cosineWeight b q))⁻¹ : ℝ) : ℂ) *
      (Real.cos ((q : ℝ)*Real.pi*x/b) : ℂ)‖^2 = _
    rw [norm_mul, mul_pow, Complex.norm_real, Complex.norm_real]
    simp only [Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hw.le]
    ring
  rw [he]
  calc
    _ ≤ 1 / cosineWeight b q := div_le_div_of_nonneg_right (Real.cos_sq_le_one _) hw.le
    _ ≤ 2/b := by unfold cosineWeight; split_ifs <;> field_simp <;> nlinarith

lemma cubeMode_sq_bound {b : ℝ} (hb : 0 < b) (q : Fin 3 → ℕ) (x : Fin 3 → ℝ) :
    ‖cubeMode b q x‖^2 ≤ 8/b^3 := by
  calc
    _ = ∏ i : Fin 3, ‖neumannMode b (q i) (x i)‖^2 := by
      simp only [cubeMode, norm_prod, Finset.prod_pow]
    _ ≤ ∏ i : Fin 3, (2/b) := Finset.prod_le_prod₀
      (fun i _ => sq_nonneg _) (fun i _ => neumannMode_sq_bound hb (q i) (x i))
    _ = _ := by simp; ring

lemma spinCubeMode_sq_bound {b : ℝ} (hb : 0 < b) (a : SpinMode)
    (x : Fin 2 × (Fin 3 → ℝ)) : ‖spinCubeMode b a x‖^2 ≤ 8/b^3 := by
  by_cases hs : x.1 = a.1
  · simpa only [spinCubeMode, spinDelta, hs, ite_true, one_mul] using cubeMode_sq_bound hb a.2 x.2
  · simp only [spinCubeMode, spinDelta, hs, ite_false, zero_mul, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

def coarseCubeModes (k : ℕ) : Finset SpinMode :=
  Finset.univ.product (Fintype.piFinset fun _ : Fin 3 => Finset.range (2^k+1))

lemma coarseCubeModes_card (k : ℕ) : (coarseCubeModes k).card = 2*(2^k+1)^3 := by
  simp [coarseCubeModes, Fintype.card_piFinset]

lemma coarseCubeModes_card_le (k : ℕ) : ((coarseCubeModes k).card : ℝ) ≤ 16*(8:ℝ)^k := by
  rw [coarseCubeModes_card]
  push_cast
  have hq : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  calc
    _ ≤ 2*(2*(2:ℝ)^k)^3 := by gcongr; linarith
    _ = 16*(8:ℝ)^k := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm k 3, pow_mul]
      norm_num
      ring

lemma spinCubeMode_diagonal {b : ℝ} (hb : 0 < b) (k : ℕ)
    (x : Fin 2 × (Fin 3 → ℝ)) :
    (∑ a ∈ coarseCubeModes k, ‖spinCubeMode b a x‖^2) ≤ (128/b^3)*(8:ℝ)^k := by
  calc
    _ ≤ ∑ a ∈ coarseCubeModes k, (8/b^3) := Finset.sum_le_sum
      (fun a _ => spinCubeMode_sq_bound hb a x)
    _ = ((coarseCubeModes k).card : ℝ)*(8/b^3) := by simp
    _ ≤ (16*(8:ℝ)^k)*(8/b^3) := mul_le_mul_of_nonneg_right (coarseCubeModes_card_le k) (by positivity)
    _ = _ := by ring

lemma coarseCubeModes_cutoff (k : ℕ) (a : SpinMode) (ha : a ∉ coarseCubeModes k) :
    (4:ℝ)^k < (latticeRadius a.2)^2 := by
  classical
  rcases a with ⟨a,q⟩
  have hn : ¬ ∀ i, q i < 2^k+1 := by
    intro h
    exact ha (Finset.mem_product.mpr ⟨Finset.mem_univ _,
      Fintype.mem_piFinset.mpr (fun i => Finset.mem_range.mpr (h i))⟩)
  push Not at hn
  obtain ⟨i,hi⟩ := hn
  have hi' : (2:ℝ)^k < (q i : ℝ) := by exact_mod_cast (show 2^k < q i by omega)
  have he : ((2:ℝ)^k)^2 = (4:ℝ)^k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  have ht : ((q i : ℝ))^2 ≤ (latticeRadius q)^2 := by
    simp only [latticeRadius, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    exact Finset.single_le_sum (f := fun j => (q j : ℝ)^2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hz : 0 ≤ (2:ℝ)^k := by positivity
  nlinarith

end Coulomb

end OAI
