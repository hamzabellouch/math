import Mathlib
import OAI.NumberTheory.PrimePackets.LatticeDuality
import OAI.NumberTheory.PrimePackets.MellinGrowth

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
namespace PrimeDegreePackets.AnalyticGrowth

lemma zeroMultiplicity_reflection {f : ℂ → ℂ} (hfe : ∀ z, f (1-z) = f z) (z : ℂ) :
    zeroMultiplicity f (1-z) = zeroMultiplicity f z := by
  have Hg : HasDerivAt (fun z : ℂ => 1-z) (-1) z := by
    apply ((hasDerivAt_id z).const_sub 1).congr_deriv
    simp
  have H := meromorphicOrderAt_comp_of_deriv_ne_zero (f := f)
    (g := fun z : ℂ => 1-z) (x := z) (analyticAt_const.sub analyticAt_id) (by rw [Hg.deriv]; norm_num)
  have HE : f ∘ (fun z : ℂ => 1-z) = f := funext hfe
  rw [HE] at H
  exact congrArg WithTop.untop₀ H.symm

lemma logDeriv_reflection {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfe : ∀ z, f (1-z) = f z) (z : ℂ) : logDeriv f (1-z) = -logDeriv f z := by
  have Hg : HasDerivAt (fun z : ℂ => 1-z) (-1) z := by
    apply ((hasDerivAt_id z).const_sub 1).congr_deriv
    simp
  have H := ((hf (1-z)).hasDerivAt.comp z Hg)
  have HE : (fun z : ℂ => f (1-z)) = f := funext hfe
  simp only [Function.comp_def] at H
  rw [HE] at H
  have HD := H.deriv
  rw [logDeriv_apply, logDeriv_apply, hfe]
  have HD' : deriv f (1-z) = -deriv f z := by linear_combination HD
  rw [HD', neg_div]

 

lemma hasSum_of_nonneg_finite_exhaustion {α ι : Type*} {l : Filter ι} [NeBot l]
    {a : α → ℝ} (ha : ∀ x, 0 ≤ a x) (t : ι → Finset α)
    (ht : ∀ x, a x ≠ 0 → ∀ᶠ i in l, x ∈ t i) {A : ℝ}
    (hA : Tendsto (fun i => ∑ x ∈ t i, a x) l (𝓝 A)) : HasSum a A := by
  classical
  have HB : ∀ s : Finset α, ∑ x ∈ s, a x ≤ A := by
    intro s
    have H : ∀ᶠ i in l, ∀ x ∈ s, a x ≠ 0 → x ∈ t i := by
      rw [Filter.eventually_all_finset]
      intro x hx
      by_cases hx0 : a x = 0
      · exact Filter.Eventually.of_forall (by simp [hx0])
      · exact (ht x hx0).mono (fun i hi _ => hi)
    apply ge_of_tendsto hA
    filter_upwards [H] with i hi
    calc
      _ = ∑ x ∈ s.filter (fun x => a x ≠ 0), a x := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro x hx hn
        by_contra h
        exact hn (Finset.mem_filter.mpr ⟨hx,h⟩)
      _ ≤ ∑ x ∈ t i, a x := Finset.sum_le_sum_of_subset_of_nonneg
        (fun x hx => hi x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2)
        (fun x _ _ => ha x)
  have HS := summable_of_sum_le ha HB
  have HE : ∑' x, a x = A := le_antisymm (HS.tsum_le_of_sum_le HB)
    (le_of_tendsto hA (Filter.Eventually.of_forall (fun i => HS.sum_le_tsum (t i) (fun x _ => ha x))))
  exact HE ▸ HS.hasSum

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

 
def realZeroPole (f : ℂ → ℂ) (σ : ℝ) (ρ : ℂ) : ℝ :=
  (zeroMultiplicity f ρ : ℝ)*(1/((σ:ℂ)-ρ)).re

lemma realZeroPole_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) {σ : ℝ} (hσ : 1 < σ) (ρ : ℂ) :
    0 ≤ realZeroPole f σ ρ := by
  by_cases hm : zeroMultiplicity f ρ = 0
  · simp [realZeroPole, hm]
  have hρ := hstrip ρ ((zeroMultiplicity_ne_zero_iff hf h0 ρ).mp hm)
  unfold realZeroPole
  apply mul_nonneg (by exact_mod_cast zeroMultiplicity_nonneg hf ρ)
  simp only [one_div, Complex.inv_re, Complex.sub_re, Complex.ofReal_re]
  exact div_nonneg (by linarith) (Complex.normSq_nonneg _)

lemma realZeroPole_pair {f : ℂ → ℂ} (hfe : ∀ z, f (1-z) = f z)
    (σ : ℝ) (ρ : ℂ) :
    realZeroPole f σ ρ + realZeroPole f σ (1-ρ) =
      ((zeroMultiplicity f ρ : ℂ)*(1/((σ:ℂ)-ρ)-1/((1-(σ:ℂ))-ρ))).re := by
  have HE : (σ:ℂ)-(1-ρ) = -((1-(σ:ℂ))-ρ) := by ring
  simp only [realZeroPole, zeroMultiplicity_reflection hfe, HE, one_div, inv_neg,
    Complex.neg_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    zero_mul, sub_zero, Complex.sub_re]
  ring

lemma diskPoleSum_sub_re {f : ℂ → ℂ} (hfe : ∀ z, f (1-z) = f z)
    (σ R : ℝ) :
    (diskPoleSum f R σ-diskPoleSum f R (1-(σ:ℂ))).re =
      ∑ ρ ∈ zeroDiskFinset f R, (realZeroPole f σ ρ+realZeroPole f σ (1-ρ)) := by
  classical
  simp only [diskPoleSum, ← Finset.sum_sub_distrib, ← mul_sub,
    realZeroPole_pair hfe]
  exact map_sum Complex.reAddGroupHom _ _

 

theorem hasSum_realZeroPole {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hg : HasSubquadraticGrowth f) (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    HasSum (realZeroPole f σ) (logDeriv f σ).re := by
  classical
  have hσ0 : f (σ:ℂ) ≠ 0 := by
    intro h
    have HH := hstrip σ h
    simp only [Complex.ofReal_re] at HH
    linarith
  have hσ1 : f (1-(σ:ℂ)) ≠ 0 := by rwa [hfe]
  obtain ⟨r,hr,_,hS⟩ := exists_good_radii hf h0
  have HT := (Complex.continuous_re.tendsto _).comp (tendsto_diskPoleSum_sub hf h0 hg hr
    (Filter.Eventually.of_forall hS) hσ0 hσ1)
  have HT' : Tendsto (fun j => ∑ ρ ∈ zeroDiskFinset f (r j),
      (realZeroPole f σ ρ+realZeroPole f σ (1-ρ))) atTop (𝓝 (2*(logDeriv f σ).re)) := by
    simpa only [Function.comp_def, diskPoleSum_sub_re hfe,
      logDeriv_reflection hf hfe, Complex.sub_re, Complex.neg_re, sub_neg_eq_add, two_mul, Complex.add_re] using HT
  have HNN := realZeroPole_nonneg hf h0 hstrip hσ
  have Hsum : HasSum (fun ρ => realZeroPole f σ ρ+realZeroPole f σ (1-ρ))
      (2*(logDeriv f σ).re) := by
    apply hasSum_of_nonneg_finite_exhaustion (fun ρ => add_nonneg (HNN ρ) (HNN (1-ρ)))
      (fun j => zeroDiskFinset f (r j)) _ HT'
    intro ρ hρ
    have Hm : zeroMultiplicity f ρ ≠ 0 := by
      intro H
      apply hρ
      simp [realZeroPole, zeroMultiplicity_reflection hfe, H]
    filter_upwards [hr.eventually_ge_atTop ‖ρ‖] with j hj
    rw [mem_zeroDiskFinset, divisor_closedBall_eq_multiplicity hf hj]
    exact Hm
  have HS : Summable (realZeroPole f σ) := Hsum.summable.of_nonneg_of_le HNN
    (fun ρ => le_add_of_nonneg_right (HNN (1-ρ)))
  let e : ℂ ≃ ℂ := ⟨fun ρ => 1-ρ, fun ρ => 1-ρ, by intro ρ; ring, by intro ρ; ring⟩
  have HS' : Summable (fun ρ => realZeroPole f σ (1-ρ)) := e.summable_iff.mpr HS
  have HE : (∑' ρ, realZeroPole f σ (1-ρ)) = ∑' ρ, realZeroPole f σ ρ :=
    e.tsum_eq (realZeroPole f σ)
  have HH := Hsum.tsum_eq
  rw [HS.tsum_add HS', HE] at HH
  have HA : (∑' ρ, realZeroPole f σ ρ) = (logDeriv f σ).re := by linarith
  exact HA ▸ HS.hasSum

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.HeckeMellin

lemma lintegral_comp_pos_mul {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ≥0∞) :
    (∫⁻ x, f (c*x)) = ENNReal.ofReal c⁻¹ * ∫⁻ x, f x := by
  have H := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Set.univ) (f := fun x : ℝ => c⁻¹*x) (f' := fun _ => c⁻¹)
    MeasurableSet.univ
    (fun x _ => by simpa using (hasDerivAt_id x).const_mul c⁻¹)
    (fun _ _ _ _ h => mul_left_cancel₀ (inv_ne_zero hc.ne') h)
    (fun x => f (c*x))
  have hi : (fun x : ℝ => c⁻¹*x) '' Set.univ = Set.univ := by
    ext y
    simp only [mem_image, mem_univ, true_and, iff_true]
    exact ⟨c*y, by simp [hc.ne']⟩
  simpa only [hi, Measure.restrict_univ, abs_of_pos (inv_pos.mpr hc),
    ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] using H

lemma lintegral_snoc (d : ℕ) (f : (Fin (d+1) → ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ u : Fin d → ℝ, ∫⁻ v : ℝ, f (Fin.snoc u v)) = ∫⁻ x, f x := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) (Fin.last d)
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) (Fin.last d)).symm
  have H := he.lintegral_comp (f := f) hf
  change (∫⁻ p : ℝ × (Fin d → ℝ), f (e.symm p)) = _ at H
  have hs (p : ℝ × (Fin d → ℝ)) : e.symm p = Fin.snoc p.2 p.1 := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
  simp_rw [hs] at H
  rw [Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)] at H
  rw [lintegral_lintegral_swap (by fun_prop)] at H
  exact H

 
def coordinates (d : ℕ) (u : Fin d → ℝ) (v : ℝ) : Fin (d+1) → ℝ :=
  Fin.snoc (fun i => u i + v/2) (-∑ i, u i + v/2)

lemma continuous_coordinates (d : ℕ) :
    Continuous (fun p : (Fin d → ℝ) × ℝ => coordinates d p.1 p.2) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [coordinates, Fin.snoc_last, Fin.snoc_castSucc] <;> fun_prop

 
theorem lintegral_coordinates (d : ℕ) (f : (Fin (d+1) → ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ v : ℝ, ∫⁻ u : Fin d → ℝ, f (coordinates d u v)) =
      ENNReal.ofReal (2/(d+1 : ℝ)) * ∫⁻ x, f x := by
  let c : ℝ := (d+1 : ℝ)/2
  have hc : 0 < c := by dsimp [c]; positivity
  have he (u : Fin d → ℝ) (v : ℝ) :
      coordinates d u v =
        Fin.snoc (u + (fun _ : Fin d => v/2)) (c*v - ∑ i, (u + (fun _ : Fin d => v/2)) i) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [coordinates, Finset.sum_add_distrib, c]
      ring
    · simp [coordinates]
  calc
    _ = ∫⁻ v : ℝ, ∫⁻ u : Fin d → ℝ, f (Fin.snoc u (c*v - ∑ i, u i)) := by
      apply lintegral_congr
      intro v
      simp_rw [he]
      exact lintegral_add_right_eq_self (fun u : Fin d → ℝ =>
        f (Fin.snoc u (c*v - ∑ i, u i))) (fun _ => v/2)
    _ = ∫⁻ u : Fin d → ℝ, ∫⁻ v : ℝ, f (Fin.snoc u (c*v - ∑ i, u i)) := by
      apply lintegral_lintegral_swap
      apply Measurable.aemeasurable
      apply hf.comp
      apply measurable_pi_iff.mpr
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i <;>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] <;> fun_prop
    _ = ∫⁻ u : Fin d → ℝ, ENNReal.ofReal c⁻¹ * ∫⁻ w : ℝ, f (Fin.snoc u w) := by
      apply lintegral_congr
      intro u
      rw [lintegral_comp_pos_mul hc (fun v => f (Fin.snoc u (v - ∑ i, u i)))]
      congr 1
      exact lintegral_sub_right_eq_self (fun w => f (Fin.snoc u w)) (∑ i, u i)
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ x, f x := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_snoc d f hf]
    _ = _ := by congr 2; dsimp [c]; field_simp

 

theorem map_coordinates (d : ℕ) :
    Measure.map (fun p : ℝ × (Fin d → ℝ) => coordinates d p.2 p.1) volume =
      ENNReal.ofReal (2/(d+1 : ℝ)) • (volume : Measure (Fin (d+1) → ℝ)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hc : Continuous (fun p : ℝ × (Fin d → ℝ) => coordinates d p.2 p.1) :=
    (continuous_coordinates d).comp continuous_swap
  have hfc : Measurable (fun p : ℝ × (Fin d → ℝ) => f (coordinates d p.2 p.1)) :=
    hf.comp hc.measurable
  rw [lintegral_map hf hc.measurable, lintegral_smul_measure,
    Measure.volume_eq_prod, lintegral_prod _ hfc.aemeasurable]
  exact lintegral_coordinates d f hf

lemma integral_coordinates {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d : ℕ) (f : (Fin (d+1) → ℝ) → F) (hf : StronglyMeasurable f) :
    (∫ p : ℝ × (Fin d → ℝ), f (coordinates d p.2 p.1)) =
      (2/(d+1 : ℝ)) • ∫ x, f x := by
  have hc : Continuous (fun p : ℝ × (Fin d → ℝ) => coordinates d p.2 p.1) :=
    (continuous_coordinates d).comp continuous_swap
  rw [← integral_map hc.measurable.aemeasurable hf.aestronglyMeasurable,
    map_coordinates, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]

lemma integrable_coordinates {F : Type*} [NormedAddCommGroup F]
    (d : ℕ) (f : (Fin (d+1) → ℝ) → F) (hf : StronglyMeasurable f)
    (hI : Integrable f) :
    Integrable (fun p : ℝ × (Fin d → ℝ) => f (coordinates d p.2 p.1)) := by
  have hc : Continuous (fun p : ℝ × (Fin d → ℝ) => coordinates d p.2 p.1) :=
    (continuous_coordinates d).comp continuous_swap
  apply (integrable_map_measure hf.aestronglyMeasurable hc.measurable.aemeasurable).mp
  rw [map_coordinates]
  exact hI.smul_measure ENNReal.ofReal_ne_top

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin

 
def logGammaKernel (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (s * (x : ℂ) - (Real.exp x : ℂ))

lemma logGammaKernel_eq (s : ℂ) (x : ℝ) :
    logGammaKernel s x = Real.exp x •
      ((Real.exp (-Real.exp x) : ℂ) * (Real.exp x : ℂ) ^ (s-1)) := by
  rw [Complex.real_smul, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [logGammaKernel, Complex.ofReal_exp, Complex.ofReal_neg]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

lemma integrable_logGammaKernel {s : ℂ} (hs : 0 < s.re) :
    Integrable (logGammaKernel s) := by
  have H := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ (s-1))
  simp only [Set.image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _),
    ← logGammaKernel_eq, integrableOn_univ] at H
  exact H.mp (Complex.GammaIntegral_convergent hs)

lemma integral_logGammaKernel {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℝ, logGammaKernel s x) = Complex.Gamma s := by
  have H := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ (s-1))
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  simpa only [Set.image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _),
    ← logGammaKernel_eq, Measure.restrict_univ] using H.symm

 
def gaussianLogKernel (s : ℂ) (r x : ℝ) : ℂ :=
  Complex.exp (s * (x : ℂ) - (r * Real.exp (2*x) : ℝ))

lemma gaussianLogKernel_eq {r : ℝ} (hr : 0 < r) (s : ℂ) (x : ℝ) :
    gaussianLogKernel s r x = (r : ℂ) ^ (-(s/2)) *
      logGammaKernel (s/2) (2*x + Real.log r) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    ← Complex.ofReal_log hr.le, logGammaKernel, ← Complex.exp_add,
    Real.exp_add, Real.exp_log hr]
  simp only [gaussianLogKernel, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  congr 1
  ring

lemma integrable_gaussianLogKernel {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    Integrable (gaussianLogKernel s r) := by
  have ha : 0 < (s/2).re := by simpa using half_pos hs
  have H := ((integrable_logGammaKernel ha).comp_add_right (Real.log r)).comp_mul_left'
    (R := (2 : ℝ)) (by norm_num)
  simpa only [← gaussianLogKernel_eq hr] using H.const_mul ((r : ℂ)^(-(s/2)))

lemma integral_gaussianLogKernel {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ, gaussianLogKernel s r x) =
      (1/2 : ℂ) * (r : ℂ) ^ (-(s/2)) * Complex.Gamma (s/2) := by
  have ha : 0 < (s/2).re := by simpa using half_pos hs
  simp_rw [gaussianLogKernel_eq hr]
  rw [integral_const_mul, Measure.integral_comp_mul_left
      (fun x => logGammaKernel (s/2) (x + Real.log r)) 2,
    integral_add_right_eq_self, integral_logGammaKernel ha]
  norm_num [Complex.real_smul]
  ring

lemma continuous_gaussianLogKernel (s : ℂ) (r : ℝ) :
    Continuous (gaussianLogKernel s r) := by
  unfold gaussianLogKernel
  fun_prop

 
lemma integral_gaussianLogKernel_product (n : ℕ) {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) :
    (∫ x : Fin n → ℝ, ∏ i, gaussianLogKernel s r (x i)) =
      ((1/2 : ℂ) * (r : ℂ)^(-(s/2)) * Complex.Gamma (s/2)) ^ n := by
  rw [integral_fintype_prod_volume_eq_pow, Fintype.card_fin, integral_gaussianLogKernel hs hr]

lemma integrable_gaussianLogKernel_product (n : ℕ) {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : Fin n → ℝ => ∏ i, gaussianLogKernel s r (x i)) :=
  Integrable.fintype_prod (fun _ => integrable_gaussianLogKernel hs hr)

lemma exp_two_mul (x : ℝ) : Real.exp (2*x) = (Real.exp x)^2 := by
  rw [show 2*x = x+x by ring, Real.exp_add, pow_two]

lemma scaled_cpow {r a : ℝ} (hr : 0 < r) (ha : a ≠ 0) (s : ℂ) :
    ((r*a^2 : ℝ) : ℂ)^(-(s/2)) = (r : ℂ)^(-(s/2)) * ((|a| : ℝ) : ℂ)^(-s) := by
  have hsq : 0 < a^2 := sq_pos_of_ne_zero ha
  have hab : 0 < |a| := abs_pos.mpr ha
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos hr hsq).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hab.ne'),
    ← Complex.exp_add, ← Complex.ofReal_log (mul_pos hr hsq).le,
    ← Complex.ofReal_log hr.le, ← Complex.ofReal_log hab.le,
    Real.log_mul hr.ne' (pow_ne_zero _ ha), Real.log_pow, Real.log_abs]
  push_cast
  congr 1
  ring

lemma gaussianLogKernel_scale (s : ℂ) (r a x : ℝ) :
    gaussianLogKernel s (r*a^2) x =
      Complex.exp (s*(x : ℂ) - (r*(a*Real.exp x)^2 : ℝ)) := by
  rw [gaussianLogKernel, exp_two_mul]
  congr 2
  push_cast
  ring

lemma integral_scaled_gaussianLogKernel {s : ℂ} (hs : 0 < s.re)
    {r a : ℝ} (hr : 0 < r) (ha : a ≠ 0) :
    (∫ x : ℝ, Complex.exp (s*(x : ℂ) - (r*(a*Real.exp x)^2 : ℝ))) =
      ((1/2 : ℂ) * (r : ℂ)^(-(s/2)) * Complex.Gamma (s/2)) * ((|a| : ℝ) : ℂ)^(-s) := by
  simp_rw [← gaussianLogKernel_scale]
  rw [integral_gaussianLogKernel hs (mul_pos hr (sq_pos_of_ne_zero ha))]
  rw [scaled_cpow hr ha]
  ring

lemma prod_abs_cpow {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) (s : ℂ) :
    (∏ i, ((|a i| : ℝ) : ℂ)^s) = ((∏ i, |a i| : ℝ) : ℂ)^s := by
  have hp : 0 < ∏ i, |a i| := Finset.prod_pos (fun i _ => abs_pos.mpr (ha i))
  have H (i : ι) : ((|a i| : ℝ) : ℂ)^s = Complex.exp ((Real.log |a i| : ℂ)*s) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (ha i))),
      ← Complex.ofReal_log (abs_nonneg _)]
  simp_rw [H]
  rw [← Complex.exp_sum,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le, Real.log_prod (fun i _ => abs_ne_zero.mpr (ha i)),
    Complex.ofReal_sum, Finset.sum_mul]

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin

lemma coordinates_eq (d : ℕ) (u : LogCoordinates d) (v : ℝ) (i : Fin (d+1)) :
    coordinates d u v i = restoredLogCoordinates u i + v/2 := by
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [coordinates, restoredLogCoordinates]

lemma sum_coordinates (d : ℕ) (u : LogCoordinates d) (v : ℝ) :
    ∑ i, coordinates d u v i = (d+1 : ℝ)*v/2 := by
  simp_rw [coordinates_eq]
  rw [Finset.sum_add_distrib, restoredLogCoordinates_sum]
  simp
  ring

 
def logEnergy {d : ℕ} (a : Fin (d+1) → ℝ) (u : LogCoordinates d) : ℝ :=
  ∑ i, (a i * Real.exp (restoredLogCoordinates u i))^2

lemma continuous_logEnergy {d : ℕ} (a : Fin (d+1) → ℝ) :
    Continuous (logEnergy a) := by
  unfold logEnergy
  exact continuous_finsetSum _ (fun i _ =>
    (continuous_const.mul (Real.continuous_exp.comp (restoredLogCoordinates_continuous i))).pow 2)

lemma logEnergy_pos {d : ℕ} (a : Fin (d+1) → ℝ) (ha : ∀ i, a i ≠ 0)
    (u : LogCoordinates d) : 0 < logEnergy a u := by
  unfold logEnergy
  apply Finset.sum_pos
  · intro i _
    exact sq_pos_of_ne_zero (mul_ne_zero (ha i) (Real.exp_ne_zero _))
  · exact Finset.univ_nonempty

 
def logRadialKernel {d : ℕ} (s : ℂ) (r : ℝ) (a : Fin (d+1) → ℝ)
    (p : ℝ × LogCoordinates d) : ℂ :=
  Complex.exp (((d+1 : ℕ) : ℂ)*s/2*(p.1 : ℂ) - (r*Real.exp p.1*logEnergy a p.2 : ℝ))

lemma gaussianLogKernel_coordinates {d : ℕ} (s : ℂ) (r : ℝ)
    (a : Fin (d+1) → ℝ) (p : ℝ × LogCoordinates d) :
    (∏ i, gaussianLogKernel s (r*(a i)^2) (coordinates d p.2 p.1 i)) =
      logRadialKernel s r a p := by
  simp_rw [gaussianLogKernel_scale]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum,
    sum_coordinates, ← Complex.ofReal_sum]
  have HE : ∑ i, r*(a i*Real.exp (coordinates d p.2 p.1 i))^2 =
      r*Real.exp p.1*logEnergy a p.2 := by
    have H (i : Fin (d+1)) : r*(a i*Real.exp (coordinates d p.2 p.1 i))^2 =
        (r*Real.exp p.1)*(a i*Real.exp (restoredLogCoordinates p.2 i))^2 := by
      rw [coordinates_eq, Real.exp_add, mul_pow, mul_pow, ← exp_two_mul (p.1/2),
        show 2*(p.1/2) = p.1 by ring, mul_pow]
      ring
    simp_rw [H]
    rw [← Finset.mul_sum]
    rfl
  rw [HE]
  push_cast
  congr 1
  ring

lemma integrable_logRadialKernel {d : ℕ} {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) (a : Fin (d+1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    Integrable (logRadialKernel s r a) := by
  have hprod : Integrable (fun x : Fin (d+1) → ℝ => ∏ i, gaussianLogKernel s (r*(a i)^2) (x i)) :=
    Integrable.fintype_prod (fun i => integrable_gaussianLogKernel hs
      (mul_pos hr (sq_pos_of_ne_zero (ha i))))
  have hcont : Continuous (fun x : Fin (d+1) → ℝ => ∏ i, gaussianLogKernel s (r*(a i)^2) (x i)) := by
    apply continuous_finsetProd
    intro i _
    exact (continuous_gaussianLogKernel s _).comp (continuous_apply i)
  have H := integrable_coordinates d _ hcont.stronglyMeasurable hprod
  simpa only [gaussianLogKernel_coordinates] using H

 
theorem integral_logRadialKernel {d : ℕ} {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) (a : Fin (d+1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    (∫ p, logRadialKernel s r a p) =
      (2/(d+1 : ℂ)) *
        ((1/2 : ℂ)*(r : ℂ)^(-(s/2))*Complex.Gamma (s/2))^(d+1) *
        ((∏ i, |a i| : ℝ) : ℂ)^(-s) := by
  have hcont : Continuous (fun x : Fin (d+1) → ℝ => ∏ i, gaussianLogKernel s (r*(a i)^2) (x i)) := by
    apply continuous_finsetProd
    intro i _
    exact (continuous_gaussianLogKernel s _).comp (continuous_apply i)
  have H := integral_coordinates d _ hcont.stronglyMeasurable
  simp only [gaussianLogKernel_coordinates] at H
  rw [H, integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_gaussianLogKernel hs (mul_pos hr (sq_pos_of_ne_zero (ha _))),
    scaled_cpow hr (ha _)]
  simp_rw [show ∀ i, (1/2 : ℂ)*((r : ℂ)^(-(s/2)) * ((|a i| : ℝ) : ℂ)^(-s)) *
      Complex.Gamma (s/2) =
        ((1/2 : ℂ)*(r : ℂ)^(-(s/2))*Complex.Gamma (s/2)) * ((|a i| : ℝ) : ℂ)^(-s)
      from fun i => by ring]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin, prod_abs_cpow a ha,
    Complex.real_smul]
  push_cast
  ring

 
def radialKernel {d : ℕ} (s : ℂ) (r : ℝ) (a : Fin (d+1) → ℝ)
    (t : ℝ) (u : LogCoordinates d) : ℂ :=
  (t : ℂ)^(((d+1 : ℕ) : ℂ)*s/2-1) *
    Complex.exp (-(r*t*logEnergy a u : ℝ))

lemma logRadialKernel_eq_radial {d : ℕ} (s : ℂ) (r : ℝ)
    (a : Fin (d+1) → ℝ) (v : ℝ) (u : LogCoordinates d) :
    logRadialKernel s r a (v,u) = Real.exp v • radialKernel s r a (Real.exp v) u := by
  rw [radialKernel, Complex.real_smul,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero v)),
    ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp, Complex.ofReal_exp,
    ← Complex.exp_add, ← Complex.exp_add]
  unfold logRadialKernel
  congr 1
  push_cast
  ring

lemma radialIntegral_log {d : ℕ} (s : ℂ) (r : ℝ)
    (a : Fin (d+1) → ℝ) (v : ℝ) :
    (∫ u, logRadialKernel s r a (v,u)) =
      Real.exp v • ∫ u, radialKernel s r a (Real.exp v) u := by
  simp_rw [logRadialKernel_eq_radial]
  exact integral_smul _ _

lemma integrable_radialIntegral {d : ℕ} {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) (a : Fin (d+1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    IntegrableOn (fun t => ∫ u, radialKernel s r a t u) (Ioi 0) := by
  have H := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun t => ∫ u, radialKernel s r a t u)
  simp only [Set.image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _),
    ← radialIntegral_log, integrableOn_univ] at H
  apply H.mpr
  have HI := integrable_logRadialKernel hs hr a ha
  rw [Measure.volume_eq_prod] at HI
  exact HI.integral_prod_left

 

theorem integral_radialKernel {d : ℕ} {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) (a : Fin (d+1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    (∫ t in Ioi 0, ∫ u, radialKernel s r a t u) =
      (2/(d+1 : ℂ)) *
        ((1/2 : ℂ)*(r : ℂ)^(-(s/2))*Complex.Gamma (s/2))^(d+1) *
        ((∏ i, |a i| : ℝ) : ℂ)^(-s) := by
  have H := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun t => ∫ u, radialKernel s r a t u)
  simp only [Set.image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _),
    ← radialIntegral_log, Measure.restrict_univ] at H
  rw [H]
  have HI := integrable_logRadialKernel hs hr a ha
  rw [Measure.volume_eq_prod] at HI
  rw [← integral_prod _ HI, ← Measure.volume_eq_prod]
  exact integral_logRadialKernel hs hr a ha

end PrimeDegreePackets.HeckeMellin
end
end

end OAI
