import Mathlib
import OAI.Analysis.CoulombIonization.Localization.Trace
import OAI.Analysis.CoulombIonization.RadialBounds.WeakWindowMoment
import OAI.Analysis.CoulombIonization.FormDomain.WeakL2PartialDerivative

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace CoulombPackets

section
open CoulombPauli CoulombSobolev
open scoped FourierTransform LineDeriv
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma packet_fourier (g : 𝓢(V, ℝ)) (p : V × V) (f : Lp ℂ 2 (volume : Measure V)) :
    inner ℂ (packet g p) f = 𝓕 (fun x => f x * (g (x-p.1) : ℂ)) p.2 := by
  rw [L2.inner_def, Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [(packetFunction_memLp g p).coeFn_toLp] with x hx
  change inner ℂ ((packetFunction_memLp g p).toLp _ x) _ = _
  rw [hx, RCLike.inner_apply, packetFunction]
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, Circle.smul_def, smul_eq_mul]
  ring

lemma packet_kinetic {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (f : Lp ℂ 2 (volume : Measure V)) (u : ι → Lp ℂ 2 (volume : Measure V))
    (hw : ∀ i, CoulombAtom.HasWeakDirectionalDerivative f (u i) (b i))
    (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1) :
    Integrable (fun p : V × V => (2*Real.pi)^2 * ‖p.2‖^2 *
      ‖inner ℂ (packet g p) f‖^2) ((volume : Measure V).prod volume) ∧
    (∫ p : V × V, (2*Real.pi)^2 * ‖p.2‖^2 * ‖inner ℂ (packet g p) f‖^2
      ∂((volume : Measure V).prod volume)) =
      (∑ i, ‖u i‖^2) + (∑ i, ∫ x : V, (∂_{b i} g x)^2) * ‖f‖^2 := by
  simp_rw [packet_fourier]
  simpa only [hg, one_mul, ← CoulombPauli.l2_norm_sq] using
    CoulombAtom.weak_window_kinetic b (Lp.memLp f) (fun i => Lp.memLp (u i)) hw g

variable {B : Type*} [MeasurableSpace B] {ν : Measure B} [SigmaFinite ν]
  [SeparableSpace (Lp ℂ 2 ν)]

omit [SeparableSpace (Lp ℂ 2 ν)] in
lemma tensorRight_hasSum {ι κ : Type*}
    (a : HilbertBasis ι ℂ (Lp ℂ 2 (volume : Measure V)))
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν))
    (ψ : Lp ℂ 2 ((volume : Measure V).prod ν)) :
    HasSum (fun j => ‖(tensorRight (b j)).adjoint ψ‖^2) (‖ψ‖^2) := by
  have he := tensorRight_parseval a b ψ
  have ht : (∑' j, ENNReal.ofReal (‖(tensorRight (b j)).adjoint ψ‖^2)) ≠ ⊤ := by
    rw [he]
    exact ENNReal.ofReal_ne_top
  have hh := ENNReal.hasSum_toReal ht
  rw [← ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top), he] at hh
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hh

lemma partialOccupation_kinetic_lintegral {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V)
    (ψ : Lp ℂ 2 ((volume : Measure V).prod ν))
    (u : ι → Lp ℂ 2 ((volume : Measure V).prod ν))
    (hw : ∀ i, HasWeakL2PartialDerivative ψ (u i) (b i))
    (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1) :
    (∫⁻ p : V × V, ENNReal.ofReal ((2*Real.pi)^2 * ‖p.2‖^2 * partialOccupation g ψ p)
      ∂((volume : Measure V).prod volume)) =
    ENNReal.ofReal ((∑ i, ‖u i‖^2) + (∑ i, ∫ x : V, (∂_{b i} g x)^2) * ‖ψ‖^2) := by
  classical
  obtain ⟨κ,a,-⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 ν)
  obtain ⟨η,c,-⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 (volume : Measure V))
  let : Countable κ := hilbertBasis_countable a
  let f (j : κ) := (tensorRight (a j)).adjoint ψ
  let v (i : ι) (j : κ) := (tensorRight (a j)).adjoint (u i)
  let C : ℝ := ∑ i, ∫ x : V, (∂_{b i} g x)^2
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => integral_nonneg fun _ => sq_nonneg _)
  have hscalar (j : κ) := packet_kinetic b (f j) (fun i => v i j)
    (fun i => projected_weak_derivative_general (hw i) (a j)) g hg
  have hs (p : V × V) : (2*Real.pi)^2 * ‖p.2‖^2 * partialOccupation g ψ p =
      ∑' j : κ, (2*Real.pi)^2 * ‖p.2‖^2 * ‖inner ℂ (packet g p) (f j)‖^2 := by
    have h := (basis_parseval a ((tensorLeft (ν := ν) (packet g p)).adjoint ψ)).mul_left
      ((2*Real.pi)^2 * ‖p.2‖^2)
    simp_rw [tensor_adjoint_exchange] at h
    exact h.tsum_eq.symm
  have hsum (p : V × V) : Summable (fun j : κ =>
      (2*Real.pi)^2 * ‖p.2‖^2 * ‖inner ℂ (packet g p) (f j)‖^2) := by
    have h := (basis_parseval a ((tensorLeft (ν := ν) (packet g p)).adjoint ψ)).summable.mul_left
      ((2*Real.pi)^2 * ‖p.2‖^2)
    simpa only [tensor_adjoint_exchange] using h
  have hj (j : κ) : (∫⁻ p : V × V, ENNReal.ofReal
      ((2*Real.pi)^2 * ‖p.2‖^2 * ‖inner ℂ (packet g p) (f j)‖^2)
      ∂((volume : Measure V).prod volume)) =
      ENNReal.ofReal ((∑ i, ‖v i j‖^2) + C * ‖f j‖^2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hscalar j).1
      (Filter.Eventually.of_forall fun _ => by positivity), (hscalar j).2]
  have hf := tensorRight_hasSum c a ψ
  have hv (i : ι) := tensorRight_hasSum c a (u i)
  have hall : HasSum (fun j : κ => (∑ i, ‖v i j‖^2) + C * ‖f j‖^2)
      ((∑ i, ‖u i‖^2) + C * ‖ψ‖^2) :=
    (hasSum_sum (fun i _ => hv i)).add (hf.mul_left C)
  calc
    _ = ∫⁻ p : V × V, ∑' j : κ, ENNReal.ofReal
        ((2*Real.pi)^2 * ‖p.2‖^2 * ‖inner ℂ (packet g p) (f j)‖^2)
        ∂((volume : Measure V).prod volume) := by
      apply lintegral_congr
      intro p
      rw [hs, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (hsum p)]
    _ = ∑' j : κ, ∫⁻ p : V × V, ENNReal.ofReal
        ((2*Real.pi)^2 * ‖p.2‖^2 * ‖inner ℂ (packet g p) (f j)‖^2)
        ∂((volume : Measure V).prod volume) :=
      lintegral_tsum (fun j => (hscalar j).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    _ = ∑' j : κ, ENNReal.ofReal ((∑ i, ‖v i j‖^2) + C * ‖f j‖^2) := by simp_rw [hj]
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hall.summable, hall.tsum_eq]

end

open CoulombPauli CoulombSobolev
open scoped LineDeriv
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {B : Type*} [MeasurableSpace B] {ν : Measure B} [SigmaFinite ν]
  [SeparableSpace (Lp ℂ 2 ν)]

lemma partialOccupation_kinetic {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V)
    (ψ : Lp ℂ 2 ((volume : Measure V).prod ν))
    (u : ι → Lp ℂ 2 ((volume : Measure V).prod ν))
    (hw : ∀ i, HasWeakL2PartialDerivative ψ (u i) (b i))
    (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1) :
    Integrable (fun p : V × V => (2*Real.pi)^2 * ‖p.2‖^2 * partialOccupation g ψ p)
      ((volume : Measure V).prod volume) ∧
    (∫ p : V × V, (2*Real.pi)^2 * ‖p.2‖^2 * partialOccupation g ψ p
      ∂((volume : Measure V).prod volume)) =
    (∑ i, ‖u i‖^2) + (∑ i, ∫ x : V, (∂_{b i} g x)^2) * ‖ψ‖^2 := by
  have hp (p : V × V) : 0 ≤ (2*Real.pi)^2 * ‖p.2‖^2 * partialOccupation g ψ p := by
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hm : AEStronglyMeasurable
      (fun p : V × V => (2*Real.pi)^2 * ‖p.2‖^2 * partialOccupation g ψ p)
      ((volume : Measure V).prod volume) :=
    (by fun_prop : Continuous (fun p : V × V => (2*Real.pi)^2 * ‖p.2‖^2)).aestronglyMeasurable.mul
      (partialOccupation_integrable g hg ψ).aestronglyMeasurable
  have he := partialOccupation_kinetic_lintegral b ψ u hw g hg
  have hi : Integrable (fun p : V × V => (2*Real.pi)^2 * ‖p.2‖^2 * partialOccupation g ψ p)
      ((volume : Measure V).prod volume) := by
    refine ⟨hm, ?_⟩
    rw [HasFiniteIntegral]
    simp only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hp _)]
    rw [he]
    exact ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hp)] at he
  apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hp) (by positivity)).1 he
end CoulombPackets

namespace CoulombPauli
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]
lemma tensorRight_hasSum_general {ι κ : Type*}
    (a : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν)) (ψ : Lp ℂ 2 (μ.prod ν)) :
    HasSum (fun j => ‖(tensorRight (b j)).adjoint ψ‖^2) (‖ψ‖^2) := by
  have he := tensorRight_parseval a b ψ
  have ht : (∑' j, ENNReal.ofReal (‖(tensorRight (b j)).adjoint ψ‖^2)) ≠ ⊤ := by
    rw [he]; exact ENNReal.ofReal_ne_top
  have hh := ENNReal.hasSum_toReal ht
  rw [← ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top), he] at hh
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hh
end CoulombPauli

namespace CoulombPackets
open CoulombPauli CoulombSobolev
open scoped LineDeriv
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {B : Type*} [MeasurableSpace B] {ν : Measure B} [SigmaFinite ν]

def spinMarginal (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν))
    (s : Fin 2) (w : Lp ℂ 2 ν) : Lp ℂ 2 (volume : Measure V) :=
  (tensorRight (spinVector s)).adjoint ((tensorRight w).adjoint ψ)

def HasWeakSpinPartialDerivative
    (ψ u : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν)) (v : V) : Prop :=
  ∀ (φ : CoulombSobolev.Test V) (s : Fin 2),
    (tensorLeft (tensor (φ.deriv v).toL2 (spinVector s))).adjoint ψ +
      (tensorLeft (tensor φ.toL2 (spinVector s))).adjoint u = 0

lemma spinMarginal_weak_derivative
    {ψ u : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν)} {v : V}
    (hw : HasWeakSpinPartialDerivative ψ u v) (s : Fin 2) (w : Lp ℂ 2 ν) :
    CoulombAtom.HasWeakDirectionalDerivative (spinMarginal ψ s w) (spinMarginal u s w) v := by
  intro φ hφ hcφ
  let Φ : CoulombSobolev.Test V := ⟨φ,hφ,hcφ⟩
  have h : inner ℂ (Φ.deriv v).toL2 (spinMarginal ψ s w) +
      inner ℂ Φ.toL2 (spinMarginal u s w) = 0 := by
    simp only [spinMarginal, ContinuousLinearMap.adjoint_inner_right, tensorRight_apply]
    have hh := congrArg (fun z => inner ℂ w z) (hw Φ s)
    simpa only [inner_add_right, ContinuousLinearMap.adjoint_inner_right, tensorLeft_apply,
      inner_zero_right] using hh
  rw [CoulombSobolev.Test.inner_toL2, CoulombSobolev.Test.inner_toL2] at h
  apply eq_neg_of_add_eq_zero_left
  convert h using 1
  apply congrArg₂ (· + ·) _ rfl
  apply integral_congr_ae
  filter_upwards [] with x
  congr 2
  exact (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv

lemma spinMarginal_sum_norm (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν))
    (w : Lp ℂ 2 ν) :
    (∑ s : Fin 2, ‖spinMarginal ψ s w‖^2) = ‖(tensorRight w).adjoint ψ‖^2 := by
  obtain ⟨κ,a,-⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 (volume : Measure V))
  have h := tensorRight_hasSum_general a spinBasis ((tensorRight w).adjoint ψ)
  simpa only [tsum_fintype, spinBasis_apply, spinMarginal] using h.tsum_eq

end CoulombPackets

end

end OAI
