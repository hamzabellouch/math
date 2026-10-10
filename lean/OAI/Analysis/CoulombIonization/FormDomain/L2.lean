import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.Basis
import OAI.Analysis.CoulombIonization.FormDomain.WeakDirectionalDerivative

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
namespace CoulombSobolev

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

abbrev L2 (E : Type*) [MeasureSpace E] : Type _ := Lp ℂ 2 (volume : Measure E)

structure Test (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  fn : E → ℝ
  smooth : ContDiff ℝ ∞ fn
  compact : HasCompactSupport fn

namespace Test

def deriv (φ : Test E) (v : E) : Test E where
  fn x := fderiv ℝ φ.fn x v
  smooth := (φ.smooth.fderiv_right (by simp)).clm_apply contDiff_const
  compact := φ.compact.fderiv_apply ℝ v

omit [FiniteDimensional ℝ E] in
lemma memLp (φ : Test E) : MemLp (fun x => (φ.fn x : ℂ)) 2 :=
  (Complex.continuous_ofReal.comp φ.smooth.continuous).memLp_of_hasCompactSupport
    (φ.compact.comp_left (by simp))

def toL2 (φ : Test E) : L2 E := φ.memLp.toLp (fun x => (φ.fn x : ℂ))

omit [FiniteDimensional ℝ E] in
lemma coe_toL2 (φ : Test E) : (φ.toL2 : E → ℂ) =ᵐ[volume] fun x => (φ.fn x : ℂ) :=
  φ.memLp.coeFn_toLp

omit [FiniteDimensional ℝ E] in
lemma inner_toL2 (φ : Test E) (f : L2 E) :
    ⟪φ.toL2, f⟫_ℂ = ∫ x, f x * (φ.fn x : ℂ) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [φ.coe_toL2] with x hx
  rw [hx]
  simp [RCLike.inner_apply]

end Test

lemma test_total (f : L2 E) (hf : ∀ φ : Test E, ⟪φ.toL2, f⟫_ℂ = 0) : f = 0 := by
  apply Lp.ext
  have ht : ∀ (g : E → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • f x = 0 := by
    intro g hg hc
    have hid := hf ⟨g, hg, hc⟩
    rw [Test.inner_toL2] at hid
    simpa only [Complex.real_smul, mul_comm] using hid
  have hh : (f : E → ℂ) =ᵐ[volume] 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((Lp.memLp f).locallyIntegrable (by norm_num)) ht
  exact hh.trans (Lp.coeFn_zero _ _ _).symm

variable {ι : Type*} [Fintype ι]

end

section
open CoulombPauli
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [(volume : Measure V).IsAddHaarMeasure]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasureSpace W] [BorelSpace W]
  [(volume : Measure W).IsAddHaarMeasure]

local instance productVolumeHaar : (volume : Measure (V × W)).IsAddHaarMeasure := by
  change ((volume : Measure V).prod (volume : Measure W)).IsAddHaarMeasure
  infer_instance

namespace Test
omit [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [(volume : Measure V).IsAddHaarMeasure]
  [FiniteDimensional ℝ W] [MeasureSpace W] [BorelSpace W]
  [(volume : Measure W).IsAddHaarMeasure] in
 def tensor (φ : Test V) (η : Test W) : Test (V × W) where
  fn z := φ.fn z.1 * η.fn z.2
  smooth := (φ.smooth.comp contDiff_fst).mul (η.smooth.comp contDiff_snd)
  compact := HasCompactSupport.of_support_subset_isCompact
    (φ.compact.prod η.compact) (by
      intro z hz
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hz
      exact ⟨subset_tsupport φ.fn hz.1, subset_tsupport η.fn hz.2⟩)

lemma tensor_toL2 (φ : Test V) (η : Test W) :
    (φ.tensor η).toL2 = CoulombPauli.tensor φ.toL2 η.toL2 := by
  apply Lp.ext
  filter_upwards [(φ.tensor η).coe_toL2, CoulombPauli.tensor_ae φ.toL2 η.toL2,
    Measure.quasiMeasurePreserving_fst.ae φ.coe_toL2,
    Measure.quasiMeasurePreserving_snd.ae η.coe_toL2] with z h1 h2 h3 h4
  calc
    _ = ((φ.tensor η).fn z : ℂ) := h1
    _ = _ := by rw [h2, h3, h4]; exact Complex.ofReal_mul _ _

omit [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [(volume : Measure V).IsAddHaarMeasure]
  [FiniteDimensional ℝ W] [MeasureSpace W] [BorelSpace W]
  [(volume : Measure W).IsAddHaarMeasure] in
lemma tensor_deriv (φ : Test V) (η : Test W) (v : V) :
    (φ.tensor η).deriv (v,0) = (φ.deriv v).tensor η := by
  have hext {a b : Test (V × W)} (h : a.fn = b.fn) : a = b := by
    cases a; cases b; cases h; rfl
  apply hext
  funext z
  dsimp [tensor,deriv]
  change (fderiv ℝ ((φ.fn ∘ Prod.fst) * (η.fn ∘ Prod.snd)) z) (v,0) = _
  rw [fderiv_mul ((φ.smooth.comp contDiff_fst).differentiable (by simp) z)
      ((η.smooth.comp contDiff_snd).differentiable (by simp) z),
    add_apply]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_comp z (φ.smooth.differentiable (by simp) _) (by fun_prop),
    fderiv_comp z (η.smooth.differentiable (by simp) _) (by fun_prop)]
  simp only [fderiv_fst, fderiv_snd, ContinuousLinearMap.comp_apply]
  change φ.fn z.1 * (fderiv ℝ η.fn z.2) 0 + η.fn z.2 * (fderiv ℝ φ.fn z.1) v = _
  rw [map_zero]
  ring
end Test

def HasWeakPartialDerivative (ψ u : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W)))
    (v : V) : Prop :=
  ∀ Φ : Test (V × W), inner ℂ (Φ.deriv (v,0)).toL2 ψ + inner ℂ Φ.toL2 u = 0

lemma partial_derivative_adjoint_zero {ψ u : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))}
    {v : V} (hw : HasWeakPartialDerivative ψ u v) (φ : Test V) :
    (tensorLeft (φ.deriv v).toL2).adjoint ψ + (tensorLeft φ.toL2).adjoint u = 0 := by
  apply test_total
  intro η
  rw [inner_add_right, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right, tensorLeft_apply, tensorLeft_apply,
    ← Test.tensor_toL2, ← Test.tensor_toL2, ← Test.tensor_deriv]
  exact hw (φ.tensor η)

lemma projected_test_derivative {ψ u : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))}
    {v : V} (hw : HasWeakPartialDerivative ψ u v) (w : Lp ℂ 2 (volume : Measure W))
    (φ : Test V) :
    inner ℂ (φ.deriv v).toL2 ((tensorRight w).adjoint ψ) +
      inner ℂ φ.toL2 ((tensorRight w).adjoint u) = 0 := by
  rw [← tensor_adjoint_exchange, ← tensor_adjoint_exchange, ← inner_add_right,
    partial_derivative_adjoint_zero hw, inner_zero_right]

end

open CoulombPauli
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasureSpace W] [BorelSpace W]
  [(volume : Measure W).IsAddHaarMeasure]
lemma projected_weak_derivative {ψ u : Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W))}
    {v : V} (hw : HasWeakPartialDerivative ψ u v) (w : Lp ℂ 2 (volume : Measure W)) :
    CoulombAtom.HasWeakDirectionalDerivative ((tensorRight w).adjoint ψ)
      ((tensorRight w).adjoint u) v := by
  intro φ hφ hcφ
  let Φ : Test V := ⟨φ,hφ,hcφ⟩
  have h := projected_test_derivative hw w Φ
  rw [Test.inner_toL2, Test.inner_toL2] at h
  apply eq_neg_of_add_eq_zero_left
  convert h using 1
  apply congrArg₂ (· + ·) _ rfl
  apply integral_congr_ae
  filter_upwards [] with x
  congr 2
  exact (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv
end CoulombSobolev

end

end OAI
