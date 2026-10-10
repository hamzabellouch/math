import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.BlockIndex
import OAI.Analysis.CoulombRadii.FieldAnalysis.Rotation

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal

open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb
instance : IsProbabilityMeasure rotationMeasure := ⟨Measure.haarMeasure_self⟩

instance : Measure.IsMulLeftInvariant rotationMeasure := by
  unfold rotationMeasure
  infer_instance

instance : Measure.IsHaarMeasure rotationMeasure := by
  unfold rotationMeasure
  infer_instance

instance : Measure.IsMulRightInvariant rotationMeasure where
  map_mul_right_eq_self P := by
    have H := Measure.isMulInvariant_eq_smul_of_compactSpace
      (Measure.map (· * P) rotationMeasure) rotationMeasure
    have H1 := congrArg (fun μ : Measure Rotation => μ univ) H
    simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at H1
    have H2 : (Measure.map (· * P) rotationMeasure).haarScalarFactor rotationMeasure = 1 :=
      ENNReal.coe_injective (by simpa using H1.symm)
    rw [H2, one_smul] at H
    exact H

lemma ae_all_zero_of_continuous {X T : Type*} [MeasurableSpace X]
    {μ : Measure X} [TopologicalSpace T] [TopologicalSpace.SeparableSpace T]
    (A : X → T → ℂ) (hc : ∀ x, Continuous (A x))
    (hz : ∀ t, ∀ᵐ x ∂μ, A x t = 0) : ∀ᵐ x ∂μ, ∀ t, A x t = 0 := by
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense T
  have hDz : ∀ᵐ x ∂μ, ∀ t ∈ D, A x t = 0 := (ae_ball_iff hD).mpr (fun t _ => hz t)
  filter_upwards [hDz] with x hx
  have he : A x = fun _ => 0 := Continuous.ext_on hdense (hc x) continuous_const hx
  intro t
  exact congrFun he t

section SmoothSlices
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F]
  [IsLocallyFiniteMeasure (volume : Measure F)] [SigmaFinite (volume : Measure F)]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [IsLocallyFiniteMeasure (volume : Measure F)] [SigmaFinite (volume : Measure F)] in
lemma compact_tensor_test {χ : E → ℝ} {φ : F → ℝ}
    (hχ : HasCompactSupport χ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun z : E × F => χ z.1 * φ z.2) := by
  apply HasCompactSupport.of_support_subset_isCompact (hχ.prod hφ)
  intro z hz
  simp only [Function.mem_support, mul_ne_zero_iff] at hz
  exact ⟨subset_tsupport _ hz.1, subset_tsupport _ hz.2⟩

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)]
  [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [IsLocallyFiniteMeasure (volume : Measure F)] [SigmaFinite (volume : Measure F)] in
lemma tensor_test_deriv {χ : E → ℝ} {φ : F → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (v : F) (z : E × F) :
    fderiv ℝ (fun z : E × F => χ z.1 * φ z.2) z (0, v) =
      χ z.1 * fderiv ℝ φ z.2 v := by
  have h1 := (hχ.differentiable (by simp) z.1).hasFDerivAt.comp z (hasFDerivAt_fst (𝕜 := ℝ))
  have h2 := (hφ.differentiable (by simp) z.2).hasFDerivAt.comp z (hasFDerivAt_snd (𝕜 := ℝ))
  change (fderiv ℝ ((χ ∘ Prod.fst) * (φ ∘ Prod.snd)) z) (0,v) = _
  rw [(h1.mul h2).fderiv]
  simp

omit [SigmaFinite (volume : Measure E)] in
lemma test_complex_memLp {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) :
    MemLp (fun x => (φ x : ℂ)) 2 volume :=
  (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
    (hφC.comp_left (by simp))

omit [SigmaFinite (volume : Measure E)] in
lemma test_direction_complex_memLp {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) (v : E) :
    MemLp (fun x => (fderiv ℝ φ x v : ℂ)) 2 volume :=
  (Complex.continuous_ofReal.comp
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
      ((hφC.fderiv_apply ℝ v).comp_left (by simp))

lemma weak_slice_fixed_test {u g : E × F → ℂ}
    (hu : MemLp u 2 (volume.prod volume)) (hg : MemLp g 2 (volume.prod volume))
    (v : F)
    (hw : ∀ (η : E × F → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ z, u z * (fderiv ℝ η z (0,v) : ℂ) ∂(volume.prod volume)) =
        -(∫ z, g z * (η z : ℂ) ∂(volume.prod volume)))
    (φ : F → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) :
    ∀ᵐ x ∂(volume : Measure E),
      (∫ y, u (x,y) * (fderiv ℝ φ y v : ℂ)) = -(∫ y, g (x,y) * (φ y : ℂ)) := by
  let dφ : F → ℂ := fun y => (fderiv ℝ φ y v : ℂ)
  let cφ : F → ℂ := fun y => (φ y : ℂ)
  have hd := test_direction_complex_memLp hφ hφC v
  have hc := test_complex_memLp hφ hφC
  let A := fiberContract (μ := volume) dφ u
  let B := fiberContract (μ := volume) cφ g
  have hA : MemLp A 2 volume := fiberContract_memLp hd hu
  have hB : MemLp B 2 volume := fiberContract_memLp hc hg
  have hzero : ∀ᵐ x ∂(volume : Measure E), (A + B) x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero ((hA.add hB).locallyIntegrable (by norm_num))
    intro χ hχ hχC
    have hχL := test_complex_memLp hχ hχC
    have H := hw (fun z => χ z.1 * φ z.2)
      ((hχ.comp contDiff_fst).mul (hφ.comp contDiff_snd)) (compact_tensor_test hχC hφC)
    simp_rw [tensor_test_deriv hχ hφ v, Complex.ofReal_mul] at H
    have H1 := integral_tensorPair hχL hd hu
    have H2 := integral_tensorPair hχL hc hg
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal] at H1 H2
    have L1 : (∫ z, u z * ((χ z.1 : ℂ) * (fderiv ℝ φ z.2 v : ℂ)) ∂(volume.prod volume)) =
      ∫ x, (χ x : ℂ) * A x := by
      simpa only [A, dφ, mul_comm] using H1
    have L2 : (∫ z, g z * ((χ z.1 : ℂ) * (φ z.2 : ℂ)) ∂(volume.prod volume)) =
      ∫ x, (χ x : ℂ) * B x := by
      simpa only [B, cφ, mul_comm] using H2
    rw [L1, L2] at H
    change (∫ x, (χ x) • (A x + B x)) = 0
    simp_rw [Complex.real_smul, mul_add]
    have hIntA : Integrable (fun x => (χ x : ℂ) * A x) := hχL.integrable_mul hA
    have hIntB : Integrable (fun x => (χ x : ℂ) * B x) := hχL.integrable_mul hB
    rw [integral_add hIntA hIntB, H, neg_add_cancel]
  filter_upwards [hzero] with x hx
  simpa only [Pi.add_apply, A, B, fiberContract, dφ, cφ,
    Complex.star_def, Complex.conj_ofReal, mul_comm, add_eq_zero_iff_eq_neg] using hx

lemma weak_slice {u g : E × F → ℂ}
    (hu : MemLp u 2 (volume.prod volume)) (hg : MemLp g 2 (volume.prod volume))
    (v : F)
    (hw : ∀ (η : E × F → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ z, u z * (fderiv ℝ η z (0,v) : ℂ) ∂(volume.prod volume)) =
        -(∫ z, g z * (η z : ℂ) ∂(volume.prod volume))) :
    ∀ᵐ x ∂(volume : Measure E),
      MemLp (fun y => u (x,y)) 2 volume ∧ MemLp (fun y => g (x,y)) 2 volume ∧
      ∀ (φ : F → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ y, u (x,y) * (fderiv ℝ φ y v : ℂ)) = -(∫ y, g (x,y) * (φ y : ℂ)) := by
  classical
  have : Fact ((2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞)) := ⟨by norm_num⟩
  have : SecondCountableTopology F :=
    (ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm :
      F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ)).toHomeomorph.secondCountableTopology
  let Tests := {φ : F → ℝ // ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ}
  let Q : Tests → Lp ℂ 2 (volume : Measure F) × Lp ℂ 2 (volume : Measure F) := fun φ =>
    ⟨(test_direction_complex_memLp φ.2.1 φ.2.2 v).toLp _,
      (test_complex_memLp φ.2.1 φ.2.2).toLp _⟩
  let T := Set.range Q
  let U : E → Lp ℂ 2 (volume : Measure F) := fun x =>
    if h : MemLp (fun y => u (x,y)) 2 volume then h.toLp _ else 0
  let G : E → Lp ℂ 2 (volume : Measure F) := fun x =>
    if h : MemLp (fun y => g (x,y)) 2 volume then h.toLp _ else 0
  let A : E → T → ℂ := fun x t => inner ℂ t.1.1 (U x) + inner ℂ t.1.2 (G x)
  have hAc (x : E) : Continuous (A x) :=
    ((continuous_fst.comp continuous_subtype_val).inner continuous_const).add
      ((continuous_snd.comp continuous_subtype_val).inner continuous_const)
  have hAQ (x : E) (hx : MemLp (fun y => u (x,y)) 2 volume)
      (hxg : MemLp (fun y => g (x,y)) 2 volume) (φ : Tests) :
      A x ⟨Q φ, mem_range_self _⟩ =
        (∫ y, u (x,y) * (fderiv ℝ φ.1 y v : ℂ)) + (∫ y, g (x,y) * (φ.1 y : ℂ)) := by
    dsimp only [A, Q]
    simp only [U, G, dite_eq_left hx, dite_eq_left hxg]
    rw [inner_toLp_complex, inner_toLp_complex]
    simp only [Complex.star_def, Complex.conj_ofReal, mul_comm]
  have hAz (t : T) : ∀ᵐ x ∂(volume : Measure E), A x t = 0 := by
    rcases t with ⟨_, φ, rfl⟩
    filter_upwards [memLp_fiber_ae hu, memLp_fiber_ae hg,
      weak_slice_fixed_test hu hg v hw φ.1 φ.2.1 φ.2.2] with x hx hxg hweak
    rw [hAQ x hx hxg φ, hweak, neg_add_cancel]
  have hall := ae_all_zero_of_continuous A hAc hAz
  filter_upwards [memLp_fiber_ae hu, memLp_fiber_ae hg, hall] with x hx hxg hall
  refine ⟨hx, hxg, ?_⟩
  intro φ hφ hφC
  have H := hall ⟨Q ⟨φ, hφ, hφC⟩, mem_range_self _⟩
  rw [hAQ x hx hxg] at H
  exact add_eq_zero_iff_eq_neg.mp H

end SmoothSlices
section LinearChange
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure E} {ν : Measure F}

lemma weak_directional_change {u g : F → ℂ} (L : E ≃L[ℝ] F)
    (hL : MeasurePreserving L.toHomeomorph.toMeasurableEquiv μ ν) (v : E)
    (hw : ∀ (φ : F → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ y, u y * (fderiv ℝ φ y (L v) : ℂ) ∂ν) = -(∫ y, g y * (φ y : ℂ) ∂ν)) :
    ∀ (η : E → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ x, u (L x) * (fderiv ℝ η x v : ℂ) ∂μ) =
        -(∫ x, g (L x) * (η x : ℂ) ∂μ) := by
  intro η hη hηC
  let Φ : F → ℝ := η ∘ L.symm
  have HΦ : ContDiff ℝ (⊤ : ℕ∞) Φ := hη.comp L.symm.contDiff
  have HC : HasCompactSupport Φ := hηC.comp_homeomorph L.symm.toHomeomorph
  have Hd (y : F) : fderiv ℝ Φ y (L v) = fderiv ℝ η (L.symm y) v := by
    dsimp only [Φ]
    rw [fderiv_comp y (hη.differentiable (by simp)).differentiableAt L.symm.differentiableAt,
      show fderiv ℝ (⇑L.symm) y = L.symm.toContinuousLinearMap from
        L.symm.toContinuousLinearMap.fderiv]
    simp
  have H := hw Φ HΦ HC
  simp_rw [Hd] at H
  rw [← hL.integral_comp' (fun y => u y * (fderiv ℝ η (L.symm y) v : ℂ)),
    ← hL.integral_comp' (fun y => g y * (Φ y : ℂ))] at H
  simpa [Φ] using H
end LinearChange

lemma H1Vector.weak_partial_join {m k : ℕ} (ψ : H1Vector (m+k))
    (s : Spins (m+k)) (a : Fin k × Fin 3) :
    ∀ (η : Configuration m × Configuration k → ℝ), ContDiff ℝ (⊤ : ℕ∞) η →
      HasCompactSupport η →
      (∫ z, ψ.value s (joinConfiguration m k z) *
        (fderiv ℝ η z (0, EuclideanSpace.single a 1) : ℂ) ∂(volume.prod volume)) =
      -(∫ z, ψ.gradient s (Fin.natAdd m a.1, a.2) (joinConfiguration m k z) *
        (η z : ℂ) ∂(volume.prod volume)) := by
  apply weak_directional_change (joinConfiguration m k) (joinConfiguration_measurePreserving m k)
    (0, EuclideanSpace.single a 1)
  rw [joinConfiguration_right_single]
  exact ψ.weak_partial s (Fin.natAdd m a.1, a.2)

lemma H1Vector.core_slices_H1 {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    ∀ᵐ x ∂(volume : Measure (Configuration m)),
      (∀ t : Spins k, MemLp (fun y => ψ.value (Fin.append s t) (joinConfiguration m k (x,y))) 2 volume) ∧
      (∀ (t : Spins k) (a : Fin k × Fin 3),
        MemLp (fun y => ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
          (joinConfiguration m k (x,y))) 2 volume ∧
        ∀ (φ : Configuration k → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ y, ψ.value (Fin.append s t) (joinConfiguration m k (x,y)) *
          (fderiv ℝ φ y (EuclideanSpace.single a 1) : ℂ)) =
        -(∫ y, ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
          (joinConfiguration m k (x,y)) * (φ y : ℂ))) := by
  have hV (t : Spins k) := (ψ.value_L2 (Fin.append s t)).comp_measurePreserving
    (joinConfiguration_measurePreserving m k)
  have hG (t : Spins k) (a : Fin k × Fin 3) :=
    (ψ.partial_L2 (Fin.append s t) (Fin.natAdd m a.1,a.2)).comp_measurePreserving
      (joinConfiguration_measurePreserving m k)
  have hval : ∀ᵐ x ∂(volume : Measure (Configuration m)),
      ∀ t : Spins k, MemLp (fun y => ψ.value (Fin.append s t) (joinConfiguration m k (x,y))) 2 volume :=
    ae_all_iff.mpr (fun t => memLp_fiber_ae
      (f := fun z : Configuration m × Configuration k =>
        ψ.value (Fin.append s t) (joinConfiguration m k z)) (hV t))
  have hgrad := fun (t : Spins k) (a : Fin k × Fin 3) =>
    weak_slice (hV t) (hG t a) (EuclideanSpace.single a 1)
      (ψ.weak_partial_join (Fin.append s t) a)
  have hall := ae_all_iff.mpr (fun t => ae_all_iff.mpr (hgrad t))
  filter_upwards [hval, hall] with x hx hall
  exact ⟨hx, fun t a => (hall t a).2⟩

def H1Vector.CoreSliceRegular {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    (x : Configuration m) : Prop :=
      (∀ t : Spins k, MemLp (fun y => ψ.value (Fin.append s t) (joinConfiguration m k (x,y))) 2 volume) ∧
      (∀ (t : Spins k) (a : Fin k × Fin 3),
        MemLp (fun y => ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
          (joinConfiguration m k (x,y))) 2 volume ∧
        ∀ (φ : Configuration k → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ y, ψ.value (Fin.append s t) (joinConfiguration m k (x,y)) *
          (fderiv ℝ φ y (EuclideanSpace.single a 1) : ℂ)) =
        -(∫ y, ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
          (joinConfiguration m k (x,y)) * (φ y : ℂ)))

lemma H1Vector.coreSliceRegular_ae {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    ∀ᵐ x ∂volume, ψ.CoreSliceRegular s x := ψ.core_slices_H1 s

noncomputable def H1Vector.zero (n : ℕ) : H1Vector n where
  value := fun _ _ => 0
  gradient := fun _ _ _ => 0
  value_L2 := fun _ => MemLp.zero'
  partial_L2 := fun _ _ => MemLp.zero'
  weak_partial := by intros; simp

noncomputable def H1Vector.coreSlice {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    (x : Configuration m) : H1Vector k := by
  classical
  exact if h : ψ.CoreSliceRegular s x then
    { value := fun t y => ψ.value (Fin.append s t) (joinConfiguration m k (x,y))
      gradient := fun t a y => ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
        (joinConfiguration m k (x,y))
      value_L2 := h.1
      partial_L2 := fun t a => (h.2 t a).1
      weak_partial := fun t a => (h.2 t a).2 }
  else H1Vector.zero k

lemma H1Vector.coreSlice_value {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    {x : Configuration m} (hx : ψ.CoreSliceRegular s x) (t : Spins k) (y : Configuration k) :
    (ψ.coreSlice s x).value t y = ψ.value (Fin.append s t) (joinConfiguration m k (x,y)) := by
  simp [H1Vector.coreSlice, hx]

lemma H1Vector.coreSlice_gradient {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    {x : Configuration m} (hx : ψ.CoreSliceRegular s x) (t : Spins k) (a : Fin k × Fin 3)
    (y : Configuration k) :
    (ψ.coreSlice s x).gradient t a y =
      ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2) (joinConfiguration m k (x,y)) := by
  simp [H1Vector.coreSlice, hx]

lemma mass_coreSlice_ae {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    (fun x => mass (ψ.coreSlice s x)) =ᵐ[volume]
      fun x => ∑ t : Spins k, ∫ y, ‖ψ.value (Fin.append s t) (joinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.coreSliceRegular_ae s] with x hx
  simp only [mass, ψ.coreSlice_value s hx]

lemma mass_coreSlice_integrable {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)) := by
  apply Integrable.congr _ (mass_coreSlice_ae ψ s).symm
  apply integrable_finsetSum
  intro t _
  have h := ((ψ.value_L2 (Fin.append s t)).comp_measurePreserving
    (joinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)
  exact h.integral_prod_left

lemma integral_mass_coreSlice {m k : ℕ} (ψ : H1Vector (m+k)) :
    (∑ s : Spins m, ∫ x, mass (ψ.coreSlice s x)) = mass ψ := by
  calc
    _ = ∑ s : Spins m, ∑ t : Spins k, ∫ z, ‖ψ.value (Fin.append s t) z‖^2 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [integral_congr_ae (mass_coreSlice_ae ψ s), integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro t _
        have h := ((ψ.value_L2 (Fin.append s t)).comp_measurePreserving
          (joinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)
        change Integrable (fun z : Configuration m × Configuration k =>
          ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) at h
        rw [← integral_prod _ h]
        exact (joinConfiguration_measurePreserving m k).integral_comp'
          (fun z => ‖ψ.value (Fin.append s t) z‖^2)
      · intro t _
        exact (((ψ.value_L2 (Fin.append s t)).comp_measurePreserving
          (joinConfiguration_measurePreserving m k)).integrable_norm_pow
            (p := 2) (by decide)).integral_prod_left
    _ = mass ψ := by
      rw [← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
        ∫ z, ‖ψ.value (Fin.append st.1 st.2) z‖^2)]
      exact Fintype.sum_equiv (Fin.appendEquiv m k) _ _ (fun _ => rfl)

end Coulomb

end

end OAI
