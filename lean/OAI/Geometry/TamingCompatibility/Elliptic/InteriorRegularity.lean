import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.MatrixH1Smooth

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter Set
open scoped SchwartzMap LineDeriv Topology Manifold ContDiff BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] in

lemma exists_outer_cutoff {U : Set E} (hU : IsOpen U) (g : 𝓢(E,ℂ))
    (hg : HasCompactSupport (g : E → ℂ)) (hgU : tsupport g ⊆ U) :
    ∃ h : 𝓢(E,ℂ), HasCompactSupport (h : E → ℂ) ∧ tsupport h ⊆ U ∧
      ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1 := by
  obtain ⟨t,ht,hgt,htU⟩ := exists_compact_between hg hU hgU
  obtain ⟨h,he,hz,-⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ,E) (n := (⊤ : ℕ∞)) (isClosed_tsupport g) hgt
  let f : E → ℂ := fun x => (h x : ℂ)
  have hs : ContDiff ℝ ∞ f := by
    exact Complex.ofRealCLM.contDiff.comp h.contMDiff.contDiff
  have hft : tsupport f ⊆ t := by
    apply closure_minimal _ ht.isClosed
    intro x hx
    by_contra hn
    exact hx (by simp only [f, hz x hn, Complex.ofReal_zero])
  have hf : HasCompactSupport f := ht.of_isClosed_subset (isClosed_tsupport f) hft
  refine ⟨hf.toSchwartzMap hs, hf, hft.trans htU, ?_⟩
  intro x hx
  filter_upwards [he.filter_mono (nhds_le_nhdsSet hx)] with y hy
  change (h y : ℂ) = 1
  simp [hy]

def MemSobolevLoc (U : Set E) (s : ℝ) (u : 𝓢'(E,F)) : Prop :=
  ∀ g : 𝓢(E,ℂ), HasCompactSupport (g : E → ℂ) → tsupport g ⊆ U →
    MemSobolev s 2 (smulLeftCLM F g u)

lemma MemSobolevLoc.mono {U : Set E} {s t : ℝ} {u : 𝓢'(E,F)}
    (h : MemSobolevLoc U s u) (hst : t ≤ s) : MemSobolevLoc U t u :=
  fun g hg hgU => (h g hg hgU).mono hst

theorem matrix_H1_interior_bootstrap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ℕ) {U : Set E} (hU : IsOpen U)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbationNegOne (F := F) a‖ < 1)
    (hstrong : ‖perturbation (F := F) 0 a‖ < 1)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) {u : 𝓢'(E,F)}
    (hu : MemSobolevLoc U 1 u)
    (hf : MemSobolevLoc U n (perturbedHelmholtz a u + matrixLowerOrder b L v c K u)) :
    MemSobolevLoc U ((n:ℝ)+2) u := by
  induction n with
  | zero =>
    intro g hg hgU
    obtain ⟨h,hh,hhU,hhg⟩ := exists_outer_cutoff hU g hg hgU
    have hloc := hf g hg hgU
    have he : smulLeftCLM F g (perturbedHelmholtz a (smulLeftCLM F h u) +
        matrixLowerOrder b L v c K (smulLeftCLM F h u)) =
        smulLeftCLM F g (perturbedHelmholtz a u + matrixLowerOrder b L v c K u) := by
      rw [map_add, perturbedHelmholtz_locality a g h hhg,
        matrixLowerOrder_locality b L v c K g h hhg, ← map_add]
    have hr := matrix_cutoff_H1_regular a hweak hstrong b L v c K g
      (hu h hh hhU) (by simpa only [he, Nat.cast_zero] using hloc)
    simpa only [cutoff_mul_cutoff g h hhg, Nat.cast_zero, zero_add] using hr
  | succ n ih =>
    have hun := ih (hf.mono (by exact_mod_cast Nat.le_succ n))
    intro g hg hgU
    obtain ⟨h,hh,hhU,hhg⟩ := exists_outer_cutoff hU g hg hgU
    have hhu : MemSobolev ((n+1:ℕ)+1:ℝ) 2 (smulLeftCLM F h u) := by
      convert hun h hh hhU using 1
      push_cast
      ring
    have he : smulLeftCLM F g (perturbedHelmholtz a (smulLeftCLM F h u) +
        matrixLowerOrder b L v c K (smulLeftCLM F h u)) =
        smulLeftCLM F g (perturbedHelmholtz a u + matrixLowerOrder b L v c K u) := by
      rw [map_add, perturbedHelmholtz_locality a g h hhg,
        matrixLowerOrder_locality b L v c K g h hhg, ← map_add]
    have hr := matrix_cutoff_succ_regular (n+1) a hweak hstrong b L v c K g
      hhu (he ▸ hf g hg hgU)
    simpa only [cutoff_mul_cutoff g h hhg] using hr

theorem matrix_H1_interior_smooth {ι κ : Type*} [Fintype ι] [Fintype κ]
    {U : Set E} (hU : IsOpen U)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbationNegOne (F := F) a‖ < 1)
    (hstrong : ‖perturbation (F := F) 0 a‖ < 1)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) {u : 𝓢'(E,F)}
    (hu : MemSobolevLoc U 1 u)
    (hf : ∀ n : ℕ, MemSobolevLoc U n
      (perturbedHelmholtz a u + matrixLowerOrder b L v c K u))
    (g : 𝓢(E,ℂ)) (hg : HasCompactSupport (g : E → ℂ)) (hgU : tsupport g ⊆ U) :
    ∃ f : E →ᵇ F, ContDiff ℝ ∞ (f : E → F) ∧
      smulLeftCLM F g u = EuclideanSobolev.boundedDistribution f := by
  apply EuclideanSobolev.exists_smooth_representative
  intro s
  obtain ⟨n,hn⟩ := exists_nat_gt s
  exact (matrix_H1_interior_bootstrap n hU a hweak hstrong b L v c K hu (hf n)
    g hg hgU).mono (by linarith)

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def linearDistribution (L : E ≃L[ℝ] E) : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F) :=
  PointwiseConvergenceCLM.precomp F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma linearDistribution_apply (L : E ≃L[ℝ] E) (u : 𝓢'(E,F)) (φ : 𝓢(E,ℂ)) :
    linearDistribution L u φ = u (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L φ) := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma linearSchwartz_derivative (L : E ≃L[ℝ] E) (φ : 𝓢(E,ℂ)) (v : E) :
    ∂_{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L φ) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L (∂_{L v} φ) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rw [((φ.hasFDerivAt (L x)).comp x L.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma linearDistribution_derivative (L : E ≃L[ℝ] E) (u : 𝓢'(E,F)) (v : E) :
    linearDistribution L (∂_{v} u) = ∂_{L v} (linearDistribution L u) := by
  ext φ
  simp only [linearDistribution_apply,lineDerivOp_apply_apply,
    linearSchwartz_derivative,map_neg]

omit [InnerProductSpace ℂ F] [CompleteSpace F] in
lemma memLp_comp_linearEquiv (L : E ≃L[ℝ] E) {f : E → F}
    (hf : MemLp f 2 (volume : Measure E)) :
    MemLp (fun x => f (L x)) 2 (volume : Measure E) := by
  have hm : MemLp f 2 (Measure.map L volume) := by
    rw [show Measure.map L volume = ENNReal.ofReal |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹| • volume from
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume L.toLinearEquiv.isUnit_det'.ne_zero]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hm.comp_of_map L.continuous.measurable.aemeasurable

lemma linearDistribution_lp (L : E ≃L[ℝ] E) (f : Lp F 2 (volume : Measure E)) :
    ∃ g : Lp F 2 (volume : Measure E), linearDistribution L (f : 𝓢'(E,F)) = (g : 𝓢'(E,F)) := by
  let c : ℝ := |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹|
  let h : E → F := fun y => c • f (L.symm y)
  have hh : MemLp h 2 (volume : Measure E) :=
    (memLp_comp_linearEquiv L.symm (Lp.memLp f)).const_smul c
  refine ⟨hh.toLp h,?_⟩
  ext φ
  rw [linearDistribution_apply,Lp.toTemperedDistribution_apply,Lp.toTemperedDistribution_apply]
  have he : (∫ y, φ y • (hh.toLp h) y) = ∫ y, φ y • h y := by
    apply integral_congr_ae
    filter_upwards [hh.coeFn_toLp] with y hy
    rw [hy]
  rw [he]
  change (∫ x, φ (L x) • f x) = _
  have hm := L.toHomeomorph.measurableEmbedding.integral_map
    (μ := (volume : Measure E)) (fun y => φ y • f (L.symm y))
  change (∫ y, φ y • f (L.symm y) ∂Measure.map L volume) =
    ∫ x, φ (L x) • f (L.symm (L x)) at hm
  rw [show Measure.map L volume = ENNReal.ofReal c • volume from
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume L.toLinearEquiv.isUnit_det'.ne_zero,
    integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _)] at hm
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hm
  rw [← hm,← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  exact smul_comm c (φ y) _

lemma memSobolev_zero_linear (L : E ≃L[ℝ] E) {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) :
    MemSobolev 0 2 (linearDistribution L u) := by
  obtain ⟨f,hf⟩ := hu
  have he : u = (f : 𝓢'(E,F)) := by simpa using hf
  rw [he]
  obtain ⟨g,hg⟩ := linearDistribution_lp L f
  exact ⟨g,by simpa using hg⟩

theorem memSobolev_nat_linear (n : ℕ) (L : E ≃L[ℝ] E) {u : 𝓢'(E,F)}
    (hu : MemSobolev n 2 u) : MemSobolev n 2 (linearDistribution L u) := by
  induction n generalizing u with
  | zero =>
    simp only [Nat.cast_zero] at hu ⊢
    exact memSobolev_zero_linear L hu
  | succ n ih =>
    have hu' : MemSobolev n 2 u := hu.mono (by exact_mod_cast Nat.le_succ n)
    have hd (i : Fin (Module.finrank ℝ E)) :
        MemSobolev n 2 (∂_{stdOrthonormalBasis ℝ E i} (linearDistribution L u)) := by
      have hdu : MemSobolev n 2 (∂_{L.symm (stdOrthonormalBasis ℝ E i)} u) := by
        convert hu.lineDerivOp using 1
        simp
      have h := ih hdu
      rw [linearDistribution_derivative,ContinuousLinearEquiv.apply_symm_apply] at h
      exact h
    simpa using memSobolev_succ_of_derivatives (stdOrthonormalBasis ℝ E) (ih hu') hd
end TamingCompatibility.EuclideanSobolevOperators

end
end

end
end
end

end OAI
