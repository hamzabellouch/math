import OAI.Analysis.PeriodicLattice.FluidLift

namespace OAI

/-! Translation derivatives and smooth periodic lifts. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingTorusDerivatives {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace TorusCalculus

open scoped ContDiff

theorem mk_isOpenQuotientMap : IsOpenQuotientMap torusMk := by
  have h : IsOpenQuotientMap (fun x : Fin 3 → ℝ => fun i => (x i : UnitAddCircle)) :=
    IsOpenQuotientMap.piMap (fun _ : Fin 3 => QuotientAddGroup.isOpenQuotientMap_mk)
  exact h.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toHomeomorph.isOpenQuotientMap

theorem continuous_iff_lifted {A : Type*} [TopologicalSpace A] (F : ℝ → Torus → A) :
    Continuous (Function.uncurry F) ↔
      Continuous (fun tx : ℝ × Space => F tx.1 (torusMk tx.2)) :=
  (IsOpenQuotientMap.id.prodMap mk_isOpenQuotientMap).isQuotientMap.continuous_iff

theorem single_eq_smul (i : Fin 3) (s : ℝ) :
    EuclideanSpace.single i s = s • EuclideanSpace.single i 1 := by
  ext j
  simp only [PiLp.single_apply, PiLp.smul_apply, smul_eq_mul]
  split <;> simp

section Derivatives
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem spaceD_eq_fderiv (i : Fin 3) {F : Field A} {t : ℝ} (x : Space)
    (hF : Differentiable ℝ (spaceLift F t)) :
    spaceD i F t (torusMk x) =
      (fderiv ℝ (spaceLift F t) x) (EuclideanSpace.single i 1) := by
  rw [spaceD_cover]
  have heq : (fun s : ℝ => spaceLift F t (x + EuclideanSpace.single i s)) =
      (fun s : ℝ => spaceLift F t (x + s • EuclideanSpace.single i 1)) := by
    funext s
    rw [single_eq_smul i s]
  rw [heq]
  have h := (hF (x + (0 : ℝ) • EuclideanSpace.single i 1)).hasFDerivAt.comp_hasDerivAt 0
    (((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i 1)).const_add x)
  simpa only [Function.comp_def, id_eq, zero_smul, add_zero, one_smul] using h.deriv

theorem contDiff_spaceD {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) (i : Fin 3) :
    ContDiff ℝ ∞ (lifted (spaceD i F)) := by
  let f : (ℝ × Space) → Space → A := fun tx x => F tx.1 (torusMk x)
  have hf : ContDiff ℝ ∞ (Function.uncurry f) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hf.fderiv_apply contDiff_snd
    (show ContDiff ℝ ∞ (fun _ : ℝ × Space => EuclideanSpace.single i 1) from contDiff_const)
    (by simp)
  have heq : lifted (spaceD i F) = fun tx : ℝ × Space =>
      (fderiv ℝ (f tx) tx.2) (EuclideanSpace.single i 1) := by
    funext tx
    exact spaceD_eq_fderiv i tx.2
      ((hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp))
  rw [heq]
  exact hd

def fullTimeD (F : Field A) : Field A := fun t q => deriv (fun s => F s q) t

theorem contDiff_fullTimeD {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) :
    ContDiff ℝ ∞ (lifted (fullTimeD F)) := by
  let f : (ℝ × Space) → ℝ → A := fun tx s => F s (torusMk tx.2)
  have hf : ContDiff ℝ ∞ (Function.uncurry f) :=
    hF.comp (contDiff_snd.prodMk contDiff_fst.snd)
  exact hf.fderiv_apply contDiff_fst contDiff_const (by simp)

theorem timeD_eq_fullTimeD {F : Field A} (hF : ContDiff ℝ ∞ (lifted F))
    {t : ℝ} (ht : 0 ≤ t) (q : Torus) : timeD F t q = fullTimeD F t q := by
  obtain ⟨x, rfl⟩ := mk_surjective q
  have hd : Differentiable ℝ (fun s => F s (torusMk x)) :=
    (hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
  exact (hd t).hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht)

theorem contDiff_laplacian {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) :
    ContDiff ℝ ∞ (lifted (laplacian F)) := by
  unfold lifted laplacian
  exact ContDiff.sum (s := Finset.univ) (fun i _ => (contDiff_spaceD (contDiff_spaceD hF i) i))

theorem cylinderContinuous {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) : CylinderContinuous F :=
  fun _ _ => ((continuous_iff_lifted F).mpr hF.continuous).continuousOn

theorem timeD_cylinderContinuous {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) :
    CylinderContinuous (timeD F) := by
  intro T _hT
  apply (cylinderContinuous (contDiff_fullTimeD hF) T _hT).congr
  intro tq htq
  exact timeD_eq_fullTimeD hF htq.1.1 tq.2

end Derivatives

theorem contDiff_advection {U : VectorField} (hU : ContDiff ℝ ∞ (lifted U)) :
    ContDiff ℝ ∞ (lifted (advection U)) := by
  unfold lifted advection
  apply ContDiff.sum (s := Finset.univ)
  intro i _
  have hi : ContDiff ℝ ∞ (fun tx : ℝ × Space => lifted U tx i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).contDiff.comp hU
  exact hi.smul (contDiff_spaceD hU i)

theorem classical_of_smooth {ν : ℝ} {F U : VectorField}
    (hU : ContDiff ℝ ∞ (lifted U)) (hNS : NavierStokes ν F U 0) :
    ClassicalSolution ν F U 0 where
  velocityContinuous := cylinderContinuous hU
  timeDifferentiable := by
    intro t _ht q
    obtain ⟨x, rfl⟩ := mk_surjective q
    exact (((hU.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)) t).differentiableWithinAt
  timeContinuous := timeD_cylinderContinuous hU
  spaceTwiceDifferentiable := fun _t _ht =>
    (hU.comp (contDiff_const.prodMk contDiff_id)).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  spaceFirstContinuous := fun i => cylinderContinuous (contDiff_spaceD hU i)
  spaceSecondContinuous := fun i j => cylinderContinuous (contDiff_spaceD (contDiff_spaceD hU j) i)
  pressureContinuous := fun _ _ => continuousOn_const
  pressureDifferentiable := fun _t _ht => differentiable_const _
  pressureGradientContinuous := by
    simp only [Residual.gradient_zero]
    exact fun _ _ => continuousOn_const
  pressureMeanZero := fun _t _ht => MeasureTheory.integral_zero _ _
  equations := hNS

end TorusCalculus
namespace TorusCalculus

open scoped ContDiff Topology
open Filter Set MeasureTheory

@[simp] theorem mk_zero : torusMk 0 = 0 := by
  ext i
  simp [torusMk]

@[simp] theorem single_zero (i : Fin 3) : EuclideanSpace.single i (0 : ℝ) = 0 := by
  ext j
  simp only [PiLp.single_apply, PiLp.zero_apply]
  split <;> rfl

instance volume_probability : IsProbabilityMeasure torusVolume := by
  dsimp [torusVolume]
  infer_instance

instance volume_rightInvariant : torusVolume.IsAddRightInvariant := by
  dsimp [torusVolume]
  infer_instance

section Integrals
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

omit [NormedSpace ℝ A] in
theorem slice_integrable {F : Field A} (hF : Continuous (Function.uncurry F)) (t : ℝ) :
    Integrable (F t) torusVolume :=
  (hF.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem smooth_slice_integrable {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) (t : ℝ) :
    Integrable (F t) torusVolume :=
  slice_integrable ((continuous_iff_lifted F).mpr hF.continuous) t

theorem hasDerivAt_translation {F : Field A} (hF : ContDiff ℝ ∞ (lifted F))
    (t : ℝ) (q : Torus) (i : Fin 3) (s : ℝ) :
    HasDerivAt (fun s => F t (q + torusMk (EuclideanSpace.single i s)))
      (spaceD i F t (q + torusMk (EuclideanSpace.single i s))) s := by
  obtain ⟨x, rfl⟩ := mk_surjective q
  have hsp : Differentiable ℝ (spaceLift F t) :=
    (hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  simp only [← mk_add, spaceD_eq_fderiv i _ hsp]
  have hcv : HasDerivAt (fun r : ℝ => x + EuclideanSpace.single i r)
      (EuclideanSpace.single i 1) s := by
    have heq : (fun r : ℝ => x + EuclideanSpace.single i r) =
        (fun r : ℝ => x + r • EuclideanSpace.single i 1) := by
      funext r
      rw [single_eq_smul i r]
    rw [heq]
    simpa only [id_eq, one_smul] using
      (((hasDerivAt_id s).smul_const (EuclideanSpace.single i 1)).const_add x)
  exact (hsp _).hasFDerivAt.comp_hasDerivAt s hcv

theorem integral_spaceD {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) (t : ℝ) (i : Fin 3) :
    (∫ q, spaceD i F t q ∂torusVolume) = 0 := by
  have hFc := (continuous_iff_lifted F).mpr hF.continuous
  have hDc := (continuous_iff_lifted (spaceD i F)).mpr (contDiff_spaceD hF i).continuous
  have hFct : Continuous (F t) := hFc.comp (continuous_const.prodMk continuous_id)
  have hDct : Continuous (spaceD i F t) := hDc.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hDct.continuousOn
  let G : ℝ → Torus → A := fun s q => F t (q + torusMk (EuclideanSpace.single i s))
  let G' : ℝ → Torus → A := fun s q => spaceD i F t (q + torusMk (EuclideanSpace.single i s))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := torusVolume)
    (F := G) (F' := G') (s := univ) (x₀ := 0) (bound := fun _ => C)
    (Filter.univ_mem)
    (Filter.Eventually.of_forall (fun s =>
      (hFct.comp (continuous_id.add continuous_const)).aestronglyMeasurable))
    (by simpa [G] using (smooth_slice_integrable hF t))
    ((hDct.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun q s _ => hC _ (mem_univ _)))
    (integrable_const C)
    (Filter.Eventually.of_forall (fun q s _ => hasDerivAt_translation hF t q i s))
  have heq : (fun s => ∫ q, G s q ∂torusVolume) =
      fun _ : ℝ => ∫ q, F t q ∂torusVolume := by
    funext s
    exact integral_add_right_eq_self _ _
  rw [heq] at h
  have hz := h.2.unique (hasDerivAt_const (0 : ℝ) (∫ q, F t q ∂torusVolume))
  simpa [G'] using hz

theorem integral_laplacian {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) (t : ℝ) :
    (∫ q, laplacian F t q ∂torusVolume) = 0 := by
  rw [show (laplacian F t) = fun q => ∑ i : Fin 3, spaceD i (spaceD i F) t q from rfl,
    integral_finsetSum Finset.univ (fun i _ => smooth_slice_integrable
      (contDiff_spaceD (contDiff_spaceD hF i) i) t)]
  simp only [integral_spaceD (contDiff_spaceD hF _) t, Finset.sum_const_zero]

end Integrals
end TorusCalculus

namespace Residual

open scoped ContDiff
open TorusCalculus

def fullForce (ν : ℝ) (U : VectorField) : VectorField := fun t q =>
  fullTimeD U t q + advection U t q - ν • laplacian U t q

theorem fullForce_contDiff (ν : ℝ) {U : VectorField} (hU : ContDiff ℝ ∞ (lifted U)) :
    ContDiff ℝ ∞ (lifted (fullForce ν U)) :=
  ((contDiff_fullTimeD hU).add (contDiff_advection hU)).sub
    ((contDiff_laplacian hU).const_smul ν)

theorem fullForce_eq (ν : ℝ) {U : VectorField} (hU : ContDiff ℝ ∞ (lifted U))
    {t : ℝ} (ht : 0 ≤ t) (q : Torus) : fullForce ν U t q = force ν U t q := by
  rw [fullForce, force, timeD_eq_fullTimeD hU ht]

theorem fullForce_equations (ν : ℝ) {U : VectorField} (hU : ContDiff ℝ ∞ (lifted U))
    (hdiv : Solenoidal U) (hinit : ∀ q, U 0 q = 0) :
    NavierStokes ν (fullForce ν U) U 0 := by
  refine ⟨?_, hdiv, hinit⟩
  intro t ht q
  rw [fullForce_eq ν hU ht]
  exact (equations ν U hdiv hinit).1 t ht q

end Residual

namespace FluidLift

open scoped ContDiff
open TorusCalculus

def force (ν : ℝ) (d : Input) : VectorField := Residual.fullForce ν (velocity d)

theorem force_contDiff (ν : ℝ) (d : Input) : ContDiff ℝ ∞ (lifted (force ν d)) :=
  Residual.fullForce_contDiff ν (velocity_contDiff d)

theorem force_smooth (ν : ℝ) (d : Input) : Smooth (force ν d) :=
  (force_contDiff ν d).contDiffOn

theorem equations (ν : ℝ) (d : Input) : NavierStokes ν (force ν d) (velocity d) 0 :=
  Residual.fullForce_equations ν (velocity_contDiff d) (velocity_solenoidal d) (velocity_start d)

theorem classical_solution (ν : ℝ) (d : Input) :
    ClassicalSolution ν (force ν d) (velocity d) 0 :=
  classical_of_smooth (velocity_contDiff d) (equations ν d)

end FluidLift

namespace TorusCalculus

open scoped ContDiff
open MeasureTheory

theorem contDiff_component {U : VectorField} (hU : ContDiff ℝ ∞ (lifted U)) (j : Fin 3) :
    ContDiff ℝ ∞ (lifted (fun t q => U t q j)) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).contDiff.comp hU

theorem spaceD_smul {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {c : ScalarField} {F : Field A} (hc : ContDiff ℝ ∞ (lifted c))
    (hF : ContDiff ℝ ∞ (lifted F)) (i : Fin 3) (t : ℝ) (q : Torus) :
    spaceD i (fun t q => c t q • F t q) t q =
      spaceD i c t q • F t q + c t q • spaceD i F t q := by
  have h := ((hasDerivAt_translation hc t q i 0).fun_smul
    (hasDerivAt_translation hF t q i 0)).deriv
  simpa only [single_zero, mk_zero, add_zero, spaceD, Pi.smul_apply, add_comm] using h

theorem advection_eq_tensor_divergence {U : VectorField}
    (hU : ContDiff ℝ ∞ (lifted U)) (t : ℝ) (hdiv : ∀ q, divergence U t q = 0) (q : Torus) :
    advection U t q = ∑ i : Fin 3, spaceD i (fun t q => U t q i • U t q) t q := by
  simp_rw [spaceD_smul (contDiff_component hU _) hU]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul]
  change advection U t q = divergence U t q • U t q + advection U t q
  rw [hdiv q, zero_smul, zero_add]

theorem integral_advection {U : VectorField} (hU : ContDiff ℝ ∞ (lifted U))
    (t : ℝ) (hdiv : ∀ q, divergence U t q = 0) :
    (∫ q, advection U t q ∂torusVolume) = 0 := by
  have hprod (i : Fin 3) : ContDiff ℝ ∞ (lifted (fun t q => U t q i • U t q)) :=
    (contDiff_component hU i).smul hU
  simp_rw [advection_eq_tensor_divergence hU t hdiv]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    smooth_slice_integrable (contDiff_spaceD (hprod i) i) t)]
  simp only [integral_spaceD (hprod _) t, Finset.sum_const_zero]

end TorusCalculus

namespace FluidLift

open scoped ContDiff
open TorusCalculus MeasureTheory

theorem timeDerivative_half_shift (d : Input) (t : ℝ) (q : Torus) :
    fullTimeD (velocity d) t (q + torusMk (EuclideanSpace.single 2 (1 / 2))) =
      -fullTimeD (velocity d) t q := by
  unfold fullTimeD
  simp_rw [velocity_half_shift]
  exact deriv.neg

theorem integral_timeDerivative (d : Input) (t : ℝ) :
    (∫ q, fullTimeD (velocity d) t q ∂torusVolume) = 0 :=
  integral_eq_zero_of_add_right_eq_neg (timeDerivative_half_shift d t)

theorem force_meanZero (ν : ℝ) (d : Input) : MeanZero (force ν d) := by
  intro t _ht
  have hU := velocity_contDiff d
  have h₁ := smooth_slice_integrable (contDiff_fullTimeD hU) t
  have h₂ := smooth_slice_integrable (contDiff_advection hU) t
  have h₃ : Integrable (fun q => ν • laplacian (velocity d) t q) torusVolume :=
    (smooth_slice_integrable (contDiff_laplacian hU) t).fun_smul ν
  change (∫ q, fullTimeD (velocity d) t q + advection (velocity d) t q -
    ν • laplacian (velocity d) t q ∂torusVolume) = 0
  rw [integral_sub (h₁.fun_add h₂) h₃, integral_add h₁ h₂, integral_smul,
    integral_timeDerivative, integral_advection hU t (divergence_zero d t), integral_laplacian hU t]
  simp

theorem residual_computation (ν : ℝ) (d : Input) (hd : d.WellFormed) :
    Smooth (velocity d) ∧ Smooth (force ν d) ∧
    MeanZero (velocity d) ∧ MeanZero (force ν d) ∧
    ClassicalSolution ν (force ν d) (velocity d) 0 ∧
    IsParticle (velocity d) (path d) ∧
    (∀ Y : ℝ → Space, IsParticle (velocity d) Y → ∀ t : ℝ, 0 ≤ t → Y t = path d t) ∧
    (MaterialEvent (path d) ↔ Halts d) :=
  ⟨velocity_smooth d, force_smooth ν d, velocity_meanZero d, force_meanZero ν d,
    classical_solution ν d, path_isParticle d hd,
    fun _Y hY _t ht => path_unique d hd hY ht, path_event_iff d hd⟩

end FluidLift

end
end PeriodicLattice

end OAI
