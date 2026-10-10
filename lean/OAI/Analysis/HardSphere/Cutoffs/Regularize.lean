import Mathlib
import OAI.Analysis.HardSphere.Orbitals.FieldApply

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace ComplexRegularization

def regularize (ε : ℝ) (z : ℂ) : ℂ := (Real.sqrt (‖z‖ ^ 2 + ε ^ 2) - ε : ℝ)

def differential (ε : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (Real.sqrt (‖z‖ ^ 2 + ε ^ 2))⁻¹ • (Complex.ofRealCLM.comp (innerSL ℝ z))

lemma smooth {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (regularize ε) := by
  apply Complex.ofRealCLM.contDiff.comp
  apply ContDiff.sub _ contDiff_const
  apply ContDiff.sqrt ((contDiff_norm_sq ℝ).add contDiff_const)
  intro z
  positivity

lemma zero {ε : ℝ} (hε : 0 ≤ ε) : regularize ε 0 = 0 := by
  simp [regularize, Real.sqrt_sq hε]

lemma hasFDerivAt {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    HasFDerivAt (regularize ε) (differential ε z) z := by
  have hn : ‖z‖ ^ 2 + ε ^ 2 ≠ 0 := by positivity
  have h := Complex.ofRealCLM.hasFDerivAt.comp z
    ((((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε ^ 2)).sqrt hn).sub_const ε)
  have hd : differential ε z = Complex.ofRealCLM.comp
      ((1 / (2 * Real.sqrt (‖z‖ ^ 2 + ε ^ 2))) • (2 • innerSL ℝ z)) := by
    ext w
    simp [differential, two_smul, div_eq_mul_inv, mul_inv_rev]
    ring

  rw [hd]
  exact h

lemma sqroot_ge_norm (ε : ℝ) (z : ℂ) : ‖z‖ ≤ Real.sqrt (‖z‖ ^ 2 + ε ^ 2) := by
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by nlinarith [sq_nonneg ε])

lemma differential_apply_le (ε : ℝ) (z w : ℂ) :
    ‖differential ε z w‖ ≤ ‖w‖ := by
  by_cases hz : z = 0
  · simp [hz, differential]
  have hp : 0 < Real.sqrt (‖z‖ ^ 2 + ε ^ 2) :=
    lt_of_lt_of_le (norm_pos_iff.mpr hz) (sqroot_ge_norm ε z)
  simp only [differential, smul_apply, ContinuousLinearMap.comp_apply,
    norm_smul, Complex.ofRealCLM_apply, Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_pos hp, innerSL_apply_apply]
  change _ * ‖inner ℝ z w‖ ≤ _
  apply le_trans (mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℝ) z w) (by positivity :
    0 ≤ (Real.sqrt (‖z‖ ^ 2 + ε ^ 2))⁻¹))
  rw [← div_eq_inv_mul, div_le_iff₀ hp]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (sqroot_ge_norm ε z) (norm_nonneg w)

lemma differential_le (ε : ℝ) (z : ℂ) : ‖differential ε z‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  simpa only [one_mul] using differential_apply_le ε z w

lemma fderiv_eq {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    fderiv ℝ (regularize ε) z = differential ε z := (hasFDerivAt hε z).fderiv

lemma tendsto_regularize (z : ℂ) {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n ↦ regularize (e n) z) atTop (𝓝 (‖z‖ : ℂ)) := by
  have h : Tendsto (fun n ↦ Real.sqrt (‖z‖ ^ 2 + e n ^ 2) - e n) atTop (𝓝 ‖z‖) := by
    have h := (((tendsto_const_nhds (x := ‖z‖ ^ 2)).add (he.pow 2)).sqrt.sub he)
    simpa using h

  exact Complex.continuous_ofReal.tendsto _ |>.comp h

lemma tendsto_differential (z : ℂ) {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n ↦ differential (e n) z) atTop (𝓝 (differential 0 z)) := by
  by_cases hz : z = 0
  · simp only [hz, differential, map_zero, ContinuousLinearMap.comp_zero, smul_zero]
    exact tendsto_const_nhds
  have hp : Real.sqrt (‖z‖ ^ 2 + (0 : ℝ) ^ 2) ≠ 0 := by
    simp [Real.sqrt_sq (norm_nonneg z), hz]
  exact (((tendsto_const_nhds.add (he.pow 2)).sqrt.inv₀ hp).smul tendsto_const_nhds)

end ComplexRegularization

namespace HardSphere
open ComplexRegularization

def regularization (ε : ℝ) (hε : 0 < ε) : SmoothContraction where
  toFun := regularize ε
  smooth := smooth hε
  zero := zero hε.le
  derivative_le z := by rw [fderiv_eq hε]; exact differential_le ε z

def regularizationScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

lemma regularizationScale_pos (n : ℕ) : 0 < regularizationScale n := by
  unfold regularizationScale
  positivity

lemma tendsto_regularizationScale : Tendsto regularizationScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma modulus_lipschitz : LipschitzWith 1 (fun z : ℂ ↦ (‖z‖ : ℂ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, NNReal.coe_one, one_mul]
    using dist_norm_norm_le z w

def modulusScalar {N : ℕ} {L : Length} (u : ScalarL2 N L) : ScalarL2 N L :=
  modulus_lipschitz.compLp (by simp) u

lemma coe_modulusScalar {N : ℕ} {L : Length} (u : ScalarL2 N L) :
    modulusScalar u =ᵐ[volume] fun X ↦ (‖u X‖ : ℂ) :=
  modulus_lipschitz.coeFn_compLp (by simp) u

lemma modulusCoefficient_meas {N : ℕ} {L : Length} (u : ScalarL2 N L) :
    AEStronglyMeasurable (fun X ↦ differential 0 (u X)) volume := by
  apply aestronglyMeasurable_of_tendsto_ae atTop (f := fun n X ↦
    differential (regularizationScale n) (u X))
  · intro n
    have he : differential (regularizationScale n) =
        fderiv ℝ (regularize (regularizationScale n)) :=
      funext fun z ↦ (fderiv_eq (regularizationScale_pos n) z).symm
    rw [he]
    exact ((smooth (regularizationScale_pos n)).continuous_fderiv (by simp)).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable u)
  · exact Eventually.of_forall fun X ↦ tendsto_differential (u X) tendsto_regularizationScale

def modulusPartial {N : ℕ} {L : Length} (u v : ScalarL2 N L) : ScalarL2 N L :=
  L2Contraction.fieldApply (fun X ↦ differential 0 (u X)) (modulusCoefficient_meas u)
    (Eventually.of_forall fun X ↦ differential_le 0 (u X)) v

def modulusJet {N : ℕ} {L : Length} (u : Jet N L) : Jet N L :=
  (modulusScalar u.1, fun p ↦ modulusPartial u.1 (u.2 p))

lemma coe_modulusPartial {N : ℕ} {L : Length} (u v : ScalarL2 N L) :
    modulusPartial u v =ᵐ[volume] fun X ↦ differential 0 (u X) (v X) :=
  L2Contraction.coe_fieldApply _ _ _ v

lemma tendsto_regularization_partial {N : ℕ} {L : Length} (u v : ScalarL2 N L) :
    Tendsto (fun n ↦ (regularization (regularizationScale n) (regularizationScale_pos n)).onPartial u v)
      atTop (𝓝 (modulusPartial u v)) := by
  refine L2Contraction.tendsto_toLp_of_domination
    (fun n ↦ L2Contraction.field_memLp _
      (L2Contraction.coeff_meas _ (regularization _ (regularizationScale_pos n)).derivative_continuous u)
      (Eventually.of_forall fun X ↦ (regularization _ (regularizationScale_pos n)).derivative_le (u X)) v)
    (L2Contraction.field_memLp _ (modulusCoefficient_meas u)
      (Eventually.of_forall fun X ↦ differential_le 0 (u X)) v)
    (Lp.memLp v) ?_ ?_
  · intro n
    apply Eventually.of_forall
    intro X
    change ‖fderiv ℝ (regularize (regularizationScale n)) (u X) (v X)‖ ≤ ‖v X‖
    rw [fderiv_eq (regularizationScale_pos n)]
    exact differential_apply_le _ _ _
  · apply Eventually.of_forall
    intro X
    change Tendsto (fun n ↦ fderiv ℝ (regularize (regularizationScale n)) (u X) (v X))
      atTop (𝓝 (differential 0 (u X) (v X)))
    simp only [fderiv_eq (regularizationScale_pos _)]
    exact ((ContinuousLinearMap.apply ℝ ℂ (v X)).continuous.tendsto _).comp
      (tendsto_differential (u X) tendsto_regularizationScale)

lemma tendsto_regularization_scalar {N : ℕ} {L : Length} (u : ScalarL2 N L) :
    Tendsto (fun n ↦ (regularization (regularizationScale n) (regularizationScale_pos n)).onScalar u)
      atTop (𝓝 (modulusScalar u)) := by
  have he (f : ℂ → ℂ) (hf : LipschitzWith 1 f) (h0 : f 0 = 0) :
      hf.compLp h0 u = (hf.comp_memLp h0 (Lp.memLp u)).toLp (f ∘ u) := by
    apply Lp.ext
    exact (hf.coeFn_compLp h0 u).trans (MemLp.coeFn_toLp _).symm
  simp only [SmoothContraction.onScalar, modulusScalar, he]
  refine L2Contraction.tendsto_toLp_of_domination
    (fun n ↦ (regularization _ (regularizationScale_pos n)).lipschitz.comp_memLp
      (regularization _ (regularizationScale_pos n)).zero (Lp.memLp u))
    (modulus_lipschitz.comp_memLp (by simp) (Lp.memLp u)) (Lp.memLp u) ?_ ?_
  · intro n
    apply Eventually.of_forall
    intro X
    have h := (regularization (regularizationScale n) (regularizationScale_pos n)).lipschitz.norm_sub_le
      (u X) 0
    simpa only [SmoothContraction.zero, sub_zero, NNReal.coe_one, one_mul, Function.comp_apply] using h
  · exact Eventually.of_forall fun X ↦ tendsto_regularize (u X) tendsto_regularizationScale

lemma tendsto_regularization_jet {N : ℕ} {L : Length} (u : Jet N L) :
    Tendsto (fun n ↦ (regularization (regularizationScale n) (regularizationScale_pos n)).onJet u)
      atTop (𝓝 (modulusJet u)) :=
  (tendsto_regularization_scalar u.1).prodMk_nhds
    (tendsto_pi_nhds.mpr fun p ↦ tendsto_regularization_partial u.1 (u.2 p))

lemma modulusJet_mem_domain {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : u ∈ dirichletDomain N L a) : modulusJet u ∈ dirichletDomain N L a :=
  isClosed_closure.mem_of_tendsto (tendsto_regularization_jet u)
    (Eventually.of_forall fun n ↦
      (regularization (regularizationScale n) (regularizationScale_pos n)).onJet_mem_domain hu)

lemma norm_modulusScalar {N : ℕ} {L : Length} (u : ScalarL2 N L) :
    ‖modulusScalar u‖ = ‖u‖ := by
  have he : ∀ᵐ X ∂volume, ‖modulusScalar u X‖ = ‖u X‖ := by
    filter_upwards [coe_modulusScalar u] with X hX
    simp [hX]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono fun _ hx ↦ hx.le))
    (Lp.norm_le_norm_of_ae_le (he.mono fun _ hx ↦ hx.ge))

lemma energy_modulusJet_le {N : ℕ} {L : Length} (u : Jet N L) :
    energy (modulusJet u) ≤ energy u := by
  apply Finset.sum_le_sum
  intro p _
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  exact L2Contraction.norm_fieldApply_le _ (modulusCoefficient_meas u.1)
    (Eventually.of_forall fun X ↦ differential_le 0 (u.1 X)) (u.2 p)

lemma bosonic_modulusScalar {N : ℕ} {L : Length} {u : ScalarL2 N L}
    (hu : bosonic u) : bosonic (modulusScalar u) := by
  intro σ
  have hp : MeasurePreserving (fun X : Configuration N L ↦ fun i ↦ X (σ i)) volume volume := by
    have h := volume_measurePreserving_piCongrLeft (fun _ : Fin N ↦ Torus L) σ.symm
    convert h using 1
    funext X i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have hae := hp.quasiMeasurePreserving.ae_eq_comp (coe_modulusScalar u)
  filter_upwards [hae, coe_modulusScalar u, hu σ] with X h1 h2 h3
  change modulusScalar u (fun i ↦ X (σ i)) = (‖u (fun i ↦ X (σ i))‖ : ℂ) at h1
  rw [h1, h2, h3]

lemma IsGroundVector.modulus {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) : IsGroundVector N L a (modulusJet u) := by
  refine ⟨modulusJet_mem_domain hu.1, bosonic_modulusScalar hu.2.1, ?_, ?_⟩
  · exact (norm_modulusScalar u.1).trans hu.2.2.1
  · intro v hv hb hn
    exact (energy_modulusJet_le u).trans (hu.2.2.2 v hv hb hn)

lemma IsGroundVector.energy_modulus {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) : energy (modulusJet u) = energy u :=
  le_antisymm (energy_modulusJet_le u)
    (hu.2.2.2 _ hu.modulus.1 hu.modulus.2.1 hu.modulus.2.2.1)

end HardSphere

end
end
end

end OAI
