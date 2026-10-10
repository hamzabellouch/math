import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.CriticalRescaleH1

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv ENNReal NNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
local instance : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩

lemma schwartz_derivative_L2_H1 (f : 𝓢(E,F)) (v : E) :
    ‖(∂_{v} f).toLp 2 (volume : Measure E)‖ ≤ ‖derivative (F := F) 1 v‖ * ‖schwartzToH 1 f‖ := by
  have h := (derivative (F := F) 1 v).le_opNorm (schwartzToH 1 f)
  rw [← schwartzToH_derivative] at h
  rw [show (1:ℝ)-1=0 by ring] at h
  simpa only [schwartzToH_zero] using h

lemma critical_norm_H1 (hdim : Module.finrank ℝ E = 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(E,F), HasCompactSupport f →
      ‖f.toLp 4 (volume : Measure E)‖ +
        ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖ ≤
          C * ‖schwartzToH 1 f‖ := by
  classical
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  let c := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure E) 2
  let D := ∑ i, ‖derivative (F := F) 1 (stdOrthonormalBasis ℝ E i)‖
  refine ⟨((c:ℝ)+1)*D,by dsimp only [D]; positivity,fun f hf => ?_⟩
  have hd : eLpNorm (fderiv ℝ f) 2 (volume : Measure E) ≤
      ∑ i, eLpNorm (∂_{stdOrthonormalBasis ℝ E i} f : 𝓢(E,F)) 2 volume := by
    calc
      _ ≤ eLpNorm (fun x => ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} f : 𝓢(E,F)) x‖) 2 volume := by
        apply eLpNorm_mono_ae_real
          ((f.smooth 1).continuous_fderiv (by norm_num)).aestronglyMeasurable
        exact Filter.Eventually.of_forall (fun x => by
          simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using
            CriticalSobolev.opNorm_le_sum_basis (fderiv ℝ f x))
      _ ≤ ∑ i, eLpNorm (fun x => ‖(∂_{stdOrthonormalBasis ℝ E i} f : 𝓢(E,F)) x‖) 2 volume := by
        simpa only [Finset.sum_fn] using eLpNorm_sum_le (μ := (volume : Measure E))
          (f := fun index point => ‖(∂_{stdOrthonormalBasis ℝ E index} f : 𝓢(E,F)) point‖)
          (by norm_num : (1:ℝ≥0∞) ≤ 2)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro index _
        exact eLpNorm_norm _
          ((∂_{stdOrthonormalBasis ℝ E index} f : 𝓢(E,F)).memLp 2 volume).aestronglyMeasurable
  have hgns := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure E)
    (f.smooth 1) hf (p := (2:ℝ≥0)) (p' := (4:ℝ≥0)) (by norm_num)
    (by rw [hdim]; norm_num) (by rw [hdim]; norm_num)
  have hh := hgns.trans (mul_le_mul_of_nonneg_left hd (zero_le))
  have he : (∑ i, eLpNorm (∂_{stdOrthonormalBasis ℝ E i} f : 𝓢(E,F)) 2 volume) ≠ ∞ := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ((∂_{stdOrthonormalBasis ℝ E i} f : 𝓢(E,F)).memLp 2 volume).eLpNorm_ne_top
  have ht := ENNReal.toReal_mono (by finiteness) hh
  rw [ENNReal.toReal_mul,ENNReal.coe_toReal,ENNReal.toReal_sum (fun i _ =>
    ((∂_{stdOrthonormalBasis ℝ E i} f : 𝓢(E,F)).memLp 2 volume).eLpNorm_ne_top)] at ht
  have hb : (∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖) ≤
      D * ‖schwartzToH 1 f‖ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => schwartz_derivative_L2_H1 f _)
  have h₄ : ‖f.toLp 4 (volume : Measure E)‖ ≤
      (c:ℝ) * ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖ := by
    simpa [SchwartzMap.norm_toLp,c] using ht
  calc
    _ ≤ ((c:ℝ)+1) * ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖ := by linarith
    _ ≤ ((c:ℝ)+1) * (D * ‖schwartzToH 1 f‖) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

def linearH (n : ℕ) (L : E ≃L[ℝ] E) : H E F n →L[ℂ] H E F n :=
  liftOperator (linearDistribution L) (fun _ h => memSobolev_nat_linear n L h)

lemma linearH_spec (n : ℕ) (L : E ≃L[ℝ] E) (u : H E F n) :
    toDistribution E F n (linearH n L u) = linearDistribution L (toDistribution E F n u) :=
  toDistribution_liftOperator _ _ _

lemma linearH_schwartz (n : ℕ) (L : E ≃L[ℝ] E) (f : 𝓢(E,F)) :
    linearH n L (schwartzToH n f) =
      |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹| •
        schwartzToH n (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f) := by
  apply toDistribution_injective n
  rw [linearH_spec,schwartzToH_spec,ContinuousLinearMap.map_smul_of_tower,
    schwartzToH_spec,linearDistribution_schwartz]
  exact ContinuousLinearMap.map_smul_of_tower _ _ _

lemma linear_schwartz_H_bound (n : ℕ) (L : E ≃L[ℝ] E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : 𝓢(E,F),
      ‖schwartzToH n (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f)‖ ≤
        K * ‖schwartzToH n f‖ := by
  let d := |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹|
  have hd : 0 < d := abs_pos.mpr (inv_ne_zero L.toLinearEquiv.isUnit_det'.ne_zero)
  refine ⟨d⁻¹ * ‖linearH (F := F) n L‖,by positivity,fun f => ?_⟩
  have h := (linearH (F := F) n L).le_opNorm (schwartzToH n f)
  rw [linearH_schwartz,norm_smul,Real.norm_eq_abs,abs_abs] at h
  have hb := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hd.le)
  change d⁻¹ * (d * _) ≤ _ at hb
  simpa only [← mul_assoc,inv_mul_cancel₀ hd.ne',one_mul] using hb
end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv ENNReal NNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
local instance : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩

lemma critical_linear_H1 (hdim : Module.finrank ℝ E = 4) (L : E ≃L[ℝ] E) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : 𝓢(E,F), HasCompactSupport f →
      let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f
      ‖u.toLp 4 (volume : Measure E)‖ +
        ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖ ≤
          B * ‖schwartzToH 1 f‖ := by
  obtain ⟨C,hC,hbound⟩ := critical_norm_H1 (F := F) hdim
  obtain ⟨B,hB,hlinear⟩ := linear_schwartz_H_bound (F := F) 1 L
  refine ⟨C*B,mul_nonneg hC hB,fun f hf => ?_⟩
  dsimp only
  have hc := hf.comp_homeomorph L.symm.toHomeomorph
  apply (hbound (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f) hc).trans
  have hb := hlinear f
  simpa only [schwartzToH,Nat.cast_one] using
    (mul_le_mul_of_nonneg_left hb hC).trans_eq (mul_assoc _ _ _).symm
end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv Set Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem normalized_scalar_uniform_regular {ι κ : Type*} [Fintype ι] [Fintype κ]
    {U : Set E} (hU : IsOpen U) (p : E) (hp : p ∈ U)
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hgp : ∀ i j, g i j p = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) :
    ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ ∀ (n : ℕ) (u : 𝓢'(E,F)),
      MemSobolevLoc U 1 u → MemSobolevLoc U n
        (-directionalPrincipal (stdOrthonormalBasis ℝ E) g u + matrixLowerOrder b L v c K u) →
      MemSobolevLoc V ((n:ℝ)+2) u := by
  obtain ⟨χ,hχ,hχone⟩ := exists_unit_cutoff (E := E)
  obtain ⟨r,hr,hweak,hstrong⟩ := exists_small_frozen_scale (F := F) χ hχ g p
  have hr0 : r ≠ 0 := ne_of_gt hr
  let W : Set E := (fun y => r • y+p) ⁻¹' U ∩ Metric.ball 0 1
  have hW : IsOpen W := (hU.preimage (by fun_prop)).inter Metric.isOpen_ball
  have h0W : (0 : E) ∈ W := by simpa only [W,mem_inter_iff,mem_preimage,smul_zero,zero_add,
    Metric.mem_ball,dist_self] using And.intro hp (show (0 : ℝ) < 1 by norm_num)
  let a := frozenPrincipal χ hχ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p r
  let B := fun i => r • affineSchwartz p r hr0 (b i)
  let C := fun i => (r*r) • affineSchwartz p r hr0 (c i)
  let V : Set E := (fun y => r⁻¹ • y + -(r⁻¹ • p)) ⁻¹' W
  have hV : IsOpen V := hW.preimage (by fun_prop)
  have hpV : p ∈ V := by
    change r⁻¹ • p + -(r⁻¹ • p) ∈ W
    simpa only [add_neg_cancel] using h0W
  have hVU : V ⊆ U := by
    intro x hx
    have h := hx.1
    change r • (r⁻¹ • x + -(r⁻¹ • p))+p ∈ U at h
    simpa only [smul_add,smul_neg,smul_smul,mul_inv_cancel₀ hr0,one_smul,neg_add_cancel_right] using h
  refine ⟨V,hV,hpV,hVU,?_⟩
  intro n u hu hf
  let z := zoomDistribution p r hr0 u
  have hz : MemSobolevLoc W 1 z := by
    exact (memSobolevLoc_zoom_one p r hr0 hu).restrict inter_subset_left
  have hsource : MemSobolevLoc W n
      (perturbedHelmholtz a z + matrixLowerOrder B L v
        (Sum.elim C (fun _ : Unit => -χ))
        (Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F)) z) := by
    intro ψ hψ hψW
    have hpψ : ∀ x ∈ tsupport ψ, χ x = 1 := fun x hx => hχone x (hψW hx).2
    have h := (memSobolevLoc_zoom n p r hr0 hf).real_smul (r*r) ψ hψ
      (fun x hx => (hψW hx).1)
    rw [rescaled_system] at h
    rw [local_frozen_system χ hχ g p hgp r hr0 ψ hpψ B L v C K z]
    exact h
  have hzreg : MemSobolevLoc W ((n:ℝ)+2) z :=
    matrix_H1_interior_bootstrap n hW a hweak hstrong B L v
      (Sum.elim C (fun _ : Unit => -χ))
      (Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F)) hz hsource
  have hzreg' : MemSobolevLoc W ((n+2 : ℕ) : ℝ) z := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hzreg
  have h := memSobolevLoc_affine (n+2) p r hr0 hzreg'
  rw [zoomDistribution_inverse] at h
  simpa only [Nat.cast_add,Nat.cast_ofNat] using h

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
