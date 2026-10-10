import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.CriticalRescale
import OAI.Geometry.TamingCompatibility.Elliptic.SobolevBounded

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
local instance : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩

lemma schwartzToH_zero (f : 𝓢(E,F)) : schwartzToH 0 f = f.toLp 2 (volume : Measure E) := by
  simp [schwartzToH]

lemma schwartzToH_inclusion {s t : ℝ} (h : t ≤ s) (f : 𝓢(E,F)) :
    inclusion h (schwartzToH s f) = schwartzToH t f := by
  apply toDistribution_injective t
  rw [toDistribution_inclusion,schwartzToH_spec,schwartzToH_spec]

lemma schwartz_H1_norm_le (f : 𝓢(E,F)) :
    ‖schwartzToH 1 f‖ ≤ ‖f.toLp 2 (volume : Measure E)‖ +
      |((2*Real.pi)^2)⁻¹| * ∑ i, ‖derivative (F := F) 0 (stdOrthonormalBasis ℝ E i)‖ *
        ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖ := by
  have h := norm_le_gradient 0 (schwartzToH (0+1) f)
  have h₀ : inclusion (s := (0+1:ℝ)) (t := (0:ℝ)) (by norm_num) (schwartzToH (0+1) f) =
      f.toLp 2 (volume : Measure E) :=
    (schwartzToH_inclusion (s := 0+1) (t := 0) (by norm_num) f).trans (schwartzToH_zero f)
  have hd (i : basisIndex E) : derivative (0+1) (stdOrthonormalBasis ℝ E i) (schwartzToH (0+1) f) =
      (∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E) := by
    have h' := schwartzToH_derivative (0+1) (stdOrthonormalBasis ℝ E i) f
    have hz : (0:ℝ)+1-1 = 0 := by ring
    rw [hz] at h'
    exact h'.symm.trans (schwartzToH_zero _)
  rw [h₀] at h
  simp only [hd] at h
  have he : schwartzToH (E := E) (F := F) (0+1) f = schwartzToH 1 f :=
    congrArg (fun s : ℝ => schwartzToH s f) (zero_add 1)
  exact (congrArg norm he).symm.le.trans h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma schwartz_derivative_smul (g : 𝓢(E,ℂ)) (f : 𝓢(E,F)) (v : E) :
    ∂_{v} (SchwartzMap.smulLeftCLM F g f) =
      SchwartzMap.smulLeftCLM F (∂_{v} g : 𝓢(E,ℂ)) f +
      SchwartzMap.smulLeftCLM F g (∂_{v} f) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,add_apply]
  have he : (SchwartzMap.smulLeftCLM F g f : E → F) = (⇑g • ⇑f) := by
    ext y; simp [g.hasTemperateGrowth]
  rw [he,fderiv_smul g.differentiableAt f.differentiableAt]
  simp [g.hasTemperateGrowth,(∂_{v} g : 𝓢(E,ℂ)).hasTemperateGrowth,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,add_comm]

omit [CompleteSpace F] in
lemma cutoff_rescale_derivative_L2 (hdim : Module.finrank ℝ E = 4)
    (χ : 𝓢(E,ℂ)) (p : E) {r : ℝ} (hr : 0 < r) (f : 𝓢(E,F)) (v : E) :
    ‖(∂_{v} (SchwartzMap.smulLeftCLM F χ (rescaleSchwartz p r hr.ne' f))).toLp
      2 (volume : Measure E)‖ ≤ r⁻¹ *
      (‖(∂_{v} χ).toLp 4 (volume : Measure E)‖ * ‖f.toLp 4 (volume : Measure E)‖ +
      SchwartzMap.seminorm ℂ 0 0 χ * ‖(∂_{v} f).toLp 2 (volume : Measure E)‖) := by
  rw [schwartz_derivative_smul,rescaleSchwartz_derivative]
  have he : SchwartzMap.smulLeftCLM F χ (r • rescaleSchwartz p r hr.ne' (∂_{v} f)) =
      r • SchwartzMap.smulLeftCLM F χ (rescaleSchwartz p r hr.ne' (∂_{v} f)) := by
    exact (SchwartzMap.smulLeftCLM F χ).map_smul_of_tower r _
  rw [he]
  change ‖(SchwartzMap.toLpCLM ℂ F 2 (volume : Measure E)) (_ + r • _)‖ ≤ _
  rw [map_add,ContinuousLinearMap.map_smul_of_tower]
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  have h₀ := schwartz_cutoff_L2_L4 (∂_{v} χ) (rescaleSchwartz p r hr.ne' f)
  have h₁ := schwartz_cutoff_L2_L2 χ (rescaleSchwartz p r hr.ne' (∂_{v} f))
  rw [rescaleSchwartz_L4 hdim p hr] at h₀
  rw [rescaleSchwartz_L2 hdim p hr] at h₁
  apply (add_le_add h₀ (mul_le_mul_of_nonneg_left h₁ hr.le)).trans_eq
  field_simp

theorem cutoff_rescale_H1 (hdim : Module.finrank ℝ E = 4) (χ : 𝓢(E,ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : E) (r : ℝ) (hr : 0 < r) (f : 𝓢(E,F)),
      ‖schwartzToH 1 (SchwartzMap.smulLeftCLM F χ (rescaleSchwartz p r hr.ne' f))‖ ≤
        C * r⁻¹ * (‖f.toLp 4 (volume : Measure E)‖ +
          ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖) := by
  classical
  let D := fun i : basisIndex E => ‖derivative (F := F) 0 (stdOrthonormalBasis ℝ E i)‖
  let K := |((2*Real.pi)^2)⁻¹|
  let A := ‖χ.toLp 4 (volume : Measure E)‖
  let B := fun i : basisIndex E => ‖(∂_{stdOrthonormalBasis ℝ E i} χ).toLp 4 (volume : Measure E)‖
  let T := SchwartzMap.seminorm ℂ 0 0 χ
  have hK : 0 ≤ K := abs_nonneg _
  have hT : 0 ≤ T := apply_nonneg _ _
  refine ⟨A + K * ∑ i, D i * (B i + T),by positivity,?_⟩
  intro p r hr f
  let S := ‖f.toLp 4 (volume : Measure E)‖ +
    ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖
  have hf : ‖f.toLp 4 (volume : Measure E)‖ ≤ S :=
    le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hd (i : basisIndex E) : ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖ ≤ S := by
    have ht := Finset.single_le_sum (fun j _ => norm_nonneg ((∂_{stdOrthonormalBasis ℝ E j} f).toLp 2 (volume : Measure E)))
      (Finset.mem_univ i)
    dsimp only [S]
    linarith [norm_nonneg (f.toLp 4 (volume : Measure E))]
  apply (schwartz_H1_norm_le _).trans
  have h₀ := schwartz_cutoff_L2_L4 χ (rescaleSchwartz p r hr.ne' f)
  rw [rescaleSchwartz_L4 hdim p hr] at h₀
  have h₁ (i : basisIndex E) := cutoff_rescale_derivative_L2 hdim χ p hr f (stdOrthonormalBasis ℝ E i)
  calc
    _ ≤ A * (r⁻¹ * ‖f.toLp 4 (volume : Measure E)‖) +
        K * ∑ i, D i * (r⁻¹ * (B i * ‖f.toLp 4 (volume : Measure E)‖ +
          T * ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖)) := by
      apply add_le_add h₀
      apply mul_le_mul_of_nonneg_left _ hK
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h₁ i) (norm_nonneg _))
    _ ≤ A * (r⁻¹ * S) + K * ∑ i, D i * (r⁻¹ * (B i * S + T * S)) := by
      gcongr with i
      exact hd i
    _ = _ := by
      change A * (r⁻¹ * S) + K * ∑ i, D i * (r⁻¹ * (B i * S + T * S)) =
        (A + K * ∑ i, D i * (B i + T)) * r⁻¹ * S
      simp only [← add_mul]
      simp_rw [show ∀ i, D i * (r⁻¹ * ((B i + T) * S)) = D i * (B i + T) * r⁻¹ * S by intro i; ring]
      rw [← Finset.sum_mul,← Finset.sum_mul]
      ring
end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.CriticalSobolev
open MeasureTheory
open scoped SchwartzMap ENNReal NNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma opNorm_le_sum_basis (L : E →L[ℝ] F) :
    ‖L‖ ≤ ∑ i, ‖L (stdOrthonormalBasis ℝ E i)‖ := by
  classical
  let b := stdOrthonormalBasis ℝ E
  apply L.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro x
  calc
    ‖L x‖ = ‖∑ i, (b.repr x i) • L (b i)‖ := by
      conv_lhs => rw [← b.sum_repr x]
      rw [map_sum]
      simp only [map_smul]
    _ ≤ ∑ i, ‖(b.repr x i) • L (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖x‖ * ‖L (b i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      have hi : ‖b.repr x i‖ ≤ ‖x‖ := by
        simpa only [LinearIsometryEquiv.norm_map] using PiLp.norm_apply_le (b.repr x) i
      exact mul_le_mul_of_nonneg_right hi (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; exact mul_comm _ _
end TamingCompatibility.CriticalSobolev

namespace TamingCompatibility.ScalarPair
open MeasureTheory ManifoldLocalization LineDeriv
open scoped SchwartzMap ENNReal NNReal LineDeriv

lemma critical_sobolev_jet : ∃ C : ℝ, 0 ≤ C ∧
    ∀ u : 𝓢(Space,F), HasCompactSupport u →
      ‖u.toLp 4 (volume : Measure Space)‖ ≤ C * ‖jet u‖ := by
  let c := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2
  refine ⟨(c:ℝ)*4,by positivity,fun u hu => ?_⟩
  let du (i : Fin (Module.finrank ℝ Space)) :=
    lineDerivOpCLM ℝ 𝓢(Space,F) (stdOrthonormalBasis ℝ Space i) u
  have hd : eLpNorm (fderiv ℝ u) 2 (volume : Measure Space) ≤
      ∑ i, eLpNorm (du i) 2 volume := by
    calc
      eLpNorm (fderiv ℝ u) 2 volume ≤
          eLpNorm (fun x => ∑ i, ‖du i x‖) 2 volume := by
        apply eLpNorm_mono_ae_real
          ((u.smooth 1).continuous_fderiv (by norm_num)).aestronglyMeasurable
        exact Filter.Eventually.of_forall (fun x => by
          simpa only [du,LineDeriv.lineDerivOpCLM_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv] using
            CriticalSobolev.opNorm_le_sum_basis (fderiv ℝ u x))
      _ ≤ ∑ i, eLpNorm (fun x => ‖du i x‖) 2 volume := by
        simpa only [Finset.sum_fn] using eLpNorm_sum_le (μ := (volume : Measure Space))
          (f := fun index x => ‖du index x‖)
          (by norm_num : (1:ℝ≥0∞) ≤ 2)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro index _
        exact eLpNorm_norm _ ((du index).memLp 2 volume).aestronglyMeasurable
  have hj (i : Fin (Module.finrank ℝ Space)) :
      eLpNorm (du i) 2 volume ≤ ENNReal.ofReal ‖jet u‖ := by
    have hi : ‖(du i).toLp 2 (volume : Measure Space)‖ ≤ ‖jet u‖ := by
      exact PiLp.norm_apply_le (jet u) (some i)
    rw [SchwartzMap.norm_toLp] at hi
    rw [← ENNReal.ofReal_toReal ((du i).memLp 2 volume).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hi
  have hsum : (∑ i, eLpNorm (du i) 2 volume) ≤ 4 * ENNReal.ofReal ‖jet u‖ := by
    calc
      _ ≤ ∑ _i : Fin (Module.finrank ℝ Space), ENNReal.ofReal ‖jet u‖ :=
        Finset.sum_le_sum (fun i _ => hj i)
      _ = _ := by simp [Space]
  have hgns := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure Space)
    (u.smooth 1) hu
    (p := (2:ℝ≥0)) (p' := (4:ℝ≥0)) (by norm_num)
    (by simp [Space]) (by norm_num [Space])
  have hb : eLpNorm u 4 volume ≤ (c:ℝ≥0∞) * (4 * ENNReal.ofReal ‖jet u‖) :=
    hgns.trans (mul_le_mul_of_nonneg_left (hd.trans hsum) (zero_le))
  have hr := ENNReal.toReal_mono (by finiteness) hb
  simpa only [SchwartzMap.norm_toLp,ENNReal.toReal_mul,ENNReal.coe_toReal,
    ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (norm_nonneg _),mul_assoc] using hr
end TamingCompatibility.ScalarPair

end
end

end
end
end

end OAI
