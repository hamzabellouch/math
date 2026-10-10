import OAI.Analysis.AncientFlat.Evolution.MovingSource
import OAI.Analysis.AncientFlat.Evolution.SemigroupNormalize

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ZeroAtInfty BoundedContinuousFunction Topology
namespace FlatSimilarity
open ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V]
lemma continuous_normalizedSource (γ a : ℝ) (f : ℝ →ᵇ C₀(V,ℂ)) :
    Continuous (fun t => (Real.exp (-γ*unitClamp t) : ℂ) • f (a+unitClamp t)) := by
  exact (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul unitClamp_lipschitz.continuous))).smul
    (f.continuous.comp (continuous_const.add unitClamp_lipschitz.continuous))
def normalizedSource (γ a : ℝ) (hγ : 0≤γ) (f : ℝ →ᵇ C₀(V,ℂ)) : ℝ →ᵇ C₀(V,ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => (Real.exp (-γ*unitClamp t) : ℂ) • f (a+unitClamp t))
    (continuous_normalizedSource γ a f) ‖f‖ (fun t => by
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-γ*unitClamp t)≤1 := Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) (unitClamp_mem t).1)
      exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans
        (by simpa using f.norm_coe_le_norm (a+unitClamp t)))
@[simp] lemma normalizedSource_apply (γ a : ℝ) (hγ : 0≤γ) (f : ℝ →ᵇ C₀(V,ℂ))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    normalizedSource γ a hγ f t=(Real.exp (-γ*t) : ℂ) • f (a+t) := by
  change (Real.exp (-γ*unitClamp t) : ℂ) • f (a+unitClamp t)=_
  rw [unitClamp_eq ht]
lemma normalizedSource_holder (γ a η : ℝ) (hγ : 0≤γ) (f : ℝ →ᵇ C₀(V,ℂ))
    (hf : ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc a (a+1), ∀ x y, ‖f t x-f t y‖≤H*‖x-y‖^η) :
    ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ x y,
      ‖normalizedSource γ a hγ f t x-normalizedSource γ a hγ f t y‖≤H*‖x-y‖^η := by
  obtain ⟨H,hH,hf⟩ := hf
  refine ⟨H,hH,fun t ht x y => ?_⟩
  rw [normalizedSource_apply γ a hγ f ht]
  change ‖(Real.exp (-γ*t) : ℂ) • f (a+t) x-(Real.exp (-γ*t) : ℂ) • f (a+t) y‖≤_
  rw [←smul_sub,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-γ*t)≤1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) ht.1)
  exact ((mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq (one_mul _)).trans
    (hf _ ⟨by linarith [ht.1],by linarith [ht.2]⟩ x y)
end FlatSimilarity
namespace AncientMild
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma unnormalize_duhamel (γ : ℝ) (S : ℝ → E →L[ℂ] E) (f v : ℝ → E) (a t : ℝ)
    (hv : v (a+t)=(Real.exp (γ*t) : ℂ) • S t (v a)+
      ∫ s in (0:ℝ)..t, (Real.exp (γ*(t-s)) : ℂ) • S (t-s) (f (a+s))) :
    (Real.exp (-γ*t) : ℂ) • v (a+t)=S t (v a)+
      ∫ s in (0:ℝ)..t, S (t-s) ((Real.exp (-γ*s) : ℂ) • f (a+s)) := by
  rw [hv,smul_add,smul_smul,←Complex.ofReal_mul,←Real.exp_add,
    show -γ*t+γ*t=0 by ring,Real.exp_zero,Complex.ofReal_one,one_smul,
    ←intervalIntegral.integral_smul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [map_smul,smul_smul,←Complex.ofReal_mul,←Real.exp_add]
  congr 2
  ring_nf
end AncientMild

end

end OAI
