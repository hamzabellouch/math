import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalParameterLogJets
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralParameterShear

namespace OAI

/-! The physical parameter shear costs an arbitrarily small positive exponent. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem HasLogJetBound.identity (σ : ℝ) (hσ : 0 < σ) :
    HasLogJetBound σ (fun t : ℝ => t) := by
  refine ⟨⟨0,contDiffOn_id⟩,?_⟩
  intro k
  by_cases hk : k=0
  · subst k
    refine ⟨σ⁻¹,inv_nonneg.mpr hσ.le,?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp only [iteratedDeriv_zero,Real.norm_eq_abs,abs_of_nonneg ht]
    have hh : σ*t ≤ Real.exp (σ*t) := by linarith [Real.add_one_le_exp (σ*t)]
    calc
      t = σ⁻¹*(σ*t) := by field_simp
      _ ≤ σ⁻¹*Real.exp (σ*t) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hσ.le)
  · by_cases hk₁ : k=1
    · subst k
      refine ⟨1,zero_le_one,?_⟩
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      simpa only [iteratedDeriv_fun_id,ite_false,ite_true,one_ne_zero,norm_one,one_mul] using
        (Real.one_le_exp_iff.mpr (mul_nonneg hσ.le ht))
    · refine ⟨0,le_rfl,Filter.Eventually.of_forall ?_⟩
      intro t
      simp only [iteratedDeriv_fun_id,hk,hk₁,ite_false,norm_zero,zero_mul,le_refl]

theorem HasLogJetBound.parameterShear {f g : ℝ → ℂ}
    (hf : HasLogJetBound 0 f) (hg : HasLogJetBound 0 g)
    (σ : ℝ) (hσ : 0 < σ) :
    HasLogJetBound σ (fun t => f t-2*(t : ℂ)*g t) := by
  have hid : HasLogJetBound σ (fun t : ℝ => (t : ℂ)) :=
    (HasLogJetBound.identity σ hσ).map Complex.ofRealCLM
  have hmul : HasLogJetBound σ (fun t => 2*(t : ℂ)*g t) := by
    simpa only [add_zero] using (hid.const_mul 2).mul hg
  exact (hf.mono hσ.le).sub hmul

theorem homogeneousNormalizedEuler_bound_order (ν : ℂ) (f : ℝ → ℂ) (σ : ℝ)
    (hf : HasLogJetBound σ f) (n : ℕ) :
    HasLogJetBound σ (homogeneousNormalizedEuler ν f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.deriv.add (ih.const_mul _)

theorem canonical_parameterShear_value_logJets (ν η b : ℂ) (n : ℕ) (hn : 1≤n)
    (L : ℝ) (hX : HasRadialExterior ν n b L) (hb : b ≠ 0)
    (c : ℂ × ℂ) (Y : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn ν η b n L c Y) (z : ℂ)
    (σ : ℝ) (hσ : 0 < σ) :
    HasLogJetBound σ (fun t =>
      (circularParameterShear t (Y z t) (deriv (fun lam => Y lam t) z)).1.1) ∧
    HasLogJetBound σ (fun t =>
      (circularParameterShear t (Y z t) (deriv (fun lam => Y lam t) z)).2.1) := by
  have hD := canonical_circular_parameter_logJets ν η b n hn L hX hb c Y hY z
  have hV := homogeneous_canonical_circular_value_logJets ν (ν-2*z) (star ν-2*z)
    η b n L hX (Y z) c (hY.1 z) (hY.2.1 z) (hY.2.2.2 z)
  simpa only [circularParameterShear,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,
    smul_eq_mul,sub_zero] using
    And.intro (hD.1.parameterShear hV.1 σ hσ) (hD.2.parameterShear hV.2 σ hσ)

end DefocusingNLS

end OAI
