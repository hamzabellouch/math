import OAI.NumberTheory.JointDickman.Amplification.MultiplicityRates

namespace OAI

/-! # Quantitative lower-tail exponent with a perturbed prefix mean -/

namespace JointDickman

/-- The only mean hypothesis is an explicit numerical lower bound. In the
application it comes from `tilted_prefix_mean_uniform`, which uses the
published reciprocal-prime Mertens input. -/
theorem multiplicity_chernoff_exponent {g ℓ ω m τ ε δ r : ℝ}
    (hg : 0 ≤ g) (hℓ : 0 ≤ ℓ) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hr : 0 ≤ r) (hr1 : r ≤ 1/2)
    (hω : g*r*ℓ ≤ ω) (hm : (g/2-ε)*ℓ ≤ m) :
    let t := -Real.log (2*max δ (1/2-r))
    t*((g/2+τ)*ℓ-ω)+(Real.exp (-t)-1)*m ≤
      (-g*halfPoissonRate (1/2-r)+g*δ+(-Real.log (2*δ))*τ+ε)*ℓ := by
  let t := -Real.log (2*max δ (1/2-r))
  obtain ⟨ht,htop,hrate⟩ := halfPoisson_clamped_chernoff (u := 1/2-r) (by linarith)
    (by linarith) hδ hδ1
  change 0 ≤ t at ht
  change t ≤ -Real.log (2*δ) at htop
  change t*(1/2-r)+(Real.exp (-t)-1)/2 ≤ -halfPoissonRate (1/2-r)+δ at hrate
  have he0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have he1 : Real.exp (-t) ≤ 1 := by
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hfirst : t*((g/2+τ)*ℓ-ω) ≤ t*(g*(1/2-r)*ℓ+τ*ℓ) := by
    apply mul_le_mul_of_nonneg_left _ ht
    nlinarith
  have hsecond : (Real.exp (-t)-1)*m ≤
      (Real.exp (-t)-1)*(g/2*ℓ)+ε*ℓ := by
    have hh := mul_le_mul_of_nonpos_left hm (sub_nonpos.mpr he1)
    have herr := mul_nonneg (mul_nonneg he0 hε) hℓ
    nlinarith
  have hscale := mul_le_mul_of_nonneg_right hrate (mul_nonneg hg hℓ)
  have hτbound := mul_le_mul_of_nonneg_right htop (mul_nonneg hτ hℓ)
  change t*((g/2+τ)*ℓ-ω)+(Real.exp (-t)-1)*m ≤ _
  nlinarith

end JointDickman

end OAI
