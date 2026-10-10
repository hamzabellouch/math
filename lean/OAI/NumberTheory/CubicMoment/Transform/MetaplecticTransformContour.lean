import OAI.NumberTheory.CubicMoment.Transform.MetaplecticGammaRecurrence

namespace OAI

/-! Contour motion for the actual angular metaplectic transform. The two
fixed shifted Hecke Gamma strip estimates are the same published Stirling
input already used for the individual Hecke transforms. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma metaplecticGamma_shift_factor (ℓ : ℤ) (s : ℂ) :
    metaplecticGammaQuotient ℓ s =
      angularGammaFEQuotient (metaplecticAngularShift ℓ-1/6) s *
      angularGammaFEQuotient (metaplecticAngularShift ℓ+1/6) s := by
  have hk : (metaplecticAngularShift ℓ:ℂ) = (|ℓ|:ℤ)/2 := by
    simp only [metaplecticAngularShift,Complex.ofReal_div,Complex.ofReal_intCast,
      Complex.ofReal_ofNat]
  unfold metaplecticGammaQuotient angularGammaFEQuotient
  push_cast
  rw [hk]
  have h1 : 1-s+((|ℓ|:ℤ)/2-1/6) = 5/6+(|ℓ|:ℤ)/2-s := by ring
  have h2 : 1-s+((|ℓ|:ℤ)/2+1/6) = 7/6+(|ℓ|:ℤ)/2-s := by ring
  have h3 : s+((|ℓ|:ℤ)/2-1/6) = s+(|ℓ|:ℤ)/2-1/6 := by ring
  have h4 : s+((|ℓ|:ℤ)/2+1/6) = s+(|ℓ|:ℤ)/2+1/6 := by ring
  rw [h1,h2,h3,h4]
  ring

lemma metaplecticGamma_strip_bound (ℓ : ℤ) (a : ℝ)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) a)
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) a) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ ∈ Icc a (1/2:ℝ), ∀ t : ℝ,
      ‖metaplecticGammaQuotient ℓ (σ+(t:ℂ)*Complex.I)‖ ≤ C*(1+|t|)^N := by
  obtain ⟨Cm,Nm,hCm,hgm⟩ := hm
  obtain ⟨Cp,Np,hCp,hgp⟩ := hp
  refine ⟨Cm*Cp,Nm+Np,mul_nonneg hCm hCp,?_⟩
  intro σ hσ t
  rw [metaplecticGamma_shift_factor,norm_mul]
  calc
    _ ≤ (Cm*(1+|t|)^Nm)*(Cp*(1+|t|)^Np) :=
      mul_le_mul (hgm σ hσ t) (hgp σ hσ t) (_root_.norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

lemma differentiableOn_metaplecticGammaQuotient (ℓ : ℤ) :
    DifferentiableOn ℂ (metaplecticGammaQuotient ℓ) {s : ℂ | s.re < 5/6} := by
  intro s hs
  have hk : 0 ≤ ((|ℓ|:ℤ):ℝ)/2 := by positivity
  have hreg (c : ℝ) (hc : 5/6 ≤ c) :
      ∀ n : ℕ, (c:ℂ)+(|ℓ|:ℤ)/2-s ≠ -(n:ℂ) := by
    intro n hn
    have he := congrArg Complex.re hn
    simp only [Complex.sub_re,Complex.add_re,Complex.div_ofNat_re,Complex.ofReal_re,
      Complex.intCast_re,Complex.neg_re,Complex.natCast_re] at he
    change s.re < 5/6 at hs
    have hn0 : (0:ℝ) ≤ n := by positivity
    linarith
  have h1 := (Complex.differentiableAt_Gamma ((5/6:ℂ)+(|ℓ|:ℤ)/2-s)
    (by simpa using hreg (5/6) le_rfl)).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => (5/6:ℂ)+(|ℓ|:ℤ)/2-z) s by fun_prop)
  have h2 := (Complex.differentiableAt_Gamma ((7/6:ℂ)+(|ℓ|:ℤ)/2-s)
    (by simpa using hreg (7/6) (by norm_num))).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => (7/6:ℂ)+(|ℓ|:ℤ)/2-z) s by fun_prop)
  have h3 := (Complex.differentiable_one_div_Gamma (s+(|ℓ|:ℤ)/2-1/6)).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => z+(|ℓ|:ℤ)/2-1/6) s by fun_prop)
  have h4 := (Complex.differentiable_one_div_Gamma (s+(|ℓ|:ℤ)/2+1/6)).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => z+(|ℓ|:ℤ)/2+1/6) s by fun_prop)
  convert ((h1.mul h2).mul (h3.mul h4)).differentiableWithinAt using 1
  ext z
  dsimp [metaplecticGammaQuotient]
  ring

lemma norm_angularGammaFEQuotient_half {k : ℝ} (hk : -1/2 < k) (t : ℝ) :
    ‖angularGammaFEQuotient k ((1/2:ℂ)+(t:ℂ)*Complex.I)‖ = 1 := by
  let z : ℂ := (1/2:ℂ)+(t:ℂ)*Complex.I+(k:ℂ)
  have hz : 0 < z.re := by dsimp [z]; simp; linarith
  have hG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have he : 1-((1/2:ℂ)+(t:ℂ)*Complex.I)+(k:ℂ) = starRingEnd ℂ z := by
    dsimp [z]
    simp only [map_add,map_mul,map_div₀,map_one,map_ofNat,
      Complex.conj_ofReal,Complex.conj_I]
    ring
  unfold angularGammaFEQuotient
  rw [he,Complex.Gamma_conj,norm_div,Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr hG)

lemma norm_metaplecticGamma_half (ℓ : ℤ) (t : ℝ) :
    ‖metaplecticGammaQuotient ℓ ((1/2:ℂ)+(t:ℂ)*Complex.I)‖ = 1 := by
  rw [metaplecticGamma_shift_factor,norm_mul,
    norm_angularGammaFEQuotient_half (by linarith [metaplecticAngularShift_nonneg ℓ]),
    norm_angularGammaFEQuotient_half (by linarith [metaplecticAngularShift_nonneg ℓ]),one_mul]

private lemma metaplectic_scale_strip {a b v : ℝ} (hv : 0 < v)
    {σ : ℝ} (hσ : σ ∈ Icc a b) :
    v^σ ≤ max (v^a) (v^b) := by
  by_cases h : 1 ≤ v
  · exact (Real.rpow_le_rpow_of_exponent_le h hσ.2).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_exponent_ge hv (le_of_not_ge h) hσ.1).trans (le_max_left _ _)

/-- Exact vertical contour move for the transform integrand. The scale
may lie on either side of one. -/
theorem metaplectic_transform_contour (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {a b v : ℝ} (hab : a ≤ b) (hb : b ≤ 1/2)
    (hv : 0 < v)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) a)
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) a) :
    (∫ t : ℝ, (v:ℂ)^((a:ℂ)+(t:ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ ((a:ℂ)+(t:ℂ)*Complex.I)*
      mellin W ((a:ℂ)+(t:ℂ)*Complex.I)) =
    ∫ t : ℝ, (v:ℂ)^((b:ℂ)+(t:ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ ((b:ℂ)+(t:ℂ)*Complex.I)*
      mellin W ((b:ℂ)+(t:ℂ)*Complex.I) := by
  obtain ⟨C,N,hC,hQ⟩ := metaplecticGamma_strip_bound ℓ a hm hp
  let L : ℂ → ℂ := fun s => (v:ℂ)^s*metaplecticGammaQuotient ℓ s
  let D : ℝ := max (v^a) (v^b)*C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hg (σ : ℝ) (hσ : σ ∈ Icc a b) (t : ℝ) :
      ‖L (σ+((t-0:ℝ):ℂ)*Complex.I)‖ ≤ D*(1+|t-0|)^N := by
    simp only [sub_zero]
    dsimp [L]
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hv]
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    calc
      _ ≤ max (v^a) (v^b)*(C*(1+|t|)^N) :=
        mul_le_mul (metaplectic_scale_strip hv hσ) (hQ σ ⟨hσ.1,hσ.2.trans hb⟩ t)
          (_root_.norm_nonneg _) (by positivity)
      _ = _ := by dsimp [D]; ring
  have : NeZero (v:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hv.ne'⟩
  have hd : DifferentiableOn ℂ L (closedVerticalStrip a b) := by
    apply (differentiable_const_cpow_of_neZero _).differentiableOn.mul
    exact (differentiableOn_metaplecticGammaQuotient ℓ).mono (by
      intro s hs
      exact lt_of_le_of_lt (hs.2.trans hb) (by norm_num))
  let f : ℂ → ℂ := fun s => mellin W s*L s
  have hf : DifferentiableOn ℂ f (closedVerticalStrip a b) :=
    (smooth_mellin_entire W hW hpos hsm.continuous).differentiableOn.mul hd
  obtain ⟨K,_hK,hbound⟩ := norm_mellinHecke_integrand_le W hW hpos hsm
    (Z := 1) (by norm_num) 0 L hD N hg
  have hmajor (σ : ℝ) (hσ : σ ∈ Icc a b) (t : ℝ) :
      ‖f (σ+(t:ℂ)*Complex.I)‖ ≤ mellinEdgeMajorant K t := by
    simpa only [f,sub_zero,Complex.ofReal_one,Complex.one_cpow,mul_one] using hbound σ hσ t
  have hs := mellin_contour_shift_of_majorant hab f hf (mellinEdgeMajorant K)
    (mellinEdgeMajorant_integrable K) (mellinEdgeMajorant_tendsto K).1
    (mellinEdgeMajorant_tendsto K).2 hmajor
  convert hs using 1 <;> congr 1 <;> funext t <;> dsimp [f,L] <;> ring

end CubicFirstMoment

end

end OAI
