import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeSecondColumn

namespace OAI

/-! The explicit free H columns have the prescribed unit limits at infinity. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralFreeSlowJet_tendsto (ell : ℕ) (q : ℂ) (hq : -1 < q.re) :
    Tendsto (spectralFreeSlowJet q (ell+6)) atTop (𝓝 (1,0)) := by
  let P := spectralFreeSlowPolynomial ell q 1 1
  obtain ⟨C,_,hb⟩ := spectralFreeSlowJet_remainder ell q hq 0
  have he : Tendsto (fun t : ℝ => Real.exp (-4*t)) atTop (𝓝 0) := by
    simpa only [neg_mul,Function.comp_def,id_eq] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
  have hz : Tendsto (fun t => spectralFreeSlowJet q (ell+6) t-radialPolynomialJet P t)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa only [mul_zero] using he.const_mul C)
    filter_upwards [eventually_ge_atTop (Real.log 4/2)] with t ht
    convert hb t ht using 1
    norm_num [P]
  have hc : P.coeff 0=1 := by
    rw [spectralFreeSlowPolynomial_coefficient ell q 1 1 0 (by omega),
      spectralFreeSlowCoefficient_zero]
  have hp : Tendsto (radialPolynomialJet P) atTop (𝓝 (1,0)) := by
    have h := (radialExteriorPolynomialFunction_tendsto P).prodMk_nhds
      (radialExteriorPolynomialFunction_tendsto (radialPolynomialEuler P))
    change Tendsto (fun t => (radialExteriorPolynomialFunction P t,
      radialExteriorPolynomialFunction (radialPolynomialEuler P) t)) atTop (𝓝 (1,0))
    simpa only [hc,radialPolynomialEuler_coeff,Nat.cast_zero,mul_zero,zero_mul] using h
  convert hz.add hp using 1 <;> simp

theorem spectralFreeFirstColumn_tendsto (ell : ℕ) (q : ℂ) (hq : -1 < q.re) :
    Tendsto (spectralFreeFirstColumn ell q) atTop (𝓝 ((1,0),(0,0))) :=
  (spectralFreeSlowJet_tendsto ell q hq).prodMk_nhds tendsto_const_nhds

theorem spectralFreeSecondColumn_tendsto (ell : ℕ) (q : ℂ) (hq : -1 < q.re) :
    Tendsto (spectralFreeSecondColumn ell q) atTop (𝓝 ((0,0),(1,0))) := by
  have hq' : -1 < (star q).re := by simpa only [Complex.star_def,Complex.conj_re] using hq
  have hs := (spectralFreeSlowJet_tendsto ell (star q) hq').star
  have h0 : Tendsto (fun _ : ℝ => (0 : ℂ × ℂ)) atTop (𝓝 0) := tendsto_const_nhds
  have hs' : Tendsto (fun t => star (spectralFreeSlowJet (star q) (ell+6) t))
      atTop (𝓝 ((1,0) : ℂ × ℂ)) := by
    simpa only [Prod.star_def,star_one,star_zero] using hs
  change Tendsto (fun t => ((0 : ℂ × ℂ),
    star (spectralFreeSlowJet (star q) (ell+6) t))) atTop (𝓝 ((0,0),(1,0)))
  exact h0.prodMk_nhds hs'

end DefocusingNLS

end OAI
