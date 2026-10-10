import OAI.NumberTheory.TotientAsymptotic.LocalSuffixBounds
import OAI.NumberTheory.TotientAsymptotic.LocalSquareNormality
import OAI.NumberTheory.TotientAsymptotic.DyadicLogGeometry
import OAI.NumberTheory.TotientAsymptotic.MovingSmoothDyadic

namespace OAI

/-! Uniform dyadic data from the actual geometric residual endpoints. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma predecessor_B_lower {p v : ℕ} (hp : 2 ≤ p) (hv : 2 ≤ v)
    (hpv : p-1 ≤ v) : B p ≤ B v+1 := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hv2 : (2:ℝ) ≤ v := by exact_mod_cast hv
  have hle : (p:ℝ) ≤ 2*v := by
    exact_mod_cast (show p ≤ 2*v by omega)
  exact (B_mono hp1 hle).trans (double_log_double_le hv2)

lemma local_dyadic_height {U : ℝ} (hU : 2 ≤ U) {v : ℕ} (hv : 1 < v)
    (hvu : (v:ℝ) ≤ Real.exp (Real.exp U)) :
    v ≤ 2^discardExponent U ∧
    B ((2:ℝ)^(Nat.clog 2 v)) ≤ 2*U+1 ∧
    1+Real.log (discardExponent U) ≤ 3*U := by
  have hbound := discardPrimeBound_bounds hU
  have hU' : U ≤ (6/5:ℝ)*U := by linarith only [hU]
  have hvN : (v:ℝ) ≤ discardPrimeBound U :=
    hvu.trans ((Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hU')).trans hbound.2.2.2)
  have hvN' : v ≤ 2^discardExponent U := by exact_mod_cast hvN
  have hk : Nat.clog 2 v ≤ discardExponent U :=
    (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr hvN'
  have hz1 : 1 < (2:ℝ)^(Nat.clog 2 v) :=
    lt_of_lt_of_le (by exact_mod_cast hv) (dyadic_nat_bounds hv).2.2
  have hle : (2:ℝ)^(Nat.clog 2 v) ≤ (discardPrimeBound U:ℝ) := by
    simpa only [discardPrimeBound,Nat.cast_pow,Nat.cast_ofNat] using
      pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hk
  refine ⟨hvN',(B_mono hz1 hle).trans hbound.2.2.1,?_⟩
  have hlog := (discardExponent_bounds hU).2
  linarith only [hlog,hU]

theorem local_residual_layer_bounds {c A : ℝ} (hc : 0 < c) (hA : 0 < A)
    (L : ℕ) : ∃ D : ℝ,0 < D ∧ ∀ z₀ : ℝ,
      ∀ᶠ h : ℕ in atTop,∀ p v : ℕ,p.Prime → p-1 ≤ v →
        c*(rho^h)⁻¹ ≤ B p →
        (v:ℝ) ≤ Real.exp (Real.exp (localPrimeHeight A L h)) →
        1 < v ∧ v ≤ 2^discardExponent (localPrimeHeight A L h) ∧
        let z := (2:ℝ)^(Nat.clog 2 v)
        max 256 z₀ ≤ z ∧ (c/2)*(rho^h)⁻¹ ≤ B z ∧ 0 ≤ B z ∧
        Real.log (B z+4) ≤ D*h ∧
        (localSquareCutoff z:ℝ) ≤ localNormalityScale h := by
  obtain ⟨D,hD,hlog⟩ := localPrimeHeight_log_bound hA L
  refine ⟨D,hD,?_⟩
  intro z₀
  let Z := max 256 z₀
  obtain ⟨H,hH⟩ := eventually_atTop.mp
    (geometric_dominates_polynomial (half_pos hc) (max 4 (B Z+1)) 0)
  filter_upwards [eventually_ge_atTop H,hlog,local_square_cutoff_le_normality hD.le]
    with h hh hlog hcut
  intro p v hp hpv hgeo hupper
  have hlarge : max 4 (B Z+1) ≤ (c/2)*(rho^h)⁻¹ := by
    simpa only [pow_zero,mul_one] using hH h hh h le_rfl
  have hfour : 4 ≤ (c/2)*(rho^h)⁻¹ := (le_max_left _ _).trans hlarge
  have hhalf : (c/2)*(rho^h)⁻¹=(c*(rho^h)⁻¹)/2 := by ring
  have hp4 : 4 ≤ p := by
    by_contra hn
    have hp3 : (p:ℝ) ≤ 3 := by exact_mod_cast (show p≤3 by omega)
    have hlogp : 0 ≤ Real.log (p:ℝ) :=
      (Real.log_pos (by exact_mod_cast hp.one_lt)).le
    have hBp : B p ≤ p :=
      (Real.log_le_self hlogp).trans (Real.log_le_self (by positivity))
    rw [hhalf] at hfour
    linarith only [hBp,hp3,hfour,hgeo]
  have hv : 1 < v := by omega
  have hv1 : (1:ℝ) < v := by exact_mod_cast hv
  have hdata := local_dyadic_height (localPrimeHeight_ge_two hA.le L h) hv hupper
  let z := (2:ℝ)^(Nat.clog 2 v)
  have hvz : (v:ℝ) ≤ z := (dyadic_nat_bounds hv).2.2
  have hz1 : 1 < z := hv1.trans_le hvz
  have hBvz := B_mono hv1 hvz
  have hBpv := predecessor_B_lower hp.two_le (by omega) hpv
  have hBlow : (c/2)*(rho^h)⁻¹ ≤ B z := by
    rw [hhalf] at hfour ⊢
    linarith only [hfour,hBpv,hgeo,hBvz]
  have hB0 : 0 ≤ B z := (by positivity : 0≤(c/2)*(rho^h)⁻¹).trans hBlow
  have hZ : Z ≤ z := by
    have hZ0 : 1 < Z := by dsimp [Z]; have := le_max_left (256:ℝ) z₀; linarith
    have hBZZ : B Z ≤ B z := by
      have hh := (le_max_right 4 (B Z+1)).trans hlarge
      linarith only [hh,hBlow]
    exact (Real.log_le_log_iff (by linarith : 0<Z) (by linarith : 0<z)).mp
      ((Real.log_le_log_iff (Real.log_pos hZ0) (Real.log_pos hz1)).mp hBZZ)
  have hlogz : Real.log (B z+4) ≤ D*h := by
    apply le_trans _ hlog
    apply Real.log_le_log (by linarith only [hB0])
    have hU := localPrimeHeight_ge_two hA.le L h
    have hBupper : B z ≤ 2*localPrimeHeight A L h+1 := hdata.2.1
    linarith only [hBupper,hU]
  exact ⟨hv,hdata.1,hZ,hBlow,hB0,hlogz,hcut z hz1 hB0 hlogz⟩

end TotientAsymptotic

end

end OAI
