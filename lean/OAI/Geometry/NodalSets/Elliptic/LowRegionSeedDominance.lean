import OAI.Geometry.NodalSets.Elliptic.FirstJetSize
import OAI.Geometry.NodalSets.Elliptic.SeedDerivativeBounds
import OAI.Geometry.NodalSets.Elliptic.SeedJetLowerBound
import OAI.Geometry.NodalSets.Waves.LatticeFieldBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter
open scoped ContDiff Topology
noncomputable section

lemma low_envelope_ratio {Ω : Set Coord} {S S0 : Coord → ℝ} {n : ℕ}
    (hn : 0 < n) {x : Coord} (hx : x ∈ Ω) (hxE : x ∉ highEnvelopeRegion Ω S S0 n) :
    Real.exp ((n:ℝ)*S x) ≤ ((n:ℝ)^8)⁻¹*Real.exp ((n:ℝ)*S0 x) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hgap : S x-S0 x < -8*Real.log (n:ℝ)/(n:ℝ) := by
    by_contra hh
    exact hxE ⟨hx,le_of_not_gt hh⟩
  have hb := (lt_div_iff₀ hnR).mp hgap
  have he : (n:ℝ)*S x ≤ (n:ℝ)*S0 x-8*Real.log (n:ℝ) := by nlinarith
  have hlog : Real.exp (8*Real.log (n:ℝ)) = (n:ℝ)^8 := by
    rw [show (8:ℝ)*Real.log (n:ℝ) = (8:ℕ)*Real.log (n:ℝ) by norm_num,
      Real.exp_nat_mul,Real.exp_log hnR]
  have h := Real.exp_le_exp.mpr he
  rw [Real.exp_sub,hlog] at h
  simpa [div_eq_mul_inv,mul_comm] using h

variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem low_region_seed_dominance (hUD : U ⊆ D) (hUb : Bornology.IsBounded U)
    (S0 T0 : Coord → ℝ) (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    {Ω : Set Coord} (hΩ : IsCompact Ω) (hq : ∀ x ∈ Ω, fderiv ℝ T0 x ≠ 0) (hk0 : 1 ≤ k0) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
        coeff ∈ coefficientEvent (n:ℝ) → ∀ x ∈ Ω, x ∉ highEnvelopeRegion Ω S S0 n →
        (4*((n:ℝ)^65)⁻¹)*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x)) ≤
          firstJetSize (fun z ↦ oscillatorySeed S0 T0 n z+gaussianWaveField
            (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff z) n x := by
  obtain ⟨c,hc,hseed⟩ := uniform_oscillatory_seed_jet S0 T0 hS0 hT0 hΩ hq
  obtain ⟨C,hC,hfield⟩ := a.lattice_field_derivative_bound hUD hUb
  have hfreq : ∀ᶠ n : ℕ in atTop, max 1 (max (4*C/c) (8/c)) ≤ (n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hfield,hfreq,eventually_gt_atTop (0:ℕ)] with n hn hf hnpos
  obtain ⟨hfin,hb⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff hcoeff x hx hxE
  obtain ⟨hW,hWb⟩ := hb coeff hcoeff
  let W := gaussianWaveField
    (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have hn1 : (1:ℝ) ≤ n := (le_max_left _ _).trans hf
  have hnC : 4*C/c ≤ (n:ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hf)
  have hnc : 8/c ≤ (n:ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hf)
  have hratio := low_envelope_ratio hnpos hx hxE
  have hrand : firstJetSize W n x ≤ 2*C*((n:ℝ)^5)⁻¹*Real.exp ((n:ℝ)*S0 x) := by
    have h0 := hWb x ⟨0,by omega⟩
    have h1 := hWb x ⟨1,by omega⟩
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h0
    simp only [norm_iteratedFDeriv_one] at h1
    have hval : firstJetSize W n x ≤ 2*C*(n:ℝ)^3*Real.exp ((n:ℝ)*S x) := by
      have hi := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hnR.le)
      have he : (n:ℝ)⁻¹*(C*(n:ℝ)^4*Real.exp ((n:ℝ)*S x)) =
          C*(n:ℝ)^3*Real.exp ((n:ℝ)*S x) := by field_simp
      change (n:ℝ)⁻¹*‖fderiv ℝ W x‖ ≤ _ at hi
      rw [he] at hi
      change |W x| ≤ C*(n:ℝ)^3*Real.exp ((n:ℝ)*S x) at h0
      unfold firstJetSize
      linarith
    refine hval.trans ?_
    calc
      _ ≤ 2*C*(n:ℝ)^3*(((n:ℝ)^8)⁻¹*Real.exp ((n:ℝ)*S0 x)) := by gcongr
      _ = _ := by field_simp
  have hsmall : 2*C*((n:ℝ)^5)⁻¹ ≤ c/2 := by
    have h5 : (n:ℝ) ≤ (n:ℝ)^5 := by simpa using pow_le_pow_right₀ hn1 (show 1 ≤ 5 by omega)
    have hC' := (div_le_iff₀ hc).mp hnC
    change 2*C/(n:ℝ)^5 ≤ c/2
    apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)^5)).mpr
    change 2*C ≤ c/2*(n:ℝ)^5
    nlinarith
  have hlower := firstJetSize_seed_dominance (oscillatorySeed S0 T0 n) W hnR.le x
    ((oscillatorySeed_contDiff S0 T0 hS0 hT0 n).differentiable (by simp)).differentiableAt
    (hW.differentiable (by simp)).differentiableAt (hseed n hnR x hx)
    (hrand.trans (mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le))
  have hmax : max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x)) = Real.exp ((n:ℝ)*S0 x) := by
    apply max_eq_right
    have hi : ((n:ℝ)^8)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ hn1)
    exact hratio.trans (by nlinarith [Real.exp_pos ((n:ℝ)*S0 x)])
  rw [hmax]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le) hlower
  have h65 : (n:ℝ) ≤ (n:ℝ)^65 := by simpa using pow_le_pow_right₀ hn1 (show 1 ≤ 65 by omega)
  have hc' := (div_le_iff₀ hc).mp hnc
  change 4/(n:ℝ)^65 ≤ c/2
  apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)^65)).mpr
  nlinarith

end LocalCompactWaveData

end
end Yau.Geometry

end OAI
