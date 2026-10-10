import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.Geometry.NodalSets.Elliptic.RescaledCoordinates
import OAI.Geometry.NodalSets.Elliptic.RescaledSeedBounds
import OAI.Geometry.NodalSets.Waves.LatticeVarianceComparison

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem rescaled_seed_decay (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (hS : ContDiff ℝ ∞ S) (S0 T0 : Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    (δ : ℝ) (hδ : 0 < δ) (hgap : ∀ x ∈ Q, S0 x+δ ≤ S x)
    (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
      ∀ x ∈ Q, ∀ s : ℝ, 1 ≤ s → ∀ v : Coord, ‖v‖ ≤ R →
        ‖iteratedFDeriv ℝ k
          (rescaledSeed S0 T0 S n s (a.latticeSigma hUD n x) x) v‖ ≤ ε := by
  obtain ⟨c,hc,C,hC,hsigma⟩ := a.lattice_sigma_comparison hUD hU hUb hQ hQU
  obtain ⟨B,hB,hseed⟩ := rescaledSeed_derivative_bound S0 T0 S hS0 hT0 hS hQ R k
  obtain ⟨L,hL,hshift⟩ := compact_rescaled_envelope_bound S0 hS0 hQ R hR
  have hdecay : Tendsto (fun n : ℕ ↦ (B*Real.exp L/c)*
      ((n:ℝ)^k*Real.exp (-δ*(n:ℝ)))) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k:ℝ) δ hδ).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n:ℝ)) atTop atTop)
    simpa only [Function.comp_def,Real.rpow_natCast,mul_zero] using ht.const_mul (B*Real.exp L/c)
  filter_upwards [hsigma,hdecay.eventually (gt_mem_nhds hε),eventually_gt_atTop (0:ℕ)]
    with n hn hsmall hnpos
  obtain ⟨hfin,hσ⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx s hs v hv
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hn0 : (0:ℝ) < n := by exact_mod_cast hnpos
  have hσ0 : 0 < a.latticeSigma hUD n x :=
    lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) (hσ x hx).1
  have he : Real.exp ((n:ℝ)*S0 (x+((n:ℝ)*s)⁻¹ • v)) ≤
      Real.exp ((n:ℝ)*S x)*Real.exp (-δ*(n:ℝ))*Real.exp L := by
    rw [← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := (le_abs_self _).trans (hshift n s hnR hs x hx v hv)
    have hg := mul_le_mul_of_nonneg_left (hgap x hx) hn0.le
    nlinarith
  have hσ' := mul_le_mul_of_nonneg_left (hσ x hx).1
    (by positivity : 0 ≤ (B*Real.exp L/c)*((n:ℝ)^k*Real.exp (-δ*(n:ℝ))))
  apply (hseed n s _ hnR hs hσ0 x hx v hv).trans
  apply le_trans _ hsmall.le
  apply (div_le_iff₀ hσ0).mpr
  calc
    _ ≤ B*(n:ℝ)^k*(Real.exp ((n:ℝ)*S x)*Real.exp (-δ*(n:ℝ))*Real.exp L) := by gcongr
    _ = ((B*Real.exp L/c)*((n:ℝ)^k*Real.exp (-δ*(n:ℝ))))*
        (c*Real.exp ((n:ℝ)*S x)) := by field_simp
    _ ≤ _ := hσ'

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
