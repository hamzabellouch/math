import OAI.Geometry.NodalSets.Elliptic.JetNetExtension
import OAI.Geometry.NodalSets.Waves.LatticeNeighborhoodJets
import OAI.Geometry.NodalSets.Waves.LatticeProbabilityRates

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology ENNReal
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem high_region_nonvanishing_probability (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hS : ContDiff ℝ ∞ S)
    (S0 T0 : Coord → ℝ) (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    {Ω : Set Coord} (hΩ : IsCompact Ω) (hk0 : 2 ≤ k0)
    {d : ℝ} (hd : 0 < d) (hgap : ∀ x ∈ Ω, x ∉ U → S x-S0 x ≤ -d) :
    ∃ B > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      gaussianPairs {coeff | ∃ x ∈ highEnvelopeRegion Ω S S0 n,
        ‖a.latticeSeededJet hUD n hfin (oscillatorySeed S0 T0 n) x coeff‖ < ((n:ℝ)^56)⁻¹} ≤
      ENNReal.ofReal (B/((n:ℝ)*Real.sqrt n)+C*(n:ℝ)^2*Real.exp (-(n:ℝ)^2/8)) := by
  obtain ⟨Q,hQ,hQU,_,hEQ⟩ := high_envelope_fixed_compact hΩ hU S S0
    hS.continuous hS0.continuous hd hgap
  obtain ⟨B,hB,hnet⟩ := a.actual_lattice_net_failure_rate hUD hU hUb hQ hQU
  obtain ⟨C,hC,hcoeff⟩ := lattice_coefficient_event_failure hUb
  have hder := a.lattice_neighborhood_jet_bound hUD hUb hS S0 T0 hS0 hT0 hΩ hk0
  refine ⟨B,hB,C,hC,?_⟩
  filter_upwards [hnet,hder,hEQ,lattice_wave_estimates a.cover a.beams hUD,
    eventually_gt_atTop (0:ℕ)] with n hn hdn hEn hw hnpos
  obtain ⟨hfin,hnb⟩ := hn
  obtain ⟨hfin',hdb⟩ := hdn
  cases Subsingleton.elim hfin' hfin
  let := hfin
  refine ⟨hfin,?_⟩
  obtain ⟨t,ht,hcover,hprob⟩ := hnb (highEnvelopeRegion Ω S S0 n) hEn
  let Z := fun coeff x ↦ a.latticeSeededJet hUD n hfin (oscillatorySeed S0 T0 n) x coeff
  have hs := oscillatorySeed_contDiff S0 T0 hS0 hT0 (n:ℝ)
  have hZ (coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ) : ContDiff ℝ ∞ (Z coeff) := by
    apply normalizedRealJet_contDiff _ S _ hS n
    exact hs.add (gaussianWaveField_contDiff _ coeff
      (fun i ↦ (hw i.1 i.2).1))
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have harith := jet_mesh_arithmetic hn1
  have happrox : ∀ coeff ∈ coefficientEvent (n:ℝ),
      ∀ x ∈ highEnvelopeRegion Ω S S0 n, ∃ y ∈ t,
        ‖Z coeff y-Z coeff x‖ ≤ ((n:ℝ)^56)⁻¹ := by
    intro coeff hc
    apply neighborhood_net_approximation t (highEnvelopeRegion Ω S S0 n) (Z coeff)
      (δ := (4*(n:ℝ)^69)⁻¹) (R := ((n:ℝ)^2)⁻¹) (L := (n:ℝ)^13)
      (by positivity) harith.1 (by positivity) harith.2
    · intro x hx
      obtain ⟨y,hy,hxy,_⟩ := hcover x hx
      exact ⟨y,hy,hxy⟩
    · exact fun _ _ _ _ ↦ ((hZ coeff).differentiable (by simp)).differentiableAt
    · exact hdb coeff hc
  have h := net_failure_le_union gaussianPairs t (highEnvelopeRegion Ω S S0 n)
    Z (coefficientEvent (n:ℝ)) (((n:ℝ)^56)⁻¹) happrox
  have hp := hprob (oscillatorySeed S0 T0 n)
    (fun _ _ ↦ (hs.differentiable (by simp)).differentiableAt)
  have hpc : gaussianPairs {coeff | ∃ y ∈ t, ‖Z coeff y‖ ≤ 2*((n:ℝ)^56)⁻¹} ≤
      ENNReal.ofReal (B/((n:ℝ)*Real.sqrt n)) := by
    simpa only [div_eq_mul_inv] using hp
  refine h.trans ((add_le_add (hcoeff n hnpos hfin) hpc).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
