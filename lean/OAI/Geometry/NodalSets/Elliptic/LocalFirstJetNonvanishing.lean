import OAI.Geometry.NodalSets.Elliptic.HighRegionNonvanishing
import OAI.Geometry.NodalSets.Elliptic.LowRegionSeedDominance

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology ENNReal
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem local_first_jet_nonvanishing (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hS : ContDiff ℝ ∞ S)
    (S0 T0 : Coord → ℝ) (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    {Ω : Set Coord} (hΩ : IsCompact Ω) (hk0 : 2 ≤ k0)
    (hq : ∀ x ∈ Ω, fderiv ℝ T0 x ≠ 0)
    {d : ℝ} (hd : 0 < d) (hgap : ∀ x ∈ Ω, x ∉ U → S x-S0 x ≤ -d) :
    ∃ B > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      gaussianPairs {coeff | ∃ x ∈ Ω,
        firstJetSize (fun z ↦ oscillatorySeed S0 T0 n z+gaussianWaveField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff z) n x <
        (4*((n:ℝ)^65)⁻¹)*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x))} ≤
      ENNReal.ofReal (B/((n:ℝ)*Real.sqrt n)+C*(n:ℝ)^2*Real.exp (-(n:ℝ)^2/8)) := by
  obtain ⟨B,hB,C,hC,hhigh⟩ := a.high_region_nonvanishing_probability
    hUD hU hUb hS S0 T0 hS0 hT0 hΩ hk0 hd hgap
  obtain ⟨D,hD,htail⟩ := lattice_coefficient_event_failure hUb
  have hlow := a.low_region_seed_dominance hUD hUb S0 T0 hS0 hT0 hΩ hq (by omega)
  refine ⟨B,hB,C+D,by positivity,?_⟩
  filter_upwards [hhigh,hlow,eventually_ge_atTop (24:ℕ)] with n hn hln hn6
  obtain ⟨hfin,hprob⟩ := hn
  obtain ⟨hfin',hdom⟩ := hln
  cases Subsingleton.elim hfin' hfin
  let := hfin
  refine ⟨hfin,?_⟩
  let u := fun coeff z ↦ oscillatorySeed S0 T0 n z+gaussianWaveField
    (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff z
  have hsub : {coeff | ∃ x ∈ Ω, firstJetSize (u coeff) n x <
      (4*((n:ℝ)^65)⁻¹)*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x))} ⊆
      (coefficientEvent (n:ℝ))ᶜ ∪ {coeff | ∃ x ∈ highEnvelopeRegion Ω S S0 n,
        ‖a.latticeSeededJet hUD n hfin (oscillatorySeed S0 T0 n) x coeff‖ < ((n:ℝ)^56)⁻¹} := by
    intro coeff hc
    by_cases hevent : coeff ∈ coefficientEvent (n:ℝ)
    · obtain ⟨x,hx,hbad⟩ := hc
      by_cases hxE : x ∈ highEnvelopeRegion Ω S S0 n
      · right
        refine ⟨x,hxE,?_⟩
        by_contra hjet
        have hj : ((n:ℝ)^56)⁻¹ ≤ ‖normalizedRealJet (u coeff) n (S x) x‖ := le_of_not_gt hjet
        exact (not_lt_of_ge (high_region_firstJetSize_lower hn6 hxE (u coeff) hj)) hbad
      · exact False.elim ((not_lt_of_ge (hdom coeff hevent x hx hxE)) hbad)
    · exact Or.inl hevent
  have h := (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add (htail n (by omega) hfin) hprob))
  refine h.trans_eq ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

theorem local_first_jet_failure_tends_zero (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hS : ContDiff ℝ ∞ S)
    (S0 T0 : Coord → ℝ) (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    {Ω : Set Coord} (hΩ : IsCompact Ω) (hk0 : 2 ≤ k0)
    (hq : ∀ x ∈ Ω, fderiv ℝ T0 x ≠ 0)
    {d : ℝ} (hd : 0 < d) (hgap : ∀ x ∈ Ω, x ∉ U → S x-S0 x ≤ -d) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      gaussianPairs {coeff | ∃ x ∈ Ω,
        firstJetSize (fun z ↦ oscillatorySeed S0 T0 n z+gaussianWaveField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff z) n x <
        (4*((n:ℝ)^65)⁻¹)*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x))} ≤
      ENNReal.ofReal ε := by
  obtain ⟨B,_,C,_,hprob⟩ := a.local_first_jet_nonvanishing hUD hU hUb hS
    S0 T0 hS0 hT0 hΩ hk0 hq hd hgap
  have hrate : Tendsto (fun n : ℕ ↦ B/((n:ℝ)*Real.sqrt n)+
      C*(n:ℝ)^2*Real.exp (-(n:ℝ)^2/8)) atTop (𝓝 0) := by
    simpa only [add_zero] using (tendsto_net_rate B).add (tendsto_coefficient_tail_rate C)
  intro ε hε
  filter_upwards [hprob,hrate.eventually (gt_mem_nhds hε)] with n hn hsmall
  obtain ⟨hfin,hp⟩ := hn
  exact ⟨hfin,hp.trans (ENNReal.ofReal_le_ofReal hsmall.le)⟩

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
