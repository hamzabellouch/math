import OAI.Geometry.NodalSets.Elliptic.FirstJetGoodEvent
import OAI.Geometry.NodalSets.Elliptic.FirstJetNonvanishing

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
    {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticeGoodEvent (hUD : U ⊆ D) (n : ℕ) (hfin : Fintype (SourceGrid U n))
    (S0 T0 : Coord → ℝ) (Ω : Set Coord) : Set (((SourceGrid U n × Fin 3) × Fin 2) → ℝ) :=
  letI := hfin
  coefficientJetGoodEvent
    (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2)
    (oscillatorySeed S0 T0 n) n Ω
    (fun x ↦ ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x)))

theorem lattice_good_event_probability (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hS : ContDiff ℝ ∞ S)
    (S0 T0 : Coord → ℝ) (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    {Ω : Set Coord} (hΩ : IsCompact Ω) (hk0 : 2 ≤ k0)
    (hq : ∀ x ∈ Ω, fderiv ℝ T0 x ≠ 0)
    {d : ℝ} (hd : 0 < d) (hgap : ∀ x ∈ Ω, x ∉ U → S x-S0 x ≤ -d) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      MeasurableSet (a.latticeGoodEvent hUD n hfin S0 T0 Ω) ∧
      gaussianPairs (a.latticeGoodEvent hUD n hfin S0 T0 Ω)ᶜ ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨C,hC,hcoeff⟩ := lattice_coefficient_event_failure hUb
  have htail := (tendsto_coefficient_tail_rate C).eventually (gt_mem_nhds (by linarith : 0 < ε/2))
  filter_upwards [a.source_first_jet_failure_tends_zero hUD hU hUb hS S0 T0 hS0 hT0
    hΩ hk0 hq hd hgap (ε/2) (by linarith),htail,a.estimates,eventually_gt_atTop (0:ℕ)] with n hn ht he hn0
  obtain ⟨hfin,hjet⟩ := hn
  let := hfin
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have hV (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (he (latticeFrame a.cover hUD n i.1,i.2)).1
  refine ⟨hfin,coefficientJetGoodEvent_measurable V (oscillatorySeed S0 T0 n)
    hV (oscillatorySeed_contDiff S0 T0 hS0 hT0 n) n Ω _,?_⟩
  apply (coefficientJetGoodEvent_failure_le V (oscillatorySeed S0 T0 n) n Ω _).trans
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) :=
      add_le_add ((hcoeff n hn0 hfin).trans (ENNReal.ofReal_le_ofReal ht.le)) hjet
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by linarith : 0 ≤ ε/2) (by linarith : 0 ≤ ε/2)]
      congr 1
      ring

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
