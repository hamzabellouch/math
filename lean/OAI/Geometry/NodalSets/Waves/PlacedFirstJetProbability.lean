import OAI.Geometry.NodalSets.Elliptic.PlacedSmoothRepresentatives
import OAI.Geometry.NodalSets.Waves.LatticeGoodEvent

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Yau.Probability Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w : Coord → ℝ}
variable {r a : ℝ} {Kset : Set Coord} {T : ℝ} {m J K k0 : ℕ}

def PlacedEnvelopeData.representativeWaves (d : PlacedEnvelopeData g r a Kset T)
    (b : LocalCompactWaveData g w d.S (closure d.U) m J K k0)
    (S : Coord → ℝ) (he : ∀ x ∈ closure d.Ω, S =ᶠ[𝓝 x] d.S) :
    LocalCompactWaveData g w S (closure d.U) m J K k0 :=
  b.withEnvelope S (envelope_germ_open d.S S)
    (fun x hx ↦ he x (subset_closure (d.closure_U_Ω hx))) (fun _ hx ↦ hx)

lemma PlacedEnvelopeData.literal_good_event_eq (d : PlacedEnvelopeData g r a Kset T)
    (b : LocalCompactWaveData g w d.S (closure d.U) m J K k0)
    (S S0 T0 : Coord → ℝ)
    (he : ∀ x ∈ closure d.Ω, S =ᶠ[𝓝 x] d.S ∧ S0 =ᶠ[𝓝 x] seedCoordReal ∧
      T0 =ᶠ[𝓝 x] seedCoordImag)
    (n : ℕ) (hfin : Fintype (SourceGrid d.U n)) :
    (d.representativeWaves b S (fun x hx ↦ (he x hx).1)).latticeGoodEvent
      subset_closure n hfin S0 T0 (closure d.Ω) =
    letI := hfin
    coefficientJetGoodEvent
      (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2)
      (seedCoordinateField n) n (closure d.Ω)
      (fun x ↦ ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*d.S x))
        (Real.exp ((n:ℝ)*seedCoordReal x))) := by
  let := hfin
  ext coeff
  simp only [LocalCompactWaveData.latticeGoodEvent,coefficientJetGoodEvent,
    mem_inter_iff,firstJetGoodEvent,mem_ofPred_eq]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hx
  have hg := seedCoordinateField_log_germ n (d.closure_Ω_branch hx) S0 T0
    (he x hx).2.1 (he x hx).2.2
  have hj := seeded_sourceFirstJetSize_germ (v := gaussianWaveField
    (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff) hg (n:ℝ)
  change (_ ≤ sourceFirstJetSize _ _ _) ↔ (_ ≤ sourceFirstJetSize _ _ _)
  rw [hj,(he x hx).1.eq_of_nhds,(he x hx).2.1.eq_of_nhds]
  rfl

theorem PlacedEnvelopeData.literal_good_event_probability
    (d : PlacedEnvelopeData g r a Kset T)
    (b : LocalCompactWaveData g w d.S (closure d.U) m J K k0) (hk0 : 2 ≤ k0)
    (hq : ∀ x ∈ closure d.Ω, fderiv ℝ seedCoordImag x ≠ 0) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n),
      letI := hfin
      let event := coefficientJetGoodEvent
        (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2)
        (seedCoordinateField n) n (closure d.Ω)
        (fun x ↦ ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*d.S x))
          (Real.exp ((n:ℝ)*seedCoordReal x)))
      MeasurableSet event ∧ gaussianPairs eventᶜ ≤ ENNReal.ofReal ε := by
  obtain ⟨S,S0,T0,hS,hS0,hT0,he⟩ := d.smooth_representatives
  let b' := d.representativeWaves b S (fun x hx ↦ (he x hx).1)
  have hq' : ∀ x ∈ closure d.Ω, fderiv ℝ T0 x ≠ 0 := by
    intro x hx
    rw [(he x hx).2.2.fderiv_eq]
    exact hq x hx
  have hgap : ∀ x ∈ closure d.Ω, x ∉ d.U → S x-S0 x ≤ -d.gap := by
    intro x hx hxu
    rw [(he x hx).1.eq_of_nhds,(he x hx).2.1.eq_of_nhds]
    exact d.outside_gap x hxu
  intro ε hε
  filter_upwards [b'.lattice_good_event_probability subset_closure d.open_U
    (d.compact_closure_U.isBounded.subset subset_closure) hS S0 T0 hS0 hT0
    d.compact_closure_Ω hk0 hq' d.gap_pos hgap ε hε] with n hn
  obtain ⟨hfin,hn⟩ := hn
  refine ⟨hfin,?_⟩
  rw [d.literal_good_event_eq b S S0 T0 he n hfin] at hn
  exact hn

end
end Yau.Target

end OAI
