import OAI.Geometry.NodalSets.Hausdorff.FixedDomainLatticeCoordinateNodalCertificate
import OAI.Geometry.NodalSets.Hausdorff.PlacedNodalCertificate

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Yau.Probability Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

theorem fixed_domain_literal_nodal_certificate
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) {H : Set Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ c > 0, ∀ {w : Coord → ℝ} {r a : ℝ} {Kset : Set Coord} {T : ℝ} {m J K k0 : ℕ}
    (d : PlacedEnvelopeData g r a Kset T)
    (b : LocalCompactWaveData g w d.S (closure d.U) m J K k0)
    (_ : closure d.U ⊆ H)
    (_ : 5 ≤ k0) (_ : ∀ x ∈ closure d.Ω, fderiv ℝ seedCoordImag x ≠ 0)
    {Q : Set Coord} (_ : IsCompact Q) (_ : Q ⊆ d.U)
    {gamma : ℝ} (_ : 0 < gamma)
    (_ : ∀ x ∈ Q, seedCoordReal x+gamma ≤ d.S x) (_ : volume Q ≠ 0),
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n), letI := hfin
      ∃ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
        let f := fun y ↦ seedCoordinateField n y + gaussianWaveField
          (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff y
        coeff ∈ coefficientEvent (n:ℝ) ∧ ContDiff ℝ ∞ f ∧
        (∀ x ∈ closure d.Ω, ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*d.S x))
          (Real.exp ((n:ℝ)*seedCoordReal x)) ≤ sourceFirstJetSize f n x) ∧
        ENNReal.ofReal (c*((n:ℝ)*(∫ x in Q, sourceSignScale g d.S x))) ≤
          Measure.hausdorffMeasure (4:ℝ)
            ((d.U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Coord × ℝ | f y.1 = 0}) := by
  obtain ⟨c,hc,hcert⟩ := lattice_coordinate_nodal_certificate_fixed_domain g hH hg hp
  refine ⟨c,hc,?_⟩
  intro w r a Kset T m J K k0 d b hDH hk0 hq Q hQ hQU gamma hgamma hgap hvolume

  obtain ⟨S,S0,T0,hS,hS0,hT0,he⟩ := d.smooth_representatives
  let b' := d.representativeWaves b S (fun x hx ↦ (he x hx).1)
  have hUΩ : d.U ⊆ closure d.Ω := subset_closure.trans (d.closure_U_Ω.trans subset_closure)
  have hq' : ∀ x ∈ closure d.Ω, fderiv ℝ T0 x ≠ 0 := by
    intro x hx
    rw [(he x hx).2.2.fderiv_eq]
    exact hq x hx
  have hout : ∀ x ∈ closure d.Ω, x ∉ d.U → S x-S0 x ≤ -d.gap := by
    intro x hx hxu
    rw [(he x hx).1.eq_of_nhds,(he x hx).2.1.eq_of_nhds]
    exact d.outside_gap x hxu
  have hin : ∀ x ∈ Q, S0 x+gamma ≤ S x := by
    intro x hx
    rw [(he x (hUΩ (hQU hx))).1.eq_of_nhds,(he x (hUΩ (hQU hx))).2.1.eq_of_nhds]
    exact hgap x hx
  have hint : (∫ x in Q, sourceSignScale g S x) = ∫ x in Q, sourceSignScale g d.S x := by
    apply setIntegral_congr_fun hQ.measurableSet
    intro x hx
    exact sourceSignScale_germ (he x (hUΩ (hQU hx))).1
  filter_upwards [hcert w S S0 T0 (closure d.U) d.U Q (closure d.Ω) m J K k0 b'
    d.compact_closure_U hDH subset_closure (subset_closure.trans hDH) d.open_U
    (d.compact_closure_U.isBounded.subset subset_closure) hQ hQU hS hS0 hT0 hk0
    gamma hgamma hin d.compact_closure_Ω hq' d.gap d.gap_pos hout hvolume,b.estimates] with n hn hb
  obtain ⟨hfin,coeff,hcoeff,_,hmeasure⟩ := hn
  let := hfin
  let V := fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2
  let f := fun y ↦ seedCoordinateField n y+gaussianWaveField V coeff y
  have hf : ContDiff ℝ ∞ f := (seedCoordinateField_smooth n).add
    (gaussianWaveField_contDiff V coeff (fun i ↦ (hb (latticeFrame b.cover subset_closure n i.1,i.2)).1))
  rw [d.literal_good_event_eq b S S0 T0 he n hfin] at hcoeff
  refine ⟨hfin,coeff,hcoeff.1,hf,hcoeff.2,?_⟩
  have hsets : ((d.U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Coord × ℝ |
      (oscillatorySeed S0 T0 n y.1+gaussianWaveField V coeff y.1) = 0}) =
      ((d.U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Coord × ℝ | f y.1 = 0}) := by
    ext y
    constructor <;> intro hy
    · refine ⟨hy.1,?_⟩
      have heq := (seedCoordinateField_log_germ n (d.closure_Ω_branch (hUΩ hy.1.1)) S0 T0
        (he y.1 (hUΩ hy.1.1)).2.1 (he y.1 (hUΩ hy.1.1)).2.2).eq_of_nhds
      simpa only [f,heq,mem_ofPred_eq] using hy.2
    · refine ⟨hy.1,?_⟩
      have heq := (seedCoordinateField_log_germ n (d.closure_Ω_branch (hUΩ hy.1.1)) S0 T0
        (he y.1 (hUΩ hy.1.1)).2.1 (he y.1 (hUΩ hy.1.1)).2.2).eq_of_nhds
      simpa only [f,heq,mem_ofPred_eq] using hy.2
  change ENNReal.ofReal (c*((n:ℝ)*(∫ x in Q, sourceSignScale g S x))) ≤
    Measure.hausdorffMeasure (4:ℝ) ((d.U ×ˢ Icc (-1:ℝ) 1) ∩
      {y : Coord × ℝ | oscillatorySeed S0 T0 n y.1+gaussianWaveField V coeff y.1 = 0}) at hmeasure
  rw [hint,hsets] at hmeasure
  exact hmeasure

end
end Yau.Target

end OAI
