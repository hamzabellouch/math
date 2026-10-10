import OAI.Geometry.NodalSets.Elliptic.FixedDomainLiteralPacking
import OAI.Geometry.NodalSets.Hausdorff.LiteralNodalCertificate
import OAI.Geometry.NodalSets.Hausdorff.PlacedNodalCertificate

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Yau.Probability Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

theorem fixed_domain_literal_nodal_certificate_with_packing
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
            ((d.U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Coord × ℝ | f y.1 = 0}) ∧
        LiteralNodalCertificate g d.S Q d.U n f
          (c*((n:ℝ)*(∫ x in Q, sourceSignScale g d.S x))) := by
  classical
  obtain ⟨tau,ht,ht4,rf,hr,hrt,hr1,c,hc,hpack⟩ :=
    fixed_domain_literal_successful_packing g hH hg hp
  refine ⟨2*rf^3*c,by positivity,?_⟩
  intro w r a Kset T m J K k0 d b hDH hk0 hq Q hQ hQU gamma hgamma hgap hvolume
  have hmass := b.source_sign_mass_pos hQ hvolume (hQU.trans subset_closure)
  filter_upwards [hpack d b hDH hk0 hq hQ hQU hgamma hgap hmass] with n hn
  obtain ⟨hfin,coeff,hcoeff,hf,hjet,t,j,u,htQ,htdis,htU,hsign,hweight⟩ := hn
  let := hfin
  let f := fun y ↦ seedCoordinateField n y+gaussianWaveField
    (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff y
  have hweight' : (2*rf^3*c)*((n:ℝ)*(∫ x in Q, sourceSignScale g d.S x)) ≤
      2*rf^3*∑ x ∈ u, (((n:ℝ)*sourceSignScale g d.S x)⁻¹)^3 := by
    have hh := mul_le_mul_of_nonneg_left hweight (by positivity : 0 ≤ 2*rf^3)
    simpa only [mul_assoc] using hh
  have hcert := literal_nodal_certificate_of_packing g d.S Q d.U n f hf.continuous
    tau rf ht ht4 hr hrt hr1 t j u _ htQ htdis htU hsign hweight'
  exact ⟨hfin,coeff,hcoeff,hf,hjet,hcert.measure hf.continuous,hcert⟩

end
end Yau.Target

end OAI
