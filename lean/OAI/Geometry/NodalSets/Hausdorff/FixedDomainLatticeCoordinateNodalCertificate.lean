import OAI.Geometry.NodalSets.Elliptic.SignMass
import OAI.Geometry.NodalSets.Hausdorff.FiniteNodalCylinder
import OAI.Geometry.NodalSets.Hausdorff.LatticeCoordinateNodalCertificate
import OAI.Geometry.NodalSets.Waves.FixedDomainLatticeSuccessfulPacking

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology ENNReal
noncomputable section

theorem lattice_coordinate_nodal_certificate_fixed_domain
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) {H : Set Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (w S S0 T0 : Coord → ℝ) (D U Q Ω : Set Coord) (m J K k0 : ℕ)
        (a : LocalCompactWaveData g w S D m J K k0) (_ : IsCompact D) (_ : D ⊆ H) (hUD : U ⊆ D),
        U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
        ContDiff ℝ ∞ S → ContDiff ℝ ∞ S0 → ContDiff ℝ ∞ T0 → 5 ≤ k0 →
        ∀ gamma > 0, (∀ x ∈ Q, S0 x+gamma ≤ S x) →
        IsCompact Ω → (∀ x ∈ Ω, fderiv ℝ T0 x ≠ 0) →
        ∀ d > 0, (∀ x ∈ Ω, x ∉ U → S x-S0 x ≤ -d) →
        volume Q ≠ 0 →
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
          ∃ coeff ∈ a.latticeGoodEvent hUD n hfin S0 T0 Ω,
            let f := fun y ↦ oscillatorySeed S0 T0 n y + gaussianWaveField
              (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff y
            ContDiff ℝ ∞ f ∧
            ENNReal.ofReal (c*((n:ℝ)*(∫ x in Q, sourceSignScale g S x))) ≤
              Measure.hausdorffMeasure (4:ℝ)
                ((U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Coord × ℝ | f y.1 = 0}) := by
  classical
  obtain ⟨tau,ht,ht4,r,hr,hrt,hr1,c,hc,hpack⟩ := lattice_successful_packing_fixed_domain g hH hg hp
  refine ⟨2*r^3*c,by positivity,?_⟩
  intro w S S0 T0 D U Q Ω m J K k0 a hD hDH hUD hUH hU hUb hQ hQU hS hS0 hT0 hk0
    gamma hgamma hgap hΩ hq d hd hout hvolume
  have hmass := a.source_sign_mass_pos hQ hvolume (hQU.trans hUD)
  filter_upwards [hpack w S S0 T0 D U Q Ω m J K k0 a hD hDH hUD hUH hU hUb hQ hQU
    hS hS0 hT0 hk0 gamma hgamma hgap hΩ hq d hd hout hmass,a.estimates] with n hn he
  obtain ⟨hfin,t,j,coeff,hcoeff,u,htQ,htdis,htU,hsign,hweight⟩ := hn
  let := hfin
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  let f := fun y ↦ oscillatorySeed S0 T0 n y+gaussianWaveField V coeff y
  let R := fun x ↦ ((n:ℝ)*sourceSignScale g S x)⁻¹
  have hV (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (he (latticeFrame a.cover hUD n i.1,i.2)).1
  have hf : ContDiff ℝ ∞ f :=
    (oscillatorySeed_contDiff S0 T0 hS0 hT0 n).add (gaussianWaveField_contDiff V coeff hV)
  have hdis : (↑u : Set t).PairwiseDisjoint (fun x ↦ sourceClosedBall (x:Coord) (R x)) := by
    intro x _ y _ hxy
    exact htdis x.property y.property (fun h ↦ hxy (Subtype.ext h))
  have hU' : ∀ x ∈ u, sourceClosedBall (x:Coord) (R x) ⊆ U := by
    intro x hx y hy
    apply (htU x x.property).2
    change sourceEuclideanNorm (y-x) ≤ 5*R x
    exact hy.trans (by linarith [(htU x x.property).1])
  have hmeasure := finite_nodal_cylinder_measure u f hf.continuous
    (fun x : t ↦ (x:Coord)) (fun x : t ↦ R x) j ht.le hr.le (by linarith)
    (fun x _ ↦ (htU x x.property).1) hdis hU' hsign
  refine ⟨hfin,coeff,hcoeff,hf,?_⟩
  apply (ENNReal.ofReal_le_ofReal ?_).trans hmeasure
  have hh := mul_le_mul_of_nonneg_left hweight (by positivity : 0 ≤ 2*r^3)
  simpa only [mul_assoc] using hh

end
end Yau.Geometry

end OAI
