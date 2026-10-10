import OAI.Geometry.NodalSets.Elliptic.SignScalePacking
import OAI.Geometry.NodalSets.Elliptic.SuccessfulTestSelection
import OAI.Geometry.NodalSets.Waves.FixedDomainLatticePhysicalSignSubballs
import OAI.Geometry.NodalSets.Waves.LatticeGoodEvent
import OAI.Geometry.NodalSets.Waves.LatticeSuccessfulPacking

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section

theorem lattice_successful_packing_fixed_domain
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) {H : Set Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ tau : ℝ, 0 < tau ∧ tau < 1/4 ∧ ∃ r : ℝ, 0 < r ∧
      r < tau/4 ∧ r < (1-tau)/2 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (w S S0 T0 : Coord → ℝ) (D U Q Ω : Set Coord) (m J K k0 : ℕ)
        (a : LocalCompactWaveData g w S D m J K k0) (_ : IsCompact D) (_ : D ⊆ H) (hUD : U ⊆ D),
        U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
        ContDiff ℝ ∞ S → ContDiff ℝ ∞ S0 → ContDiff ℝ ∞ T0 → 5 ≤ k0 →
        ∀ gamma > 0, (∀ x ∈ Q, S0 x+gamma ≤ S x) →
        IsCompact Ω → (∀ x ∈ Ω, fderiv ℝ T0 x ≠ 0) →
        ∀ d > 0, (∀ x ∈ Ω, x ∉ U → S x-S0 x ≤ -d) →
        0 < (∫ x in Q, sourceSignScale g S x) →
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
          ∃ t : Finset Coord, ∃ j : t → Fin 4,
          ∃ coeff ∈ a.latticeGoodEvent hUD n hfin S0 T0 Ω, ∃ u : Finset t,
            let R := fun x ↦ ((n:ℝ)*sourceSignScale g S x)⁻¹
            let f := fun y ↦ oscillatorySeed S0 T0 n y + gaussianWaveField
              (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff y
            (↑t : Set Coord) ⊆ Q ∧
            (↑t : Set Coord).PairwiseDisjoint (fun x ↦ sourceClosedBall x (R x)) ∧
            (∀ x ∈ t, 0 < R x ∧ sourceClosedBall x (5*R x) ⊆ U) ∧
            (∀ x ∈ u,
              (∀ y ∈ sourceClosedBall x (r*R x), 0 < f y) ∧
              (∀ y ∈ sourceClosedBall ((x : Coord)+R x • (tau • Pi.single (j x) 1)) (r*R x), f y < 0)) ∧
            c*((n:ℝ)*(∫ x in Q, sourceSignScale g S x)) ≤ ∑ x ∈ u, (R x)^3 := by
  classical
  obtain ⟨tau,ht,ht4,r,hr,hrt,hr1,p,hp0,hprob⟩ := lattice_physical_sign_subballs_fixed_domain g hH hg hp
  let C : ℝ := 2*(Real.pi^2/2)*5^4
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨tau,ht,ht4,r,hr,hrt,hr1,p/(2*C),by positivity,?_⟩
  intro w S S0 T0 D U Q Ω m J K k0 a hD hDH hUD hUH hU hUb hQ hQU hS hS0 hT0 hk0
    gamma hgamma hgap hΩ hq d hd hout hmass
  filter_upwards [hprob w S S0 T0 D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU
    hS hS0 hT0 hk0 gamma hgamma hgap,
    a.source_sign_scale_packing hQ hU hQU hUD,
    a.lattice_good_event_probability hUD hU hUb hS S0 T0 hS0 hT0 hΩ (by omega) hq hd hout
      (p/4) (by positivity)] with n hsign hpack hgood
  obtain ⟨hfin,hsign⟩ := hsign
  obtain ⟨hfin',hgood⟩ := hgood
  have heq : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  let : IsProbabilityMeasure (gaussianPairs (ι := SourceGrid U n × Fin 3)) := by
    unfold gaussianPairs; infer_instance
  obtain ⟨hn,t,htQ,htdis,htcov,htU,hvol⟩ := hpack
  let R := fun x ↦ ((n:ℝ)*sourceSignScale g S x)⁻¹
  let f := fun coeff y ↦ oscillatorySeed S0 T0 n y + gaussianWaveField
    (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff y
  choose j hj using (fun x : t ↦ hsign x (htQ x.property))
  let A := fun x : t ↦ {coeff |
    (∀ y ∈ sourceClosedBall x (r*R x), 0 < f coeff y) ∧
    (∀ y ∈ sourceClosedBall ((x : Coord)+R x • (tau • Pi.single (j x) 1)) (r*R x), f coeff y < 0)}
  have hA (x : t) : MeasurableSet (A x) ∧ p ≤ gaussianPairs.real (A x) := by
    simpa only [A,f,R,sourceClosedBall,mem_ofPred_eq,div_eq_mul_inv] using (hj x).2
  have hsum : (∑ x : t, (R x)^3) = ∑ x ∈ t, (R x)^3 := by
    exact Finset.sum_coe_sort t (fun x ↦ (R x)^3)
  have hvol' : (n:ℝ)*(∫ x in Q, sourceSignScale g S x) ≤ C * ∑ x : t, (R x)^3 := by
    rw [hsum]
    exact hvol
  have hT : 0 < ∑ x : t, (R x)^3 := by
    have hh : 0 < (n:ℝ)*(∫ x in Q, sourceSignScale g S x) := mul_pos (by exact_mod_cast hn) hmass
    nlinarith
  have hfail : (gaussianPairs (a.latticeGoodEvent hUD n hfin S0 T0 Ω)ᶜ).toReal < p/2 := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgood.2
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ p/4)] at hh
    linarith
  obtain ⟨coeff,hcoeff,u,hu,hw⟩ := exists_good_successful_tests
    (fun x : t ↦ (R x)^3) (fun x ↦ (pow_pos (htU x x.property).1 3).le) hT
    A (fun x ↦ (hA x).1) hp0 (fun x ↦ (hA x).2)
    (a.latticeGoodEvent hUD n hfin S0 T0 Ω) hgood.1 hfail
  refine ⟨hfin,t,j,coeff,hcoeff,u,htQ,htdis,htU,hu,?_⟩
  calc
    p/(2*C)*((n:ℝ)*(∫ x in Q, sourceSignScale g S x)) ≤
        p/(2*C)*(C*∑ x : t, (R x)^3) := mul_le_mul_of_nonneg_left hvol' (by positivity)
    _ = p*(∑ x : t, (R x)^3)/2 := by field_simp
    _ ≤ _ := hw

end
end Yau.Geometry

end OAI
