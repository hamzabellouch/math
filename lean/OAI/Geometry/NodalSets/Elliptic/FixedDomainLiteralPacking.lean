import OAI.Geometry.NodalSets.Hausdorff.PlacedNodalCertificate
import OAI.Geometry.NodalSets.Waves.FixedDomainLatticeSuccessfulPacking

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Yau.Probability Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

theorem fixed_domain_literal_successful_packing
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) {H : Set Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ tau : ℝ, 0 < tau ∧ tau < 1/4 ∧ ∃ rf : ℝ, 0 < rf ∧
      rf < tau/4 ∧ rf < (1-tau)/2 ∧ ∃ c > 0, ∀ {w : Coord → ℝ} {r a : ℝ} {Kset : Set Coord} {T : ℝ} {m J K k0 : ℕ}
    (d : PlacedEnvelopeData g r a Kset T)
    (b : LocalCompactWaveData g w d.S (closure d.U) m J K k0)
    (_ : closure d.U ⊆ H)
    (_ : 5 ≤ k0) (_ : ∀ x ∈ closure d.Ω, fderiv ℝ seedCoordImag x ≠ 0)
    {Q : Set Coord} (_ : IsCompact Q) (_ : Q ⊆ d.U)
    {gamma : ℝ} (_ : 0 < gamma)
    (_ : ∀ x ∈ Q, seedCoordReal x+gamma ≤ d.S x) (_ : 0 < ∫ x in Q, sourceSignScale g d.S x),
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n), letI := hfin
      ∃ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
        let f := fun y ↦ seedCoordinateField n y + gaussianWaveField
          (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff y
        coeff ∈ coefficientEvent (n:ℝ) ∧ ContDiff ℝ ∞ f ∧
        (∀ x ∈ closure d.Ω, ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*d.S x))
          (Real.exp ((n:ℝ)*seedCoordReal x)) ≤ sourceFirstJetSize f n x) ∧
        ∃ t : Finset Coord, ∃ j : t → Fin 4, ∃ u : Finset t,
          let R := fun x ↦ ((n:ℝ)*sourceSignScale g d.S x)⁻¹
          (↑t : Set Coord) ⊆ Q ∧
          (↑t : Set Coord).PairwiseDisjoint (fun x ↦ sourceClosedBall x (R x)) ∧
          (∀ x ∈ t, 0 < R x ∧ sourceClosedBall x (5*R x) ⊆ d.U) ∧
          (∀ x ∈ u,
            (∀ y ∈ sourceClosedBall x (rf*R x), 0 < f y) ∧
            (∀ y ∈ sourceClosedBall ((x : Coord)+R x • (tau • Pi.single (j x) 1))
              (rf*R x), f y < 0)) ∧
          c*((n:ℝ)*(∫ x in Q, sourceSignScale g d.S x)) ≤ ∑ x ∈ u, (R x)^3 := by
  classical
  obtain ⟨tau,ht,ht4,rf,hr,hrt,hr1,c,hc,hcert⟩ := lattice_successful_packing_fixed_domain g hH hg hp
  refine ⟨tau,ht,ht4,rf,hr,hrt,hr1,c,hc,?_⟩
  intro w r a Kset T m J K k0 d b hDH hk0 hq Q hQ hQU gamma hgamma hgap hmass

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
    gamma hgamma hin d.compact_closure_Ω hq' d.gap d.gap_pos hout (by rwa [hint]),b.estimates] with n hn hb
  obtain ⟨hfin,t,j,coeff,hcoeff,u,htQ,htdis,htU,hsign,hweight⟩ := hn
  let := hfin
  let V := fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2
  let f := fun y ↦ seedCoordinateField n y+gaussianWaveField V coeff y
  have hf : ContDiff ℝ ∞ f := (seedCoordinateField_smooth n).add
    (gaussianWaveField_contDiff V coeff (fun i ↦ (hb (latticeFrame b.cover subset_closure n i.1,i.2)).1))
  rw [d.literal_good_event_eq b S S0 T0 he n hfin] at hcoeff
  have hRad : ∀ x ∈ t, ((n:ℝ)*sourceSignScale g S x)⁻¹ =
      ((n:ℝ)*sourceSignScale g d.S x)⁻¹ := by
    intro x hx
    rw [sourceSignScale_germ (he x (hUΩ (hQU (htQ hx)))).1]
  have hfield : ∀ y ∈ d.U, f y = oscillatorySeed S0 T0 n y+gaussianWaveField V coeff y := by
    intro y hy
    dsimp [f]
    rw [(seedCoordinateField_log_germ n (d.closure_Ω_branch (hUΩ hy)) S0 T0
      (he y (hUΩ hy)).2.1 (he y (hUΩ hy)).2.2).eq_of_nhds]
  have hsmall (x : t) :
      sourceClosedBall (x:Coord) (rf*((n:ℝ)*sourceSignScale g d.S x)⁻¹) ⊆ d.U ∧
      sourceClosedBall ((x:Coord)+((n:ℝ)*sourceSignScale g d.S x)⁻¹ •
        (tau • Pi.single (j x) 1)) (rf*((n:ℝ)*sourceSignScale g d.S x)⁻¹) ⊆ d.U := by
    have hRU := htU x x.property
    dsimp only at hRU
    rw [hRad x x.property] at hRU
    constructor
    · intro y hy
      apply hRU.2
      change sourceEuclideanNorm (y-(x:Coord)) ≤ _
      exact hy.trans (mul_le_mul_of_nonneg_right (by linarith : rf ≤ 5) hRU.1.le)
    · intro y hy
      apply hRU.2
      change sourceEuclideanNorm (y-(x:Coord)) ≤ _
      have hh := sourceEuclideanNorm_add_le
        (y-((x:Coord)+((n:ℝ)*sourceSignScale g d.S x)⁻¹ • (tau • Pi.single (j x) 1)))
        (((n:ℝ)*sourceSignScale g d.S x)⁻¹ • (tau • Pi.single (j x) 1))
      have hadd : y-((x:Coord)+((n:ℝ)*sourceSignScale g d.S x)⁻¹ • (tau • Pi.single (j x) 1))+
          ((n:ℝ)*sourceSignScale g d.S x)⁻¹ • (tau • Pi.single (j x) 1) = y-(x:Coord) := by abel
      rw [hadd,sourceEuclideanNorm_smul,abs_of_pos hRU.1,
        sourceEuclideanNorm_single,abs_of_pos ht] at hh
      change sourceEuclideanNorm (y-((x:Coord)+_)) ≤ _ at hy
      nlinarith
  refine ⟨hfin,coeff,hcoeff.1,hf,hcoeff.2,t,j,u,htQ,?_,?_,?_,?_⟩
  · intro x hx y hy hxy
    simpa only [Function.onFun,hRad x hx,hRad y hy] using htdis hx hy hxy
  · intro x hx
    simpa only [hRad x hx] using htU x hx
  · intro x hx
    have hh := hsign x hx
    change (∀ y ∈ sourceClosedBall (x:Coord) (rf*((n:ℝ)*sourceSignScale g S x)⁻¹),
      0 < oscillatorySeed S0 T0 n y+gaussianWaveField V coeff y) ∧
      (∀ y ∈ sourceClosedBall ((x:Coord)+((n:ℝ)*sourceSignScale g S x)⁻¹ •
        (tau • Pi.single (j x) 1)) (rf*((n:ℝ)*sourceSignScale g S x)⁻¹),
        oscillatorySeed S0 T0 n y+gaussianWaveField V coeff y < 0) at hh
    rw [hRad x x.property] at hh
    constructor
    · intro y hy
      change 0 < f y
      rw [hfield y ((hsmall x).1 hy)]
      exact hh.1 y hy
    · intro y hy
      change f y < 0
      rw [hfield y ((hsmall x).2 hy)]
      exact hh.2 y hy
  · change c*((n:ℝ)*(∫ x in Q, sourceSignScale g S x)) ≤
      ∑ x ∈ u, (((n:ℝ)*sourceSignScale g S x)⁻¹)^3 at hweight
    rw [hint] at hweight
    simpa only [hRad _ (Subtype.property _)] using hweight

end
end Yau.Target

end OAI
