import OAI.MeasureTheory.Falconer.Radial.MiddleHeavyRadialMass
import OAI.MeasureTheory.Falconer.Measures.RepresentedPruning
import OAI.MeasureTheory.Falconer.Radial.RadialBadWitness
import OAI.MeasureTheory.Falconer.Angular.WitnessDirection

namespace OAI

/-! # Original-product middle-interval pruning with no choice of pin witnesses -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem middle_radial_pruning (μ ν : Measure (Space (n+1)))
    [SFinite μ] [SFinite ν] (w₀ : Sphere (n+1))
    (G : Set (Space (n+1) × Space (n+1))) (hG : MeasurableSet G)
    (Bad : Set (Sphere (n+1))) (hBad : MeasurableSet Bad)
    (c : Space (n+1)) {r D δ θ C B H R : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hfreeze : 8*D^2/r ≤ δ)
    (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D) (hbounded : ∀ᵐ y ∂μ, ‖y‖ ≤ B)
    (hgeom : ∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z-c‖ ≤ D ∧ ‖z‖ ≤ B)
    (hpin : ∀ x, (∃ z, (z,x) ∈ G) →
      r ≤ ‖c-x‖ ∧ ∀ᵐ y ∂μ, ‖y-x‖ ≤ H)
    (hwidth : H*θ ≤ C*δ)
    (hrobust : (2*((n+1:ℕ):ℝ)+1)*δ+2*(2*D/r)*(B+B) ≤ R)
    (F a e : ℝ≥0∞) (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ))
    (henvelope : ∀ v : Sphere (n+1), ∀ S : Finset (Space (n+1)),
      (S.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ →
      a ≤ μ {z | ∃ b ∈ S, ‖perpendicularPart (v:Space (n+1)) (z-b)‖ ≤ R} → v ∈ Bad)
    (hbadmass : (μ.prod ν) (radialBadWitness w₀ G Bad) ≤ e) :
    ∃ G' : Set (Space (n+1) × Space (n+1)), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ e+a*ν univ ∧
      ∀ p ∈ G', radialCollisionMass μ θ p ≤ F := by
  let G₁ := G \ radialBadWitness w₀ G Bad
  have hG₁ : MeasurableSet G₁ := hG.diff (radialBadWitness_measurable w₀ hG hBad)
  have hsub : G₁ ⊆ G := sdiff_subset
  have hsmall (x : Space (n+1)) (hx : ∃ z, (z,x) ∈ G₁) :
      μ {z | (z,x) ∈ G₁ ∧ F < radialCollisionMass μ θ (z,x)} ≤ a := by
    obtain ⟨z,hz⟩ := hx
    have hzx := hgeom z x (hsub hz)
    have hpx := hpin x ⟨z,hsub hz⟩
    let v := normalizeToSphere w₀ (x-z)
    have hv : v ∉ Bad := direction_good_of_not_radialBadWitness w₀ G Bad hz
    apply le_of_lt
    apply middle_heavy_radial_mass_lt μ x c hr hpx.1 hδ hfreeze hsource hbounded
      hpx.2 hwidth Bad v hv (Or.inr (cell_center_witness_direction w₀ x c z hr
        hpx.1 hzx.1 hzx.2.1)) hrobust F a L hL (henvelope v)
    intro y hy
    have hh := hgeom y x (hsub hy.1)
    exact ⟨hh.1,hh.2.1,hh.2.2,hy.2⟩
  obtain ⟨G',hG',hG'sub,hdeleted,hbound⟩ := represented_threshold_pruning μ ν G₁ hG₁
    (radialCollisionMass μ θ) (radialCollisionMass_measurable μ θ) F a hsmall
  refine ⟨G',hG',hG'sub.trans hsub,?_,hbound⟩
  have hcover : G \ G' ⊆ radialBadWitness w₀ G Bad ∪ (G₁ \ G') := by
    intro p hp
    by_cases hb : p ∈ radialBadWitness w₀ G Bad
    · exact Or.inl hb
    · exact Or.inr ⟨⟨hp.1,hb⟩,hp.2⟩
  exact (measure_mono hcover).trans ((measure_union_le _ _).trans (add_le_add hbadmass hdeleted))

end Falconer

end OAI
