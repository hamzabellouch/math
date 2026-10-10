import OAI.MeasureTheory.Falconer.Measures.MultiscaleCollisionMass
import OAI.MeasureTheory.Falconer.Radial.RadialCollisionMass
import Mathlib.Probability.ConditionalProbability

namespace OAI

/-! # Multiplying conditional-source radial estimates at retained original witnesses -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

theorem conditional_radial_collision_test (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (P : Set (Space d)) (hP : MeasurableSet P) (x z : Space d) (r : ℝ) (F : ℝ≥0∞)
    (h : radialCollisionMass (ProbabilityTheory.cond μ P) r (z,x) ≤ F) :
    μ (P ∩ {y | dist (normalize (y-x)) (normalize (z-x)) ≤ r}) ≤ F*μ P := by
  rw [← ProbabilityTheory.cond_mul_eq_inter hP _ μ]
  exact mul_le_mul' h le_rfl

theorem radial_collision_pruning_multiplication (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (J : ℕ) (D W : ℕ → ℝ) (r s : ℝ) (θ : ℝ≥0∞) (F : ℕ → ℝ≥0∞)
    (hs : 0 < s) (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ j < J, ∀ i ∈ I (j+1),
      parent j i ∈ I j ∧ Q (j+1) i ⊆ Q j (parent j i))
    (hdiam : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, ∀ z ∈ Q (j+1) i, ‖y-z‖ ≤ D j)
    (hsep : ∀ x, (∃ z, (x,z) ∈ G) → ∀ j < J, ∀ i ∈ I (j+1),
      ∀ y ∈ Q (j+1) i, s ≤ ‖y-x‖)
    (hwidth : ∀ j < J, 2*D j/s+2*r ≤ W j)
    (hlocal : ∀ j < J, ∀ p ∈ I j, ∀ x z, (x,z) ∈ G → z ∈ Q j p →
      radialCollisionMass (ProbabilityTheory.cond μ (Q j p)) (W j) (z,x) ≤ F j)
    (hcover : ∀ x z, (x,z) ∈ G → ∃ i ∈ I J, z ∈ Q J i) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (ν.prod μ) (G \ G') ≤ (J+1:ℝ≥0∞)*(θ*μ univ)*ν univ ∧
      ∀ x u : Space d,
        μ {z | (x,z) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ r} ≤
          (∏ j ∈ Finset.range J, θ⁻¹*F j)*μ univ := by
  let Bad := multiscaleFiberBad μ G Q I θ J
  have hBad : MeasurableSet Bad := multiscaleFiberBad_measurable μ G hG Q I θ J hQ
  let G' := G \ Bad
  have hG' : MeasurableSet G' := hG.diff hBad
  refine ⟨G',hG',sdiff_subset,?_,?_⟩
  · apply (measure_mono _).trans (multiscaleFiberBad_mass ν μ G hG Q I J hQ hdisj θ)
    intro p hp
    by_contra hb
    exact hp.2 ⟨hp.1,hb⟩
  · intro x u
    by_cases hx : ∃ z, (x,z) ∈ G
    · apply multiscale_collision_cap_mass μ G hG Q I parent J x u r s D θ F hs hθ hθtop
        hQ hdisj hparent hdiam (hsep x hx)
      · intro j hj p hp z hz hzg
        apply (measure_mono _).trans
          (conditional_radial_collision_test μ (Q j p) (hQ j hj.le p hp) x z (W j) (F j)
            (hlocal j hj p hp x z hzg hz))
        rintro y ⟨hy,hclose⟩
        exact ⟨hy,hclose.trans (hwidth j hj)⟩
      · intro z hz
        exact hcover x z hz.1.1
    · have he : {z | (x,z) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ r} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hx ⟨z,hz.1.1⟩
      rw [he,measure_empty]
      exact zero_le

end Falconer

end OAI
