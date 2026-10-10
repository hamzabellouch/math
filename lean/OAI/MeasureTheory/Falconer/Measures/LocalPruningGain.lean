import OAI.MeasureTheory.Falconer.Estimates.FiniteCellwiseCollision
import OAI.MeasureTheory.Falconer.Estimates.SourceCollisionMultiplication

namespace OAI

/-! # Original cellwise deletions followed by radial density multiplication -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

theorem radial_gain_of_local_prunings (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (J : ℕ) (D W : ℕ → ℝ) (r s : ℝ) (θ : ℝ≥0∞) (F cost : ℕ → ℝ≥0∞)
    (hs : 0 < s) (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hpos : ∀ j < J, ∀ i ∈ I j, μ (Q j i) ≠ 0)
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ j < J, ∀ i ∈ I (j+1),
      parent j i ∈ I j ∧ Q (j+1) i ⊆ Q j (parent j i))
    (hdiam : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, ∀ z ∈ Q (j+1) i, ‖y-z‖ ≤ D j)
    (hsep : ∀ x, (∃ z, (z,x) ∈ G) → ∀ j < J, ∀ i ∈ I (j+1),
      ∀ y ∈ Q (j+1) i, s ≤ ‖y-x‖)
    (hwidth : ∀ j < J, 2*D j/s+2*r ≤ W j)
    (hlocal : ∀ j < J, ∀ i ∈ I j, ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      ((ProbabilityTheory.cond μ (Q j i)).prod ν) ((G ∩ (Q j i ×ˢ univ)) \ H) ≤ cost j ∧
      ∀ p ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q j i)) (W j) p ≤ F j)
    (hcover : ∀ z x, (z,x) ∈ G → ∃ i ∈ I J, z ∈ Q J i) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ (∑ j ∈ Finset.range J, cost j*μ univ)+
        (J+1:ℝ≥0∞)*(θ*μ univ)*ν univ ∧
      ∀ x u : Space d,
        μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ r} ≤
          (∏ j ∈ Finset.range J, θ⁻¹*F j)*μ univ := by
  obtain ⟨H,hH,hHG,hdel,hbound⟩ := finite_cellwise_collision_pruning μ ν J I Q
    (fun j hj => hQ j hj.le) hpos (fun j hj => hdisj j hj.le) G hG W
    (fun j _ => F j) cost hlocal
  obtain ⟨G',hG',hsub,hdel',hcap⟩ := source_collision_pruning_multiplication μ ν H hH
    Q I parent J D W r s θ F hs hθ hθtop hQ hdisj hparent hdiam
    (fun x hx => hsep x (by obtain ⟨z,hz⟩ := hx; exact ⟨z,hHG hz⟩)) hwidth
    (fun j hj i hi z x hz hzi => hbound j hj i hi (z,x) hz hzi)
    (fun z x hz => hcover z x (hHG hz))
  refine ⟨G',hG',hsub.trans hHG,?_,hcap⟩
  have hdiff : G \ G' ⊆ (G \ H) ∪ (H \ G') := by
    intro p hp
    by_cases hpH : p ∈ H
    · exact Or.inr ⟨hpH,hp.2⟩
    · exact Or.inl ⟨hp.1,hpH⟩
  exact (measure_mono hdiff).trans ((measure_union_le _ _).trans (add_le_add hdel hdel'))

end Falconer

end OAI
