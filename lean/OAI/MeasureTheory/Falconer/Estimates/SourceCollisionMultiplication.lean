import OAI.MeasureTheory.Falconer.Measures.CollisionPruningMultiplication

namespace OAI

/-! # The radial multiplication theorem in source-first original-pair coordinates -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

theorem source_collision_pruning_multiplication (μ ν : Measure (Space d))
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
    (hsep : ∀ x, (∃ z, (z,x) ∈ G) → ∀ j < J, ∀ i ∈ I (j+1),
      ∀ y ∈ Q (j+1) i, s ≤ ‖y-x‖)
    (hwidth : ∀ j < J, 2*D j/s+2*r ≤ W j)
    (hlocal : ∀ j < J, ∀ p ∈ I j, ∀ z x, (z,x) ∈ G → z ∈ Q j p →
      radialCollisionMass (ProbabilityTheory.cond μ (Q j p)) (W j) (z,x) ≤ F j)
    (hcover : ∀ z x, (z,x) ∈ G → ∃ i ∈ I J, z ∈ Q J i) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ (J+1:ℝ≥0∞)*(θ*μ univ)*ν univ ∧
      ∀ x u : Space d,
        μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ r} ≤
          (∏ j ∈ Finset.range J, θ⁻¹*F j)*μ univ := by
  let Gs := Prod.swap ⁻¹' G
  have hGs : MeasurableSet Gs := hG.preimage measurable_swap
  obtain ⟨H,hH,hHG,hdel,hcap⟩ := radial_collision_pruning_multiplication μ ν Gs hGs
    Q I parent J D W r s θ F hs hθ hθtop hQ hdisj hparent hdiam hsep hwidth
    (fun j hj p hp x z hx hz => hlocal j hj p hp z x hx hz) (fun x z hx => hcover z x hx)
  refine ⟨Prod.swap ⁻¹' H,hH.preimage measurable_swap,fun p hp => hHG hp,?_,?_⟩
  · have he : G \ Prod.swap ⁻¹' H = Prod.swap ⁻¹' (Gs \ H) := by
      ext p
      simp only [mem_sdiff,mem_preimage,Gs,Prod.swap_swap]
    rw [he,← Measure.map_apply measurable_swap (hGs.diff hH),Measure.prod_swap]
    exact hdel
  · exact hcap

end Falconer

end OAI
