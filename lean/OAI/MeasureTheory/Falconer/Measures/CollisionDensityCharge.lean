import OAI.MeasureTheory.Falconer.Measures.MultiscaleDensityPruning
import OAI.MeasureTheory.Falconer.Measures.DensityCellCharge
import OAI.MeasureTheory.Falconer.Radial.RadialCapCollision

namespace OAI

/-! # Original fiber densities multiply local radial collision tests -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

theorem collision_density_children_charge (μ : Measure (Space d))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (J j : ℕ) (hj : j ≤ J)
    (C : Finset ι) (hCI : C ⊆ I j) (P : Set (Space d)) (x u : Space d)
    {r D s : ℝ} {θ F : ℝ≥0∞} (hs : 0 < s) (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ i ∈ C, MeasurableSet (Q j i)) (hdisj : (C : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ i ∈ C, Q j i ⊆ P)
    (hdiam : ∀ i ∈ C, ∀ y ∈ Q j i, ∀ z ∈ Q j i, ‖y-z‖ ≤ D)
    (hsep : ∀ i ∈ C, ∀ y ∈ Q j i, s ≤ ‖y-x‖)
    (hhit : ∀ i ∈ C, ∃ z ∈ Q j i,
      (x,z) ∈ G \ multiscaleFiberBad μ G Q I θ J ∧ ‖normalize (z-x)-u‖ ≤ r)
    (htest : ∀ q ∈ P, (x,q) ∈ G \ multiscaleFiberBad μ G Q I θ J →
      ‖normalize (q-x)-u‖ ≤ r →
      μ (P ∩ {y | dist (normalize (y-x)) (normalize (q-x)) ≤ 2*D/s+2*r}) ≤ F*μ P) :
    (∑ i ∈ C, μ (Q j i)) ≤ (θ⁻¹*F)*μ P := by
  classical
  by_cases hC : C.Nonempty
  · obtain ⟨i,hi⟩ := hC
    obtain ⟨q,hqQ,hq,hqcap⟩ := hhit i hi
    let T : Set (Space d) := {y | dist (normalize (y-x)) (normalize (q-x)) ≤ 2*D/s+2*r}
    apply density_hit_children_charge μ (Prod.mk x ⁻¹' G) P T
      (hG.preimage (by fun_prop)) (Q j) C hQ hdisj hθ hθtop
    · intro i hi
      obtain ⟨z,hzQ,hz,_⟩ := hhit i hi
      exact multiscaleFiber_retained μ G Q I θ J hz hj (hCI hi) hzQ
    · intro i hi y hy
      obtain ⟨z,hzQ,_hz,hzcap⟩ := hhit i hi
      have hzx : z ≠ x := by
        intro he
        have hh := hsep i hi z hzQ
        rw [he,sub_self,norm_zero] at hh
        linarith
      exact ⟨hparent i hi hy.1,radial_cap_child_distance x z q y u hs
        (hsep i hi y hy.1) hzx hzcap hqcap (hdiam i hi y hy.1 z hzQ)⟩
    · exact htest q (hparent i hi hqQ) hq hqcap
  · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    simp only [he,Finset.sum_empty,zero_le]

end Falconer

end OAI
