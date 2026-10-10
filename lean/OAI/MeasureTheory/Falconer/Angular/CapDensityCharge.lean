import OAI.MeasureTheory.Falconer.Measures.MultiscaleDensityPruning
import OAI.MeasureTheory.Falconer.Measures.DensityCellCharge
import OAI.MeasureTheory.Falconer.Radial.RadialCapTube

namespace OAI

/-! # A single retained cap witness charges all hit children of a parent -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

theorem cap_density_children_charge (μ : Measure (Space d))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (J j : ℕ) (hj : j ≤ J)
    (C : Finset ι) (hCI : C ⊆ I j) (P : Set (Space d)) (x u : Space d)
    {r D B : ℝ} {θ F : ℝ≥0∞} (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ i ∈ C, MeasurableSet (Q j i)) (hdisj : (C : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ i ∈ C, Q j i ⊆ P)
    (hdiam : ∀ i ∈ C, ∀ y ∈ Q j i, ∀ z ∈ Q j i, ‖y-z‖ ≤ D)
    (hhit : ∀ i ∈ C, ∃ z ∈ Q j i,
      (x,z) ∈ G \ multiscaleFiberBad μ G Q I θ J ∧
      z ≠ x ∧ ‖z-x‖ ≤ B ∧ ‖normalize (z-x)-u‖ ≤ r)
    (htest : ∀ q ∈ P, (x,q) ∈ G \ multiscaleFiberBad μ G Q I θ J →
      q ≠ x → ‖normalize (q-x)-u‖ ≤ r →
      μ (P ∩ {y | ‖perpendicularPart (normalize (q-x)) (y-x)‖ ≤ D+2*B*r}) ≤ F*μ P) :
    (∑ i ∈ C, μ (Q j i)) ≤ (θ⁻¹*F)*μ P := by
  classical
  by_cases hC : C.Nonempty
  · obtain ⟨i,hi⟩ := hC
    obtain ⟨q,hqQ,hq,hqne,_hqB,hqcap⟩ := hhit i hi
    let T : Set (Space d) := {y | ‖perpendicularPart (normalize (q-x)) (y-x)‖ ≤ D+2*B*r}
    apply density_hit_children_charge μ (Prod.mk x ⁻¹' G) P T
      (hG.preimage (by fun_prop)) (Q j) C hQ hdisj hθ hθtop
    · intro i hi
      obtain ⟨z,hzQ,hz,_hzne,_hzB,_hzcap⟩ := hhit i hi
      exact multiscaleFiber_retained μ G Q I θ J hz hj (hCI hi) hzQ
    · intro i hi y hy
      obtain ⟨z,hzQ,_hz,_hzne,hzB,hzcap⟩ := hhit i hi
      exact ⟨hparent i hi hy.1,
        radial_cap_child_tube x z q y u hqne hzB hzcap hqcap (hdiam i hi y hy.1 z hzQ)⟩
    · exact htest q (hparent i hi hqQ) hq hqne hqcap
  · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    simp only [he,Finset.sum_empty,zero_le]

end Falconer

end OAI
