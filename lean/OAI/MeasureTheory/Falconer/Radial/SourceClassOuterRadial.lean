import OAI.MeasureTheory.Falconer.Radial.OuterRadialCell
import OAI.MeasureTheory.Falconer.Geometry.ConditionalCellGeometry

namespace OAI

/-! # Outer-interval pruning for the actual regularized conditional source laws -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem source_class_outer_radial_pruning (Q : DyadicCube d) (hQ : Q.side = 1)
    {D η₀ q : ℝ} (hD : 1 ≤ D) (hDdim : Real.sqrt d ≤ D)
    (hη₀ : 0 < η₀) (hq : 0 ≤ q) (C : ℝ) :
    ∃ J N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η →
      ∀ g v : ℕ, g+J ≤ v → v ≤ N →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ B : ℕ, 0 < N → 0 < B → ∀ lam E : ℝ,
      (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ P : CellPath d, P.length = g →
      0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier →
      (∀ n, g ≤ n → n ≤ v →
        q*(n-g:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ g) →
      (((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^q*
        ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam) ≤ ((2:ℝ)^N)^η →
      ∀ G : Set (Space d × Space d), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ z x, (z,x) ∈ G → ∀ y ∈ (Q.descendant P).carrier, ‖y-x‖ ≤ D) →
      (∀ᵐ z ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier,
        ∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^η*r^q)) →
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
        ((ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier).prod ν)
          (G \ H) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-(2*η))) ∧
        ∀ p ∈ H, radialCollisionMass
          (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)
          (C/(2:ℝ)^v) p ≤ ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^(v-g))^(-q)) := by
  obtain ⟨J,N₀,hN₀⟩ := outer_radial_cell_pruning (d := d) hD hη₀ hq C
  refine ⟨J,N₀,?_⟩
  intro N hN η hη g v hgv hvN μ ν _ _ B hNp hB lam E hwidth hlarge
    p₀ hp₀ P hP hpos hinc hcoef G hG hdiag hpin hcap
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have : IsProbabilityMeasure (ProbabilityTheory.cond (sourceClass Q μ N B p₀)
      (Q.descendant P).carrier) := sourceClass_conditional_probability Q hside μ N B hp₀ P hpos
  exact hN₀ N hN η hη g v hgv hvN _ ν G hG hdiag
    (conditional_cell_pair_geometry Q hQ _ P hP hDdim G hpin)
    (sourceClass_original_conditional_frostman_power Q hQ μ hNp hB hq hwidth hlarge
      hp₀ (by omega) hvN hP hpos hinc hcoef) hcap

end Falconer.Regularization

end OAI
