import OAI.MeasureTheory.Falconer.Radial.RegularClassRadialBudget
import OAI.MeasureTheory.Falconer.Radial.WeakRadialDeletionBudget

namespace OAI

/-! # Uniform small troublesome-pair mass for the original regularized class -/

namespace Falconer.Regularization
open Set Metric MeasureTheory
open scoped ENNReal
variable {n : ℕ}

theorem regular_class_small_troublesome (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (L : ℕ) {e τ η lam u v c Cp : ℝ}
    (hη : 0 ≤ η) (hCp : 0 ≤ Cp)
    (hτ : 2*(((n+1:ℕ):ℝ)+1)*lam < τ)
    (hgap : 0 < (n+1)*e-n*τ-η*n*(n+1)^2-n*u)
    (hu : c*((n+1:ℕ):ℝ) < u) (hv : c*((n+1:ℕ):ℝ) < v) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube (n+1)), 0 < Q.side →
      ∀ (μ ν : Measure (Space (n+1))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ B : ℕ, 0 < B →
      (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ a b : ℕ, a ≤ N → b ≤ N →
      ∀ p : CellPath (n+1), p.length = a →
        0 < sourceClass Q μ N B p₀ (Q.descendant p).carrier →
      ∀ r C Bs R : ℝ, 0 < r → C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ) →
        8*(Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^a))^2/r ≤ Q.side/(2:ℝ)^b →
        (∀ᵐ x ∂ν, ‖(Q.descendant p).center-x‖ ≤ R) →
        (∀ w : Space (n+1), ‖w‖ = 1 →
          ν {x | |inner ℝ w x-inner ℝ w (Q.descendant p).center| ≤ R*((2:ℝ)^N)^(-η)} ≤
            ENNReal.ofReal (Cp*((2:ℝ)^N)^(-v))) →
      ((ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant p).carrier).prod ν)
        (troublesomePair (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant p).carrier)
          (Q.descendant p).center r (Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^a)) Bs
            (C*(Q.side/(2:ℝ)^b))
            (ENNReal.ofReal (((2:ℝ)^N)^e /
              (((2:ℝ)^N)^(sourceProfile Q μ N B p₀ b-sourceProfile Q μ N B p₀ a))^((n:ℝ)/(n+1))))) ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  obtain ⟨N₁,h₁⟩ := eventually_radialClassBallBound_le n hτ
  obtain ⟨N₂,h₂⟩ := eventually_weak_radial_reciprocal_budget n
    (((2*L+1)^(n+1):ℕ):ℝ) (generalTubeCountConstant (n+1) ((n+1:ℕ):ℝ)) e τ η u hgap
  obtain ⟨N₃,h₃⟩ := weak_radial_local_deletion_budget (n+1) (by omega) hCp hu hv
  refine ⟨max 1 (max N₁ (max N₂ N₃)),?_⟩
  intro N hN Q hQ μ ν _ _ B hB hwidth hlarge p₀ hp₀ a b ha hb p hp hpos r C Bs R hr hL hfreeze hR hslab
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : 0 < 1) ((le_max_left _ _).trans hN)
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN₃ : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  let R₀ : ℝ := (2:ℝ)^N
  let D : ℝ := R₀^(sourceProfile Q μ N B p₀ b-sourceProfile Q μ N B p₀ a)
  have hR₀ : 0 < R₀ := by dsimp [R₀]; positivity
  have hD : 0 < D := Real.rpow_pos_of_pos hR₀ _
  have hH := h₁ N hN₁ Q μ B p₀ a b
  have hHpos : 0 ≤ radialClassBallBound Q μ N B p₀ a b lam := by
    unfold radialClassBallBound
    positivity
  have hbudget : (((2*L+1)^(n+1):ℕ)/(R₀^e/D^((n:ℝ)/(n+1))))^(n+1)*
      (generalTubeCountConstant (n+1) ((n+1:ℕ):ℝ)/(R₀^(-η))^(n+1))^(n*(n+1))*
        (radialClassBallBound Q μ N B p₀ a b lam)^n ≤ (R₀^(-u))^n := by
    have hG : 0 ≤ generalTubeCountConstant (n+1) ((n+1:ℕ):ℝ) := by
      unfold generalTubeCountConstant
      positivity
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hHpos hH n) (by positivity)).trans
    exact h₂ N hN₂ D hD
  have hh := regular_class_radial_incidence hLW hn Q hQ μ ν hNpos hB hwidth hlarge hp₀
    ha hb hp hpos (Bs := Bs) hr (show 0 < R₀^e/D^((n:ℝ)/(n+1)) by positivity)
    (Real.rpow_pos_of_pos hR₀ (-η))
    (Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ (by norm_num)) (neg_nonpos.mpr hη))
    hfreeze hR (ENNReal.ofReal (Cp*R₀^(-v))) hslab L hL
    (Real.rpow_nonneg hR₀.le (-u)) hbudget
  apply h₃ N hN₃
  simpa only [R₀,D,Nat.cast_add,Nat.cast_one] using hh

end Falconer.Regularization

end OAI
