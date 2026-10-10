import OAI.MeasureTheory.Falconer.Estimates.EndpointOriginalMiddle
import OAI.MeasureTheory.Falconer.Estimates.SourceClassMiddleData

namespace OAI

/-! # The endpoint middle estimate for an actual regularized source cell -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem endpoint_source_class_middle_pruning (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ : ℝ} (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2)
    (hζ : 0 < ζ) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀,
      ∀ (Q : DyadicCube (h+3)), Q.side = 1 →
      ∀ (μ ν : Measure (Space (h+3))) [IsProbabilityMeasure μ] [IsFiniteMeasure ν],
      ν univ ≤ 1 → ∀ N B : ℕ, 0 < N → 0 < B →
      ∀ lam E σ : ℝ, 0 ≤ E → 0 ≤ lam → 0 < σ → σ ≤ 1 → σ*Real.sqrt (h+3:ℕ) ≤ 1/4 →
      (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ p v : ℕ, p ≤ v → v ≤ N → M ≤ v-p →
      ∀ P : CellPath (h+3), P.length = p →
      0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier →
      (∀ n, p ≤ n → n ≤ v →
        t*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p) →
      (((((2*Nat.ceil (2+4*Real.sqrt (h+3:ℕ))+1)^(h+3):ℕ):ℝ)*(2:ℝ)^t*
        ((2:ℝ)^N)^(E+2*(((h+3:ℕ):ℝ)+1)*lam))*σ^(-t)) ≤ (1/(2:ℝ)^M)^(-ε) →
      ∀ (_w₀ : Sphere (h+3)) (G : Set (Space (h+3) × Space (h+3))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ z ∈ (Q.descendant P).carrier) →
      (∀ᵐ z ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier,
        (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ M →
          ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+3)) < 1/(2:ℝ)^j} ≤
            ENNReal.ofReal ((1/(2:ℝ)^M)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) ∧
        (∀ w : Sphere (h+3), ∀ u : ℝ, 1/(2:ℝ)^M ≤ u → u ≤ 1 →
          ν {x | (z,x) ∈ G ∧ |inner ℝ (w:Space (h+3)) (normalize (x-z))| ≤ u} ≤
            ENNReal.ofReal ((1/(2:ℝ)^M)^(-ε)*u^ζ))) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/((σ*(2:ℝ)^p)*r) ≤ 1/(2:ℝ)^M →
      ((σ*(2:ℝ)^p)*H)*θ ≤ 1/(2:ℝ)^M →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖(Q.descendant P).center-x‖ ∧
        ∀ᵐ y ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+3) × Space (h+3)), MeasurableSet G' ∧ G' ⊆ G ∧
        ((ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier).prod ν)
          (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^M)^b) ∧
        ∀ z ∈ G', radialCollisionMass
          (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier) θ z ≤
            ENNReal.ofReal ((1/(2:ℝ)^M)^((h+1:ℝ)+b/2)) := by
  obtain ⟨ε,b,hε,hb,M₀,hM₀⟩ := endpoint_original_middle_pruning hLW ht ht' hζ
  refine ⟨ε,b,hε,hb,M₀,?_⟩
  intro M hM Q hQ μ ν _ _ hν N B hN hB lam E σ hE hlam hσ hσ1 hsmall hwidth hlarge
    p₀ hp₀ p v hpv hvN hMv P hP hpos hinc hcoef w₀ G hG hgeom hcap r H θ hr hfreeze hwidth' hpin
  have ht0 : 0 ≤ t := by have hh : (0:ℝ) ≤ h := Nat.cast_nonneg h; linarith
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have : IsProbabilityMeasure (ProbabilityTheory.cond (sourceClass Q μ N B p₀)
      (Q.descendant P).carrier) := sourceClass_conditional_probability Q hside μ N B hp₀ P hpos
  have hdata := source_class_middle_data Q hQ μ hN hB ht0 hE hlam hσ hσ1 hsmall hwidth hlarge
    hp₀ hpv hvN hMv hP hpos hinc hcoef
  exact hM₀ M hM _ ν hν w₀ (Q.descendant P).center (σ*(2:ℝ)^p) (by positivity) G hG
    (fun z x hz => ⟨(hgeom z x hz).1,hdata.1 z (hgeom z x hz).2⟩)
    hdata.2.1 hdata.2.2 hcap r H θ hr hfreeze hwidth' hpin

end Falconer.Regularization

end OAI
