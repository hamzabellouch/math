import OAI.MeasureTheory.Falconer.Angular.DyadicPerpendicular
import OAI.MeasureTheory.Falconer.Angular.DyadicLongitudinal
import OAI.MeasureTheory.Falconer.Angular.CapPairSymmetry
import OAI.MeasureTheory.Falconer.Graphs.DyadicGraph

namespace OAI

/-!
# All failed geometric tests for an original cell pair

For probability starting laws the four restricted masses are at most one.
Each discarded edge fails one of the two perpendicular tests or the
longitudinal test. The estimate below is derived from those three cases.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem four_restrictions_mass_le_one {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s₁ s₂ : Set X) (t₁ t₂ : Set Y) :
    (((μ.restrict s₁).prod (μ.restrict s₂)).prod
      ((ν.restrict t₁).prod (ν.restrict t₂))).real univ ≤ 1 := by
  have hle : ((μ.restrict s₁).prod (μ.restrict s₂)).prod
      ((ν.restrict t₁).prod (ν.restrict t₂)) ≤ (μ.prod μ).prod (ν.prod ν) :=
    Measure.prod_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
      (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
  have ht : (((μ.restrict s₁).prod (μ.restrict s₂)).prod
      ((ν.restrict t₁).prod (ν.restrict t₂))) univ ≤ 1 := by
    simpa using hle univ
  exact (ENNReal.toReal_mono (by simp) ht).trans_eq (by simp)

theorem dyadic_failed_tests_bound
    (hpublished : PublishedGnomonicSurface) (n m : ℕ) (hn : 1 ≤ n)
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ (Q₁ Q₂ : DyadicCube (n+2)), 0 < Q₁.side → Q₂.side = Q₁.side →
      ∀ (μ ν : Measure (Space (n+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (j : ℕ) (row col : List (Fin (n+2) → Bool) × List (Fin (n+2) → Bool)),
      row.1.length = j → col.1.length = j → row.2.length = j → col.2.length = j →
      ∀ R : ℝ, 1 ≤ R → ∀ (v τ δ H B D : ℝ), 0 < τ → 0 < δ → δ ≤ 1/2 →
      0 ≤ H → 0 ≤ B → 1 ≤ D → δ⁻¹ ≤ D →
      Real.sqrt (n+2 : ℕ)*Q₁.side ≤ (τ/4)*D →
      2*Real.sqrt (n+2 : ℕ)*(Q₁.side/(2 : ℝ)^j)+8*δ*(Real.sqrt (n+2 : ℕ)*Q₁.side) ≤ τ/4 →
      4*Real.pi*R^α ≤ (2 : ℝ)^v*τ →
      ∀ (M₁ M₂ : ℝ), 0 < M₁ → 0 < M₂ →
      ∀ (w₁ w₂ : Sphere (n+2)) (η θ : Sphere (n+2) → ℝ),
      ChartCapControl m η (w₁ : Space (n+2)) δ H →
      ChartCapControl m θ (w₂ : Space (n+2)) δ H →
      ∀ (b c : Space (n+2) → Sphere (n+2) → ℂ),
      ChartSymbolControl m b B D → ChartSymbolControl m c B D →
      ¬retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ row col →
      ‖endpointCapCrossTerm (μ.restrict (Q₁.descendant row.1).carrier)
        (μ.restrict (Q₁.descendant col.1).carrier) (ν.restrict (Q₂.descendant row.2).carrier)
        (ν.restrict (Q₂.descendant col.2).carrier) M₁ M₁ M₂ M₂ v Ψ b b c c η θ‖ ≤
      |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
        (A*(4^m*H*B*B)*(B*B)*(sphereMeasure (n+2)).real univ) *
          (16*D/((2 : ℝ)^v*τ))^m*(4*W) +
      |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
        ((B*B)*(B*B)*C*((sphereMeasure (n+2)).real univ)^2*R^(-T)) := by
  obtain ⟨A,hA,hperp⟩ := dyadic_perpendicular_cross_term hpublished n m hn
  have hz : ∀ t, 4 < t → Ψ t = 0 := by
    intro t ht
    by_contra hne
    exact (not_lt_of_ge (hsupp t hne).2.le) ht
  obtain ⟨C,hC,hlong⟩ := dyadic_longitudinal_cross_term φ Ψ hφ hΨ hpos hzero hW hΨW hz hα T
  refine ⟨A,C,hA,hC,?_⟩
  intro Q₁ Q₂ hQ hside μ ν _ _ j row col hr₁ hc₁ hr₂ hc₂ R hR v τ δ H B D
    hτ hδ hδsmall hH hB hD hδD hnorm herr hfreq M₁ M₂ hM₁ hM₂ w₁ w₂ η θ hη hθ b c hb hc hbad
  let EP := |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
    (A*(4^m*H*B*B)*(B*B)*(sphereMeasure (n+2)).real univ) *
      (16*D/((2 : ℝ)^v*τ))^m*(4*W)
  let EL := |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
    ((B*B)*(B*B)*C*((sphereMeasure (n+2)).real univ)^2*R^(-T))
  have hEP : 0 ≤ EP := by dsimp [EP]; positivity
  have hEL : 0 ≤ EL := by dsimp [EL]; positivity
  have herr' : 2*Real.sqrt (n+2 : ℕ)*(Q₁.side/(2 : ℝ)^j)+
      8*δ*(Real.sqrt (n+2 : ℕ)*Q₁.side) ≤ τ/2 := by linarith
  have hbad' : ¬retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ col row :=
    fun he => hbad ((retainedDyadicEdge_symm Q₁ Q₂ w₁ w₂ τ row col).mpr he)
  by_cases hfirst : ‖perpendicularPart (w₁ : Space (n+2))
      ((Q₁.descendant row.1).center-(Q₁.descendant col.1).center)‖ ≤ τ
  · by_cases hsecond : ‖perpendicularPart (w₂ : Space (n+2))
        ((Q₂.descendant row.2).center-(Q₂.descendant col.2).center)‖ ≤ τ
    · have hthird : τ < |inner ℝ (w₁ : Space (n+2))
          ((Q₁.descendant row.1).center-(Q₁.descendant col.1).center)+
          inner ℝ (w₂ : Space (n+2))
          ((Q₂.descendant row.2).center-(Q₂.descendant col.2).center)| := by
        apply lt_of_not_ge
        intro hle
        exact hbad' ⟨hfirst,hsecond,hle⟩
      have he := hlong Q₁ Q₂ hQ (hside.symm ▸ hQ) μ ν j row col hr₁ hc₁ hr₂ hc₂
        R hR v τ δ hδ.le hfreq (by rw [hside]; linarith) w₁ w₂ hthird
        η θ hη.measurable hθ.measurable hη.bound hθ.bound hη.support hθ.support
        b c hb.measurable hc.measurable B hB hb.bound hc.bound M₁ M₂
      have hmass := four_restrictions_mass_le_one μ ν
        (Q₁.descendant row.1).carrier (Q₁.descendant col.1).carrier
        (Q₂.descendant row.2).carrier (Q₂.descendant col.2).carrier
      apply he.trans
      calc
        _ = EL * (((μ.restrict (Q₁.descendant row.1).carrier).prod
          (μ.restrict (Q₁.descendant col.1).carrier)).prod
          ((ν.restrict (Q₂.descendant row.2).carrier).prod
          (ν.restrict (Q₂.descendant col.2).carrier))).real univ := by dsimp [EL]; ring
        _ ≤ EL := mul_le_of_le_one_right hEL hmass
        _ ≤ EP+EL := le_add_of_nonneg_left hEP
    · have he := hperp Q₂ Q₁ (hside.symm ▸ hQ) ν μ j (row.2,row.1) (col.2,col.1)
        hr₂ hc₂ w₂ τ δ H B D hτ hδ hδsmall hH hB hD hδD
        (by simpa only [hside] using hnorm) (by simpa only [hside] using herr')
        (lt_of_not_ge hsecond) θ η hθ hη.measurable hη.bound c b hc hb.measurable hb.bound
        M₂ M₁ v Ψ hM₂ hM₁ hΨ hsupp W hW hΨW
      have hmass := four_restrictions_mass_le_one ν μ
        (Q₂.descendant row.2).carrier (Q₂.descendant col.2).carrier
        (Q₁.descendant row.1).carrier (Q₁.descendant col.1).carrier
      rw [endpointCapCrossTerm_swap]
      apply he.trans
      calc
        _ = EP * (((ν.restrict (Q₂.descendant row.2).carrier).prod
          (ν.restrict (Q₂.descendant col.2).carrier)).prod
          ((μ.restrict (Q₁.descendant row.1).carrier).prod
          (μ.restrict (Q₁.descendant col.1).carrier))).real univ := by
            dsimp [EP]
            rw [mul_comm (M₂⁻¹*M₂⁻¹) (M₁⁻¹*M₁⁻¹)]
            ring
        _ ≤ EP := mul_le_of_le_one_right hEP hmass
        _ ≤ EP+EL := le_add_of_nonneg_right hEL
  · have he := hperp Q₁ Q₂ hQ μ ν j row col hr₁ hc₁ w₁ τ δ H B D
      hτ hδ hδsmall hH hB hD hδD hnorm herr' (lt_of_not_ge hfirst) η θ
      hη hθ.measurable hθ.bound b c hb hc.measurable hc.bound M₁ M₂ v Ψ hM₁ hM₂ hΨ hsupp W hW hΨW
    have hmass := four_restrictions_mass_le_one μ ν
      (Q₁.descendant row.1).carrier (Q₁.descendant col.1).carrier
      (Q₂.descendant row.2).carrier (Q₂.descendant col.2).carrier
    apply he.trans
    calc
      _ = EP * (((μ.restrict (Q₁.descendant row.1).carrier).prod
        (μ.restrict (Q₁.descendant col.1).carrier)).prod
        ((ν.restrict (Q₂.descendant row.2).carrier).prod
        (ν.restrict (Q₂.descendant col.2).carrier))).real univ := by dsimp [EP]; ring
      _ ≤ EP := mul_le_of_le_one_right hEP hmass
      _ ≤ EP+EL := le_add_of_nonneg_right hEL

end Falconer

end OAI
