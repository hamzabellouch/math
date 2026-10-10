import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedPolynomialMoments
import OAI.Analysis.LipschitzHilbert.Estimates.NeighborhoodGeometric

namespace OAI

/-! The source neighborhood estimate needs only the lengths of actual packets.
Empty scales impose no condition on the reference window; all constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform ENNReal

namespace LipschitzHilbert

theorem uniform_line_neighborhood_of_supported (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (α : Type)
      (P : Fin 2 → ℝ → LinePacketFamily N κ ι) (C B : ℝ),
      0 < C → 0 ≤ B →
      (∀ i y, (P i y).constant = C) →
      (∀ i y, (P i y).HasLocalBudget B) →
      (∀ i y j u k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 ((P i y).wave j u k) ξ = 0) →
      (∀ i y j u k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 ((P i y).wave j u k) ξ = 0) →
      (∀ i, Continuous (fun z : ℝ × ℝ => (P i z.1).variation z.2)) →
      ∀ (grid : FiniteLineGrid), 1 < grid.branching →
      (∀ i y j (_u : ι j), (P i y).length j ≤ grid.width) →
      ∀ (frequency : κ → ℝ) (f : α → κ → ℝ → ℝ → ℂ) (c r : ℝ), 0 < r →
      (∀ i x y, y ∈ Icc (c-2*r) (c+2*r) → ∀ k, DifferentiableAt ℝ (f i k x) y) →
      (∀ i x, MemLp (covariantSignal frequency (fun k => f i k x)) 2
        (volume.restrict (Icc (c-2*r) (c+2*r)))) →
      (∀ i x y, y ∈ Icc (c-2*r) (c+2*r) →
        ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ ≤ (P 0 y).variation x) →
      (∀ i x y, y ∈ Icc (c-2*r) (c+2*r) →
        (4*r)*‖covariantSignal frequency (fun k => f i k x) y‖ ≤ (P 1 y).variation x) →
      ∀ n : ℕ, 1 ≤ n →
      let K := lineMomentBase C (A*C^2*B+1) grid.branching
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        bad ⊆ grid.root ×ˢ Icc (c-r) (c+r) ∧
        (volume.prod volume) bad ≤ 2*(1/4:ℝ≥0∞)^n*grid.lineMeasure univ*ENNReal.ofReal (2*r) ∧
        ∀ i x z v, x ∈ grid.root → |z-c| ≤ r → |v| ≤ r → (x,z) ∉ bad →
          ‖(WithLp.toLp 2 (fun k => f i k x (z+v)) : EuclideanSpace ℂ κ)‖ ≤ 8*K*(n:ℝ) := by
  obtain ⟨A,hA,hm⟩ := LinePacketFamily.uniform_polynomial_line_moment_of_supported hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ α P C B hC hB hconstant hbudget hlow hhigh hcont grid hb hwidth
    frequency f c r hr hf hmem hV hD n hn
  dsimp only
  let K := lineMomentBase C (A*C^2*B+1) grid.branching
  have hK : 0 < K := lineMomentBase_pos _ _ _ hC.le (Nat.cast_nonneg _)
  have hnR : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
  have hr4 : 0 < 4*r := by positivity
  let V : ℝ × ℝ → ℝ := fun z => (P 0 z.1).variation z.2
  let D : ℝ × ℝ → ℝ := fun z => (P 1 z.1).variation z.2/(4*r)
  have hscale (y x : ℝ) : 4*r*D (y,x) = (P 1 y).variation x := by
    dsimp [D]
    field_simp
  have hline (y : ℝ) : (∫⁻ x in grid.root, ENNReal.ofReal
      (V (y,x)^(2*n)+(4*r*D (y,x))^(2*n))) ≤
        2*(ENNReal.ofReal (K*(2*n:ℕ)))^(2*n)*grid.lineMeasure univ := by
    have hmoment (i : Fin 2) := hm N κ ι (P i y) B hB (hbudget i y)
      (hlow i y) (hhigh i y) grid hb (hwidth i y) (2*n) (by omega)
    have hv0 (x : ℝ) : 0 ≤ (P 0 y).variation x := cubicVariation_nonneg _ _
    have hv1 (x : ℝ) : 0 ≤ (P 1 y).variation x := cubicVariation_nonneg _ _
    simp_rw [hscale, V, ENNReal.ofReal_add (pow_nonneg (hv0 _) _) (pow_nonneg (hv1 _) _),
      ENNReal.ofReal_pow (hv0 _), ENNReal.ofReal_pow (hv1 _)]
    rw [lintegral_add_left ((P 0 y).continuous_variation.measurable.ennreal_ofReal.pow_const _)]
    have h0 := hmoment 0
    have h1 := hmoment 1
    rw [hconstant] at h0 h1
    change (∫⁻ x, _ ∂grid.lineMeasure) + (∫⁻ x, _ ∂grid.lineMeasure) ≤ _
    calc
      _ ≤ 2*ENNReal.ofReal ((K*(2*n:ℕ))^(2*n))*grid.lineMeasure univ := by
        have hsum := add_le_add h0 h1
        convert hsum using 1
        ring
      _ = _ := by rw [ENNReal.ofReal_pow (by positivity)]
  obtain ⟨bad,hbad,hsub,harea,hpoint⟩ := top_neighborhood_geometric frequency f V D
    (hcont 0) ((hcont 1).div_const _) grid.root measurableSet_Ico c r (K*(2*n:ℕ))
    hr (by positivity) n (grid.lineMeasure univ) hline hf hmem hV
    (by
      intro i x y hy
      apply (le_div_iff₀ hr4).mpr
      simpa only [mul_comm] using hD i x y hy)
  refine ⟨bad,hbad,hsub,harea,?_⟩
  intro i x z v hx hz hv hout
  convert hpoint i x z v hx hz hv hout using 1
  push_cast
  ring

end LipschitzHilbert

end

end OAI
