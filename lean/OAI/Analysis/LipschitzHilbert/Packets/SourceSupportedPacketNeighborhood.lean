import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketContinuity
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedLineNeighborhood

namespace OAI

/-! The source neighborhood estimate needs only the lengths of actual packets.
Empty scales impose no condition on the reference window; all constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform ENNReal

namespace LipschitzHilbert

theorem packet_interval_neighborhood_of_supported (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)]
      (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
      (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (frequency : κ → ℝ)
      (P : Fin 2 → ℝ → LinePacketFamily N κ ι) (C B c r : ℝ),
      0 < C → 0 ≤ B → 0 < r →
      (∀ i y, (P i y).constant = C) →
      (∀ i y, (P i y).HasLocalBudget B) →
      (∀ i y j u k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 ((P i y).wave j u k) ξ = 0) →
      (∀ i y j u k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 ((P i y).wave j u k) ξ = 0) →
      (∀ i y j u, coeff j u = (P i y).coeff j u) →
      (∀ y j u k x, wave j u k y x = (P 0 y).wave j u k x) →
      (∀ y j u k x, (4*r:ℂ)*(deriv (fun t => wave j u k t x) y -
        (frequency k:ℂ)*Complex.I*wave j u k y x) = (P 1 y).wave j u k x) →
      (∀ j u k, Continuous (fun z : ℝ × ℝ => wave j u k z.1 z.2)) →
      (∀ j u k x t, DifferentiableAt ℝ (fun y => wave j u k y x) t) →
      (∀ j u k, Continuous (fun z : ℝ × ℝ =>
        deriv (fun t => wave j u k t z.2) z.1 -
          (frequency k:ℂ)*Complex.I*wave j u k z.1 z.2)) →
      ∀ (grid : FiniteLineGrid), 1 < grid.branching →
      (∀ i y j (_u : ι j), (P i y).length j ≤ grid.width) →
      ∀ n : ℕ, 1 ≤ n →
      let K := lineMomentBase C (A*C^2*B+1) grid.branching
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ bad ⊆ grid.root ×ˢ Icc (c-r) (c+r) ∧
        (volume.prod volume) bad ≤ 2*(1/4:ℝ≥0∞)^n*grid.lineMeasure univ*ENNReal.ofReal (2*r) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ x z v,
          x ∈ grid.root → |z-c| ≤ r → |v| ≤ r → (x,z) ∉ bad →
          ‖planarPacketInterval coeff wave a b x (z+v)‖ ≤ 8*K*(n:ℝ) := by
  obtain ⟨A,hA,htop⟩ := uniform_line_neighborhood_of_supported hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ coeff wave frequency P C B c r hC hB hr hconstant hbudget
    hlow hhigh hcoeff hwave hcov hcont hdiff hD grid hb hwidth n hn
  dsimp only
  let α := {p : ℕ × ℕ // p.1 ≤ p.2 ∧ p.2 ≤ N}
  let f : α → κ → ℝ → ℝ → ℂ := fun i k x y =>
    planarPacketInterval coeff wave i.val.1 i.val.2 x y k
  have hregular (i : Fin 2) : Continuous (fun z : ℝ × ℝ => (P i z.1).variation z.2) := by
    fin_cases i
    · exact lineFamily_variation_continuous coeff wave (P 0) hcont (hcoeff 0) hwave
    · apply lineFamily_variation_continuous coeff
        (fun j u k y x => (4*r:ℂ)*(deriv (fun t => wave j u k t x) y -
          (frequency k:ℂ)*Complex.I*wave j u k y x)) (P 1)
      · intro j u k
        exact continuous_const.mul (hD j u k)
      · exact hcoeff 1
      · exact hcov
  have hf (i : α) (x y : ℝ) (_hy : y ∈ Icc (c-2*r) (c+2*r)) (k : κ) :
      DifferentiableAt ℝ (f i k x) y :=
    planarPacketInterval_component_differentiable coeff wave _ _ x y k (fun j u => hdiff j u k x y)
  have hmem (i : α) (x : ℝ) : MemLp (covariantSignal frequency (fun k => f i k x)) 2
      (volume.restrict (Icc (c-2*r) (c+2*r))) :=
    planarPacketInterval_covariant_memLp coeff wave frequency hdiff hD _ _ x _ _
  have hv (i : α) (x y : ℝ) (_hy : y ∈ Icc (c-2*r) (c+2*r)) :
      ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ ≤ (P 0 y).variation x := by
    change ‖planarPacketInterval coeff wave i.val.1 i.val.2 x y‖ ≤ _
    exact planarPacketInterval_norm_le coeff wave (P 0 y) y (hcoeff 0 y) (hwave y)
      _ _ i.property.1 i.property.2 x
  have hd (i : α) (x y : ℝ) (_hy : y ∈ Icc (c-2*r) (c+2*r)) :
      4*r*‖covariantSignal frequency (fun k => f i k x) y‖ ≤ (P 1 y).variation x :=
    planarPacketInterval_scaled_covariant_norm_le coeff wave (P 1 y) frequency (4*r) y
      (by positivity) (hcoeff 1 y) (by simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hcov y)
      hdiff _ _ i.property.1 i.property.2 x
  obtain ⟨bad,hbad,hsub,harea,hpoint⟩ := htop N κ ι α P C B hC hB hconstant hbudget
    hlow hhigh hregular grid hb hwidth frequency f c r hr hf hmem hv hd n hn
  refine ⟨bad,hbad,hsub,harea,?_⟩
  intro a b hab hbn x z v hx hz hv hout
  exact hpoint ⟨(a,b),hab,hbn⟩ x z v hx hz hv hout

end LipschitzHilbert

end

end OAI
