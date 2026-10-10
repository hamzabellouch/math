import OAI.MeasureTheory.Falconer.Graphs.GraphWeightDerivatives

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def graphAmplitudePullback (b : Fin 4 → Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (distance plus : Bool) (axis δ : ℝ) (j k : ℕ)
    (Ψ : ℝ → ℝ) (p : Plane × ℝ) : ℂ :=
  graphShellJacobian Ψ p * graphFourAmplitude b
    (graphSourceWeight distance plus axis (angularBinCount δ) j k) x
      (sourceUnitDirection (graphPlaneAngle p.1+Real.arctan p.2))
      (sourceUnitDirection (graphPlaneAngle p.1-Real.arctan p.2+graphSourceChartAxis distance plus))

theorem graphAmplitudePullback_factorization (b : Fin 4 → Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (distance plus : Bool) (axis δ : ℝ) (j k : ℕ)
    (Ψ : ℝ → ℝ) (p : Plane × ℝ) :
    graphAmplitudePullback b x distance plus axis δ j k Ψ p =
      (graphShellJacobian Ψ p * graphWeightPullback distance plus axis δ j k p) *
        graphFourSymbolProduct (fun a => graphAngularPullback
          (fun θ => b a (x a) (sourceUnitDirection θ))
          (decide (a.val < 2)) (if a.val < 2 then 0 else graphSourceChartAxis distance plus)) p := by
  norm_num [graphAmplitudePullback, graphFourAmplitude, graphWeightPullback,
    graphFourSymbolProduct, graphAngularPullback, ← sub_eq_add_neg]
  ring

theorem uniform_actual_four_symbol_budget {sig : ℝ} (hsig : 0 < sig) (K n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ a, DecidableEq (ι a)],
    ∀ (S : ∀ a, Finset (ι a)) (d : ∀ a, ι a → PolicyDescriptor) (k : ∀ a, ι a → ℕ),
    (∀ a, (S a).card ≤ (N+1)^3+1) → (∀ a, (∑ t ∈ S a, k a t) ≤ K) →
    ∀ L : ℕ, (∀ a t, t ∈ S a → descriptorLength (d a t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ a, 0 < (Q a).side) →
    ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Fin 4 → Plane → ℂ) (x : Fin 4 → Plane),
    (∀ a, ‖h a (x a)‖ ≤ 1) → ∀ (plus : Fin 4 → Bool) (c : Fin 4 → ℝ),
    let F := fun a => graphAngularPullback
      (fun θ => inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (mass a)
        N lam sig J i (h a) (x a) (sourceUnitDirection θ)) (plus a) (c a)
    GraphDerivativeBound n (graphFourSymbolProduct F) A (sourceSymbolScale N sig L) := by
  choose A hA N₀ hb using fun j => uniform_actual_graph_four_symbols hsig K j
  let C := ∑ j ∈ Finset.range (n+1), A j
  refine ⟨C,Finset.sum_nonneg (fun j _ => hA j),(Finset.range (n+1)).sup N₀,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass lam J i h x hx plus c
  dsimp only
  let F := fun a => graphAngularPullback
    (fun θ => inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (mass a)
      N lam sig J i (h a) (x a) (sourceUnitDirection θ)) (plus a) (c a)
  have hF : ∀ a, ContDiffOn ℝ ∞ (F a) graphSmoothDomain := by
    intro a p hp
    apply (graphAngularPullback_contDiffAt
      (inheritedCircleSymbol_contDiff (S a) (d a) (k a) (Q a) (hQ a) (ρ a) (mass a)
        N lam sig J i (h a) (x a)) _ (plus a) (c a) hp).contDiffWithinAt
    intro θ
    exact congrArg (inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (mass a)
      N lam sig J i (h a) (x a)) (sourceUnitDirection_periodic θ)
  refine ⟨?_,?_⟩
  · exact ((hF 0).mul (Complex.conjCLE.contDiff.comp_contDiffOn (hF 1))).mul
      ((hF 2).mul (Complex.conjCLE.contDiff.comp_contDiffOn (hF 3)))
  · intro j hj η z hhi hz hlo
    have hjmem : j ∈ Finset.range (n+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    apply (hb j N ((Finset.le_sup hjmem).trans hN) S d k hcard hK L hL Q hQ ρ mass lam J i h x hx
      plus c η z hhi hz hlo).trans
    exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun l _ => hA l) hjmem)
      (pow_nonneg (sourceSymbolScale_pos _ _ _).le _)

theorem uniform_actual_graph_amplitude {sig : ℝ} (hsig : 0 < sig) (K n : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ a, DecidableEq (ι a)],
    ∀ (S : ∀ a, Finset (ι a)) (d : ∀ a, ι a → PolicyDescriptor) (k : ∀ a, ι a → ℕ),
    (∀ a, (S a).card ≤ (N+1)^3+1) → (∀ a, (∑ t ∈ S a, k a t) ≤ K) →
    ∀ L : ℕ, (∀ a t, t ∈ S a → descriptorLength (d a t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ a, 0 < (Q a).side) →
    ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Fin 4 → Plane → ℂ) (x : Fin 4 → Plane),
    (∀ a, ‖h a (x a)‖ ≤ 1) → ∀ δ : ℝ, 0 < δ → δ ≤ 2*Real.pi →
    ∀ (distance plus : Bool) (axis : ℝ) (j₁ j₂ : ℕ),
    let b := fun a => inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (mass a)
      N lam sig J i (h a)
    GraphDerivativeBound n (graphAmplitudePullback b x distance plus axis δ j₁ j₂ Ψ)
      A (1+4*max 1 δ⁻¹+sourceSymbolScale N sig L) := by
  obtain ⟨B,hB,N₀,hb⟩ := uniform_actual_four_symbol_budget hsig K n
  obtain ⟨W,hW,hw⟩ := graph_source_weight_derivative_budget n
  obtain ⟨Jc,hJc,hjc⟩ := graph_fixed_derivative_budget
    (fun _ hp => graphShellJacobian_contDiffAt hΨ hp) n
  refine ⟨(Jc*W)*B,mul_nonneg (mul_nonneg hJc hW) hB,N₀,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass lam J i h x hx δ hδ hcap distance plus axis j₁ j₂
  dsimp only
  have hfour := hb N hN S d k hcard hK L hL Q hQ ρ mass lam J i h x hx
    (fun a => decide (a.val < 2)) (fun a => if a.val < 2 then 0 else graphSourceChartAxis distance plus)
  have hD := sourceSymbolScale_pos N sig L
  have hweight := hjc.mul (hw δ hδ hcap distance plus axis j₁ j₂) hJc hW zero_le_one (by positivity)
  have hall := hweight.mul hfour (mul_nonneg hJc hW) hB (by positivity) hD.le
  exact hall.congr (fun p _ => graphAmplitudePullback_factorization _ x distance plus axis δ j₁ j₂ Ψ p)

end PlanarFalconer

end OAI
