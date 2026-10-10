import OAI.MeasureTheory.Falconer.Graphs.GraphActualMixedDerivatives
import OAI.MeasureTheory.Falconer.Estimates.FrechetProductScale

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

def graphSmoothDomain : Set (Plane × ℝ) := {p | p.1 ≠ 0}

theorem graphSmoothDomain_isOpen : IsOpen graphSmoothDomain :=
  isOpen_ne_fun continuous_fst continuous_const

noncomputable def graphFourSymbolProduct (F : Fin 4 → (Plane × ℝ) → ℂ)
    (p : Plane × ℝ) : ℂ := (F 0 p * conj (F 1 p)) * (F 2 p * conj (F 3 p))

theorem graph_four_symbol_product_scale (F : Fin 4 → (Plane × ℝ) → ℂ)
    (hF : ∀ a, ContDiffOn ℝ ∞ (F a) graphSmoothDomain)
    {p : Plane × ℝ} (hp : p ∈ graphSmoothDomain) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (n : ℕ)
    (hb : ∀ a j, j ≤ n → ‖iteratedFDeriv ℝ j (F a) p‖ ≤ C*D^j) :
    ‖iteratedFDeriv ℝ n (graphFourSymbolProduct F) p‖ ≤ C^4*(4*D)^n := by
  have hconj (a) : ContDiffOn ℝ ∞ (fun q => conj (F a q)) graphSmoothDomain :=
    Complex.conjCLE.contDiff.comp_contDiffOn (hF a)
  have hpair (a b : Fin 4) (j : ℕ) (hj : j ≤ n) :
      ‖iteratedFDeriv ℝ j (fun q => F a q * conj (F b q)) p‖ ≤ C*C*(D+D)^j := by
    apply frechet_mul_scale_on graphSmoothDomain_isOpen (hF a) (hconj b) hp hC hC hD hD j
    · intro k hk
      exact hb a k (hk.trans hj)
    · intro k hk
      change ‖iteratedFDeriv ℝ k (fun q => star (F b q)) p‖ ≤ _
      rw [frechet_conj_norm]
      exact hb b k (hk.trans hj)
  have he := frechet_mul_scale_on graphSmoothDomain_isOpen
    ((hF 0).mul (hconj 1)) ((hF 2).mul (hconj 3)) hp
    (mul_nonneg hC hC) (mul_nonneg hC hC) (add_nonneg hD hD) (add_nonneg hD hD) n
    (hpair 0 1) (hpair 2 3)
  convert he using 1 <;> first | rfl | ring

theorem uniform_actual_graph_four_symbols {sig : ℝ} (hsig : 0 < sig) (K n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ a, DecidableEq (ι a)],
    ∀ (S : ∀ a, Finset (ι a)) (d : ∀ a, ι a → PolicyDescriptor) (k : ∀ a, ι a → ℕ),
    (∀ a, (S a).card ≤ (N+1)^3+1) → (∀ a, (∑ t ∈ S a, k a t) ≤ K) →
    ∀ L : ℕ, (∀ a t, t ∈ S a → descriptorLength (d a t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ a, 0 < (Q a).side) →
    ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Fin 4 → Plane → ℂ) (x : Fin 4 → Plane),
    (∀ a, ‖h a (x a)‖ ≤ 1) → ∀ (plus : Fin 4 → Bool) (c : Fin 4 → ℝ),
    ∀ (η : Plane) (z : ℝ), ‖η‖ ≤ 8 → |z| ≤ 4 → 1/8 ≤ ‖η‖ →
    let F := fun a => graphAngularPullback
      (fun θ => inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (mass a)
        N lam sig J i (h a) (x a) (sourceUnitDirection θ)) (plus a) (c a)
    ‖iteratedFDeriv ℝ n (graphFourSymbolProduct F) (η,z)‖ ≤ A*sourceSymbolScale N sig L^n := by
  choose A hA N₀ hb using fun j => uniform_actual_graph_symbol_mixed hsig K 0 j
  let C : ℝ := ∑ j ∈ Finset.range (n+1), A j
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => hA j)
  refine ⟨C^4*4^n,by positivity,(Finset.range (n+1)).sup N₀,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass lam J i h x hx plus c η z hhi hz hlo
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
  have hder : ∀ a j, j ≤ n → ‖iteratedFDeriv ℝ j (F a) (η,z)‖ ≤ C*sourceSymbolScale N sig L^j := by
    intro a j hj
    have hjmem : j ∈ Finset.range (n+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    have he := hb j N ((Finset.le_sup hjmem).trans hN) (S a) (d a) (k a) (hcard a)
      (hK a) L (hL a) (Q a) (hQ a) (ρ a) (mass a) lam J i (h a) (x a) (hx a)
      (plus a) (c a) η z hhi hz hlo
    simp only [iteratedDeriv_zero, Nat.zero_add] at he
    apply he.trans
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun l _ => hA l) hjmem)
      (pow_nonneg (sourceSymbolScale_pos _ _ _).le _)
  have hp : (η,z) ∈ graphSmoothDomain := norm_pos_iff.mp (by linarith)
  have he := graph_four_symbol_product_scale F hF hp hC (sourceSymbolScale_pos N sig L).le n hder
  convert he using 1
  first | rfl | (rw [mul_pow]; ring)

end PlanarFalconer

end OAI
