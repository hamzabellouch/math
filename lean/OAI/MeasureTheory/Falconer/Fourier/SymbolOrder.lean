import OAI.MeasureTheory.Falconer.Geometry.FixedChartBounds
import OAI.MeasureTheory.Falconer.Estimates.QuadraticBudget

namespace OAI

/-! # Derivative order of the separated angular factors

A fixed smooth multiplier or chart substitution preserves the order
charged to the original symbol. A directional derivative charges one
order. Constants are uniform in the symbol and its scale, on each fixed
compact angular set.
-/

namespace Falconer
open Set
open scoped ContDiff

variable {X V E H : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

structure SymbolOrder (B : X → V → ℂ) (F : X → E → ℂ) (q : ℕ) : Prop where
  smooth : ∀ x, ContDiff ℝ ∞ (F x)
  bound : ∀ K : Set E, IsCompact K → ∀ r : ℕ, ∃ A : ℝ, 0 ≤ A ∧
    ∀ x C D, 0 ≤ C → 1 ≤ D →
      (∀ l ≤ r+q, ∀ w, ‖iteratedFDeriv ℝ l (B x) w‖ ≤ C*D^l) →
      ∀ z ∈ K, ‖iteratedFDeriv ℝ r (F x) z‖ ≤ A*C*D^(r+q)

namespace SymbolOrder

theorem base (B : X → V → ℂ) (hB : ∀ x, ContDiff ℝ ∞ (B x)) :
    SymbolOrder B B 0 := by
  refine ⟨hB,?_⟩
  intro K _ r
  refine ⟨1,zero_le_one,?_⟩
  intro x C D _ _ hb z _
  simpa only [Nat.add_zero,one_mul] using hb r (by omega) z

theorem mono {B : X → V → ℂ} {F : X → E → ℂ} {p q : ℕ}
    (h : SymbolOrder B F p) (hpq : p ≤ q) : SymbolOrder B F q := by
  refine ⟨h.smooth,?_⟩
  intro K hK r
  obtain ⟨A,hA,hAb⟩ := h.bound K hK r
  refine ⟨A,hA,?_⟩
  intro x C D hC hD hb z hz
  apply (hAb x C D hC hD (fun l hl w => hb l (by omega) w) z hz).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA hC)
  exact pow_le_pow_right₀ hD (by omega)

theorem derivative {B : X → V → ℂ} {F : X → E → ℂ} {q : ℕ}
    (h : SymbolOrder B F q) (v : E) :
    SymbolOrder B (fun x z => fderiv ℝ (F x) z v) (q+1) := by
  refine ⟨fun x => ((h.smooth x).fderiv_right (by simp)).clm_apply contDiff_const,?_⟩
  intro K hK r
  obtain ⟨A,hA,hAb⟩ := h.bound K hK (r+1)
  refine ⟨‖v‖*A,mul_nonneg (norm_nonneg _) hA,?_⟩
  intro x C D hC hD hb z hz
  have hf : ContDiff ℝ ∞ (fderiv ℝ (F x)) := (h.smooth x).fderiv_right (by simp)
  have hh := norm_iteratedFDeriv_clm_apply_const (c := v) (n := r) (hf.contDiffAt (x := z)) (by simp)
  rw [norm_iteratedFDeriv_fderiv] at hh
  apply (hh.trans (mul_le_mul_of_nonneg_left
    (hAb x C D hC hD (fun l hl w => hb l (by omega) w) z hz) (norm_nonneg v))).trans_eq
  rw [show r+1+q = r+(q+1) by omega]
  ring

theorem mul_fixed {B : X → V → ℂ} {F : X → E → ℂ} {q : ℕ}
    (h : SymbolOrder B F q) (c : E → ℂ) (hc : ContDiff ℝ ∞ c) :
    SymbolOrder B (fun x z => c z*F x z) q := by
  refine ⟨fun x => hc.mul (h.smooth x),?_⟩
  intro K hK r
  obtain ⟨Q,hQ,hQb⟩ := compact_iteratedFDeriv_bound hc hK r
  choose A hA hAb using fun k => h.bound K hK k
  let U := ∑ k ∈ Finset.range (r+1), A k
  have hU : 0 ≤ U := Finset.sum_nonneg (fun k _ => hA k)
  have hAU (k : ℕ) (hk : k ≤ r) : A k ≤ U :=
    Finset.single_le_sum (fun k _ => hA k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  refine ⟨2^r*Q*U,by positivity,?_⟩
  intro x C D hC hD hb z hz
  have hFbound (k : ℕ) (hk : k ≤ r) :
      ‖iteratedFDeriv ℝ k (F x) z‖ ≤ U*C*D^(r+q) := by
    apply (hAb k x C D hC hD (fun l hl w => hb l (by omega) w) z hz).trans
    apply mul_le_mul
      (mul_le_mul_of_nonneg_right (hAU k hk) hC)
      (pow_le_pow_right₀ hD (by omega)) (pow_nonneg (zero_le_one.trans hD) _)
      (mul_nonneg hU hC)
  have hh := mixed_product_uniform_bound_at hc.contDiffAt (h.smooth x).contDiffAt
    hQ (mul_nonneg (mul_nonneg hU hC) (pow_nonneg (zero_le_one.trans hD) _)) r
    (fun k hk => hQb k hk z hz) hFbound
  apply hh.trans_eq
  ring

theorem pullback {B : X → V → ℂ} {F : X → E → ℂ} {q : ℕ}
    (h : SymbolOrder B F q) (g : H → E) (hg : ContDiff ℝ ∞ g) :
    SymbolOrder B (fun x => F x ∘ g) q := by
  refine ⟨fun x => (h.smooth x).comp hg,?_⟩
  intro K hK r
  obtain ⟨Q,hQ,hQb⟩ := compact_iteratedFDeriv_bound hg hK r
  choose A hA hAb using fun k => h.bound (g '' K) (hK.image hg.continuous) k
  let U := ∑ k ∈ Finset.range (r+1), A k
  have hU : 0 ≤ U := Finset.sum_nonneg (fun k _ => hA k)
  have hAU (k : ℕ) (hk : k ≤ r) : A k ≤ U :=
    Finset.single_le_sum (fun k _ => hA k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  refine ⟨mixedCompositionBudget (fun _ => Q) r*U,
    mul_nonneg (mixedCompositionBudget_nonneg (fun _ => hQ) _) hU,?_⟩
  intro x C D hC hD hb z hz
  have hFbound (k : ℕ) (hk : k ≤ r) :
      ‖iteratedFDeriv ℝ k (F x) (g z)‖ ≤ U*C*D^(r+q) := by
    apply (hAb k x C D hC hD (fun l hl w => hb l (by omega) w)
      (g z) ⟨z,hz,rfl⟩).trans
    apply mul_le_mul
      (mul_le_mul_of_nonneg_right (hAU k hk) hC)
      (pow_le_pow_right₀ hD (by omega)) (pow_nonneg (zero_le_one.trans hD) _)
      (mul_nonneg hU hC)
  have hh := mixed_composition_derivative_bound hg.contDiffAt (h.smooth x).contDiffAt
    (B := fun _ => Q) (C := U*C*D^(r+q)) (D := 1)
    (by positivity) r hFbound (fun k _ hk => by simpa using hQb k hk z hz)
  apply hh.trans_eq
  simp only [one_pow,mul_one]
  ring

end SymbolOrder
end Falconer

end OAI
