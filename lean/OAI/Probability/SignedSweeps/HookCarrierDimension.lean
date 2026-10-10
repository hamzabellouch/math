import OAI.Probability.SignedSweeps.HookDimension
import OAI.Probability.SignedSweeps.HookArms

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def coreHookProduct (q : ℕ) (lam : YoungDiagram) : ℕ :=
  ∏ c ∈ lam.cells.filter (fun c => c.1 < q ∧ c.2 < q), boxHook lam c.1 c.2

lemma coreHookProduct_le (q B : ℕ) (lam : YoungDiagram)
    (hB : 2 * lam.card ≤ B) (hB₁ : 1 ≤ B) :
    coreHookProduct q lam ≤ B ^ (q * q) := by
  let S := lam.cells.filter (fun c => c.1 < q ∧ c.2 < q)
  have hcard : S.card ≤ q * q := by
    have hs : S ⊆ Finset.range q ×ˢ Finset.range q := by
      intro c hc
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Finset.mem_filter.mp hc).2.1,
        Finset.mem_range.mpr (Finset.mem_filter.mp hc).2.2⟩
    simpa using Finset.card_le_card hs
  exact (Finset.prod_le_pow_card S _ B (fun c _ =>
    (boxHook_le_twice_card lam c.1 c.2).trans hB)).trans (Nat.pow_le_pow_right hB₁ hcard)

lemma rightHookProduct_transpose (q : ℕ) (lam : YoungDiagram) :
    rightHookProduct q lam.transpose =
      ∏ c ∈ lam.cells.filter (fun c => q ≤ c.1), boxHook lam c.1 c.2 := by
  unfold rightHookProduct
  rw [show lam.transpose.cells = lam.cells.map (Equiv.prodComm ℕ ℕ).toEmbedding from rfl,
    Finset.filter_map, Finset.prod_map]
  simp only [Equiv.coe_toEmbedding, Equiv.prodComm_apply, Prod.swap,
    boxHook_transpose, Function.comp_def]
  rfl

lemma hookProduct_core_arms {q : ℕ} (lam : YoungDiagram) (h : IsSignedHook q lam) :
    cellHookProduct lam = coreHookProduct q lam * rightHookProduct q lam *
      rightHookProduct q lam.transpose := by
  rw [rightHookProduct_transpose]
  have ht := Finset.prod_filter_mul_prod_filter_not lam.cells
    (fun c => c.1 < q) (fun c => boxHook lam c.1 c.2)
  have hh := Finset.prod_filter_mul_prod_filter_not
    (lam.cells.filter (fun c => c.1 < q)) (fun c => c.2 < q)
    (fun c => boxHook lam c.1 c.2)
  have hs : (lam.cells.filter (fun c => c.1 < q)).filter (fun c => ¬c.2 < q) =
      lam.cells.filter (fun c => q ≤ c.2) := by
    ext c
    simp only [Finset.mem_filter, not_lt]
    constructor
    · intro hc; exact ⟨hc.1.1, hc.2⟩
    · intro hc
      exact ⟨⟨hc.1, (signedHook_no_southeast h hc.1).resolve_right (Nat.not_lt.mpr hc.2)⟩, hc.2⟩
  rw [Finset.filter_filter, hs] at hh
  simp only [not_lt] at ht
  unfold cellHookProduct coreHookProduct rightHookProduct
  rw [← ht, ← hh]

theorem hook_capacity_dimension_lower {n q : ℕ} (lam : Partition n)
    (hhook : IsSignedHook q lam.1) (a b : Fin q → ℕ)
    (ha : ∀ i : Fin q, lam.1.rowLen i - q ≤ a i)
    (hb : ∀ j : Fin q, lam.1.colLen j - q ≤ b j)
    (B : ℕ) (hB : 2 * n + q + 1 ≤ B) :
    (n.factorial : ℝ) ≤ (spechtDimension lam : ℝ) *
      (∏ i, ((a i).factorial : ℝ)) * (∏ j, ((b j).factorial : ℝ)) *
        (B : ℝ) ^ (3 * (q * q)) := by
  have hcore := coreHookProduct_le q B lam.1 (by omega) (by omega)
  have hr := rightHookProduct_le lam.1 hhook a ha B (by omega)
  have hb' : ∀ j : Fin q, lam.1.transpose.rowLen j - q ≤ b j := by
    simpa only [YoungDiagram.rowLen_transpose] using hb
  have ht := rightHookProduct_le lam.1.transpose hhook.transpose b hb' B (by
    have hc : lam.1.transpose.card = n := by
      simpa [YoungDiagram.card, YoungDiagram.transpose] using lam.2
    omega)
  have hprod : cellHookProduct lam.1 ≤
      (∏ i, (a i).factorial) * (∏ j, (b j).factorial) * B ^ (3 * (q * q)) := by
    rw [hookProduct_core_arms lam.1 hhook]
    calc
      _ ≤ B ^ (q*q) * ((∏ i, (a i).factorial) * B ^ (q*q)) *
          ((∏ j, (b j).factorial) * B ^ (q*q)) := Nat.mul_le_mul (Nat.mul_le_mul hcore hr) ht
      _ = _ := by ring
  have hprodR : (cellHookProduct lam.1 : ℝ) ≤
      (∏ i, ((a i).factorial : ℝ)) * (∏ j, ((b j).factorial : ℝ)) *
        (B : ℝ) ^ (3 * (q * q)) := by exact_mod_cast hprod
  exact (factorial_le_dimension_mul_hooks lam).trans
    (by simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hprodR
      (Nat.cast_nonneg (spechtDimension lam))))

end SignedSweeps
end

end OAI
