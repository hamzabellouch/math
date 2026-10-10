import Mathlib
import OAI.Analysis.Conductivity.Variational.VariationalDN

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Filter Topology

lemma productFactor_spec_le {M : ℝ} (hM : 0 < M) (α : DiagonalTriple) (i : Fin 3)
    (hα : 0 < α i ∧ α i ≤ M) :
    0 < productFactorMinus M α i ∧ 0 < productFactorPlus M α i ∧
      productFactorMinus M α i + productFactorPlus M α i = 2 ∧
      productFactorMinus M α i * productFactorPlus M α i = α i / M := by
  have hq : 0 < α i / M := div_pos hα.1 hM
  have hq1 : α i / M ≤ 1 := (div_le_one hM).mpr hα.2
  have hr : Real.sqrt (1 - α i / M) < 1 := by
    apply (Real.sqrt_lt' (by norm_num)).mpr
    linarith
  have hr0 := Real.sqrt_nonneg (1 - α i / M)
  have hrs := Real.sq_sqrt (sub_nonneg.mpr hq1)
  dsimp [productFactorMinus, productFactorPlus]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> nlinarith

lemma scalar_mem_interior_finiteLaminate {a b s : ℝ} (ha : 0 < a)
    (has : a < s) (hsb : s < b) :
    (fun _ : Fin 3 => s) ∈ interior {α : DiagonalTriple | IsFiniteLaminate a b α} := by
  let c : DiagonalTriple := fun _ => s
  let M : DiagonalTriple → ℝ := fun α => s + ‖α - c‖
  have hs : 0 < s := ha.trans has
  have hM (α : DiagonalTriple) : 0 < M α := by
    dsimp [M]
    positivity
  have halpha (α : DiagonalTriple) (i : Fin 3) : α i ≤ M α := by
    have hh : |α i - s| ≤ ‖α - c‖ := by
      simpa [c, Real.norm_eq_abs] using norm_le_pi_norm (α - c) i
    dsimp [M]
    linarith [le_abs_self (α i - s)]
  have hMc : M c = s := by simp [M]
  have hMc_cont : ContinuousAt M c := by
    fun_prop
  have hx (i : Fin 3) : ContinuousAt (fun α => productFactorMinus (M α) α i) c := by
    unfold productFactorMinus
    exact continuousAt_const.sub ((continuousAt_const.sub
      ((continuous_apply i).continuousAt.div hMc_cont (by rw [hMc]; exact hs.ne'))).sqrt)
  have hy (i : Fin 3) : ContinuousAt (fun α => productFactorPlus (M α) α i) c := by
    unfold productFactorPlus
    exact continuousAt_const.add ((continuousAt_const.sub
      ((continuous_apply i).continuousAt.div hMc_cont (by rw [hMc]; exact hs.ne'))).sqrt)
  let t : (Fin 3 → Bool) → DiagonalTriple → Fin 3 → ℝ :=
    fun σ α i => if σ i then productFactorPlus (M α) α i else productFactorMinus (M α) α i
  have htcont (σ : Fin 3 → Bool) (i : Fin 3) : ContinuousAt (fun α => t σ α i) c := by
    dsimp [t]
    split <;> [exact hy i; exact hx i]
  have htc (σ : Fin 3 → Bool) (i : Fin 3) : t σ c i = 1 := by
    simp [t, productFactorPlus, productFactorMinus, hMc, c, hs.ne']
  have hleaves (σ : Fin 3 → Bool) : ∀ᶠ α in 𝓝 c,
      a < M α * t σ α 0 * t σ α 1 * t σ α 2 ∧
        M α * t σ α 0 * t σ α 1 * t σ α 2 < b := by
    have hh := ((hMc_cont.mul (htcont σ 0)).mul (htcont σ 1)).mul (htcont σ 2)
    have hv : M c * t σ c 0 * t σ c 1 * t σ c 2 = s := by rw [hMc, htc, htc, htc]; ring
    exact hh.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by
      change a < _ ∧ _ < b
      simp only [Pi.mul_apply, hv]
      exact ⟨has, hsb⟩))
  have hpos (i : Fin 3) : ∀ᶠ α : DiagonalTriple in 𝓝 c, 0 < α i :=
    (continuous_apply i).continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hs)
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [Filter.eventually_all.mpr hleaves, Filter.eventually_all.mpr hpos] with α hleaf hα
  have hspec (i : Fin 3) := productFactor_spec_le (hM α) α i ⟨hα i, halpha α i⟩
  have heq : (fun i => M α * productFactorMinus (M α) α i * productFactorPlus (M α) α i) = α := by
    ext i
    rw [mul_assoc, (hspec i).2.2.2]
    exact mul_div_cancel₀ _ (hM α).ne'
  rw [← heq]
  apply product_eight_leaf_laminate _ _ (fun i => (hspec i).1.ne')
    (fun i => (hspec i).2.1.ne') (fun i => (hspec i).2.2.1)
  intro t₀ t₁ t₂ ht₀ ht₁ ht₂
  rcases ht₀ with rfl | rfl <;> rcases ht₁ with rfl | rfl <;> rcases ht₂ with rfl | rfl
  · simpa [t] using hleaf ![false, false, false]
  · simpa [t] using hleaf ![false, false, true]
  · simpa [t] using hleaf ![false, true, false]
  · simpa [t] using hleaf ![false, true, true]
  · simpa [t] using hleaf ![true, false, false]
  · simpa [t] using hleaf ![true, false, true]
  · simpa [t] using hleaf ![true, true, false]
  · simpa [t] using hleaf ![true, true, true]

end ScalarConductivity

end

end OAI
