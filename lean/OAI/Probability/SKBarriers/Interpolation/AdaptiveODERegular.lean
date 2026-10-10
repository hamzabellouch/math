import Mathlib

namespace OAI

section

section
noncomputable section
open scoped BigOperators NNReal
open Set Metric
namespace SK.Analytic

theorem lipschitzWith_sqrt_max (ε : ℝ) (hε : 0 < ε) :
    LipschitzWith ⟨(2*Real.sqrt ε)⁻¹, by positivity⟩ (fun x : ℝ => Real.sqrt (max ε x)) := by
  have h : LipschitzOnWith ⟨(2*Real.sqrt ε)⁻¹, by positivity⟩ Real.sqrt (Ici ε) := by
    apply (convex_Ici ε).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (Real.hasDerivAt_sqrt (ne_of_gt (hε.trans_le hx))).hasDerivWithinAt)
    intro x hx
    apply NNReal.coe_le_coe.mp
    change ‖1/(2*Real.sqrt x)‖ ≤ (2*Real.sqrt ε)⁻¹
    rw [one_div]
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hx) (by norm_num))
  have hm := LipschitzWith.id.const_max ε
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (Real.sqrt (max ε x)) (Real.sqrt (max ε y)) ≤ (2*Real.sqrt ε)⁻¹*dist x y
  calc
    _ ≤ (2*Real.sqrt ε)⁻¹ * dist (max ε x) (max ε y) :=
      h.dist_le_mul _ (show ε ≤ max ε x from le_max_left ε x)
        _ (show ε ≤ max ε y from le_max_left ε y)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa using hm.dist_le_mul x y) (by positivity)

theorem lipschitzWith_pi_of_uniform {X : Type} [PseudoMetricSpace X] {ι : Type} [Fintype ι]
    {K : ℝ≥0} {f : X → ι → ℝ} (hf : ∀ i, LipschitzWith K (fun x => f x i)) :
    LipschitzWith K f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (dist_pi_le_iff (by positivity)).mpr (fun i => (hf i).dist_le_mul x y)

def cumulativeGapMap (k : ℕ) : (Fin (k+1) → ℝ) →L[ℝ] (Fin (k+1) → ℝ) :=
  ContinuousLinearMap.pi (fun j : Fin (k+1) =>
    Fin.cases (motive := fun _ => (Fin (k+1) → ℝ) →L[ℝ] ℝ) (ContinuousLinearMap.proj (0 : Fin (k+1)) : (Fin (k+1) → ℝ) →L[ℝ] ℝ)
      (fun i : Fin k => (ContinuousLinearMap.proj i.succ : (Fin (k+1) → ℝ) →L[ℝ] ℝ)-
        (ContinuousLinearMap.proj i.castSucc : (Fin (k+1) → ℝ) →L[ℝ] ℝ)) j)

@[simp] theorem cumulativeGapMap_zero (k : ℕ) (q : Fin (k+1) → ℝ) :
    cumulativeGapMap k q 0 = q 0 := rfl

@[simp] theorem cumulativeGapMap_succ (k : ℕ) (q : Fin (k+1) → ℝ) (i : Fin k) :
    cumulativeGapMap k q i.succ = q i.succ-q i.castSucc := rfl

def positiveGapScales (k : ℕ) (ε : ℝ) (q : Fin (k+1) → ℝ) : Fin (k+1) → ℝ :=
  fun j => Real.sqrt (max ε (cumulativeGapMap k q j))

theorem positiveGapScales_lipschitz (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K, LipschitzWith K (positiveGapScales k ε) := by
  have h := lipschitzWith_pi_of_uniform (ι := Fin (k+1))
    (fun j => (lipschitzWith_sqrt_max ε hε).comp (LipschitzWith.eval j))
  exact ⟨_,h.comp (cumulativeGapMap k).lipschitzWith⟩

theorem regular_positiveGapScales {k : ℕ}
    (R : (ℝ × (Fin (k+1) → ℝ)) → (Fin (k+1) → ℝ)) (hR : ContDiff ℝ 1 R)
    (ε : ℝ) (hε : 0 < ε) :
    LocallyLipschitz (fun p : ℝ × (Fin (k+1) → ℝ) => R (p.1,positiveGapScales k ε p.2)) := by
  obtain ⟨K,hK⟩ := positiveGapScales_lipschitz k ε hε
  exact hR.locallyLipschitz.comp
    (LipschitzWith.prod_fst.prodMk (hK.comp LipschitzWith.prod_snd)).locallyLipschitz
end SK.Analytic

end
end

end

end OAI
