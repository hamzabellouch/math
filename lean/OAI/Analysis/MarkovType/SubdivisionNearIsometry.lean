import OAI.Analysis.MarkovType.SubdivisionLimit
import OAI.Analysis.MarkovType.SeminormUniformApproximation
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

noncomputable section

open scoped BigOperators NNReal

namespace MarkovSuperreflexivity

namespace C00

def uniformArrayMap (q m : ℕ) : (Fin m → ℝ) →ₗ[ℝ] (Fin (q * m) → ℝ) where
  toFun a i := uniformSubdivision q (ofArray a) i.val
  map_add' a b := by
    funext i
    change ((uniformSubdivision q).comp (arrayLinear m)) (a + b) i.val = _
    rw [map_add]
    rfl
  map_smul' c a := by
    funext i
    change ((uniformSubdivision q).comp (arrayLinear m)) (c • a) i.val = _
    rw [map_smul]
    rfl

theorem ofArray_uniformArrayMap (q m : ℕ) (a : Fin m → ℝ) :
    ofArray (uniformArrayMap q m a) = uniformSubdivision q (ofArray a) :=
  ofArray_of_vanishes (uniformSubdivision q (ofArray a)) (q * m)
    (fun k hk => uniformSubdivision_ofArray_apply_of_ge q a k hk)

end C00

namespace SpreadingModel

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem averaged_array_norm_lower (S : SpreadingModel Y) {m : ℕ} (a : Fin m → ℝ) :
    (S.d / 2) * ‖a‖ ≤ S.averagedSeminorm (C00.ofArray a) := by
  have hd : 0 < S.d / 2 := half_pos S.d_pos
  have hn : ‖a‖ ≤ S.averagedSeminorm (C00.ofArray a) / (S.d / 2) := by
    apply (pi_norm_le_iff_of_nonneg
      (div_nonneg (apply_nonneg S.averagedSeminorm _) hd.le)).mpr
    intro i
    apply (le_div_iff₀ hd).mpr
    simpa only [Real.norm_eq_abs, C00.ofArray_apply, mul_comm] using
      S.averaged_coordinate_lower (C00.ofArray a) i.val
  simpa only [mul_comm] using (le_div_iff₀ hd).mp hn

theorem subdivisionFamily_array_norm_upper (S : SpreadingModel Y) (n : ℕ)
    {m : ℕ} (a : Fin m → ℝ) :
    S.subdivisionFamily n (C00.ofArray a) ≤ (m : ℝ) * ‖a‖ := by
  have hfirst := S.subdivisionFamily_upper n (C00.ofArray a)
  rw [C00.l1Mass_ofArray] at hfirst
  apply hfirst.trans
  simpa only [Real.norm_eq_abs, Fintype.card_fin, nsmul_eq_mul] using
    (Pi.sum_norm_apply_le_norm (f := a))

theorem exists_uniform_nearIsometry (S : SpreadingModel Y) (m : ℕ)
    {η : ℝ} (hη : 0 < η) :
    ∃ q : ℕ, 0 < q ∧ ∀ a : Fin m → ℝ,
      S.averagedSeminorm (C00.ofArray a) ≤
          S.p (C00.ofArray (C00.uniformArrayMap q m a)) ∧
        S.p (C00.ofArray (C00.uniformArrayMap q m a)) ≤
          (1 + η) * S.averagedSeminorm (C00.ofArray a) := by
  let p : ℕ → Seminorm ℝ (Fin m → ℝ) :=
    fun n => (S.subdivisionFamily n).comp (C00.arrayLinear m)
  let q : Seminorm ℝ (Fin m → ℝ) := S.averagedSeminorm.comp (C00.arrayLinear m)
  obtain ⟨n, hn⟩ := SeminormApproximation.exists_relative_approximation p q
    (fun a => S.subdivisionFamily_antitone (C00.ofArray a))
    (fun a => S.tendsto_averagedSeminorm (C00.ofArray a))
    (m : ℝ≥0) (fun n a => S.subdivisionFamily_array_norm_upper n a)
    (half_pos S.d_pos) (fun a => S.averaged_array_norm_lower a) hη
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  intro a
  simp only [C00.ofArray_uniformArrayMap]
  change q a ≤ p n a ∧ p n a ≤ (1 + η) * q a
  exact hn a

end SpreadingModel

end MarkovSuperreflexivity

end

end OAI
