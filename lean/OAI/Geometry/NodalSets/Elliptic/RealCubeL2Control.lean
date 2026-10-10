import OAI.Geometry.NodalSets.Elliptic.CoordinatePartialJets
import OAI.Geometry.NodalSets.Elliptic.PolynomialEvaluation
import OAI.Geometry.NodalSets.Elliptic.RealIntervalL2Embedding

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set Function
open scoped ContDiff
noncomputable section

def realCubeL2Control (W : Yau.Jets.Coord → ℝ) :
    List (Fin 4) → List (Fin 4) → Yau.Jets.Coord → ℝ
  | [], ds, x => (partialJet W ds x)^2
  | i::is, ds, x => 2*∫ t in Icc (-1:ℝ) 1,
    (realCubeL2Control W is ds (update x i t)+realCubeL2Control W is (i::ds) (update x i t))

lemma real_coordinate_update_continuous (i : Fin 4) :
    Continuous (fun z : Yau.Jets.Coord × ℝ ↦ update z.1 i z.2) := by
  apply continuous_pi
  intro j
  by_cases hj : j=i
  · subst j; simpa using (continuous_snd : Continuous (fun z : Yau.Jets.Coord × ℝ ↦ z.2))
  · simpa only [update_of_ne hj,Function.comp_def] using (continuous_apply j).comp
      (continuous_fst : Continuous (fun z : Yau.Jets.Coord × ℝ ↦ z.1))

lemma realCubeL2Control_continuous (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (is ds : List (Fin 4)) : Continuous (realCubeL2Control W is ds) := by
  induction is generalizing ds with
  | nil => exact ((partialJet_smooth W hW ds).pow 2).continuous
  | cons i is ih =>
    apply continuous_const.mul
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    exact ((ih ds).comp (real_coordinate_update_continuous i)).add
      ((ih (i::ds)).comp (real_coordinate_update_continuous i))

lemma realCubeL2Control_nonneg (W : Yau.Jets.Coord → ℝ)
    (is ds : List (Fin 4)) (x : Yau.Jets.Coord) : 0 ≤ realCubeL2Control W is ds x := by
  induction is generalizing ds x with
  | nil => exact sq_nonneg _
  | cons i is ih =>
    exact mul_nonneg (by norm_num) (integral_nonneg (fun t ↦ add_nonneg (ih ds _) (ih (i::ds) _)))

theorem partialJet_sq_le_realCubeL2Control (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (is ds : List (Fin 4)) (x : Yau.Jets.Coord) (hx : InUnitCube x) :
    (partialJet W ds x)^2 ≤ realCubeL2Control W is ds x := by
  induction is generalizing ds x with
  | nil => exact le_rfl
  | cons i is ih =>
    have hd (t : ℝ) : deriv (fun s ↦ partialJet W ds (update x i s)) t =
        partialJet W (i::ds) (update x i t) := by
      change deriv (partialJet W ds ∘ update x i) t = _
      rw [((partialJet_smooth W hW ds).differentiable (by simp) (update x i t)).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_update x i t) |>.deriv]
      rfl
    have h := real_interval_l2_embedding (fun t ↦ partialJet W ds (update x i t))
      ((partialJet_smooth W hW ds).comp (contDiff_update ∞ x i)) (x i) (abs_le.mp (hx i))
    simp only [update_eq_self] at h
    simp_rw [hd] at h
    have hc (es : List (Fin 4)) : Continuous (fun t ↦ partialJet W es (update x i t)) :=
      (partialJet_smooth W hW es).continuous.comp (contDiff_update (𝕜 := ℝ) ∞ x i).continuous
    have hc' (es : List (Fin 4)) : Continuous (fun t ↦ realCubeL2Control W is es (update x i t)) :=
      (realCubeL2Control_continuous W hW is es).comp (contDiff_update (𝕜 := ℝ) ∞ x i).continuous
    have hm := setIntegral_mono_on (μ := volume)
      (((hc ds).pow 2).add ((hc (i::ds)).pow 2)).continuousOn.integrableOn_Icc
      ((hc' ds).add (hc' (i::ds))).continuousOn.integrableOn_Icc measurableSet_Icc
      (fun t ht ↦ add_le_add
        (ih ds _ (inUnitCube_update hx i (abs_le.mpr ht)))
        (ih (i::ds) _ (inUnitCube_update hx i (abs_le.mpr ht))))
    exact h.trans (mul_le_mul_of_nonneg_left hm (by norm_num))

end
end Yau.Geometry

end OAI
