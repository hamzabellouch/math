import OAI.Geometry.NodalSets.Elliptic.RealCubeL2Control
import OAI.Geometry.NodalSets.Elliptic.RealFiniteJetSquare

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set Function
open scoped ContDiff
noncomputable section

def realCubeAverage (F : Yau.Jets.Coord → ℝ) : List (Fin 4) → Yau.Jets.Coord → ℝ
  | [], x => F x
  | i::is, x => ∫ t in Icc (-1:ℝ) 1, realCubeAverage F is (update x i t)

lemma realCubeAverage_continuous (F : Yau.Jets.Coord → ℝ) (hF : Continuous F)
    (is : List (Fin 4)) : Continuous (realCubeAverage F is) := by
  induction is with
  | nil => exact hF
  | cons i is ih =>
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    exact ih.comp (real_coordinate_update_continuous i)

theorem realCubeL2Control_le_average (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (n : ℕ) (is ds : List (Fin 4)) (hd : ds.length+is.length ≤ n) (x : Yau.Jets.Coord) :
    realCubeL2Control W is ds x ≤
      4^is.length * realCubeAverage (realFiniteJetSquare W n) is x := by
  induction is generalizing ds x with
  | nil => simpa [realCubeL2Control,realCubeAverage] using
      partialJet_sq_le_realFiniteJetSquare W n ds (by simpa using hd) x
  | cons i is ih =>
    have hi (es : List (Fin 4)) : IntegrableOn
        (fun t ↦ realCubeL2Control W is es (update x i t)) (Icc (-1:ℝ) 1) :=
      ((realCubeL2Control_continuous W hW is es).comp
        (contDiff_update (𝕜 := ℝ) ∞ x i).continuous).continuousOn.integrableOn_Icc
    have ha : IntegrableOn
        (fun t ↦ realCubeAverage (realFiniteJetSquare W n) is (update x i t))
        (Icc (-1:ℝ) 1) :=
      ((realCubeAverage_continuous _ (realFiniteJetSquare_smooth W hW n).continuous is).comp
        (contDiff_update (𝕜 := ℝ) ∞ x i).continuous).continuousOn.integrableOn_Icc
    have hm := setIntegral_mono_on (μ := volume) ((hi ds).add (hi (i::ds)))
      ((ha.const_mul (4^is.length)).add (ha.const_mul (4^is.length))) measurableSet_Icc
      (fun t _ ↦ add_le_add (ih ds (by simpa using (show ds.length+is.length ≤ n by
          simp only [List.length_cons] at hd; omega)) _)
        (ih (i::ds) (by simp only [List.length_cons] at hd ⊢; omega) _))
    simp only [Pi.add_apply,integral_add (ha.const_mul _) (ha.const_mul _),
      integral_const_mul] at hm
    change 2 * _ ≤ _
    calc
      _ ≤ 2*(4^is.length * (∫ t in Icc (-1:ℝ) 1,
          realCubeAverage (realFiniteJetSquare W n) is (update x i t)) +
        4^is.length * (∫ t in Icc (-1:ℝ) 1,
          realCubeAverage (realFiniteJetSquare W n) is (update x i t))) :=
        mul_le_mul_of_nonneg_left hm (by norm_num)
      _ = _ := by simp only [List.length_cons,realCubeAverage,pow_succ]; ring

end
end Yau.Geometry

end OAI
