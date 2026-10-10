import OAI.Geometry.IsometricImmersion.Metrics.MetricLocality
import OAI.Geometry.IsometricImmersion.Calculus.QuotientCalculus
import OAI.Geometry.IsometricImmersion.Calculus.HessianCommutator
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
namespace LowQuotient

variable {U : Set Coord} {a b : Coord → ℝ} {p : Coord}

theorem iterated_contDiffOn (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U)
    (ds : List (Fin 2)) : ContDiffOn ℝ ∞ (iteratedCoordPartial ds a) U := by
  induction ds with
  | nil => exact ha
  | cons i ds ih => exact partial_contDiffOn ih hU i

theorem iterated_differentiableAt (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U)
    (hp : p ∈ U) (ds : List (Fin 2)) :
    DifferentiableAt ℝ (iteratedCoordPartial ds a) p :=
  ((iterated_contDiffOn ha hU ds).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)

theorem product_one (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (i : Fin 2) :
    iteratedCoordPartial [i] (fun x => a x * b x) p =
      iteratedCoordPartial [i] a p * b p + a p * iteratedCoordPartial [i] b p :=
  HessianCalculus.coordPartial_mul_at
    (iterated_differentiableAt ha hU hp []) (iterated_differentiableAt hb hU hp []) i

theorem product_two (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (i j : Fin 2) :
    iteratedCoordPartial [i, j] (fun x => a x * b x) p =
      iteratedCoordPartial [i, j] a p * b p +
      iteratedCoordPartial [j] a p * iteratedCoordPartial [i] b p +
      iteratedCoordPartial [i] a p * iteratedCoordPartial [j] b p +
      a p * iteratedCoordPartial [i, j] b p := by
  have he : coordPartial j (fun x => a x * b x) =ᶠ[𝓝 p]
      (fun x => coordPartial j a x * b x + a x * coordPartial j b x) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact product_one ha hb hU hx j
  change coordPartial i (coordPartial j (fun x => a x * b x)) p = _
  rw [coordPartial_eq_of_eventuallyEq he i]
  have ha0 := iterated_differentiableAt ha hU hp []
  have hb0 := iterated_differentiableAt hb hU hp []
  have haj := iterated_differentiableAt ha hU hp [j]
  have hbj := iterated_differentiableAt hb hU hp [j]
  have ht0 : DifferentiableAt ℝ (fun x => coordPartial j a x * b x) p := haj.mul hb0
  have ht1 : DifferentiableAt ℝ (fun x => a x * coordPartial j b x) p := ha0.mul hbj
  rw [HessianCalculus.coordPartial_add_at
      (f := fun x => coordPartial j a x * b x) (h := fun x => a x * coordPartial j b x) ht0 ht1 i,
    HessianCalculus.coordPartial_mul_at (f := coordPartial j a) (h := b) haj hb0 i,
    HessianCalculus.coordPartial_mul_at (f := a) (h := coordPartial j b) ha0 hbj i]
  dsimp [iteratedCoordPartial]
  ring

theorem product_three (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (i j k : Fin 2) :
    iteratedCoordPartial [i, j, k] (fun x => a x * b x) p =
      iteratedCoordPartial [i, j, k] a p * b p +
      iteratedCoordPartial [j, k] a p * iteratedCoordPartial [i] b p +
      iteratedCoordPartial [i, k] a p * iteratedCoordPartial [j] b p +
      iteratedCoordPartial [k] a p * iteratedCoordPartial [i, j] b p +
      iteratedCoordPartial [i, j] a p * iteratedCoordPartial [k] b p +
      iteratedCoordPartial [j] a p * iteratedCoordPartial [i, k] b p +
      iteratedCoordPartial [i] a p * iteratedCoordPartial [j, k] b p +
      a p * iteratedCoordPartial [i, j, k] b p := by
  have he : iteratedCoordPartial [j, k] (fun x => a x * b x) =ᶠ[𝓝 p]
      (fun x => iteratedCoordPartial [j, k] a x * b x +
        iteratedCoordPartial [k] a x * iteratedCoordPartial [j] b x +
        iteratedCoordPartial [j] a x * iteratedCoordPartial [k] b x +
        a x * iteratedCoordPartial [j, k] b x) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact product_two ha hb hU hx j k
  change coordPartial i (iteratedCoordPartial [j, k] (fun x => a x * b x)) p = _
  rw [coordPartial_eq_of_eventuallyEq he i]
  have ha0 := iterated_differentiableAt ha hU hp []
  have hb0 := iterated_differentiableAt hb hU hp []
  have haj := iterated_differentiableAt ha hU hp [j]
  have hak := iterated_differentiableAt ha hU hp [k]
  have hajk := iterated_differentiableAt ha hU hp [j, k]
  have hbj := iterated_differentiableAt hb hU hp [j]
  have hbk := iterated_differentiableAt hb hU hp [k]
  have hbjk := iterated_differentiableAt hb hU hp [j, k]
  have ht0 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [j, k] a x * b x) p := hajk.mul hb0
  have ht1 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [k] a x * iteratedCoordPartial [j] b x) p := hak.mul hbj
  have ht2 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [j] a x * iteratedCoordPartial [k] b x) p := haj.mul hbk
  have ht3 : DifferentiableAt ℝ (fun x => a x * iteratedCoordPartial [j, k] b x) p := ha0.mul hbjk
  have ht01 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [j, k] a x * b x +
      iteratedCoordPartial [k] a x * iteratedCoordPartial [j] b x) p := ht0.add ht1
  have ht012 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [j, k] a x * b x +
      iteratedCoordPartial [k] a x * iteratedCoordPartial [j] b x +
      iteratedCoordPartial [j] a x * iteratedCoordPartial [k] b x) p := ht01.add ht2
  rw [HessianCalculus.coordPartial_add_at
      ht012 ht3 i,
    HessianCalculus.coordPartial_add_at ht01 ht2 i,
    HessianCalculus.coordPartial_add_at ht0 ht1 i,
    HessianCalculus.coordPartial_mul_at (f := iteratedCoordPartial [j, k] a) (h := b) hajk hb0 i,
    HessianCalculus.coordPartial_mul_at (f := iteratedCoordPartial [k] a) (h := iteratedCoordPartial [j] b) hak hbj i,
    HessianCalculus.coordPartial_mul_at (f := iteratedCoordPartial [j] a) (h := iteratedCoordPartial [k] b) haj hbk i,
    HessianCalculus.coordPartial_mul_at (f := a) (h := iteratedCoordPartial [j, k] b) ha0 hbjk i]
  dsimp [iteratedCoordPartial]
  ring

theorem denominator_mul_quotient_word
    (hU : IsOpen U) (hp : p ∈ U) (hne : ∀ x ∈ U, b x ≠ 0) (ds : List (Fin 2)) :
    iteratedCoordPartial ds (fun x => b x * (a x / b x)) p =
      iteratedCoordPartial ds a p := by
  have he : (fun x => b x * (a x / b x)) =ᶠ[𝓝 p] a := by
    filter_upwards [hU.mem_nhds hp] with x hx
    field_simp [hne x hx]
  exact (iteratedCoordPartial_eventuallyEq he ds).self_of_nhds

theorem quotient_one (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (hne : ∀ x ∈ U, b x ≠ 0) (i : Fin 2) :
    iteratedCoordPartial [i] (fun x => a x / b x) p =
      (iteratedCoordPartial [i] a p -
        iteratedCoordPartial [i] b p * (a p / b p)) / b p := by
  have he := denominator_mul_quotient_word (a := a) hU hp hne [i]
  rw [product_one hb (quotient_contDiffOn ha hb hne) hU hp i] at he
  apply (eq_div_iff (hne p hp)).2
  nlinarith [he]

theorem quotient_two (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (hne : ∀ x ∈ U, b x ≠ 0) (i j : Fin 2) :
    iteratedCoordPartial [i, j] (fun x => a x / b x) p =
      (iteratedCoordPartial [i, j] a p -
        (iteratedCoordPartial [i, j] b p * (a p / b p) +
        iteratedCoordPartial [j] b p * iteratedCoordPartial [i] (fun x => a x / b x) p +
        iteratedCoordPartial [i] b p * iteratedCoordPartial [j] (fun x => a x / b x) p)) / b p := by
  have he := denominator_mul_quotient_word (a := a) hU hp hne [i, j]
  rw [product_two hb (quotient_contDiffOn ha hb hne) hU hp i j] at he
  apply (eq_div_iff (hne p hp)).2
  nlinarith [he]

theorem quotient_three (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (hne : ∀ x ∈ U, b x ≠ 0) (i j k : Fin 2) :
    iteratedCoordPartial [i, j, k] (fun x => a x / b x) p =
      (iteratedCoordPartial [i, j, k] a p -
        (iteratedCoordPartial [i, j, k] b p * (a p / b p) +
        iteratedCoordPartial [j, k] b p * iteratedCoordPartial [i] (fun x => a x / b x) p +
        iteratedCoordPartial [i, k] b p * iteratedCoordPartial [j] (fun x => a x / b x) p +
        iteratedCoordPartial [k] b p * iteratedCoordPartial [i, j] (fun x => a x / b x) p +
        iteratedCoordPartial [i, j] b p * iteratedCoordPartial [k] (fun x => a x / b x) p +
        iteratedCoordPartial [j] b p * iteratedCoordPartial [i, k] (fun x => a x / b x) p +
        iteratedCoordPartial [i] b p * iteratedCoordPartial [j, k] (fun x => a x / b x) p)) / b p := by
  have he := denominator_mul_quotient_word (a := a) hU hp hne [i, j, k]
  rw [product_three hb (quotient_contDiffOn ha hb hne) hU hp i j k] at he
  apply (eq_div_iff (hne p hp)).2
  nlinarith [he]

end LowQuotient
end SmoothLocal.Geometry

end

end OAI
