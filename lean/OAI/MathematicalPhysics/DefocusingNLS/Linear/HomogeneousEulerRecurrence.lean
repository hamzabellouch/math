import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialDefect
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace OAI

/-! # Exact finite recurrence for high physical radial derivatives

In logarithmic radius the falling Euler derivatives are represented by two
operator rows. This is an identity for the original second-order equation,
not an asymptotic ansatz for a fast solution.
-/

open Set Filter Topology
open scoped ContDiff

namespace DefocusingNLS

local notation "V" => ℂ × ℂ
local notation "End" => V →L[ℂ] V

noncomputable def homogeneousEulerDeriv (F : ℝ → V) : ℕ → ℝ → V
  | 0 => F
  | n + 1 => fun t => deriv (homogeneousEulerDeriv F n) t -
      (n : ℝ) • homogeneousEulerDeriv F n t

noncomputable def homogeneousEulerRows (B C : ℝ → End) : ℕ → (ℝ → End) × (ℝ → End)
  | 0 => (fun _ => 1, fun _ => 0)
  | n + 1 =>
      let S := (homogeneousEulerRows B C n).1
      let T := (homogeneousEulerRows B C n).2
      (fun t => deriv S t - (n : ℝ) • S t - T t * C t,
       fun t => S t + deriv T t - (n : ℝ) • T t - T t * B t)

theorem homogeneousEulerRows_smooth (B C : ℝ → End) (L : ℝ)
    (hB : ContDiffOn ℝ ∞ B (Ioi L)) (hC : ContDiffOn ℝ ∞ C (Ioi L)) (n : ℕ) :
    ContDiffOn ℝ ∞ (homogeneousEulerRows B C n).1 (Ioi L) ∧
      ContDiffOn ℝ ∞ (homogeneousEulerRows B C n).2 (Ioi L) := by
  induction n with
  | zero => exact ⟨contDiffOn_const, contDiffOn_const⟩
  | succ n ih =>
      exact ⟨((ih.1.deriv_of_isOpen isOpen_Ioi (by simp)).sub (ih.1.const_smul _)).sub
          (ih.2.mul hC),
        ((ih.1.add (ih.2.deriv_of_isOpen isOpen_Ioi (by simp))).sub
          (ih.2.const_smul _)).sub (ih.2.mul hB)⟩

theorem homogeneousEulerRows_identity (B C : ℝ → End) (F G : ℝ → V) (L : ℝ)
    (hB : ContDiffOn ℝ ∞ B (Ioi L)) (hC : ContDiffOn ℝ ∞ C (Ioi L))
    (hF : ∀ t, L < t → HasDerivAt F (G t) t)
    (hG : ∀ t, L < t → HasDerivAt G (-B t (G t) - C t (F t)) t) (n : ℕ) :
    ∀ t, L < t → homogeneousEulerDeriv F n t =
      (homogeneousEulerRows B C n).1 t (F t) +
        (homogeneousEulerRows B C n).2 t (G t) := by
  induction n with
  | zero => intro t ht; simp [homogeneousEulerDeriv, homogeneousEulerRows]
  | succ n ih =>
      intro t ht
      let S := (homogeneousEulerRows B C n).1
      let T := (homogeneousEulerRows B C n).2
      obtain ⟨hS, hT⟩ := homogeneousEulerRows_smooth B C L hB hC n
      have hSd : HasDerivAt S (deriv S t) t :=
        ((hS t ht).contDiffAt (Ioi_mem_nhds ht)).differentiableAt (by simp) |>.hasDerivAt
      have hTd : HasDerivAt T (deriv T t) t :=
        ((hT t ht).contDiffAt (Ioi_mem_nhds ht)).differentiableAt (by simp) |>.hasDerivAt
      have hEq : homogeneousEulerDeriv F n =ᶠ[𝓝 t]
          (fun s => S s (F s) + T s (G s)) := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact ih s hs
      have hd := ((homogeneousComplexOperator_hasDerivAt_apply S _ F _ t hSd (hF t ht)).add
        (homogeneousComplexOperator_hasDerivAt_apply T _ G _ t hTd (hG t ht))).congr_of_eventuallyEq
          hEq
      change deriv (homogeneousEulerDeriv F n) t - (n : ℝ) •
        homogeneousEulerDeriv F n t = _
      rw [hd.deriv, ih t ht]
      change _ = (deriv S t - (n : ℝ) • S t - T t * C t) (F t) +
        (S t + deriv T t - (n : ℝ) • T t - T t * B t) (G t)
      simp only [sub_apply, add_apply, smul_apply, mul_apply_eq_comp,
        map_sub, map_neg, smul_add, S, T]
      abel

/-- At each derivative order the value-row remainder is exactly the
corresponding derivative of the two outgoing columns. -/
theorem homogeneousEulerRows_outgoing_remainder
    (B C : ℝ → End) (u v du dv : ℝ → V) (L : ℝ)
    (hB : ContDiffOn ℝ ∞ B (Ioi L)) (hC : ContDiffOn ℝ ∞ C (Ioi L))
    (hu : ∀ t, L < t → HasDerivAt u (du t) t)
    (hv : ∀ t, L < t → HasDerivAt v (dv t) t)
    (hdu : ∀ t, L < t → HasDerivAt du (-B t (du t) - C t (u t)) t)
    (hdv : ∀ t, L < t → HasDerivAt dv (-B t (dv t) - C t (v t)) t)
    (n : ℕ) (t : ℝ) (ht : L < t) (hdet : spectralValueDet (u t) (v t) ≠ 0) :
    (homogeneousEulerRows B C n).1 t +
        (homogeneousEulerRows B C n).2 t * spectralRobinOperator (u t) (v t) (du t) (dv t) =
      spectralTwoColumns (homogeneousEulerDeriv u n t) (homogeneousEulerDeriv v n t) *
        spectralValueInverse (u t) (v t) := by
  let S := (homogeneousEulerRows B C n).1 t
  let T := (homogeneousEulerRows B C n).2 t
  let A := spectralRobinOperator (u t) (v t) (du t) (dv t)
  have hArF : A * spectralTwoColumns (u t) (v t) = spectralTwoColumns (du t) (dv t) := by
    apply ContinuousLinearMap.ext
    intro z
    exact spectralRobinOperator_columns (u t) (v t) (du t) (dv t) z hdet
  have hleft : (S + T * A) * spectralTwoColumns (u t) (v t) =
      spectralTwoColumns (homogeneousEulerDeriv u n t) (homogeneousEulerDeriv v n t) := by
    rw [add_mul, mul_assoc, hArF]
    apply ContinuousLinearMap.ext
    intro z
    simp only [add_apply, mul_apply_eq_comp, spectralTwoColumns_apply, map_add, map_smul]
    rw [homogeneousEulerRows_identity B C u du L hB hC hu hdu n t ht,
      homogeneousEulerRows_identity B C v dv L hB hC hv hdv n t ht]
    simp only [S, T, smul_add]
    abel
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := LinearMap.surjective_of_injective
    (f := (spectralTwoColumns (u t) (v t)).toLinearMap)
    (show Function.Injective (spectralTwoColumns (u t) (v t)) from
      (show Function.LeftInverse (spectralValueInverse (u t) (v t))
        (spectralTwoColumns (u t) (v t)) from
        fun z => spectralValueInverse_apply_columns (u t) (v t) z hdet).injective) x
  change ((S + T * A) * spectralTwoColumns (u t) (v t)) z = _
  rw [hleft]
  exact congrArg (spectralTwoColumns (homogeneousEulerDeriv u n t)
    (homogeneousEulerDeriv v n t)) (spectralValueInverse_apply_columns (u t) (v t) z hdet).symm

end DefocusingNLS

end OAI
