import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicCoefficientSupport
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicExpansionInit

namespace OAI

/-! Finite triangular recursion for the angle-independent metric coefficients. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

namespace Geometry

variable {dy : A} (g : Geometry (E := E) O dy)

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xxCoefficient_congr {dx : A} {U W : ℕ → Family O E} {r : ℕ}
    (h : ∀ i ≤ r, U i = W i) : g.xxCoefficient dx U r = g.xxCoefficient dx W r := by
  unfold xxCoefficient
  rw [xCoefficient_congr (h _ (by omega)) (h _ le_rfl),
    xxQuadratic_congr (fun i hi => h i (by omega))]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xyCoefficient_congr {dx : A} {U W : ℕ → Family O E} {r : ℕ}
    (h : ∀ i ≤ r, U i = W i) : g.xyCoefficient dx U r = g.xyCoefficient dx W r := by
  unfold xyCoefficient
  rw [xCoefficient_congr (h _ (by omega)) (h _ le_rfl),
    yCoefficient_congr (h _ (by omega)), xyQuadratic_congr (fun i hi => h i (by omega))]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yyCoefficient_congr {U W : ℕ → Family O E} {r : ℕ}
    (hr : 0 < r) (h : ∀ i < r, U i = W i) : g.yyCoefficient U r = g.yyCoefficient W r := by
  unfold yyCoefficient
  rw [yCoefficient_congr (h _ (by omega)), yyQuadratic_congr (fun i hi => h i (by omega))]

/-- Add the next corrector while retaining every earlier coefficient. -/
theorem advance (dx : A) (U : ℕ → Family O E) (r : ℕ) (hr : 0 < r)
    (hU : ∀ i p, p ∈ O → average ((U i).val p) = 0) :
    ∃ W : ℕ → Family O E,
      (∀ i < r, W i = U i) ∧ (∀ i p, p ∈ O → average ((W i).val p) = 0) ∧
      (g.xxCoefficient dx W r).fluct = 0 ∧
      (g.xyCoefficient dx W r).fluct = 0 ∧
      (g.yyCoefficient W (r + 1)).fluct = 0 ∧
      (∀ Z : Set A, IsOpen Z → Z ⊆ O → (∀ i p, p ∈ Z → (U i).val p = 0) →
        ∀ i p, p ∈ Z → (W i).val p = 0) := by
  let b := g.longitudinal.inner (yCoefficient dy U r) +
    g.transverse.inner ((U (r - 1)).slow dx) + xyQuadratic dx dy U r
  let c := g.longitudinal.inner ((U (r - 1)).slow dx) +
    (1 / 2 : ℝ) • xxQuadratic dx U r
  let d := yyQuadratic dy U (r + 1)
  obtain ⟨u, hu0, hb, hc, hd, hzero⟩ := g.exists_cancellation b c d
  let W := Function.update U r u
  have hlow (i : ℕ) (hi : i < r) : W i = U i := by
    exact Function.update_of_ne (a := i) (a' := r) (by omega) u U
  have hprev : W (r - 1) = U (r - 1) := hlow _ (by omega)
  have hcur : W r = u := Function.update_self r u U
  have hA : xCoefficient dx W r = (U (r - 1)).slow dx + u.angle := by
    simp only [xCoefficient, hprev, hcur]
  have hB : yCoefficient dy W r = yCoefficient dy U r := yCoefficient_congr hprev
  have hB' : yCoefficient dy W (r + 1) = u.slow dy := by
    simp only [yCoefficient, Nat.add_sub_cancel, hcur]
  have hxx := xxQuadratic_congr (dx := dx) hlow
  have hxy := xyQuadratic_congr (dx := dx) (dy := dy) hlow
  have hyy : yyQuadratic dy W (r + 1) = d :=
    yyQuadratic_congr (fun i hi => hlow i (by omega))
  refine ⟨W, hlow, ?_, ?_, ?_, ?_, ?_⟩
  · intro i p hp
    by_cases hi : i = r
    · subst i
      rw [hcur]
      exact hu0 p hp
    · rw [show W i = U i from Function.update_of_ne hi u U]
      exact hU i p hp
  · have he : g.xxCoefficient dx W r =
        (2 : ℝ) • (g.longitudinal.inner u.angle + c) := by
      unfold xxCoefficient c
      rw [hA, hxx, Family.inner_add_right]
      module
    rw [he, Family.fluct_smul, hc, smul_zero]
  · have he : g.xyCoefficient dx W r = g.transverse.inner u.angle + b := by
      unfold xyCoefficient b
      rw [hA, hB, hxy, Family.inner_add_right]
      abel
    rw [he, hb]
  · change ((2 : ℝ) • g.transverse.inner (yCoefficient dy W (r + 1)) +
      yyQuadratic dy W (r + 1)).fluct = 0
    rw [hB', hyy]
    exact hd
  · intro Z hO hZO hUO i p hp
    have huO : ∀ q ∈ Z, u.val q = 0 := by
      apply hzero Z hO hZO
      · intro q hq
        ext t
        have hs := (U (r - 1)).slow_zero_on hO (hUO (r - 1)) dx (hZO hq) hq
        simp only [b, Family.add_apply, Family.inner_apply,
          yCoefficient_zero_on hO hZO U hUO dy r hq, hs,
          xyQuadratic_zero_on hO hZO U hUO dx dy r hq,
          ContinuousMap.zero_apply, inner_zero_right, add_zero]
      · intro q hq
        ext t
        have hs := (U (r - 1)).slow_zero_on hO (hUO (r - 1)) dx (hZO hq) hq
        simp only [c, Family.add_apply, Family.smul_apply, Family.inner_apply,
          hs, xxQuadratic_zero_on hO hZO U hUO dx r hq,
          ContinuousMap.zero_apply, inner_zero_right, smul_zero, add_zero]
      · intro q hq
        exact yyQuadratic_zero_on hO hZO U hUO dy (r + 1) hq
    by_cases hi : i = r
    · subst i
      rw [hcur]
      exact huO p hp
    · rw [show W i = U i from Function.update_of_ne hi u U]
      exact hUO i p hp

/-- The finite recursion produces mean-zero smooth coefficients with no
angle dependence in all prescribed lower metric coefficients. -/
theorem exists_coefficients (dx : A) (n : ℕ) :
    ∃ U : ℕ → Family O E,
      U 0 = g.initial ∧ (∀ i p, p ∈ O → average ((U i).val p) = 0) ∧
      (g.yyCoefficient U 1).fluct = 0 ∧
      (∀ Z : Set A, IsOpen Z → Z ⊆ O → (∀ p ∈ Z, g.initial.val p = 0) →
        ∀ i p, p ∈ Z → (U i).val p = 0) ∧
      ∀ r, 1 ≤ r → r ≤ n →
        (g.xxCoefficient dx U r).fluct = 0 ∧
        (g.xyCoefficient dx U r).fluct = 0 ∧
        (g.yyCoefficient U (r + 1)).fluct = 0 := by
  induction n with
  | zero =>
    refine ⟨fun _ => g.initial, rfl, fun _ _ hp => g.initial_mean_zero hp, ?_, ?_, ?_⟩
    · have hz : g.yyCoefficient (fun _ => g.initial) 1 = 0 := by
        simp only [yyCoefficient, yCoefficient, yyQuadratic,
          Finset.Ico_self, Finset.sum_empty, g.initial_transverse_derivative, smul_zero, add_zero]
      rw [hz]
      ext p hp t
      simp only [Family.fluct_apply, CovarianceCorrector.fluctuation, Family.zero_apply]
      change (0 : ℝ) - average (fun _ => (0 : ℝ)) = 0
      rw [average_const, sub_self]
    · intro Z hO hZO hz i p hp
      exact hz p hp
    · intro r hr hn
      omega
  | succ n ih =>
    obtain ⟨U, hinit, hU, hy₁, hsupport, hcoeff⟩ := ih
    obtain ⟨W, hlow, hW, hxx, hxy, hyy, hzero⟩ := g.advance dx U (n + 1) (by omega) hU
    refine ⟨W, (hlow 0 (by omega)).trans hinit, hW, ?_, ?_, ?_⟩
    · rw [g.yyCoefficient_congr (U := W) (W := U) (by omega : 0 < 1)
        (fun i hi => hlow i (by omega))]
      exact hy₁
    · intro Z hO hZO hz
      exact hzero Z hO hZO (hsupport Z hO hZO hz)
    · intro r hr hn
      by_cases he : r = n + 1
      · subst r
        exact ⟨hxx, hxy, hyy⟩
      · have hrn : r ≤ n := by omega
        obtain ⟨hx, hxy', hy⟩ := hcoeff r hr hrn
        rw [g.xxCoefficient_congr (fun i hi => hlow i (by omega)),
          g.xyCoefficient_congr (fun i hi => hlow i (by omega)),
          g.yyCoefficient_congr (by omega) (fun i hi => hlow i (by omega))]
        exact ⟨hx, hxy', hy⟩

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
