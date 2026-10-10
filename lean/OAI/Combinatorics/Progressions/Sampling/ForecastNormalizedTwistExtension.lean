import OAI.Combinatorics.Progressions.Lattices.ParametricFullResidueCoveredExtension
import OAI.Combinatorics.Progressions.Polynomial.MeasureDegreeZeroTwistTransfer

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical NNReal Matrix

theorem exists_forecast_normalized_twist_extension
    {X : Type*} [Fintype X] {m : ℕ} {J E : Fin m → Type*}
    [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ}
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (q : ℕ) [NeZero q]
    (mask : (X → ZMod q) → ℂ) (hmask : ∀ a, ‖mask a‖ ≤ 1)
    (F : (∀ j, Fin (n j) ⊕ E j → ZMod q) → (X → ℝ) × ((Σ j, J j) → ℝ) → ℂ)
    (L : ℝ≥0) (hL : ∀ a, LipschitzWith L (F a)) (hF : ∀ a v, ‖F a v‖ ≤ 1) :
    ∃ twist : NormalizedPolynomialTwist X (Σ j, J j) q q
        (max (L * max 1 (q : ℝ≥0)) (4 * q)),
      twist.modulus = q ∧ twist.cover = q ∧
      ∀ (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ)
        (x : ∀ j, euclideanSubspace (U j) × (Fin (n j) → ℤ)) (w : ∀ j, E j → ℤ),
        (∀ j i, eval (fun a => (u a : ℝ)) (p j) i =
          (normalizedLatticeRepresentative (euclideanSubspace (U j)) (b j) (hb j) (x j) +
            ((bW j).equivFun.symm (w j)).val).val i) →
        (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (x j) i| ≤ 1 / 4) →
        twist.eval N p u = mask (fun i => (u i : ZMod q)) *
          F (fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => (w j i : ZMod q)))
            (fun i => (u i : ℝ) / N i,
              fun a => normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1) (x a.1) a.2) / 2 := by
  obtain ⟨g, hg, hgb, hvalue⟩ := exists_parametric_layered_full_residue_extension
    (fun j => euclideanSubspace (U j)) bW b hb q F L 1 hL hF
  let K : ℝ≥0 := max (L * max 1 (q : ℝ≥0)) (4 * q)
  have hg' : LipschitzWith (2 * K) g := by
    simpa only [mul_one, K] using hg
  have hbound (y : (X → ℝ) × ((Σ j, J j) → UnitAddCircle)) : ‖g y / 2‖ ≤ 1 := by
    have h := hgb y
    norm_num only [norm_div, Complex.norm_ofNat, NNReal.coe_one, mul_one] at h ⊢
    linarith
  have hlip : LipschitzWith K (fun y => g y / 2) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    have h := hg'.dist_le_mul y z
    simp only [NNReal.coe_mul, NNReal.coe_ofNat] at h
    calc
      dist (g y / 2) (g z / 2) = dist (g y) (g z) / 2 := by
        simp only [dist_eq_norm, ← sub_div, norm_div, Complex.norm_ofNat]
      _ ≤ (K : ℝ) * dist y z := by linarith
  let twist : NormalizedPolynomialTwist X (Σ j, J j) q q K :=
    { modulus := q
      modulus_pos := Nat.pos_of_ne_zero (NeZero.ne q)
      modulus_bound := le_rfl
      cover := q
      cover_pos := Nat.pos_of_ne_zero (NeZero.ne q)
      cover_bound := le_rfl
      mask := mask
      mask_bound := hmask
      smooth := fun y => g y / 2
      smooth_bound := hbound
      smooth_lipschitz := hlip }
  refine ⟨twist, rfl, rfl, ?_⟩
  intro N p u x w heval hquarter
  have hpoint : physicalGridFactorInput q p (fun i => (u i : ℝ)) =
      fun a => (((normalizedLatticeRepresentative (euclideanSubspace (U a.1))
        (b a.1) (hb a.1) (x a.1) + ((bW a.1).equivFun.symm (w a.1)).val).val a.2 /
          q : ℝ) : UnitAddCircle) := by
    funext a
    dsimp only [physicalGridFactorInput]
    rw [heval a.1 a.2]
  change mask (fun i => (u i : ZMod q)) *
    (g (fun i => (u i : ℝ) / N i, physicalGridFactorInput q p (fun i => (u i : ℝ))) / 2) = _
  rw [hpoint, hvalue (fun i => (u i : ℝ) / N i) x w hquarter]
  rw [mul_div_assoc]

end Erdos3.VectorPolynomial

end

end OAI
