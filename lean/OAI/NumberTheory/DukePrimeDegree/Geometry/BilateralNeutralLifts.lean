import OAI.NumberTheory.DukePrimeDegree.Entropy.RadialFutureLifts

namespace OAI

/-! # Bilateral observation fibers have neutral relative displacement

The same small radial cells are used in both time directions. Uniqueness
of the small lift identifies the two triangular lifts; their common lift
commutes with the diagonal flow. This supplies the geometry needed to
bound the entropy left over after the complete observation itinerary.
-/

noncomputable section
open Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma commute_diagonalOneParameter_of_weight_support {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (g : G n)
    (hg : ∀ i j, ell i ≠ ell j → g.val i j=0) (t : ℝ) :
    Commute g (diagonalOneParameter ell hell t) := by
  change g * diagonalOneParameter ell hell t = diagonalOneParameter ell hell t * g
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (g.val * Matrix.diagonal (fun k => Real.exp (ell k*t))) i j =
    (Matrix.diagonal (fun k => Real.exp (ell k*t)) * g.val) i j
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases h : ell i=ell j
  · rw [h,mul_comm]
  · rw [hg i j h]
    simp

theorem exists_radial_radius_bilateral_neutral_lifts {n : ℕ} (hn : 0 < n)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (B : ℝ) (hB : 0 < B) (H : X n → ℕ)
    (hheight : ∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤
      2*B*(H x:ℝ)+B) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ Q : X n → ℕ,
      (∀ x y, Q y=Q x →
        ∃ g ∈ matrixBall n (r*Real.exp (-(4*B)*(H x:ℝ))), rightAction x g=y) →
      ∀ x y,
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
        ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
          ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t) := by
  obtain ⟨b,hb,hinj⟩ := exists_uniform_logarithmic_injectivity_radius hn
  let R := b/(2*(n:ℝ)*Real.exp (2*(B+1)))
  have hR : 0 < R := by dsimp [R]; positivity
  have hneg : ∑ i, -ell i=0 := by simp only [Finset.sum_neg_distrib,hell,neg_zero]
  obtain ⟨rpos,hp,hp1,hpR,hplus⟩ := exists_radial_radius_small_triangular_lifts
    hn ell hell B hB H hheight R hR
  obtain ⟨rneg,hm,hm1,hmR,hminus⟩ := exists_radial_radius_small_triangular_lifts
    hn (fun i => -ell i) hneg B hB H hheight R hR
  let r := min rpos rneg
  refine ⟨r,lt_min hp hm,(min_le_left _ _).trans hp1,?_⟩
  intro Q hsmall x y hforward hbackward
  have hsp : ∀ x y, Q y=Q x →
      ∃ g ∈ matrixBall n (rpos*Real.exp (-(4*B)*(H x:ℝ))), rightAction x g=y := by
    intro x y hxy
    obtain ⟨g,hg,hgx⟩ := hsmall x y hxy
    exact ⟨g,matrixBall_mono
      (mul_le_mul_of_nonneg_right (min_le_left rpos rneg) (Real.exp_pos _).le) hg,hgx⟩
  have hsm : ∀ x y, Q y=Q x →
      ∃ g ∈ matrixBall n (rneg*Real.exp (-(4*B)*(H x:ℝ))), rightAction x g=y := by
    intro x y hxy
    obtain ⟨g,hg,hgx⟩ := hsmall x y hxy
    exact ⟨g,matrixBall_mono
      (mul_le_mul_of_nonneg_right (min_le_right rpos rneg) (Real.exp_pos _).le) hg,hgx⟩
  obtain ⟨g,hg,hgx,hgt⟩ := hplus Q hsp x y hforward
  have ha : diagonalOneParameter (fun i => -ell i) hneg (-1) =
      diagonalOneParameter ell hell 1 := by
    simpa only [neg_neg] using diagonalOneParameter_neg_weights ell hell (-1)
  obtain ⟨g',hg',hg'x,hg't⟩ := hminus Q hsm x y (by
    rw [ha]
    exact hbackward)
  have heqrad : R*Real.exp (-(4*B)*(H x:ℝ)) =
      b/(2*(n:ℝ)*Real.exp (2*(2*B*(H x:ℝ)+B+1))) := by
    have he : Real.exp (2*(2*B*(H x:ℝ)+B+1)) =
        Real.exp (2*(B+1))*Real.exp ((4*B)*(H x:ℝ)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [he,neg_mul,Real.exp_neg]
    dsimp [R]
    field_simp
  have hi := (hinj (2*B*(H x:ℝ)+B) x (hheight x)).injOn
  have hgR : g ∈ matrixBall n (b/(2*(n:ℝ)*Real.exp (2*(2*B*(H x:ℝ)+B+1)))) := by
    rw [←heqrad]
    exact matrixBall_mono (mul_le_mul_of_nonneg_right hpR (Real.exp_pos _).le) hg
  have hg'R : g' ∈ matrixBall n (b/(2*(n:ℝ)*Real.exp (2*(2*B*(H x:ℝ)+B+1)))) := by
    rw [←heqrad]
    exact matrixBall_mono (mul_le_mul_of_nonneg_right hmR (Real.exp_pos _).le) hg'
  have heq : g=g' := hi hgR hg'R (hgx.trans hg'x.symm)
  have hsupport : ∀ i j, ell i ≠ ell j → g.val i j=0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · rw [heq]
      exact hg't i j (by linarith)
    · exact hgt i j h
  have hrad : rpos*Real.exp (-(4*B)*(H x:ℝ)) ≤ 1 := by
    apply le_trans _ hp1
    apply mul_le_of_le_one_right hp.le
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hB.le (Nat.cast_nonneg (H x))]
  exact ⟨g,matrixBall_mono hrad hg,hgx,
    commute_diagonalOneParameter_of_weight_support ell hell g hsupport⟩

end DukePrimeDegree

end

end OAI
