import OAI.NumberTheory.DukePrimeDegree.Entropy.RadialFutureLifts

namespace OAI

/-! # The radial future lift is inside an injective quotient chart -/

noncomputable section
open Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_radial_radius_injective_triangular_lifts {n : ℕ} (hn : 0 < n)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (B : ℝ) (hB : 0 < B) (H : X n → ℕ)
    (hheight : ∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤
      2*B*(H x:ℝ)+B) (R : ℝ) (hR : 0 < R) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ r₀ ≤ R ∧
      (∀ x, LocalInjectivityAt (r₀*Real.exp (-(4*B)*(H x:ℝ))) x) ∧
      ∀ (Q : X n → ℕ),
      (∀ x y, Q y=Q x →
        ∃ g ∈ matrixBall n (r₀*Real.exp (-(4*B)*(H x:ℝ))), rightAction x g=y) →
      ∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g ∈ matrixBall n (r₀*Real.exp (-(4*B)*(H x:ℝ))),
          rightAction x g=y ∧ ∀ i j, ell j < ell i → g.val i j=0 := by
  obtain ⟨b,hb,hinj⟩ := exists_uniform_logarithmic_injectivity_radius hn
  let c := b/(2*(n:ℝ)*Real.exp (2*(B+1)))
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨r,hr,hr1,hrR,htri⟩ := exists_radial_radius_small_triangular_lifts
    hn ell hell B hB H hheight (min R c) (lt_min hR hc)
  refine ⟨r,hr,hr1,hrR.trans (min_le_left _ _),?_,htri⟩
  intro x
  apply (hinj (2*B*(H x:ℝ)+B) x (hheight x)).mono
  have he : Real.exp (2*(2*B*(H x:ℝ)+B+1)) =
      Real.exp (2*(B+1))*Real.exp ((4*B)*(H x:ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have heq : c*Real.exp (-(4*B)*(H x:ℝ)) =
      b/(2*(n:ℝ)*Real.exp (2*(2*B*(H x:ℝ)+B+1))) := by
    rw [he,neg_mul,Real.exp_neg]
    dsimp [c]
    field_simp
  rw [←heq]
  exact mul_le_mul_of_nonneg_right (hrR.trans (min_le_right _ _))
    (Real.exp_pos _).le

end DukePrimeDegree

end

end OAI
