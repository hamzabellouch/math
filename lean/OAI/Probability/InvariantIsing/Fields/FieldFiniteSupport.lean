import OAI.Probability.InvariantIsing.Fields.FieldFiniteDirections
import OAI.Probability.InvariantIsing.Fields.FieldHessianAlgebra

namespace OAI

/-! The finite height Hessian criterion and its supporting-plane
consequence. The conclusion assumes the mixed and radial derivative signs of the
scalar Ising recursion. -/

noncomputable section
open Set IsingPerceptron
open scoped BigOperators

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma hessian_nonpos (r : Fin n → ℝ) (z : ℝ) (hr : r ∈ I)
    (hpos : ∀ i, 0 < r i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ F.PP i j (r, z))
    (hrow : ∀ i, ∑ j, F.PP i j (r, z) * r j ≤ 0) (x : Fin n → ℝ) :
    ∑ i, ∑ j, F.PP i j (r, z) * x i * x j ≤ 0 := by
  have hq := field_quadratic_nonneg_of_positive_scaling
    (fun i j => -F.PP i j (r, z)) r
    (fun i j => congrArg Neg.neg (F.symmetric i j (r, z) hr))
    (fun i j hij => neg_nonpos.mpr (hoff i j hij)) hpos
    (fun i => by simpa only [neg_mul, Finset.sum_neg_distrib] using neg_nonneg.mpr (hrow i)) x
  simpa only [neg_mul, Finset.sum_neg_distrib, neg_nonneg] using hq

/-- A supporting plane follows from the Hessian sign criterion along a
segment. Existence of the second derivatives suffices; continuity of the
second derivatives is not assumed. -/
theorem support_of_hessian (hI : Convex ℝ I) (r s : Fin n → ℝ) (z : ℝ)
    (hr : r ∈ I) (hs : s ∈ I)
    (hq : ∀ t ∈ Icc (0 : ℝ) 1,
      ∑ i, ∑ j, F.PP i j (r + t • (s - r), z) * (s i - r i) * (s j - r j) ≤ 0) :
    F.U (s, z) ≤ F.U (r, z) + ∑ i, F.P i (r, z) * (s i - r i) := by
  let c := s - r
  let f := fun t : ℝ => F.U (r + t • c, z)
  let g := fun t : ℝ => ∑ i, F.P i (r + t • c, z) * c i
  let q := fun t : ℝ => ∑ i, ∑ j, F.PP i j (r + t • c, z) * c i * c j
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : r + t • c ∈ I := by
    have he : r + t • c = (1 - t) • r + t • s := by
      dsimp only [c]
      module
    rw [he]
    exact hI hr hs (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f (g t) t :=
    F.line_derivative r c z t (hp t ht)
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g (q t) t :=
    F.line_gradient_derivative r c z t (hp t ht)
  have hanti : AntitoneOn g (Icc (0 : ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hq t (interior_subset ht))
  have hbound : ∀ t ∈ interior (Icc (0 : ℝ) 1), deriv f t ≤ g 0 := by
    intro t ht
    have ht' := interior_subset ht
    rw [(hf t ht').deriv]
    exact hanti (by simp) ht' ht'.1
  have hslope := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    hbound 0 (by simp) 1 (by simp) zero_le_one
  have he0 : r + (0 : ℝ) • c = r := by simp
  have he1 : r + (1 : ℝ) • c = s := by dsimp only [c]; module
  dsimp only [f, g] at hslope
  rw [he0, he1] at hslope
  simpa only [sub_zero, mul_one, c, Pi.sub_apply, add_comm] using (sub_le_iff_le_add.mp hslope)

end FieldFiniteFamily
end InvariantIsing

end

end OAI
