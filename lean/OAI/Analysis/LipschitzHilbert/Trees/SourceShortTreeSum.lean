import OAI.Analysis.LipschitzHilbert.Geometry.SourceShortTreeOverlap
import OAI.Analysis.LipschitzHilbert.Trees.SourceShortDyadicBudget

namespace OAI

/-! Summation of the short-tree density tails over the actual center
lattice and all retained dyadic scales. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney

/-- A single length, with the actual sheared lattice and strip cutoff. -/
theorem sheared_strip_kernel_sum (a b ell W delta c y r : ℝ)
    (hell : 0<ell) (hW : 0<W) (S : Finset (ℤ×ℤ))
    (hstrip : ∀ p∈S, |b+delta*ell*p.1+W*p.2-y|≤W)
    (hsep : ∀ p∈S, ell≤r → r≤stripDistance c r (a+ell*p.1)) :
    (∑ p∈S, (1+(stripDistance c r (a+ell*p.1)/ell)^2)⁻¹^2) ≤
      144*(4*Real.pi)^2 := by
  calc
    _ ≤ ∑ p∈S, 8*lineEnvelope (a+ell*p.1) ell 1 c :=
      Finset.sum_le_sum (fun p hp => strip_kernel_le_center hell (hsep p hp))
    _ = 8*∑ p∈S, lineEnvelope (a+ell*p.1) ell 1 c := (Finset.mul_sum _ _ _).symm
    _ ≤ 8*(18*(4*Real.pi)^2) := mul_le_mul_of_nonneg_left
      (sheared_strip_overlap a b ell W delta c y hell hW S hstrip) (by norm_num)
    _ = _ := by ring

/-- A single short length retains the squared length-to-distance gain. -/
theorem sheared_strip_kernel_decay_sum (a b ell W delta c y r : ℝ)
    (hell : 0<ell) (hW : 0<W) (hr : 0<r) (S : Finset (ℤ×ℤ))
    (hstrip : ∀ p∈S, |b+delta*ell*p.1+W*p.2-y|≤W)
    (hsep : ∀ p∈S, r≤stripDistance c r (a+ell*p.1)) :
    (∑ p∈S, (1+(stripDistance c r (a+ell*p.1)/ell)^2)⁻¹^2) ≤
      144*(4*Real.pi)^2*(ell/r)^2 := by
  calc
    _ ≤ ∑ p∈S, 8*lineEnvelope (a+ell*p.1) ell 1 c*(ell/r)^2 :=
      Finset.sum_le_sum (fun p hp => strip_kernel_le_center_decay hell hr (hsep p hp))
    _ = 8*(∑ p∈S, lineEnvelope (a+ell*p.1) ell 1 c)*(ell/r)^2 := by
      rw [←Finset.sum_mul,←Finset.mul_sum]
    _ ≤ 8*(18*(4*Real.pi)^2)*(ell/r)^2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (sheared_strip_overlap a b ell W delta c y hell hW S hstrip) (by norm_num)) (sq_nonneg _)
    _ = _ := by ring

/-- The weighted short-packet tail on one Whitney strip, summed over all
retained sites and all lengths at most `R`, is bounded by its strip scale. -/
theorem short_lattice_sum (L R W c y r : ℝ) (hL : 0<L) (hR : 0≤R) (hW : 0<W)
    (levels : Finset ℕ) (sites : ℕ → Finset (ℤ×ℤ)) (a b delta : ℕ → ℝ)
    (hlength : ∀ j∈levels, L/(2:ℝ)^j≤R)
    (hstrip : ∀ j∈levels, ∀ p∈sites j,
      |b j+delta j*(L/(2:ℝ)^j)*p.1+W*p.2-y|≤W)
    (hsep : ∀ j∈levels, ∀ p∈sites j, L/(2:ℝ)^j≤r →
      r≤stripDistance c r (a j+(L/(2:ℝ)^j)*p.1)) :
    (∑ j∈levels, ∑ p∈sites j, (L/(2:ℝ)^j)*W*
      (1+(stripDistance c r (a j+(L/(2:ℝ)^j)*p.1)/(L/(2:ℝ)^j))^2)⁻¹^2) ≤
      288*(4*Real.pi)^2*W*R := by
  have hlevel (j) (hj : j∈levels) :
      (∑ p∈sites j, (L/(2:ℝ)^j)*W*
        (1+(stripDistance c r (a j+(L/(2:ℝ)^j)*p.1)/(L/(2:ℝ)^j))^2)⁻¹^2) ≤
      144*(4*Real.pi)^2*W*(L/(2:ℝ)^j) := by
    rw [←Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left
      (sheared_strip_kernel_sum (a j) (b j) (L/(2:ℝ)^j) W (delta j) c y r
        (by positivity) hW (sites j) (hstrip j hj) (hsep j hj))
      (show 0≤(L/(2:ℝ)^j)*W by positivity)
    convert h using 1
    ring
  calc
    _ ≤ ∑ j∈levels, 144*(4*Real.pi)^2*W*(L/(2:ℝ)^j) := Finset.sum_le_sum hlevel
    _ = (144*(4*Real.pi)^2*W)*∑ j∈levels, L/(2:ℝ)^j := (Finset.mul_sum _ _ _).symm
    _ ≤ (144*(4*Real.pi)^2*W)*(2*R) := mul_le_mul_of_nonneg_left
      (finite_dyadic_length_sum L R hR levels hlength) (by positivity)
    _ = _ := by ring

/-- Outside the top length, the same sum retains quadratic decay in the
Whitney length. This is summable over the large Whitney cells. -/
theorem short_lattice_decay_sum (L R W c y r : ℝ)
    (hL : 0<L) (hR : 0≤R) (hW : 0<W) (hr : 0<r)
    (levels : Finset ℕ) (sites : ℕ → Finset (ℤ×ℤ)) (a b delta : ℕ → ℝ)
    (hlength : ∀ j∈levels, L/(2:ℝ)^j≤R)
    (hstrip : ∀ j∈levels, ∀ p∈sites j,
      |b j+delta j*(L/(2:ℝ)^j)*p.1+W*p.2-y|≤W)
    (hsep : ∀ j∈levels, ∀ p∈sites j,
      r≤stripDistance c r (a j+(L/(2:ℝ)^j)*p.1)) :
    (∑ j∈levels, ∑ p∈sites j, (L/(2:ℝ)^j)*W*
      (1+(stripDistance c r (a j+(L/(2:ℝ)^j)*p.1)/(L/(2:ℝ)^j))^2)⁻¹^2) ≤
      288*(4*Real.pi)^2*W*R*(R/r)^2 := by
  have hlevel (j) (hj : j∈levels) :
      (∑ p∈sites j, (L/(2:ℝ)^j)*W*
        (1+(stripDistance c r (a j+(L/(2:ℝ)^j)*p.1)/(L/(2:ℝ)^j))^2)⁻¹^2) ≤
      144*(4*Real.pi)^2*W*((L/(2:ℝ)^j)*((L/(2:ℝ)^j)/r)^2) := by
    rw [←Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left
      (sheared_strip_kernel_decay_sum (a j) (b j) (L/(2:ℝ)^j) W (delta j) c y r
        (by positivity) hW hr (sites j) (hstrip j hj) (hsep j hj))
      (show 0≤(L/(2:ℝ)^j)*W by positivity)
    convert h using 1
    ring
  calc
    _ ≤ ∑ j∈levels, 144*(4*Real.pi)^2*W*((L/(2:ℝ)^j)*((L/(2:ℝ)^j)/r)^2) :=
      Finset.sum_le_sum hlevel
    _ = (144*(4*Real.pi)^2*W)*∑ j∈levels, (L/(2:ℝ)^j)*((L/(2:ℝ)^j)/r)^2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (144*(4*Real.pi)^2*W)*(2*R*(R/r)^2) := mul_le_mul_of_nonneg_left
      (finite_dyadic_decay_sum L R r hL hR hr levels hlength) (by positivity)
    _ = _ := by ring

end LipschitzHilbert.SourceWhitney

end

end OAI
