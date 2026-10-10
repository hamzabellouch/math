import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.Pinning

namespace OAI

/-! Zero-padded spectra and pinned core/shell filters. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open Filter Topology
open Set Filter Complex Complex.HadamardThreeLines
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.PinnedSpectral
open Matrix Polynomial
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem sum_eigen_stat_isometry (V : Matrix ι κ ℂ) (hV : V.conjTranspose * V = 1)
    (A : Matrix κ κ ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) (hf : f 0 = 0) :
    ∑ i, f ((Matrix.isHermitian_mul_mul_conjTranspose V hA).eigenvalues i) =
      ∑ j, f (hA.eigenvalues j) := by
  have hp := Matrix.charpoly_mul_comm' V (A * V.conjTranspose)
  rw [Matrix.mul_assoc, hV, Matrix.mul_one] at hp
  rw [← Matrix.mul_assoc] at hp
  have hh := congrArg
    (fun P : Polynomial ℂ => (P.roots.map (fun z => f z.re)).sum) hp
  rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero)
        (Matrix.charpoly_monic _).ne_zero),
    Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero)
        (Matrix.charpoly_monic _).ne_zero)] at hh
  rw [Multiset.map_add, Multiset.map_add, Multiset.sum_add, Multiset.sum_add,
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at hh
  simp only [Multiset.map_nsmul, Multiset.map_singleton, Multiset.sum_nsmul, Multiset.sum_singleton, Complex.zero_re, hf,
    nsmul_zero, zero_add] at hh
  have hm := Matrix.isHermitian_mul_mul_conjTranspose V hA
  have hleft := hm.roots_charpoly_eq_eigenvalues
  have hright := hA.roots_charpoly_eq_eigenvalues
  rw [hleft, hright] at hh
  simpa only [Multiset.map_map, Function.comp_def, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_re, Finset.sum_map_val] using hh

end PolynomialPEPS.Subvolume.PinnedSpectral

namespace PolynomialPEPS.Subvolume.Pinning
open Matrix
variable {L q : ℕ} (C X : Finset (Vertex L)) (hCX : C ⊆ X)

def insertedMatrix (u : EuclideanSpace ℂ (RegionConfiguration q C))
    (b : Matrix (RegionConfiguration q (X \ C)) (RegionConfiguration q (X \ C)) ℂ) :
    Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ :=
  insertion C X hCX u * b * (insertion C X hCX u).conjTranspose

theorem insertedMatrix_posSemidef (u : EuclideanSpace ℂ (RegionConfiguration q C))
    (b : Matrix (RegionConfiguration q (X \ C)) (RegionConfiguration q (X \ C)) ℂ)
    (hb : b.PosSemidef) : (insertedMatrix C X hCX u b).PosSemidef :=
  hb.mul_mul_conjTranspose_same _

theorem insertedMatrix_tracePower (u : EuclideanSpace ℂ (RegionConfiguration q C))
    (hu : ‖u‖ = 1)
    (b : Matrix (RegionConfiguration q (X \ C)) (RegionConfiguration q (X \ C)) ℂ)
    (hb : b.PosSemidef) (p : ℝ) (hp : 0 < p) :
    ∑ i, Real.rpow ((insertedMatrix_posSemidef C X hCX u b hb).isHermitian.eigenvalues i) p =
      ∑ j, Real.rpow (hb.isHermitian.eigenvalues j) p := by
  exact PinnedSpectral.sum_eigen_stat_isometry _ (insertion_isometry C X hCX u hu)
    b hb.isHermitian (fun t => Real.rpow t p) (Real.zero_rpow (ne_of_gt hp))

theorem insertedMatrix_join (u : EuclideanSpace ℂ (RegionConfiguration q C))
    (b : Matrix (RegionConfiguration q (X \ C)) (RegionConfiguration q (X \ C)) ℂ)
    (x y : RegionConfiguration q C) (w z : RegionConfiguration q (X \ C)) :
    insertedMatrix C X hCX u b (joinWithin C X x w) (joinWithin C X y z) =
      u x * b w z * star (u y) := by
  classical
  simp [insertedMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, insertion_join,
    apply_ite]

def coreMatrix (u : EuclideanSpace ℂ (RegionConfiguration q C)) :
    Matrix (RegionConfiguration q C) (RegionConfiguration q C) ℂ :=
  fun x y => u x * star (u y)

theorem insertedMatrix_eq_product (u : EuclideanSpace ℂ (RegionConfiguration q C))
    (b : Matrix (RegionConfiguration q (X \ C)) (RegionConfiguration q (X \ C)) ℂ) :
    insertedMatrix C X hCX u b = liftBetween hCX (coreMatrix C u) *
      liftBetween (Finset.sdiff_subset : X \ C ⊆ X) b := by
  classical
  ext x y
  obtain ⟨⟨xc,xs⟩,rfl⟩ := (splitEquiv (q := q) C X hCX).surjective x
  obtain ⟨⟨yc,ys⟩,rfl⟩ := (splitEquiv (q := q) C X hCX).surjective y
  change insertedMatrix C X hCX u b (joinWithin C X xc xs) (joinWithin C X yc ys) = _
  rw [insertedMatrix_join, Matrix.mul_apply, ← Equiv.sum_comp (splitEquiv (q := q) C X hCX)]
  simp only [splitEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    liftBetween_core_join, liftBetween_shell_join C X hCX]
  simp [coreMatrix, mul_comm, mul_assoc]

theorem liftBetween_core_shell_commute
    (a : Matrix (RegionConfiguration q C) (RegionConfiguration q C) ℂ)
    (b : Matrix (RegionConfiguration q (X \ C)) (RegionConfiguration q (X \ C)) ℂ) :
    Commute (liftBetween hCX a) (liftBetween (Finset.sdiff_subset : X \ C ⊆ X) b) := by
  classical
  ext x y
  obtain ⟨⟨xc,xs⟩,rfl⟩ := (splitEquiv (q := q) C X hCX).surjective x
  obtain ⟨⟨yc,ys⟩,rfl⟩ := (splitEquiv (q := q) C X hCX).surjective y
  simp only [Matrix.mul_apply]
  rw [← Equiv.sum_comp (splitEquiv (q := q) C X hCX),
    ← Equiv.sum_comp (splitEquiv (q := q) C X hCX)]
  simp only [splitEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    liftBetween_core_join, liftBetween_shell_join C X hCX]
  simp [mul_comm]

include hCX in
theorem lift_core_shell_commute
    (a : Matrix (RegionConfiguration q C) (RegionConfiguration q C) ℂ)
    (b : Matrix (RegionConfiguration q (X \ C)) (RegionConfiguration q (X \ C)) ℂ) :
    Commute (liftLocal C a) (liftLocal (X \ C) b) := by
  have h := congrArg (liftLocal X) (liftBetween_core_shell_commute C X hCX a b).eq
  change _ = _
  simpa only [liftLocal_mul, liftLocal_liftBetween] using h

theorem lift_insertedMatrix (u : EuclideanSpace ℂ (RegionConfiguration q C))
    (b : Matrix (RegionConfiguration q (X \ C)) (RegionConfiguration q (X \ C)) ℂ) :
    liftLocal X (insertedMatrix C X hCX u b) =
      liftLocal C (coreMatrix C u) * liftLocal (X \ C) b := by
  rw [insertedMatrix_eq_product, liftLocal_mul, liftLocal_liftBetween, liftLocal_liftBetween]

theorem coreMatrix_idempotent (u : EuclideanSpace ℂ (RegionConfiguration q C))
    (hu : ‖u‖ = 1) : coreMatrix C u * coreMatrix C u = coreMatrix C u := by
  classical
  have hnorm : ∑ i, star (u i) * u i = (1 : ℂ) := by
    simpa only [PiLp.inner_apply, RCLike.inner_apply, hu, one_pow,
      RCLike.ofReal_one, starRingEnd_apply, mul_comm] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u)
  ext x y
  simp only [Matrix.mul_apply, coreMatrix]
  calc
    _ = u x * (∑ i, star (u i) * u i) * star (u y) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [hnorm,mul_one]

theorem coreMatrix_isHermitian (u : EuclideanSpace ℂ (RegionConfiguration q C)) :
    (coreMatrix C u).IsHermitian := by
  ext x y
  simp [coreMatrix,Matrix.conjTranspose_apply,mul_comm]

end PolynomialPEPS.Subvolume.Pinning

end

end OAI
