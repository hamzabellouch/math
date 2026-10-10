import OAI.NumberTheory.DukePrimeDegree.Dynamics.FiniteOrbitDensity

namespace OAI

/-!
# Rational block centralizers from finite-volume lattice orbits

The rational matrices in the integral orbit-stabilizer centralizer span
its real centralizer. Conjugation by the actual lattice matrix transports
this statement to the embedding coordinates. Finite-orbit density then
identifies this transported centralizer with the block-scalar algebra.
-/

noncomputable section
open Matrix Module Set MeasureTheory
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def slMatrixConjugationHom {n : ℕ} (g : G n) :
    Matrix (Fin n) (Fin n) ℝ →* Matrix (Fin n) (Fin n) ℝ where
  toFun := slMatrixConjugation g
  map_one' := by
    simp only [slMatrixConjugation, mul_one, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  map_mul' A B := by
    have hg : g.val * g⁻¹.val = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    simp only [slMatrixConjugation, mul_assoc,
      ← mul_assoc g.val g⁻¹.val, hg, one_mul]

def slMatrixConjugationLinear {n : ℕ} (g : G n) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.mulLeftRight ℝ (g⁻¹.val, g.val)

lemma slMatrixConjugationLinear_apply {n : ℕ} (g : G n)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    slMatrixConjugationLinear g M = slMatrixConjugation g M := rfl

lemma slMatrixConjugation_inverse {n : ℕ} (g : G n)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    slMatrixConjugation g (slMatrixConjugation g⁻¹ M) = M := by
  rw [← slMatrixConjugation_mul, inv_mul_cancel, slMatrixConjugation_one]

lemma rationalMatrixCast_latticeStabilizer {n : ℕ} (g : G n) (H : Subgroup (G n))
    (γ : latticeOrbitStabilizer g H) :
    rationalMatrixCast (latticeStabilizerMatrix g H γ) =
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ.val).val := by
  ext i j
  simp [rationalMatrixCast_apply, latticeStabilizerMatrix]

/-- Every actual point stabilizer element is a conjugated integral
stabilizer element. This uses the integral quotient, not an abstract
field action. -/
lemma pointOrbitStabilizer_eq_conjugate {n : ℕ} (g : G n) (H : Subgroup (G n))
    (s : pointOrbitStabilizer g H) :
    ∃ γ : latticeOrbitStabilizer g H,
      slMatrixConjugation g (rationalMatrixCast (latticeStabilizerMatrix g H γ)) =
        s.val.val.val := by
  have hs : (MulAut.conj g) s.val.val ∈ integralGroup n := s.property
  obtain ⟨γ, hγ⟩ := hs
  have hc : (MulAut.conj g⁻¹) (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) =
      s.val.val := by
    rw [hγ]
    simp [MulAut.conj_apply, mul_assoc]
  have hm : γ ∈ latticeOrbitStabilizer g H := by
    change (MulAut.conj g⁻¹) (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) ∈ H
    rw [hc]
    exact s.val.property
  refine ⟨⟨γ, hm⟩, ?_⟩
  rw [rationalMatrixCast_latticeStabilizer]
  simpa only [slMatrixConjugation, MulAut.conj_apply, inv_inv,
    Matrix.SpecialLinearGroup.coe_mul] using congrArg Subtype.val hc

lemma conjugate_rational_commutant_mem_block {n : ℕ}
    (g : G n) (H : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g H)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : H, μ.map (fun x => latticeOrbitRightAction g H x h) = μ)
    (ell : Fin n → ℝ) (hsum : ∑ i, ell i = 0) (hell : Function.Injective ell)
    (hdiag : ∀ t : ℝ, diagonalOneParameter ell hsum t ∈ H)
    (r : Setoid (Fin n))
    (hroot : ∀ i j (hij : i ≠ j), r i j →
      Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ H)
    (B : Matrix (Fin n) (Fin n) ℚ)
    (hB : B ∈ (commutatorFamily (latticeStabilizerMatrix g H)).ker) :
    slMatrixConjugation g (rationalMatrixCast B) ∈ blockScalarAlgebra r := by
  apply centralizer_subset_blockScalar_of_finite_orbit g H μ hμ hinv ell hsum hell hdiag r hroot
  intro s
  obtain ⟨γ, hγ⟩ := pointOrbitStabilizer_eq_conjugate g H s
  rw [← hγ]
  exact ((commute_rationalMatrixCast_iff B (latticeStabilizerMatrix g H γ)).mpr
    ((mem_commutatorFamily_ker _ _).mp hB γ)).map
    (slMatrixConjugationHom g)

lemma conjugate_rational_commutant_diagonal_mem {n : ℕ}
    (g : G n) (H : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g H)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : H, μ.map (fun x => latticeOrbitRightAction g H x h) = μ)
    (ell : Fin n → ℝ) (hsum : ∑ i, ell i = 0) (hell : Function.Injective ell)
    (hdiag : ∀ t : ℝ, diagonalOneParameter ell hsum t ∈ H)
    (r : Setoid (Fin n))
    (hroot : ∀ i j (hij : i ≠ j), r i j →
      Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ H)
    (B : Matrix (Fin n) (Fin n) ℚ)
    (hB : B ∈ (commutatorFamily (latticeStabilizerMatrix g H)).ker) :
    (fun i => slMatrixConjugation g (rationalMatrixCast B) i i) ∈
      rationalBlockStabilizer g r := by
  have hD := (mem_blockScalarAlgebra_iff r _).mp
    (conjugate_rational_commutant_mem_block g H μ hμ hinv ell hsum hell hdiag r hroot B hB)
  refine ⟨?_, hD.2⟩
  apply (mem_rationalDiagonalStabilizer_iff_rational_matrix g _).mpr
  refine ⟨B, ?_⟩
  rw [← hD.1]
  have hg : g.val * g⁻¹.val = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  change rationalMatrixCast B * g.val = g.val * (g⁻¹.val * rationalMatrixCast B * g.val)
  simp only [← mul_assoc, hg, one_mul]

/-- The real-span condition required by the prime-block endpoint follows
from the finite volume of the actual block orbit. Both inclusions use
the given matrix group; no rational field action is assumed. -/
theorem rationalBlockRealSpan_of_finite_orbit {n : ℕ}
    (g : G n) (H : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g H)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : H, μ.map (fun x => latticeOrbitRightAction g H x h) = μ)
    (ell : Fin n → ℝ) (hsum : ∑ i, ell i = 0) (hell : Function.Injective ell)
    (hdiag : ∀ t : ℝ, diagonalOneParameter ell hsum t ∈ H)
    (r : Setoid (Fin n))
    (hroot : ∀ i j (hij : i ≠ j), r i j →
      Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ H)
    (hblock : ∀ h : H, ∀ c ∈ blockCoordinateAlgebra r, Commute (Matrix.diagonal c) h.val.val)
    {c : Fin n → ℝ} (hc : c ∈ blockCoordinateAlgebra r) :
    c ∈ rationalBlockRealSpan g r := by
  let A := slMatrixConjugation g⁻¹ (Matrix.diagonal c)
  have hA : A ∈ (commutatorFamily
      (fun γ => rationalMatrixCast (latticeStabilizerMatrix g H γ))).ker := by
    rw [mem_commutatorFamily_ker]
    intro γ
    let h : H := ⟨(MulAut.conj g⁻¹)
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ.val), γ.property⟩
    have he : h.val.val = slMatrixConjugation g
        (rationalMatrixCast (latticeStabilizerMatrix g H γ)) := by
      rw [rationalMatrixCast_latticeStabilizer]
      simp only [h, slMatrixConjugation, MulAut.conj_apply, inv_inv,
        Matrix.SpecialLinearGroup.coe_mul]
    have Hc := (hblock h c hc).map (slMatrixConjugationHom g⁻¹)
    change Commute A (slMatrixConjugation g⁻¹ h.val.val) at Hc
    rw [he] at Hc
    simpa only [← slMatrixConjugation_mul, mul_inv_cancel, slMatrixConjugation_one] using Hc
  rw [latticeStabilizer_commutant_rational] at hA
  let T : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (Fin n → ℝ) :=
    (LinearMap.pi fun i => (LinearMap.proj i).comp (LinearMap.proj i)).comp
      (slMatrixConjugationLinear g)
  have hspan : Submodule.span ℝ (rationalMatrixCast ''
      ((commutatorFamily (latticeStabilizerMatrix g H)).ker :
        Set (Matrix (Fin n) (Fin n) ℚ))) ≤ (rationalBlockRealSpan g r).comap T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨B, hB, rfl⟩
    have hb := conjugate_rational_commutant_diagonal_mem g H μ hμ hinv
      ell hsum hell hdiag r hroot B hB
    exact Submodule.subset_span ⟨⟨_, hb⟩, rfl⟩
  have hT : T A ∈ rationalBlockRealSpan g r := hspan hA
  have hTA : T A = c := by
    change (fun i => slMatrixConjugation g (slMatrixConjugation g⁻¹ (Matrix.diagonal c)) i i) = c
    rw [slMatrixConjugation_inverse]
    funext i
    exact Matrix.diagonal_apply_eq c i
  rwa [hTA] at hT

/-- A nontrivial root block of a finite-volume block orbit in generic
prime degree must contain every coordinate. -/
theorem root_partition_universal_of_finite_orbit {n : ℕ}
    (hn : n.Prime) (g : G n)
    (hzero : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ j, v j ≠ 0)
    (H : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g H)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : H, μ.map (fun x => latticeOrbitRightAction g H x h) = μ)
    (ell : Fin n → ℝ) (hsum : ∑ i, ell i = 0) (hell : Function.Injective ell)
    (hdiag : ∀ t : ℝ, diagonalOneParameter ell hsum t ∈ H)
    (r : Setoid (Fin n))
    (hroot : ∀ i j (hij : i ≠ j), r i j →
      Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ H)
    (hblock : ∀ h : H, ∀ c ∈ blockCoordinateAlgebra r, Commute (Matrix.diagonal c) h.val.val)
    (hnontrivial : ∃ i j, i ≠ j ∧ r i j) : ∀ i j, r i j := by
  apply root_partition_universal_of_rational_span hn g hzero r hnontrivial
  intro c hc
  exact rationalBlockRealSpan_of_finite_orbit g H μ hμ hinv
    ell hsum hell hdiag r hroot hblock hc

end DukePrimeDegree

end

end OAI
