import OAI.NumberTheory.DukePrimeDegree.Geometry.RootVectorDensity
import OAI.NumberTheory.DukePrimeDegree.Geometry.RationalFixedVectors
import OAI.NumberTheory.DukePrimeDegree.Dynamics.OrbitRationality

namespace OAI

/-!
# No fixed coordinate subspace on a generic finite root orbit

The actual integral stabilizer has rational matrices. A nonzero fixed
vector of the orbit group would therefore supply a nonzero rational fixed
vector. The finite-orbit recurrence argument annihilates one coordinate
of its image in the lattice's rational row space, contradicting genericity.
This is the fixed-space obstruction used to exclude singleton root blocks.
-/

noncomputable section
open Matrix Set MeasureTheory
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma vecMul_slMatrixConjugation_fixed_iff {n : ℕ} (g : G n)
    (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    v ᵥ* slMatrixConjugation g B = v ↔
      (v ᵥ* g⁻¹.val) ᵥ* B = v ᵥ* g⁻¹.val := by
  have hg : g.val * g⁻¹.val = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hgi : g⁻¹.val * g.val = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  constructor
  · intro h
    have he := congrArg (fun w : Fin n → ℝ => w ᵥ* g⁻¹.val) h
    simpa only [slMatrixConjugation, Matrix.vecMul_vecMul, mul_assoc, hg, mul_one] using he
  · intro h
    have he := congrArg (fun w : Fin n → ℝ => w ᵥ* g.val) h
    simpa only [slMatrixConjugation, Matrix.vecMul_vecMul, mul_assoc, hgi,
      Matrix.vecMul_one] using he

lemma rational_fixedVector_fixes_pointOrbitStabilizer {n : ℕ}
    (g : G n) (H : Subgroup (G n)) (q : Fin n → ℚ)
    (hq : ∀ γ : latticeOrbitStabilizer g H, q ᵥ* latticeStabilizerMatrix g H γ = q) :
    ∀ s : pointOrbitStabilizer g H,
      rationalRowMap g.val q ᵥ* s.val.val = rationalRowMap g.val q := by
  intro s
  obtain ⟨γ, hγ⟩ := pointOrbitStabilizer_eq_conjugate g H s
  rw [← hγ]
  apply (vecMul_slMatrixConjugation_fixed_iff g _ _).mpr
  have he : rationalRowMap g.val q ᵥ* g⁻¹.val = rationalVectorCast q := by
    rw [rationalRowMap_apply, Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
    rfl
  rw [he]
  have hr := congrArg rationalVectorCast (hq γ)
  rwa [rationalVectorCast_vecMul] at hr

lemma exists_rational_fixedVector_of_fixedVector {n : ℕ}
    (g : G n) (H : Subgroup (G n)) (v : Fin n → ℝ) (hv0 : v ≠ 0)
    (hv : ∀ h : H, v ᵥ* h.val.val = v) :
    ∃ q : Fin n → ℚ, q ≠ 0 ∧
      ∀ γ : latticeOrbitStabilizer g H, q ᵥ* latticeStabilizerMatrix g H γ = q := by
  let w := v ᵥ* g⁻¹.val
  have hw : w ᵥ* g.val = v := by
    dsimp only [w]
    rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  have hw0 : w ≠ 0 := by
    intro hzero
    rw [hzero, Matrix.zero_vecMul] at hw
    exact hv0 hw.symm
  apply exists_nonzero_rational_fixedVector (latticeStabilizerMatrix g H) w hw0
  intro γ
  let h : H := ⟨(MulAut.conj g⁻¹)
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ.val), γ.property⟩
  have hh : h.val.val = slMatrixConjugation g
      (rationalMatrixCast (latticeStabilizerMatrix g H γ)) := by
    rw [rationalMatrixCast_latticeStabilizer]
    simp only [h, MulAut.conj_apply, inv_inv, Matrix.SpecialLinearGroup.coe_mul,
      slMatrixConjugation]
  apply (vecMul_slMatrixConjugation_fixed_iff g _ v).mp
  rw [← hh]
  exact hv h

/-- A finite-volume orbit through a generic lattice cannot simultaneously
contain a nontrivial root group and fix a nonzero vector. -/
theorem fixedVector_eq_zero_of_generic_finite_root_orbit {n : ℕ}
    (g : G n)
    (hgeneric : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ j, v j ≠ 0)
    (H : Subgroup (G n)) (μ : Measure (LatticeOrbitQuotient g H))
    [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : H, μ.map (fun x => latticeOrbitRightAction g H x h) = μ)
    (i j : Fin n) (hij : i ≠ j)
    (hroot : Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ H)
    (v : Fin n → ℝ) (hv : ∀ h : H, v ᵥ* h.val.val = v) : v = 0 := by
  by_contra hv0
  obtain ⟨q, hq0, hq⟩ := exists_rational_fixedVector_of_fixedVector g H v hv0 hv
  have hz := fixedVector_root_coordinate_zero_of_finite_orbit g H μ hμ hinv
    (rationalRowMap g.val q) (rational_fixedVector_fixes_pointOrbitStabilizer g H q hq)
    i j hij hroot
  have hqzero : rationalRowMap g.val q = 0 :=
    rationalRowSpace_no_coordinate_zero g hgeneric _ ⟨q, rfl⟩ i hz
  exact hq0 (rationalRowMap_injective g (hqzero.trans (map_zero _).symm))

end DukePrimeDegree

end

end OAI
