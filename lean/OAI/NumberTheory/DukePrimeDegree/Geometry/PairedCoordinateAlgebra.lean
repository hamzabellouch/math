import OAI.NumberTheory.DukePrimeDegree.Dynamics.PrimeBlockRationality
import Mathlib.Algebra.Algebra.Prod

namespace OAI

/-!
# Rational operators scalar on two coordinates

The algebra below consists of concrete real matrices preserving the rational
row space and acting by a common scalar on two specified coordinate
functionals. In prime dimension, the generic-lattice condition forces this
algebra to contain only rational scalar matrices. No diagonal condition is
imposed on the other coordinates. This is the arithmetic form needed when
singleton root blocks are still present.
-/

noncomputable section
open Matrix Module Set
open scoped BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- A concrete matrix algebra, with the common coordinate eigenvalue recorded
as its first component. -/
def pairedCoordinateAlgebra {n : ℕ} (W : Submodule ℚ (Fin n → ℝ))
    (i j : Fin n) : Subalgebra ℚ (ℝ × Matrix (Fin n) (Fin n) ℝ) where
  carrier := {a | (∀ w ∈ W, a.2 *ᵥ w ∈ W) ∧
    (∀ v, (a.2 *ᵥ v) i = a.1 * v i) ∧
    (∀ v, (a.2 *ᵥ v) j = a.1 * v j)}
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro w _; simpa only [Prod.snd_zero, Matrix.zero_mulVec] using W.zero_mem
    · intro v; simp
    · intro v; simp
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw; simpa using hw
    · intro v; simp
    · intro v; simp
  add_mem' := by
    rintro a b ⟨ha, hai, haj⟩ ⟨hb, hbi, hbj⟩
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      simpa only [Prod.fst_add, Prod.snd_add, Matrix.add_mulVec] using
        W.add_mem (ha w hw) (hb w hw)
    · intro v; simp only [Prod.snd_add, Prod.fst_add, Matrix.add_mulVec,
        Pi.add_apply, hai, hbi, add_mul]
    · intro v; simp only [Prod.snd_add, Prod.fst_add, Matrix.add_mulVec,
        Pi.add_apply, haj, hbj, add_mul]
  mul_mem' := by
    rintro a b ⟨ha, hai, haj⟩ ⟨hb, hbi, hbj⟩
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      simpa only [Prod.snd_mul, Matrix.mulVec_mulVec] using ha _ (hb w hw)
    · intro v
      simp only [Prod.snd_mul, Prod.fst_mul, ← Matrix.mulVec_mulVec, hai, hbi,
        mul_assoc]
    · intro v
      simp only [Prod.snd_mul, Prod.fst_mul, ← Matrix.mulVec_mulVec, haj, hbj,
        mul_assoc]
  algebraMap_mem' := by
    intro q
    change (∀ w ∈ W, (algebraMap ℚ (Matrix (Fin n) (Fin n) ℝ) q) *ᵥ w ∈ W) ∧
      (∀ v, ((algebraMap ℚ (Matrix (Fin n) (Fin n) ℝ) q) *ᵥ v) i =
        (q : ℝ) * v i) ∧
      (∀ v, ((algebraMap ℚ (Matrix (Fin n) (Fin n) ℝ) q) *ᵥ v) j =
        (q : ℝ) * v j)
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      simpa only [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
        Matrix.one_mulVec] using W.smul_mem q hw
    · intro v
      simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Rat.smul_def]
    · intro v
      simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Rat.smul_def]

def pairedCoordinateEval {n : ℕ} (W : Submodule ℚ (Fin n → ℝ))
    (i j : Fin n) : pairedCoordinateAlgebra W i j →ₐ[ℚ] ℝ where
  toFun a := a.val.1
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- The generic coordinate functional is faithful on the concrete matrix
algebra: it detects an operator on the rational space, which spans over ℝ. -/
theorem pairedCoordinateEval_injective {n : ℕ}
    (W : Submodule ℚ (Fin n → ℝ)) (i j : Fin n)
    (hzero : ∀ w ∈ W, ∀ k, w k = 0 → w = 0)
    (hspan : Submodule.span ℝ (W : Set (Fin n → ℝ)) = ⊤) :
    Function.Injective (pairedCoordinateEval W i j) := by
  intro a b hab
  have heval : a.val.1 = b.val.1 := hab
  let F := Matrix.mulVecLin (a.val.2 - b.val.2)
  have hsub : (W : Set (Fin n → ℝ)) ⊆ F.ker := by
    intro w hw
    have hd : a.val.2 *ᵥ w - b.val.2 *ᵥ w ∈ W :=
      W.sub_mem (a.property.1 w hw) (b.property.1 w hw)
    have hdi : (a.val.2 *ᵥ w - b.val.2 *ᵥ w) i = 0 := by
      simp only [Pi.sub_apply, a.property.2.1, b.property.2.1, heval, sub_self]
    have hz := hzero _ hd i hdi
    change (a.val.2 - b.val.2) *ᵥ w = 0
    simpa only [Matrix.sub_mulVec] using hz
  have hker : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ F.ker := by
    rw [← hspan]
    exact Submodule.span_le.mpr hsub
  apply Subtype.ext
  apply Prod.ext heval
  apply sub_eq_zero.mp
  apply Matrix.mulVec_injective
  funext v
  have hv := hker (Submodule.mem_top : v ∈ (⊤ : Submodule ℝ (Fin n → ℝ)))
  change (a.val.2 - b.val.2) *ᵥ v = 0 at hv
  simpa only [Matrix.zero_mulVec] using hv

instance pairedCoordinateModule {n : ℕ} (W : Submodule ℚ (Fin n → ℝ))
    (i j : Fin n) : Module (pairedCoordinateAlgebra W i j) W where
  smul a w := ⟨a.val.2 *ᵥ w.val, a.property.1 w.val w.property⟩
  one_smul w := by
    apply Subtype.ext
    exact Matrix.one_mulVec _
  mul_smul a b w := by
    apply Subtype.ext
    change (a.val.2 * b.val.2) *ᵥ w.val = a.val.2 *ᵥ (b.val.2 *ᵥ w.val)
    exact (Matrix.mulVec_mulVec _ _ _).symm
  smul_zero a := by
    apply Subtype.ext
    change a.val.2 *ᵥ 0 = 0
    exact Matrix.mulVec_zero _
  smul_add a v w := by
    apply Subtype.ext
    change a.val.2 *ᵥ (v.val + w.val) = a.val.2 *ᵥ v.val + a.val.2 *ᵥ w.val
    exact Matrix.mulVec_add _ _ _
  add_smul a b w := by
    apply Subtype.ext
    change (a.val.2 + b.val.2) *ᵥ w.val = a.val.2 *ᵥ w.val + b.val.2 *ᵥ w.val
    exact Matrix.add_mulVec _ _ _
  zero_smul w := by
    apply Subtype.ext
    change (0 : Matrix (Fin n) (Fin n) ℝ) *ᵥ w.val = 0
    exact Matrix.zero_mulVec _

instance pairedCoordinateTower {n : ℕ} (W : Submodule ℚ (Fin n → ℝ))
    (i j : Fin n) : IsScalarTower ℚ (pairedCoordinateAlgebra W i j) W where
  smul_assoc q a w := by
    apply Subtype.ext
    exact Matrix.smul_mulVec q a.val.2 w.val

def pairedCoordinateActionAt {n : ℕ} (W : Submodule ℚ (Fin n → ℝ))
    (i j : Fin n) (w : W) : pairedCoordinateAlgebra W i j →ₗ[ℚ] W where
  toFun a := a • w
  map_add' a b := add_smul a b w
  map_smul' q a := smul_assoc q a w

theorem pairedCoordinateActionAt_injective {n : ℕ}
    (W : Submodule ℚ (Fin n → ℝ)) (i j : Fin n)
    (hzero : ∀ v ∈ W, ∀ k, v k = 0 → v = 0)
    (hspan : Submodule.span ℝ (W : Set (Fin n → ℝ)) = ⊤)
    (w : W) (hw : w ≠ 0) :
    Function.Injective (pairedCoordinateActionAt W i j w) := by
  intro a b hab
  apply pairedCoordinateEval_injective W i j hzero hspan
  have hwi : w.val i ≠ 0 := fun h => hw (Subtype.ext (hzero _ w.property i h))
  have he := congrArg (fun z : W => z.val i) hab
  change (a.val.2 *ᵥ w.val) i = (b.val.2 *ᵥ w.val) i at he
  rw [a.property.2.1, b.property.2.1] at he
  exact mul_right_cancel₀ hwi he

/-- Prime dimension rules out non-scalar operators with two equal coordinate
eigenvalues, even when their action on the remaining coordinates is arbitrary. -/
theorem pairedCoordinateAlgebra_eq_bot {n : ℕ} (hn : n.Prime)
    (W : Submodule ℚ (Fin n → ℝ)) [FiniteDimensional ℚ W]
    (hdim : Module.finrank ℚ W = n)
    (hzero : ∀ v ∈ W, ∀ k, v k = 0 → v = 0)
    (hspan : Submodule.span ℝ (W : Set (Fin n → ℝ)) = ⊤)
    (i j : Fin n) (hij : i ≠ j) : pairedCoordinateAlgebra W i j = ⊥ := by
  let A := pairedCoordinateAlgebra W i j
  let : Nontrivial W := Module.nontrivial_of_finrank_pos (by rw [hdim]; exact hn.pos)
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have hinj := pairedCoordinateActionAt_injective W i j hzero hspan w hw
  let : FiniteDimensional ℚ A :=
    FiniteDimensional.of_injective (pairedCoordinateActionAt W i j w) hinj
  let : IsDomain A := Function.Injective.isDomain (pairedCoordinateEval W i j)
    (pairedCoordinateEval_injective W i j hzero hspan)
  let algA : Algebra ℚ A := inferInstance
  let : DivisionRing A := divisionRingOfFiniteDimensional ℚ A
  let : Algebra ℚ A := algA
  have hdiv : Module.finrank ℚ A ∣ n := by
    simpa only [hdim] using Module.finrank_dvd_finrank_right ℚ A W
  apply Subalgebra.finrank_eq_one_iff.mp
  rcases (Nat.dvd_prime hn).mp hdiv with h | h
  · exact h
  · have hsurj : Function.Surjective (pairedCoordinateActionAt W i j w) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (h.trans hdim.symm)).mp hinj
    let F : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
      w.val j • LinearMap.proj i - w.val i • LinearMap.proj j
    have hsub : (W : Set (Fin n → ℝ)) ⊆ F.ker := by
      intro v hv
      obtain ⟨a, ha⟩ := hsurj ⟨v, hv⟩
      have hv' : a.val.2 *ᵥ w.val = v := congrArg Subtype.val ha
      change w.val j * v i - w.val i * v j = 0
      rw [← hv', a.property.2.1, a.property.2.2]
      ring
    have hker : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ F.ker := by
      rw [← hspan]
      exact Submodule.span_le.mpr hsub
    have he := hker (show Pi.single i (1 : ℝ) ∈ (⊤ : Submodule ℝ (Fin n → ℝ)) from trivial)
    have hwj : w.val j ≠ 0 := fun h => hw (Subtype.ext (hzero _ w.property j h))
    exfalso
    apply hwj
    simpa [F, Pi.single_apply, hij, hij.symm] using he

/-- Actual lattice specialization. The rational structure is the row space
of the supplied matrix, not an independent field-action assumption. -/
theorem rationalRowSpace_pairedCoordinateAlgebra_eq_bot {n : ℕ}
    (hn : n.Prime) (g : G n)
    (hzero : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ k, v k ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    pairedCoordinateAlgebra (rationalRowSpace g) i j = ⊥ :=
  pairedCoordinateAlgebra_eq_bot hn (rationalRowSpace g)
    (finrank_rationalRowSpace g) (rationalRowSpace_no_coordinate_zero g hzero)
    (real_span_rationalRowSpace g) i j hij

end DukePrimeDegree

end

end OAI
