import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianPolynomialCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralLinearExtension

namespace OAI

/-! # The real abelian coordinate space and its explicit integer lattice -/

noncomputable section
namespace PolycyclicRecognition

def AbelianRealSpace (n : ℕ) := Fin n → ℝ

instance abelianRealNormedLie (n : ℕ) : RealNormedLieAlgebra (AbelianRealSpace n) := by
  let : NormedAddCommGroup (AbelianRealSpace n) :=
    inferInstanceAs (NormedAddCommGroup (Fin n → ℝ))
  let : NormedSpace ℝ (AbelianRealSpace n) :=
    inferInstanceAs (NormedSpace ℝ (Fin n → ℝ))
  let lr : LieRing (AbelianRealSpace n) :=
    { toAddCommGroup := inferInstanceAs (AddCommGroup (Fin n → ℝ))
      bracket := fun _ _ => 0
      add_lie := by intros; simp
      lie_add := by intros; simp
      lie_self := by intro; rfl
      leibniz_lie := by intros; simp }
  let : LieRing (AbelianRealSpace n) := lr
  let la : LieAlgebra ℝ (AbelianRealSpace n) :=
    { toModule := inferInstanceAs (Module ℝ (Fin n → ℝ))
      lie_smul := by
        intro r x y
        change (0 : AbelianRealSpace n) = r • (0 : AbelianRealSpace n)
        exact (smul_zero r).symm }
  exact
    { (inferInstance : NormedAddCommGroup (AbelianRealSpace n)), lr,
      (inferInstance : NormedSpace ℝ (AbelianRealSpace n)), la with }

instance abelianRealFiniteDimensional (n : ℕ) : FiniteDimensional ℝ (AbelianRealSpace n) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin n → ℝ))

instance abelianRealLieAbelian (n : ℕ) : IsLieAbelian (AbelianRealSpace n) where
  trivial _ _ := rfl

instance abelianRealCoordinates (n : ℕ) : PolynomialExponentialCoordinates (AbelianRealSpace n) :=
  abelianPolynomialCoordinates

instance abelianRealCommGroup (n : ℕ) : CommGroup (AbelianRealSpace n) :=
  inferInstanceAs (CommGroup (Multiplicative (Fin n → ℝ)))

def abelianRealLattice (n : ℕ) : Subgroup (AbelianRealSpace n) :=
  (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))).toAddSubgroup.toSubgroup

theorem abelianRealLattice_uniform (n : ℕ) : IsUniformLattice (abelianRealLattice n) :=
  standardVectorLattice_uniform n

def abelianRealLatticeMap (n : ℕ) : Multiplicative (Fin n → ℤ) →* abelianRealLattice n where
  toFun x := ⟨integerVectorMap n x.toAdd, integerVectorMap_mem n x.toAdd⟩
  map_one' := by apply Subtype.ext; exact (integerVectorMap n).map_zero
  map_mul' x y := by apply Subtype.ext; exact (integerVectorMap n).map_add x.toAdd y.toAdd

def abelianRealLatticeEquiv (n : ℕ) : Multiplicative (Fin n → ℤ) ≃* abelianRealLattice n :=
  MulEquiv.ofBijective (abelianRealLatticeMap n) ⟨
    fun x y h => Multiplicative.ext (integerVectorMap_injective n (congrArg Subtype.val h)),
    fun y => by
      obtain ⟨x, hx⟩ := exists_integerVectorMap_of_mem n y.val y.property
      exact ⟨Multiplicative.ofAdd x, Subtype.ext hx⟩⟩

@[simp] theorem abelianRealLatticeEquiv_apply (n : ℕ) (x : Multiplicative (Fin n → ℤ)) :
    (abelianRealLatticeEquiv n x : AbelianRealSpace n) = integerVectorMap n x.toAdd := rfl

end PolycyclicRecognition

end

end OAI
