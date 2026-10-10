import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegerExtensionDuality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.GroupIsoDuality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.TrivialGroupDuality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteDimensionCohomology

namespace OAI

/-! # Free abelian rank bounds from integral cohomological dimension

The coordinate homomorphism splits off one infinite cyclic quotient at a time.
The resulting duality calculation bounds the rank of every embedded integral
lattice in a group of finite integral cohomological dimension.
-/

noncomputable section
namespace PolycyclicRecognition

abbrev IntegralLatticeGroup (n : ℕ) := Multiplicative (Fin n → ℤ)

def latticeCoordinate (n : ℕ) : IntegralLatticeGroup (n + 1) →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (a.toAdd 0)
  map_one' := rfl
  map_mul' _ _ := rfl

def latticeCoordinateSection (n : ℕ) : IntegralLatticeGroup (n + 1) :=
  Multiplicative.ofAdd (Fin.cases 1 (fun _ => 0))

@[simp] theorem latticeCoordinate_section (n : ℕ) :
    latticeCoordinate n (latticeCoordinateSection n) = Multiplicative.ofAdd 1 := rfl

def latticeCoordinateKernel (n : ℕ) : (latticeCoordinate n).ker ≃* IntegralLatticeGroup n where
  toFun a := Multiplicative.ofAdd (fun i => a.val.toAdd i.succ)
  invFun a := ⟨Multiplicative.ofAdd (Fin.cases 0 a.toAdd), by
    change latticeCoordinate n (Multiplicative.ofAdd (Fin.cases 0 a.toAdd)) = 1
    rfl⟩
  left_inv a := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    refine Fin.cases ?_ (fun j => rfl) i
    have ha : a.val.toAdd 0 = 0 := congrArg Multiplicative.toAdd a.property
    exact ha.symm
  right_inv a := rfl
  map_mul' _ _ := rfl

theorem integralLattice_poincareDuality (n : ℕ) :
    IsIntegralPoincareDualityGroup (IntegralLatticeGroup n) n := by
  induction n with
  | zero => exact poincareDuality_zero_of_subsingleton _
  | succ n ih =>
    have hkernel := ih.of_equiv (latticeCoordinateKernel n).symm
    exact poincareDuality_of_integerQuotient (latticeCoordinate n)
      (latticeCoordinateSection n) (latticeCoordinate_section n) hkernel

theorem lattice_rank_le_cohomologicalDimension {G : Type} [Group G] (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (n : ℕ) (f : IntegralLatticeGroup n →* G) (hf : Function.Injective f) : n ≤ d := by
  let e := MonoidHom.ofInjective hf
  have hpd := (integralLattice_poincareDuality n).of_equiv e
  let := subgroup_cohomologicalDimension_le f.range d
  exact hpd.dimension_le

theorem HasFiniteIntegralCohomologicalDimension.bounds_integral_lattice_rank
    {G : Type} [Group G] (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ d : ℕ, ∀ (n : ℕ) (f : IntegralLatticeGroup n →* G), Function.Injective f → n ≤ d := by
  obtain ⟨d, hd⟩ := hG
  let := hd
  exact ⟨d, lattice_rank_le_cohomologicalDimension d⟩

end PolycyclicRecognition

end

end OAI
