import OAI.GroupTheory.PolycyclicRecognition.Algebra.InnerCentralizerMembership
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExtensionSemisimpleCentralizer

namespace OAI

/-! # The exact extension carried by a semisimple centralizer -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

theorem inl_mem_semisimpleCentralizer_iff (E : GroupExtension L G Q)
    (S : L ≃ₗ⁅ℝ⁆ L) (x : L) :
    E.inl x ∈ semisimpleActionCentralizer E S ↔ x ∈ innerCentralizerLieSubalgebra S := by
  rw [mem_innerCentralizerLieSubalgebra_iff]
  change E.conjAct (E.inl x) ∈
    Subgroup.centralizer {PolynomialExponentialCoordinates.groupAutomorphism (P := P) S} ↔ _
  rw [extension_conjAct_inl, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply LinearMap.ext
    intro y
    have hh := congrArg (fun f : MulAut L => f y) h
    change x * S y * x⁻¹ = S (x * y * x⁻¹) at hh
    change S (polynomialInnerLieEquiv x y) = polynomialInnerLieEquiv x (S y)
    simpa only [polynomialInnerLieEquiv_apply] using hh.symm
  · intro h
    apply DFunLike.ext
    intro y
    have hh : S (polynomialInnerLieEquiv x y) = polynomialInnerLieEquiv x (S y) :=
      LinearMap.congr_fun h.eq y
    change x * S y * x⁻¹ = S (x * y * x⁻¹)
    simpa only [polynomialInnerLieEquiv_apply] using hh.symm

def semisimpleCentralizerInclusion (E : GroupExtension L G Q) (S : L ≃ₗ⁅ℝ⁆ L) :
    innerCentralizerLieSubalgebra S →* semisimpleActionCentralizer E S where
  toFun x := ⟨E.inl x, (inl_mem_semisimpleCentralizer_iff E S x).mpr x.property⟩
  map_one' := Subtype.ext (E.inl.map_one)
  map_mul' x y := Subtype.ext (E.inl.map_mul x y)

def semisimpleCentralizerExtension (E : GroupExtension L G Q) (S : L ≃ₗ⁅ℝ⁆ L)
    (hsurj : Function.Surjective (E.rightHom.comp (semisimpleActionCentralizer E S).subtype)) :
    GroupExtension (innerCentralizerLieSubalgebra S) (semisimpleActionCentralizer E S) Q where
  inl := semisimpleCentralizerInclusion E S
  rightHom := E.rightHom.comp (semisimpleActionCentralizer E S).subtype
  inl_injective := by
    intro x y h
    exact Subtype.ext (E.inl_injective (congrArg Subtype.val h))
  range_inl_eq_ker_rightHom := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact E.rightHom_inl x
    · intro hg
      have hg' : (g : G) ∈ E.inl.range := by
        rw [E.range_inl_eq_ker_rightHom]
        exact hg
      obtain ⟨x, hx⟩ := hg'
      have hxmem : x ∈ innerCentralizerLieSubalgebra S :=
        (inl_mem_semisimpleCentralizer_iff E S x).mp (hx ▸ g.property)
      exact ⟨⟨x, hxmem⟩, Subtype.ext hx⟩
  rightHom_surjective := hsurj

theorem semisimpleCentralizerExtension_conjAct (E : GroupExtension L G Q)
    (S : L ≃ₗ⁅ℝ⁆ L)
    (hsurj : Function.Surjective (E.rightHom.comp (semisimpleActionCentralizer E S).subtype))
    (g : semisimpleActionCentralizer E S) (x : innerCentralizerLieSubalgebra S) :
    ((semisimpleCentralizerExtension E S hsurj).conjAct g x : L) = E.conjAct g x := by
  apply E.inl_injective
  have hh := congrArg Subtype.val
    ((semisimpleCentralizerExtension E S hsurj).inl_conjAct_comm (e := g) (n := x))
  change E.inl ((semisimpleCentralizerExtension E S hsurj).conjAct g x : L) =
    (g : G) * E.inl x * (g : G)⁻¹ at hh
  exact hh.trans (E.inl_conjAct_comm (e := (g : G)) (n := (x : L))).symm

end PolycyclicRecognition

end

end OAI
