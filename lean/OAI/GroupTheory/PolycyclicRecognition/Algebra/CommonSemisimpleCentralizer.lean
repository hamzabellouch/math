import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExtensionSemisimpleCentralizer
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommutingSemisimpleCorrection

namespace OAI

/-! # Common semisimple centralizers in the completed extension -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

def commonSemisimpleCentralizer (E : GroupExtension L G Q) (ss : List (L ≃ₗ⁅ℝ⁆ L)) :
    Subgroup G := ⨅ T : {T : L ≃ₗ⁅ℝ⁆ L // T ∈ ss}, semisimpleActionCentralizer E T.val

omit [LieRing.IsNilpotent L] in
theorem mem_commonSemisimpleCentralizer (E : GroupExtension L G Q)
    (ss : List (L ≃ₗ⁅ℝ⁆ L)) (g : G) :
    g ∈ commonSemisimpleCentralizer E ss ↔ ∀ T ∈ ss, g ∈ semisimpleActionCentralizer E T := by
  simp only [commonSemisimpleCentralizer, Subgroup.mem_iInf]
  exact ⟨fun h T ht => h ⟨T, ht⟩, fun h T => h T.val T.property⟩

omit [LieRing.IsNilpotent L] in
theorem inl_mem_commonSemisimpleCentralizer_of_fixed (E : GroupExtension L G Q)
    (ss : List (L ≃ₗ⁅ℝ⁆ L)) (x : L) (hx : ∀ T ∈ ss, T x = x) :
    E.inl x ∈ commonSemisimpleCentralizer E ss := by
  apply (mem_commonSemisimpleCentralizer E ss (E.inl x)).mpr
  intro T ht
  change E.conjAct (E.inl x) ∈
    Subgroup.centralizer {PolynomialExponentialCoordinates.groupAutomorphism (P := C) T}
  rw [extension_conjAct_inl]
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply DFunLike.ext
  intro y
  let t := PolynomialExponentialCoordinates.groupAutomorphism (P := C) T
  change x * t y * x⁻¹ = t (x * y * x⁻¹)
  rw [map_mul, map_mul, map_inv]
  change x * t y * x⁻¹ = T x * t y * (T x)⁻¹
  rw [hx T ht]

omit [LieRing.IsNilpotent L] in
theorem mem_semisimpleActionCentralizer_iff (E : GroupExtension L G Q)
    (S : L ≃ₗ⁅ℝ⁆ L) (g : G)
    (hg : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) :
    g ∈ semisimpleActionCentralizer E S ↔
      Commute S.toLinearMap (polynomialModelLieEquiv (E.conjAct g) hg).toLinearMap := by
  let B := polynomialModelLieEquiv (E.conjAct g) hg
  have hb (x : L) : B x = E.conjAct g x := polynomialModelLieEquiv_apply _ _ x
  change E.conjAct g ∈
    Subgroup.centralizer {PolynomialExponentialCoordinates.groupAutomorphism (P := C) S} ↔ _
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    have hh := congrArg (fun f : MulAut L => f x) h
    change E.conjAct g (S x) = S (E.conjAct g x) at hh
    change S (B x) = B (S x)
    rw [hb, hb]
    exact hh.symm
  · intro h
    apply DFunLike.ext
    intro x
    have hh : S (B x) = B (S x) := LinearMap.congr_fun h.eq x
    rw [hb, hb] at hh
    exact hh.symm

theorem common_semisimpleCentralizer_step [IsMulCommutative Q]
    (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g))
    (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hss : ∀ T ∈ ss, Module.End.IsSemisimple T.toLinearMap)
    (hpair : ∀ T ∈ ss, ∀ R ∈ ss, Commute T.toLinearMap R.toLinearMap)
    (t : G) (ht : t ∈ commonSemisimpleCentralizer E ss) :
    ∃ S U : L ≃ₗ⁅ℝ⁆ L, Module.End.IsSemisimple S.toLinearMap ∧
      IsNilpotent (U.toLinearMap - 1) ∧ Commute S.toLinearMap U.toLinearMap ∧
      (polynomialModelLieEquiv (E.conjAct t) (hsmooth t)).toLinearMap =
        S.toLinearMap * U.toLinearMap ∧
      (∀ T ∈ ss, Commute T.toLinearMap S.toLinearMap) ∧
      ∀ g ∈ commonSemisimpleCentralizer E ss, ∃ v : L,
        (∀ T ∈ ss, T v = v) ∧ E.inl v * g ∈ commonSemisimpleCentralizer E (S :: ss) := by
  let A := polynomialModelLieEquiv (E.conjAct t) (hsmooth t)
  have hTA (T : L ≃ₗ⁅ℝ⁆ L) (hT : T ∈ ss) : Commute T.toLinearMap A.toLinearMap :=
    (mem_semisimpleActionCentralizer_iff E T t (hsmooth t)).mp
      ((mem_commonSemisimpleCentralizer E ss t).mp ht T hT)
  obtain ⟨S, U, hS, hU, hSU, hA, hTS, hcorrect⟩ :=
    exists_semisimple_factor_with_preserving_corrections A ss hss hpair hTA
  refine ⟨S, U, hS, hU, hSU, hA, hTS, ?_⟩
  intro g hg
  let B := polynomialModelLieEquiv (E.conjAct g) (hsmooth g)
  have hTB (T : L ≃ₗ⁅ℝ⁆ L) (hT : T ∈ ss) : Commute T.toLinearMap B.toLinearMap :=
    (mem_semisimpleActionCentralizer_iff E T g (hsmooth g)).mp
      ((mem_commonSemisimpleCentralizer E ss g).mp hg T hT)
  obtain ⟨u, hu⟩ := extension_outer_conjugation_identity E hsmooth t g
  obtain ⟨v, hv, hc⟩ := hcorrect B hTB u hu
  have hnew : E.inl v * g ∈ semisimpleActionCentralizer E S := by
    change E.conjAct (E.inl v * g) ∈
      Subgroup.centralizer {PolynomialExponentialCoordinates.groupAutomorphism (P := C) S}
    rw [map_mul, extension_conjAct_inl]
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply DFunLike.ext
    intro x
    have hh : polynomialInnerLieEquiv v (B (S x)) = S (polynomialInnerLieEquiv v (B x)) :=
      LinearMap.congr_fun hc.eq x
    change v * E.conjAct g (S x) * v⁻¹ = S (v * E.conjAct g x * v⁻¹)
    simpa only [polynomialInnerLieEquiv_apply, B, polynomialModelLieEquiv_apply] using hh
  refine ⟨v, hv, (mem_commonSemisimpleCentralizer E (S :: ss) (E.inl v * g)).mpr ?_⟩
  intro T hT
  rcases List.mem_cons.mp hT with he | hT
  · subst T
    exact hnew
  · exact (mem_commonSemisimpleCentralizer E ss (E.inl v * g)).mp
      ((commonSemisimpleCentralizer E ss).mul_mem
        (inl_mem_commonSemisimpleCentralizer_of_fixed E ss v hv) hg) T hT

end PolycyclicRecognition

end

end OAI
