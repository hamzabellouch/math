import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteSemisimpleCocycleReduction
import OAI.GroupTheory.PolycyclicRecognition.Lattices.ExtensionFixedCocycleSection
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubgroupExtensionSection

namespace OAI

/-! # Simultaneously fixed section factors for finitely many quotient lifts

The original extension has a normalized section centralizing a finite
commuting semisimple family. All its factors are fixed by that entire family,
and the specified quotient elements retain their semisimple Jordan factors.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q] [IsMulCommutative Q]

omit [LieRing.IsNilpotent L] [IsMulCommutative Q] in
theorem inl_mem_semisimpleCentralizer_of_center (E : GroupExtension L G Q)
    (S : L ≃ₗ⁅ℝ⁆ L) (x : L) (hx : x ∈ Subgroup.center L) :
    E.inl x ∈ semisimpleActionCentralizer E S := by
  have hi : MulAut.conj x = 1 := by
    apply DFunLike.ext
    intro y
    change x * y * x⁻¹ = y
    rw [← Subgroup.mem_center_iff.mp hx y]
    group
  change E.conjAct (E.inl x) ∈
    Subgroup.centralizer {PolynomialExponentialCoordinates.groupAutomorphism (P := P) S}
  rw [extension_conjAct_inl, hi]
  exact Subgroup.one_mem _

theorem exists_finite_fixed_cocycle_section (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) (qs : List Q) :
    ∃ ss : List (L ≃ₗ⁅ℝ⁆ L),
      (∀ S ∈ ss, Module.End.IsSemisimple S.toLinearMap) ∧
      (∀ S ∈ ss, ∀ T ∈ ss, Commute S.toLinearMap T.toLinearMap) ∧
      ∃ σ : E.Section, σ 1 = 1 ∧
        (∀ S ∈ ss, ∀ q, σ q ∈ semisimpleActionCentralizer E S) ∧
        (∀ S ∈ ss, ∀ q r, S (GroupExtensionSection.factor E σ q r) =
          GroupExtensionSection.factor E σ q r) ∧
        ∀ q ∈ qs, ∃ S ∈ ss, ∃ U : L ≃ₗ⁅ℝ⁆ L,
          IsNilpotent (U.toLinearMap - 1) ∧ Commute S.toLinearMap U.toLinearMap ∧
          (polynomialModelLieEquiv (E.conjAct (σ q)) (hsmooth (σ q))).toLinearMap =
            S.toLinearMap * U.toLinearMap := by
  classical
  obtain ⟨ss₀, hss₀, hpair₀, hsurj, hlifts⟩ := exists_finite_semisimple_lift_family E hsmooth qs
  have hh : ∀ q : {q : Q // q ∈ qs}, ∃ g : G,
      g ∈ commonSemisimpleCentralizer E ss₀ ∧ E.rightHom g = (q : Q) ∧
      ∃ S ∈ ss₀, ∃ U : L ≃ₗ⁅ℝ⁆ L, IsNilpotent (U.toLinearMap - 1) ∧
        Commute S.toLinearMap U.toLinearMap ∧
        (polynomialModelLieEquiv (E.conjAct g) (hsmooth g)).toLinearMap =
          S.toLinearMap * U.toLinearMap := fun q => hlifts q q.property
  choose g hg hgq s hs u hu hsu hgu using hh
  let ss := qs.attach.map s
  have hmem (S : L ≃ₗ⁅ℝ⁆ L) (hS : S ∈ ss) : S ∈ ss₀ := by
    obtain ⟨q, _, hq⟩ := List.mem_map.mp hS
    rw [← hq]
    exact hs q
  obtain ⟨σ, hσ, hσH⟩ := exists_normalized_section_in_subgroup E
    (commonSemisimpleCentralizer E ss₀) hsurj
  have hσS : ∀ S ∈ ss₀, ∀ q, σ q ∈ semisimpleActionCentralizer E S :=
    fun S hS q => (mem_commonSemisimpleCentralizer E ss₀ (σ q)).mp (hσH q) S hS
  let F := GroupExtensionSection.factorSystem E σ hσ
  let A := fun q => polynomialModelLieEquiv (E.conjAct (σ q)) (hsmooth (σ q))
  have hact : ∀ q x, F.action q x = A q x :=
    fun _ _ => (polynomialModelLieEquiv_apply _ _ _).symm
  have hcomm : ∀ S ∈ ss, ∀ q, Commute S.toLinearMap (A q).toLinearMap := by
    intro S hS q
    exact (mem_semisimpleActionCentralizer_iff E S (σ q) (hsmooth (σ q))).mp
      (hσS S (hmem S hS) q)
  have hpair : ∀ S ∈ ss, ∀ T ∈ ss, Commute S.toLinearMap T.toLinearMap :=
    fun S hS T hT => hpair₀ S (hmem S hS) T (hmem T hT)
  have hsemisimple : ∀ S ∈ ss, Module.End.IsSemisimple S.toLinearMap :=
    fun S hS => hss₀ S (hmem S hS)
  have hlift : ∀ S ∈ ss, ∃ q₀ : Q, ∃ U : L ≃ₗ⁅ℝ⁆ L,
      IsNilpotent (U.toLinearMap - 1) ∧ Commute S.toLinearMap U.toLinearMap ∧
      (A q₀).toLinearMap = S.toLinearMap * U.toLinearMap := by
    intro S hS
    obtain ⟨q, _, hq⟩ := List.mem_map.mp hS
    subst S
    obtain ⟨W, hW, hsW, he⟩ := centralizer_same_fiber_jordan_factor E hsmooth (s q) (u q)
      (g q) (σ q) ((mem_commonSemisimpleCentralizer E ss₀ _).mp (hg q) _ (hs q))
      (hσS _ (hs q) q) ((σ.rightHom_section q).trans (hgq q).symm) (hu q) (hsu q) (hgu q)
    exact ⟨q, W, hW, hsW, he⟩
  obtain ⟨b, hb, hbZ, _, hfixed⟩ := finite_semisimple_cocycle_reduction F A hact ss
    hsemisimple hpair hcomm hlift
  let θ := GroupExtensionSection.gaugeSection E σ b
  have hθS : ∀ S ∈ ss, ∀ q, θ q ∈ semisimpleActionCentralizer E S := by
    intro S hS q
    exact (semisimpleActionCentralizer E S).mul_mem
      (inl_mem_semisimpleCentralizer_of_center E S (b q) (hbZ q)) (hσS S (hmem S hS) q)
  refine ⟨ss, hsemisimple, hpair, θ, GroupExtensionSection.gaugeSection_one E σ hσ b hb,
    hθS, ?_, ?_⟩
  · intro S hS q r
    rw [GroupExtensionSection.factor_gaugeSection E σ hσ b hb]
    exact hfixed S hS q r
  · intro q hq
    let i : {q : Q // q ∈ qs} := ⟨q, hq⟩
    have hi : s i ∈ ss := List.mem_map.mpr ⟨i, List.mem_attach _ _, rfl⟩
    obtain ⟨W, hW, hsW, he⟩ := centralizer_same_fiber_jordan_factor E hsmooth (s i) (u i)
      (g i) (θ q) ((mem_commonSemisimpleCentralizer E ss₀ _).mp (hg i) _ (hs i))
      (hθS _ hi q) ((θ.rightHom_section q).trans (hgq i).symm) (hu i) (hsu i) (hgu i)
    exact ⟨s i, hi, W, hW, hsW, he⟩

end PolycyclicRecognition

end

end OAI
