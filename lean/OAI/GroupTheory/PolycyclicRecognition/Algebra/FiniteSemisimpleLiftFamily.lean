import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommonCentralizerSurjection
import OAI.GroupTheory.PolycyclicRecognition.Geometry.InnerCorrectedJordanFactor

namespace OAI

/-! # A finite commuting semisimple family adapted to quotient generators

Successive inner corrections preserve the earlier semisimple factors. Every
member of a finite list in the abelian quotient therefore has a lift in one
common centralizer, with its semisimple factor belonging to that family.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

omit [LieRing.IsNilpotent L] in
theorem extension_conjugationLinear_inl_mul (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) (v : L) (g : G) :
    (polynomialModelLieEquiv (E.conjAct (E.inl v * g)) (hsmooth _)).toLinearMap =
      (polynomialInnerLieEquiv v).toLinearMap *
        (polynomialModelLieEquiv (E.conjAct g) (hsmooth g)).toLinearMap := by
  apply LinearMap.ext
  intro x
  change polynomialModelLieEquiv (E.conjAct (E.inl v * g)) (hsmooth _) x =
    polynomialInnerLieEquiv v (polynomialModelLieEquiv (E.conjAct g) (hsmooth g) x)
  rw [polynomialModelLieEquiv_apply, polynomialModelLieEquiv_apply,
    polynomialInnerLieEquiv_apply, map_mul, extension_conjAct_inl]
  rfl

def HasSemisimpleLift (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g))
    (ss : List (L ≃ₗ⁅ℝ⁆ L)) (q : Q) : Prop :=
  ∃ g : G, g ∈ commonSemisimpleCentralizer E ss ∧ E.rightHom g = q ∧
    ∃ S ∈ ss, ∃ U : L ≃ₗ⁅ℝ⁆ L, IsNilpotent (U.toLinearMap - 1) ∧
      Commute S.toLinearMap U.toLinearMap ∧
      (polynomialModelLieEquiv (E.conjAct g) (hsmooth g)).toLinearMap =
        S.toLinearMap * U.toLinearMap

theorem HasSemisimpleLift.extend {E : GroupExtension L G Q}
    {hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)}
    {ss : List (L ≃ₗ⁅ℝ⁆ L)} {q : Q} (hq : HasSemisimpleLift E hsmooth ss q)
    (S : L ≃ₗ⁅ℝ⁆ L)
    (hc : ∀ g ∈ commonSemisimpleCentralizer E ss, ∃ v : L,
      (∀ T ∈ ss, T v = v) ∧ E.inl v * g ∈ commonSemisimpleCentralizer E (S :: ss)) :
    HasSemisimpleLift E hsmooth (S :: ss) q := by
  obtain ⟨g, hg, hgq, T, hT, U, hU, hTU, hA⟩ := hq
  obtain ⟨v, hv, hvg⟩ := hc g hg
  obtain ⟨W, hW, hTW, he⟩ := inner_correction_preserves_jordan_factor
    (polynomialModelLieEquiv (E.conjAct g) (hsmooth g)) T U hU hTU hA v (hv T hT)
  refine ⟨E.inl v * g, hvg, ?_, T, List.mem_cons_of_mem S hT, W, hW, hTW, ?_⟩
  · rw [map_mul, E.rightHom_inl, one_mul, hgq]
  · rw [extension_conjugationLinear_inl_mul]
    exact he

variable [IsMulCommutative Q]

theorem exists_finite_semisimple_lift_family (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) (qs : List Q) :
    ∃ ss : List (L ≃ₗ⁅ℝ⁆ L),
      (∀ T ∈ ss, Module.End.IsSemisimple T.toLinearMap) ∧
      (∀ T ∈ ss, ∀ R ∈ ss, Commute T.toLinearMap R.toLinearMap) ∧
      Function.Surjective (E.rightHom.comp (commonSemisimpleCentralizer E ss).subtype) ∧
      ∀ q ∈ qs, HasSemisimpleLift E hsmooth ss q := by
  induction qs with
  | nil =>
    refine ⟨[], by simp, by simp, ?_, by simp⟩
    intro q
    obtain ⟨g, hg⟩ := E.rightHom_surjective q
    exact ⟨⟨g, (mem_commonSemisimpleCentralizer E [] g).mpr (by simp)⟩, hg⟩
  | cons q qs ih =>
    obtain ⟨ss, hss, hpair, hsurj, hlifts⟩ := ih
    obtain ⟨t, htq⟩ := hsurj q
    obtain ⟨S, U, hS, hU, hSU, hA, hTS, hc⟩ :=
      common_semisimpleCentralizer_step E hsmooth ss hss hpair t t.property
    have hnewss : ∀ T ∈ S :: ss, Module.End.IsSemisimple T.toLinearMap := by
      intro T hT
      rcases List.mem_cons.mp hT with h | h
      · subst T; exact hS
      · exact hss T h
    have hnewpair : ∀ T ∈ S :: ss, ∀ R ∈ S :: ss, Commute T.toLinearMap R.toLinearMap := by
      intro T hT R hR
      rcases List.mem_cons.mp hT with hT | hT <;> rcases List.mem_cons.mp hR with hR | hR
      · subst T; subst R; exact Commute.refl _
      · subst T; exact (hTS R hR).symm
      · subst R; exact hTS T hT
      · exact hpair T hT R hR
    have hnewsurj : Function.Surjective
        (E.rightHom.comp (commonSemisimpleCentralizer E (S :: ss)).subtype) := by
      intro r
      obtain ⟨g, hgr⟩ := hsurj r
      obtain ⟨v, _, hv⟩ := hc g g.property
      refine ⟨⟨E.inl v * g, hv⟩, ?_⟩
      change E.rightHom (E.inl v * g) = r
      rw [map_mul, E.rightHom_inl, one_mul]
      exact hgr
    have htnew : (t : G) ∈ commonSemisimpleCentralizer E (S :: ss) := by
      apply (mem_commonSemisimpleCentralizer E (S :: ss) t).mpr
      intro T hT
      rcases List.mem_cons.mp hT with h | h
      · subst T
        apply (mem_semisimpleActionCentralizer_iff E S t (hsmooth t)).mpr
        rw [hA]
        exact (Commute.refl _).mul_right hSU
      · exact (mem_commonSemisimpleCentralizer E ss t).mp t.property T h
    refine ⟨S :: ss, hnewss, hnewpair, hnewsurj, ?_⟩
    intro r hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst r
      exact ⟨t, htnew, htq, S, by simp, U, hU, hSU, hA⟩
    · exact (hlifts r hr).extend S hc

end PolycyclicRecognition

end

end OAI
