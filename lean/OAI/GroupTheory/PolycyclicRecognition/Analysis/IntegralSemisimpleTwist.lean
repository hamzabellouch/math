import OAI.GroupTheory.PolycyclicRecognition.Lattices.JointFixedReductionData
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CommutingIntegralHom
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothPolynomialAutomorphisms
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorSystemSymmetrySubgroup

namespace OAI

/-! # Removing the actual semisimple generator action

The normalized section and its commuting semisimple factors are constructed
in the original extension. Their integral action fixes the actual cocycle,
and removing it leaves unipotent actions on every quotient generator.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L] [Group G]

theorem integral_semisimple_twist {n : ℕ}
    (E : GroupExtension L G (IntegralLatticeGroup n))
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) :
    ∃ (σ : E.Section) (hσ : σ 1 = 1) (χ : IntegralLatticeGroup n →* MulAut L),
      let R := GroupExtensionSection.factorSystem E σ hσ
      ∃ (hc : ∀ q r, Commute (R.action q) (χ r))
        (hf : ∀ q r s, χ q (R.factor r s) = R.factor r s),
      (∀ q, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (χ q)) ∧
      (∀ q, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ ((R.twist χ hc hf).action q)) ∧
      ∀ i : Fin n, ∃ U : L ≃ₗ⁅ℝ⁆ L, IsNilpotent (U.toLinearMap - 1) ∧
        ∀ x, (R.twist χ hc hf).action (integralLatticeGenerator n i) x = U x := by
  classical
  let qs := List.ofFn (integralLatticeGenerator n)
  obtain ⟨D⟩ := exists_jointFixedReductionData E hsmooth qs
  have hj (i : Fin n) := D.jordanLifts (integralLatticeGenerator n i)
    (List.mem_ofFn.mpr ⟨i, rfl⟩)
  choose S hS U hU hSU hA using hj
  let a := fun i => PolynomialExponentialCoordinates.groupAutomorphism (P := P) (S i)
  have ha (i j : Fin n) : Commute (a i) (a j) := by
    apply DFunLike.ext
    intro x
    exact LinearMap.congr_fun (D.commute (S i) (hS i) (S j) (hS j)).eq x
  let χ := commutingIntegralHom a ha
  let R := GroupExtensionSection.factorSystem E D.sectionMap D.normalized
  have hsym (i : Fin n) : a i ∈ factorSystemSymmetries R := by
    refine ⟨?_, ?_⟩
    · intro q
      apply DFunLike.ext
      intro x
      have h := LinearMap.congr_fun (D.action_commutes (S i) (hS i) q).eq x
      change S i (D.action q x) = D.action q (S i x) at h
      change S i (E.conjAct (D.sectionMap q) x) = E.conjAct (D.sectionMap q) (S i x)
      simpa only [JointFixedReductionData.action, polynomialModelLieEquiv_apply] using h
    · exact D.factorsFixed (S i) (hS i)
  have hχsym (q : IntegralLatticeGroup n) : χ q ∈ factorSystemSymmetries R :=
    commutingIntegralHom_range_le a ha (factorSystemSymmetries R) hsym ⟨q, rfl⟩
  have hc (q r : IntegralLatticeGroup n) : Commute (R.action q) (χ r) :=
    ((hχsym r).1 q).symm
  have hf (q r s : IntegralLatticeGroup n) : χ q (R.factor r s) = R.factor r s :=
    (hχsym q).2 r s
  have hχ (q : IntegralLatticeGroup n) : χ q ∈ smoothPolynomialAutomorphisms :=
    commutingIntegralHom_range_le a ha smoothPolynomialAutomorphisms
      (fun i => groupAutomorphism_mem_smooth (S i)) ⟨q, rfl⟩
  refine ⟨D.sectionMap, D.normalized, χ, hc, hf, fun q => (hχ q).1, ?_, ?_⟩
  · intro q
    exact (hχ q).2.comp (hsmooth (D.sectionMap q))
  · intro i
    refine ⟨U i, hU i, ?_⟩
    intro x
    have hg : χ (integralLatticeGenerator n i) = a i :=
      commutingIntegralHom_generator a ha i
    change (χ (integralLatticeGenerator n i))⁻¹
      (E.conjAct (D.sectionMap (integralLatticeGenerator n i)) x) = U i x
    rw [hg]
    have he : E.conjAct (D.sectionMap (integralLatticeGenerator n i)) x = S i (U i x) := by
      have h := LinearMap.congr_fun (hA i) x
      change polynomialModelLieEquiv _ _ x = S i (U i x) at h
      rwa [polynomialModelLieEquiv_apply] at h
    rw [he]
    exact (S i).symm_apply_apply (U i x)

end PolycyclicRecognition

end

end OAI
