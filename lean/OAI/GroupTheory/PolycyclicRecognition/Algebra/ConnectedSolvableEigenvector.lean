import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConnectedScalarCommutators
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SeparateDerivedClosure

namespace OAI

/-! # A common eigenvector for a connected solvable matrix action

Induct on the derived length. The connected derived subgroup has a common
eigenspace. The whole group preserves it, and acts there with scalar
commutators. Those commutators are trivial by connectedness and determinant
one, leaving a commuting action on this nonzero subspace.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

open scoped commutatorElement
variable {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ} [Nontrivial (Fin n → K)]

theorem connected_solvable_commonEigenspace_of_bound
    {G : Type*} [Group G] [TopologicalSpace G] [PreconnectedSpace G]
    [SeparatelyContinuousMul G] [ContinuousInv G]
    (hc₁ : ∀ g : G, Continuous (fun h : G => ⁅g, h⁆))
    (hc₂ : ∀ h : G, Continuous (fun g : G => ⁅g, h⁆))
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι)
    (d : ℕ) (hd : derivedSeries G d = ⊥) :
    ∃ χ : G → K, commonEigenspace (fun g => (linearAction (ι g)).toLinearMap) χ ≠ ⊥ := by
  induction d generalizing G with
  | zero =>
    have hg1 (g : G) : g = 1 := by
      have hg : g ∈ derivedSeries G 0 := Subgroup.mem_top g
      simpa only [hd, Subgroup.mem_bot] using hg
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → K)
    refine ⟨fun _ => 1, ?_⟩
    intro he
    have hm : v ∈ commonEigenspace (fun g => (linearAction (ι g)).toLinearMap) (fun _ => 1) := by
      apply (mem_commonEigenspace _ _ _).mpr
      intro g
      simp only [hg1 g, map_one, one_smul]
      rfl
    exact hv (by simpa only [he, Submodule.mem_bot] using hm)
  | succ d ih =>
    let A := commutator G
    let : SeparatelyContinuousMul A :=
      Topology.IsInducing.subtypeVal.separatelyContinuousMul A.subtype
    let : ContinuousInv A := Topology.IsInducing.subtypeVal.continuousInv (fun _ => rfl)
    have hApre : IsPreconnected (A : Set G) := by
      simpa only [A, _root_.commutator_def, Subgroup.coe_top] using
        isPreconnected_commutator hc₁ hc₂ (⊤ : Subgroup G) ⊤
          isPreconnected_univ isPreconnected_univ
    let : PreconnectedSpace A := Subtype.preconnectedSpace hApre
    have hAc₁ (g : A) : Continuous (fun h : A => ⁅g, h⁆) := by
      apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
      exact (hc₁ (g : G)).comp continuous_subtype_val
    have hAc₂ (h : A) : Continuous (fun g : A => ⁅g, h⁆) := by
      apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
      exact (hc₂ (h : G)).comp continuous_subtype_val
    have hshift (k : ℕ) : (derivedSeries A k).map A.subtype = derivedSeries G (k + 1) := by
      induction k with
      | zero => simp only [derivedSeries_zero, Subgroup.map_top, Subgroup.range_subtype,
          Nat.zero_add, derivedSeries_one, A]
      | succ k ihk =>
        simp only [derivedSeries_succ, Subgroup.map_commutator, ihk]
    have hAd : derivedSeries A d = ⊥ := by
      apply Subgroup.map_injective (f := A.subtype) Subtype.val_injective
      rw [Subgroup.map_bot, hshift, hd]
    obtain ⟨χA, hχA⟩ := ih hAc₁ hAc₂ (ι.comp A.subtype)
      (hι.comp continuous_subtype_val) hAd
    let ρ := linearAction.toMonoidHom.comp ι
    change normalCommonEigenspace A ρ χA ≠ ⊥ at hχA
    let W := normalCommonEigenspace A ρ χA
    have hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W :=
      connected_invariant_commonEigenspace ι hι A χA hχA
    have hs : ∀ g h : G, ∃ c : K, ∀ v ∈ W, ρ ⁅g, h⁆ v = c • v := by
      intro g h
      have hgh : ⁅g, h⁆ ∈ A := by
        change ⁅g, h⁆ ∈ (⁅(⊤ : Subgroup G), ⊤⁆ : Subgroup G)
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h)
      refine ⟨χA ⟨⁅g, h⁆, hgh⟩, ?_⟩
      intro v hv
      exact (mem_normalCommonEigenspace A ρ χA v).mp hv ⟨⁅g, h⁆, hgh⟩
    have htriv := connected_scalar_commutators_trivial ι hι W hW hs
    let R := invariantSubspaceAction ρ W hW
    let : Nontrivial W := (Submodule.nontrivial_iff_ne_bot).mpr hχA
    have hR (g h : G) : R ⁅g, h⁆ = 1 := by
      apply LinearEquiv.ext
      intro v
      apply Subtype.ext
      exact htriv g h v v.property
    have hcomm (g h : G) : Commute (R g).toLinearMap (R h).toLinearMap := by
      have hh : Commute (R g) (R h) := commutatorElement_eq_one_iff_commute.mp
        (by rw [← map_commutatorElement]; exact hR g h)
      exact hh.map LinearEquiv.automorphismGroup.toLinearMapMonoidHom
    obtain ⟨χ, hχ⟩ := exists_commonEigenspace (fun g => (R g).toLinearMap) hcomm
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
    refine ⟨χ, ?_⟩
    intro he
    have hvG : (v : Fin n → K) ∈
        commonEigenspace (fun g => (linearAction (ι g)).toLinearMap) χ := by
      apply (mem_commonEigenspace _ _ _).mpr
      intro g
      exact congrArg Subtype.val ((mem_commonEigenspace _ _ _).mp hv g)
    have hz : (v : Fin n → K) = 0 := by simpa only [he, Submodule.mem_bot] using hvG
    exact hv0 (Subtype.ext hz)

theorem connected_solvable_commonEigenspace
    {G : Type*} [Group G] [TopologicalSpace G] [PreconnectedSpace G]
    [SeparatelyContinuousMul G] [ContinuousInv G] [Group.IsSolvable G]
    (hc₁ : ∀ g : G, Continuous (fun h : G => ⁅g, h⁆))
    (hc₂ : ∀ h : G, Continuous (fun g : G => ⁅g, h⁆))
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι) :
    ∃ χ : G → K, commonEigenspace (fun g => (linearAction (ι g)).toLinearMap) χ ≠ ⊥ := by
  obtain ⟨d, hd⟩ := Group.IsSolvable.solvable (G := G)
  exact connected_solvable_commonEigenspace_of_bound hc₁ hc₂ ι hι d hd

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
