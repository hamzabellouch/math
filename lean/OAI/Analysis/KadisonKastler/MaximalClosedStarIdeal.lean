import OAI.Analysis.Pureness.Completion.ClosedStarIdealQuotientCStar
import OAI.Analysis.TracialSplitting.SimpleIdeals
import Mathlib.Order.Zorn

namespace OAI

/-! # A maximal proper closed star ideal in a unital C-star algebra

This supplies the quotient step in the unital specialization of Sakai's
ideal-extension argument. The closure of a proper ideal remains proper:
otherwise the original ideal meets the open set of invertible elements.
-/

namespace KadisonKastler

noncomputable section

open Filter Topology CuntzPureness

variable {B : Type*} [CStarAlgebra B]

theorem twoSidedIdeal_eq_top_of_isUnit_mem (I : TwoSidedIdeal B)
    {x : B} (hx : x ∈ I) (hu : IsUnit x) : I = ⊤ := by
  obtain ⟨u, rfl⟩ := hu
  apply I.eq_top
  simpa using I.mul_mem_left (↑(u⁻¹) : B) (u : B) hx

theorem closedTwoSidedIdeal_ne_top {I : TwoSidedIdeal B} (hI : I ≠ ⊤) :
    Pureness.closedTwoSidedIdeal I ≠ ⊤ := by
  intro h
  have h1 : (1 : B) ∈ closure (I : Set B) := by
    rw [← Pureness.coe_closedTwoSidedIdeal]
    change (1 : B) ∈ Pureness.closedTwoSidedIdeal I
    rw [h]
    exact TwoSidedIdeal.mem_top B
  obtain ⟨x, hxunit, hx⟩ := mem_closure_iff_nhds.mp h1 _
    (Units.isOpen.mem_nhds isUnit_one)
  exact hI (twoSidedIdeal_eq_top_of_isUnit_mem I hx hxunit)

def idealChainUnion (c : Set (TwoSidedIdeal B)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) : TwoSidedIdeal B :=
  TwoSidedIdeal.mk' {x | ∃ I ∈ c, x ∈ I}
    (by obtain ⟨I, hI⟩ := hne; exact ⟨I, hI, I.zero_mem⟩)
    (by
      rintro x y ⟨I, hI, hx⟩ ⟨J, hJ, hy⟩
      obtain ⟨K, hK, hIK, hJK⟩ := hc.directedOn I hI J hJ
      exact ⟨K, hK, K.add_mem (hIK hx) (hJK hy)⟩)
    (by rintro x ⟨I, hI, hx⟩; exact ⟨I, hI, I.neg_mem hx⟩)
    (by rintro x y ⟨I, hI, hy⟩; exact ⟨I, hI, I.mul_mem_left x y hy⟩)
    (by rintro x y ⟨I, hI, hx⟩; exact ⟨I, hI, I.mul_mem_right x y hx⟩)

theorem mem_idealChainUnion (c : Set (TwoSidedIdeal B))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) (x : B) :
    x ∈ idealChainUnion c hc hne ↔ ∃ I ∈ c, x ∈ I := by
  simp only [idealChainUnion, TwoSidedIdeal.mem_mk', Set.mem_ofPred_eq]

theorem closedTwoSidedIdeal_star {I : TwoSidedIdeal B}
    (hstar : ∀ {x : B}, x ∈ I → star x ∈ I) {x : B}
    (hx : x ∈ Pureness.closedTwoSidedIdeal I) :
    star x ∈ Pureness.closedTwoSidedIdeal I := by
  rw [← SetLike.mem_coe, Pureness.coe_closedTwoSidedIdeal] at hx ⊢
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
  exact isClosed_closure.mem_of_tendsto hux.star
    (Eventually.of_forall fun n => subset_closure (hstar (hu n)))

theorem exists_maximal_proper_closedStarIdeal [Nontrivial B] :
    ∃ J : ClosedStarIdeal B, J.ideal ≠ ⊤ ∧
      ∀ K : ClosedStarIdeal B, K.ideal ≠ ⊤ → J.ideal ≤ K.ideal → K.ideal = J.ideal := by
  let S : Set (TwoSidedIdeal B) :=
    {I | IsClosed (I : Set B) ∧ (∀ {x : B}, x ∈ I → star x ∈ I) ∧ I ≠ ⊤}
  have hchain : ∀ c ⊆ S, IsChain (· ≤ ·) c →
      ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcs hc
    rcases c.eq_empty_or_nonempty with rfl | hne
    · refine ⟨⊥, ?_, by simp⟩
      refine ⟨?_, ?_, bot_ne_top⟩
      · simpa only [TwoSidedIdeal.coe_bot] using (isClosed_singleton : IsClosed ({0} : Set B))
      · intro x hx
        rw [TwoSidedIdeal.mem_bot] at hx ⊢
        rw [hx, star_zero]
    · let I := idealChainUnion c hc hne
      have hproper : I ≠ ⊤ := by
        intro h
        have hone : (1 : B) ∈ I := by rw [h]; exact TwoSidedIdeal.mem_top B
        obtain ⟨K, hK, h1⟩ := (mem_idealChainUnion c hc hne 1).mp hone
        exact (hcs hK).2.2 (K.eq_top h1)
      have hstar : ∀ {x : B}, x ∈ I → star x ∈ I := by
        intro x hx
        obtain ⟨K, hK, hxK⟩ := (mem_idealChainUnion c hc hne x).mp hx
        exact (mem_idealChainUnion c hc hne (star x)).mpr ⟨K, hK, (hcs hK).2.1 hxK⟩
      refine ⟨Pureness.closedTwoSidedIdeal I,
        ⟨?_, closedTwoSidedIdeal_star hstar, closedTwoSidedIdeal_ne_top hproper⟩, ?_⟩
      · simpa only [Pureness.coe_closedTwoSidedIdeal] using
          (isClosed_closure : IsClosed (closure (I : Set B)))
      · intro K hK x hx
        rw [← SetLike.mem_coe, Pureness.coe_closedTwoSidedIdeal]
        exact subset_closure ((mem_idealChainUnion c hc hne x).mpr ⟨K, hK, hx⟩)
  obtain ⟨J, hJ, hmax⟩ := zorn_le₀ S hchain
  refine ⟨⟨J, hJ.2.1, hJ.1⟩, hJ.2.2, ?_⟩
  intro K hK hJK
  exact le_antisymm (hmax ⟨K.isClosed, K.star_mem, hK⟩ hJK) hJK

local instance maximalClosedStarIdealInstance1 : PartialOrder B := CStarAlgebra.spectralOrder B
local instance maximalClosedStarIdealInstance2 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

/-- Every unital representation of the maximal quotient is faithful. The
preimage of its kernel is a closed star ideal, so maximality applies directly. -/
theorem maximal_closedStarIdeal_quotient_injective
    (J : ClosedStarIdeal B)
    (hmax : ∀ K : ClosedStarIdeal B, K.ideal ≠ ⊤ →
      J.ideal ≤ K.ideal → K.ideal = J.ideal)
    {C : Type*} [CStarAlgebra C] [Nontrivial C]
    (ψ : J.Quotient →⋆ₐ[ℂ] C) : Function.Injective ψ := by
  let θ : B →⋆ₐ[ℂ] C := ψ.comp J.quotientStarHom
  let K : ClosedStarIdeal B := {
    ideal := TwoSidedIdeal.ker θ
    star_mem := by
      intro x hx
      apply (TwoSidedIdeal.mem_ker θ).mpr
      rw [map_star, (TwoSidedIdeal.mem_ker θ).mp hx, star_zero]
    isClosed := by
      have hc : Continuous θ :=
        (θ.toLinearMap.mkContinuous 1 (fun x => by
          change ‖θ x‖ ≤ 1 * ‖x‖
          simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le θ x)).continuous
      have he : (TwoSidedIdeal.ker θ : Set B) = {x | θ x = 0} := by
        ext x
        exact TwoSidedIdeal.mem_ker θ
      rw [he]
      exact isClosed_eq hc continuous_const }
  have hK : K.ideal ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ K.ideal := by rw [h]; exact TwoSidedIdeal.mem_top B
    have hzero := (TwoSidedIdeal.mem_ker θ).mp h1
    exact one_ne_zero (by simpa only [map_one] using hzero)
  have hJK : J.ideal ≤ K.ideal := by
    intro x hx
    apply (TwoSidedIdeal.mem_ker θ).mpr
    change ψ (J.quotientStarHom x) = 0
    have hzero : J.quotientStarHom x = 0 := Quotient.sound hx
    rw [hzero, map_zero]
  have heq := hmax K hK hJK
  intro x y hxy
  obtain ⟨a, rfl⟩ := J.quotientMap_surjective x
  obtain ⟨b, rfl⟩ := J.quotientMap_surjective y
  change ψ (J.quotientStarHom a) = ψ (J.quotientStarHom b) at hxy
  have hab : a - b ∈ K.ideal := by
    apply (TwoSidedIdeal.mem_ker θ).mpr
    change ψ (J.quotientStarHom (a - b)) = 0
    simpa only [map_sub, sub_eq_zero] using hxy
  rw [heq] at hab
  have hzero : J.quotientStarHom (a - b) = 0 := Quotient.sound hab
  change J.quotientStarHom a = J.quotientStarHom b
  exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)

end

end KadisonKastler

end OAI
