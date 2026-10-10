import Mathlib

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.CompactQuotient
variable {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
variable (H : Subgroup A) [H.Normal]

lemma compact_preimage_of_finite (hH : IsCompact (H : Set A))
    (T : Set (A ⧸ H)) (hT : T.Finite) : IsCompact ((QuotientGroup.mk' H) ⁻¹' T) := by
  let a : A ⧸ H → A := fun t => (QuotientGroup.mk_surjective t).choose
  have ha : ∀ t, QuotientGroup.mk' H (a t)=t := fun t =>
    (QuotientGroup.mk_surjective t).choose_spec
  have he : (QuotientGroup.mk' H) ⁻¹' T =
      ⋃ t∈T, (fun h : A => a t*h) '' (H : Set A) := by
    ext g
    constructor
    · intro hg
      refine Set.mem_iUnion.mpr ⟨QuotientGroup.mk' H g,Set.mem_iUnion.mpr ⟨hg,?_⟩⟩
      refine ⟨(a (QuotientGroup.mk' H g))⁻¹*g,?_,by simp⟩
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' H ((a (QuotientGroup.mk' H g))⁻¹*g)=1
      rw [map_mul,map_inv,ha,inv_mul_cancel]
    · intro hg
      obtain ⟨t,hut⟩ := Set.mem_iUnion.mp hg
      obtain ⟨ht,h,hHh,rfl⟩ := Set.mem_iUnion.mp hut
      change QuotientGroup.mk' H (a t*h)∈T
      have hh : QuotientGroup.mk' H h=1 := (QuotientGroup.eq_one_iff _).mpr hHh
      rw [map_mul,ha,hh,mul_one]
      exact ht
  rw [he]
  exact hT.isCompact_biUnion fun t _ => hH.image (continuous_const.mul continuous_id)

theorem compact_open_comap_finite
    (hcomp : IsCompact (H : Set A)) (hopen : IsOpen (H : Set A))
    (F : Subgroup (A ⧸ H)) (hF : (F : Set (A ⧸ H)).Finite) :
    IsCompact (F.comap (QuotientGroup.mk' H) : Set A) ∧
      IsOpen (F.comap (QuotientGroup.mk' H) : Set A) := by
  let _ : DiscreteTopology (A ⧸ H) := QuotientGroup.discreteTopology hopen
  exact ⟨compact_preimage_of_finite H hcomp F hF,
    (isOpen_discrete (F : Set (A ⧸ H))).preimage QuotientGroup.continuous_mk⟩

theorem finite_generating_approximate_powers
    (hopen : IsOpen (H : Set A)) (K : ℝ) (S : Set A)
    (hcomp : IsCompact S) (hone : (1 : A)∈S) (hsym : S⁻¹=S)
    (hgen : Subgroup.closure S=⊤)
    (hpow : ∀ R : ℕ, ∃ n≥R, IsApproximateSubgroup K (S^n)) :
    ∃ T : Set (A ⧸ H), T.Finite ∧ (1 : A ⧸ H)∈T ∧ T⁻¹=T ∧
      Subgroup.closure T=⊤ ∧
      ∀ R : ℕ, ∃ n≥R, IsApproximateSubgroup K (T^n) := by
  let _ : DiscreteTopology (A ⧸ H) := QuotientGroup.discreteTopology hopen
  refine ⟨(QuotientGroup.mk' H) '' S,
    isCompact_iff_finite.mp (hcomp.image QuotientGroup.continuous_mk),
    ⟨1,hone,map_one _⟩,?_,?_,?_⟩
  · rw [←Set.image_inv,hsym]
  · rw [←MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective _ QuotientGroup.mk_surjective
  · intro R
    obtain ⟨n,hn,ha⟩ := hpow R
    refine ⟨n,hn,?_⟩
    rw [←Set.image_pow]
    exact ha.image (QuotientGroup.mk' H)

theorem lift_finite_by_virtually_nilpotent
    (hcomp : IsCompact (H : Set A)) (hopen : IsOpen (H : Set A))
    (F : Subgroup (A ⧸ H)) [F.Normal] (hF : (F : Set (A ⧸ H)).Finite)
    (N : Subgroup ((A ⧸ H) ⧸ F)) [Group.IsNilpotent N] (hN : N.index≠0) :
    ∃ C : Subgroup A, ∃ hn : C.Normal, let _ := hn
      IsCompact (C : Set A) ∧ IsOpen (C : Set A) ∧
        ∃ M : Subgroup (A ⧸ C), Group.IsNilpotent M ∧ M.index≠0 := by
  let f : A →* (A ⧸ H) ⧸ F := (QuotientGroup.mk' F).comp (QuotientGroup.mk' H)
  have hf : Surjective f := QuotientGroup.mk_surjective.comp QuotientGroup.mk_surjective
  have hker : f.ker=F.comap (QuotientGroup.mk' H) := by
    change ((QuotientGroup.mk' F).comp (QuotientGroup.mk' H)).ker=_
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
  let e : A ⧸ f.ker ≃* (A ⧸ H) ⧸ F := QuotientGroup.quotientKerEquivOfSurjective f hf
  let M : Subgroup (A ⧸ f.ker) := N.comap e.toMonoidHom
  have hnil : Group.IsNilpotent M := by
    let j : M →* N :=
      {toFun := fun g => ⟨e g.val,g.property⟩
       map_one' := Subtype.ext (map_one e)
       map_mul' := fun g h => Subtype.ext (map_mul e g.val h.val)}
    have hj : Injective j := by
      intro g h he
      apply Subtype.ext
      exact e.injective (congrArg Subtype.val he)
    apply Subgroup.isNilpotent_of_ker_le_center j
    rw [(MonoidHom.ker_eq_bot_iff j).mpr hj]
    exact bot_le
  have hi : M.index=N.index := N.index_comap_of_surjective e.surjective
  have hc := compact_open_comap_finite H hcomp hopen F hF
  rw [←hker] at hc
  exact ⟨f.ker,inferInstance,hc.1,hc.2,M,hnil,hi ▸ hN⟩

end CriticalPercolation.CompactQuotient
end
end

end OAI
