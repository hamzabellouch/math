import Mathlib

namespace OAI

 

namespace Campana

 
def VirtuallyAbelian (G : Type*) [Group G] : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧ IsMulCommutative H

section FiniteKernel

variable {G A : Type*} [Group G] [CommGroup A]

 
theorem commutatorSet_subset_ker (f : G →* A) :
    commutatorSet G ⊆ (f.ker : Set G) := by
  intro x hx
  apply Abelianization.commutator_subset_ker f
  rw [commutator_eq_closure]
  exact Subgroup.subset_closure hx

 

theorem finiteIndex_center_of_finite_kernel [Group.FG G]
    (f : G →* A) [Finite f.ker] : (Subgroup.center G).FiniteIndex := by
  have : Finite (commutatorSet G) :=
    Set.finite_coe_iff.mpr ((Set.toFinite (f.ker : Set G)).subset
      (commutatorSet_subset_ker f))
  infer_instance

 

theorem virtuallyAbelian_of_finite_kernel [Group.FG G]
    (f : G →* A) [Finite f.ker] : VirtuallyAbelian G := by
  exact ⟨Subgroup.center G, finiteIndex_center_of_finite_kernel f, inferInstance⟩

end FiniteKernel

section FiniteIndex

variable {G : Type*} [Group G]

 

theorem finiteIndex_map_subtype (H : Subgroup G) [H.FiniteIndex]
    (K : Subgroup H) [K.FiniteIndex] : (K.map H.subtype).FiniteIndex := by
  rw [Subgroup.finiteIndex_iff, Subgroup.index_map_subtype]
  exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero

 
theorem virtuallyAbelian_of_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (hH : VirtuallyAbelian H) : VirtuallyAbelian G := by
  obtain ⟨K, hK, hcomm⟩ := hH
  let := hK
  refine ⟨K.map H.subtype, finiteIndex_map_subtype H K, ?_⟩
  apply IsMulCommutative.of_setLike_mul_comm
  rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
  exact congrArg (fun k : K => (k : G))
    (isMulCommutative_iff.mp hcomm ⟨x', hx'⟩ ⟨y', hy'⟩)

 
theorem virtuallyAbelian_of_surjective {H : Type*} [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hG : VirtuallyAbelian G) :
    VirtuallyAbelian H := by
  obtain ⟨K, hK, hcomm⟩ := hG
  refine ⟨K.map f, ?_, ?_⟩
  · apply Subgroup.finiteIndex_iff.mpr
    exact ne_zero_of_dvd_ne_zero hK.index_ne_zero (K.index_map_dvd hf)
  · apply IsMulCommutative.of_setLike_mul_comm
    rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
    simpa using congrArg (fun k : K => f k)
      (isMulCommutative_iff.mp hcomm ⟨x', hx'⟩ ⟨y', hy'⟩)

 
theorem virtuallyAbelian_iff_mulEquiv {H : Type*} [Group H] (e : G ≃* H) :
    VirtuallyAbelian G ↔ VirtuallyAbelian H :=
  ⟨virtuallyAbelian_of_surjective e.toMonoidHom e.surjective,
    virtuallyAbelian_of_surjective e.symm.toMonoidHom e.symm.surjective⟩

end FiniteIndex

 

theorem virtuallyAbelian_fundamentalGroup_iff {X : Type*} [TopologicalSpace X]
    {x y : X} (p : Path x y) :
    VirtuallyAbelian (FundamentalGroup X x) ↔ VirtuallyAbelian (FundamentalGroup X y) :=
  virtuallyAbelian_iff_mulEquiv (FundamentalGroup.fundamentalGroupMulEquivOfPath p)

section ResidualFiniteness

variable {G H : Type*} [Group G] [Group H]

 
theorem residuallyFinite_of_injective [Group.ResiduallyFinite H]
    (f : G →* H) (hf : Function.Injective f) : Group.ResiduallyFinite G := by
  apply Group.residuallyFinite_iff_forall_finiteIndexNormalSubgroup.mpr
  intro g hg
  apply hf
  rw [map_one]
  apply Group.eq_one_iff_forall_finiteIndexNormalSubroup
  intro K
  exact hg (K.comap f)

 

theorem residuallyFinite_pi {ι : Type*} (P : ι → Type*) [∀ i, Group (P i)]
    [∀ i, Group.ResiduallyFinite (P i)] : Group.ResiduallyFinite (∀ i, P i) := by
  apply Group.residuallyFinite_iff_forall_finiteIndexNormalSubgroup.mpr
  intro g hg
  funext i
  apply Group.eq_one_iff_forall_finiteIndexNormalSubroup
  intro K
  exact hg (K.comap (Pi.evalMonoidHom P i))

 
theorem residuallyFinite_int : Group.ResiduallyFinite (Multiplicative ℤ) := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  let n := (Multiplicative.toAdd g).natAbs + 1
  have : NeZero n := ⟨Nat.succ_ne_zero _⟩
  let f : Multiplicative ℤ →* Multiplicative (ZMod n) :=
    (Int.castAddHom (ZMod n)).toMultiplicative
  refine ⟨Multiplicative (ZMod n), inferInstance, inferInstance, f, ?_⟩
  intro h
  have hzero : (↑(Multiplicative.toAdd g) : ZMod n) = 0 := h
  have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hg
  simp only [Int.natAbs_natCast] at hle
  exact (Nat.not_succ_le_self _) hle

 
theorem residuallyFinite_of_fg_commGroup (A : Type*) [CommGroup A] [Group.FG A] :
    Group.ResiduallyFinite A := by
  obtain ⟨ι, j, _, _, p, hp, e, ⟨f⟩⟩ :=
    CommGroup.equiv_free_prod_prod_multiplicative_zmod A
  have : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have : ∀ i, Finite (Multiplicative (ZMod (p i ^ e i))) := fun i => inferInstance
  have : Group.ResiduallyFinite (Multiplicative ℤ) := residuallyFinite_int
  have : Group.ResiduallyFinite (j → Multiplicative ℤ) := residuallyFinite_pi _
  have : Group.ResiduallyFinite ((i : ι) → Multiplicative (ZMod (p i ^ e i))) :=
    residuallyFinite_pi _
  exact residuallyFinite_of_injective f.toMonoidHom f.injective

 
theorem residuallyFinite_of_finiteIndex (K : Subgroup G) [K.FiniteIndex]
    [Group.ResiduallyFinite K] : Group.ResiduallyFinite G := by
  rw [Group.residuallyFinite_iff_exists_finiteIndex]
  intro g hg
  by_cases hgK : g ∈ K
  · have hgne : (⟨g, hgK⟩ : K) ≠ 1 := fun h => hg (congrArg Subtype.val h)
    obtain ⟨L, hL, hgL⟩ := Group.residuallyFinite_iff_exists_finiteIndex.mp
      (inferInstance : Group.ResiduallyFinite K) ⟨g, hgK⟩ hgne
    let := hL
    refine ⟨L.map K.subtype, finiteIndex_map_subtype K L, ?_⟩
    rintro ⟨x, hx, hxg⟩
    have : x = ⟨g, hgK⟩ := Subtype.ext hxg
    exact hgL (this ▸ hx)
  · exact ⟨K, inferInstance, hgK⟩

open scoped IsMulCommutative in
 
theorem residuallyFinite_of_fg_virtuallyAbelian [Group.FG G]
    (hG : VirtuallyAbelian G) : Group.ResiduallyFinite G := by
  obtain ⟨K, hK, hcomm⟩ := hG
  let := hK
  let := hcomm
  have : Group.ResiduallyFinite K := residuallyFinite_of_fg_commGroup K
  exact residuallyFinite_of_finiteIndex K

 

theorem exists_finiteIndex_disjoint [Group.ResiduallyFinite G]
    (F : Subgroup G) [Finite F] :
    ∃ K : Subgroup G, K.FiniteIndex ∧ K ⊓ F = ⊥ := by
  classical
  let S := {x : F // x ≠ 1}
  have hnontrivial (s : S) : (s.val : G) ≠ 1 := by
    intro h
    exact s.property (Subtype.ext h)
  choose K hK using fun s : S =>
    Group.exists_finiteIndexNormalSubgroup_notMem (s.val : G) (hnontrivial s)
  refine ⟨⨅ s, (K s).toSubgroup,
    Subgroup.finiteIndex_iInf (fun s => inferInstance), ?_⟩
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  by_contra hgne
  let s : S := ⟨⟨g, hg.2⟩, fun h => hgne (congrArg Subtype.val h)⟩
  exact hK s (Subgroup.mem_iInf.mp hg.1 s)

end ResidualFiniteness

 

theorem finite_by_abelian {G A : Type*} [Group G] [Group.FG G] [CommGroup A]
    (f : G →* A) [Finite f.ker] :
    VirtuallyAbelian G ∧ Group.ResiduallyFinite G ∧
      ∃ K : Subgroup G, K.FiniteIndex ∧ K ⊓ f.ker = ⊥ := by
  have hv := virtuallyAbelian_of_finite_kernel f
  have hr := residuallyFinite_of_fg_virtuallyAbelian hv
  exact ⟨hv, hr, exists_finiteIndex_disjoint f.ker⟩

end Campana

end OAI
