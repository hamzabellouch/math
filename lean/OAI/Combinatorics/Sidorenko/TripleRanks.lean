import OAI.Combinatorics.Sidorenko.Reduction

namespace OAI

namespace SidorenkoCounterexample
open Module
section GeneralIsometry
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

/-- Orthogonal complements commute with isometries between different spaces. -/
theorem orthogonal_map_isometry_between
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (e : E ≃ₗ[K] F) (he : ∀ x y, η (e x) (e y) = ω x y)
    (U : Submodule K E) :
    η.orthogonal (U.map e.toLinearMap) = (ω.orthogonal U).map e.toLinearMap := by
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    intro u hu
    rw [← he,e.apply_symm_apply]
    exact hx (e u) ⟨u,hu,rfl⟩
  · rintro ⟨y,hy,rfl⟩ _ ⟨u,hu,rfl⟩
    change η (e u) (e y) = 0
    rw [he]
    exact hy u hu

end GeneralIsometry
section Horizontal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def horizontalSpace : Submodule K (V × Module.Dual K V) :=
  (LinearMap.snd K V (Module.Dual K V)).ker

@[simp] theorem mem_horizontalSpace (p : V × Module.Dual K V) :
    p ∈ horizontalSpace (K := K) ↔ p.2 = 0 := Iff.rfl

theorem horizontalSpace_selforthogonal :
    canonicalSymplectic.orthogonal (horizontalSpace (K := K) (V := V)) = horizontalSpace := by
  ext x
  constructor
  · intro hx
    change x.2 = 0
    ext v
    have hh := hx (v,0) (by rfl)
    simpa only [canonicalSymplectic_apply,LinearMap.zero_apply,sub_zero] using hh
  · intro hx v hv
    change x.2 v.1 - v.2 x.1 = 0
    rw [(mem_horizontalSpace x).mp hx,(mem_horizontalSpace v).mp hv]
    simp

noncomputable def verticalSpaceEquiv : Module.Dual K V ≃ₗ[K]
    verticalSpace (K := K) (V := V) where
  toFun f := ⟨(0,f),rfl⟩
  invFun x := x.val.2
  map_add' _ _ := by ext <;> simp
  map_smul' a f := by ext <;> simp
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext ((mem_verticalSpace x.val).mp x.property).symm rfl

end Horizontal
section TripleOneBlock
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)



theorem triple_pair_block (ha : ω.IsAlt)
    (L M N : Submodule K E) (hL : ω.orthogonal L = L)
    (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hzero : (L ⊓ M) ⊓ N = ⊥) :
    ∃ B Q : Submodule K E,
      (ω.restrict B).Nondegenerate ∧ (L ⊓ M) ≤ B ∧ Q ≤ B ∧ Q ≤ N ∧
      finrank K Q = finrank K ↥(L ⊓ M) ∧
      B = (L ⊓ M) ⊔ Q ∧
      L = (L ⊓ M) ⊔ (L ⊓ ω.orthogonal B) ∧
      M = (L ⊓ M) ⊔ (M ⊓ ω.orthogonal B) ∧
      N = Q ⊔ (N ⊓ ω.orthogonal B) ∧
      L ⊓ N ≤ ω.orthogonal B ∧ M ⊓ N ≤ ω.orthogonal B ∧
      (L ⊓ ω.orthogonal B) ⊓ (M ⊓ ω.orthogonal B) = ⊥ ∧
      (∀ A ∈ ({L,M,N} : Set (Submodule K E)),
        (ω.restrict (ω.orthogonal B)).orthogonal (A.comap (ω.orthogonal B).subtype) =
          A.comap (ω.orthogonal B).subtype) ∧
      ∃ e : (↥(L ⊓ M) × Module.Dual K ↥(L ⊓ M)) ≃ₗ[K] B,
        (∀ s : ↥(L ⊓ M), (e (s,0)).val = s.val) ∧
        (verticalSpace.map e.toLinearMap).map B.subtype = Q ∧
        ∀ x y, ω (e x).val (e y).val = canonicalSymplectic x y := by
  let S := L ⊓ M
  have hS : S ≤ ω.orthogonal S := by
    intro s hs t ht
    exact hL.ge hs.1 t ht.1
  obtain ⟨B,hB,hSB,e,heS,heN,heform⟩ := exists_pair_block ω ha S N hS hN hzero
  let T : Submodule K B := (horizontalSpace (K := K) (V := S)).map e.toLinearMap
  let U : Submodule K B := (verticalSpace (K := K) (V := S)).map e.toLinearMap
  let Q := U.map B.subtype
  have hT : (ω.restrict B).orthogonal T = T := by
    change (ω.restrict B).orthogonal (horizontalSpace.map e.toLinearMap) = horizontalSpace.map e.toLinearMap
    rw [orthogonal_map_isometry_between (canonicalSymplectic (K := K) (V := S))
      (ω.restrict B) e (fun x y => heform x y),horizontalSpace_selforthogonal]
  have hU : (ω.restrict B).orthogonal U = U := by
    change (ω.restrict B).orthogonal (verticalSpace.map e.toLinearMap) = verticalSpace.map e.toLinearMap
    rw [orthogonal_map_isometry_between (canonicalSymplectic (K := K) (V := S))
      (ω.restrict B) e (fun x y => heform x y)]
    exact congrArg (fun U : Submodule K (S × Module.Dual K S) => U.map e.toLinearMap)
      (verticalLagrangian (K := K) (V := S)).property
  have hTS : T.map B.subtype = S := by
    ext x
    constructor
    · rintro ⟨b,⟨z,hz,rfl⟩,rfl⟩
      obtain ⟨s,f⟩ := z
      have hf : f = 0 := hz
      subst f
      change (e (s,0)).val ∈ S
      rw [heS]
      exact s.property
    · intro hx
      refine ⟨e (⟨x,hx⟩,0),⟨(⟨x,hx⟩,0),rfl,rfl⟩,?_⟩
      exact heS ⟨x,hx⟩
  have hQN : Q ≤ N := by
    rintro x ⟨b,⟨z,hz,rfl⟩,rfl⟩
    obtain ⟨s,f⟩ := z
    have hs : s = 0 := hz
    subst s
    exact heN f
  have hQB : Q ≤ B := by rintro x ⟨b,_,rfl⟩; exact b.property
  have hdim : finrank K Q = finrank K S := by
    change finrank K (U.map B.subtype) = finrank K S
    rw [← (Submodule.equivMapOfInjective B.subtype B.injective_subtype U).finrank_eq]
    change finrank K (verticalSpace.map e.toLinearMap) = finrank K S
    rw [e.finrank_map_eq]
    rw [← (verticalSpaceEquiv (K := K) (V := S)).finrank_eq,Subspace.dual_finrank_eq]
  have hBQ : B = S ⊔ Q := by
    apply le_antisymm
    · intro x hx
      obtain ⟨z,hz⟩ := e.surjective ⟨x,hx⟩
      have hsum : x = z.1.val + (e (0,z.2)).val := by
        have headd := e.map_add (z.1,0) (0,z.2)
        have headd' := congrArg Subtype.val headd
        simp only [Prod.mk_add_mk,add_zero,zero_add] at headd'
        rw [hz] at headd'
        change x = (e (z.1,0)).val + (e (0,z.2)).val at headd'
        rw [heS] at headd'
        exact headd'
      rw [hsum]
      exact Submodule.add_mem_sup z.1.property ⟨e (0,z.2),⟨(0,z.2),rfl,rfl⟩,rfl⟩
    · exact sup_le hSB hQB
  have hsplitL : L = S ⊔ (L ⊓ ω.orthogonal B) := by
    simpa only [hTS] using forced_orthogonal_splitting ω ha B L hB hL.ge T hT
      (by rw [hTS]; exact inf_le_left)
  have hsplitM : M = S ⊔ (M ⊓ ω.orthogonal B) := by
    simpa only [hTS] using forced_orthogonal_splitting ω ha B M hB hM.ge T hT
      (by rw [hTS]; exact inf_le_right)
  have hsplitN : N = Q ⊔ (N ⊓ ω.orthogonal B) :=
    forced_orthogonal_splitting ω ha B N hB hN.ge U hU hQN
  have hsurvive (A : Submodule K E) (hA : ω.orthogonal A = A) (hSA : S ≤ A) :
      A ⊓ N ≤ ω.orthogonal B := by
    intro x hx b hb
    rw [hBQ] at hb
    obtain ⟨s,hs,q,hq,rfl⟩ := Submodule.mem_sup.mp hb
    simp only [map_add,LinearMap.add_apply]
    rw [hA.ge hx.1 s (hSA hs),hN.ge hx.2 q (hQN hq),add_zero]
  have hdisj : (L ⊓ ω.orthogonal B) ⊓ (M ⊓ ω.orthogonal B) = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hb : x ∈ B := hSB ⟨hx.1.1,hx.2.1⟩
    exact (ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hB).disjoint.le_bot
      ⟨hb,hx.1.2⟩
  refine ⟨B,Q,hB,hSB,hQB,hQN,hdim,hBQ,hsplitL,hsplitM,hsplitN,
    hsurvive L hL inf_le_left,hsurvive M hM inf_le_right,hdisj,?_,e,heS,rfl,heform⟩
  intro A hA
  rcases (show A = L ∨ A = M ∨ A = N from hA) with hA | hA | hA
  · subst A
    exact split_residual_lagrangian ω ha B L hB hL T hT (by rw [hTS]; exact inf_le_left)
  · subst A
    exact split_residual_lagrangian ω ha B M hB hM T hT (by rw [hTS]; exact inf_le_right)
  · subst A
    exact split_residual_lagrangian ω ha B N hB hN U hU hQN

end TripleOneBlock
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section OrthogonalReduction
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)

/-- If an isotropic space is Lagrangian in a nondegenerate block, its
symplectic quotient is the orthogonal complement of that block, with the
literal quotient map as isometry. -/
theorem exists_complement_reduction_equiv (ha : ω.IsAlt)
    (S B : Submodule K E) (hB : (ω.restrict B).Nondegenerate)
    (hSB : S ≤ B) (hBS : B ⊓ ω.orthogonal S = S) :
    ∃ e : ω.orthogonal B ≃ₗ[K] ReducedSpace ω S,
      (∀ x : ω.orthogonal B, e x = (reductionKernel ω S).mkQ
        ⟨x.val,by intro s hs; exact x.property s (hSB hs)⟩) ∧
      (∀ x y, symplecticReductionForm ω S ha (e x) (e y) = ω x.val y.val) ∧
      ∀ L : Submodule K E, L = (L ⊓ B) ⊔ (L ⊓ ω.orthogonal B) →
        (L.comap (ω.orthogonal B).subtype).map e.toLinearMap = reduceSubspace ω S L := by
  let U := ω.orthogonal B
  have hUS : U ≤ ω.orthogonal S := by
    intro x hx s hs
    exact hx s (hSB hs)
  let f : U →ₗ[K] ReducedSpace ω S :=
    (reductionKernel ω S).mkQ.comp (Submodule.inclusion hUS)
  have hf (x : U) : f x = (reductionKernel ω S).mkQ ⟨x.val,hUS x.property⟩ := rfl
  have hc := ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hB
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hxS : x.val ∈ S := (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hx
    apply Subtype.ext
    exact hc.disjoint.le_bot ⟨hSB hxS,x.property⟩
  have hsurj : Function.Surjective f := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H z =>
      have hz : z.val ∈ B ⊔ U := hc.sup_eq_top.symm ▸ Submodule.mem_top
      obtain ⟨b,hb,u,hu,hbu⟩ := Submodule.mem_sup.mp hz
      have hbS : b ∈ S := by
        apply hBS.le
        refine ⟨hb,?_⟩
        have hbval : b = z.val-u := by rw [←hbu]; abel
        rw [hbval]
        exact (ω.orthogonal S).sub_mem z.property (hUS hu)
      refine ⟨⟨u,hu⟩,?_⟩
      apply (Submodule.Quotient.eq (reductionKernel ω S)).mpr
      change u-z.val ∈ S
      have huval : u-z.val = -b := by rw [←hbu]; abel
      rw [huval]
      exact S.neg_mem hbS
  let e : U ≃ₗ[K] ReducedSpace ω S := LinearEquiv.ofBijective f ⟨hinj,hsurj⟩
  refine ⟨e,fun _ => rfl,fun _ _ => rfl,?_⟩
  intro L hL
  ext z
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨⟨u.val,hUS u.property⟩,hu,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    have hx' : x.val ∈ (L ⊓ B) ⊔ (L ⊓ U) := hL ▸ hx
    obtain ⟨b,hb,u,hu,hbu⟩ := Submodule.mem_sup.mp hx'
    have hbS : b ∈ S := by
      apply hBS.le
      refine ⟨hb.2,?_⟩
      have hbval : b = x.val-u := by rw [←hbu]; abel
      rw [hbval]
      exact (ω.orthogonal S).sub_mem x.property (hUS hu.2)
    refine ⟨⟨u,hu.2⟩,hu.1,?_⟩
    change (reductionKernel ω S).mkQ ⟨u,hUS hu.2⟩ = (reductionKernel ω S).mkQ x
    apply (Submodule.Quotient.eq (reductionKernel ω S)).mpr
    change u-x.val ∈ S
    have huval : u-x.val = -b := by rw [←hbu]; abel
    rw [huval]
    exact S.neg_mem hbS
end OrthogonalReduction
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section ReductionInStages
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (ha : ω.IsAlt)

/-- Symplectic reduction in two nested isotropic spaces agrees with direct
reduction. The equivalence also identifies the general (not merely containing)
reduction of every subspace. -/
theorem exists_reduction_in_stages (S T : Submodule K E)
    (hST : S ≤ T) (hT : T ≤ ω.orthogonal T) :
    ∃ e : ReducedSpace ω T ≃ₗ[K]
        ReducedSpace (symplecticReductionForm ω S ha) (reduceSubspace ω S T),
      (∀ x y, symplecticReductionForm (symplecticReductionForm ω S ha)
          (reduceSubspace ω S T) (symplecticReductionForm_alt ω S ha) (e x) (e y) =
        symplecticReductionForm ω T ha x y) ∧
      ∀ L : Submodule K E,
        (reduceSubspace ω T L).map e.toLinearMap =
          reduceSubspace (symplecticReductionForm ω S ha)
            (reduceSubspace ω S T) (reduceSubspace ω S L) := by
  let α := symplecticReductionForm ω S ha
  let R := reduceSubspace ω S T
  have hPS : ω.orthogonal T ≤ ω.orthogonal S := by
    intro x hx s hs
    exact hx s (hST hs)
  have hmem (x : ω.orthogonal S) :
      (reductionKernel ω S).mkQ x ∈ α.orthogonal R ↔ x.val ∈ ω.orthogonal T := by
    constructor
    · intro hx t ht
      have htS : t ∈ ω.orthogonal S := hPS (hT ht)
      exact hx ((reductionKernel ω S).mkQ ⟨t,htS⟩) ⟨⟨t,htS⟩,ht,rfl⟩
    · intro hx z hz
      obtain ⟨t,ht,rfl⟩ := hz
      exact hx t.val ht
  let p : ω.orthogonal T →ₗ[K] α.orthogonal R :=
    { toFun := fun x => ⟨(reductionKernel ω S).mkQ ⟨x.val,hPS x.property⟩,
          (hmem _).mpr x.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact (reductionKernel ω S).mkQ.map_add
          ⟨x.val,hPS x.property⟩ ⟨y.val,hPS y.property⟩
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact (reductionKernel ω S).mkQ.map_smul c ⟨x.val,hPS x.property⟩ }
  let g : ω.orthogonal T →ₗ[K] ReducedSpace α R := (reductionKernel α R).mkQ.comp p
  have hker : reductionKernel ω T ≤ g.ker := by
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero (reductionKernel α R)).mpr
    exact ⟨⟨x.val,hPS x.property⟩,hx,rfl⟩
  let f : ReducedSpace ω T →ₗ[K] ReducedSpace α R := (reductionKernel ω T).liftQ g hker
  have hf (x : ω.orthogonal T) : f ((reductionKernel ω T).mkQ x) =
      (reductionKernel α R).mkQ (p x) := rfl
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      have hxR : (p x).val ∈ R :=
        (Submodule.Quotient.mk_eq_zero (reductionKernel α R)).mp hz
      obtain ⟨t,ht,heq⟩ := hxR
      have hdiff : t.val-x.val ∈ S :=
        (Submodule.Quotient.eq (reductionKernel ω S)).mp heq
      apply (Submodule.Quotient.mk_eq_zero (reductionKernel ω T)).mpr
      have hxT := T.sub_mem ht (hST hdiff)
      change x.val ∈ T
      simpa only [Submodule.subtype_apply,sub_sub_cancel] using hxT
  have hsurj : Function.Surjective f := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨x,hx⟩ := (reductionKernel ω S).mkQ_surjective y.val
      have hxT : x.val ∈ ω.orthogonal T := (hmem x).mp (hx.symm ▸ y.property)
      refine ⟨(reductionKernel ω T).mkQ ⟨x.val,hxT⟩,?_⟩
      rw [hf]
      apply congrArg (reductionKernel α R).mkQ
      apply Subtype.ext
      exact hx
  let e : ReducedSpace ω T ≃ₗ[K] ReducedSpace α R := LinearEquiv.ofBijective f ⟨hinj,hsurj⟩
  refine ⟨e,?_,?_⟩
  · intro x y
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y => rfl
  · intro L
    ext z
    constructor
    · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
      refine ⟨p x,?_,rfl⟩
      exact ⟨⟨x.val,hPS x.property⟩,hx,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨x,hx,hxy⟩ := hy
      have hxT : x.val ∈ ω.orthogonal T := (hmem x).mp (hxy.symm ▸ y.property)
      refine ⟨(reductionKernel ω T).mkQ ⟨x.val,hxT⟩,
        ⟨⟨x.val,hxT⟩,hx,rfl⟩,?_⟩
      change (reductionKernel α R).mkQ (p ⟨x.val,hxT⟩) = (reductionKernel α R).mkQ y
      congr 1
      apply Subtype.ext
      exact hxy
end ReductionInStages
end SidorenkoCounterexample

namespace SidorenkoCounterexample
section ReductionIsometry
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

/-- Naturality of symplectic reduction under an isometry between arbitrary
ambient spaces. Both forms and every reduced subspace are preserved. -/
theorem exists_reduction_isometry_between
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt) (e : E ≃ₗ[K] F)
    (he : ∀ x y, η (e x) (e y) = ω x y)
    (S : Submodule K E) (T : Submodule K F) (hST : S.map e.toLinearMap = T) :
    ∃ f : ReducedSpace ω S ≃ₗ[K] ReducedSpace η T,
      (∀ x y, symplecticReductionForm η T hb (f x) (f y) =
        symplecticReductionForm ω S ha x y) ∧
      ∀ L : Submodule K E,
        (reduceSubspace ω S L).map f.toLinearMap = reduceSubspace η T (L.map e.toLinearMap) := by
  have hP : (ω.orthogonal S).map e.toLinearMap = η.orthogonal T := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩ t ht
      rw [←hST] at ht
      obtain ⟨s,hs,rfl⟩ := ht
      change η (e s) (e x) = 0
      rw [he]
      exact hx s hs
    · intro hy
      refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
      intro s hs
      rw [←he,e.apply_symm_apply]
      exact hy (e s) (hST.le ⟨s,hs,rfl⟩)
  let p : ω.orthogonal S ≃ₗ[K] η.orthogonal T := e.ofSubmodules _ _ hP
  have hp (x : ω.orthogonal S) : (p x).val = e x.val := rfl
  have hker : (reductionKernel ω S).map p.toLinearMap = reductionKernel η T := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hST.le ⟨x.val,hx,rfl⟩
    · intro hy
      obtain ⟨x,rfl⟩ := p.surjective y
      have hex : e x.val ∈ T := hy
      rw [←hST] at hex
      obtain ⟨s,hs,hse⟩ := hex
      have hsx : s = x.val := e.injective hse
      refine ⟨x,?_,rfl⟩
      change x.val ∈ S
      exact hsx ▸ hs
  let f := Submodule.Quotient.equiv (reductionKernel ω S) (reductionKernel η T) p hker
  have hf (x : ω.orthogonal S) : f ((reductionKernel ω S).mkQ x) =
      (reductionKernel η T).mkQ (p x) := rfl
  refine ⟨f,?_,?_⟩
  · intro x y
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y => exact he x.val y.val
  · intro L
    ext z
    constructor
    · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
      refine ⟨p x,?_,rfl⟩
      exact ⟨x.val,hx,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨x,rfl⟩ := p.surjective y
      obtain ⟨l,hl,hlx⟩ := hy
      have hlx' : l = x.val := e.injective hlx
      refine ⟨(reductionKernel ω S).mkQ x,⟨x,?_,rfl⟩,rfl⟩
      change x.val ∈ L
      exact hlx' ▸ hl
end ReductionIsometry
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section OrthogonalIsometries
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]

/-- Assemble isometries on a nondegenerate block and its orthogonal complement. -/
theorem exists_orthogonal_isometry_between
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt)
    (B : Submodule K E) (C : Submodule K F)
    (hB : (ω.restrict B).Nondegenerate) (hC : (η.restrict C).Nondegenerate)
    (f : B ≃ₗ[K] C) (g : ω.orthogonal B ≃ₗ[K] η.orthogonal C)
    (hf : ∀ x y, η (f x).val (f y).val = ω x.val y.val)
    (hg : ∀ x y, η (g x).val (g y).val = ω x.val y.val) :
    ∃ e : E ≃ₗ[K] F, (∀ x y, η (e x) (e y) = ω x y) ∧
      (∀ x : B, e x.val = (f x).val) ∧
      (∀ x : ω.orthogonal B, e x.val = (g x).val) := by
  let c := B.prodEquivOfIsCompl (ω.orthogonal B)
    (ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hB)
  let d := C.prodEquivOfIsCompl (η.orthogonal C)
    (η.isCompl_orthogonal_of_restrict_nondegenerate hb.isRefl hC)
  let e := c.symm.trans ((f.prodCongr g).trans d)
  have he (x : B × ω.orthogonal B) : e (c x) = d (f x.1,g x.2) := by simp [e]
  refine ⟨e,?_,?_,?_⟩
  · intro x y
    obtain ⟨x,rfl⟩ := c.surjective x
    obtain ⟨y,rfl⟩ := c.surjective y
    rw [he,he]
    change η ((f x.1).val + (g x.2).val) ((f y.1).val + (g y.2).val) =
      ω (x.1.val + x.2.val) (y.1.val + y.2.val)
    rw [form_orthogonal_sum η hb C (f x.1,g x.2) (f y.1,g y.2),
      form_orthogonal_sum ω ha B x y,hf,hg]
  · intro x
    have h := he (x,0)
    simpa [c,d] using h
  · intro x
    have h := he (0,x)
    simpa [c,d] using h

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- Mapping the two honest summands maps their sum, including repeated or zero
summands. This is used only for actual orthogonal splittings of Lagrangians. -/
theorem map_orthogonal_split (e : E ≃ₗ[K] F)
    (B : Submodule K E) (C : Submodule K F)
    (f : B ≃ₗ[K] C) (heB : ∀ x : B, e x.val = (f x).val)
    (U : Submodule K E) (W : Submodule K F)
    (g : U ≃ₗ[K] W) (heU : ∀ x : U, e x.val = (g x).val)
    (L : Submodule K E) (M : Submodule K F)
    (hL : L = (L ⊓ B) ⊔ (L ⊓ U)) (hM : M = (M ⊓ C) ⊔ (M ⊓ W))
    (hf : (L.comap B.subtype).map f.toLinearMap = M.comap C.subtype)
    (hg : (L.comap U.subtype).map g.toLinearMap = M.comap W.subtype) :
    L.map e.toLinearMap = M := by
  have hblock : (L ⊓ B).map e.toLinearMap = M ⊓ C := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hy : f ⟨x,hx.2⟩ ∈ M.comap C.subtype := hf.le ⟨⟨x,hx.2⟩,hx.1,rfl⟩
      change e x ∈ M ⊓ C
      rw [heB ⟨x,hx.2⟩]
      exact ⟨hy,(f ⟨x,hx.2⟩).property⟩
    · intro hy
      have hy' : (⟨y,hy.2⟩ : C) ∈ (L.comap B.subtype).map f.toLinearMap := hf.ge hy.1
      obtain ⟨x,hx,hxy⟩ := hy'
      refine ⟨x.val,⟨hx,x.property⟩,?_⟩
      change e x.val = y
      exact (heB x).trans (congrArg Subtype.val hxy)
  have hres : (L ⊓ U).map e.toLinearMap = M ⊓ W := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hy : g ⟨x,hx.2⟩ ∈ M.comap W.subtype := hg.le ⟨⟨x,hx.2⟩,hx.1,rfl⟩
      change e x ∈ M ⊓ W
      rw [heU ⟨x,hx.2⟩]
      exact ⟨hy,(g ⟨x,hx.2⟩).property⟩
    · intro hy
      have hy' : (⟨y,hy.2⟩ : W) ∈ (L.comap U.subtype).map g.toLinearMap := hg.ge hy.1
      obtain ⟨x,hx,hxy⟩ := hy'
      refine ⟨x.val,⟨hx,x.property⟩,?_⟩
      change e x.val = y
      exact (heU x).trans (congrArg Subtype.val hxy)
  calc
    L.map e.toLinearMap = ((L ⊓ B) ⊔ (L ⊓ U)).map e.toLinearMap := congrArg _ hL
    _ = (M ⊓ C) ⊔ (M ⊓ W) := by rw [Submodule.map_sup,hblock,hres]
    _ = M := hM.symm
end OrthogonalIsometries
end SidorenkoCounterexample

namespace SidorenkoCounterexample
section SplitHelpers
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem split_inter_block (L A B U : Submodule K E)
    (hBU : Disjoint B U) (hAB : A ≤ B) (hL : L = A ⊔ (L ⊓ U)) :
    L ⊓ B = A := by
  apply le_antisymm
  · intro x hx
    have hxL : x ∈ A ⊔ (L ⊓ U) := hL ▸ hx.1
    obtain ⟨a,ha,u,hu,hau⟩ := Submodule.mem_sup.mp hxL
    have huB : u ∈ B := by
      have huval : u = x-a := by rw [←hau]; abel
      rw [huval]
      exact B.sub_mem hx.2 (hAB ha)
    have hu0 : u = 0 := hBU.le_bot ⟨huB,hu.2⟩
    rw [hu0,add_zero] at hau
    exact hau ▸ ha
  · exact le_inf (hL.symm ▸ le_sup_left) hAB

theorem split_over_block (L A B U : Submodule K E)
    (hAB : A ≤ B) (hL : L = A ⊔ (L ⊓ U)) :
    L = (L ⊓ B) ⊔ (L ⊓ U) := by
  apply le_antisymm
  · calc
      L = A ⊔ (L ⊓ U) := hL
      _ ≤ (L ⊓ B) ⊔ (L ⊓ U) :=
        sup_le_sup (le_inf (hL.symm ▸ le_sup_left) hAB) le_rfl
  · exact sup_le inf_le_left inf_le_left
end SplitHelpers
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section TripleBlockData
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)

/-- A common-zero triple has honest pair-block coordinates and the same
residual triple as direct symplectic reduction by that pair intersection. -/
theorem triple_block_reduction_data (ha : ω.IsAlt)
    (L M N : Submodule K E) (hL : ω.orthogonal L = L)
    (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hzero : (L ⊓ M) ⊓ N = ⊥) :
    ∃ B : Submodule K E, (ω.restrict B).Nondegenerate ∧
      ∃ e : (↥(L ⊓ M) × Module.Dual K ↥(L ⊓ M)) ≃ₗ[K] B,
      ∃ f : ω.orthogonal B ≃ₗ[K] ReducedSpace ω (L ⊓ M),
        (∀ x y, ω (e x).val (e y).val = canonicalSymplectic x y) ∧
        (∀ x y, symplecticReductionForm ω (L ⊓ M) ha (f x) (f y) = ω x.val y.val) ∧
        L.comap B.subtype = horizontalSpace.map e.toLinearMap ∧
        M.comap B.subtype = horizontalSpace.map e.toLinearMap ∧
        N.comap B.subtype = verticalSpace.map e.toLinearMap ∧
        ∀ A ∈ ({L,M,N} : Set (Submodule K E)),
          A = (A ⊓ B) ⊔ (A ⊓ ω.orthogonal B) ∧
          (A.comap (ω.orthogonal B).subtype).map f.toLinearMap =
            reduceSubspace ω (L ⊓ M) A := by
  obtain ⟨B,Q,hB,hSB,hQB,_hQN,_hdim,_hBQ,hSL,hSM,hSN,_hsL,_hsM,_hdisj,_hres,
    e,heS,heQ,heform⟩ := triple_pair_block ω ha L M N hL hM hN hzero
  let S := L ⊓ M
  let T : Submodule K B := horizontalSpace.map e.toLinearMap
  have hTS : T.map B.subtype = S := by
    ext x
    constructor
    · rintro ⟨b,⟨z,hz,rfl⟩,rfl⟩
      obtain ⟨s,g⟩ := z
      have hg : g = 0 := hz
      subst g
      change (e (s,0)).val ∈ S
      rw [heS]
      exact s.property
    · intro hx
      refine ⟨e (⟨x,hx⟩,0),⟨(⟨x,hx⟩,0),rfl,rfl⟩,?_⟩
      exact heS ⟨x,hx⟩
  have hT : (ω.restrict B).orthogonal T = T := by
    rw [orthogonal_map_isometry_between (canonicalSymplectic (K := K) (V := S))
      (ω.restrict B) e (fun x y => heform x y),horizontalSpace_selforthogonal]
  have hBS : B ⊓ ω.orthogonal S = S := by
    apply le_antisymm
    · intro x hx
      have hxT : (⟨x,hx.1⟩ : B) ∈ T := by
        apply hT.le
        intro b hb
        exact hx.2 b.val (hTS.le ⟨b,hb,rfl⟩)
      exact hTS.le ⟨⟨x,hx.1⟩,hxT,rfl⟩
    · refine le_inf hSB ?_
      intro s hs t ht
      exact hL.ge hs.1 t ht.1
  have hLU := split_over_block L S B (ω.orthogonal B) hSB hSL
  have hMU := split_over_block M S B (ω.orthogonal B) hSB hSM
  have hNU := split_over_block N Q B (ω.orthogonal B) hQB hSN
  obtain ⟨f,_hf,hfform,hfred⟩ := exists_complement_reduction_equiv ω ha S B hB hSB hBS
  have hcompl := ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hB
  have hLB := split_inter_block L S B (ω.orthogonal B) hcompl.disjoint hSB hSL
  have hMB := split_inter_block M S B (ω.orthogonal B) hcompl.disjoint hSB hSM
  have hNB := split_inter_block N Q B (ω.orthogonal B) hcompl.disjoint hQB hSN
  refine ⟨B,hB,e,f,heform,hfform,?_,?_,?_,?_⟩
  · apply Submodule.map_injective_of_injective B.injective_subtype
    rw [Submodule.map_comap_subtype,inf_comm,hLB]
    exact hTS.symm
  · apply Submodule.map_injective_of_injective B.injective_subtype
    rw [Submodule.map_comap_subtype,inf_comm,hMB]
    exact hTS.symm
  · apply Submodule.map_injective_of_injective B.injective_subtype
    rw [Submodule.map_comap_subtype,inf_comm,hNB]
    exact heQ.symm
  · intro A hA
    rcases (show A = L ∨ A = M ∨ A = N from hA) with heq | heq | heq
    · subst A; exact ⟨hLU,hfred L hLU⟩
    · subst A; exact ⟨hMU,hfred M hMU⟩
    · subst A; exact ⟨hNU,hfred N hNU⟩
end TripleBlockData
end SidorenkoCounterexample

namespace SidorenkoCounterexample
section MapTransport
variable {K E F E' F' : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [AddCommGroup E'] [Module K E'] [AddCommGroup F'] [Module K F']

theorem map_transport_equiv (u : E ≃ₗ[K] E') (v : F ≃ₗ[K] F')
    (r : E' ≃ₗ[K] F') (A : Submodule K E) (B : Submodule K F)
    (h : (A.map u.toLinearMap).map r.toLinearMap = B.map v.toLinearMap) :
    A.map (u.trans (r.trans v.symm)).toLinearMap = B := by
  apply Submodule.map_injective_of_injective v.injective
  calc
    (A.map (u.trans (r.trans v.symm)).toLinearMap).map v.toLinearMap =
        (A.map u.toLinearMap).map r.toLinearMap := by
      simp only [← Submodule.map_comp]
      congr 1
      ext x
      simp
    _ = B.map v.toLinearMap := h

theorem map_conjugate_equiv (u : E ≃ₗ[K] E') (v : F ≃ₗ[K] F')
    (r : E ≃ₗ[K] F) (A : Submodule K E) :
    (A.map u.toLinearMap).map (u.symm.trans (r.trans v)).toLinearMap =
      (A.map r.toLinearMap).map v.toLinearMap := by
  simp only [← Submodule.map_comp]
  congr 1
  ext x
  simp
end MapTransport

open Module
section TripleOneBlockLift
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]

/-- The extension across one pair block. No extension invariant remains:
any isometry of the three reduced Lagrangians lifts to the triple. -/
theorem triple_one_block_lift
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M')
    (hN' : η.orthogonal N' = N')
    (hzero : (L ⊓ M) ⊓ N = ⊥) (hzero' : (L' ⊓ M') ⊓ N' = ⊥)
    (hdim : finrank K ↥(L ⊓ M) = finrank K ↥(L' ⊓ M'))
    (r : ReducedSpace ω (L ⊓ M) ≃ₗ[K] ReducedSpace η (L' ⊓ M'))
    (hr : ∀ x y, symplecticReductionForm η (L' ⊓ M') hb (r x) (r y) =
      symplecticReductionForm ω (L ⊓ M) ha x y)
    (hrL : (reduceSubspace ω (L ⊓ M) L).map r.toLinearMap =
      reduceSubspace η (L' ⊓ M') L')
    (hrM : (reduceSubspace ω (L ⊓ M) M).map r.toLinearMap =
      reduceSubspace η (L' ⊓ M') M')
    (hrN : (reduceSubspace ω (L ⊓ M) N).map r.toLinearMap =
      reduceSubspace η (L' ⊓ M') N') :
    ∃ e : E ≃ₗ[K] F, (∀ x y, η (e x) (e y) = ω x y) ∧
      L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' ∧
      N.map e.toLinearMap = N' := by
  obtain ⟨B,hB,b,f,hbform,hfform,hLb,hMb,hNb,hsplit⟩ :=
    triple_block_reduction_data ω ha L M N hL hM hN hzero
  obtain ⟨C,hC,c,g,hcform,hgform,hLc,hMc,hNc,hsplit'⟩ :=
    triple_block_reduction_data η hb L' M' N' hL' hM' hN' hzero'
  let t : ↥(L ⊓ M) ≃ₗ[K] ↥(L' ⊓ M') := LinearEquiv.ofFinrankEq _ _ hdim
  let w := t.prodCongr t.symm.dualMap
  have hw (x y : ↥(L ⊓ M) × Module.Dual K ↥(L ⊓ M)) :
      canonicalSymplectic (w x) (w y) = canonicalSymplectic x y := by
    simp [w,canonicalSymplectic_apply]
  have hwH : horizontalSpace.map w.toLinearMap = horizontalSpace := by
    apply subspace_map_eq_of_mem_iff
    intro x
    change t.symm.dualMap x.2 = 0 ↔ x.2 = 0
    exact t.symm.dualMap.map_eq_zero_iff
  have hwV : verticalSpace.map w.toLinearMap = verticalSpace := by
    apply subspace_map_eq_of_mem_iff
    intro x
    change t x.1 = 0 ↔ x.1 = 0
    exact t.map_eq_zero_iff
  let u := b.symm.trans (w.trans c)
  let v := f.trans (r.trans g.symm)
  have hu (x y : B) : η (u x).val (u y).val = ω x.val y.val := by
    change η (c (w (b.symm x))).val (c (w (b.symm y))).val = _
    rw [hcform,hw,←hbform,b.apply_symm_apply,b.apply_symm_apply]
  have hv (x y : ω.orthogonal B) : η (v x).val (v y).val = ω x.val y.val := by
    rw [← hgform]
    change symplecticReductionForm η (L' ⊓ M') hb
      (g (g.symm (r (f x)))) (g (g.symm (r (f y)))) = _
    rw [g.apply_symm_apply,g.apply_symm_apply,hr,hfform]
  obtain ⟨e,he,heB,heU⟩ := exists_orthogonal_isometry_between ω η ha hb B C hB hC u v hu hv
  have hblockH : (horizontalSpace.map b.toLinearMap).map u.toLinearMap =
      horizontalSpace.map c.toLinearMap := by
    rw [map_conjugate_equiv b c w,hwH]
  have hblockV : (verticalSpace.map b.toLinearMap).map u.toLinearMap =
      verticalSpace.map c.toLinearMap := by
    rw [map_conjugate_equiv b c w,hwV]
  have hmap (A : Submodule K E) (A' : Submodule K F)
      (hA : A ∈ ({L,M,N} : Set (Submodule K E)))
      (hA' : A' ∈ ({L',M',N'} : Set (Submodule K F)))
      (hblock : (A.comap B.subtype).map u.toLinearMap = A'.comap C.subtype)
      (hres : (reduceSubspace ω (L ⊓ M) A).map r.toLinearMap =
        reduceSubspace η (L' ⊓ M') A') : A.map e.toLinearMap = A' := by
    obtain ⟨hAs,hAr⟩ := hsplit A hA
    obtain ⟨hAs',hAr'⟩ := hsplit' A' hA'
    apply map_orthogonal_split e B C u heB (ω.orthogonal B) (η.orthogonal C)
      v heU A A' hAs hAs' hblock
    apply map_transport_equiv f g r
    rw [hAr,hAr',hres]
  refine ⟨e,he,?_,?_,?_⟩
  · exact hmap L L' (by simp) (by simp) (by rw [hLb,hLc]; exact hblockH) hrL
  · exact hmap M M' (by simp) (by simp) (by rw [hMb,hMc]; exact hblockH) hrM
  · exact hmap N N' (by simp) (by simp) (by rw [hNb,hNc]; exact hblockV) hrN
end TripleOneBlockLift
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section ReductionIntersections
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)

@[simp] theorem reduceSubspace_self : reduceSubspace ω S S = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  rintro x ⟨y,hy,rfl⟩
  exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr hy

/-- Intersections commute with quotienting when the first subspace contains
its kernel. This includes the two pair intersections which survive a split. -/
theorem reduceSubspace_inf (L N : Submodule K E) (hSL : S ≤ L) :
    reduceSubspace ω S (L ⊓ N) =
      reduceSubspace ω S L ⊓ reduceSubspace ω S N := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact ⟨⟨y,hy.1,rfl⟩,⟨y,hy.2,rfl⟩⟩
  · rintro x ⟨⟨l,hl,hlx⟩,⟨n,hn,hnx⟩⟩
    have heq : (reductionKernel ω S).mkQ (l-n) = 0 := by
      rw [map_sub,hlx,hnx,sub_self]
    have hln : l.val-n.val ∈ S :=
      (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp heq
    have hnL : n.val ∈ L := by
      have h := L.sub_mem hl (hSL hln)
      simpa using h
    exact ⟨n,⟨hnL,hn⟩,hnx⟩

/-- Reduction preserves a subspace disjoint from the quotient kernel. -/
theorem reduceSubspace_finrank_of_disjoint [FiniteDimensional K E]
    (A : Submodule K E) (hAP : A ≤ ω.orthogonal S) (hAS : Disjoint A S) :
    finrank K (reduceSubspace ω S A) = finrank K A := by
  let f : A →ₗ[K] ReducedSpace ω S :=
    (reductionKernel ω S).mkQ.comp ((Submodule.inclusion hAP))
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply Subtype.ext
    have hxS : x.val ∈ S :=
      (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hx
    exact hAS.le_bot ⟨x.property,hxS⟩
  have hfr : LinearMap.range f = reduceSubspace ω S A := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x.val,hAP x.property⟩,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,rfl⟩
  rw [←hfr]
  exact (LinearEquiv.ofInjective f hf).finrank_eq.symm

theorem reduceSubspace_sup (A B : Submodule K E)
    (hA : A ≤ ω.orthogonal S) (hB : B ≤ ω.orthogonal S) :
    reduceSubspace ω S (A ⊔ B) = reduceSubspace ω S A ⊔ reduceSubspace ω S B := by
  have hcomap : (A ⊔ B).comap (ω.orthogonal S).subtype =
      A.comap (ω.orthogonal S).subtype ⊔ B.comap (ω.orthogonal S).subtype := by
    ext x
    constructor
    · intro hx
      obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hx
      exact Submodule.mem_sup.mpr
        ⟨⟨a,hA ha⟩,ha,⟨b,hB hb⟩,hb,Subtype.ext hab⟩
    · intro hx
      obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
      exact Submodule.mem_sup.mpr ⟨a.val,ha,b.val,hb,rfl⟩
  unfold reduceSubspace
  rw [hcomap,Submodule.map_sup]
end ReductionIntersections

section PairSum
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)

def triplePairSum (L M N : Submodule K E) : Submodule K E :=
  (L ⊓ M) ⊔ (L ⊓ N) ⊔ (M ⊓ N)

theorem triplePairSum_isotropic (L M N : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hN : ω.orthogonal N = N) :
    triplePairSum L M N ≤ ω.orthogonal (triplePairSum L M N) := by
  rw [triplePairSum,orthogonal_sup_eq,orthogonal_sup_eq]
  refine sup_le (sup_le (le_inf (le_inf ?_ ?_) ?_) (le_inf (le_inf ?_ ?_) ?_))
    (le_inf (le_inf ?_ ?_) ?_)
  all_goals intro x hx y hy
  · exact hL.ge hx.1 y hy.1
  · exact hL.ge hx.1 y hy.1
  · exact hM.ge hx.2 y hy.1
  · exact hL.ge hx.1 y hy.1
  · exact hL.ge hx.1 y hy.1
  · exact hN.ge hx.2 y hy.2
  · exact hM.ge hx.1 y hy.2
  · exact hN.ge hx.2 y hy.2
  · exact hM.ge hx.1 y hy.1

theorem triple_pair_reduction_intersections [FiniteDimensional K E]
    (L M N : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hzero : (L ⊓ M) ⊓ N = ⊥) :
    let S := L ⊓ M
    let P := reduceSubspace ω S L
    let Q := reduceSubspace ω S M
    let R := reduceSubspace ω S N
    P ⊓ Q = ⊥ ∧
      P ⊓ R = reduceSubspace ω S (L ⊓ N) ∧
      Q ⊓ R = reduceSubspace ω S (M ⊓ N) ∧
      finrank K ↥(P ⊓ R) = finrank K ↥(L ⊓ N) ∧
      finrank K ↥(Q ⊓ R) = finrank K ↥(M ⊓ N) ∧
      triplePairSum P Q R = reduceSubspace ω S (triplePairSum L M N) := by
  dsimp only
  have hLM := reduceSubspace_inf ω (L ⊓ M) L M inf_le_left
  have hLN := reduceSubspace_inf ω (L ⊓ M) L N inf_le_left
  have hMN := reduceSubspace_inf ω (L ⊓ M) M N inf_le_right
  have hLP : L ≤ ω.orthogonal (L ⊓ M) := lagrangian_le_orthogonal ω _ L hL inf_le_left
  have hMP : M ≤ ω.orthogonal (L ⊓ M) := lagrangian_le_orthogonal ω _ M hM inf_le_right
  have hLNdis : Disjoint (L ⊓ N) (L ⊓ M) := by
    apply disjoint_iff.mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    exact hzero.le ⟨hx.2,hx.1.2⟩
  have hMNdis : Disjoint (M ⊓ N) (L ⊓ M) := by
    apply disjoint_iff.mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    exact hzero.le ⟨hx.2,hx.1.2⟩
  rw [←hLM,reduceSubspace_self,←hLN,←hMN]
  refine ⟨rfl,rfl,rfl,?_,?_,?_⟩
  · exact reduceSubspace_finrank_of_disjoint ω _ _ (inf_le_left.trans hLP) hLNdis
  · exact reduceSubspace_finrank_of_disjoint ω _ _ (inf_le_left.trans hMP) hMNdis
  · rw [triplePairSum,triplePairSum,
      reduceSubspace_sup ω _ _ _ (sup_le (inf_le_left.trans hLP)
        (inf_le_left.trans hLP)) (inf_le_left.trans hMP),
      reduceSubspace_sup ω _ _ _ (inf_le_left.trans hLP) (inf_le_left.trans hLP),
      reduceSubspace_self,←hLM,←hLN,←hMN,reduceSubspace_self]
end PairSum
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section ClassificationPredicates
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

def TripleIsometry (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (L M N : Submodule K E) (L' M' N' : Submodule K F) : Prop :=
  ∃ e : E ≃ₗ[K] F, (∀ x y, η (e x) (e y) = ω x y) ∧
    L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' ∧ N.map e.toLinearMap = N'

def TripleResidualIsometry (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt)
    (L M N : Submodule K E) (L' M' N' : Submodule K F) : Prop :=
  TripleIsometry (symplecticReductionForm ω (triplePairSum L M N) ha)
    (symplecticReductionForm η (triplePairSum L' M' N') hb)
    (reduceSubspace ω (triplePairSum L M N) L)
    (reduceSubspace ω (triplePairSum L M N) M)
    (reduceSubspace ω (triplePairSum L M N) N)
    (reduceSubspace η (triplePairSum L' M' N') L')
    (reduceSubspace η (triplePairSum L' M' N') M')
    (reduceSubspace η (triplePairSum L' M' N') N')

theorem TripleResidualIsometry.swap_right
    {ω : LinearMap.BilinForm K E} {η : LinearMap.BilinForm K F}
    {ha : ω.IsAlt} {hb : η.IsAlt}
    {L M N : Submodule K E} {L' M' N' : Submodule K F}
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleResidualIsometry ω η ha hb L N M L' N' M' := by
  have hs : triplePairSum L N M = triplePairSum L M N := by unfold triplePairSum; ac_rfl
  have hs' : triplePairSum L' N' M' = triplePairSum L' M' N' := by unfold triplePairSum; ac_rfl
  unfold TripleResidualIsometry at *
  rw [hs,hs']
  obtain ⟨e,he,hL,hM,hN⟩ := h
  exact ⟨e,he,hL,hN,hM⟩

theorem TripleResidualIsometry.rotate
    {ω : LinearMap.BilinForm K E} {η : LinearMap.BilinForm K F}
    {ha : ω.IsAlt} {hb : η.IsAlt}
    {L M N : Submodule K E} {L' M' N' : Submodule K F}
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleResidualIsometry ω η ha hb M N L M' N' L' := by
  have hs : triplePairSum M N L = triplePairSum L M N := by unfold triplePairSum; ac_rfl
  have hs' : triplePairSum M' N' L' = triplePairSum L' M' N' := by unfold triplePairSum; ac_rfl
  unfold TripleResidualIsometry at *
  rw [hs,hs']
  obtain ⟨e,he,hL,hM,hN⟩ := h
  exact ⟨e,he,hM,hN,hL⟩
end ClassificationPredicates

section ResidualClassificationStep
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]

theorem triple_residual_isometry_reduce_pair
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
    (hzero : (L ⊓ M) ⊓ N = ⊥) (hzero' : (L' ⊓ M') ⊓ N' = ⊥)
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleResidualIsometry (symplecticReductionForm ω (L ⊓ M) ha)
      (symplecticReductionForm η (L' ⊓ M') hb)
      (symplecticReductionForm_alt ω (L ⊓ M) ha)
      (symplecticReductionForm_alt η (L' ⊓ M') hb)
      (reduceSubspace ω (L ⊓ M) L) (reduceSubspace ω (L ⊓ M) M)
      (reduceSubspace ω (L ⊓ M) N) (reduceSubspace η (L' ⊓ M') L')
      (reduceSubspace η (L' ⊓ M') M') (reduceSubspace η (L' ⊓ M') N') := by
  have hs := (triple_pair_reduction_intersections ω L M N hL hM hzero).2.2.2.2.2
  have hs' := (triple_pair_reduction_intersections η L' M' N' hL' hM' hzero').2.2.2.2.2

  unfold TripleResidualIsometry
  rw [hs,hs']
  obtain ⟨u,hu,huA⟩ := exists_reduction_in_stages ω ha (L ⊓ M) (triplePairSum L M N)
    (le_sup_left.trans le_sup_left) (triplePairSum_isotropic ω L M N hL hM hN)
  obtain ⟨v,hv,hvA⟩ := exists_reduction_in_stages η hb (L' ⊓ M') (triplePairSum L' M' N')
    (le_sup_left.trans le_sup_left) (triplePairSum_isotropic η L' M' N' hL' hM' hN')
  obtain ⟨r,hr,hrL,hrM,hrN⟩ := h
  let e := u.symm.trans (r.trans v)
  refine ⟨e,?_,?_,?_,?_⟩
  · intro x y
    change symplecticReductionForm (symplecticReductionForm η (L' ⊓ M') hb)
      (reduceSubspace η (L' ⊓ M') (triplePairSum L' M' N'))
      (symplecticReductionForm_alt η (L' ⊓ M') hb)
      (v (r (u.symm x))) (v (r (u.symm y))) = _
    rw [hv,hr,←hu,u.apply_symm_apply,u.apply_symm_apply]
  · rw [←huA L,←hvA L',map_conjugate_equiv,hrL]
  · rw [←huA M,←hvA M',map_conjugate_equiv,hrM]
  · rw [←huA N,←hvA N',map_conjugate_equiv,hrN]

/-- When the pair intersections vanish, the final quotient already carries
all of the ambient ordered triple. -/
theorem triple_isometry_of_zero_pairs
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
    (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥)
    (hLM' : L' ⊓ M' = ⊥) (hLN' : L' ⊓ N' = ⊥) (hMN' : M' ⊓ N' = ⊥)
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleIsometry ω η L M N L' M' N' := by
  have hs : triplePairSum L M N = L ⊓ M := by simp [triplePairSum,hLM,hLN,hMN]
  have hs' : triplePairSum L' M' N' = L' ⊓ M' := by simp [triplePairSum,hLM',hLN',hMN']
  unfold TripleResidualIsometry at h
  rw [hs,hs'] at h
  obtain ⟨r,hr,hrL,hrM,hrN⟩ := h
  exact triple_one_block_lift ω η ha hb L M N L' M' N' hL hM hN hL' hM' hN'
    (by rw [hLM,bot_inf_eq]) (by rw [hLM',bot_inf_eq]) (by rw [hLM,hLM']; simp)
    r hr hrL hrM hrN
end ResidualClassificationStep
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section FullClassification
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]

omit [FiniteDimensional K E] in
@[simp] theorem reduceSubspace_bot (ω : LinearMap.BilinForm K E) (S : Submodule K E) :
    reduceSubspace ω S ⊥ = ⊥ := by
  unfold reduceSubspace
  simp

theorem triple_isometry_of_two_zero_pairs
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt) (hω : ω.Nondegenerate) (hη : η.Nondegenerate)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
    (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥)
    (hLM' : L' ⊓ M' = ⊥) (hLN' : L' ⊓ N' = ⊥)
    (hdim : finrank K ↥(M ⊓ N) = finrank K ↥(M' ⊓ N'))
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleIsometry ω η L M N L' M' N' := by
  have hz : (M ⊓ N) ⊓ L = ⊥ := by
    calc
      _ = (L ⊓ M) ⊓ N := by ac_rfl
      _ = ⊥ := by rw [hLM,bot_inf_eq]
  have hz' : (M' ⊓ N') ⊓ L' = ⊥ := by
    calc
      _ = (L' ⊓ M') ⊓ N' := by ac_rfl
      _ = ⊥ := by rw [hLM',bot_inf_eq]
  have hS : M ⊓ N ≤ ω.orthogonal (M ⊓ N) := by
    intro x hx y hy
    exact hM.ge hx.1 y hy.1
  have hS' : M' ⊓ N' ≤ η.orthogonal (M' ⊓ N') := by
    intro x hx y hy
    exact hM'.ge hx.1 y hy.1
  let α := symplecticReductionForm ω (M ⊓ N) ha
  let β := symplecticReductionForm η (M' ⊓ N') hb
  have ha' := symplecticReductionForm_alt ω (M ⊓ N) ha
  have hb' := symplecticReductionForm_alt η (M' ⊓ N') hb
  have hred := general_lagrangian_reduction ω (M ⊓ N) ha hω hS
  have hred' := general_lagrangian_reduction η (M' ⊓ N') hb hη hS'
  obtain ⟨hpq,hpr,hqr,_hd1,_hd2,_hs⟩ :=
    triple_pair_reduction_intersections ω M N L hM hN hz
  obtain ⟨hpq',hpr',hqr',_hd1',_hd2',_hs'⟩ :=
    triple_pair_reduction_intersections η M' N' L' hM' hN' hz'
  have hh := triple_residual_isometry_reduce_pair ω η ha hb M N L M' N' L'
    hM hN hL hM' hN' hL' hz hz' h.rotate
  obtain ⟨r,hr,hrM,hrN,hrL⟩ := triple_isometry_of_zero_pairs α β ha' hb'
    _ _ _ _ _ _ (hred M hM) (hred N hN) (hred L hL)
    (hred' M' hM') (hred' N' hN') (hred' L' hL') hpq
    (by rw [hpr,inf_comm M L,hLM,reduceSubspace_bot])
    (by rw [hqr,inf_comm N L,hLN,reduceSubspace_bot]) hpq'
    (by rw [hpr',inf_comm M' L',hLM',reduceSubspace_bot])
    (by rw [hqr',inf_comm N' L',hLN',reduceSubspace_bot]) hh
  obtain ⟨e,he,heM,heN,heL⟩ := triple_one_block_lift ω η ha hb M N L M' N' L'
    hM hN hL hM' hN' hL' hz hz' hdim r hr hrM hrN hrL
  exact ⟨e,he,heL,heM,heN⟩

theorem triple_isometry_of_one_zero_pair
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt) (hω : ω.Nondegenerate) (hη : η.Nondegenerate)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
    (hLM : L ⊓ M = ⊥) (hLM' : L' ⊓ M' = ⊥)
    (hdimLN : finrank K ↥(L ⊓ N) = finrank K ↥(L' ⊓ N'))
    (hdimMN : finrank K ↥(M ⊓ N) = finrank K ↥(M' ⊓ N'))
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleIsometry ω η L M N L' M' N' := by
  have hz : (L ⊓ N) ⊓ M = ⊥ := by
    calc
      _ = (L ⊓ M) ⊓ N := by ac_rfl
      _ = ⊥ := by rw [hLM,bot_inf_eq]
  have hz' : (L' ⊓ N') ⊓ M' = ⊥ := by
    calc
      _ = (L' ⊓ M') ⊓ N' := by ac_rfl
      _ = ⊥ := by rw [hLM',bot_inf_eq]
  have hS : L ⊓ N ≤ ω.orthogonal (L ⊓ N) := by
    intro x hx y hy
    exact hL.ge hx.1 y hy.1
  have hS' : L' ⊓ N' ≤ η.orthogonal (L' ⊓ N') := by
    intro x hx y hy
    exact hL'.ge hx.1 y hy.1
  let α := symplecticReductionForm ω (L ⊓ N) ha
  let β := symplecticReductionForm η (L' ⊓ N') hb
  have ha' := symplecticReductionForm_alt ω (L ⊓ N) ha
  have hb' := symplecticReductionForm_alt η (L' ⊓ N') hb
  have hω' := symplecticReductionForm_nondegenerate ω (L ⊓ N) ha hω
  have hη' := symplecticReductionForm_nondegenerate η (L' ⊓ N') hb hη
  have hred := general_lagrangian_reduction ω (L ⊓ N) ha hω hS
  have hred' := general_lagrangian_reduction η (L' ⊓ N') hb hη hS'
  obtain ⟨hpq,hpr,_hqr,_hd1,hd2,_hs⟩ :=
    triple_pair_reduction_intersections ω L N M hL hN hz
  obtain ⟨hpq',hpr',_hqr',_hd1',hd2',_hs'⟩ :=
    triple_pair_reduction_intersections η L' N' M' hL' hN' hz'
  have hh := triple_residual_isometry_reduce_pair ω η ha hb L N M L' N' M'
    hL hN hM hL' hN' hM' hz hz' h.swap_right
  obtain ⟨r,hr,hrL,hrN,hrM⟩ := triple_isometry_of_two_zero_pairs α β ha' hb' hω' hη'
    _ _ _ _ _ _ (hred L hL) (hred N hN) (hred M hM)
    (hred' L' hL') (hred' N' hN') (hred' M' hM') hpq
    (by rw [hpr,hLM,reduceSubspace_bot]) hpq'
    (by rw [hpr',hLM',reduceSubspace_bot])
    (by rw [hd2,hd2',inf_comm N M,inf_comm N' M']; exact hdimMN) hh
  obtain ⟨e,he,heL,heN,heM⟩ := triple_one_block_lift ω η ha hb L N M L' N' M'
    hL hN hM hL' hN' hM' hz hz' hdimLN r hr hrL hrN hrM
  exact ⟨e,he,heL,heM,heN⟩




theorem triple_common_zero_classification
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt) (hω : ω.Nondegenerate) (hη : η.Nondegenerate)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
    (hzero : (L ⊓ M) ⊓ N = ⊥) (hzero' : (L' ⊓ M') ⊓ N' = ⊥)
    (hdimLM : finrank K ↥(L ⊓ M) = finrank K ↥(L' ⊓ M'))
    (hdimLN : finrank K ↥(L ⊓ N) = finrank K ↥(L' ⊓ N'))
    (hdimMN : finrank K ↥(M ⊓ N) = finrank K ↥(M' ⊓ N'))
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleIsometry ω η L M N L' M' N' := by
  have hS : L ⊓ M ≤ ω.orthogonal (L ⊓ M) := by
    intro x hx y hy
    exact hL.ge hx.1 y hy.1
  have hS' : L' ⊓ M' ≤ η.orthogonal (L' ⊓ M') := by
    intro x hx y hy
    exact hL'.ge hx.1 y hy.1
  let α := symplecticReductionForm ω (L ⊓ M) ha
  let β := symplecticReductionForm η (L' ⊓ M') hb
  have ha' := symplecticReductionForm_alt ω (L ⊓ M) ha
  have hb' := symplecticReductionForm_alt η (L' ⊓ M') hb
  have hω' := symplecticReductionForm_nondegenerate ω (L ⊓ M) ha hω
  have hη' := symplecticReductionForm_nondegenerate η (L' ⊓ M') hb hη
  have hred := general_lagrangian_reduction ω (L ⊓ M) ha hω hS
  have hred' := general_lagrangian_reduction η (L' ⊓ M') hb hη hS'
  obtain ⟨hpq,_hpr,_hqr,hd1,hd2,_hs⟩ :=
    triple_pair_reduction_intersections ω L M N hL hM hzero
  obtain ⟨hpq',_hpr',_hqr',hd1',hd2',_hs'⟩ :=
    triple_pair_reduction_intersections η L' M' N' hL' hM' hzero'
  have hh := triple_residual_isometry_reduce_pair ω η ha hb L M N L' M' N'
    hL hM hN hL' hM' hN' hzero hzero' h
  obtain ⟨r,hr,hrL,hrM,hrN⟩ := triple_isometry_of_one_zero_pair α β ha' hb' hω' hη'
    _ _ _ _ _ _ (hred L hL) (hred M hM) (hred N hN)
    (hred' L' hL') (hred' M' hM') (hred' N' hN') hpq hpq'
    (by rw [hd1,hd1']; exact hdimLN) (by rw [hd2,hd2']; exact hdimMN) hh
  exact triple_one_block_lift ω η ha hb L M N L' M' N' hL hM hN hL' hM' hN'
    hzero hzero' hdimLM r hr hrL hrM hrN
end FullClassification
end SidorenkoCounterexample

end OAI
