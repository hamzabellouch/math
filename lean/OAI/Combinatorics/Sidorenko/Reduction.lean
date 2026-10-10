import OAI.Combinatorics.Sidorenko.Nullity

namespace OAI

namespace SidorenkoCounterexample
open Module
section Reduction
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)

/-- The copy of an isotropic space inside its orthogonal complement. -/
def reductionKernel : Submodule K (ω.orthogonal S) := S.comap (ω.orthogonal S).subtype
abbrev ReducedSpace := (ω.orthogonal S) ⧸ reductionKernel ω S

private theorem restricted_alt (ha : ω.IsAlt) :
    (ω.compl₁₂ (ω.orthogonal S).subtype (ω.orthogonal S).subtype).IsAlt := by
  intro x
  exact ha x.val

private theorem reductionKernel_le_ker : reductionKernel ω S ≤
    (ω.compl₁₂ (ω.orthogonal S).subtype (ω.orthogonal S).subtype).ker := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  ext y
  exact y.property x.val hx



def symplecticReductionForm (ha : ω.IsAlt) : LinearMap.BilinForm K (ReducedSpace ω S) :=
  LinearMap.IsRefl.liftQ₂
    (ω.compl₁₂ (ω.orthogonal S).subtype (ω.orthogonal S).subtype)
    (reductionKernel ω S) (restricted_alt ω S ha).isRefl (reductionKernel_le_ker ω S)

@[simp] theorem reductionForm_mk (ha : ω.IsAlt) (x y : ω.orthogonal S) :
    symplecticReductionForm ω S ha
      ((reductionKernel ω S).mkQ x) ((reductionKernel ω S).mkQ y) = ω x.val y.val := rfl

theorem symplecticReductionForm_alt (ha : ω.IsAlt) :
    (symplecticReductionForm ω S ha).IsAlt := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x => exact ha x.val

theorem symplecticReductionForm_nondegenerate [FiniteDimensional K E]
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) :
    (symplecticReductionForm ω S ha).Nondegenerate := by
  have hl (x : ReducedSpace ω S)
      (hx : ∀ y, symplecticReductionForm ω S ha x y = 0) : x = 0 := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      apply (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr
      change x.val ∈ S
      apply (ω.orthogonal_orthogonal hω ha.isRefl S).le
      intro y hy
      exact ha.isRefl _ _ (hx ((reductionKernel ω S).mkQ ⟨y,hy⟩))
  refine ⟨hl, ?_⟩
  intro x hx
  apply hl
  intro y
  exact (symplecticReductionForm_alt ω S ha).isRefl _ _ (hx y)

theorem reducedSpace_finrank [FiniteDimensional K E]
    (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S) :
    finrank K (ReducedSpace ω S) + 2 * finrank K S = finrank K E := by
  have hker : finrank K (reductionKernel ω S) = finrank K S :=
    (Submodule.comapSubtypeEquivOfLe hS).finrank_eq
  have hq := Submodule.finrank_quotient_add_finrank (reductionKernel ω S)
  have hp := ω.finrank_orthogonal hω S
  have hle := Submodule.finrank_le S
  change finrank K (ReducedSpace ω S) + finrank K (reductionKernel ω S) =
    finrank K (ω.orthogonal S) at hq
  rw [hker] at hq
  omega


def liftReduction (T : Submodule K (ReducedSpace ω S)) : Submodule K E :=
  (T.comap (reductionKernel ω S).mkQ).map (ω.orthogonal S).subtype

@[simp] theorem mem_liftReduction (T : Submodule K (ReducedSpace ω S)) (x : E) :
    x ∈ liftReduction ω S T ↔ ∃ hx : x ∈ ω.orthogonal S,
      (reductionKernel ω S).mkQ ⟨x,hx⟩ ∈ T := by
  constructor
  · rintro ⟨y,hy,hx⟩
    cases hx
    exact ⟨y.property,hy⟩
  · rintro ⟨hx,ht⟩
    exact ⟨⟨x,hx⟩,ht,rfl⟩

theorem le_liftReduction (hS : S ≤ ω.orthogonal S)
    (T : Submodule K (ReducedSpace ω S)) : S ≤ liftReduction ω S T := by
  intro x hx
  apply (mem_liftReduction ω S T x).mpr
  refine ⟨hS hx, ?_⟩
  have hz : (reductionKernel ω S).mkQ ⟨x,hS hx⟩ = 0 :=
    (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr hx
  rw [hz]
  exact T.zero_mem

theorem liftReduction_le (T : Submodule K (ReducedSpace ω S)) :
    liftReduction ω S T ≤ ω.orthogonal S := by
  rintro x ⟨y,hy,rfl⟩
  exact y.property

/-- Orthogonality commutes exactly with lifting from an isotropic quotient. -/
theorem orthogonal_liftReduction (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
    (T : Submodule K (ReducedSpace ω S)) :
    ω.orthogonal (liftReduction ω S T) =
      liftReduction ω S ((symplecticReductionForm ω S ha).orthogonal T) := by
  ext x
  constructor
  · intro hx
    have hxP : x ∈ ω.orthogonal S := by
      intro s hs
      exact hx s (le_liftReduction ω S hS T hs)
    apply (mem_liftReduction ω S _ x).mpr
    refine ⟨hxP, ?_⟩
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      exact hx y.val ((mem_liftReduction ω S T y.val).mpr ⟨y.property,hy⟩)
  · intro hx
    obtain ⟨hxP,hxQ⟩ := (mem_liftReduction ω S _ x).mp hx
    intro y hy
    obtain ⟨hyP,hyQ⟩ := (mem_liftReduction ω S T y).mp hy
    exact hxQ ((reductionKernel ω S).mkQ ⟨y,hyP⟩) hyQ

/-- Thus every quotient Lagrangian lifts to a Lagrangian containing S. -/
theorem liftReduction_lagrangian (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
    (T : Submodule K (ReducedSpace ω S))
    (hT : (symplecticReductionForm ω S ha).orthogonal T = T) :
    ω.orthogonal (liftReduction ω S T) = liftReduction ω S T := by
  rw [orthogonal_liftReduction ω S ha hS, hT]

/-- The image of a subspace intersected with Sᗮ in the quotient. -/
def reduceSubspace (L : Submodule K E) : Submodule K (ReducedSpace ω S) :=
  (L.comap (ω.orthogonal S).subtype).map (reductionKernel ω S).mkQ

theorem reduce_lift (T : Submodule K (ReducedSpace ω S)) :
    reduceSubspace ω S (liftReduction ω S T) = T := by
  ext z
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    constructor
    · rintro ⟨y,hy,heq⟩
      obtain ⟨hyP,hyT⟩ := (mem_liftReduction ω S T y.val).mp hy
      change (reductionKernel ω S).mkQ y ∈ T at hyT
      exact heq ▸ hyT
    · intro hz
      refine ⟨z,?_,rfl⟩
      exact (mem_liftReduction ω S T z.val).mpr ⟨z.property,hz⟩

theorem liftReduction_injective : Function.Injective (liftReduction ω S) := by
  intro T U h
  have hh := congrArg (reduceSubspace ω S) h
  simpa only [reduce_lift] using hh

theorem lift_reduce (L : Submodule K E) (hSL : S ≤ L) (hLP : L ≤ ω.orthogonal S) :
    liftReduction ω S (reduceSubspace ω S L) = L := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxP,y,hy,hyeq⟩ := (mem_liftReduction ω S _ x).mp hx
    have hz : (reductionKernel ω S).mkQ (y - ⟨x,hxP⟩) = 0 := by
      rw [map_sub,hyeq,sub_self]
    have hzS : y.val-x ∈ S := (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hz
    have hxL := L.sub_mem hy (hSL hzS)
    simpa only [Submodule.subtype_apply, sub_sub_cancel] using hxL
  · intro hx
    apply (mem_liftReduction ω S _ x).mpr
    exact ⟨hLP hx,⟨⟨x,hLP hx⟩,hx,rfl⟩⟩

theorem lagrangian_le_orthogonal (L : Submodule K E)
    (hL : ω.orthogonal L = L) (hSL : S ≤ L) : L ≤ ω.orthogonal S := by
  intro x hx s hs
  have hxO : x ∈ ω.orthogonal L := hL.symm ▸ hx
  exact hxO s (hSL hs)

theorem reduce_lagrangian (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
    (L : Submodule K E) (hL : ω.orthogonal L = L) (hSL : S ≤ L) :
    (symplecticReductionForm ω S ha).orthogonal (reduceSubspace ω S L) =
      reduceSubspace ω S L := by
  apply liftReduction_injective ω S
  rw [← orthogonal_liftReduction ω S ha hS,
    lift_reduce ω S L hSL (lagrangian_le_orthogonal ω S L hL hSL),hL]



def containingLagrangianEquiv (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S) :
    {L : Submodule K E // ω.orthogonal L = L ∧ S ≤ L} ≃
      {T : Submodule K (ReducedSpace ω S) // (symplecticReductionForm ω S ha).orthogonal T = T} where
  toFun L := ⟨reduceSubspace ω S L.val,reduce_lagrangian ω S ha hS L.val L.property.1 L.property.2⟩
  invFun T := ⟨liftReduction ω S T.val,
    liftReduction_lagrangian ω S ha hS T.val T.property,le_liftReduction ω S hS T.val⟩
  left_inv L := Subtype.ext (lift_reduce ω S L.val L.property.2
    (lagrangian_le_orthogonal ω S L.val L.property.1 L.property.2))
  right_inv T := Subtype.ext (reduce_lift ω S T.val)

theorem orthogonal_sup_eq (U W : Submodule K E) :
    ω.orthogonal (U ⊔ W) = ω.orthogonal U ⊓ ω.orthogonal W := by
  ext x
  constructor
  · intro hx
    exact ⟨fun y hy => hx y ((le_sup_left : U ≤ U ⊔ W) hy), fun y hy => hx y ((le_sup_right : W ≤ U ⊔ W) hy)⟩
  · rintro ⟨hU,hW⟩ y hy
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hy
    simp only [map_add,LinearMap.add_apply,hU u hu,hW w hw,add_zero]

theorem orthogonal_inf_eq [FiniteDimensional K E] (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (U W : Submodule K E) :
    ω.orthogonal (U ⊓ W) = ω.orthogonal U ⊔ ω.orthogonal W := by
  have hinj : Function.Injective ω.orthogonal := by
    intro A B h
    have hh := congrArg ω.orthogonal h
    simpa only [ω.orthogonal_orthogonal hω ha.isRefl] using hh
  apply hinj
  rw [ω.orthogonal_orthogonal hω ha.isRefl, orthogonal_sup_eq,
    ω.orthogonal_orthogonal hω ha.isRefl,ω.orthogonal_orthogonal hω ha.isRefl]

/-- Every Lagrangian has a Lagrangian reduction, even when it does not contain
or avoid the isotropic space S. -/
theorem general_lagrangian_reduction [FiniteDimensional K E]
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
    (L : Submodule K E) (hL : ω.orthogonal L = L) :
    (symplecticReductionForm ω S ha).orthogonal (reduceSubspace ω S L) =
      reduceSubspace ω S L := by
  let U := (L ⊓ ω.orthogonal S) ⊔ S
  have hUL : ω.orthogonal U = U := by
    dsimp only [U]
    rw [orthogonal_sup_eq, orthogonal_inf_eq ω ha hω, hL,
      ω.orthogonal_orthogonal hω ha.isRefl]
    apply le_antisymm
    · rintro x ⟨hx,hxP⟩
      obtain ⟨l,hl,s,hs,rfl⟩ := Submodule.mem_sup.mp hx
      have hlP : l ∈ ω.orthogonal S := by
        have h := (ω.orthogonal S).sub_mem hxP (hS hs)
        simpa only [add_sub_cancel_right] using h
      exact Submodule.mem_sup.mpr ⟨l,⟨hl,hlP⟩,s,hs,rfl⟩
    · rintro x hx
      obtain ⟨l,hl,s,hs,rfl⟩ := Submodule.mem_sup.mp hx
      exact ⟨Submodule.mem_sup.mpr ⟨l,hl.1,s,hs,rfl⟩,
        (ω.orthogonal S).add_mem hl.2 (hS hs)⟩
  have hUred : reduceSubspace ω S U = reduceSubspace ω S L := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨l,hl,s,hs,hls⟩ := Submodule.mem_sup.mp hy
      refine ⟨⟨l,hl.2⟩,hl.1,?_⟩
      have hz : (reductionKernel ω S).mkQ ⟨s,hS hs⟩ = 0 :=
        (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr hs
      have heq : y = (⟨l,hl.2⟩ : ω.orthogonal S) + ⟨s,hS hs⟩ :=
        Subtype.ext hls.symm
      rw [heq,map_add,hz,add_zero]
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y,(le_sup_left : L ⊓ ω.orthogonal S ≤ U) ⟨hy,y.property⟩,rfl⟩
  rw [← hUred]
  exact reduce_lagrangian ω S ha hS U hUL le_sup_right

end Reduction
section IsotropicExtension
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)

omit [Finite E] in
theorem isotropic_sup_line (ha : ω.IsAlt) (L : Submodule K E)
    (hL : L ≤ ω.orthogonal L) (x : E) (hx : x ∈ ω.orthogonal L) :
    L ⊔ K ∙ x ≤ ω.orthogonal (L ⊔ K ∙ x) := by
  intro y hy z hz
  obtain ⟨l,hl,v,hv,rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨m,hm,w,hw,rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
  obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hw
  have hxl : ω x l = 0 := ha.isRefl _ _ (hx l hl)
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
    hL hl m hm,hx m hm,hxl,ha x,smul_zero,add_zero]

/-- Finite-dimensional finite-field spaces admit Lagrangian extensions of
all isotropic spaces; no completion or existence axiom is used. -/
theorem exists_containing_lagrangian (ha : ω.IsAlt) (S : Submodule K E)
    (hS : S ≤ ω.orthogonal S) :
    ∃ L : Submodule K E, S ≤ L ∧ ω.orthogonal L = L := by
  classical
  let A : Set (Submodule K E) := {L | S ≤ L ∧ L ≤ ω.orthogonal L}
  obtain ⟨L,hL,hmax⟩ := (Set.toFinite A).exists_maximal ⟨S,le_rfl,hS⟩
  refine ⟨L,hL.1,le_antisymm ?_ hL.2⟩
  intro x hx
  have hU : (L ⊔ K ∙ x) ∈ A :=
    ⟨hL.1.trans le_sup_left,isotropic_sup_line ω ha L hL.2 x hx⟩
  exact hmax hU le_sup_left ((le_sup_right : K ∙ x ≤ L ⊔ K ∙ x) (Submodule.mem_span_singleton_self x))

end IsotropicExtension
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section QuotientExtension
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)

omit [FiniteDimensional K E] in
/-- The form splits as an orthogonal direct sum along a nondegenerate subspace. -/
theorem form_orthogonal_sum (ha : ω.IsAlt) (U : Submodule K E)
    (x y : U × ω.orthogonal U) :
    ω (x.1.val + x.2.val) (y.1.val + y.2.val) =
      ω x.1.val y.1.val + ω x.2.val y.2.val := by
  have hxy : ω x.1.val y.2.val = 0 := y.2.property x.1.val x.1.property
  have hyx : ω x.2.val y.1.val = 0 :=
    ha.isRefl _ _ (x.2.property y.1.val y.1.property)
  simp only [map_add, LinearMap.add_apply, hxy, hyx, add_zero, zero_add]

/-- An isometry of a nondegenerate subspace extends by identity on its
orthogonal complement. This avoids any symplectic-basis assumptions. -/
theorem exists_orthogonal_extension (ha : ω.IsAlt) (U : Submodule K E)
    (hU : (ω.restrict U).Nondegenerate) (f : U ≃ₗ[K] U)
    (hf : ∀ x y : U, ω (f x).val (f y).val = ω x.val y.val) :
    ∃ e : E ≃ₗ[K] E,
      (∀ x y, ω (e x) (e y) = ω x y) ∧
      (∀ x : U, e x.val = (f x).val) ∧
      (∀ x : ω.orthogonal U, e x.val = x.val) := by
  let c := U.prodEquivOfIsCompl (ω.orthogonal U)
    (ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hU)
  let e := c.symm.trans ((f.prodCongr (LinearEquiv.refl K (ω.orthogonal U))).trans c)
  have he (x : U × ω.orthogonal U) : e (c x) = c (f x.1,x.2) := by
    simp [e]
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨x,rfl⟩ := c.surjective x
    obtain ⟨y,rfl⟩ := c.surjective y
    rw [he,he]
    change ω ((f x.1).val + x.2.val) ((f y.1).val + y.2.val) =
      ω (x.1.val + x.2.val) (y.1.val + y.2.val)
    rw [form_orthogonal_sum ω ha U (f x.1,x.2) (f y.1,y.2),
      form_orthogonal_sum ω ha U x y,hf]
  · intro x
    have h := he (x,0)
    simpa [c] using h
  · intro x
    have h := he (0,x)
    simpa [c] using h

omit [FiniteDimensional K E] in
/-- A linear section of the symplectic quotient automatically preserves the
form, because that form was defined on representatives. -/
theorem reduction_section_isometry (ha : ω.IsAlt)
    (s : ReducedSpace ω S →ₗ[K] ω.orthogonal S)
    (hs : (reductionKernel ω S).mkQ.comp s = LinearMap.id)
    (x y : ReducedSpace ω S) :
    ω (s x).val (s y).val = symplecticReductionForm ω S ha x y := by
  have hx : (reductionKernel ω S).mkQ (s x) = x := LinearMap.congr_fun hs x
  have hy : (reductionKernel ω S).mkQ (s y) = y := LinearMap.congr_fun hs y
  calc
    _ = symplecticReductionForm ω S ha
      ((reductionKernel ω S).mkQ (s x)) ((reductionKernel ω S).mkQ (s y)) := rfl
    _ = _ := by rw [hx,hy]





theorem exists_reduction_isometry_extension (ha : ω.IsAlt)
    (hω : ω.Nondegenerate)
    (f : ReducedSpace ω S ≃ₗ[K] ReducedSpace ω S)
    (hf : ∀ x y, symplecticReductionForm ω S ha (f x) (f y) =
      symplecticReductionForm ω S ha x y) :
    ∃ e : E ≃ₗ[K] E,
      (∀ x y, ω (e x) (e y) = ω x y) ∧
      (∀ x : S, e x.val = x.val) ∧
      (∀ x : ω.orthogonal S, e x.val ∈ ω.orthogonal S) ∧
      (∀ x y : ω.orthogonal S, e x.val = y.val →
        (reductionKernel ω S).mkQ y = f ((reductionKernel ω S).mkQ x)) := by
  let π := (reductionKernel ω S).mkQ
  obtain ⟨s,hs⟩ := π.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _))
  let g : ReducedSpace ω S →ₗ[K] E := (ω.orthogonal S).subtype.comp s
  have hπ (x : ReducedSpace ω S) : π (s x) = x := LinearMap.congr_fun hs x
  have hg (x y : ReducedSpace ω S) : ω (g x) (g y) =
      symplecticReductionForm ω S ha x y :=
    reduction_section_isometry ω S ha s hs x y
  have hginj : Function.Injective g := by
    intro x y h
    have h' : s x = s y := Subtype.ext h
    simpa only [hπ] using congrArg π h'
  let U := g.range
  let j : ReducedSpace ω S ≃ₗ[K] U := LinearEquiv.ofInjective g hginj
  have hj (x : ReducedSpace ω S) : (j x).val = g x := rfl
  have hUn : (ω.restrict U).Nondegenerate := by
    have hn := symplecticReductionForm_nondegenerate ω S ha hω
    have left (x : U) (hx : ∀ y : U, ω x.val y.val = 0) : x = 0 := by
      obtain ⟨x,rfl⟩ := j.surjective x
      have hx0 : x = 0 := hn.1 x (fun y => by
        rw [← hg]
        exact hx (j y))
      simp [hx0]
    refine ⟨left, ?_⟩
    intro x hx
    apply left
    intro y
    exact ha.isRefl _ _ (hx y)
  let fU := j.symm.trans (f.trans j)
  have hfU (x y : U) : ω (fU x).val (fU y).val = ω x.val y.val := by
    obtain ⟨x,rfl⟩ := j.surjective x
    obtain ⟨y,rfl⟩ := j.surjective y
    change ω (j (f (j.symm (j x)))).val (j (f (j.symm (j y)))).val = ω (j x).val (j y).val
    simp only [j.symm_apply_apply,hj,hg,hf]
  obtain ⟨e,he,heU,heO⟩ := exists_orthogonal_extension ω ha U hUn fU hfU
  have hSO : S ≤ ω.orthogonal U := by
    intro x hx y hy
    obtain ⟨z,rfl⟩ := hy
    exact ha.isRefl _ _ ((s z).property x hx)
  have heS (x : S) : e x.val = x.val := heO ⟨x.val,hSO x.property⟩
  have heP (x : ω.orthogonal S) : e x.val ∈ ω.orthogonal S := by
    intro y hy
    have hyfix : e y = y := heS ⟨y,hy⟩
    rw [← hyfix,he]
    exact x.property y hy
  refine ⟨e,he,heS,heP,?_⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply (symplecticReductionForm_nondegenerate ω S ha hω).1
  intro z
  have hpair (a : ω.orthogonal S) (b : ReducedSpace ω S) :
      symplecticReductionForm ω S ha (π a) b = ω a.val (g b) := by
    calc
      _ = symplecticReductionForm ω S ha (π a) (π (s b)) := by rw [hπ]
      _ = _ := rfl
  have hegj (z : ReducedSpace ω S) : e (g z) = g (f z) := by
    have h := heU (j z)
    simpa only [fU,LinearEquiv.trans_apply,j.symm_apply_apply,hj] using h
  change symplecticReductionForm ω S ha (π y - f (π x)) z = 0
  rw [map_sub,LinearMap.sub_apply,sub_eq_zero]
  rw [hpair]
  calc
    ω y.val (g z) = ω (e x.val) (e (g (f.symm z))) := by
      rw [hxy,hegj,f.apply_symm_apply]
    _ = ω x.val (g (f.symm z)) := he _ _
    _ = symplecticReductionForm ω S ha (π x) (f.symm z) := (hpair x _).symm
    _ = symplecticReductionForm ω S ha (f (π x)) z := by
      simpa only [f.apply_symm_apply] using (hf (π x) (f.symm z)).symm

end QuotientExtension
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module

/-- Equal fiber cardinalities imply an exactly uniform pushforward, without
any measure-theoretic identification or conditional-independence assumption. -/
theorem equal_fiber_card_identity {A B : Type*} [Finite A] [Finite B]
    (f : A → B) (b : B)
    (h : ∀ c : B, Nonempty ({a : A // f a = b} ≃ {a : A // f a = c})) :
    Nat.card {a : A // f a = b} * Nat.card B = Nat.card A := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  have hc (c : B) : Nat.card {a : A // f a = c} = Nat.card {a : A // f a = b} :=
    (Nat.card_congr (h c).some).symm
  calc
    _ = ∑ c : B, Nat.card {a : A // f a = c} := by
      simp only [hc,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
      exact Nat.mul_comm _ _
    _ = Nat.card (Σ c : B, {a : A // f a = c}) := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]
    _ = Nat.card A := Nat.card_congr (Equiv.sigmaFiberEquiv f)

section ReductionLaws
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)

/-- Naturality of reduction for an actual extension of a quotient map. -/
theorem reduceSubspace_map (e : E ≃ₗ[K] E)
    (f : ReducedSpace ω S ≃ₗ[K] ReducedSpace ω S)
    (hP : (ω.orthogonal S).map e.toLinearMap = ω.orthogonal S)
    (hQ : ∀ x y : ω.orthogonal S, e x.val = y.val →
      (reductionKernel ω S).mkQ y = f ((reductionKernel ω S).mkQ x))
    (L : Submodule K E) :
    reduceSubspace ω S (L.map e.toLinearMap) =
      (reduceSubspace ω S L).map f.toLinearMap := by
  ext z
  constructor
  · rintro ⟨y,⟨x,hx,hxy⟩,rfl⟩
    have hxP : x ∈ ω.orthogonal S := by
      have hyP : y.val ∈ (ω.orthogonal S).map e.toLinearMap := hP.symm ▸ y.property
      obtain ⟨x',hx',hx'y⟩ := hyP
      have heq : x' = x := e.injective (hx'y.trans hxy.symm)
      exact heq ▸ hx'
    refine ⟨(reductionKernel ω S).mkQ ⟨x,hxP⟩,⟨⟨x,hxP⟩,hx,rfl⟩,?_⟩
    exact (hQ ⟨x,hxP⟩ y hxy).symm
  · rintro ⟨w,⟨x,hx,rfl⟩,rfl⟩
    have hyP : e x.val ∈ ω.orthogonal S := hP.le ⟨x.val,x.property,rfl⟩
    refine ⟨⟨e x.val,hyP⟩,⟨x.val,hx,rfl⟩,?_⟩
    exact hQ x ⟨e x.val,hyP⟩ rfl

/-- A pointwise-fixed subspace is fixed under the subspace action. -/
theorem subspace_map_eq_of_fixed (e : E ≃ₗ[K] E) (U : Submodule K E)
    (h : ∀ x : U, e x.val = x.val) : U.map e.toLinearMap = U := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change e y ∈ U
    rw [h ⟨y,hy⟩]
    exact hy
  · intro hx
    exact ⟨x,hx,h ⟨x,hx⟩⟩

abbrev AvoidanceSpace (A : Submodule K E) :=
  {L : Submodule K E // ω.orthogonal L = L ∧ L ⊓ S = A}

/-- An extension fixing S preserves separately each containment-and-avoidance
condition A⊂L, L∩S=A used in the independent residual laws. -/
noncomputable def avoidanceIsometryEquiv (A : Submodule K E) (hAS : A ≤ S)
    (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y) = ω x y)
    (hS : ∀ x : S, e x.val = x.val) :
    AvoidanceSpace ω S A ≃ AvoidanceSpace ω S A := by
  have hSm := subspace_map_eq_of_fixed e S hS
  have hAm := subspace_map_eq_of_fixed e A (fun x => hS ⟨x.val,hAS x.property⟩)
  refine (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv ?_
  intro L
  change (ω.orthogonal L = L ∧ L ⊓ S = A) ↔
    (ω.orthogonal (L.map e.toLinearMap) = L.map e.toLinearMap ∧
      L.map e.toLinearMap ⊓ S = A)
  have hinj := (Submodule.orderIsoMapComap e).injective
  constructor
  · rintro ⟨hL,hLA⟩
    constructor
    · rw [orthogonal_map_of_isometry ω e he,hL]
    · calc
        L.map e.toLinearMap ⊓ S = L.map e.toLinearMap ⊓ S.map e.toLinearMap := by rw [hSm]
        _ = (L ⊓ S).map e.toLinearMap := (Submodule.map_inf e.toLinearMap e.injective).symm
        _ = A.map e.toLinearMap := congrArg (Submodule.map e.toLinearMap) hLA
        _ = A := hAm
  · rintro ⟨hL,hLA⟩
    constructor
    · apply hinj
      change (ω.orthogonal L).map e.toLinearMap = L.map e.toLinearMap
      rw [← orthogonal_map_of_isometry ω e he,hL]
    · apply hinj
      change (L ⊓ S).map e.toLinearMap = A.map e.toLinearMap
      rw [Submodule.map_inf e.toLinearMap e.injective,hSm,hAm,hLA]

variable [FiniteDimensional K E]

noncomputable def avoidanceReduction (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hS : S ≤ ω.orthogonal S) (A : Submodule K E) :
    AvoidanceSpace ω S A →
      {T : Submodule K (ReducedSpace ω S) //
        (symplecticReductionForm ω S ha).orthogonal T = T} :=
  fun L => ⟨reduceSubspace ω S L.val,
    general_lagrangian_reduction ω S ha hω hS L.val L.property.1⟩



theorem avoidanceReduction_fiber_equiv (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
    (A : Submodule K E) (hAS : A ≤ S)
    (T U : {T : Submodule K (ReducedSpace ω S) //
      (symplecticReductionForm ω S ha).orthogonal T = T}) :
    Nonempty ({L : AvoidanceSpace ω S A // avoidanceReduction ω S ha hω hS A L = T} ≃
      {L : AvoidanceSpace ω S A // avoidanceReduction ω S ha hω hS A L = U}) := by
  let B := symplecticReductionForm ω S ha
  obtain ⟨f,hf,hTU⟩ := lagrangian_transitivity B T.val h2
    (symplecticReductionForm_alt ω S ha)
    (symplecticReductionForm_nondegenerate ω S ha hω) T.property U.val U.property
  obtain ⟨e,he,heS,_,heQ⟩ := exists_reduction_isometry_extension ω S ha hω f hf
  let a := avoidanceIsometryEquiv ω S A hAS e he heS
  have hPm : (ω.orthogonal S).map e.toLinearMap = ω.orthogonal S := by
    rw [← orthogonal_map_of_isometry ω e he,subspace_map_eq_of_fixed e S heS]
  have hred (L : AvoidanceSpace ω S A) :
      (avoidanceReduction ω S ha hω hS A (a L)).val =
        (avoidanceReduction ω S ha hω hS A L).val.map f.toLinearMap :=
    reduceSubspace_map ω S e f hPm heQ L.val
  refine ⟨a.subtypeEquiv ?_⟩
  intro L
  constructor
  · intro hL
    apply Subtype.ext
    rw [hred,hL]
    exact hTU
  · intro hL
    apply Subtype.ext
    apply (Submodule.orderIsoMapComap f).injective
    change (avoidanceReduction ω S ha hω hS A L).val.map f.toLinearMap = T.val.map f.toLinearMap
    rw [← hred,hL,hTU]

variable [Finite E]

/-- The conditional residual law is exactly uniform, in cardinal form.
It remains valid when the conditioning event is empty, without division by 0. -/
theorem avoidanceReduction_uniform (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
    (A : Submodule K E) (hAS : A ≤ S)
    (T : {T : Submodule K (ReducedSpace ω S) //
      (symplecticReductionForm ω S ha).orthogonal T = T}) :
    Nat.card {L : AvoidanceSpace ω S A // avoidanceReduction ω S ha hω hS A L = T} *
      Nat.card {U : Submodule K (ReducedSpace ω S) //
        (symplecticReductionForm ω S ha).orthogonal U = U} =
        Nat.card (AvoidanceSpace ω S A) := by
  classical
  let := Fintype.ofFinite E
  let := Fintype.ofFinite (ω.orthogonal S)
  exact equal_fiber_card_identity (avoidanceReduction ω S ha hω hS A) T
    (avoidanceReduction_fiber_equiv ω S h2 ha hω hS A hAS T)

end ReductionLaws
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module

/-- A prescribed equivalence of subspaces extends to the ambient spaces
when both ambient dimensions and the complementary dimensions agree. -/
theorem exists_linearEquiv_extension
    {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
    (U : Submodule K E) (W : Submodule K F)
    (hEF : finrank K E = finrank K F) (f : U ≃ₗ[K] W) :
    ∃ e : E ≃ₗ[K] F, ∀ u : U, e u.val = (f u).val := by
  obtain ⟨U',hU⟩ := U.exists_isCompl
  obtain ⟨W',hW⟩ := W.exists_isCompl
  let cU := Submodule.prodEquivOfIsCompl U U' hU
  let cW := Submodule.prodEquivOfIsCompl W W' hW
  have hdim : finrank K U' = finrank K W' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hU
    have h2 := Submodule.finrank_add_eq_of_isCompl hW
    have h3 := f.finrank_eq
    omega
  let g : U' ≃ₗ[K] W' := LinearEquiv.ofFinrankEq U' W' hdim
  let e := cU.symm.trans ((f.prodCongr g).trans cW)
  refine ⟨e, ?_⟩
  intro u
  have hu : cU (u,0) = u.val := by simp [cU]
  change cW ((f.prodCongr g) (cU.symm u.val)) = (f u).val
  rw [← hu, cU.symm_apply_apply]
  simp [cW]

/-- Full linear groups are transitive on subspaces of each dimension. -/
theorem subspace_transitivity
    {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
    (U : Submodule K E) (W : Submodule K F)
    (hEF : finrank K E = finrank K F) (hUW : finrank K U = finrank K W) :
    ∃ e : E ≃ₗ[K] F, U.map e.toLinearMap = W := by
  let f : U ≃ₗ[K] W := LinearEquiv.ofFinrankEq U W hUW
  obtain ⟨e,he⟩ := exists_linearEquiv_extension U W hEF f
  refine ⟨e, ?_⟩
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change e y ∈ W
    rw [he ⟨y,hy⟩]
    exact (f ⟨y,hy⟩).property
  · intro hx
    let u := f.symm ⟨x,hx⟩
    refine ⟨u.val,u.property, ?_⟩
    change e u.val = x
    rw [he]
    exact congrArg Subtype.val (f.apply_symm_apply ⟨x,hx⟩)

end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section IsotropicTransitivity
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)



theorem isotropic_transitivity (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (S T : Submodule K E)
    (hS : S ≤ ω.orthogonal S) (hT : T ≤ ω.orthogonal T)
    (hST : finrank K S = finrank K T) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧ S.map e.toLinearMap = T := by
  obtain ⟨L,hSL,hL⟩ := exists_containing_lagrangian ω ha S hS
  obtain ⟨M,hTM,hM⟩ := exists_containing_lagrangian ω ha T hT
  obtain ⟨eL,hEL,hωL⟩ := exists_lagrangian_coordinates ω L h2 ha hω hL
  obtain ⟨eM,hEM,hωM⟩ := exists_lagrangian_coordinates ω M h2 ha hω hM
  have hdim : finrank K L = finrank K M := by
    have h1 := self_orthogonal_twice_finrank ω L hω hL
    have h2 := self_orthogonal_twice_finrank ω M hω hM
    omega
  let U := S.comap L.subtype
  let W := T.comap M.subtype
  have hUW : finrank K U = finrank K W := by
    exact (Submodule.comapSubtypeEquivOfLe hSL).finrank_eq.trans
      (hST.trans (Submodule.comapSubtypeEquivOfLe hTM).finrank_eq.symm)
  obtain ⟨f,hf⟩ := subspace_transitivity U W hdim hUW
  let c : (L × Module.Dual K L) ≃ₗ[K] (M × Module.Dual K M) :=
    f.prodCongr f.symm.dualMap
  have hc (x y : L × Module.Dual K L) :
      canonicalSymplectic (c x) (c y) = canonicalSymplectic x y := by
    simp [c,canonicalSymplectic_apply]
  let e := eL.symm.trans (c.trans eM)
  have he (l : L) : e l.val = (f l).val := by
    change eM (c (eL.symm l.val)) = (f l).val
    rw [← hEL l, eL.symm_apply_apply]
    simpa [c] using hEM (f l)
  refine ⟨e, ?_, ?_⟩
  · intro x y
    change ω (eM (c (eL.symm x))) (eM (c (eL.symm y))) = ω x y
    rw [hωM, hc, ← hωL, eL.apply_symm_apply, eL.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change e y ∈ T
      rw [he ⟨y,hSL hy⟩]
      have hfu : f ⟨y,hSL hy⟩ ∈ U.map f.toLinearMap := ⟨⟨y,hSL hy⟩,hy,rfl⟩
      exact hf.le hfu
    · intro hx
      have hw : (⟨x,hTM hx⟩ : M) ∈ W := hx
      obtain ⟨l,hl,hel⟩ := hf.ge hw
      refine ⟨l.val,hl, ?_⟩
      change e l.val = x
      rw [he]
      exact congrArg Subtype.val hel

end IsotropicTransitivity
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section TransversePairs
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)

theorem transverse_isCompl (hω : ω.Nondegenerate)
    (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLM : L ⊓ M = ⊥) : IsCompl L M := by
  have h1 := self_orthogonal_twice_finrank ω L hω hL
  have h2 := self_orthogonal_twice_finrank ω M hω hM
  apply (Submodule.isCompl_iff_disjoint L M (by omega)).mpr
  exact disjoint_iff.mpr hLM

/-- Darboux coordinates respecting a specified ordered transverse pair. -/
theorem exists_transverse_pair_coordinates (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLM : L ⊓ M = ⊥) :
    ∃ e : (L × Module.Dual K L) ≃ₗ[K] E,
      (∀ x, e x ∈ L ↔ x.2 = 0) ∧ (∀ x, e x ∈ M ↔ x.1 = 0) ∧
      ∀ x y, ω (e x) (e y) = canonicalSymplectic x y := by
  let p := (symplecticProjection ω L).comp M.subtype
  have hp : Function.Injective p := by
    apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).mpr
    intro m hm
    apply Subtype.ext
    have hml : m.val ∈ L := (symplecticProjection_ker ω L hL).le hm
    have hz : m.val ∈ L ⊓ M := ⟨hml,m.property⟩
    change m.val = 0
    simpa only [hLM,Submodule.mem_bot] using hz
  have hd : finrank K M = finrank K (Module.Dual K L) := by
    rw [Subspace.dual_finrank_eq]
    have h1 := self_orthogonal_twice_finrank ω L hω hL
    have h2 := self_orthogonal_twice_finrank ω M hω hM
    omega
  let f : M ≃ₗ[K] Module.Dual K L := LinearEquiv.ofBijective p
    ⟨hp,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hp⟩
  let d := Submodule.prodEquivOfIsCompl L M (transverse_isCompl ω hω L M hL hM hLM)
  let e := ((LinearEquiv.refl K L).prodCongr f.symm).trans d
  have he (x : L × Module.Dual K L) : e x = x.1.val + (f.symm x.2).val := rfl
  have hproj (x : L × Module.Dual K L) : symplecticProjection ω L (e x) = x.2 := by
    rw [he,map_add]
    have hl : symplecticProjection ω L x.1.val = 0 :=
      (symplecticProjection_ker ω L hL).ge x.1.property
    rw [hl,zero_add]
    exact f.apply_symm_apply x.2
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hz : symplecticProjection ω L (e x) = 0 :=
        (symplecticProjection_ker ω L hL).ge hx
      rwa [hproj] at hz
    · intro hx
      apply (symplecticProjection_ker ω L hL).le
      change symplecticProjection ω L (e x) = 0
      rw [hproj,hx]
  · intro x
    constructor
    · intro hx
      have hv : x.1.val ∈ M := by
        have hh := M.sub_mem hx (f.symm x.2).property
        simpa only [he,add_sub_cancel_right] using hh
      have hz : x.1.val ∈ L ⊓ M := ⟨x.1.property,hv⟩
      apply Subtype.ext
      change x.1.val = 0
      simpa only [hLM,Submodule.mem_bot] using hz
    · intro hx
      rw [he,hx]
      simp
  · intro x y
    have hLL : ω x.1.val y.1.val = 0 := (hL.ge y.1.property) x.1.val x.1.property
    have hMM : ω (f.symm x.2).val (f.symm y.2).val = 0 :=
      (hM.ge (f.symm y.2).property) (f.symm x.2).val (f.symm x.2).property
    have hfg (g : Module.Dual K L) (l : L) : ω l.val (f.symm g).val = g l :=
      LinearMap.congr_fun (f.apply_symm_apply g) l
    rw [he,he]
    simp only [map_add,LinearMap.add_apply,hLL,hMM,
      ← ha.neg_eq y.1.val (f.symm x.2).val,hfg,canonicalSymplectic_apply]
    ring

end TransversePairs
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module

 theorem subspace_map_eq_of_mem_iff
    {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] (e : E ≃ₗ[K] F)
    (U : Submodule K E) (W : Submodule K F)
    (h : ∀ x, e x ∈ W ↔ x ∈ U) : U.map e.toLinearMap = W := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (h y).mpr hy
  · intro hx
    refine ⟨e.symm x,(h (e.symm x)).mp ?_,e.apply_symm_apply x⟩
    simpa only [e.apply_symm_apply] using hx

section PairTransitivity
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)

theorem transverse_pair_transitivity (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M L' M' : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M')
    (hLM : L ⊓ M = ⊥) (hLM' : L' ⊓ M' = ⊥) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' := by
  obtain ⟨eL,hEL,hEM,hωL⟩ := exists_transverse_pair_coordinates ω ha hω L M hL hM hLM
  obtain ⟨eM,hEL',hEM',hωM⟩ := exists_transverse_pair_coordinates ω ha hω L' M' hL' hM' hLM'
  have hdim : finrank K L = finrank K L' := by
    have h1 := self_orthogonal_twice_finrank ω L hω hL
    have h2 := self_orthogonal_twice_finrank ω L' hω hL'
    omega
  let f : L ≃ₗ[K] L' := LinearEquiv.ofFinrankEq L L' hdim
  let c : (L × Module.Dual K L) ≃ₗ[K] (L' × Module.Dual K L') :=
    f.prodCongr f.symm.dualMap
  have hc (x y : L × Module.Dual K L) :
      canonicalSymplectic (c x) (c y) = canonicalSymplectic x y := by
    simp [c,canonicalSymplectic_apply]
  let e := eL.symm.trans (c.trans eM)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x y
    change ω (eM (c (eL.symm x))) (eM (c (eL.symm y))) = ω x y
    rw [hωM, hc, ← hωL, eL.apply_symm_apply, eL.apply_symm_apply]
  · apply subspace_map_eq_of_mem_iff e
    intro x
    change eM (c (eL.symm x)) ∈ L' ↔ x ∈ L
    rw [hEL']
    change f.symm.dualMap ((eL.symm x).2) = 0 ↔ x ∈ L
    rw [LinearEquiv.map_eq_zero_iff]
    simpa only [eL.apply_symm_apply] using (hEL (eL.symm x)).symm
  · apply subspace_map_eq_of_mem_iff e
    intro x
    change eM (c (eL.symm x)) ∈ M' ↔ x ∈ M
    rw [hEM']
    change f ((eL.symm x).1) = 0 ↔ x ∈ M
    rw [LinearEquiv.map_eq_zero_iff]
    simpa only [eL.apply_symm_apply] using (hEM (eL.symm x)).symm

end PairTransitivity
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section PairReduction
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)

theorem liftReduction_inf (T U : Submodule K (ReducedSpace ω S)) :
    liftReduction ω S (T ⊓ U) = liftReduction ω S T ⊓ liftReduction ω S U := by
  ext x
  simp only [mem_liftReduction,Submodule.mem_inf]
  tauto

theorem liftReduction_bot (hS : S ≤ ω.orthogonal S) :
    liftReduction ω S ⊥ = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxP,hxQ⟩ := (mem_liftReduction ω S ⊥ x).mp hx
    exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hxQ
  · intro hx
    apply (mem_liftReduction ω S ⊥ x).mpr
    refine ⟨hS hx, ?_⟩
    exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr hx

theorem reduced_pair_transverse (hS : S ≤ ω.orthogonal S)
    (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLM : L ⊓ M = S) :
    reduceSubspace ω S L ⊓ reduceSubspace ω S M = ⊥ := by
  have hSL : S ≤ L := hLM.ge.trans inf_le_left
  have hSM : S ≤ M := hLM.ge.trans inf_le_right
  apply liftReduction_injective ω S
  rw [liftReduction_inf,lift_reduce ω S L hSL (lagrangian_le_orthogonal ω S L hL hSL),
    lift_reduce ω S M hSM (lagrangian_le_orthogonal ω S M hM hSM),
    liftReduction_bot ω S hS,hLM]

variable [FiniteDimensional K E]

theorem pair_transitivity_fixed_intersection (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hS : S ≤ ω.orthogonal S) (L M L' M' : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M')
    (hLM : L ⊓ M = S) (hLM' : L' ⊓ M' = S) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' := by
  have hSL : S ≤ L := hLM.ge.trans inf_le_left
  have hSM : S ≤ M := hLM.ge.trans inf_le_right
  have hSL' : S ≤ L' := hLM'.ge.trans inf_le_left
  have hSM' : S ≤ M' := hLM'.ge.trans inf_le_right
  let Ω := symplecticReductionForm ω S ha
  have hΩa : Ω.IsAlt := symplecticReductionForm_alt ω S ha
  have hΩ : Ω.Nondegenerate := symplecticReductionForm_nondegenerate ω S ha hω
  obtain ⟨f,hf,hfL,hfM⟩ := transverse_pair_transitivity Ω hΩa hΩ
    (reduceSubspace ω S L) (reduceSubspace ω S M)
    (reduceSubspace ω S L') (reduceSubspace ω S M')
    (reduce_lagrangian ω S ha hS L hL hSL)
    (reduce_lagrangian ω S ha hS M hM hSM)
    (reduce_lagrangian ω S ha hS L' hL' hSL')
    (reduce_lagrangian ω S ha hS M' hM' hSM')
    (reduced_pair_transverse ω S hS L M hL hM hLM)
    (reduced_pair_transverse ω S hS L' M' hL' hM' hLM')
  obtain ⟨e,he,heS,heP,heQ⟩ := exists_reduction_isometry_extension ω S ha hω f hf
  have hSe : S.map e.toLinearMap = S := subspace_map_eq_of_fixed e S heS
  have hPe : (ω.orthogonal S).map e.toLinearMap = ω.orthogonal S := by
    rw [← orthogonal_map_of_isometry ω e he,hSe]
  have hmap (U W : Submodule K E) (hU : ω.orthogonal U = U)
      (hW : ω.orthogonal W = W) (hSU : S ≤ U) (hSW : S ≤ W)
      (hfU : (reduceSubspace ω S U).map f.toLinearMap = reduceSubspace ω S W) :
      U.map e.toLinearMap = W := by
    have hSUe : S ≤ U.map e.toLinearMap := by
      rw [← hSe]
      exact Submodule.map_mono hSU
    have hUe : ω.orthogonal (U.map e.toLinearMap) = U.map e.toLinearMap := by
      rw [orthogonal_map_of_isometry ω e he,hU]
    calc
      U.map e.toLinearMap = liftReduction ω S (reduceSubspace ω S (U.map e.toLinearMap)) :=
        (lift_reduce ω S _ hSUe (lagrangian_le_orthogonal ω S _ hUe hSUe)).symm
      _ = liftReduction ω S (reduceSubspace ω S W) := by
        rw [reduceSubspace_map ω S e f hPe heQ,hfU]
      _ = W := lift_reduce ω S W hSW (lagrangian_le_orthogonal ω S W hW hSW)
  exact ⟨e,he,hmap L L' hL hL' hSL hSL' hfL,hmap M M' hM hM' hSM hSM' hfM⟩

end PairReduction
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section OrderedPairTransitivity
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)



theorem ordered_pair_transitivity (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (L M L' M' : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M')
    (hdim : finrank K ↥(L ⊓ M) = finrank K ↥(L' ⊓ M')) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' := by
  have hi (U V : Submodule K E) (hU : ω.orthogonal U = U) :
      U ⊓ V ≤ ω.orthogonal (U ⊓ V) := by
    intro x hx y hy
    exact (hU.ge hx.1) y hy.1
  obtain ⟨e0,he0,hS⟩ := isotropic_transitivity ω h2 ha hω
    (L ⊓ M) (L' ⊓ M') (hi L M hL) (hi L' M' hL') hdim
  have hLe : ω.orthogonal (L.map e0.toLinearMap) = L.map e0.toLinearMap := by
    rw [orthogonal_map_of_isometry ω e0 he0,hL]
  have hMe : ω.orthogonal (M.map e0.toLinearMap) = M.map e0.toLinearMap := by
    rw [orthogonal_map_of_isometry ω e0 he0,hM]
  have hLM : L.map e0.toLinearMap ⊓ M.map e0.toLinearMap = L' ⊓ M' := by
    rw [← Submodule.map_inf e0.toLinearMap e0.injective,hS]
  obtain ⟨e1,he1,hL1,hM1⟩ := pair_transitivity_fixed_intersection ω (L' ⊓ M') ha hω
    (hi L' M' hL') (L.map e0.toLinearMap) (M.map e0.toLinearMap) L' M'
    hLe hMe hL' hM' hLM rfl
  refine ⟨e0.trans e1, ?_, ?_, ?_⟩
  · intro x y
    exact (he1 (e0 x) (e0 y)).trans (he0 x y)
  · change L.map (e1.toLinearMap.comp e0.toLinearMap) = L'
    rw [Submodule.map_comp,hL1]
  · change M.map (e1.toLinearMap.comp e0.toLinearMap) = M'
    rw [Submodule.map_comp,hM1]

end OrderedPairTransitivity
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section TripleBlocks
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)




theorem pairing_from_lagrangian_surjective (ha : ω.IsAlt)
    (S N : Submodule K E) (hN : ω.orthogonal N = N) (hSN : S ⊓ N = ⊥) :
    Function.Surjective ((symplecticProjection ω S).comp N.subtype) := by
  let p := (symplecticProjection ω S).comp N.subtype
  apply LinearMap.dualMap_injective_iff.mp
  apply (LinearMap.ker_eq_bot).mp
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  obtain ⟨s,rfl⟩ := (Module.evalEquiv K S).surjective z
  have hsN : s.val ∈ N := by
    apply hN.le
    intro n hn
    have hh := LinearMap.congr_fun (LinearMap.mem_ker.mp hz) (⟨n,hn⟩ : N)
    change ω s.val n = 0 at hh
    exact ha.isRefl _ _ hh
  have hs0 : s = 0 := by
    apply Subtype.ext
    change s.val = 0
    exact hSN.le ⟨s.property,hsN⟩
  rw [hs0,map_zero]

/-- A dual to a pair-intersection space may be chosen inside the third
Lagrangian; the resulting block is nondegenerate and has canonical coordinates. -/
theorem exists_pair_block (ha : ω.IsAlt)
    (S N : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hN : ω.orthogonal N = N) (hSN : S ⊓ N = ⊥) :
    ∃ B : Submodule K E, (ω.restrict B).Nondegenerate ∧ S ≤ B ∧
      ∃ e : (S × Module.Dual K S) ≃ₗ[K] B,
        (∀ s : S, (e (s,0)).val = s.val) ∧
        (∀ f : Module.Dual K S, (e (0,f)).val ∈ N) ∧
        ∀ x y, ω (e x).val (e y).val = canonicalSymplectic x y := by
  let p := (symplecticProjection ω S).comp N.subtype
  obtain ⟨s,hs⟩ := p.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (pairing_from_lagrangian_surjective ω ha S N hN hSN))
  let g := N.subtype.comp s
  have hpair (l : S) (f : Module.Dual K S) : ω l.val (g f) = f l :=
    LinearMap.congr_fun (LinearMap.congr_fun hs f) l
  let f : (S × Module.Dual K S) →ₗ[K] E :=
    S.subtype.comp (LinearMap.fst K S (Module.Dual K S)) +
    g.comp (LinearMap.snd K S (Module.Dual K S))
  have hf (x : S × Module.Dual K S) : f x = x.1.val + g x.2 := rfl
  have hform (x y : S × Module.Dual K S) :
      ω (f x) (f y) = canonicalSymplectic x y := by
    have hSS : ω x.1.val y.1.val = 0 := hS y.1.property x.1.val x.1.property
    have hNN : ω (g x.2) (g y.2) = 0 := (hN.ge (s y.2).property) _ (s x.2).property
    rw [hf,hf]
    simp only [map_add,LinearMap.add_apply,hSS,hNN,
      ← ha.neg_eq y.1.val (g x.2),hpair,canonicalSymplectic_apply]
    ring
  have hinj : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply canonicalSymplectic_nondegenerate.1
    intro y
    rw [← hform,hx]
    simp
  let B := f.range
  let e : (S × Module.Dual K S) ≃ₗ[K] B := LinearEquiv.ofInjective f hinj
  have he (x : S × Module.Dual K S) : (e x).val = f x := rfl
  have hleft (x : B) (hx : ∀ y : B, ω x.val y.val = 0) : x = 0 := by
    obtain ⟨z,rfl⟩ := e.surjective x
    have hz : z = 0 := canonicalSymplectic_nondegenerate.1 z (fun w => by
      rw [← hform]
      exact hx (e w))
    rw [hz,map_zero]
  refine ⟨B,⟨hleft, ?_⟩, ?_,e, ?_, ?_, ?_⟩
  · intro x hx
    apply hleft
    intro y
    exact ha.isRefl _ _ (hx y)
  · intro x hx
    refine ⟨(⟨x,hx⟩,0),?_⟩
    simp [hf]
  · intro l
    simp [he,hf]
  · intro l
    change (0 : E) + (s l).val ∈ N
    simpa only [zero_add] using (s l).property
  · intro x y
    exact hform x y

/-- A Lagrangian containing a Lagrangian of a nondegenerate block splits
orthogonally over that block. No choice of extensions is hidden here. -/
theorem forced_orthogonal_splitting (ha : ω.IsAlt)
    (B L : Submodule K E) (hB : (ω.restrict B).Nondegenerate)
    (hL : L ≤ ω.orthogonal L) (T : Submodule K B)
    (hT : (ω.restrict B).orthogonal T = T) (hTL : T.map B.subtype ≤ L) :
    L = T.map B.subtype ⊔ (L ⊓ ω.orthogonal B) := by
  let c := B.prodEquivOfIsCompl (ω.orthogonal B)
    (ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hB)
  apply le_antisymm
  · intro x hx
    let b := (c.symm x).1
    let p := (c.symm x).2
    have hxp : b.val + p.val = x := c.apply_symm_apply x
    have hbT : b ∈ T := by
      apply hT.le
      intro t ht
      have htL : t.val ∈ L := hTL ⟨t,ht,rfl⟩
      have htx : ω t.val x = 0 := hL hx t.val htL
      have htp : ω t.val p.val = 0 := p.property t.val t.property
      rw [← hxp,map_add,htp,add_zero] at htx
      exact htx
    have hbL : b.val ∈ L := hTL ⟨b,hbT,rfl⟩
    have hpL : p.val ∈ L := by
      have hp : p.val = x - b.val := by rw [← hxp]; abel
      rw [hp]
      exact L.sub_mem hx hbL
    exact Submodule.mem_sup.mpr ⟨b.val,⟨b,hbT,rfl⟩,p.val,⟨hpL,p.property⟩,hxp⟩
  · exact sup_le hTL inf_le_left

/-- The remaining part of a split Lagrangian is a Lagrangian for the
restricted form on the orthogonal complement. -/
theorem split_residual_lagrangian (ha : ω.IsAlt)
    (B L : Submodule K E) (hB : (ω.restrict B).Nondegenerate)
    (hL : ω.orthogonal L = L) (T : Submodule K B)
    (hT : (ω.restrict B).orthogonal T = T) (hTL : T.map B.subtype ≤ L) :
    (ω.restrict (ω.orthogonal B)).orthogonal
      (L.comap (ω.orthogonal B).subtype) = L.comap (ω.orthogonal B).subtype := by
  have hs := forced_orthogonal_splitting ω ha B L hB hL.ge T hT hTL
  ext x
  constructor
  · intro hx
    change x.val ∈ L
    apply hL.le
    intro y hy
    rw [hs] at hy
    obtain ⟨b,⟨bt,hbt,rfl⟩,p,hp,rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add,LinearMap.add_apply]
    have hb : ω bt.val x.val = 0 := x.property bt.val bt.property
    have hq : ω p x.val = 0 := hx (⟨p,hp.2⟩ : ω.orthogonal B) hp.1
    change ω bt.val x.val + ω p x.val = 0
    rw [hb,hq,add_zero]
  · intro hx y hy
    exact hL.ge hx y.val hy

end TripleBlocks
end SidorenkoCounterexample

end OAI
