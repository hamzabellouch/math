import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.ExactSequences

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.IntrinsicInterval
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The adjacent old flag terms and chosen subsystem. No splitting or exact-sequence data is an input. -/
structure Data (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  previous : Submodule R V
  current : Submodule R V
  subsystem : Submodule R V
  increasing : previous ≤ current

namespace Data
variable (D : Data R V)
abbrev p : Submodule R D.current := D.previous.comap D.current.subtype
abbrev n : Submodule R D.current := D.subsystem.comap D.current.subtype
abbrev G := D.current ⧸ D.p
abbrev up : Submodule R D.n := D.p.comap D.n.subtype
abbrev UG := D.n ⧸ D.up
abbrev qi : Submodule R (V ⧸ D.subsystem) := D.current.map D.subsystem.mkQ
abbrev qp : Submodule R D.qi :=
  (D.previous.map D.subsystem.mkQ).comap D.qi.subtype
abbrev QG := D.qi ⧸ D.qp
abbrev S : Submodule R D.G := D.n.map D.p.mkQ

/-- Inclusion of the induced intersection grade into the old grade. -/
def includeU : D.UG →ₗ[R] D.G :=
  D.up.mapQ D.p D.n.subtype (by intro x hx; exact hx)

@[simp] theorem includeU_mk (x : D.n) :
    D.includeU (Submodule.Quotient.mk x) = Submodule.Quotient.mk x.val := rfl

theorem includeU_injective : Function.Injective D.includeU := by
  rw [← LinearMap.ker_eq_bot, includeU, Submodule.ker_mapQ]
  change D.up.map D.up.mkQ = ⊥
  exact Submodule.mkQ_map_self D.up

theorem includeU_range : D.includeU.range = D.S := by
  rw [includeU, Submodule.range_mapQ]
  rw [Submodule.range_subtype]

/-- Send an old flag vector to its class in the quotient subsystem, retaining its membership in the induced image flag. -/
def toImage : D.current →ₗ[R] D.qi where
  toFun x := ⟨D.subsystem.mkQ x.val, ⟨x.val,x.property,rfl⟩⟩
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

@[simp] theorem toImage_val (x : D.current) :
    (D.toImage x).val=D.subsystem.mkQ x.val := rfl

theorem toImage_surjective : Function.Surjective D.toImage := by
  rintro ⟨x,hx⟩
  rcases hx with ⟨y,hy,hxy⟩
  exact ⟨⟨y,hy⟩,Subtype.ext hxy⟩

theorem p_toImage : D.p ≤ D.qp.comap D.toImage := by
  intro x hx
  exact ⟨x.val,hx,rfl⟩

/-- Projection to the successive quotient of the image flag on V/U. -/
def projectQ : D.G →ₗ[R] D.QG := D.p.mapQ D.qp D.toImage D.p_toImage

@[simp] theorem projectQ_mk (x : D.current) :
    D.projectQ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (D.toImage x) := rfl

theorem projectQ_surjective : Function.Surjective D.projectQ := by
  intro z
  rcases D.qp.mkQ_surjective z with ⟨w,rfl⟩
  rcases D.toImage_surjective w with ⟨x,rfl⟩
  exact ⟨D.p.mkQ x,rfl⟩

/-- Exactness follows from x having the same U-quotient as an element of the previous old flag iff their difference lies in U. This uses the old subspaces; compatibility is not an extra hypothesis. -/
theorem projectQ_kernel : D.projectQ.ker = D.S := by
  ext z
  rcases D.p.mkQ_surjective z with ⟨x,rfl⟩
  change D.qp.mkQ (D.toImage x)=0 ↔ D.p.mkQ x ∈ D.S
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    rcases hx with ⟨y,hy,hyx⟩
    have hxy : x.val-y ∈ D.subsystem := by
      apply (Submodule.Quotient.eq D.subsystem).mp
      exact hyx.symm
    let t : D.current := ⟨x.val-y,D.current.sub_mem x.property (D.increasing hy)⟩
    refine ⟨t,hxy,?_⟩
    apply (Submodule.Quotient.eq D.p).mpr
    change x.val-y-x.val ∈ D.previous
    simpa only [sub_sub_cancel_left] using D.previous.neg_mem hy
  · rintro ⟨t,ht,htx⟩
    have hdiff : t.val-x.val ∈ D.previous :=
      (Submodule.Quotient.eq D.p).mp htx
    refine ⟨x.val-t.val,?_ ,?_⟩
    · change x.val-t.val ∈ D.previous
      simpa only [neg_sub] using D.previous.neg_mem hdiff
    · apply (Submodule.Quotient.eq D.subsystem).mpr
      have ht' : t.val ∈ D.subsystem := ht
      change x.val-t.val-x.val ∈ D.subsystem
      simpa only [sub_sub_cancel_left] using D.subsystem.neg_mem ht'

theorem exact_at_grade : D.includeU.range = D.projectQ.ker := by
  rw [D.includeU_range,D.projectQ_kernel]

/-- The induced U-graded space is the subspace of the old grade. -/
def uGradeEquiv : D.UG ≃ₗ[R] D.S :=
  (LinearEquiv.ofInjective D.includeU D.includeU_injective).trans
    (LinearEquiv.ofEq _ _ D.includeU_range)

@[simp] theorem uGradeEquiv_val (x : D.UG) :
    (D.uGradeEquiv x).val=D.includeU x := rfl

/-- The quotient by that subspace is exactly the induced Q grade. -/
def qGradeEquiv : (D.G ⧸ D.S) ≃ₗ[R] D.QG :=
  (Submodule.quotEquivOfEq D.S D.projectQ.ker D.projectQ_kernel.symm).trans
    (LinearMap.quotKerEquivOfSurjective D.projectQ D.projectQ_surjective)

@[simp] theorem qGradeEquiv_mk (x : D.G) :
    D.qGradeEquiv (Submodule.Quotient.mk x)=D.projectQ x := rfl

/-- Every old interval canonically produces its required short exact sequence. -/
theorem boundary_exact_sequence :
    Function.Injective D.includeU ∧ D.includeU.range=D.projectQ.ker ∧
      Function.Surjective D.projectQ :=
  ⟨D.includeU_injective,D.exact_at_grade,D.projectQ_surjective⟩
end Data
end IntegralCharacterVarieties.IntrinsicInterval
namespace IntegralCharacterVarieties.IntrinsicInterval
variable {R V V' V'' : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V']
  [AddCommGroup V''] [Module R V'']

/-- Old parallel transport preserving the subsystem and old flag. -/
structure Transport (D : Data R V) (E : Data R V') where
  ambient : V ≃ₗ[R] V'
  previous : D.previous.map ambient.toLinearMap=E.previous
  current : D.current.map ambient.toLinearMap=E.current
  subsystem : D.subsystem.map ambient.toLinearMap=E.subsystem

namespace Transport
variable {D : Data R V} {E : Data R V'} {F : Data R V''}
  (g : Transport D E)

def onCurrent : D.current ≃ₗ[R] E.current :=
  g.ambient.ofSubmodules D.current E.current g.current

def onQuotient : (V ⧸ D.subsystem) ≃ₗ[R] (V' ⧸ E.subsystem) :=
  Submodule.Quotient.equiv D.subsystem E.subsystem g.ambient g.subsystem

theorem p_map : D.p.map g.onCurrent.toLinearMap=E.p := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext x
  change g.ambient.symm x.val ∈ D.previous ↔ x.val ∈ E.previous
  rw [← g.previous, Submodule.mem_map_equiv]

theorem n_map : D.n.map g.onCurrent.toLinearMap=E.n := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext x
  change g.ambient.symm x.val ∈ D.subsystem ↔ x.val ∈ E.subsystem
  rw [← g.subsystem, Submodule.mem_map_equiv]

def onGrade : D.G ≃ₗ[R] E.G :=
  Submodule.Quotient.equiv D.p E.p g.onCurrent g.p_map

def onIntersection : D.n ≃ₗ[R] E.n :=
  g.onCurrent.ofSubmodules D.n E.n g.n_map

theorem up_map : D.up.map g.onIntersection.toLinearMap=E.up := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext x
  change g.ambient.symm x.val.val ∈ D.previous ↔ x.val.val ∈ E.previous
  rw [← g.previous, Submodule.mem_map_equiv]

def onUGrade : D.UG ≃ₗ[R] E.UG :=
  Submodule.Quotient.equiv D.up E.up g.onIntersection g.up_map

theorem quotient_naturality :
    g.onQuotient.toLinearMap.comp D.subsystem.mkQ =
      E.subsystem.mkQ.comp g.ambient.toLinearMap := by
  ext x
  rfl

theorem qi_map : D.qi.map g.onQuotient.toLinearMap=E.qi := by
  change (D.current.map D.subsystem.mkQ).map g.onQuotient.toLinearMap =
    E.current.map E.subsystem.mkQ
  rw [← Submodule.map_comp, g.quotient_naturality, Submodule.map_comp,g.current]

theorem prev_image_map :
    (D.previous.map D.subsystem.mkQ).map g.onQuotient.toLinearMap =
      E.previous.map E.subsystem.mkQ := by
  rw [← Submodule.map_comp, g.quotient_naturality, Submodule.map_comp,g.previous]

def onImage : D.qi ≃ₗ[R] E.qi :=
  g.onQuotient.ofSubmodules D.qi E.qi g.qi_map

theorem qp_map : D.qp.map g.onImage.toLinearMap=E.qp := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext x
  change g.onQuotient.symm x.val ∈ D.previous.map D.subsystem.mkQ ↔
    x.val ∈ E.previous.map E.subsystem.mkQ
  rw [← g.prev_image_map, Submodule.mem_map_equiv]

def onQGrade : D.QG ≃ₗ[R] E.QG :=
  Submodule.Quotient.equiv D.qp E.qp g.onImage g.qp_map

@[simp] theorem grade_mk (x : D.current) :
    g.onGrade (Submodule.Quotient.mk x)=Submodule.Quotient.mk (g.onCurrent x) := rfl

@[simp] theorem uGrade_mk (x : D.n) :
    g.onUGrade (Submodule.Quotient.mk x)=Submodule.Quotient.mk (g.onIntersection x) := rfl

@[simp] theorem qGrade_mk (x : D.qi) :
    g.onQGrade (Submodule.Quotient.mk x)=Submodule.Quotient.mk (g.onImage x) := rfl

/-- Inclusion contact commutes with the old parallel transport. -/
theorem inclusion_naturality (x : D.UG) :
    g.onGrade (D.includeU x)=E.includeU (g.onUGrade x) := by
  induction x using Submodule.Quotient.induction_on
  rfl

/-- Image/quotient contact commutes with old parallel transport. -/
theorem projection_naturality (x : D.G) :
    g.onQGrade (D.projectQ x)=E.projectQ (g.onGrade x) := by
  induction x using Submodule.Quotient.induction_on
  rfl

theorem S_map : D.S.map g.onGrade.toLinearMap=E.S := by
  have h : g.onGrade.toLinearMap.comp D.p.mkQ =
      E.p.mkQ.comp g.onCurrent.toLinearMap := by ext x; rfl
  change (D.n.map D.p.mkQ).map g.onGrade.toLinearMap=E.n.map E.p.mkQ
  rw [← Submodule.map_comp,h,Submodule.map_comp,g.n_map]

def identity (D : Data R V) : Transport D D where
  ambient := LinearEquiv.refl R V
  previous := Submodule.map_id _
  current := Submodule.map_id _
  subsystem := Submodule.map_id _

def followedBy (h : Transport E F) : Transport D F where
  ambient := g.ambient.trans h.ambient
  previous := by
    change D.previous.map (h.ambient.toLinearMap.comp g.ambient.toLinearMap)=F.previous
    rw [Submodule.map_comp,g.previous,h.previous]
  current := by
    change D.current.map (h.ambient.toLinearMap.comp g.ambient.toLinearMap)=F.current
    rw [Submodule.map_comp,g.current,h.current]
  subsystem := by
    change D.subsystem.map (h.ambient.toLinearMap.comp g.ambient.toLinearMap)=F.subsystem
    rw [Submodule.map_comp,g.subsystem,h.subsystem]

@[simp] theorem identity_grade (x : D.G) : (identity D).onGrade x=x := by
  induction x using Submodule.Quotient.induction_on
  rfl
@[simp] theorem identity_uGrade (x : D.UG) : (identity D).onUGrade x=x := by
  induction x using Submodule.Quotient.induction_on
  rfl
@[simp] theorem identity_qGrade (x : D.QG) : (identity D).onQGrade x=x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    change (identity D).onQuotient z.val=z.val
    induction z.val using Submodule.Quotient.induction_on
    rfl

@[simp] theorem followedBy_grade (h : Transport E F) (x : D.G) :
    (g.followedBy h).onGrade x=h.onGrade (g.onGrade x) := by
  induction x using Submodule.Quotient.induction_on
  rfl
@[simp] theorem followedBy_uGrade (h : Transport E F) (x : D.UG) :
    (g.followedBy h).onUGrade x=h.onUGrade (g.onUGrade x) := by
  induction x using Submodule.Quotient.induction_on
  rfl
@[simp] theorem followedBy_qGrade (h : Transport E F) (x : D.QG) :
    (g.followedBy h).onQGrade x=h.onQGrade (g.onQGrade x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    change (g.followedBy h).onQuotient z.val=h.onQuotient (g.onQuotient z.val)
    induction z.val using Submodule.Quotient.induction_on
    rfl

end Transport
end IntegralCharacterVarieties.IntrinsicInterval

end

end OAI
