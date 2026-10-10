import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.IntervalTransport

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.ExactSequenceChart.Chart
variable {R U V Q : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup Q] [Module R Q]
variable {f : U →ₗ[R] V} {g : V →ₗ[R] Q} (C : Chart f g)

/-- A chart normalized on its identified quotient. -/
def normalized : (U × Q) ≃ₗ[R] V :=
  ((LinearEquiv.refl R U).prodCongr C.d.symm).trans C.t

@[simp] theorem normalized_apply (u : U) (q : Q) :
    C.normalized (u,q)=f u+C.sectionMap q := by
  exact C.t_eq (u,C.d.symm q)

@[simp] theorem normalized_inl (u : U) : C.normalized (u,0)=f u := by
  simp only [normalized_apply,map_zero,add_zero]

@[simp] theorem g_normalized (u : U) (q : Q) : g (C.normalized (u,q))=q := by
  rw [normalized_apply,map_add,C.gf,C.g_section,zero_add]

@[simp] theorem left_normalized (u : U) (q : Q) : C.left (C.normalized (u,q))=u := by
  rw [normalized_apply,map_add,C.left_f,C.left_section,add_zero]

@[simp] theorem normalized_symm (v : V) : C.normalized.symm v=(C.left v,g v) := by
  apply C.normalized.injective
  rw [C.normalized.apply_symm_apply,C.normalized_apply,C.decompose]

end IntegralCharacterVarieties.ExactSequenceChart.Chart

namespace IntegralCharacterVarieties.IntrinsicInterval.Transport
open ExactSequenceChart
variable {R V₀ V₁ V₂ : Type*} [CommRing R]
  [AddCommGroup V₀] [Module R V₀] [AddCommGroup V₁] [Module R V₁]
  [AddCommGroup V₂] [Module R V₂]
  {D : Data R V₀} {E : Data R V₁} {F : Data R V₂}
  (g : Transport D E) (h : Transport E F)
  (C : Chart D.includeU D.projectQ) (B : Chart E.includeU E.projectQ)
  (A : Chart F.includeU F.projectQ)

/-- The free extension term is read from old transport and the chosen splittings. It is not set to zero or replaced by a block-diagonal premise. -/
def stripShear : D.QG →ₗ[R] E.UG :=
  B.left.comp (g.onGrade.toLinearMap.comp C.sectionMap)

/-- Old transport in independently chosen normalized regular frames. -/
def stripForward : (D.UG × D.QG) ≃ₗ[R] (E.UG × E.QG) :=
  C.normalized.trans (g.onGrade.trans B.normalized.symm)

theorem onGrade_normalized (u : D.UG) (q : D.QG) :
    g.onGrade (C.normalized (u,q))=
      E.includeU (g.onUGrade u)+g.onGrade (C.sectionMap q) := by
  rw [C.normalized_apply,map_add,g.inclusion_naturality]

/-- Both diagonal maps are the induced subquotient transports; only the permitted strictly lowering block is free. -/
theorem stripForward_apply (u : D.UG) (q : D.QG) :
    g.stripForward C B (u,q)=
      (g.onUGrade u+g.stripShear C B q,g.onQGrade q) := by
  change B.normalized.symm (g.onGrade (C.normalized (u,q)))=_
  rw [B.normalized_symm]
  apply Prod.ext
  · rw [g.onGrade_normalized C,map_add,B.left_f]
    rfl
  · rw [←g.projection_naturality,C.g_normalized]

/-- Inverse CHILD transport gives the correct oriented seam convention. -/
def childDiagonal : (E.UG × E.QG) ≃ₗ[R] (D.UG × D.QG) :=
  g.onUGrade.symm.prodCongr g.onQGrade.symm

def stripResidual : (D.UG × D.QG) ≃ₗ[R] (D.UG × D.QG) :=
  (g.stripForward C B).trans g.childDiagonal

theorem stripResidual_apply (u : D.UG) (q : D.QG) :
    g.stripResidual C B (u,q)=
      (u+g.onUGrade.symm (g.stripShear C B q),q) := by
  change g.childDiagonal (g.stripForward C B (u,q))=_
  rw [g.stripForward_apply C B]
  change (g.onUGrade.symm (g.onUGrade u+g.stripShear C B q),
    g.onQGrade.symm (g.onQGrade q))=_
  rw [map_add,g.onUGrade.symm_apply_apply,g.onQGrade.symm_apply_apply]

/-- Successive strip charts reconstruct the original composite transport. -/
theorem stripForward_comp :
    (g.followedBy h).stripForward C A=
      (g.stripForward C B).trans (h.stripForward B A) := by
  apply LinearEquiv.ext
  intro z
  change A.normalized.symm ((g.followedBy h).onGrade (C.normalized z))=
    A.normalized.symm (h.onGrade (B.normalized
      (B.normalized.symm (g.onGrade (C.normalized z)))))
  rw [B.normalized.apply_symm_apply]
  rw [g.followedBy_grade]

/-- The shear cocycle is forced by transport. This is the compatibility needed when a retained old occurrence is traversed through several patches. -/
theorem stripShear_comp :
    (g.followedBy h).stripShear C A=
      h.onUGrade.toLinearMap.comp (g.stripShear C B)+
        (h.stripShear B A).comp g.onQGrade.toLinearMap := by
  apply LinearMap.ext
  intro q
  change (g.followedBy h).stripShear C A q=
    h.onUGrade (g.stripShear C B q)+h.stripShear B A (g.onQGrade q)
  have hh := congrArg Prod.fst
    (LinearEquiv.congr_fun (g.stripForward_comp h C B A) (0,q))
  simpa only [stripForward_apply,LinearEquiv.trans_apply,map_zero,zero_add,
    LinearMap.add_apply,LinearMap.comp_apply,LinearEquiv.coe_coe] using hh

end IntegralCharacterVarieties.IntrinsicInterval.Transport

namespace IntegralCharacterVarieties.RegularStripCoordinates
open ExactSequenceChart IntrinsicInterval
variable {R V₀ V₁ L T : Type*} [CommRing R]
  [AddCommGroup V₀] [Module R V₀] [AddCommGroup V₁] [Module R V₁]
  {D : Data R V₀} {E : Data R V₁}
  (g : Transport D E) (C : Chart D.includeU D.projectQ)
  (B : Chart E.includeU E.projectQ)
  (u : (L → R) ≃ₗ[R] D.UG) (q : (T → R) ≃ₗ[R] D.QG)

def grade : L ⊕ T → ℕ | .inl _ => 0 | .inr _ => 1

def coordinates : (L ⊕ T → R) ≃ₗ[R] (D.UG × D.QG) :=
  (LinearEquiv.sumArrowLequivProdArrow L T R R).trans (u.prodCongr q)

def residualCoordinates : (L ⊕ T → R) ≃ₗ[R] (L ⊕ T → R) :=
  (coordinates u q).trans ((g.stripResidual C B).trans (coordinates u q).symm)

theorem residual_lower (v : L ⊕ T → R) (l : L) :
    residualCoordinates g C B u q v (.inl l)=
      v (.inl l)+u.symm (g.onUGrade.symm (g.stripShear C B (q (v ∘ Sum.inr)))) l := by
  change u.symm ((g.stripResidual C B (u (v ∘ Sum.inl),q (v ∘ Sum.inr))).1) l=_
  rw [g.stripResidual_apply C B,map_add,u.symm_apply_apply]
  rfl

theorem residual_upper (v : L ⊕ T → R) (t : T) :
    residualCoordinates g C B u q v (.inr t)=v (.inr t) := by
  change q.symm ((g.stripResidual C B (u (v ∘ Sum.inl),q (v ∘ Sum.inr))).2) t=_
  rw [g.stripResidual_apply C B,q.symm_apply_apply]
  rfl

/-- Old parallel transport gives the IDENTIFIED flag equations in the regular lower two-block seam, with its full upper shear retained. -/
theorem residual_identified_flag :
    SameCoordinateFlag (grade (L:=L) (T:=T)) (residualCoordinates g C B u q) := by
  rw [sameCoordinateFlag_iff_lowering]
  intro k v hv i hi
  cases i with
  | inl l =>
    have hk : k=0 := Nat.eq_zero_of_le_zero hi
    subst k
    have hq : v ∘ Sum.inr=0 := by
      funext t
      exact hv (.inr t) (by rfl)
    change residualCoordinates g C B u q v (.inl l)-v (.inl l)=0
    rw [residual_lower,hq,map_zero,map_zero,map_zero,map_zero]
    simp
  | inr t =>
    change residualCoordinates g C B u q v (.inr t)-v (.inr t)=0
    rw [residual_upper,sub_self]

def parentFrame : (L ⊕ T → R) ≃ₗ[R] E.G :=
  (coordinates u q).trans (C.normalized.trans g.onGrade)

def childFrame : (L ⊕ T → R) ≃ₗ[R] E.G :=
  (coordinates u q).trans ((g.onUGrade.prodCongr g.onQGrade).trans B.normalized)

theorem comparison_is_residual :
    (parentFrame g C u q).trans (childFrame g B u q).symm=
      residualCoordinates g C B u q := by
  apply LinearEquiv.ext
  intro v
  rfl

/-- This is precisely the source regular seam law: transported source frame and target frame with inverse child transports have the same named grades. -/
theorem regular_seam_law :
    SameFramedFlag (grade (L:=L) (T:=T)) (parentFrame g C u q) (childFrame g B u q) := by
  rw [sameFramedFlag_iff,comparison_is_residual]
  exact residual_identified_flag g C B u q

end IntegralCharacterVarieties.RegularStripCoordinates

namespace IntegralCharacterVarieties.IntrinsicInterval.Data
open ExactSequenceChart
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (D : Data K V)

/-- Applied to the induced old interval: exactness is already proved, not a hypothesis of the forward producer. Over a field every quotient is free. -/
theorem actual_chart_exists : Nonempty (Chart D.includeU D.projectQ) :=
  chart_nonempty _ _ D.includeU_injective D.projectQ_surjective D.exact_at_grade.symm

end IntegralCharacterVarieties.IntrinsicInterval.Data

end

end OAI
