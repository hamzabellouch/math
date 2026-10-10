import OAI.Analysis.InterpolatedFactors.Restriction

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

def subalgebraEqualityEquiv (M N : StarSubalgebra ℂ A) (he : M=N) : M ≃⋆ₐ[ℂ] N :=
  subalgebraEquiv M N (StarAlgEquiv.refl ℂ A) (fun a => by change a∈N ↔ a∈M;rw [he])

@[simp] theorem subalgebraEqualityEquiv_val (M N : StarSubalgebra ℂ A) (he : M=N) (x : M) :
    (subalgebraEqualityEquiv M N he x:A)=(x:A) := rfl

variable (M : StarSubalgebra ℂ A) [IsClosed (M : Set A)]
variable (p : M) (hp : IsStarProjection p)

omit [IsClosed (M : Set A)] in
include hp in
theorem subtype_projection : IsStarProjection (p:A) :=
  hp.map M.subtype

def cornerSubtypeEquiv : Corner p hp ≃⋆ₐ[ℂ] subalgebraCorner M (p:A) (subtype_projection M p hp) p.property where
  toFun x := ⟨⟨x.val.val,⟨congrArg Subtype.val x.property.1,congrArg Subtype.val x.property.2⟩⟩,x.val.property⟩
  invFun x := ⟨⟨x.val.val,x.property⟩,⟨Subtype.ext x.val.property.1,Subtype.ext x.val.property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem projectionRepresentation_normal (p : E →L[ℂ] E) (hp : IsStarProjection p) [CompleteSpace p.range] :
    @Continuous _ _ (cornerTopology (HilbertUltraweak.topology E) p hp)
      (HilbertUltraweak.topology p.range) (projectionRepresentation p hp) := by
  let : TopologicalSpace (E →L[ℂ] E) := HilbertUltraweak.topology E
  let : TopologicalSpace (p.range →L[ℂ] p.range) := HilbertUltraweak.topology p.range
  let : TopologicalSpace (Corner p hp) := cornerTopology (HilbertUltraweak.topology E) p hp
  have he : (fun x : Corner p hp => projectionRepresentation p hp x)=
      (fun x : Corner p hp => p.range.orthogonalProjectionOnto.comp ((x:E →L[ℂ] E).comp p.range.subtypeL)) := by
    funext x
    change cornerRestrict p.range (cornerEqualityEquiv p p.range.starProjection hp isStarProjection_starProjection
      (projectionRange_starProjection p hp).symm x)=_
    unfold cornerRestrict
    rw [cornerEqualityEquiv_val]
  change Continuous (fun x : Corner p hp => projectionRepresentation p hp x)
  rw [he]
  exact (HilbertUltraweak.sandwich_continuous p.range.orthogonalProjectionOnto p.range.subtypeL).comp continuous_subtype_val

 theorem projectionRepresentation_symm_normal (p : E →L[ℂ] E) (hp : IsStarProjection p) [CompleteSpace p.range] :
    @Continuous _ _ (HilbertUltraweak.topology p.range)
      (cornerTopology (HilbertUltraweak.topology E) p hp) (projectionRepresentation p hp).symm := by
  let : TopologicalSpace (E →L[ℂ] E) := HilbertUltraweak.topology E
  let : TopologicalSpace (p.range →L[ℂ] p.range) := HilbertUltraweak.topology p.range
  apply continuous_induced_rng.mpr
  have he : (fun x : p.range →L[ℂ] p.range => ((projectionRepresentation p hp).symm x : E →L[ℂ] E))=
      (fun x : p.range →L[ℂ] p.range => p.range.subtypeL.comp (x.comp p.range.orthogonalProjectionOnto)) := by
    funext x
    have h := cornerEqualityEquiv_val p p.range.starProjection hp isStarProjection_starProjection
      (projectionRange_starProjection p hp).symm
      ((cornerEqualityEquiv p p.range.starProjection hp isStarProjection_starProjection
        (projectionRange_starProjection p hp).symm).symm ((cornerRepresentation p.range).symm x))
    rw [StarAlgEquiv.apply_symm_apply] at h
    exact h.symm
  change Continuous (fun x : p.range →L[ℂ] p.range => ((projectionRepresentation p hp).symm x : E →L[ℂ] E))
  rw [he]
  exact HilbertUltraweak.sandwich_continuous p.range.subtypeL p.range.orthogonalProjectionOnto
end

variable {A : Type u_6} {B : Type u_7} [CStarAlgebra A] [CStarAlgebra B]
@[instance_reducible] def subalgebraTopology (𝒯 : TopologicalSpace A) (M : StarSubalgebra ℂ A) : TopologicalSpace M :=
  TopologicalSpace.induced (fun x : M => (x:A)) 𝒯

theorem subalgebraEquiv_normal (M : StarSubalgebra ℂ A) (N : StarSubalgebra ℂ B)
    (e : A ≃⋆ₐ[ℂ] B) (he : ∀ a,e a∈N ↔ a∈M)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B) (hn : @Continuous _ _ 𝒯A 𝒯B e) :
    @Continuous _ _ (subalgebraTopology 𝒯A M) (subalgebraTopology 𝒯B N) (subalgebraEquiv M N e he) := by
  let : TopologicalSpace A := 𝒯A
  let : TopologicalSpace B := 𝒯B
  let : TopologicalSpace M := subalgebraTopology 𝒯A M
  exact (hn.comp continuous_subtype_val).subtype_mk _

theorem subalgebraEquiv_symm_normal (M : StarSubalgebra ℂ A) (N : StarSubalgebra ℂ B)
    (e : A ≃⋆ₐ[ℂ] B) (he : ∀ a,e a∈N ↔ a∈M)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B) (hn : @Continuous _ _ 𝒯B 𝒯A e.symm) :
    @Continuous _ _ (subalgebraTopology 𝒯B N) (subalgebraTopology 𝒯A M) (subalgebraEquiv M N e he).symm := by
  let : TopologicalSpace A := 𝒯A
  let : TopologicalSpace B := 𝒯B
  let : TopologicalSpace N := subalgebraTopology 𝒯B N
  exact (hn.comp continuous_subtype_val).subtype_mk _

theorem subalgebraEqualityEquiv_normal (M N : StarSubalgebra ℂ A) (he : M=N) (𝒯 : TopologicalSpace A) :
    @Continuous _ _ (subalgebraTopology 𝒯 M) (subalgebraTopology 𝒯 N) (subalgebraEqualityEquiv M N he) :=
  subalgebraEquiv_normal M N (StarAlgEquiv.refl ℂ A) _ 𝒯 𝒯 (@continuous_id A 𝒯)

theorem subalgebraEqualityEquiv_symm_normal (M N : StarSubalgebra ℂ A) (he : M=N) (𝒯 : TopologicalSpace A) :
    @Continuous _ _ (subalgebraTopology 𝒯 N) (subalgebraTopology 𝒯 M) (subalgebraEqualityEquiv M N he).symm :=
  subalgebraEquiv_symm_normal M N (StarAlgEquiv.refl ℂ A) _ 𝒯 𝒯 (@continuous_id A 𝒯)

theorem cornerCongr_symm_normal (Φ : A ≃⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B)
    (hΦ : @Continuous _ _ 𝒯B 𝒯A Φ.symm) :
    @Continuous _ _ (cornerTopology 𝒯B (Φ p) (map_projection Φ p hp))
      (cornerTopology 𝒯A p hp) (cornerCongr Φ p hp).symm := by
  let : TopologicalSpace A := 𝒯A
  let : TopologicalSpace B := 𝒯B
  let : TopologicalSpace (Corner (Φ p) (map_projection Φ p hp)) :=
    cornerTopology 𝒯B (Φ p) (map_projection Φ p hp)
  exact (hΦ.comp continuous_subtype_val).subtype_mk _

variable (M : StarSubalgebra ℂ A) [IsClosed (M : Set A)] (p : M) (hp : IsStarProjection p)

theorem cornerSubtypeEquiv_normal (𝒯 : TopologicalSpace A) :
    @Continuous _ _ (cornerTopology (subalgebraTopology 𝒯 M) p hp)
      (subalgebraTopology (cornerTopology 𝒯 (p:A) (subtype_projection M p hp))
        (subalgebraCorner M (p:A) (subtype_projection M p hp) p.property)) (cornerSubtypeEquiv M p hp) := by
  let : TopologicalSpace A := 𝒯
  let : TopologicalSpace M := subalgebraTopology 𝒯 M
  let : TopologicalSpace (Corner p hp) := cornerTopology (subalgebraTopology 𝒯 M) p hp
  let : TopologicalSpace (Corner (p:A) (subtype_projection M p hp)) := cornerTopology 𝒯 (p:A) (subtype_projection M p hp)
  exact ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem cornerSubtypeEquiv_symm_normal (𝒯 : TopologicalSpace A) :
    @Continuous _ _ (subalgebraTopology (cornerTopology 𝒯 (p:A) (subtype_projection M p hp))
        (subalgebraCorner M (p:A) (subtype_projection M p hp) p.property))
      (cornerTopology (subalgebraTopology 𝒯 M) p hp) (cornerSubtypeEquiv M p hp).symm := by
  let : TopologicalSpace A := 𝒯
  let : TopologicalSpace M := subalgebraTopology 𝒯 M
  let : TopologicalSpace (Corner (p:A) (subtype_projection M p hp)) := cornerTopology 𝒯 (p:A) (subtype_projection M p hp)
  let : TopologicalSpace (subalgebraCorner M (p:A) (subtype_projection M p hp) p.property) :=
    subalgebraTopology (cornerTopology 𝒯 (p:A) (subtype_projection M p hp))
      (subalgebraCorner M (p:A) (subtype_projection M p hp) p.property)
  exact ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.FreeFock
open Amplification
variable {α : Type u_8} [DecidableEq α]

theorem gaussianGroupIso_symm_normal :
    @Continuous _ _ (gaussianUltraweakTopology α) (groupUltraweakTopology (FreeGroup α))
      (gaussianGroupIso (α := α)).symm := by
  let : TopologicalSpace (GroupOperator (FreeGroup α)) := ultraweakOperatorTopology (FreeGroup α)
  let : TopologicalSpace (Operator α) := ultraweakOperatorTopology (List α)
  let : TopologicalSpace (groupVonNeumann (FreeGroup α)) := groupUltraweakTopology (FreeGroup α)
  let : TopologicalSpace (gaussianAlgebra α) := gaussianUltraweakTopology α
  have hc := ((spatial_ultraweak_continuous (haarSpatial (α := α)).symm).comp continuous_subtype_val).subtype_mk
    (fun x : gaussianAlgebra α => ((gaussianGroupIso (α := α)).symm x).property)
  convert hc using 1
  rfl

instance scalarGeneratedClosed : IsClosed (scalarSystem.generated scalarFlip : Set (Operator ScalarIndex)) :=
  Set.isClosed_centralizer _

def scalarGroupIso : groupVonNeumann (FreeGroup ScalarIndex) ≃⋆ₐ[ℂ] scalarSystem.generated scalarFlip :=
  gaussianGroupIso.trans (subalgebraEqualityEquiv _ _ scalar_generated_eq_gaussian.symm)

theorem scalarGroupIso_normal :
    @Continuous _ _ (groupUltraweakTopology (FreeGroup ScalarIndex)) (scalarSystem.generatedTopology scalarFlip)
      scalarGroupIso := by
  let : TopologicalSpace (groupVonNeumann (FreeGroup ScalarIndex)) := groupUltraweakTopology (FreeGroup ScalarIndex)
  let : TopologicalSpace (gaussianAlgebra ScalarIndex) := gaussianUltraweakTopology ScalarIndex
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  exact (subalgebraEqualityEquiv_normal _ _ scalar_generated_eq_gaussian.symm
    (HilbertUltraweak.topology (Fock ScalarIndex))).comp gaussianGroupIso_normal

theorem scalarGroupIso_symm_normal :
    @Continuous _ _ (scalarSystem.generatedTopology scalarFlip) (groupUltraweakTopology (FreeGroup ScalarIndex))
      scalarGroupIso.symm := by
  let : TopologicalSpace (groupVonNeumann (FreeGroup ScalarIndex)) := groupUltraweakTopology (FreeGroup ScalarIndex)
  let : TopologicalSpace (gaussianAlgebra ScalarIndex) := gaussianUltraweakTopology ScalarIndex
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  have hc := gaussianGroupIso_symm_normal.comp (subalgebraEqualityEquiv_symm_normal _ _
    scalar_generated_eq_gaussian.symm (HilbertUltraweak.topology (Fock ScalarIndex)))
  convert hc using 1
  rfl

def scalarTrace (T : scalarSystem.generated scalarFlip) : ℂ := vacuumTrace (T:Operator ScalarIndex)

theorem scalarGroupIso_trace (T : groupVonNeumann (FreeGroup ScalarIndex)) :
    scalarTrace (scalarGroupIso T)=canonicalTrace T := gaussianGroupIso_trace T
end FreeGroupFactorMain.FreeFock

namespace FreeGroupFactorMain.Amplification
variable {A : Type u_9} {B : Type u_10} [CStarAlgebra A] [CStarAlgebra B]
variable (p : A) (hp : IsStarProjection p) (q : Corner p hp) (hq : IsStarProjection q)

include hq in
theorem nested_projection : IsStarProjection (q:A) :=
  ⟨congrArg Subtype.val hq.isIdempotentElem.eq,congrArg Subtype.val hq.isSelfAdjoint.star_eq⟩

theorem nested_supported (x : A) (hx : (q:A)*x=x ∧ x*(q:A)=x) : p*x=x ∧ x*p=x := by
  constructor
  · calc p*x=p*((q:A)*x) := congrArg (p*·) hx.1.symm
         _=(p*(q:A))*x := (mul_assoc _ _ _).symm
         _=x := by rw [q.property.1,hx.1]
  · calc x*p=(x*(q:A))*p := congrArg (·*p) hx.2.symm
         _=x*((q:A)*p) := mul_assoc _ _ _
         _=x := by rw [q.property.2,hx.2]

def nestedCornerEquiv : Corner q hq ≃⋆ₐ[ℂ] Corner (q:A) (nested_projection p hp q hq) where
  toFun x := ⟨x.val.val,⟨congrArg Subtype.val x.property.1,congrArg Subtype.val x.property.2⟩⟩
  invFun x := ⟨⟨x.val,nested_supported p hp q x.val x.property⟩,
    ⟨Subtype.ext x.property.1,Subtype.ext x.property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

theorem nestedCornerEquiv_normal (𝒯 : TopologicalSpace A) :
    @Continuous _ _ (cornerTopology (cornerTopology 𝒯 p hp) q hq)
      (cornerTopology 𝒯 (q:A) (nested_projection p hp q hq)) (nestedCornerEquiv p hp q hq) := by
  let : TopologicalSpace A := 𝒯
  let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯 p hp
  let : TopologicalSpace (Corner q hq) := cornerTopology (cornerTopology 𝒯 p hp) q hq
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem nestedCornerEquiv_symm_normal (𝒯 : TopologicalSpace A) :
    @Continuous _ _ (cornerTopology 𝒯 (q:A) (nested_projection p hp q hq))
      (cornerTopology (cornerTopology 𝒯 p hp) q hq) (nestedCornerEquiv p hp q hq).symm := by
  let : TopologicalSpace A := 𝒯
  let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯 p hp
  let : TopologicalSpace (Corner (q:A) (nested_projection p hp q hq)) :=
    cornerTopology 𝒯 (q:A) (nested_projection p hp q hq)
  exact (continuous_subtype_val.subtype_mk _).subtype_mk _

variable (τ : A → ℂ) (𝒯 : TopologicalSpace A)

def HasCornerScaling (t : ℝ) : Prop :=
  ∃ (p : A) (hp : IsStarProjection p) (e : A ≃⋆ₐ[ℂ] Corner p hp),
    τ p=(t:ℂ) ∧
    @Continuous _ _ 𝒯 (cornerTopology 𝒯 p hp) e ∧
    @Continuous _ _ (cornerTopology 𝒯 p hp) 𝒯 e.symm ∧
    ∀ x : A, τ (e x : A)=(t:ℂ)*τ x

 theorem HasCornerScaling.mul {t s : ℝ} (ht : HasCornerScaling τ 𝒯 t)
    (hs : HasCornerScaling τ 𝒯 s) : HasCornerScaling τ 𝒯 (t*s) := by
  rcases ht with ⟨p,hp,e,hpτ,hen,hein,heτ⟩
  rcases hs with ⟨q,hq,f,hqτ,hfn,hfin,hfτ⟩
  let r : Corner p hp := e q
  have hr : IsStarProjection r := map_projection e q hq
  let g := f.trans ((cornerCongr e q hq).trans (nestedCornerEquiv p hp r hr))
  refine ⟨(r:A),nested_projection p hp r hr,g,?_,?_,?_,?_⟩
  · change τ (e q : A)=(t*s:ℝ)
    rw [heτ,hqτ,Complex.ofReal_mul]
  · let : TopologicalSpace A := 𝒯
    let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯 p hp
    let : TopologicalSpace (Corner q hq) := cornerTopology 𝒯 q hq
    let : TopologicalSpace (Corner r hr) := cornerTopology (cornerTopology 𝒯 p hp) r hr
    exact (nestedCornerEquiv_normal p hp r hr 𝒯).comp
      ((cornerCongr_normal e q hq 𝒯 (cornerTopology 𝒯 p hp) hen).comp hfn)
  · let : TopologicalSpace A := 𝒯
    let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯 p hp
    let : TopologicalSpace (Corner q hq) := cornerTopology 𝒯 q hq
    let : TopologicalSpace (Corner r hr) := cornerTopology (cornerTopology 𝒯 p hp) r hr
    let : TopologicalSpace (Corner (r:A) (nested_projection p hp r hr)) :=
      cornerTopology 𝒯 (r:A) (nested_projection p hp r hr)
    exact hfin.comp ((cornerCongr_symm_normal e q hq 𝒯 (cornerTopology 𝒯 p hp) hein).comp
      (nestedCornerEquiv_symm_normal p hp r hr 𝒯))
  · intro x
    change τ (e (f x : A) : A)=((t*s:ℝ):ℂ)*τ x
    rw [heτ,hfτ,Complex.ofReal_mul,mul_assoc]

 theorem HasCornerScaling.normalized {t : ℝ} (ht : 0<t) (h : HasCornerScaling τ 𝒯 t) :
    ∃ (p : A) (hp : IsStarProjection p) (e : Corner p hp ≃⋆ₐ[ℂ] A),
      τ p=(t:ℂ) ∧ @Continuous _ _ (cornerTopology 𝒯 p hp) 𝒯 e ∧
      @Continuous _ _ 𝒯 (cornerTopology 𝒯 p hp) e.symm ∧
      ∀ x,τ (e x)=normalizedCornerTrace τ t p hp x := by
  rcases h with ⟨p,hp,e,hpτ,hen,hein,heτ⟩
  refine ⟨p,hp,e.symm,hpτ,hein,hen,?_⟩
  intro x
  have hx := heτ (e.symm x)
  rw [StarAlgEquiv.apply_symm_apply] at hx
  change τ (e.symm x)=(t:ℂ)⁻¹*τ (x:A)
  rw [hx,← mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne'),one_mul]
end FreeGroupFactorMain.Amplification

end

end OAI
