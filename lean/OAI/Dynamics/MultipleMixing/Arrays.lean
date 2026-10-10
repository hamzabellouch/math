import OAI.Dynamics.MultipleMixing.HilbertCodes

namespace OAI

noncomputable section

namespace Rokhlin

section

open MeasureTheory ProbabilityTheory
universe u
namespace ArrayObjects

section

structure StandardSpace where
  α : Type u
  measurableSpace : MeasurableSpace α
  standardBorel : @StandardBorelSpace α measurableSpace
  nonempty : Nonempty α

instance : CoeSort StandardSpace (Type u) := ⟨StandardSpace.α⟩
instance (S : StandardSpace) : MeasurableSpace S := S.measurableSpace
instance (S : StandardSpace) : StandardBorelSpace S := S.standardBorel
instance (S : StandardSpace) : Nonempty S := S.nonempty

abbrev Index (I : Type u) (n : ℕ) := Fin n → I
abbrev Arr (I Y : Type u) (n : ℕ) := Index I n → Y

def amap {I Y Z : Type u} (f : Y → Z) (n : ℕ) : Arr I Y n → Arr I Z n :=
  fun y v => f (y v)

def plane {I Y : Type u} (n : ℕ) (a : Fin (n + 1)) (i : I) :
    Arr I Y (n + 1) → Arr I Y n := fun y v => y (a.insertNth i v)

def planes {I Y : Type u} (n : ℕ) (J : Finset I) :
    Arr I Y (n + 1) → (j : J) → Arr I Y n :=
  fun y j => plane n (Fin.last n) j y

def zeroEquiv (I Y : Type u) [MeasurableSpace Y] : Arr I Y 0 ≃ᵐ Y where
  toFun y := y Fin.elim0
  invFun y := fun _ => y
  left_inv y := by funext v; exact congrArg y (Subsingleton.elim _ _)
  right_inv _ := rfl
  measurable_toFun := measurable_pi_apply _
  measurable_invFun := Measurable.of_eval (fun _ => measurable_id)

@[fun_prop] lemma measurable_amap {I Y Z : Type u}
    [MeasurableSpace Y] [MeasurableSpace Z] {f : Y → Z} (hf : Measurable f) (n : ℕ) :
    Measurable (amap (I := I) f n) :=
  Measurable.of_eval (fun _ => hf.comp (measurable_pi_apply _))

@[fun_prop] lemma measurable_plane {I Y : Type u} [MeasurableSpace Y]
    (n : ℕ) (a : Fin (n + 1)) (i : I) : Measurable (plane (Y := Y) n a i) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

@[fun_prop] lemma measurable_planes {I Y : Type u} [MeasurableSpace Y]
    (n : ℕ) (J : Finset I) : Measurable (planes (Y := Y) n J) :=
  Measurable.of_eval (fun _ => measurable_plane _ _ _)

@[simp] lemma amap_id {I Y : Type u} (n : ℕ) : amap (I := I) (id : Y → Y) n = id := rfl
@[simp] lemma amap_comp {I X Y Z : Type u} (g : Y → Z) (f : X → Y) (n : ℕ) :
    amap (I := I) (g ∘ f) n = amap g n ∘ amap f n := rfl
@[simp] lemma plane_amap {I Y Z : Type u} (f : Y → Z) (n : ℕ)
    (a : Fin (n + 1)) (i : I) :
    plane n a i ∘ amap f (n + 1) = amap f n ∘ plane n a i := rfl

variable (I : Type u) [Fintype I]

structure InitialLaws (X : StandardSpace.{u}) (T : X ≃ᵐ X) where
  law : (n : ℕ) → Measure (Arr I X n)
  probability : ∀ n, IsProbabilityMeasure (law n)
  invariant : ∀ n, MeasurePreserving (amap T n) (law n) (law n)
  consistent : ∀ n (a : Fin (n + 1)) i,
    (law (n + 1)).map (plane n a i) = law n
  proper : ∀ n (J : Finset I), J ≠ Finset.univ →
    (law (n + 1)).map (planes n J) = Measure.pi (fun _ : J => law n)

attribute [instance] InitialLaws.probability

structure Object {X : StandardSpace.{u}} {T : X ≃ᵐ X} (base : InitialLaws I X T) where
  Y : StandardSpace.{u}
  U : StandardSpace.{u}
  timeY : Y ≃ᵐ Y
  timeU : U ≃ᵐ U
  x : Y → X
  par : Y → U
  measurable_x : Measurable x
  measurable_par : Measurable par
  time_x : x ∘ timeY = T ∘ x
  time_par : par ∘ timeY = timeU ∘ par
  law : (n : ℕ) → Measure (Arr I Y n)
  probability : ∀ n, IsProbabilityMeasure (law n)
  invariant : ∀ n, MeasurePreserving (amap timeY n) (law n) (law n)
  over_base : ∀ n, (law n).map (amap x n) = base.law n
  consistent : ∀ n (a : Fin (n + 1)) i,
    (law (n + 1)).map (plane n a i) = law n
  proper : ∀ n (J : Finset I), J ≠ Finset.univ →
    (law (n + 1)).map (planes n J) = Measure.pi (fun _ : J => law n)
  conditional : ∀ n (J : Finset I), J ≠ Finset.univ →
    condDistrib (planes n J) (amap par (n + 1)) (law (n + 1))
      =ᵐ[(law (n + 1)).map (amap par (n + 1))]
    fun p => Measure.pi (fun j : J =>
      condDistrib (id : Arr I Y n → Arr I Y n) (amap par n) (law n)
        (plane n (Fin.last n) j p))
  local_independent : IndepFun x par ((law 0).map (zeroEquiv I Y))

attribute [instance] Object.probability

namespace Object
variable {I} {X : StandardSpace.{u}} {T : X ≃ᵐ X} {base : InitialLaws I X T}

noncomputable def localLaw (M : Object I base) : Measure M.Y :=
  (M.law 0).map (zeroEquiv I M.Y)
instance (M : Object I base) : IsProbabilityMeasure M.localLaw := by
  dsimp [localLaw]
  exact (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (zeroEquiv I M.Y).measurable.aemeasurable

noncomputable def parameter (M : Object I base) : Measure M.U := M.localLaw.map M.par
instance (M : Object I base) : IsProbabilityMeasure M.parameter :=
  (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) M.measurable_par.aemeasurable

structure Extension (M N : Object I base) where
  state : N.Y → M.Y
  parameter : N.U → M.U
  measurable_state : Measurable state
  measurable_parameter : Measurable parameter
  time_state : state ∘ N.timeY = M.timeY ∘ state
  time_parameter : parameter ∘ N.timeU = M.timeU ∘ parameter
  state_x : M.x ∘ state = N.x
  state_par : M.par ∘ state = parameter ∘ N.par
  laws : ∀ n, (N.law n).map (amap state n) = M.law n

namespace Extension

def refl (M : Object I base) : Extension M M where
  state := id
  parameter := id
  measurable_state := measurable_id
  measurable_parameter := measurable_id
  time_state := rfl
  time_parameter := rfl
  state_x := rfl
  state_par := rfl
  laws n := by simp

def comp {M N P : Object I base} (e : Extension M N) (f : Extension N P) :
    Extension M P where
  state := e.state ∘ f.state
  parameter := e.parameter ∘ f.parameter
  measurable_state := e.measurable_state.comp f.measurable_state
  measurable_parameter := e.measurable_parameter.comp f.measurable_parameter
  time_state := by rw [Function.comp_assoc, f.time_state, ← Function.comp_assoc,
    e.time_state, Function.comp_assoc]
  time_parameter := by rw [Function.comp_assoc, f.time_parameter, ← Function.comp_assoc,
    e.time_parameter, Function.comp_assoc]
  state_x := by rw [← Function.comp_assoc, e.state_x, f.state_x]
  state_par := by rw [← Function.comp_assoc, e.state_par, Function.comp_assoc,
    f.state_par, ← Function.comp_assoc]
  laws n := by
    rw [amap_comp, ← Measure.map_map (measurable_amap e.measurable_state n)
      (measurable_amap f.measurable_state n), f.laws, e.laws]

lemma measurePreserving {M N : Object I base} (e : Extension M N) (n : ℕ) :
    MeasurePreserving (amap e.state n) (N.law n) (M.law n) :=
  ⟨measurable_amap e.measurable_state n, e.laws n⟩

lemma localLaw_map {M N : Object I base} (e : Extension M N) :
    N.localLaw.map e.state = M.localLaw := by
  rw [localLaw, localLaw, Measure.map_map e.measurable_state (zeroEquiv I N.Y).measurable,
    ← e.laws 0, Measure.map_map (zeroEquiv I M.Y).measurable
      (measurable_amap e.measurable_state 0)]
  rfl

lemma parameter_map {M N : Object I base} (e : Extension M N) :
    N.parameter.map e.parameter = M.parameter := by
  rw [Object.parameter, Object.parameter, Measure.map_map e.measurable_parameter N.measurable_par,
    ← e.state_par, ← Measure.map_map M.measurable_par e.measurable_state, e.localLaw_map]

end Extension
end Object
end


lemma condDistrib_condition_const {Ω E P : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    [MeasurableSpace P] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → E) (hf : Measurable f) (c : P) :
    condDistrib f (fun _ : Ω => c) μ c = μ.map f := by
  have h := condDistrib_comp_map (μ := μ) (X := fun _ : Ω => c) measurable_const.aemeasurable
    hf.aemeasurable
  simpa only [Measure.map_const, measure_univ, one_smul,
    Measure.dirac_bind (condDistrib f (fun _ : Ω => c) μ).measurable] using h

noncomputable def trivialSpace : StandardSpace.{u} where
  α := PUnit.{u + 1}
  measurableSpace := inferInstance
  standardBorel := inferInstance
  nonempty := inferInstance

variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}

noncomputable def initialObject (base : InitialLaws I X T) : Object I base where
  Y := X
  U := trivialSpace
  timeY := T
  timeU := MeasurableEquiv.refl _
  x := id
  par := fun _ => PUnit.unit
  measurable_x := measurable_id
  measurable_par := measurable_const
  time_x := rfl
  time_par := rfl
  law := base.law
  probability := base.probability
  invariant := base.invariant
  over_base n := by simp
  consistent := base.consistent
  proper := base.proper
  conditional n J hJ := by
    have hleft := condDistrib_condition_const (base.law (n + 1))
      (planes n J) (measurable_planes n J) (fun _ : Index I (n + 1) => PUnit.unit)
    have hright := condDistrib_condition_const (base.law n)
      (id : Arr I X n → Arr I X n) measurable_id (fun _ : Index I n => PUnit.unit)
    apply Filter.Eventually.of_forall
    intro p
    have hp : p = fun _ => PUnit.unit := by
      funext v
      cases p v
      rfl
    subst p
    change condDistrib (planes n J)
      (fun _ => (fun _ : Index I (n + 1) => PUnit.unit)) (base.law (n + 1))
      (fun _ => PUnit.unit) = _
    rw [hleft, base.proper n J hJ]
    congr 1
    funext j
    change base.law n = condDistrib id
      (fun _ => (fun _ : Index I n => PUnit.unit)) (base.law n) (fun _ => PUnit.unit)
    simpa using hright.symm
  local_independent := by
    let : IsProbabilityMeasure ((base.law 0).map (zeroEquiv I X)) := inferInstance
    exact indepFun_const_right id PUnit.unit


end ArrayObjects

open scoped InnerProductSpace

namespace Saturation

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem projection_difference_inner (J : E →ₗᵢ[𝕜] H)
    (P : Submodule 𝕜 E) (Q : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPQ : ∀ x ∈ P, J x ∈ Q) (v : E) :
    ⟪Q.starProjection (J v) - J (P.starProjection v), J (P.starProjection v)⟫_𝕜 = 0 := by
  have h₁ := Q.starProjection_inner_eq_zero (J v) (J (P.starProjection v))
    (hPQ _ (P.starProjection_apply_mem v))
  have h₂ := P.starProjection_inner_eq_zero v (P.starProjection v)
    (P.starProjection_apply_mem v)
  rw [inner_sub_left] at h₁ h₂ ⊢
  rw [J.inner_map_map] at h₁
  rw [J.inner_map_map, sub_eq_zero] at ⊢
  exact (sub_eq_zero.mp h₁).symm.trans (sub_eq_zero.mp h₂)

theorem projection_norm_difference (J : E →ₗᵢ[𝕜] H)
    (P : Submodule 𝕜 E) (Q : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPQ : ∀ x ∈ P, J x ∈ Q) (v : E) :
    ‖Q.starProjection (J v)‖ ^ 2 - ‖P.starProjection v‖ ^ 2 =
      ‖Q.starProjection (J v) - J (P.starProjection v)‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (Q.starProjection (J v) - J (P.starProjection v)) (J (P.starProjection v))
    (projection_difference_inner J P Q hPQ v)
  simp only [sub_add_cancel, J.norm_map] at h
  nlinarith

theorem projection_eq_of_norm_eq (J : E →ₗᵢ[𝕜] H)
    (P : Submodule 𝕜 E) (Q : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPQ : ∀ x ∈ P, J x ∈ Q) (v : E)
    (h : ‖Q.starProjection (J v)‖ = ‖P.starProjection v‖) :
    Q.starProjection (J v) = J (P.starProjection v) := by
  have he := projection_norm_difference J P Q hPQ v
  rw [h, sub_self] at he
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp he.symm))

theorem projection_norm_mono (J : E →ₗᵢ[𝕜] H)
    (P : Submodule 𝕜 E) (Q : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPQ : ∀ x ∈ P, J x ∈ Q) (v : E) :
    ‖P.starProjection v‖ ≤ ‖Q.starProjection (J v)‖ := by
  have he := projection_norm_difference J P Q hPQ v
  nlinarith [sq_nonneg ‖Q.starProjection (J v) - J (P.starProjection v)‖,
    norm_nonneg (P.starProjection v), norm_nonneg (Q.starProjection (J v))]

end Saturation

namespace ArrayObjects

inductive DataKind (I : Type u)
  | parameter
  | outside (j : I)
  | enlarged (j : I)
  deriving Fintype

namespace Object
open scoped ENNReal
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T}

noncomputable abbrev data (M : Object I base) (n : ℕ) (d : DataKind I) :
    MeasurableSpace (Arr I M.Y (n + 1)) := by
  classical
  exact match d with
  | .parameter => MeasurableSpace.comap (amap M.par (n + 1)) inferInstance
  | .outside j => MeasurableSpace.comap (planes n (Finset.univ.erase j)) inferInstance
  | .enlarged j => MeasurableSpace.comap (amap M.par (n + 1)) inferInstance ⊔
      MeasurableSpace.comap (planes n (Finset.univ.erase j)) inferInstance

lemma data_le (M : Object I base) (n : ℕ) (d : DataKind I) : M.data n d ≤ (inferInstance : MeasurableSpace (Arr I M.Y (n + 1))) := by
  classical
  cases d with
  | parameter => exact (measurable_amap M.measurable_par _).comap_le
  | outside j => exact (measurable_planes _ _).comap_le
  | enlarged j =>
    exact sup_le ((measurable_amap M.measurable_par _).comap_le)
      ((measurable_planes _ _).comap_le)

namespace Extension
variable {M N P : Object I base}

lemma data_comap_le (e : Extension M N) (n : ℕ) (d : DataKind I) :
    MeasurableSpace.comap (amap e.state (n + 1)) (M.data n d) ≤ N.data n d := by
  classical
  have hp : MeasurableSpace.comap (amap e.state (n + 1)) (M.data n .parameter) ≤
      N.data n .parameter := by
    change MeasurableSpace.comap (amap e.state (n + 1))
      (MeasurableSpace.comap (amap M.par (n + 1)) inferInstance) ≤ _
    rw [MeasurableSpace.comap_comp, ← amap_comp, e.state_par, amap_comp]
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_amap e.measurable_parameter _).comap_le
  have ho (j : I) : MeasurableSpace.comap (amap e.state (n + 1)) (M.data n (.outside j)) ≤
      N.data n (.outside j) := by
    change MeasurableSpace.comap (amap e.state (n + 1))
      (MeasurableSpace.comap (planes n (Finset.univ.erase j)) inferInstance) ≤ _
    rw [MeasurableSpace.comap_comp]
    have he : planes n (Finset.univ.erase j) ∘ amap e.state (n + 1) =
        (fun (z : (i : Finset.univ.erase j) → Arr I N.Y n) i => amap e.state n (z i)) ∘
          planes n (Finset.univ.erase j) := rfl
    rw [he, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Measurable.of_eval (fun i =>
      (measurable_amap e.measurable_state n).comp (measurable_pi_apply i))).comap_le
  cases d with
  | parameter => exact hp
  | outside j => exact ho j
  | enlarged j =>
    change MeasurableSpace.comap (amap e.state (n + 1))
      (M.data n .parameter ⊔ M.data n (.outside j)) ≤
        N.data n .parameter ⊔ N.data n (.outside j)
    rw [MeasurableSpace.comap_sup]
    exact sup_le_sup hp (ho j)

noncomputable def pull (e : Extension M N) (n : ℕ) :
    Lp ℂ 2 (M.law n) →ₗᵢ[ℂ] Lp ℂ 2 (N.law n) :=
  Lp.compMeasurePreservingₗᵢ ℂ (amap e.state n) (e.measurePreserving n)

lemma pull_comp (e : Extension M N) (f : Extension N P) (n : ℕ) (F : Lp ℂ 2 (M.law n)) :
    (e.comp f).pull n F = f.pull n (e.pull n F) :=
  Lp.compMeasurePreserving_comp_apply F (e.measurePreserving n) (f.measurePreserving n)

lemma pull_data_mem (e : Extension M N) (n : ℕ) (d : DataKind I)
    (F : Lp ℂ 2 (M.law (n + 1))) (hF : F ∈ lpMeas ℂ ℂ (M.data n d) 2 (M.law (n + 1))) :
    e.pull (n + 1) F ∈ lpMeas ℂ ℂ (N.data n d) 2 (N.law (n + 1)) := by
  have hFm := lpMeas.aestronglyMeasurable (⟨F, hF⟩ : lpMeas ℂ ℂ (M.data n d) 2 (M.law (n + 1)))
  have hm : @Measurable _ _ (N.data n d) (M.data n d) (amap e.state (n + 1)) :=
    measurable_iff_comap_le.mpr (e.data_comap_le n d)
  have hg := hFm.stronglyMeasurable_mk.comp_measurable hm
  have he := (e.measurePreserving (n + 1)).quasiMeasurePreserving.ae_eq_comp hFm.ae_eq_mk
  have hp := Lp.coeFn_compMeasurePreserving F (e.measurePreserving (n + 1))
  exact ⟨hFm.mk F ∘ amap e.state (n + 1), hg, hp.trans he⟩

end Extension
end Object
end ArrayObjects

namespace ArrayObjects.Object
open scoped ENNReal
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T}

noncomputable def project (M : Object I base) (n : ℕ) (d : DataKind I) :
    Lp ℂ 2 (M.law (n + 1)) →L[ℂ] Lp ℂ 2 (M.law (n + 1)) :=
  haveI : Fact (M.data n d ≤ (inferInstance : MeasurableSpace (Arr I M.Y (n + 1)))) :=
    ⟨M.data_le n d⟩
  (lpMeas ℂ ℂ (M.data n d) 2 (M.law (n + 1))).starProjection

lemma project_norm_le (M : Object I base) (n : ℕ) (d : DataKind I)
    (F : Lp ℂ 2 (M.law (n + 1))) : ‖M.project n d F‖ ≤ ‖F‖ :=
  norm_condExpL2_coe_le (M.data_le n d) F

namespace Extension
variable {M N : Object I base}

lemma project_norm_mono (e : Extension M N) (n : ℕ) (d : DataKind I)
    (F : Lp ℂ 2 (M.law (n + 1))) :
    ‖M.project n d F‖ ≤ ‖N.project n d (e.pull (n + 1) F)‖ := by
  let : Fact (M.data n d ≤ (inferInstance : MeasurableSpace (Arr I M.Y (n + 1)))) :=
    ⟨M.data_le n d⟩
  let : Fact (N.data n d ≤ (inferInstance : MeasurableSpace (Arr I N.Y (n + 1)))) :=
    ⟨N.data_le n d⟩
  exact Saturation.projection_norm_mono (e.pull (n + 1))
    (lpMeas ℂ ℂ (M.data n d) 2 (M.law (n + 1)))
    (lpMeas ℂ ℂ (N.data n d) 2 (N.law (n + 1))) (e.pull_data_mem n d) F

lemma project_eq_of_norm_le (e : Extension M N) (n : ℕ) (d : DataKind I)
    (F : Lp ℂ 2 (M.law (n + 1)))
    (h : ‖N.project n d (e.pull (n + 1) F)‖ ≤ ‖M.project n d F‖) :
    N.project n d (e.pull (n + 1) F) = e.pull (n + 1) (M.project n d F) := by
  let : Fact (M.data n d ≤ (inferInstance : MeasurableSpace (Arr I M.Y (n + 1)))) :=
    ⟨M.data_le n d⟩
  let : Fact (N.data n d ≤ (inferInstance : MeasurableSpace (Arr I N.Y (n + 1)))) :=
    ⟨N.data_le n d⟩
  exact Saturation.projection_eq_of_norm_eq (e.pull (n + 1))
    (lpMeas ℂ ℂ (M.data n d) 2 (M.law (n + 1)))
    (lpMeas ℂ ℂ (N.data n d) 2 (N.law (n + 1))) (e.pull_data_mem n d) F
    (le_antisymm h (e.project_norm_mono n d F))

end Extension

def IsSaturated (M : Object I base) : Prop :=
  ∀ (N : Object I base) (e : Extension M N) n d (F : Lp ℂ 2 (M.law (n + 1))),
    N.project n d (e.pull (n + 1) F) = e.pull (n + 1) (M.project n d F)

end ArrayObjects.Object

namespace KernelTests
variable {Ω U B : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]

omit [Nonempty B] in
lemma ae_eq_of_evaluations (ν : Measure U) [IsFiniteMeasure ν]
    (κ η : Kernel U B) [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : ∀ S : Set B, MeasurableSet S →
      (fun u => κ u S) =ᵐ[ν] (fun u => η u S)) : κ =ᵐ[ν] η := by
  apply Kernel.ae_eq_of_compProd_eq
  apply Measure.ext_prod
  intro A S hA hS
  rw [Measure.compProd_apply_prod hA hS, Measure.compProd_apply_prod hA hS]
  exact lintegral_congr_ae ((h S hS).filter_mono ae_restrict_le)

lemma hasCondDistrib_of_indicators (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → U) (O : Ω → B) (hE : Measurable E) (hO : Measurable O)
    (κ : Kernel U B) [IsMarkovKernel κ]
    (h : ∀ S : Set B, MeasurableSet S →
      μ⟦O ⁻¹' S | MeasurableSpace.comap E inferInstance⟧ =ᵐ[μ]
        fun ω => (κ (E ω)).real S) : HasCondDistrib O E κ μ := by
  have he : condDistrib O E μ =ᵐ[μ.map E] κ := by
    apply ae_eq_of_evaluations
    intro S hS
    apply (ae_map_iff hE.aemeasurable
      (measurableSet_eq_fun ((condDistrib O E μ).measurable_coe hS) (κ.measurable_coe hS))).mpr
    filter_upwards [condDistrib_ae_eq_condExp hE hO hS, h S hS] with ω h1 h2
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
      (h1.trans h2)
  exact ⟨(hE.prodMk hO).aemeasurable,
    (compProd_map_condDistrib hE.aemeasurable hO.aemeasurable).symm.trans (Measure.compProd_congr he)⟩

end KernelTests

namespace ArrayObjects.Object

section
open scoped ENNReal
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} {M N : Object I base}

lemma project_ae_eq_condExp (M : Object I base) (n : ℕ) (d : DataKind I)
    (F : Lp ℂ 2 (M.law (n + 1))) :
    (M.project n d F : Arr I M.Y (n + 1) → ℂ) =ᵐ[M.law (n + 1)]
      (M.law (n + 1))[F | M.data n d] := by
  have h := (Lp.memLp F).condExpL2_ae_eq_condExp (𝕜 := ℂ) (M.data_le n d)
  rw [Lp.toLp_coeFn] at h
  exact h

lemma IsSaturated.condExp (hM : M.IsSaturated) (e : Extension M N)
    (n : ℕ) (d : DataKind I) (f : Arr I M.Y (n + 1) → ℂ)
    (hf : MemLp f 2 (M.law (n + 1))) :
    (N.law (n + 1))[f ∘ amap e.state (n + 1) | N.data n d] =ᵐ[N.law (n + 1)]
      ((M.law (n + 1))[f | M.data n d] ∘ amap e.state (n + 1)) := by
  let F := hf.toLp f
  have hp := Lp.coeFn_compMeasurePreserving F (e.measurePreserving (n + 1))
  have hp' := (e.measurePreserving (n + 1)).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp
  have hout := (e.measurePreserving (n + 1)).quasiMeasurePreserving.ae_eq_comp
    ((M.project_ae_eq_condExp n d F).trans (condExp_congr_ae hf.coeFn_toLp))
  have hi := N.project_ae_eq_condExp n d (e.pull (n + 1) F)
  have hh := hM N e n d F
  have hl := Lp.coeFn_compMeasurePreserving (M.project n d F) (e.measurePreserving (n + 1))
  rw [hh] at hi
  exact (condExp_congr_ae (hp.trans hp')).symm.trans (hi.symm.trans (hl.trans hout))

lemma IsSaturated.indicator (hM : M.IsSaturated) (e : Extension M N)
    (n : ℕ) (d : DataKind I) (S : Set (Arr I M.Y (n + 1))) (hS : MeasurableSet S) :
    (N.law (n + 1))⟦amap e.state (n + 1) ⁻¹' S | N.data n d⟧ =ᵐ[N.law (n + 1)]
      ((M.law (n + 1))⟦S | M.data n d⟧ ∘ amap e.state (n + 1)) := by
  let f : Arr I M.Y (n + 1) → ℝ := S.indicator (fun _ => 1)
  have hf : Integrable f (M.law (n + 1)) := (integrable_const 1).indicator hS
  have hfeq : (fun y => (f y : ℂ)) = S.indicator (fun _ => (1 : ℂ)) := by
    funext y; by_cases hy : y ∈ S <;> simp [f, hy]
  have hg : MemLp (fun y => (f y : ℂ)) 2 (M.law (n + 1)) := by
    rw [hfeq]
    exact
      memLp_indicator_const (μ := M.law (n + 1)) 2 hS (1 : ℂ) (Or.inr (measure_ne_top _ _))
  have h := hM.condExp e n d (fun y => (f y : ℂ)) hg
  have hnew := Complex.ofRealCLM.comp_condExp_comm (m := N.data n d)
    ((e.measurePreserving (n + 1)).integrable_comp_of_integrable hf)
  have hold := (e.measurePreserving (n + 1)).quasiMeasurePreserving.ae_eq_comp
    (Complex.ofRealCLM.comp_condExp_comm (m := M.data n d) hf)
  have he := hnew.trans (h.trans hold.symm)
  have hpre : f ∘ amap e.state (n + 1) =
      (amap e.state (n + 1) ⁻¹' S).indicator (fun _ => (1 : ℝ)) := by
    funext y
    exact (Set.indicator_comp_right (s := S) (g := fun _ => (1 : ℝ))
      (amap e.state (n + 1))).symm
  filter_upwards [he] with y hy
  have hr := Complex.ofReal_injective hy
  change (N.law (n + 1))[f ∘ amap e.state (n + 1) | N.data n d] y = _ at hr
  rw [hpre] at hr
  exact hr

end

variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} {M N : Object I base}

lemma IsSaturated.hasCondDistrib (hM : M.IsSaturated) (e : Extension M N)
    (n : ℕ) (d : DataKind I) {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [StandardBorelSpace B] [Nonempty B]
    (E : Arr I M.Y (n + 1) → A) (E' : Arr I N.Y (n + 1) → C)
    (F : Arr I M.Y (n + 1) → B) (p : C → A)
    (hE : Measurable E) (hE' : Measurable E') (hF : Measurable F) (hp : Measurable p)
    (hdata : M.data n d = MeasurableSpace.comap E inferInstance)
    (hdata' : N.data n d = MeasurableSpace.comap E' inferInstance)
    (hobs : E ∘ amap e.state (n + 1) = p ∘ E') :
    HasCondDistrib (F ∘ amap e.state (n + 1)) E'
      ((condDistrib F E (M.law (n + 1))).comap p hp) (N.law (n + 1)) := by
  apply KernelTests.hasCondDistrib_of_indicators _ E' _ hE'
    (hF.comp (measurable_amap e.measurable_state _))
  intro S hS
  have hi := hM.indicator e n d (F ⁻¹' S) (hF hS)
  rw [hdata, hdata'] at hi
  have ho := (e.measurePreserving (n + 1)).quasiMeasurePreserving.ae_eq_comp
    (condDistrib_ae_eq_condExp (μ := M.law (n + 1)) hE hF hS)
  filter_upwards [hi, ho] with y h1 h2
  exact h1.trans (h2.symm.trans (by
    change ((condDistrib F E (M.law (n + 1))) (E (amap e.state (n + 1) y))).real S =
      ((condDistrib F E (M.law (n + 1))) (p (E' y))).real S
    exact congrArg (fun a => ((condDistrib F E (M.law (n + 1))) a).real S)
      (congrFun hobs y)))


end ArrayObjects.Object

namespace ArrayObjects
variable {I : Type u}

def roll {Y : Type u} [MeasurableSpace Y] (n : ℕ) :
    Arr I Y (n + 1) ≃ᵐ Arr I (I → Y) n where
  toFun y w c := y (Fin.cons c w)
  invFun y v := y (Fin.tail v) (v 0)
  left_inv y := by funext v; simp
  right_inv y := by funext w c; simp
  measurable_toFun := by exact Measurable.of_eval (fun _ =>
    Measurable.of_eval (fun _ => measurable_pi_apply _))
  measurable_invFun := by
    change Measurable (fun y : Arr I (I → Y) n => fun v : Fin (n + 1) → I => y (Fin.tail v) (v 0))
    exact Measurable.of_eval (fun _ =>
      (measurable_pi_apply _).comp (measurable_pi_apply _))

lemma roll_amap {Y Z : Type u} [MeasurableSpace Y] [MeasurableSpace Z]
    (f : Y → Z) (n : ℕ) :
    roll (I := I) n ∘ amap f (n + 1) = amap (fun y c => f (y c)) n ∘ roll n := rfl

lemma select_roll {Y : Type u} [MeasurableSpace Y] (n : ℕ) (a : I) :
    amap (Function.eval a) n ∘ roll (I := I) (Y := Y) n = plane n 0 a := by
  funext y w
  simp [amap, roll, plane, Fin.insertNth_zero']

lemma plane_roll {Y : Type u} [MeasurableSpace Y] (n : ℕ)
    (a : Fin (n + 1)) (i : I) :
    plane n a i ∘ roll (I := I) (Y := Y) (n + 1) =
      roll n ∘ plane (n + 1) a.succ i := by
  funext y w c
  exact congrArg y (Fin.insertNth_succ_cons a i c w).symm

lemma planes_roll {Y : Type u} [MeasurableSpace Y] (n : ℕ) (J : Finset I) :
    planes n J ∘ roll (I := I) (Y := Y) (n + 1) =
      (fun z j => roll n (z j)) ∘ planes (n + 1) J := by
  funext y j
  exact congrFun (plane_roll n (Fin.last n) (j : I)) y

namespace Object
variable [Fintype I]
variable {X : StandardSpace.{u}} {T : X ≃ᵐ X} {base : InitialLaws I X T}
variable (M : Object I base)
namespace Rolled

noncomputable abbrev State : StandardSpace.{u} where
  α := I → M.Y
  measurableSpace := inferInstance
  standardBorel := inferInstance
  nonempty := inferInstance

noncomputable abbrev Parameter (R : Finset I) : StandardSpace.{u} where
  α := (I → M.U) × (R → M.Y)
  measurableSpace := inferInstance
  standardBorel := inferInstance
  nonempty := inferInstance

def timeState : State M ≃ᵐ State M :=
  MeasurableEquiv.piCongrRight (fun _ : I => M.timeY)

def timeParameter (R : Finset I) : Parameter M R ≃ᵐ Parameter M R :=
  (MeasurableEquiv.piCongrRight (fun _ : I => M.timeU)).prodCongr
    (MeasurableEquiv.piCongrRight (fun _ : R => M.timeY))

def parameter (R : Finset I) (y : State M) : Parameter M R :=
  (fun c => M.par (y c), fun c => y c)

@[fun_prop] lemma measurable_parameter (R : Finset I) : Measurable (parameter M R) := by
  exact (Measurable.of_eval (fun c => M.measurable_par.comp (measurable_pi_apply c))).prodMk
    (Measurable.of_eval (fun c => measurable_pi_apply (c : I)))

lemma time_parameter (R : Finset I) :
    parameter M R ∘ timeState M = timeParameter M R ∘ parameter M R := by
  funext y
  apply Prod.ext
  · funext c; exact congrFun M.time_par (y c)
  · rfl

noncomputable def law (n : ℕ) : Measure (Arr I (State M) n) :=
  (M.law (n + 1)).map (roll n)
instance law_probability (n : ℕ) : IsProbabilityMeasure (law M n) :=
  (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (roll n).measurable.aemeasurable

lemma invariant (n : ℕ) : MeasurePreserving (amap (timeState M) n) (law M n) (law M n) := by
  refine ⟨measurable_amap (timeState M).measurable n, ?_⟩
  dsimp only [law]
  rw [Measure.map_map (measurable_amap (timeState M).measurable n) (roll n).measurable]
  change (M.law (n + 1)).map (roll n ∘ amap M.timeY (n + 1)) = _
  rw [← Measure.map_map (roll n).measurable (measurable_amap M.timeY.measurable _),
    (M.invariant (n + 1)).map_eq]

lemma select_law (n : ℕ) (a : I) :
    (law M n).map (amap (Function.eval a) n) = M.law n := by
  dsimp only [law]
  rw [Measure.map_map (measurable_amap (measurable_pi_apply a) n) (roll n).measurable,
    select_roll, M.consistent]

lemma over_base (n : ℕ) (a : I) :
    (law M n).map (amap (M.x ∘ Function.eval a) n) = base.law n := by
  rw [amap_comp, ← Measure.map_map (measurable_amap M.measurable_x n)
    (measurable_amap (measurable_pi_apply a) n), select_law, M.over_base]

lemma consistent (n : ℕ) (a : Fin (n + 1)) (i : I) :
    (law M (n + 1)).map (plane n a i) = law M n := by
  dsimp only [law]
  rw [Measure.map_map (measurable_plane _ _ _) (roll _).measurable, plane_roll,
    ← Measure.map_map (roll _).measurable (measurable_plane _ _ _), M.consistent]

lemma proper (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ) :
    (law M (n + 1)).map (planes n J) = Measure.pi (fun _ : J => law M n) := by
  have hm : Measurable (fun z : (j : J) → Arr I M.Y (n + 1) => fun j => roll n (z j)) :=
    Measurable.of_eval (fun j => (roll n).measurable.comp (measurable_pi_apply j))
  dsimp only [law]
  rw [Measure.map_map (measurable_planes _ _) (roll _).measurable, planes_roll,
    ← Measure.map_map hm (measurable_planes _ _), M.proper _ _ hJ]
  exact Measure.pi_map_pi (fun _ : J => (roll n).measurable.aemeasurable)

end Rolled
end Object
end ArrayObjects

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FiniteKernel

variable {ι X : Type*} {Y : ι → Type*}
  [Fintype ι] [MeasurableSpace X] [∀ i, MeasurableSpace (Y i)]

noncomputable def pi (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)] :
    Kernel X (∀ i, Y i) where
  toFun x := Measure.pi (fun i => κ i x)
  measurable' := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      generateFrom_pi.symm isPiSystem_pi
    rintro _ ⟨s, hs, rfl⟩
    simp only [Measure.pi_pi]
    exact Finset.measurable_prod _ (fun i _ => (κ i).measurable_coe (hs i (Set.mem_univ i)))

@[simp] theorem pi_apply (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)] (x : X) :
    pi κ x = Measure.pi (fun i => κ i x) := rfl

instance (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)] : IsMarkovKernel (pi κ) :=
  ⟨fun _ => inferInstanceAs (IsProbabilityMeasure (Measure.pi _))⟩

@[simp] theorem pi_box (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)]
    (x : X) (s : ∀ i, Set (Y i)) :
    pi κ x (Set.pi Set.univ s) = ∏ i, κ i x (s i) := Measure.pi_pi _ _

theorem map_pi {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)]
    (f : ∀ i, Y i → Z i) (hf : ∀ i, Measurable (f i)) :
    letI : ∀ i, IsMarkovKernel ((κ i).map (f i)) :=
      fun i => Kernel.IsMarkovKernel.map (κ i) (hf i)
    (pi κ).map (fun y i => f i (y i)) = pi (fun i => (κ i).map (f i)) := by
  ext x : 1
  rw [Kernel.map_apply _ (by fun_prop)]
  simp only [pi_apply, Kernel.map_apply _ (hf _)]
  exact Measure.pi_map_pi (fun i => (hf i).aemeasurable)

def zipEquiv (Y Z : ι → Type*) [∀ i, MeasurableSpace (Y i)]
    [∀ i, MeasurableSpace (Z i)] :
    ((∀ i, Y i) × (∀ i, Z i)) ≃ᵐ (∀ i, Y i × Z i) where
  toFun p i := (p.1 i, p.2 i)
  invFun p := (fun i => (p i).1, fun i => (p i).2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable (fun p : (∀ i, Y i) × (∀ i, Z i) => fun i => (p.1 i, p.2 i))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ∀ i, Y i × Z i => (fun i => (p i).1, fun i => (p i).2))
    fun_prop

theorem compProd_pi {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    (μ : ∀ i, Measure (Y i)) [∀ i, IsProbabilityMeasure (μ i)]
    (κ : ∀ i, Kernel (Y i) (Z i)) [∀ i, IsMarkovKernel (κ i)] :
    (Measure.pi μ ⊗ₘ pi (fun i => (κ i).comap (Function.eval i) (measurable_pi_apply i))).map
        (zipEquiv Y Z) = Measure.pi (fun i => μ i ⊗ₘ κ i) := by
  apply (Measure.pi_eq _).symm
  intro s hs
  rw [Measure.map_apply (zipEquiv Y Z).measurable (.univ_pi hs),
    Measure.compProd_apply ((zipEquiv Y Z).measurable (.univ_pi hs))]
  have hbox (y : ∀ i, Y i) :
      Prod.mk y ⁻¹' ((zipEquiv Y Z) ⁻¹' Set.pi Set.univ s) =
        Set.pi Set.univ (fun i => Prod.mk (y i) ⁻¹' s i) := rfl
  simp_rw [hbox, pi_box, Kernel.comap_apply]
  have hm (i : ι) : Measurable (fun y => κ i y (Prod.mk y ⁻¹' s i)) :=
    (κ i).measurable_kernel_prodMk_left (hs i)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _
    (iIndepFun_pi fun i => (hm i).aemeasurable) (fun i => (hm i).comp (measurable_pi_apply i))]
  congr 1
  funext i
  rw [(measurePreserving_eval μ i).lintegral_comp (hm i)]
  rw [← Measure.compProd_apply (hs i)]

theorem pi_compProd {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)]
    (η : ∀ i, Kernel (X × Y i) (Z i)) [∀ i, IsMarkovKernel (η i)] :
    (pi κ ⊗ₖ pi (fun i => (η i).comap (fun p : X × (∀ i, Y i) => (p.1, p.2 i))
      (by fun_prop))).map (zipEquiv Y Z) = pi (fun i => κ i ⊗ₖ η i) := by
  ext x : 1
  rw [Kernel.map_apply _ (zipEquiv Y Z).measurable,
    Kernel.compProd_apply_eq_compProd_sectR]
  have heq : Kernel.sectR
      (pi (fun i => (η i).comap (fun p : X × (∀ i, Y i) => (p.1, p.2 i))
        (by fun_prop))) x =
      pi (fun i => (Kernel.sectR (η i) x).comap (Function.eval i) (measurable_pi_apply i)) := by
    ext y : 1
    rfl
  rw [heq]
  simp only [pi_apply]
  rw [compProd_pi]
  simp only [Kernel.compProd_apply_eq_compProd_sectR]

end FiniteKernel

open MeasureTheory ProbabilityTheory

namespace ConditionalScreens

variable {Ω X Y Z : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {P : Measure Ω} [SFinite P]
  {x : Ω → X} {y : Ω → Y} {z : Ω → Z}
  {κ : Kernel X Y} [IsMarkovKernel κ]
  {η : Kernel (X × Y) Z} [IsMarkovKernel η]

omit [SFinite P] [IsMarkovKernel κ] [IsMarkovKernel η] in

theorem chain (hy : HasCondDistrib y x κ P)
    (hz : HasCondDistrib z (fun ω => (x ω, y ω)) η P) :
    HasCondDistrib (fun ω => (y ω, z ω)) x (κ ⊗ₖ η) P := by
  refine ⟨hy.aemeasurable_fst.prodMk
    (hy.aemeasurable_snd.prodMk hz.aemeasurable_snd), ?_⟩
  calc
    P.map (fun ω => (x ω, y ω, z ω)) =
        (P.map (fun ω => ((x ω, y ω), z ω))).map MeasurableEquiv.prodAssoc := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hz.aemeasurable]
      rfl
    _ = ((P.map x ⊗ₘ κ) ⊗ₘ η).map MeasurableEquiv.prodAssoc := by
      rw [hz.map_eq, hy.map_eq]
    _ = P.map x ⊗ₘ (κ ⊗ₖ η) := Measure.compProd_assoc'

theorem compProd_prodMkRight (κ : Kernel X Y) [IsSFiniteKernel κ]
    (l : Kernel X Z) [IsSFiniteKernel l] :
    κ ⊗ₖ l.prodMkRight Y = κ ×ₖ l := by
  ext a s hs
  rw [Kernel.compProd_apply hs, Kernel.prod_apply' _ _ _ hs]
  rfl

theorem screening (hy : HasCondDistrib y x κ P)
    (l : Kernel X Z) [IsMarkovKernel l]
    (hz : HasCondDistrib z (fun ω => (x ω, y ω)) (l.prodMkRight Y) P) :
    HasCondDistrib y (fun ω => (x ω, z ω)) (κ.prodMkRight Z) P := by
  have h := chain hy hz
  rw [compProd_prodMkRight] at h
  have h' := h.comp_left measurable_swap
  simp only [Function.comp_def, Prod.swap_prod_mk, Kernel.map_prod_swap] at h'
  rw [← compProd_prodMkRight] at h'
  exact h'.of_compProd

end ConditionalScreens

namespace ConditionalReveal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι Y : Type*} [DecidableEq ι] [MeasurableSpace Y]

def insertTuple (S : Finset ι) (i : ι) (p : (S → Y) × Y) : ↥(insert i S) → Y :=
  fun j => if h : j.val = i then p.2 else
    p.1 ⟨j.val, Finset.mem_of_mem_insert_of_ne j.property h⟩

theorem measurable_insertTuple (S : Finset ι) (i : ι) :
    Measurable (insertTuple (Y := Y) S i) := by
  apply Measurable.of_eval
  intro j
  unfold insertTuple
  split_ifs
  · exact measurable_snd
  · exact (measurable_pi_apply _).comp measurable_fst

theorem map_insertTuple (S : Finset ι) (i : ι) (hi : i ∉ S)
    (μ : ι → Measure Y) [∀ i, IsProbabilityMeasure (μ i)] :
    ((Measure.pi (fun j : S => μ j)).prod (μ i)).map (insertTuple S i) =
      Measure.pi (fun j : ↥(insert i S) => μ j) := by
  apply (Measure.pi_eq _).symm
  intro s hs
  rw [Measure.map_apply (measurable_insertTuple S i) (.univ_pi hs)]
  have hpre : insertTuple S i ⁻¹' Set.pi Set.univ s =
      (Set.pi Set.univ (fun j : S => s ⟨j, Finset.mem_insert_of_mem j.property⟩)) ×ˢ
        s ⟨i, Finset.mem_insert_self i S⟩ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
      Set.mem_prod]
    constructor
    · intro h
      constructor
      · intro j
        have hji : (j : ι) ≠ i := fun e => hi (e ▸ j.property)
        simpa only [insertTuple, dite_eq_right hji] using
          h ⟨j, Finset.mem_insert_of_mem j.property⟩
      · simpa [insertTuple] using h ⟨i, Finset.mem_insert_self i S⟩
    · rintro ⟨hp, hq⟩ j
      by_cases hji : (j : ι) = i
      · have ej : j = ⟨i, Finset.mem_insert_self i S⟩ := Subtype.ext hji
        rw [ej]
        simpa [insertTuple] using hq
      · simpa only [insertTuple, dite_eq_right hji] using
          hp ⟨j, Finset.mem_of_mem_insert_of_ne j.property hji⟩
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  classical
  let g : ι → ℝ≥0∞ := fun j => if h : j ∈ insert i S then μ j (s ⟨j, h⟩) else 1
  have hg (j : ↥(insert i S)) : g j = μ j (s j) := by simp only [g, dite_eq_left j.property]
  have hgS (j : S) : g j = μ j (s ⟨j, Finset.mem_insert_of_mem j.property⟩) := by
    exact dite_eq_left (Finset.mem_insert_of_mem j.property)
  simp_rw [← hg, ← hgS]
  rw [Finset.prod_coe_sort, Finset.prod_coe_sort, Finset.prod_insert hi]
  have hgi : g i = μ i (s ⟨i, Finset.mem_insert_self i S⟩) :=
    dite_eq_left (Finset.mem_insert_self i S)
  rw [hgi]
  exact mul_comm _ _

def splitTuple (S : Finset ι) (i : ι) (z : ↥(insert i S) → Y) : (S → Y) × Y :=
  (fun j => z ⟨j, Finset.mem_insert_of_mem j.property⟩,
    z ⟨i, Finset.mem_insert_self i S⟩)

theorem measurable_splitTuple (S : Finset ι) (i : ι) :
    Measurable (splitTuple (Y := Y) S i) := by
  exact (Measurable.of_eval (fun _ => measurable_pi_apply _)).prodMk
    (measurable_pi_apply _)

omit [MeasurableSpace Y] in
theorem split_insertTuple (S : Finset ι) (i : ι) (hi : i ∉ S) :
    splitTuple (Y := Y) S i ∘ insertTuple S i = id := by
  funext p
  apply Prod.ext
  · funext j
    have hji : (j : ι) ≠ i := fun h => hi (h ▸ j.property)
    exact dite_eq_right hji
  · simp [splitTuple, insertTuple]

theorem map_splitTuple (S : Finset ι) (i : ι) (hi : i ∉ S)
    (μ : ι → Measure Y) [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.pi (fun j : ↥(insert i S) => μ j)).map (splitTuple S i) =
      (Measure.pi (fun j : S => μ j)).prod (μ i) := by
  rw [← map_insertTuple S i hi μ,
    Measure.map_map (measurable_splitTuple S i) (measurable_insertTuple S i),
    split_insertTuple S i hi, Measure.map_id]

theorem probability_eq_of_subsingleton {Z : Type*} [MeasurableSpace Z] [Subsingleton Z]
    (μ ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ = ν := by
  ext s
  by_cases h : s.Nonempty
  · obtain ⟨z, hz⟩ := h
    have hs : s = Set.univ := Set.eq_univ_of_forall (fun w =>
      (Subsingleton.elim z w) ▸ hz)
    simp [hs]
  · simp [Set.not_nonempty_iff_eq_empty.mp h]

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

theorem finite_reveal (P : Measure Ω) [IsProbabilityMeasure P]
    (E : Ω → X) (hE : Measurable E) (y : ι → Ω → Y)
    (κ : ι → Kernel X Y) [∀ i, IsMarkovKernel (κ i)] (R : Finset ι)
    (h : ∀ (S : Finset ι), S ⊆ R → ∀ i ∈ R, i ∉ S →
      HasCondDistrib (y i) (fun ω => (E ω, fun j : S => y j ω))
        ((κ i).prodMkRight (S → Y)) P) :
    HasCondDistrib (fun ω => fun j : R => y j ω) E
      (FiniteKernel.pi (fun j : R => κ j)) P := by
  classical
  revert h
  induction R using Finset.induction_on with
  | empty =>
    intro _
    let z : (∅ : Finset ι) → Y := fun i => False.elim (Finset.notMem_empty _ i.property)
    have hk : FiniteKernel.pi (fun j : (∅ : Finset ι) => κ j) =
        Kernel.deterministic (fun _ : X => z) measurable_const := by
      ext x : 1
      exact probability_eq_of_subsingleton _ _
    have hy : (fun ω => fun j : (∅ : Finset ι) => y j ω) = fun _ => z := by
      funext ω j
      exact False.elim (Finset.notMem_empty _ j.property)
    rw [hy, hk]
    refine ⟨(hE.prodMk measurable_const).aemeasurable, ?_⟩
    rw [Measure.compProd_deterministic, Measure.map_map (by fun_prop) hE]
    rfl
  | @insert i S hi ih =>
    intro h
    have hS := ih (fun A hA j hj hnot => h A
      (hA.trans (Finset.subset_insert i S)) j (Finset.mem_insert_of_mem hj) hnot)
    have hi' := h S (Finset.subset_insert i S) i (Finset.mem_insert_self i S) hi
    have hh := ConditionalScreens.chain hS hi'
    rw [ConditionalScreens.compProd_prodMkRight] at hh
    have hout := hh.comp_left (measurable_insertTuple S i)
    have hk : ((FiniteKernel.pi (fun j : S => κ j)) ×ₖ κ i).map
        (insertTuple S i) = FiniteKernel.pi (fun j : ↥(insert i S) => κ j) := by
      ext x : 1
      rw [Kernel.map_apply _ (measurable_insertTuple S i), Kernel.prod_apply]
      exact map_insertTuple S i hi (fun j => κ j x)
    rw [hk] at hout
    have hy : insertTuple S i ∘ (fun ω => ((fun j : S => y j ω), y i ω)) =
        (fun ω => fun j : ↥(insert i S) => y j ω) := by
      funext ω j
      simp only [Function.comp_def, insertTuple]
      split_ifs with hji
      · rw [hji]
      · rfl
    rwa [hy] at hout

end ConditionalReveal
open MeasureTheory ProbabilityTheory

namespace ConditionalTransport
variable {Ω Ω' A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

theorem pullback {P : Measure Ω} {Q : Measure Ω'} {f : Ω → Ω'}
    {E : Ω' → A} {O : Ω' → B} {κ : Kernel A B}
    (hf : MeasurePreserving f P Q) (hE : Measurable E)
    (h : HasCondDistrib O E κ Q) : HasCondDistrib (O ∘ f) (E ∘ f) κ P := by
  have hh := h.comp hf.hasLaw
  have he : P.map (E ∘ f) = Q.map E := by
    rw [← Measure.map_map hE hf.measurable, hf.map_eq]
  change HasLaw (fun ω => (E (f ω), O (f ω))) (P.map (E ∘ f) ⊗ₘ κ) P
  rw [he]
  exact hh

theorem recondition [StandardBorelSpace B] [Nonempty B]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Ω → A} {D : Ω → C} {O : Ω → B}
    {κ : Kernel A B} [IsMarkovKernel κ] {η : Kernel C B} [IsMarkovKernel η]
    (hE : Measurable E) (hD : Measurable D) (hO : Measurable O)
    (h : HasCondDistrib O E κ P)
    (hfield : MeasurableSpace.comap E inferInstance = MeasurableSpace.comap D inferInstance)
    (hk : (fun ω => κ (E ω)) =ᵐ[P] fun ω => η (D ω)) : HasCondDistrib O D η P := by
  apply KernelTests.hasCondDistrib_of_indicators _ D O hD hO
  intro S hS
  have hc := ae_of_ae_map hE.aemeasurable
    (condDistrib_ae_eq_of_measure_eq_compProd hE.aemeasurable hO.aemeasurable h.map_eq)
  have hi := condDistrib_ae_eq_condExp (μ := P) hE hO hS
  rw [hfield] at hi
  filter_upwards [hc, hi, hk] with ω h1 h2 h3
  exact h2.symm.trans (by rw [h1, h3])

omit [MeasurableSpace Ω] in

theorem comap_le_of_factor {f : Ω → A} {g : Ω → C} {p : C → A}
    (hp : Measurable p) (h : f = p ∘ g) :
    MeasurableSpace.comap f inferInstance ≤ MeasurableSpace.comap g inferInstance := by
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hp.comap_le

theorem of_indep {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Ω → A} {O : Ω → B} (hE : Measurable E) (hO : Measurable O)
    (h : IndepFun E O P) : HasCondDistrib O E (Kernel.const A (P.map O)) P := by
  refine ⟨(hE.prodMk hO).aemeasurable, ?_⟩
  rw [Measure.compProd_const]
  exact h.map_prod_eq_prod_map_map hE.aemeasurable hO.aemeasurable

theorem indep_of_const {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Ω → A} {O : Ω → B} (hE : Measurable E) (hO : Measurable O)
    (Q : Measure B) [IsProbabilityMeasure Q]
    (h : HasCondDistrib O E (Kernel.const A Q) P) : IndepFun E O P := by
  apply (indepFun_iff_map_prod_eq_prod_map_map hE.aemeasurable hO.aemeasurable).mpr
  rw [h.map_eq, h.hasLaw_of_const.map_eq, Measure.compProd_const]

end ConditionalTransport

namespace ConditionalReveal
variable {ι Ω X Y Z : Type*} [DecidableEq ι] [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem independent_image (P : Measure Ω) [IsProbabilityMeasure P]
    (E : Ω → X) (hE : Measurable E) (y : ι → Ω → Y) (hy : ∀ i, Measurable (y i))
    (κ : ι → Kernel X Y) [∀ i, IsMarkovKernel (κ i)]
    (R : Finset ι) (i : ι) (hi : i ∉ R) (f : Y → Z) (hf : Measurable f)
    (Q : Measure Z) [IsProbabilityMeasure Q]
    (h : HasCondDistrib (fun ω => fun j : ↥(insert i R) => y j ω) E
      (FiniteKernel.pi (fun j : ↥(insert i R) => κ j)) P)
    (hk : (fun x => (κ i x).map f) =ᵐ[P.map E] fun _ => Q) :
    IndepFun (fun ω => (E ω, fun j : R => y j ω)) (f ∘ y i) P := by
  have hs := h.comp_left (measurable_splitTuple R i)
  have hsk : (FiniteKernel.pi (fun j : ↥(insert i R) => κ j)).map (splitTuple R i) =
      (FiniteKernel.pi (fun j : R => κ j)) ×ₖ κ i := by
    ext x : 1
    rw [Kernel.map_apply _ (measurable_splitTuple R i), Kernel.prod_apply]
    exact map_splitTuple R i hi (fun j => κ j x)
  rw [hsk] at hs
  change HasCondDistrib (fun ω => ((fun j : R => y j ω), y i ω)) E
    ((FiniteKernel.pi (fun j : R => κ j)) ×ₖ κ i) P at hs
  have hx := hs.comp_left (measurable_id.prodMap hf)
  rw [← Kernel.map_prod_map _ _ measurable_id hf, Kernel.map_id] at hx
  have hprod : ((FiniteKernel.pi (fun j : R => κ j)) ×ₖ (κ i).map f) =ᵐ[P.map E]
      ((FiniteKernel.pi (fun j : R => κ j)) ×ₖ Kernel.const X Q) := by
    filter_upwards [hk] with x hx
    rw [Kernel.prod_apply, Kernel.prod_apply, Kernel.map_apply _ hf, hx]
    rfl
  have hout : HasCondDistrib (fun ω => ((fun j : R => y j ω), f (y i ω))) E
      ((FiniteKernel.pi (fun j : R => κ j)) ×ₖ Kernel.const X Q) P :=
    ⟨hx.aemeasurable, hx.map_eq.trans (Measure.compProd_congr hprod)⟩
  rw [← ConditionalScreens.compProd_prodMkRight] at hout
  have hout' := hout.of_compProd
  have hc : (Kernel.const X Q).prodMkRight (R → Y) = Kernel.const (X × (R → Y)) Q := rfl
  rw [hc] at hout'
  exact ConditionalTransport.indep_of_const
    (hE.prodMk (Measurable.of_eval (fun j => hy j))) (hf.comp (hy i)) Q hout'

end ConditionalReveal

namespace ConditionalTransport
variable {Ω Ω' A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [MeasurableSpace B]
lemma map_indep {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → Ω'} {E : Ω' → A} {O : Ω' → B}
    (hf : Measurable f) (hE : Measurable E) (hO : Measurable O)
    (h : IndepFun (E ∘ f) (O ∘ f) P) : IndepFun E O (P.map f) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map hE.aemeasurable hO.aemeasurable).mpr
  rw [Measure.map_map (hE.prodMk hO) hf, Measure.map_map hE hf, Measure.map_map hO hf]
  exact h.map_prod_eq_prod_map_map (hE.comp hf).aemeasurable (hO.comp hf).aemeasurable
end ConditionalTransport

namespace ArrayObjects.Object
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

noncomputable def ownKernel (n : ℕ) : Kernel (Arr I M.U n) (Arr I M.Y n) :=
  condDistrib id (amap M.par n) (M.law n)
instance ownKernel_markov (n : ℕ) : IsMarkovKernel (ownKernel M n) := by
  unfold ownKernel
  infer_instance

lemma ownKernel_conditional (n : ℕ) :
    HasCondDistrib id (amap M.par n) (M.ownKernel n) (M.law n) :=
  ⟨((measurable_amap M.measurable_par n).prodMk measurable_id).aemeasurable,
    (compProd_map_condDistrib (measurable_amap M.measurable_par n).aemeasurable measurable_id.aemeasurable).symm⟩

lemma planes_conditional (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ) :
    HasCondDistrib (planes n J) (amap M.par (n + 1))
      (FiniteKernel.pi (fun j : J => (M.ownKernel n).comap
        (plane n (Fin.last n) j) (measurable_plane _ _ _))) (M.law (n + 1)) := by
  refine ⟨((measurable_amap M.measurable_par _).prodMk (measurable_planes _ _)).aemeasurable, ?_⟩
  exact (compProd_map_condDistrib (measurable_amap M.measurable_par _).aemeasurable (measurable_planes n J).aemeasurable).symm.trans
    (Measure.compProd_congr (M.conditional n J hJ))

lemma ownKernel_zero_image :
    (fun p => (M.ownKernel 0 p).map (M.x ∘ zeroEquiv I M.Y)) =ᵐ[
      (M.law 0).map (amap M.par 0)] fun _ => M.localLaw.map M.x := by
  have h := ConditionalTransport.of_indep (P := M.localLaw) M.measurable_par M.measurable_x M.local_independent.symm
  have h0 := ConditionalTransport.pullback
    (show MeasurePreserving (zeroEquiv I M.Y) (M.law 0) M.localLaw from
      ⟨(zeroEquiv I M.Y).measurable, rfl⟩) M.measurable_par h
  have h1 := h0.measurableEquiv_comp_right (zeroEquiv I M.U).symm
  have hpar : (zeroEquiv I M.U).symm ∘ M.par ∘ zeroEquiv I M.Y = amap M.par 0 := by
    funext y w
    exact congrArg (fun v => M.par (y v)) (Subsingleton.elim _ _)
  rw [hpar] at h1
  have h2 := (M.ownKernel_conditional 0).comp_left
    (M.measurable_x.comp (zeroEquiv I M.Y).measurable)
  have hk := Kernel.ae_eq_of_compProd_eq (h2.map_eq.symm.trans h1.map_eq)
  filter_upwards [hk] with p hp
  rw [← Kernel.map_apply _ (M.measurable_x.comp (zeroEquiv I M.Y).measurable)]
  exact hp

namespace Rolled
lemma local_independent [DecidableEq I] (R : Finset I) (a : I)
    (ha : a ∉ R) (hR : insert a R ≠ Finset.univ) :
    IndepFun (M.x ∘ Function.eval a) (parameter M R)
      ((law M 0).map (zeroEquiv I (State M))) := by
  let E := amap (I := I) M.par 1
  let y := fun c : I => plane 0 (Fin.last 0) c (Y := M.Y)
  let κ := fun c : I => (M.ownKernel 0).comap
    (plane 0 (Fin.last 0) c) (measurable_plane _ _ _)
  have hE : Measurable E := measurable_amap M.measurable_par 1
  have hfield : MeasurePreserving (plane 0 (Fin.last 0) a)
      ((M.law 1).map E) ((M.law 0).map (amap M.par 0)) := by
    refine ⟨measurable_plane _ _ _, ?_⟩
    rw [Measure.map_map (measurable_plane _ _ _) hE, plane_amap,
      ← Measure.map_map (measurable_amap M.measurable_par 0) (measurable_plane _ _ _),
      M.consistent]
  let Q := M.localLaw.map M.x
  have : IsProbabilityMeasure Q := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) M.measurable_x.aemeasurable
  have hk := hfield.quasiMeasurePreserving.ae_eq_comp M.ownKernel_zero_image
  have h := ConditionalReveal.independent_image (M.law 1) E hE y
    (fun c => measurable_plane 0 (Fin.last 0) c) κ R a ha
    (M.x ∘ zeroEquiv I M.Y) (M.measurable_x.comp (zeroEquiv I M.Y).measurable) Q
    (M.planes_conditional 0 (insert a R) hR) hk
  let e : Arr I M.U 1 × (R → Arr I M.Y 0) → Parameter M R := fun p =>
    (fun c => p.1 (Fin.cons c Fin.elim0), fun c => zeroEquiv I M.Y (p.2 c))
  have he : Measurable e := by
    exact (Measurable.of_eval (fun _ => (measurable_pi_apply _).comp measurable_fst)).prodMk
      (Measurable.of_eval (fun _ => (zeroEquiv I M.Y).measurable.comp
        ((measurable_pi_apply _).comp measurable_snd)))
  have hh := (h.comp he measurable_id).symm
  rw [law, Measure.map_map (zeroEquiv I (State M)).measurable (roll 0).measurable]
  apply ConditionalTransport.map_indep ((zeroEquiv I (State M)).measurable.comp (roll 0).measurable)
    (M.measurable_x.comp (measurable_pi_apply a)) (measurable_parameter M R)
  convert hh using 1 <;> funext z <;> simp [E, e, y, parameter, roll, zeroEquiv, plane,
    amap, Function.comp_def, Fin.insertNth_zero']

end Rolled
end ArrayObjects.Object

namespace ArrayObjects
variable {I : Type u}

lemma cons_snoc {n : ℕ} (c j : I) (v : Fin n → I) :
    (Fin.cons c (Fin.snoc (α := fun _ => I) v j) : Fin (n + 2) → I) =
      Fin.snoc (α := fun _ => I) (Fin.cons c v) j := by
  simpa only [show (Fin.last n).succ = Fin.last (n + 1) from rfl,
    Fin.insertNth_last'] using (Fin.insertNth_succ_cons (Fin.last n) j c v).symm

namespace Object.Rolled
variable [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

noncomputable abbrev Outside (j : I) : Finset I := by
  classical
  exact Finset.univ.erase j

variable [DecidableEq I]

abbrev RawData (n : ℕ) (j : I) :=
  Arr I M.U (n + 2) × (Outside j → Arr I M.Y (n + 1))

abbrev RevealData (R : Finset I) (n : ℕ) (j : I) :=
  RawData M n j × (R → Arr I M.Y n)

abbrev RollData (R : Finset I) (n : ℕ) (j : I) :=
  Arr I (Parameter M R) (n + 1) × (Outside j → Arr I (State M) n)

def rawData (n : ℕ) (j : I) (y : Arr I M.Y (n + 2)) : RawData M n j :=
  (amap M.par (n + 2) y, planes (n + 1) (Outside j) y)

def missingRow (n : ℕ) (j c : I) (y : Arr I M.Y (n + 2)) : Arr I M.Y n :=
  plane n (Fin.last n) j (plane (n + 1) 0 c y)

def revealData (R : Finset I) (n : ℕ) (j : I) (y : Arr I M.Y (n + 2)) :
    RevealData M R n j := (rawData M n j y, fun c => missingRow M n j c y)

def rollData (R : Finset I) (n : ℕ) (j : I) (y : Arr I (State M) (n + 1)) :
    RollData M R n j := (amap (parameter M R) (n + 1) y, planes n (Outside j) y)

omit [DecidableEq I] in
@[fun_prop] lemma measurable_rawData (n : ℕ) (j : I) : Measurable (rawData M n j) :=
  (measurable_amap M.measurable_par _).prodMk (measurable_planes _ _)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_missingRow (n : ℕ) (j c : I) :
    Measurable (missingRow M n j c) :=
  (measurable_plane _ _ _).comp (measurable_plane _ _ _)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_revealData (R : Finset I) (n : ℕ) (j : I) :
    Measurable (revealData M R n j) :=
  (measurable_rawData M n j).prodMk
    (Measurable.of_eval (fun c => measurable_missingRow M n j c))
omit [DecidableEq I] in
@[fun_prop] lemma measurable_rollData (R : Finset I) (n : ℕ) (j : I) :
    Measurable (rollData M R n j) :=
  (measurable_amap (measurable_parameter M R) _).prodMk (measurable_planes _ _)

def rollToReveal (R : Finset I) (n : ℕ) (j : I) (p : RollData M R n j) :
    RevealData M R n j :=
  ((fun v => (p.1 (Fin.tail v)).1 (v 0), fun k => (roll n).symm (p.2 k)),
    fun c v => (p.1 (Fin.snoc v j)).2 c)

omit [DecidableEq I] in
@[fun_prop] lemma measurable_rollToReveal (R : Finset I) (n : ℕ) (j : I) :
    Measurable (rollToReveal M R n j) := by
  unfold rollToReveal
  fun_prop

def revealToRoll (R : Finset I) (n : ℕ) (j : I) (p : RevealData M R n j) :
    RollData M R n j :=
  (fun w => (fun c => p.1.1 (Fin.cons c w), fun c =>
    if h : w (Fin.last n) = j then p.2 c (Fin.init w) else
      p.1.2 ⟨w (Fin.last n), by simp [Outside, h]⟩ (Fin.cons c (Fin.init w))),
    fun k => roll n (p.1.2 k))

@[fun_prop] lemma measurable_revealToRoll (R : Finset I) (n : ℕ) (j : I) :
    Measurable (revealToRoll M R n j) := by
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro w
    apply Measurable.prodMk
    · fun_prop
    · apply Measurable.of_eval
      intro c
      split_ifs <;> fun_prop
  · exact Measurable.of_eval (fun k => (roll n).measurable.comp
      ((measurable_pi_apply k).comp (measurable_snd.comp measurable_fst)))

omit [DecidableEq I] in
lemma rollToReveal_observation (R : Finset I) (n : ℕ) (j : I) :
    rollToReveal M R n j ∘ rollData M R n j ∘ roll (n + 1) = revealData M R n j := by
  funext y
  apply Prod.ext
  · apply Prod.ext
    · funext v
      simp [rollToReveal, rollData, revealData, rawData, amap, parameter, roll]
    · funext k
      change (roll n).symm ((planes n (Outside j) ∘ roll (n + 1)) y k) = _
      rw [planes_roll]
      exact (roll n).symm_apply_apply _
  · funext c v
    simp [rollToReveal, rollData, revealData, missingRow, amap, parameter, roll,
      plane, Fin.insertNth_zero', Fin.insertNth_last']

lemma revealToRoll_observation (R : Finset I) (n : ℕ) (j : I) :
    revealToRoll M R n j ∘ revealData M R n j = rollData M R n j ∘ roll (n + 1) := by
  funext y
  apply Prod.ext
  · funext w
    apply Prod.ext
    · rfl
    · funext c
      change (if h : w (Fin.last n) = j then missingRow M n j c y (Fin.init w) else
        planes (n + 1) (Outside j) y
          ⟨w (Fin.last n), by simp [Outside, h]⟩ (Fin.cons c (Fin.init w))) = _
      split_ifs with h
      · simp only [missingRow, plane, Fin.insertNth_zero', Fin.insertNth_last']
        rw [← h, Fin.snoc_init_self]
        rfl
      · simp only [planes, plane, Fin.insertNth_last']
        rw [← cons_snoc, Fin.snoc_init_self]
        rfl
  · funext k
    exact congrFun (congrFun (planes_roll n (Outside j)) y) k |>.symm

lemma comap_reveal_eq_rollData (R : Finset I) (n : ℕ) (j : I) :
    MeasurableSpace.comap (revealData M R n j) inferInstance =
      MeasurableSpace.comap (rollData M R n j ∘ roll (n + 1)) inferInstance := by
  apply le_antisymm
  · rw [← rollToReveal_observation M R n j, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_rollToReveal M R n j).comap_le
  · rw [← revealToRoll_observation M R n j, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_revealToRoll M R n j).comap_le

abbrev OldData (n : ℕ) (j : I) :=
  Arr I M.U (n + 1) × (Outside j → Arr I M.Y n)

def oldData (n : ℕ) (j : I) (y : Arr I M.Y (n + 1)) : OldData M n j :=
  (amap M.par (n + 1) y, planes n (Outside j) y)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_oldData (n : ℕ) (j : I) : Measurable (oldData M n j) :=
  (measurable_amap M.measurable_par _).prodMk (measurable_planes _ _)

def rowData (n : ℕ) (j c : I) (p : RawData M n j) : OldData M n j :=
  (plane (n + 1) 0 c p.1, fun k => plane n 0 c (p.2 k))
omit [DecidableEq I] in
@[fun_prop] lemma measurable_rowData (n : ℕ) (j c : I) : Measurable (rowData M n j c) :=
  ((measurable_plane _ _ _).comp measurable_fst).prodMk
    (Measurable.of_eval (fun _ => (measurable_plane _ _ _).comp
      ((measurable_pi_apply _).comp measurable_snd)))

def selectData (R : Finset I) (n : ℕ) (j c : I) (p : RollData M R n j) : OldData M n j :=
  (amap (fun q => q.1 c) (n + 1) p.1, fun k => amap (Function.eval c) n (p.2 k))
omit [DecidableEq I] in
@[fun_prop] lemma measurable_selectData (R : Finset I) (n : ℕ) (j c : I) :
    Measurable (selectData M R n j c) := by
  unfold selectData
  fun_prop

omit [DecidableEq I] in
lemma selectData_observation (R : Finset I) (n : ℕ) (j c : I) :
    selectData M R n j c ∘ rollData M R n j ∘ roll (n + 1) =
      rowData M n j c ∘ rawData M n j := by
  funext y
  apply Prod.ext
  · funext v
    simp [selectData, rollData, rowData, rawData, amap, parameter, roll, plane,
      Fin.insertNth_zero']
  · funext k v
    simp [selectData, rollData, rowData, rawData, amap, roll, plane, planes,
      Fin.insertNth_zero', Fin.insertNth_last', cons_snoc]

end Object.Rolled
end ArrayObjects
namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def IsConditional (R : Finset I) : Prop :=
  ∀ n (J : Finset I), J ≠ Finset.univ →
    condDistrib (planes n J) (amap (parameter M R) (n + 1)) (law M (n + 1))
      =ᵐ[(law M (n + 1)).map (amap (parameter M R) (n + 1))]
    fun p => Measure.pi (fun j : J =>
      condDistrib (id : Arr I (State M) n → Arr I (State M) n)
        (amap (parameter M R) n) (law M n) (plane n (Fin.last n) j p))

noncomputable def makeObject (R : Finset I) (hc : IsConditional M R)
    (a : I) (ha : a ∉ R) (hR : insert a R ≠ Finset.univ) : Object I base where
  Y := State M
  U := Parameter M R
  timeY := timeState M
  timeU := timeParameter M R
  x := M.x ∘ Function.eval a
  par := parameter M R
  measurable_x := M.measurable_x.comp (measurable_pi_apply a)
  measurable_par := measurable_parameter M R
  time_x := by funext y; exact congrFun M.time_x (y a)
  time_par := time_parameter M R
  law := law M
  probability := law_probability M
  invariant := invariant M
  over_base := fun n => over_base M n a
  consistent := consistent M
  proper := proper M
  conditional := hc
  local_independent := local_independent M R a ha hR

noncomputable def extension (R : Finset I) (hc : IsConditional M R)
    (a : I) (ha : a ∉ R) (hR : insert a R ≠ Finset.univ) :
    Extension M (makeObject M R hc a ha hR) where
  state := Function.eval a
  parameter := fun p => p.1 a
  measurable_state := measurable_pi_apply a
  measurable_parameter := (measurable_pi_apply a).comp measurable_fst
  time_state := rfl
  time_parameter := rfl
  state_x := rfl
  state_par := rfl
  laws n := select_law M n a

noncomputable def rowKernel (n : ℕ) (j c : I) : Kernel (RawData M n j) (Arr I M.Y n) :=
  (condDistrib (plane n (Fin.last n) j) (oldData M n j) (M.law (n + 1))).comap
    (rowData M n j c) (measurable_rowData M n j c)
instance rowKernel_markov (n : ℕ) (j c : I) : IsMarkovKernel (rowKernel M n j c) := by
  unfold rowKernel
  infer_instance

lemma parent_reveal (hM : M.IsSaturated) (R : Finset I) (hc : IsConditional M R)
    (c : I) (hcR : c ∉ R) (hR : insert c R ≠ Finset.univ) (n : ℕ) (j : I) :
    HasCondDistrib (missingRow M n j c) (revealData M R n j)
      ((rowKernel M n j c).prodMkRight (R → Arr I M.Y n)) (M.law (n + 2)) := by
  let N := makeObject M R hc c hcR hR
  let ext := extension M R hc c hcR hR
  have hs := hM.hasCondDistrib ext n (.enlarged j)
    (oldData M n j) (rollData M R n j) (plane n (Fin.last n) j)
    (selectData M R n j c) (measurable_oldData M n j) (measurable_rollData M R n j)
    (measurable_plane _ _ _) (measurable_selectData M R n j c)
    (by
      unfold Object.data oldData Outside
      exact (MeasurableSpace.comap_prodMk (mβ := inferInstance) (mγ := inferInstance)
        (amap M.par (n + 1)) (planes n (Outside j))).symm)
    (by
      unfold Object.data rollData Outside makeObject
      exact (MeasurableSpace.comap_prodMk (mβ := inferInstance) (mγ := inferInstance)
        (amap (parameter M R) (n + 1)) (planes n (Outside j))).symm) rfl
  have hp := ConditionalTransport.pullback
    (show MeasurePreserving (roll (Y := M.Y) (n + 1)) (M.law (n + 2)) (N.law (n + 1)) from
      ⟨(roll (n + 1)).measurable, rfl⟩) (measurable_rollData M R n j) hs
  have hobs : (plane n (Fin.last n) j ∘ amap (Function.eval c) (n + 1)) ∘ roll (n + 1) =
      missingRow M n j c := by
    rw [Function.comp_assoc, select_roll]
    rfl
  change HasCondDistrib ((plane n (Fin.last n) j ∘ amap (Function.eval c) (n + 1)) ∘
      roll (n + 1)) (rollData M R n j ∘ roll (n + 1)) _ (M.law _) at hp
  rw [hobs] at hp
  apply ConditionalTransport.recondition
    ((measurable_rollData M R n j).comp (roll (n + 1)).measurable)
    (measurable_revealData M R n j) (measurable_missingRow M n j c) hp
    (comap_reveal_eq_rollData M R n j).symm
  apply Filter.Eventually.of_forall
  intro y
  change (condDistrib (plane n (Fin.last n) j) (oldData M n j) (M.law (n + 1)))
      ((selectData M R n j c ∘ rollData M R n j ∘ roll (n + 1)) y) =
    (condDistrib (plane n (Fin.last n) j) (oldData M n j) (M.law (n + 1)))
      ((rowData M n j c ∘ rawData M n j) y)
  rw [selectData_observation]


lemma parent_joint (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I)
    (ih : ∀ S : Finset I, S ⊂ R → IsConditional M S) (n : ℕ) (j : I) :
    HasCondDistrib (fun y => fun c : R => missingRow M n j c y) (rawData M n j)
      (FiniteKernel.pi (fun c : R => rowKernel M n j c)) (M.law (n + 2)) := by
  apply ConditionalReveal.finite_reveal _ _ (measurable_rawData M n j)
  intro S hS c hc hcS
  have hstrict : S ⊂ R := (Finset.ssubset_iff_subset_ne).mpr ⟨hS, by
    intro he; subst S; exact hcS hc⟩
  have hproper : insert c S ≠ Finset.univ := by
    intro he
    have hle : (insert c S).card ≤ R.card := Finset.card_le_card
      (Finset.insert_subset hc hS)
    rw [he, Finset.card_univ] at hle
    omega
  exact parent_reveal M hM S (ih S hstrict) c hcS hproper n j

end ArrayObjects.Object.Rolled

namespace LocalConditioning
open FiniteKernel ConditionalScreens

variable {Ω X Y A : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace A]

noncomputable def observe (κ : Kernel X Y) (a : X × Y → A) (ha : Measurable a) :
    Kernel X (A × Y) :=
  (κ ⊗ₖ Kernel.deterministic a ha).map Prod.swap

instance (κ : Kernel X Y) [IsMarkovKernel κ] (a : X × Y → A) (ha : Measurable a) :
    IsMarkovKernel (observe κ a ha) :=
  Kernel.IsMarkovKernel.map _ measurable_swap

theorem observe_apply (κ : Kernel X Y) [IsMarkovKernel κ]
    (a : X × Y → A) (ha : Measurable a) (x : X) :
    observe κ a ha x = (κ x).map (fun y => (a (x, y), y)) := by
  rw [observe, Kernel.map_apply _ measurable_swap,
    Kernel.compProd_apply_eq_compProd_sectR]
  have heq : Kernel.sectR (Kernel.deterministic a ha) x =
      Kernel.deterministic (fun y => a (x, y)) (ha.comp measurable_prodMk_left) := by
    ext y : 1
    rfl
  rw [heq, Measure.compProd_deterministic]
  rw [Measure.map_map measurable_swap (by fun_prop)]
  rfl

theorem deterministic {P : Measure Ω} [SFinite P] {x : Ω → X}
    (hx : AEMeasurable x P) (a : X → A) (ha : Measurable a) :
    HasCondDistrib (a ∘ x) x (Kernel.deterministic a ha) P := by
  refine ⟨hx.prodMk (ha.comp_aemeasurable hx), ?_⟩
  rw [Measure.compProd_deterministic,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) hx]
  rfl

theorem hasCondDistrib_observe {P : Measure Ω} [SFinite P] {x : Ω → X} {y : Ω → Y}
    {κ : Kernel X Y} [IsMarkovKernel κ] (h : HasCondDistrib y x κ P)
    (a : X × Y → A) (ha : Measurable a) :
    HasCondDistrib (fun ω => (a (x ω, y ω), y ω)) x (observe κ a ha) P := by
  have h' := chain h (deterministic h.aemeasurable a ha)
  exact h'.comp_left measurable_swap

variable {ι : Type*} [Fintype ι]
  {O C : ι → Type*} [∀ i, MeasurableSpace (O i)] [∀ i, MeasurableSpace (C i)]

theorem observe_pi (κ : ∀ i, Kernel X (O i)) [∀ i, IsMarkovKernel (κ i)]
    (a : ∀ i, X × O i → C i) (ha : ∀ i, Measurable (a i)) :
    observe (pi κ) (fun p : X × (∀ i, O i) => fun i => a i (p.1, p.2 i)) (by fun_prop) =
      (pi (fun i => observe (κ i) (a i) (ha i))).map (zipEquiv C O).symm := by
  ext x : 1
  rw [observe_apply, Kernel.map_apply _ (zipEquiv C O).symm.measurable]
  simp only [pi_apply, observe_apply]
  rw [← Measure.pi_map_pi (fun i => (show Measurable (fun o => (a i (x, o), o)) by
    fun_prop).aemeasurable), Measure.map_map (zipEquiv C O).symm.measurable (by fun_prop)]
  rfl

theorem compProd_comap {E : Type*} [MeasurableSpace E]
    (κ : Kernel E A) [IsMarkovKernel κ] (η : Kernel (E × A) Y) [IsMarkovKernel η]
    (e : X → E) (he : Measurable e) :
    (κ ⊗ₖ η).comap e he = κ.comap e he ⊗ₖ
      η.comap (fun p : X × A => (e p.1, p.2)) (by fun_prop) := by
  ext x s hs
  simp only [Kernel.comap_apply, Kernel.compProd_apply hs]

theorem observe_comap {E : Type*} [MeasurableSpace E]
    (κ : Kernel E Y) [IsMarkovKernel κ] (a : E × Y → A) (ha : Measurable a)
    (e : X → E) (he : Measurable e) :
    observe (κ.comap e he) (fun p : X × Y => a (e p.1, p.2)) (by fun_prop) =
      (observe κ a ha).comap e he := by
  ext x : 1
  simp only [observe_apply, Kernel.comap_apply]

theorem disintegrate_pi (κ : ∀ i, Kernel X (C i)) [∀ i, IsMarkovKernel (κ i)]
    (η : ∀ i, Kernel (X × C i) (O i)) [∀ i, IsMarkovKernel (η i)] :
    (pi (fun i => κ i ⊗ₖ η i)).map (zipEquiv C O).symm =
      pi κ ⊗ₖ pi (fun i => (η i).comap
        (fun p : X × (∀ i, C i) => (p.1, p.2 i)) (by fun_prop)) := by
  rw [← pi_compProd, ← Kernel.map_comp_right _ (zipEquiv C O).measurable
    (zipEquiv C O).symm.measurable]
  convert Kernel.map_id _ using 1
  ext x i
  rfl

theorem hasCondDistrib_update {P : Measure Ω} [SFinite P]
    {x : Ω → X} {o : Ω → ∀ i, O i}
    (κ : ∀ i, Kernel X (O i)) [∀ i, IsMarkovKernel (κ i)]
    (a : ∀ i, X × O i → C i) (ha : ∀ i, Measurable (a i))
    (M : ∀ i, Kernel X (C i)) [∀ i, IsMarkovKernel (M i)]
    (Q : ∀ i, Kernel (X × C i) (O i)) [∀ i, IsMarkovKernel (Q i)]
    (hd : ∀ i, observe (κ i) (a i) (ha i) = M i ⊗ₖ Q i)
    (ho : HasCondDistrib o x (pi κ) P) :
    HasCondDistrib o (fun ω => (x ω, fun i => a i (x ω, o ω i)))
      (pi (fun i => (Q i).comap
        (fun p : X × (∀ i, C i) => (p.1, p.2 i)) (by fun_prop))) P := by
  have h := hasCondDistrib_observe ho
    (fun p : X × (∀ i, O i) => fun i => a i (p.1, p.2 i)) (by fun_prop)
  have hpi : pi (fun i => observe (κ i) (a i) (ha i)) = pi (fun i => M i ⊗ₖ Q i) := by
    ext x : 1
    simp only [pi_apply, hd]
  rw [observe_pi κ a ha, hpi, disintegrate_pi] at h
  exact h.of_compProd

theorem hasCondDistrib_local_update {P : Measure Ω} [SFinite P]
    {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    [∀ i, MeasurableSpace.CountablyGenerated (C i)]
    [∀ i, StandardBorelSpace (O i)] [∀ i, Nonempty (O i)]
    {x : Ω → X} {o : Ω → ∀ i, O i}
    (e : ∀ i, X → E i) (he : ∀ i, Measurable (e i))
    (κ : ∀ i, Kernel (E i) (O i)) [∀ i, IsMarkovKernel (κ i)]
    (a : ∀ i, E i × O i → C i) (ha : ∀ i, Measurable (a i))
    (ho : HasCondDistrib o x (pi (fun i => (κ i).comap (e i) (he i))) P) :
    HasCondDistrib o (fun ω => (x ω, fun i => a i (e i (x ω), o ω i)))
      (pi (fun i => (observe (κ i) (a i) (ha i)).condKernel.comap
        (fun p : X × (∀ i, C i) => (e i p.1, p.2 i)) (by fun_prop))) P := by
  let M (i : ι) : Kernel X (C i) :=
    (observe (κ i) (a i) (ha i)).fst.comap (e i) (he i)
  let Q (i : ι) : Kernel (X × C i) (O i) :=
    (observe (κ i) (a i) (ha i)).condKernel.comap
      (fun p : X × C i => (e i p.1, p.2)) (by fun_prop)
  have hd (i : ι) : observe ((κ i).comap (e i) (he i))
      (fun p : X × O i => a i (e i p.1, p.2)) (by fun_prop) = M i ⊗ₖ Q i := by
    rw [observe_comap]
    dsimp only [M, Q]
    rw [← compProd_comap, Kernel.disintegrate]
  have h := hasCondDistrib_update (fun i => (κ i).comap (e i) (he i))
    (fun i => fun p : X × O i => a i (e i p.1, p.2)) (by intro i; fun_prop)
    M Q hd ho
  convert h using 1
  ext x : 1
  rfl

theorem hasCondDistrib_posterior [MeasurableSpace.CountablyGenerated A]
    [StandardBorelSpace Y] [Nonempty Y]
    {P : Measure Ω} [SFinite P] {x : Ω → X} {y : Ω → Y}
    {κ : Kernel X Y} [IsMarkovKernel κ] (ho : HasCondDistrib y x κ P)
    (a : X × Y → A) (ha : Measurable a) :
    HasCondDistrib y (fun ω => (x ω, a (x ω, y ω)))
      (observe κ a ha).condKernel P := by
  have h := hasCondDistrib_observe ho a ha
  rw [← Kernel.disintegrate (observe κ a ha) (observe κ a ha).condKernel] at h
  exact h.of_compProd

theorem local_conditioning {P : Measure Ω} [SFinite P]
    {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    [∀ i, MeasurableSpace.CountablyGenerated (C i)]
    [∀ i, StandardBorelSpace (O i)] [∀ i, Nonempty (O i)]
    {B : Type*} [MeasurableSpace B]
    {x : Ω → X} {o : Ω → ∀ i, O i} {b : Ω → B}
    (e : ∀ i, X → E i) (he : ∀ i, Measurable (e i))
    (κ : ∀ i, Kernel (E i) (O i)) [∀ i, IsMarkovKernel (κ i)]
    (a : ∀ i, E i × O i → C i) (ha : ∀ i, Measurable (a i))
    (L : Kernel (X × (∀ i, C i)) B) [IsMarkovKernel L]
    (ho : HasCondDistrib o x (pi (fun i => (κ i).comap (e i) (he i))) P)
    (hb : HasCondDistrib b (fun ω => (x ω, o ω))
      (L.comap (fun p : X × (∀ i, O i) => (p.1, fun i => a i (e i p.1, p.2 i)))
        (by fun_prop)) P) :
    HasCondDistrib o (fun ω => ((x ω, fun i => a i (e i (x ω), o ω i)), b ω))
      ((pi (fun i => (observe (κ i) (a i) (ha i)).condKernel.comap
        (fun p : X × (∀ i, C i) => (e i p.1, p.2 i)) (by fun_prop))).prodMkRight B) P := by
  have hu := hasCondDistrib_local_update e he κ a ha ho
  let f : X × (∀ i, O i) → (X × (∀ i, C i)) × (∀ i, O i) :=
    fun p => ((p.1, fun i => a i (e i p.1, p.2 i)), p.2)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have heq : (L.prodMkRight (∀ i, O i)).comap f hf =
      L.comap (fun p : X × (∀ i, O i) => (p.1, fun i => a i (e i p.1, p.2 i)))
        (by fun_prop) := by
    ext p : 1
    rfl
  have hb' : HasCondDistrib b (fun ω => (x ω, o ω))
      ((L.prodMkRight (∀ i, O i)).comap f hf) P := by rw [heq]; exact hb
  exact screening hu L hb'.comp_right

end LocalConditioning

namespace ArrayObjects.Object.Rolled

section
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def parameterEquiv (R : Finset I) (n : ℕ) :
    Arr I (Parameter M R) n ≃ᵐ (Arr I M.U (n + 1) × (R → Arr I M.Y n)) where
  toFun p := (fun v => (p (Fin.tail v)).1 (v 0), fun c w => (p w).2 c)
  invFun p w := (fun c => p.1 (Fin.cons c w), fun c => p.2 c w)
  left_inv p := by funext w; rfl
  right_inv p := by apply Prod.ext <;> funext v <;> simp
  measurable_toFun := by
    exact (Measurable.of_eval (fun _ => (measurable_pi_apply _).comp
      (measurable_fst.comp (measurable_pi_apply _)))).prodMk
      (Measurable.of_eval (fun _ => Measurable.of_eval (fun _ =>
        (measurable_pi_apply _).comp (measurable_snd.comp (measurable_pi_apply _)))))
  measurable_invFun := by
    exact Measurable.of_eval (fun _ =>
      (Measurable.of_eval (fun _ => (measurable_pi_apply _).comp measurable_fst)).prodMk
        (Measurable.of_eval (fun _ => (measurable_pi_apply _).comp
          ((measurable_pi_apply _).comp measurable_snd))))

def parents (R : Finset I) (n : ℕ) (y : Arr I M.Y (n + 1)) : R → Arr I M.Y n :=
  fun c => plane n 0 c y
@[fun_prop] lemma measurable_parents (R : Finset I) (n : ℕ) : Measurable (parents M R n) :=
  Measurable.of_eval (fun _ => measurable_plane _ _ _)

lemma parameterEquiv_observation (R : Finset I) (n : ℕ) :
    parameterEquiv M R n ∘ amap (parameter M R) n ∘ roll n =
      fun y => (amap M.par (n + 1) y, parents M R n y) := by
  funext y
  apply Prod.ext
  · funext v; simp [parameterEquiv, amap, parameter, roll]
  · funext c w; simp [parameterEquiv, amap, parameter, roll, parents, plane,
      Fin.insertNth_zero']

def posterior (R : Finset I) (n : ℕ) :
    Kernel (Arr I M.U (n + 1) × (R → Arr I M.Y n)) (Arr I M.Y (n + 1)) :=
  (LocalConditioning.observe (M.ownKernel (n + 1))
    (fun p => parents M R n p.2) ((measurable_parents M R n).comp measurable_snd)).condKernel
instance posterior_markov (R : Finset I) (n : ℕ) : IsMarkovKernel (posterior M R n) := by
  unfold posterior
  infer_instance

def ownPosterior (R : Finset I) (n : ℕ) :
    Kernel (Arr I (Parameter M R) n) (Arr I (State M) n) :=
  ((posterior M R n).map (roll n)).comap (parameterEquiv M R n)
    (parameterEquiv M R n).measurable
instance ownPosterior_markov (R : Finset I) (n : ℕ) : IsMarkovKernel (ownPosterior M R n) := by
  unfold ownPosterior
  let := Kernel.IsMarkovKernel.map (posterior M R n) (roll n).measurable
  infer_instance

lemma roll_symm_preserving (n : ℕ) :
    MeasurePreserving (roll (I := I) (Y := M.Y) n).symm (law M n) (M.law (n + 1)) := by
  refine ⟨(roll n).symm.measurable, ?_⟩
  rw [law, Measure.map_map (roll n).symm.measurable (roll n).measurable]
  simp

lemma ownPosterior_conditional (R : Finset I) (n : ℕ) :
    HasCondDistrib id (amap (parameter M R) n) (ownPosterior M R n) (law M n) := by
  have h := LocalConditioning.hasCondDistrib_posterior (M.ownKernel_conditional (n + 1))
    (fun p => parents M R n p.2) ((measurable_parents M R n).comp measurable_snd)
  change HasCondDistrib id
    (fun y => (amap M.par (n + 1) y, parents M R n y)) (posterior M R n) (M.law _) at h
  have h' := (h.comp_left (roll n).measurable).measurableEquiv_comp_right
    (parameterEquiv M R n).symm
  have hobs : (parameterEquiv M R n).symm ∘
      (fun y => (amap M.par (n + 1) y, parents M R n y)) =
        amap (parameter M R) n ∘ roll n := by
    rw [← parameterEquiv_observation]
    funext y
    exact (parameterEquiv M R n).symm_apply_apply _
  rw [hobs] at h'
  have hout := ConditionalTransport.pullback (roll_symm_preserving M n)
    ((measurable_amap (measurable_parameter M R) n).comp (roll n).measurable) h'
  simpa only [ownPosterior, MeasurableEquiv.symm_symm, Function.comp_assoc, MeasurableEquiv.self_comp_symm,
    Function.comp_id, Function.id_comp] using hout

end

variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

abbrev ParentOutside (R : Finset I) (n : ℕ) (j : I) :=
  Arr I M.U (n + 2) × (Outside j → R → Arr I M.Y n)
abbrev ScreenData (R : Finset I) (n : ℕ) (j : I) :=
  ParentOutside M R n j × (R → Arr I M.Y n)

def parentOutside (R : Finset I) (n : ℕ) (j : I) (p : RawData M n j) :
    ParentOutside M R n j := (p.1, fun k => parents M R n (p.2 k))
omit [DecidableEq I] in
@[fun_prop] lemma measurable_parentOutside (R : Finset I) (n : ℕ) (j : I) :
    Measurable (parentOutside M R n j) := by
  unfold parentOutside
  fun_prop

def parentRow (R : Finset I) (n : ℕ) (j : I) (c : R) (p : ParentOutside M R n j) :
    OldData M n j := (plane (n + 1) 0 c p.1, fun k => p.2 k c)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_parentRow (R : Finset I) (n : ℕ) (j : I) (c : R) :
    Measurable (parentRow M R n j c) := by
  unfold parentRow
  fun_prop

def parentsKernel (R : Finset I) (n : ℕ) (j : I) :
    Kernel (ParentOutside M R n j) (R → Arr I M.Y n) :=
  FiniteKernel.pi (fun c : R =>
    (condDistrib (plane n (Fin.last n) j) (oldData M n j) (M.law (n + 1))).comap
      (parentRow M R n j c) (measurable_parentRow M R n j c))
instance parentsKernel_markov (R : Finset I) (n : ℕ) (j : I) :
    IsMarkovKernel (parentsKernel M R n j) := by
  unfold parentsKernel
  infer_instance

omit [DecidableEq I] in
lemma parentsKernel_comap (R : Finset I) (n : ℕ) (j : I) :
    (parentsKernel M R n j).comap (parentOutside M R n j)
      (measurable_parentOutside M R n j) =
        FiniteKernel.pi (fun c : R => rowKernel M n j c) := by
  ext p : 1
  rfl

def screenData (R : Finset I) (n : ℕ) (j : I) (y : Arr I M.Y (n + 2)) :
    ScreenData M R n j :=
  (parentOutside M R n j (rawData M n j y), fun c => missingRow M n j c y)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_screenData (R : Finset I) (n : ℕ) (j : I) :
    Measurable (screenData M R n j) := by
  unfold screenData
  exact ((measurable_parentOutside M R n j).comp (measurable_rawData M n j)).prodMk
    (Measurable.of_eval (fun c => measurable_missingRow M n j c))

def screenKernel (R : Finset I) (n : ℕ) (j : I) :
    Kernel (ScreenData M R n j) (Outside j → Arr I M.Y (n + 1)) :=
  (FiniteKernel.pi (fun k : Outside j => (posterior M R n).comap
    (fun p : ParentOutside M R n j => (plane (n + 1) (Fin.last (n + 1)) k p.1, p.2 k))
      (by fun_prop))).prodMkRight (R → Arr I M.Y n)
instance screenKernel_markov (R : Finset I) (n : ℕ) (j : I) :
    IsMarkovKernel (screenKernel M R n j) := by
  unfold screenKernel
  infer_instance

lemma screen_conditional (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I)
    (ih : ∀ S : Finset I, S ⊂ R → IsConditional M S) (n : ℕ) (j : I) :
    HasCondDistrib (planes (n + 1) (Outside j)) (screenData M R n j)
      (screenKernel M R n j) (M.law (n + 2)) := by
  have hproper : Outside j ≠ Finset.univ := by
    intro he
    have hj : j ∈ Outside j := he.symm ▸ Finset.mem_univ j
    simp [Outside] at hj
  have hb := parent_joint M hM R hR ih n j
  rw [← parentsKernel_comap] at hb
  exact LocalConditioning.local_conditioning
    (fun k : Outside j => plane (n + 1) (Fin.last (n + 1)) (k : I))
    (fun _ => measurable_plane _ _ _) (fun _ => M.ownKernel (n + 1))
    (fun _ => fun p => parents M R n p.2)
    (fun _ => (measurable_parents M R n).comp measurable_snd)
    (parentsKernel M R n j) (M.planes_conditional (n + 1) (Outside j) hproper) hb

def screenEquiv (R : Finset I) (n : ℕ) (j : I) :
    Arr I (Parameter M R) (n + 1) ≃ᵐ ScreenData M R n j where
  toFun p := ((fun v => (p (Fin.tail v)).1 (v 0),
    fun k c v => (p (Fin.snoc v (k : I))).2 c), fun c v => (p (Fin.snoc v j)).2 c)
  invFun p w := (fun c => p.1.1 (Fin.cons c w), fun c =>
    if h : w (Fin.last n) = j then p.2 c (Fin.init w) else
      p.1.2 ⟨w (Fin.last n), by simp [Outside, h]⟩ c (Fin.init w))
  left_inv p := by
    funext w
    apply Prod.ext
    · rfl
    · funext c
      dsimp only
      split_ifs with h
      · rw [← h, Fin.snoc_init_self]
      · rw [Fin.snoc_init_self]
  right_inv p := by
    apply Prod.ext
    · apply Prod.ext
      · funext v; simp
      · funext k c v
        have hk : (k : I) ≠ j :=
          @Finset.ne_of_mem_erase I (fun a b => Classical.propDecidable (a = b))
            _ _ _ k.property
        simp [hk]
    · funext c v
      simp
  measurable_toFun := by
    exact ((Measurable.of_eval (fun _ => (measurable_pi_apply _).comp
      (measurable_fst.comp (measurable_pi_apply _)))).prodMk
      (Measurable.of_eval (fun _ => Measurable.of_eval (fun _ =>
        Measurable.of_eval (fun _ => (measurable_pi_apply _).comp
          (measurable_snd.comp (measurable_pi_apply _))))))).prodMk
      (Measurable.of_eval (fun _ => Measurable.of_eval (fun _ =>
        (measurable_pi_apply _).comp (measurable_snd.comp (measurable_pi_apply _)))))
  measurable_invFun := by
    apply Measurable.of_eval
    intro w
    apply Measurable.prodMk
    · fun_prop
    · apply Measurable.of_eval
      intro c
      split_ifs <;> fun_prop

lemma screenEquiv_observation (R : Finset I) (n : ℕ) (j : I) :
    screenEquiv M R n j ∘ amap (parameter M R) (n + 1) ∘ roll (n + 1) =
      screenData M R n j := by
  funext y
  apply Prod.ext
  · apply Prod.ext
    · funext v; simp [screenEquiv, screenData, parentOutside, rawData, amap, parameter, roll]
    · funext k c v
      simp [screenEquiv, screenData, parentOutside, rawData, parents, planes, plane,
        amap, parameter, roll, Fin.insertNth_zero', Fin.insertNth_last', cons_snoc]
  · funext c v
    simp [screenEquiv, screenData, amap, parameter, roll, missingRow, plane,
      Fin.insertNth_zero', Fin.insertNth_last']


lemma screen_plane_parameters (R : Finset I) (n : ℕ) (j : I)
    (p : Arr I (Parameter M R) (n + 1)) (k : Outside j) :
    (plane (n + 1) (Fin.last (n + 1)) (k : I) (screenEquiv M R n j p).1.1,
      (screenEquiv M R n j p).1.2 k) =
        parameterEquiv M R n (plane n (Fin.last n) (k : I) p) := by
  apply Prod.ext
  · funext v
    obtain ⟨c, w, rfl⟩ := Fin.exists_cons v
    simp [screenEquiv, parameterEquiv, plane, Fin.insertNth_last', ← cons_snoc]
  · funext c w
    simp [screenEquiv, parameterEquiv, plane, Fin.insertNth_last']

lemma screenKernel_roll (R : Finset I) (n : ℕ) (j : I) :
    ((screenKernel M R n j).map (fun z k => roll n (z k))).comap
      (screenEquiv M R n j) (screenEquiv M R n j).measurable =
    FiniteKernel.pi (fun k : Outside j => (ownPosterior M R n).comap
      (plane n (Fin.last n) k) (measurable_plane _ _ _)) := by
  ext p : 1
  rw [Kernel.comap_apply]
  have hm : Measurable (fun z : Outside j → Arr I M.Y (n + 1) =>
      fun k => roll n (z k)) := by fun_prop
  rw [Kernel.map_apply _ hm]
  change (Measure.pi (fun k : Outside j => posterior M R n
    (plane (n + 1) (Fin.last (n + 1)) (k : I) (screenEquiv M R n j p).1.1,
      (screenEquiv M R n j p).1.2 k))).map (fun z k => roll n (z k)) = _
  rw [Measure.pi_map_pi (fun _ => (roll n).measurable.aemeasurable)]
  congr 1
  funext k
  rw [screen_plane_parameters]
  change _ = ((posterior M R n).map (roll n)) _
  rw [Kernel.map_apply _ (roll n).measurable]

lemma outside_conditional (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I)
    (ih : ∀ S : Finset I, S ⊂ R → IsConditional M S) (n : ℕ) (j : I) :
    HasCondDistrib (planes n (Outside j)) (amap (parameter M R) (n + 1))
      (FiniteKernel.pi (fun k : Outside j => (ownPosterior M R n).comap
        (plane n (Fin.last n) k) (measurable_plane _ _ _))) (law M (n + 1)) := by
  have h := screen_conditional M hM R hR ih n j
  have h' := (h.comp_left (Measurable.of_eval (fun k =>
    (roll n).measurable.comp (measurable_pi_apply k)))).measurableEquiv_comp_right
      (screenEquiv M R n j).symm
  change HasCondDistrib ((fun z k => roll n (z k)) ∘ planes (n + 1) (Outside j))
    ((screenEquiv M R n j).symm ∘ screenData M R n j)
    (((screenKernel M R n j).map (fun z k => roll n (z k))).comap
      (screenEquiv M R n j) (screenEquiv M R n j).measurable) (M.law (n + 2)) at h'
  rw [screenKernel_roll, ← planes_roll] at h'
  have hobs : (screenEquiv M R n j).symm ∘ screenData M R n j =
      amap (parameter M R) (n + 1) ∘ roll (n + 1) := by
    rw [← screenEquiv_observation]
    funext y
    exact (screenEquiv M R n j).symm_apply_apply _
  rw [hobs] at h'
  have hout := ConditionalTransport.pullback (roll_symm_preserving M (n + 1))
    ((measurable_amap (measurable_parameter M R) _).comp (roll (n + 1)).measurable) h'
  simpa only [Function.comp_assoc, MeasurableEquiv.self_comp_symm, Function.comp_id] using hout


end ArrayObjects.Object.Rolled

namespace FiniteKernel
open MeasureTheory ProbabilityTheory

lemma measure_pi_precomp {ι τ : Type*} [Fintype ι] [Fintype τ]
    {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (Y i)) [∀ i, IsProbabilityMeasure (μ i)] (e : τ ↪ ι) :
    (Measure.pi μ).map (fun y i => y (e i)) = Measure.pi (fun i => μ (e i)) := by
  have hi : iIndepFun (fun i : ι => Function.eval i) (Measure.pi μ) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  rw [(hi.precomp e.injective).map_fun_eq_pi_map
    (fun i => (measurable_pi_apply (e i)).aemeasurable)]
  congr 1
  funext i
  exact (measurePreserving_eval μ (e i)).map_eq

lemma pi_precomp {ι τ X : Type*} [Fintype ι] [Fintype τ]
    {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)] [MeasurableSpace X]
    (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)] (e : τ ↪ ι) :
    (pi κ).map (fun y i => y (e i)) = pi (fun i => κ (e i)) := by
  ext x : 1
  rw [Kernel.map_apply _ (by fun_prop)]
  exact measure_pi_precomp _ e

end FiniteKernel

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma proper_conditional (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I)
    (ih : ∀ S : Finset I, S ⊂ R → IsConditional M S) (n : ℕ)
    (J : Finset I) (hJ : J ≠ Finset.univ) :
    HasCondDistrib (planes n J) (amap (parameter M R) (n + 1))
      (FiniteKernel.pi (fun k : J => (ownPosterior M R n).comap
        (plane n (Fin.last n) k) (measurable_plane _ _ _))) (law M (n + 1)) := by
  have hj : ∃ j, j ∉ J := by
    by_contra! h
    exact hJ (Finset.eq_univ_of_forall h)
  obtain ⟨j, hj⟩ := hj
  let e : J ↪ Outside j := ⟨fun k => ⟨k, by
    have hk : (k : I) ≠ j := by intro he; exact hj (he ▸ k.property)
    simpa [Outside] using And.intro hk (Finset.mem_univ (k : I))⟩,
      fun x y h => Subtype.ext (show (x : I) = (y : I) from
        congrArg (fun v : Outside j => (v : I)) h)⟩
  have h := (outside_conditional M hM R hR ih n j).comp_left
    (show Measurable (fun z : Outside j → Arr I (State M) n => fun k => z (e k)) by fun_prop)
  rw [FiniteKernel.pi_precomp] at h
  exact h

omit [DecidableEq I] in
lemma parameter_plane_preserving (R : Finset I) (n : ℕ) (j : I) :
    MeasurePreserving (plane n (Fin.last n) j)
      ((law M (n + 1)).map (amap (parameter M R) (n + 1)))
      ((law M n).map (amap (parameter M R) n)) := by
  refine ⟨measurable_plane _ _ _, ?_⟩
  rw [Measure.map_map (measurable_plane _ _ _)
    (measurable_amap (measurable_parameter M R) _), plane_amap,
    ← Measure.map_map (measurable_amap (measurable_parameter M R) _)
      (measurable_plane _ _ _), consistent]

lemma conditional_step (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I)
    (ih : ∀ S : Finset I, S ⊂ R → IsConditional M S) : IsConditional M R := by
  intro n J hJ
  have ho := condDistrib_ae_eq_of_measure_eq_compProd (ownPosterior_conditional M R n).aemeasurable_fst
    measurable_id.aemeasurable (ownPosterior_conditional M R n).map_eq
  have hp := condDistrib_ae_eq_of_measure_eq_compProd (proper_conditional M hM R hR ih n J hJ).aemeasurable_fst
    (measurable_planes n J).aemeasurable (proper_conditional M hM R hR ih n J hJ).map_eq
  have hplanes : ∀ᵐ p ∂(law M (n + 1)).map (amap (parameter M R) (n + 1)),
      ∀ j : J, condDistrib id (amap (parameter M R) n) (law M n)
        (plane n (Fin.last n) j p) = ownPosterior M R n (plane n (Fin.last n) j p) := by
    rw [ae_all_iff]
    intro j
    exact (parameter_plane_preserving M R n j).quasiMeasurePreserving.ae_eq_comp ho
  filter_upwards [hp, hplanes] with p hp he
  exact hp.trans (congrArg Measure.pi (funext fun j => (he j).symm))

theorem isConditional (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I) : IsConditional M R := by
  have hall : ∀ R : Finset I, R.card + 2 ≤ Fintype.card I → IsConditional M R := by
    intro R
    refine Finset.strongInductionOn R ?_
    intro R ih hc
    apply conditional_step M hM R hc
    intro S hS
    exact ih S hS (le_trans (Nat.add_le_add_right (Finset.card_le_card hS.1) 2) hc)
  exact hall R hR

lemma insert_proper (R : Finset I) (hR : R.card + 2 ≤ Fintype.card I)
    (a : I) (ha : a ∉ R) : insert a R ≠ Finset.univ := by
  intro he
  have h := congrArg Finset.card he
  rw [Finset.card_insert_of_notMem ha, Finset.card_univ] at h
  omega

def object (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I) (a : I) (ha : a ∉ R) : Object I base :=
  makeObject M R (isConditional M hM R hR) a ha (insert_proper R hR a ha)

def objectExtension (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I) (a : I) (ha : a ∉ R) :
    Extension M (object M hM R hR a ha) :=
  extension M R (isConditional M hM R hR) a ha (insert_proper R hR a ha)


lemma row_reveal (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I) (a : I) (ha : a ∉ R) (n : ℕ) :
    HasCondDistrib (plane (n + 1) 0 a)
      (fun y => (amap M.par (n + 2) y, parents M R (n + 1) y))
      (((M.ownKernel (n + 1)).comap (plane (n + 1) 0 a)
        (measurable_plane _ _ _)).prodMkRight (R → Arr I M.Y (n + 1)))
      (M.law (n + 2)) := by
  let N := object M hM R hR a ha
  let e := objectExtension M hM R hR a ha
  let p : Arr I (Parameter M R) (n + 1) → Arr I M.U (n + 1) :=
    amap (fun z => z.1 a) (n + 1)
  have hpm : Measurable p := measurable_amap ((measurable_pi_apply a).comp measurable_fst) _
  have hs := hM.hasCondDistrib e n .parameter
    (amap M.par (n + 1)) (amap (parameter M R) (n + 1)) id p
    (measurable_amap M.measurable_par _) (measurable_amap (measurable_parameter M R) _)
    measurable_id hpm rfl rfl rfl
  have hp := ConditionalTransport.pullback
    (show MeasurePreserving (roll (Y := M.Y) (n + 1)) (M.law (n + 2)) (N.law (n + 1)) from
      ⟨(roll (n + 1)).measurable, rfl⟩)
    (measurable_amap (measurable_parameter M R) _) hs
  have h := hp.measurableEquiv_comp_right (parameterEquiv M R (n + 1))
  change HasCondDistrib ((id ∘ amap (Function.eval a) (n + 1)) ∘ roll (n + 1))
    (parameterEquiv M R (n + 1) ∘ amap (parameter M R) (n + 1) ∘ roll (n + 1))
    (((M.ownKernel (n + 1)).comap p hpm).comap (parameterEquiv M R (n + 1)).symm
      (parameterEquiv M R (n + 1)).symm.measurable) (M.law (n + 2)) at h
  rw [Function.id_comp, select_roll, parameterEquiv_observation] at h
  have hk : (((M.ownKernel (n + 1)).comap p hpm).comap
      (parameterEquiv M R (n + 1)).symm (parameterEquiv M R (n + 1)).symm.measurable) =
      (((M.ownKernel (n + 1)).comap (plane (n + 1) 0 a)
        (measurable_plane _ _ _)).prodMkRight (R → Arr I M.Y (n + 1))) := by
    ext z : 1
    change M.ownKernel (n + 1) (p ((parameterEquiv M R (n + 1)).symm z)) =
      M.ownKernel (n + 1) (plane (n + 1) 0 a z.1)
    congr 1
    funext v
    change z.1 (Fin.cons a v) = z.1 ((0 : Fin (n + 2)).insertNth a v)
    rw [Fin.insertNth_zero']
  rw [hk] at h
  exact h

theorem rows_conditional (hM : M.IsSaturated) (J : Finset I)
    (hJ : J ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (fun y => fun a : J => plane (n + 1) 0 (a : I) y)
      (amap M.par (n + 2))
      (FiniteKernel.pi (fun a : J => (M.ownKernel (n + 1)).comap
        (plane (n + 1) 0 (a : I)) (measurable_plane _ _ _))) (M.law (n + 2)) := by
  apply ConditionalReveal.finite_reveal (M.law (n + 2)) (amap M.par (n + 2))
    (measurable_amap M.measurable_par _)
    (fun a : I => plane (n + 1) 0 a)
    (fun a : I => (M.ownKernel (n + 1)).comap (plane (n + 1) 0 a)
      (measurable_plane _ _ _)) J
  intro R hRJ a ha haR
  have hstrict : R ⊂ J := (Finset.ssubset_iff_subset_ne).mpr ⟨hRJ, by
    intro he; subst R; exact haR ha⟩
  have hcardR := Finset.card_lt_card hstrict
  have hcardJ := Finset.card_lt_card
    ((Finset.ssubset_iff_subset_ne).mpr ⟨Finset.subset_univ J, hJ⟩)
  rw [Finset.card_univ] at hcardJ
  exact row_reveal M hM R (by omega) a haR n

theorem single_cell_locality (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I) (a : I) (ha : a ∉ R) (j : I) :
    HasCondDistrib (missingRow M 0 j a) (revealData M R 0 j)
      ((rowKernel M 0 j a).prodMkRight (R → Arr I M.Y 0)) (M.law 2) :=
  parent_reveal M hM R (isConditional M hM R hR) a ha (insert_proper R hR a ha) 0 j

end ArrayObjects.Object.Rolled

namespace ConditionalReveal
variable {Ω D B ι : Type*} [MeasurableSpace Ω] [MeasurableSpace D]
  [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B] [DecidableEq ι]

omit [MeasurableSpace Ω] [StandardBorelSpace B] [Nonempty B] in
lemma comap_union_reveal (E : Ω → D) (y : ι → Ω → B) (P S : Finset ι) :
    MeasurableSpace.comap (fun ω => (E ω, fun i : ↥(P ∪ S) => y i ω)) inferInstance =
    MeasurableSpace.comap (fun ω => ((E ω, fun i : P => y i ω), fun i : S => y i ω))
      inferInstance := by
  simp only [inferInstance, Prod.instMeasurableSpace, MeasurableSpace.comap_prodMk,
    MeasurableSpace.comap_process_pi]
  have hu : (⨆ i : ↥(P ∪ S), MeasurableSpace.comap (y i) inferInstance) =
      (⨆ i : P, MeasurableSpace.comap (y i) inferInstance) ⊔
      (⨆ i : S, MeasurableSpace.comap (y i) inferInstance) := by
    apply le_antisymm
    · refine iSup_le (fun i => ?_)
      rcases Finset.mem_union.mp i.property with hi | hi
      · apply le_sup_of_le_left
        exact le_iSup_of_le (⟨i, hi⟩ : P) le_rfl
      · apply le_sup_of_le_right
        exact le_iSup_of_le (⟨i, hi⟩ : S) le_rfl
    · apply sup_le
      · exact iSup_le (fun i => le_iSup_of_le ⟨i, Finset.mem_union_left S i.property⟩ le_rfl)
      · exact iSup_le (fun i => le_iSup_of_le ⟨i, Finset.mem_union_right P i.property⟩ le_rfl)
  rw [hu, sup_assoc]

theorem finite_reveal_with_parents (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → D) (hE : Measurable E) (y : ι → Ω → B)
    (hy : ∀ i, Measurable (y i)) (κ : ι → Kernel D B) [∀ i, IsMarkovKernel (κ i)]
    (P A : Finset ι)
    (h : ∀ S ⊆ A, ∀ i ∈ A, i ∉ S →
      HasCondDistrib (y i) (fun ω => (E ω, fun j : ↥(P ∪ S) => y j ω))
        ((κ i).prodMkRight (↥(P ∪ S) → B)) μ) :
    HasCondDistrib (fun ω => fun i : A => y i ω)
      (fun ω => (E ω, fun j : P => y j ω))
      (FiniteKernel.pi (fun i : A => (κ i).prodMkRight (P → B))) μ := by
  apply finite_reveal μ (fun ω => (E ω, fun j : P => y j ω))
    (hE.prodMk (Measurable.of_eval (fun j => hy j))) y
    (fun i => (κ i).prodMkRight (P → B)) A
  intro S hS i hi hiS
  apply ConditionalTransport.recondition
    (hE.prodMk (Measurable.of_eval (fun j : ↥(P ∪ S) => hy j)))
    ((hE.prodMk (Measurable.of_eval (fun j : P => hy j))).prodMk
      (Measurable.of_eval (fun j : S => hy j))) (hy i) (h S hS i hi hiS)
  · exact comap_union_reveal E y P S
  · exact Filter.Eventually.of_forall (fun _ => rfl)

end ConditionalReveal

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem grouped_single_missing (hM : M.IsSaturated) (P A : Finset I)
    (hPA : Disjoint P A) (hcard : P.card + A.card + 1 ≤ Fintype.card I)
    (n : ℕ) (j : I) :
    HasCondDistrib (fun y => fun a : A => missingRow M n j a y)
      (revealData M P n j)
      (FiniteKernel.pi (fun a : A => (rowKernel M n j a).prodMkRight
        (P → Arr I M.Y n))) (M.law (n + 2)) := by
  apply ConditionalReveal.finite_reveal_with_parents (M.law (n + 2)) (rawData M n j)
    (measurable_rawData M n j) (fun a => missingRow M n j a)
    (fun a => measurable_missingRow M n j a) (fun a => rowKernel M n j a) P A
  intro S hSA a ha haS
  have haP : a ∉ P := fun hp => Finset.disjoint_left.mp hPA hp ha
  have hcS : S.card < A.card := Finset.card_lt_card
    ((Finset.ssubset_iff_subset_ne).mpr ⟨hSA, by intro he; subst S; exact haS ha⟩)
  have hcU := Finset.card_union_le P S
  have hc : (P ∪ S).card + 2 ≤ Fintype.card I := by omega
  have haU : a ∉ P ∪ S := by simpa only [Finset.mem_union, not_or] using And.intro haP haS
  exact parent_reveal M hM (P ∪ S) (isConditional M hM (P ∪ S) hc) a haU
    (insert_proper _ hc a haU) n j

end ArrayObjects.Object.Rolled

namespace ConditionalScreens
variable {Ω S Z O : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
  [MeasurableSpace O] [StandardBorelSpace O] [Nonempty O]

theorem reverse_screen {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : Ω → S} {z : Ω → Z} {o : Ω → O}
    (hs : Measurable s) (hz : Measurable z) (ho : Measurable o)
    (f : Z → S) (hf : Measurable f) (g : O → S) (hg : Measurable g)
    (hsz : s = f ∘ z) (hso : s = g ∘ o)
    (κ : Kernel S O) [IsMarkovKernel κ] (l : Kernel S Z) [IsMarkovKernel l]
    (hκ : HasCondDistrib o s κ μ)
    (hl : HasCondDistrib z o (l.comap g hg) μ) :
    HasCondDistrib o z (κ.comap f hf) μ := by
  have hl' : HasCondDistrib z (fun ω => (s ω, o ω)) (l.prodMkRight O) μ := by
    apply ConditionalTransport.recondition ho (hs.prodMk ho) hz hl
    · apply le_antisymm
      · exact ConditionalTransport.comap_le_of_factor measurable_snd rfl
      · apply ConditionalTransport.comap_le_of_factor (hg.prodMk measurable_id)
        simpa only [Function.comp_def, id_eq] using congrArg (fun v => fun ω => (v ω, o ω)) hso
    · filter_upwards [] with ω
      change l (g (o ω)) = l (s ω)
      rw [hso]; rfl
  have hh := screening hκ l hl'
  apply ConditionalTransport.recondition (hs.prodMk hz) hz ho hh
  · apply le_antisymm
    · apply ConditionalTransport.comap_le_of_factor (hf.prodMk measurable_id)
      simpa only [Function.comp_def, id_eq] using congrArg (fun v => fun ω => (v ω, z ω)) hsz
    · exact ConditionalTransport.comap_le_of_factor measurable_snd rfl
  · filter_upwards [] with ω
    change κ (s ω) = κ (f (z ω))
    rw [hsz]; rfl

end ConditionalScreens

namespace FiniteKernel
variable {ι : Type*} [Fintype ι] {Y S : ι → Type*}
  [∀ i, MeasurableSpace (Y i)] [∀ i, StandardBorelSpace (Y i)] [∀ i, Nonempty (Y i)]
  [∀ i, MeasurableSpace (S i)]

theorem independent_observation (μ : ∀ i, Measure (Y i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : ∀ i, Y i → S i)
    (hf : ∀ i, Measurable (f i)) :
    HasCondDistrib (id : (∀ i, Y i) → (∀ i, Y i)) (fun y i => f i (y i))
      (pi (fun i => (condDistrib id (f i) (μ i)).comap (Function.eval i)
        (measurable_pi_apply i))) (Measure.pi μ) := by
  refine ⟨((Measurable.of_eval (fun i => (hf i).comp (measurable_pi_apply i))).prodMk
    measurable_id).aemeasurable, ?_⟩
  let (i : ι) : IsProbabilityMeasure ((μ i).map (f i)) :=
    (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (hf i).aemeasurable
  apply (zipEquiv S Y).measurableEmbedding.map_injective
  rw [Measure.pi_map_pi (fun i => (hf i).aemeasurable), compProd_pi]
  rw [Measure.map_map (zipEquiv S Y).measurable (by fun_prop)]
  change (Measure.pi μ).map (fun y i => (f i (y i), y i)) =
    Measure.pi (fun i => (μ i).map (f i) ⊗ₘ condDistrib id (f i) (μ i))
  calc
    _ = Measure.pi (fun i => (μ i).map (fun y => (f i y, y))) :=
      Measure.pi_map_pi (fun i => ((hf i).prodMk measurable_id).aemeasurable)
    _ = _ := ?_
  congr 1
  funext i
  exact (compProd_map_condDistrib (μ := μ i) (X := f i)
    (Y := id) (hf i).aemeasurable measurable_id.aemeasurable).symm

end FiniteKernel

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma outside_row_screen (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a j₀ : I) (n : ℕ) :
    HasCondDistrib (plane (n + 1) 0 a) (planes (n + 1) (Outside j₀))
      ((condDistrib id (planes n (Outside j₀)) (M.law (n + 1))).comap
        (fun o : Outside j₀ → Arr I M.Y (n + 1) => fun j => plane n 0 a (o j))
        (Measurable.of_eval (fun j => (measurable_plane _ _ _).comp (measurable_pi_apply j))))
      (M.law (n + 2)) := by
  have hR : (∅ : Finset I).card + 2 ≤ Fintype.card I := by simpa using hI
  let N := object M hM ∅ hR a (Finset.notMem_empty a)
  let e := objectExtension M hM ∅ hR a (Finset.notMem_empty a)
  let p : (Outside j₀ → Arr I (State M) n) → (Outside j₀ → Arr I M.Y n) :=
    fun o j => amap (Function.eval a) n (o j)
  have hpm : Measurable p := Measurable.of_eval (fun j =>
    (measurable_amap (measurable_pi_apply a) n).comp (measurable_pi_apply j))
  have hs := hM.hasCondDistrib e n (.outside j₀)
    (planes n (Outside j₀)) (planes (Y := State M) n (Outside j₀))
    (id : Arr I M.Y (n + 1) → Arr I M.Y (n + 1)) p
    (measurable_planes _ _) (measurable_planes _ _) measurable_id hpm rfl rfl rfl
  have hp := ConditionalTransport.pullback
    (show MeasurePreserving (roll (Y := M.Y) (n + 1)) (M.law (n + 2)) (N.law (n + 1)) from
      ⟨(roll (n + 1)).measurable, rfl⟩) (measurable_planes _ _) hs
  let E : (Outside j₀ → Arr I (State M) n) ≃ᵐ (Outside j₀ → Arr I M.Y (n + 1)) :=
    MeasurableEquiv.piCongrRight (fun _ => (roll n).symm)
  change HasCondDistrib ((id ∘ amap (Function.eval a) (n + 1)) ∘ roll (n + 1))
    (planes (Y := State M) n (Outside j₀) ∘ roll (n + 1))
    ((condDistrib (id : Arr I M.Y (n + 1) → Arr I M.Y (n + 1))
      (planes n (Outside j₀)) (M.law (n + 1))).comap p hpm) (M.law (n + 2)) at hp
  have h := hp.measurableEquiv_comp_right E
  change HasCondDistrib ((id ∘ amap (Function.eval a) (n + 1)) ∘ roll (n + 1))
    (E ∘ planes n (Outside j₀) ∘ roll (n + 1))
    (((condDistrib id (planes n (Outside j₀)) (M.law (n + 1))).comap p hpm).comap
      E.symm E.symm.measurable) (M.law (n + 2)) at h
  have he : E ∘ planes n (Outside j₀) ∘ roll (n + 1) = planes (n + 1) (Outside j₀) := by
    rw [planes_roll]
    funext y j
    change (roll n).symm (roll n (planes (n + 1) (Outside j₀) y j)) = _
    exact (roll n).symm_apply_apply _
  rw [Function.id_comp, select_roll, he] at h
  convert h using 1
  ext o : 1
  change condDistrib id (planes n (Outside j₀)) (M.law (n + 1))
    (fun j => plane n 0 a (o j)) =
    condDistrib id (planes n (Outside j₀)) (M.law (n + 1)) (p (E.symm o))
  congr 1
  funext j
  exact (congrFun (select_roll n a) (o j)).symm

omit [DecidableEq I] in

lemma plane_first_last (n : ℕ) (a j : I) :
    plane (Y := M.Y) n 0 a ∘ plane (n + 1) (Fin.last (n + 1)) j =
      plane n (Fin.last n) j ∘ plane (n + 1) 0 a := by
  funext y v
  change y ((Fin.last (n + 1)).insertNth j ((0 : Fin (n + 1)).insertNth a v)) =
    y ((0 : Fin (n + 2)).insertNth a ((Fin.last n).insertNth j v))
  simp only [Fin.insertNth_last', Fin.insertNth_zero']
  rw [cons_snoc]

theorem columns_given_row (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a j₀ : I) (n : ℕ) :
    HasCondDistrib (planes (n + 1) (Outside j₀)) (plane (n + 1) 0 a)
      (FiniteKernel.pi (fun j : Outside j₀ =>
        (condDistrib id (plane n 0 a) (M.law (n + 1))).comap
          (plane n (Fin.last n) j) (measurable_plane _ _ _))) (M.law (n + 2)) := by
  let f : Arr I M.Y (n + 1) → Outside j₀ → Arr I M.Y n := planes n (Outside j₀)
  let g : (Outside j₀ → Arr I M.Y (n + 1)) → Outside j₀ → Arr I M.Y n :=
    fun o j => plane n 0 a (o j)
  have hf : Measurable f := measurable_planes _ _
  have hg : Measurable g := Measurable.of_eval (fun j =>
    (measurable_plane _ _ _).comp (measurable_pi_apply j))
  let κ := FiniteKernel.pi (fun _j : Outside j₀ =>
    (condDistrib (id : Arr I M.Y (n + 1) → Arr I M.Y (n + 1))
      (plane n 0 a) (M.law (n + 1))).comap
        (Function.eval _j) (measurable_pi_apply _j))
  let l := condDistrib (id : Arr I M.Y (n + 1) → Arr I M.Y (n + 1)) f (M.law (n + 1))
  have hJ : Outside j₀ ≠ Finset.univ := by
    intro he
    have hj : j₀ ∈ Outside j₀ := he ▸ Finset.mem_univ j₀
    simp only [Outside, Finset.mem_erase, ne_eq, not_true_eq_false, false_and] at hj
  have ho : MeasurePreserving (planes (n + 1) (Outside j₀)) (M.law (n + 2))
      (Measure.pi (fun _ : Outside j₀ => M.law (n + 1))) :=
    ⟨measurable_planes _ _, M.proper _ _ hJ⟩
  have hk := ConditionalTransport.pullback ho hg
    (FiniteKernel.independent_observation (fun _ : Outside j₀ => M.law (n + 1))
      (fun _ => plane n 0 a) (fun _ => measurable_plane _ _ _))
  have hs : g ∘ planes (n + 1) (Outside j₀) = f ∘ plane (n + 1) 0 a := by
    funext y j
    exact congrFun (plane_first_last M n a j) y
  have h := ConditionalScreens.reverse_screen
    (hg.comp (measurable_planes _ _)) (measurable_plane _ _ _) (measurable_planes _ _)
    f hf g hg hs rfl κ l hk (outside_row_screen M hM hI a j₀ n)
  convert h using 1
  ext z : 1
  rfl

end ArrayObjects.Object.Rolled

namespace FiniteKernel
lemma map_eval {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)] (i : ι) :
    (pi κ).map (Function.eval i) = κ i := by
  ext x : 1
  rw [Kernel.map_apply _ (measurable_pi_apply i)]
  exact (measurePreserving_eval (fun j => κ j x) i).map_eq
end FiniteKernel

namespace ArrayObjects.Object
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma plane_conditional (hI : 2 ≤ Fintype.card I) (n : ℕ) (a : I) :
    HasCondDistrib (plane n (Fin.last n) a) (amap M.par (n + 1))
      ((M.ownKernel n).comap (plane n (Fin.last n) a) (measurable_plane _ _ _))
      (M.law (n + 1)) := by
  have hproper : ({a} : Finset I) ≠ Finset.univ := by
    intro he
    have hc := congrArg Finset.card he
    simp only [Finset.card_singleton, Finset.card_univ] at hc
    omega
  have h := (M.planes_conditional n {a} hproper).comp_left
    (measurable_pi_apply (⟨a, Finset.mem_singleton_self a⟩ : ({a} : Finset I)))
  rw [FiniteKernel.map_eval] at h
  exact h

omit [DecidableEq I] in
noncomputable def parameterLaw (n : ℕ) : Measure (Arr I M.U n) :=
  (M.law n).map (amap M.par n)
omit [DecidableEq I] in
instance parameterLaw_probability (n : ℕ) : IsProbabilityMeasure (M.parameterLaw n) :=
  (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (measurable_amap M.measurable_par n).aemeasurable

omit [DecidableEq I] in

noncomputable def parameterCoordinateKernel (a : I) :
    Kernel (Arr I M.U 0) (Arr I M.U 1) :=
  condDistrib id (plane 0 0 a) (M.parameterLaw 1)
omit [DecidableEq I] in
instance parameterCoordinateKernel_markov (a : I) :
    IsMarkovKernel (M.parameterCoordinateKernel a) := by
  unfold parameterCoordinateKernel
  infer_instance

omit [DecidableEq I] in

lemma column_parameter_given_cell (hI : 2 ≤ Fintype.card I) (a : I) :
    HasCondDistrib (amap M.par 1) (plane 0 0 a)
      ((M.parameterCoordinateKernel a).comap (amap M.par 0)
        (measurable_amap M.measurable_par 0)) (M.law 1) := by
  have hc : HasCondDistrib (id : Arr I M.U 1 → Arr I M.U 1) (plane 0 0 a)
      (M.parameterCoordinateKernel a) (M.parameterLaw 1) :=
    ⟨((measurable_plane _ _ _).prodMk measurable_id).aemeasurable,
      (compProd_map_condDistrib (by fun_prop) measurable_id.aemeasurable).symm⟩
  have hq := ConditionalTransport.pullback
    (show MeasurePreserving (amap M.par 1) (M.law 1) (M.parameterLaw 1) from
      ⟨measurable_amap M.measurable_par _, rfl⟩) (measurable_plane _ _ _) hc
  exact ConditionalScreens.reverse_screen
    (s := amap M.par 0 ∘ plane 0 0 a) (z := plane 0 0 a) (o := amap M.par 1)
    ((measurable_amap M.measurable_par 0).comp (measurable_plane _ _ _))
    (measurable_plane _ _ _) (measurable_amap M.measurable_par _)
    (amap M.par 0) (measurable_amap M.measurable_par _) (plane 0 0 a)
    (measurable_plane _ _ _) rfl rfl (M.parameterCoordinateKernel a) (M.ownKernel 0)
    hq (M.plane_conditional hI 0 a)

omit [DecidableEq I] in

lemma shared_parameter_kernel (hI : 2 ≤ Fintype.card I) (a : I) :
    (fun s => (condDistrib (id : Arr I M.Y 1 → Arr I M.Y 1) (plane 0 0 a)
      (M.law 1) s).map (amap M.par 1)) =ᵐ[M.law 0]
    fun s => M.parameterCoordinateKernel a (amap M.par 0 s) := by
  let κ := condDistrib (id : Arr I M.Y 1 → Arr I M.Y 1) (plane 0 0 a) (M.law 1)
  have h : HasCondDistrib id (plane 0 0 a) κ (M.law 1) :=
    ⟨((measurable_plane _ _ _).prodMk measurable_id).aemeasurable,
      (compProd_map_condDistrib (by fun_prop) measurable_id.aemeasurable).symm⟩
  have hm := h.comp_left (measurable_amap M.measurable_par 1)
  have he := Kernel.ae_eq_of_compProd_eq
    (hm.map_eq.symm.trans (M.column_parameter_given_cell hI a).map_eq)
  rw [show (M.law 1).map (plane 0 0 a) = M.law 0 from M.consistent 0 0 a] at he
  exact he.mono (fun s hs => by
    simpa only [Kernel.map_apply _ (measurable_amap M.measurable_par _), Kernel.comap_apply] using hs)

end ArrayObjects.Object

namespace ConditionalTransport
variable {Ω Ω' A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [MeasurableSpace B]

theorem pushforward {P : Measure Ω} {Q : Measure Ω'} {f : Ω → Ω'}
    {E : Ω' → A} {O : Ω' → B} {κ : Kernel A B}
    (hf : MeasurePreserving f P Q) (hE : Measurable E) (hO : Measurable O)
    (h : HasCondDistrib (O ∘ f) (E ∘ f) κ P) : HasCondDistrib O E κ Q := by
  refine ⟨(hE.prodMk hO).aemeasurable, ?_⟩
  have he : P.map (E ∘ f) = Q.map E := by
    rw [← Measure.map_map hE hf.measurable, hf.map_eq]
  have hj : P.map (fun ω => (E (f ω), O (f ω))) = Q.map (fun ω => (E ω, O ω)) := by
    change P.map ((fun ω => (E ω, O ω)) ∘ f) = _
    rw [← Measure.map_map (hE.prodMk hO) hf.measurable, hf.map_eq]
  rw [← he]
  exact hj.symm.trans h.map_eq
end ConditionalTransport

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem columns_parameter_given_row (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a j₀ : I) :
    HasCondDistrib (fun y => fun j : Outside j₀ => amap M.par 1 (planes 1 (Outside j₀) y j))
      (amap M.par 1 ∘ plane 1 0 a)
      (FiniteKernel.pi (fun j : Outside j₀ => (M.parameterCoordinateKernel a).comap
        (plane 0 0 j) (measurable_plane _ _ _))) (M.law 2) := by
  let κ := condDistrib (id : Arr I M.Y 1 → Arr I M.Y 1) (plane 0 0 a) (M.law 1)
  let η := FiniteKernel.pi (fun j : Outside j₀ => (M.parameterCoordinateKernel a).comap
    (plane 0 0 j) (measurable_plane _ _ _))
  have h := (columns_given_row M hM hI a j₀ 0).comp_left
    (Measurable.of_eval (fun j => (measurable_amap M.measurable_par 1).comp
      (measurable_pi_apply j)))
  simp only [Function.comp_def] at h
  rw [FiniteKernel.map_pi _ _ (fun _ => measurable_amap M.measurable_par 1)] at h
  have he : ∀ᵐ z ∂M.law 1, ∀ j : Outside j₀,
      (κ (plane 0 0 j z)).map (amap M.par 1) =
        M.parameterCoordinateKernel a (amap M.par 0 (plane 0 0 j z)) := by
    rw [ae_all_iff]
    intro j
    exact (show MeasurePreserving (plane 0 0 (j : I)) (M.law 1) (M.law 0) from
      ⟨measurable_plane _ _ _, M.consistent 0 0 j⟩).quasiMeasurePreserving.ae_eq_comp
      (M.shared_parameter_kernel hI a)
  have hk : HasCondDistrib
      (fun y => fun j : Outside j₀ => amap M.par 1 (planes 1 (Outside j₀) y j))
      (plane 1 0 a) (η.comap (amap M.par 1) (measurable_amap M.measurable_par 1))
      (M.law 2) := by
    refine ⟨h.aemeasurable, h.map_eq.trans (Measure.compProd_congr ?_)⟩
    rw [M.consistent 1 0 a]
    filter_upwards [he] with z hz
    change Measure.pi (fun j : Outside j₀ =>
      ((κ.comap (plane 0 (Fin.last 0) j) (measurable_plane _ _ _)).map (amap M.par 1)) z) =
      Measure.pi (fun j : Outside j₀ => M.parameterCoordinateKernel a
        (plane 0 0 j (amap M.par 1 z)))
    congr 1
    funext j
    rw [Kernel.map_apply _ (measurable_amap M.measurable_par _), Kernel.comap_apply,
      Fin.last_zero]
    exact hz j
  exact hk.comp_right

theorem parameter_geometry_outside (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a j₀ : I) :
    HasCondDistrib (planes 1 (Outside j₀)) (plane 1 0 a)
      (FiniteKernel.pi (fun j : Outside j₀ => (M.parameterCoordinateKernel a).comap
        (plane 0 0 j) (measurable_plane _ _ _))) (M.parameterLaw 2) := by
  apply ConditionalTransport.pushforward
    (show MeasurePreserving (amap M.par 2) (M.law 2) (M.parameterLaw 2) from
      ⟨measurable_amap M.measurable_par _, rfl⟩)
    (measurable_plane _ _ _) (measurable_planes _ _)
  exact columns_parameter_given_row M hM hI a j₀

theorem parameter_geometry (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a : I) (J : Finset I) (hJ : J ≠ Finset.univ) :
    HasCondDistrib (planes 1 J) (plane 1 0 a)
      (FiniteKernel.pi (fun j : J => (M.parameterCoordinateKernel a).comap
        (plane 0 0 j) (measurable_plane _ _ _))) (M.parameterLaw 2) := by
  have hex : ∃ j₀ : I, j₀ ∉ J := by
    by_contra he
    push Not at he
    exact hJ (Finset.eq_univ_iff_forall.mpr he)
  obtain ⟨j₀, hj₀⟩ := hex
  let e : J ↪ Outside j₀ :=
    ⟨fun j => ⟨j, by
      simp only [Outside, Finset.mem_erase, Finset.mem_univ, and_true]
      exact fun he => hj₀ (he ▸ j.property)⟩,
      fun _ _ he => Subtype.ext (congrArg (fun z : Outside j₀ => (z : I)) he)⟩
  have h := (parameter_geometry_outside M hM hI a j₀).comp_left
    (Measurable.of_eval (fun i => measurable_pi_apply (e i)))
  rw [FiniteKernel.pi_precomp] at h
  exact h

end ArrayObjects.Object.Rolled

namespace ConditionalScreens
variable {Ω S Z O : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  [MeasurableSpace Z] [MeasurableSpace O] [StandardBorelSpace O] [Nonempty O]

theorem joint_of_screen {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : Ω → S} {z : Ω → Z} {o : Ω → O}
    (hs : Measurable s) (hz : Measurable z) (ho : Measurable o)
    (f : Z → S) (hf : Measurable f) (hsz : s = f ∘ z)
    (κ : Kernel S Z) [IsMarkovKernel κ] (l : Kernel S O) [IsMarkovKernel l]
    (hκ : HasCondDistrib z s κ μ)
    (hl : HasCondDistrib o z (l.comap f hf) μ) :
    HasCondDistrib (fun ω => (z ω, o ω)) s (κ ×ₖ l) μ := by
  have hl' : HasCondDistrib o (fun ω => (s ω, z ω)) (l.prodMkRight Z) μ := by
    apply ConditionalTransport.recondition hz (hs.prodMk hz) ho hl
    · apply le_antisymm
      · exact ConditionalTransport.comap_le_of_factor measurable_snd rfl
      · apply ConditionalTransport.comap_le_of_factor (hf.prodMk measurable_id)
        simpa only [Function.comp_def, id_eq] using congrArg (fun v => fun ω => (v ω, z ω)) hsz
    · filter_upwards [] with ω
      change l (f (z ω)) = l (s ω)
      rw [hsz]; rfl
  have h := chain hκ hl'
  rwa [compProd_prodMkRight] at h
end ConditionalScreens

namespace ArrayObjects.Object
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma parameterLaw_consistent (n : ℕ) (a : Fin (n + 1)) (i : I) :
    (M.parameterLaw (n + 1)).map (plane n a i) = M.parameterLaw n := by
  unfold parameterLaw
  rw [Measure.map_map (measurable_plane _ _ _) (measurable_amap M.measurable_par _),
    plane_amap, ← Measure.map_map (measurable_amap M.measurable_par _)
      (measurable_plane _ _ _), M.consistent]

variable [DecidableEq I]

theorem diagonal_parameter_product (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I) (i : I) :
    HasCondDistrib (fun p => (plane 1 0 i p, plane 1 (Fin.last 1) i p))
      (plane 0 0 i ∘ plane 1 0 i)
      ((M.parameterCoordinateKernel i) ×ₖ (M.parameterCoordinateKernel i))
      (M.parameterLaw 2) := by
  have hproper : ({i} : Finset I) ≠ Finset.univ := by
    intro he
    have hc := congrArg Finset.card he
    simp only [Finset.card_singleton, Finset.card_univ] at hc
    omega
  have hcol := (Rolled.parameter_geometry M hM hI i {i} hproper).comp_left
    (measurable_pi_apply (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset I)))
  rw [FiniteKernel.map_eval] at hcol
  have hc : HasCondDistrib (id : Arr I M.U 1 → Arr I M.U 1) (plane 0 0 i)
      (M.parameterCoordinateKernel i) (M.parameterLaw 1) :=
    ⟨((measurable_plane _ _ _).prodMk measurable_id).aemeasurable,
      (compProd_map_condDistrib (by fun_prop) measurable_id.aemeasurable).symm⟩
  have hrow := ConditionalTransport.pullback
    (show MeasurePreserving (plane 1 0 i) (M.parameterLaw 2) (M.parameterLaw 1) from
      ⟨measurable_plane _ _ _, M.parameterLaw_consistent 1 0 i⟩)
    (measurable_plane _ _ _) hc
  exact ConditionalScreens.joint_of_screen
    (s := plane 0 0 i ∘ plane 1 0 i) (z := plane 1 0 i) (o := plane 1 (Fin.last 1) i)
    ((measurable_plane _ _ _).comp (measurable_plane _ _ _))
    (measurable_plane _ _ _) (measurable_plane _ _ _)
    (plane 0 0 i) (measurable_plane _ _ _) rfl
    (M.parameterCoordinateKernel i) (M.parameterCoordinateKernel i) hrow hcol

end ArrayObjects.Object

namespace FiniteKernel
variable {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem pi_split {S T W : Finset ι} (hS : S ⊆ W) (hT : T ⊆ W)
    (hST : Disjoint S T) (κ : ι → Kernel X Y) [∀ i, IsMarkovKernel (κ i)] :
    (pi (fun i : W => κ i)).map
      (fun y => ((fun i : S => y ⟨i, hS i.property⟩), (fun i : T => y ⟨i, hT i.property⟩))) =
      (pi (fun i : S => κ i)) ×ₖ (pi (fun i : T => κ i)) := by
  let e : S ⊕ T ↪ W := ⟨Sum.elim
    (fun i : S => (⟨i, hS i.property⟩ : W))
    (fun i : T => (⟨i, hT i.property⟩ : W)), by
      intro a b hab
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (Subtype.ext (congrArg (fun z : W => (z : ι)) hab))
        | inr b =>
          have he : (a : ι) = b := congrArg (fun z : W => (z : ι)) hab
          exact False.elim (Finset.disjoint_left.mp hST a.property (he ▸ b.property))
      | inr a =>
        cases b with
        | inl b =>
          have he : (a : ι) = b := congrArg (fun z : W => (z : ι)) hab
          exact False.elim (Finset.disjoint_left.mp hST b.property (he ▸ a.property))
        | inr b => exact congrArg Sum.inr (Subtype.ext (congrArg (fun z : W => (z : ι)) hab))⟩
  ext x : 1
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply]
  change (Measure.pi (fun i : W => κ i x)).map _ =
    (Measure.pi (fun i : S => κ i x)).prod (Measure.pi (fun i : T => κ i x))
  have he := measure_pi_precomp (fun i : W => κ i x) e
  have hh := (measurePreserving_sumPiEquivProdPi (fun i : S ⊕ T => κ (e i) x)).map_eq
  rw [← he, Measure.map_map (MeasurableEquiv.sumPiEquivProdPi (fun _ : S ⊕ T => Y)).measurable
    (Measurable.of_eval (fun i => measurable_pi_apply (e i)))] at hh
  exact hh
end FiniteKernel

namespace ConditionalReveal
variable {ι Ω X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y]

theorem disjoint_families (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → X) (y : ι → Ω → Y)
    (κ : ι → Kernel X Y) [∀ i, IsMarkovKernel (κ i)]
    {S T W : Finset ι} (hS : S ⊆ W) (hT : T ⊆ W) (hST : Disjoint S T)
    (h : HasCondDistrib (fun ω => fun i : W => y i ω) E
      (FiniteKernel.pi (fun i : W => κ i)) μ) :
    HasCondDistrib (fun ω => fun i : T => y i ω)
      (fun ω => (E ω, fun i : S => y i ω))
      ((FiniteKernel.pi (fun i : T => κ i)).prodMkRight (S → Y)) μ := by
  have hh := h.comp_left (show Measurable (fun z : W → Y =>
      ((fun i : S => z ⟨i, hS i.property⟩), (fun i : T => z ⟨i, hT i.property⟩))) from by fun_prop)
  rw [FiniteKernel.pi_split hS hT hST κ, ← ConditionalScreens.compProd_prodMkRight] at hh
  exact hh.of_compProd
end ConditionalReveal

namespace ConditionalScreens
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]

theorem screened_marginal {μ : Measure Ω} [IsProbabilityMeasure μ]
    {x : Ω → X} {y : Ω → Y} {z : Ω → Z}
    (hx : Measurable x) (hy : Measurable y)
    {κ η : Kernel X Z} [IsMarkovKernel κ] [IsMarkovKernel η]
    (h : HasCondDistrib z (fun ω => (x ω, y ω)) (κ.prodMkRight Y) μ)
    (hη : HasCondDistrib z x η μ) :
    HasCondDistrib z (fun ω => (x ω, y ω)) (η.prodMkRight Y) μ := by
  have hκ : HasCondDistrib z x κ μ := h.comp_right
  have hke : κ =ᵐ[μ.map x] η :=
    (condDistrib_ae_eq_of_measure_eq_compProd hκ.aemeasurable_fst hκ.aemeasurable_snd hκ.map_eq).symm.trans
      (condDistrib_ae_eq_of_measure_eq_compProd hη.aemeasurable_fst hη.aemeasurable_snd hη.map_eq)
  refine ⟨h.aemeasurable, h.map_eq.trans (Measure.compProd_congr ?_)⟩
  have hf : (μ.map (fun ω => (x ω, y ω))).map Prod.fst = μ.map x := by
    rw [Measure.map_map measurable_fst (hx.prodMk hy)]
    rfl
  rw [← hf] at hke
  exact ae_of_ae_map measurable_fst.aemeasurable hke
end ConditionalScreens

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

abbrev ParentData (R : Finset I) (n : ℕ) :=
  Arr I M.U (n + 2) × (R → Arr I M.Y (n + 1))

def parentData (R : Finset I) (n : ℕ) (y : Arr I M.Y (n + 2)) : ParentData M R n :=
  (amap M.par (n + 2) y, parents M R (n + 1) y)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_parentData (R : Finset I) (n : ℕ) :
    Measurable (parentData M R n) :=
  (measurable_amap M.measurable_par _).prodMk (measurable_parents M R _)

def columnKernel (R : Finset I) (n : ℕ) (j : I) :
    Kernel (ParentData M R n) (Arr I M.Y (n + 1)) :=
  ((ownPosterior M R n).map (roll n).symm).comap
    (plane n (Fin.last n) j ∘ (parameterEquiv M R (n + 1)).symm)
    ((measurable_plane _ _ _).comp (parameterEquiv M R (n + 1)).symm.measurable)
instance columnKernel_markov (R : Finset I) (n : ℕ) (j : I) :
    IsMarkovKernel (columnKernel M R n j) := by
  unfold columnKernel
  have : IsMarkovKernel ((ownPosterior M R n).map (roll n).symm) :=
    Kernel.IsMarkovKernel.map _ (roll n).symm.measurable
  infer_instance

theorem columns_with_parents (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I) (n : ℕ)
    (J : Finset I) (hJ : J ≠ Finset.univ) :
    HasCondDistrib (planes (n + 1) J) (parentData M R n)
      (FiniteKernel.pi (fun j : J => columnKernel M R n j)) (M.law (n + 2)) := by
  have hi : ∀ S : Finset I, S ⊂ R → IsConditional M S := by
    intro S hS
    apply isConditional M hM S
    have hc := Finset.card_lt_card hS
    omega
  have hc := proper_conditional M hM R hR hi n J hJ
  have hp := ConditionalTransport.pullback
    (show MeasurePreserving (roll (Y := M.Y) (n + 1)) (M.law (n + 2)) (law M (n + 1)) from
      ⟨(roll (n + 1)).measurable, rfl⟩)
    (measurable_amap (measurable_parameter M R) _) hc
  have hd := hp.measurableEquiv_comp_right (parameterEquiv M R (n + 1))
  have h := hd.comp_left (Measurable.of_eval (fun j : J =>
    (roll n).symm.measurable.comp (measurable_pi_apply j)))
  have ho : (fun z : J → Arr I (State M) n => fun j => (roll n).symm (z j)) ∘
      planes n J ∘ roll (n + 1) = planes (n + 1) J := by
    rw [planes_roll]
    funext y j
    exact (roll n).symm_apply_apply _
  change HasCondDistrib
    ((fun z : J → Arr I (State M) n => fun j => (roll n).symm (z j)) ∘
      planes n J ∘ roll (n + 1))
    (parameterEquiv M R (n + 1) ∘ amap (parameter M R) (n + 1) ∘ roll (n + 1))
    _ (M.law (n + 2)) at h
  rw [ho, parameterEquiv_observation] at h
  change HasCondDistrib (planes (n + 1) J) (parentData M R n) _ (M.law (n + 2)) at h
  convert h using 1
  ext p : 1
  rw [Kernel.map_apply _ (Measurable.of_eval (fun j : J =>
    (roll n).symm.measurable.comp (measurable_pi_apply j)))]
  change Measure.pi (fun j : J => columnKernel M R n j p) =
    (Measure.pi (fun j : J => ownPosterior M R n
      (plane n (Fin.last n) j ((parameterEquiv M R (n + 1)).symm p)))).map _
  simp only [Function.comp_def]
  rw [Measure.pi_map_pi (fun _ => (roll n).symm.measurable.aemeasurable)]
  simp only [columnKernel, Kernel.comap_apply, Function.comp_apply,
    Kernel.map_apply _ (roll n).symm.measurable]


def cells (A J : Finset I) (n : ℕ) (y : Arr I M.Y (n + 2)) : J → A → Arr I M.Y n :=
  fun j a => missingRow M n j a y
omit [DecidableEq I] in
@[fun_prop] lemma measurable_cells (A J : Finset I) (n : ℕ) : Measurable (cells M A J n) :=
  Measurable.of_eval (fun _ => Measurable.of_eval (fun _ => measurable_missingRow M _ _ _))

def rowRestrict (A J : Finset I) (n : ℕ) (y : A → Arr I M.Y (n + 1)) : J → A → Arr I M.Y n :=
  fun j a => plane n (Fin.last n) j (y a)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_rowRestrict (A J : Finset I) (n : ℕ) :
    Measurable (rowRestrict M A J n) := by
  unfold rowRestrict
  exact Measurable.of_eval (fun _ => Measurable.of_eval (fun _ =>
    (measurable_plane _ _ _).comp (measurable_pi_apply _)))

def columnRestrict (A J : Finset I) (n : ℕ) (y : J → Arr I M.Y (n + 1)) : J → A → Arr I M.Y n :=
  fun j a => plane n 0 a (y j)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_columnRestrict (A J : Finset I) (n : ℕ) :
    Measurable (columnRestrict M A J n) := by
  unfold columnRestrict
  exact Measurable.of_eval (fun _ => Measurable.of_eval (fun _ =>
    (measurable_plane _ _ _).comp (measurable_pi_apply _)))

omit [DecidableEq I] in
lemma columnRestrict_planes (A J : Finset I) (n : ℕ) :
    columnRestrict M A J n ∘ planes (n + 1) J = cells M A J n := by
  funext y j a
  exact congrFun (plane_first_last M n a j) y

def rowFamilyKernel (A : Finset I) (n : ℕ) :
    Kernel (Arr I M.U (n + 2)) (A → Arr I M.Y (n + 1)) :=
  FiniteKernel.pi (fun a : A => (M.ownKernel (n + 1)).comap
    (plane (n + 1) 0 a) (measurable_plane _ _ _))
instance rowFamilyKernel_markov (A : Finset I) (n : ℕ) :
    IsMarkovKernel (rowFamilyKernel M A n) := by unfold rowFamilyKernel; infer_instance

def groupMarginal (A J : Finset I) (n : ℕ) :
    Kernel (Arr I M.U (n + 2)) (J → A → Arr I M.Y n) :=
  (rowFamilyKernel M A n).map (rowRestrict M A J n)
instance groupMarginal_markov (A J : Finset I) (n : ℕ) :
    IsMarkovKernel (groupMarginal M A J n) :=
  Kernel.IsMarkovKernel.map _ (measurable_rowRestrict M A J n)

theorem group_marginal_with_parents (hM : M.IsSaturated) (P A J : Finset I)
    (hPA : Disjoint P A) (hproper : P ∪ A ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (cells M A J n) (parentData M P n)
      ((groupMarginal M A J n).prodMkRight (P → Arr I M.Y (n + 1))) (M.law (n + 2)) := by
  have h := ConditionalReveal.disjoint_families (M.law (n + 2)) (amap M.par (n + 2))
    (fun a => plane (n + 1) 0 a)
    (fun a => (M.ownKernel (n + 1)).comap (plane (n + 1) 0 a) (measurable_plane _ _ _))
    Finset.subset_union_left Finset.subset_union_right hPA
    (rows_conditional M hM (P ∪ A) hproper n)
  have hh := h.comp_left (measurable_rowRestrict M A J n)
  rw [Kernel.map_prodMkRight] at hh
  exact hh

theorem group_intermediate_marginal (hM : M.IsSaturated) (P A C J : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A)
    (hproper : P ∪ A ≠ Finset.univ) (hCJ : Disjoint C J) (hcols : C ∪ J ≠ Finset.univ)
    (n : ℕ) :
    HasCondDistrib (cells M A J n)
      (fun y => (parentData M P n y, planes (n + 1) C y))
      (((groupMarginal M A J n).prodMkRight (P → Arr I M.Y (n + 1))).prodMkRight
        (C → Arr I M.Y (n + 1))) (M.law (n + 2)) := by
  have h := ConditionalReveal.disjoint_families (M.law (n + 2)) (parentData M P n)
    (fun j => plane (n + 1) (Fin.last (n + 1)) j) (columnKernel M P n)
    Finset.subset_union_left Finset.subset_union_right hCJ
    (columns_with_parents M hM P hP n (C ∪ J) hcols)
  have hk := h.comp_left (measurable_columnRestrict M A J n)
  rw [Kernel.map_prodMkRight] at hk
  change HasCondDistrib (columnRestrict M A J n ∘ planes (n + 1) J)
    (fun y => (parentData M P n y, planes (n + 1) C y))
    (((FiniteKernel.pi (fun j : J => columnKernel M P n j)).map
      (columnRestrict M A J n)).prodMkRight (C → Arr I M.Y (n + 1))) (M.law (n + 2)) at hk
  rw [columnRestrict_planes] at hk
  have : IsMarkovKernel ((FiniteKernel.pi (fun j : J => columnKernel M P n j)).map
      (columnRestrict M A J n)) := Kernel.IsMarkovKernel.map _ (measurable_columnRestrict M A J n)
  exact ConditionalScreens.screened_marginal (measurable_parentData M P n)
    (measurable_planes _ _) hk (group_marginal_with_parents M hM P A J hPA hproper n)


abbrev GroupData (A C : Finset I) (n : ℕ) :=
  Arr I M.U (n + 2) × (C → A → Arr I M.Y n)
abbrev WholeGroupData (P C : Finset I) (n : ℕ) :=
  ParentData M P n × (C → Arr I M.Y (n + 1))

def groupData (A C : Finset I) (n : ℕ) (y : Arr I M.Y (n + 2)) : GroupData M A C n :=
  (amap M.par (n + 2) y, cells M A C n y)
def wholeGroupData (P C : Finset I) (n : ℕ) (y : Arr I M.Y (n + 2)) : WholeGroupData M P C n :=
  (parentData M P n y, planes (n + 1) C y)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_groupData (A C : Finset I) (n : ℕ) :
    Measurable (groupData M A C n) :=
  (measurable_amap M.measurable_par _).prodMk (measurable_cells M A C n)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_wholeGroupData (P C : Finset I) (n : ℕ) :
    Measurable (wholeGroupData M P C n) :=
  (measurable_parentData M P n).prodMk (measurable_planes _ _)

def groupSelect (P A C : Finset I) (n : ℕ) (p : WholeGroupData M P C n) : GroupData M A C n :=
  (p.1.1, columnRestrict M A C n p.2)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_groupSelect (P A C : Finset I) (n : ℕ) :
    Measurable (groupSelect M P A C n) :=
  (measurable_fst.comp measurable_fst).prodMk ((measurable_columnRestrict M A C n).comp measurable_snd)
omit [DecidableEq I] in
lemma groupSelect_observation (P A C : Finset I) (n : ℕ) :
    groupSelect M P A C n ∘ wholeGroupData M P C n = groupData M A C n := by
  funext y
  apply Prod.ext
  · rfl
  · exact congrFun (columnRestrict_planes M A C n) y

def revealParent (P : Finset I) (n : ℕ) (j : I) (p : RevealData M P n j) : ParentData M P n :=
  parameterEquiv M P (n + 1) (revealToRoll M P n j p).1
@[fun_prop] lemma measurable_revealParent (P : Finset I) (n : ℕ) (j : I) :
    Measurable (revealParent M P n j) :=
  (parameterEquiv M P (n + 1)).measurable.comp
    (measurable_fst.comp (measurable_revealToRoll M P n j))
lemma revealParent_observation (P : Finset I) (n : ℕ) (j : I) :
    revealParent M P n j ∘ revealData M P n j = parentData M P n := by
  change (parameterEquiv M P (n + 1) ∘ Prod.fst) ∘
    (revealToRoll M P n j ∘ revealData M P n j) = _
  rw [revealToRoll_observation]
  exact parameterEquiv_observation M P (n + 1)

def revealSelect (P A C J : Finset I) (n : ℕ) (j : I)
    (hC : C ⊆ Outside j) (hJ : J ⊆ Outside j) (p : RevealData M P n j) :
    WholeGroupData M P C n × (J → A → Arr I M.Y n) :=
  ((revealParent M P n j p, fun c => p.1.2 ⟨c, hC c.property⟩),
    fun k a => plane n 0 a (p.1.2 ⟨k, hJ k.property⟩))
@[fun_prop] lemma measurable_revealSelect (P A C J : Finset I) (n : ℕ) (j : I)
    (hC : C ⊆ Outside j) (hJ : J ⊆ Outside j) :
    Measurable (revealSelect M P A C J n j hC hJ) := by
  unfold revealSelect
  exact ((measurable_revealParent M P n j).prodMk (by fun_prop)).prodMk (by fun_prop)
lemma revealSelect_observation (P A C J : Finset I) (n : ℕ) (j : I)
    (hC : C ⊆ Outside j) (hJ : J ⊆ Outside j) :
    revealSelect M P A C J n j hC hJ ∘ revealData M P n j =
      fun y => (wholeGroupData M P C n y, cells M A J n y) := by
  funext y
  apply Prod.ext
  · apply Prod.ext
    · exact congrFun (revealParent_observation M P n j) y
    · rfl
  · funext k a
    exact congrFun (plane_first_last M n a k) y

def groupLastData (A C J : Finset I) (n : ℕ) (j : I) (hCJ : C ∪ J = Outside j)
    (a : A) (p : GroupData M A C n × (J → A → Arr I M.Y n)) : OldData M n j :=
  (plane (n + 1) 0 a p.1.1, fun k =>
    if h : (k : I) ∈ C then p.1.2 ⟨k, h⟩ a else
      p.2 ⟨k, (Finset.mem_union.mp (hCJ.symm ▸ k.property)).resolve_left h⟩ a)
@[fun_prop] lemma measurable_groupLastData (A C J : Finset I) (n : ℕ) (j : I)
    (hCJ : C ∪ J = Outside j) (a : A) : Measurable (groupLastData M A C J n j hCJ a) := by
  unfold groupLastData
  apply Measurable.prodMk (by fun_prop)
  apply Measurable.of_eval
  intro k
  split_ifs <;> fun_prop

def groupLastKernel (A C J : Finset I) (n : ℕ) (j : I) (hCJ : C ∪ J = Outside j) :
    Kernel (GroupData M A C n × (J → A → Arr I M.Y n)) (A → Arr I M.Y n) :=
  FiniteKernel.pi (fun a =>
    (condDistrib (plane n (Fin.last n) j) (oldData M n j) (M.law (n + 1))).comap
      (groupLastData M A C J n j hCJ a) (measurable_groupLastData M A C J n j hCJ a))
instance groupLastKernel_markov (A C J : Finset I) (n : ℕ) (j : I)
    (hCJ : C ∪ J = Outside j) : IsMarkovKernel (groupLastKernel M A C J n j hCJ) := by
  unfold groupLastKernel
  infer_instance

def wholeLastSelect (P A C J : Finset I) (n : ℕ)
    (p : WholeGroupData M P C n × (J → A → Arr I M.Y n)) :
    GroupData M A C n × (J → A → Arr I M.Y n) :=
  (groupSelect M P A C n p.1, p.2)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_wholeLastSelect (P A C J : Finset I) (n : ℕ) :
    Measurable (wholeLastSelect M P A C J n) :=
  ((measurable_groupSelect M P A C n).comp measurable_fst).prodMk measurable_snd

theorem grouped_missing_after_retain (hM : M.IsSaturated) (P A C J : Finset I)
    (hPA : Disjoint P A) (hcard : P.card + A.card + 1 ≤ Fintype.card I)
    (n : ℕ) (j : I) (hCJ : C ∪ J = Outside j) :
    HasCondDistrib (fun y => fun a : A => missingRow M n j a y)
      (fun y => (wholeGroupData M P C n y, cells M A J n y))
      ((groupLastKernel M A C J n j hCJ).comap (wholeLastSelect M P A C J n)
        (measurable_wholeLastSelect M P A C J n)) (M.law (n + 2)) := by
  have hC : C ⊆ Outside j := hCJ ▸ Finset.subset_union_left
  have hJ : J ⊆ Outside j := hCJ ▸ Finset.subset_union_right
  have h := grouped_single_missing M hM P A hPA hcard n j
  have he : (FiniteKernel.pi (fun a : A => (rowKernel M n j a).prodMkRight (P → Arr I M.Y n))) =
      (((groupLastKernel M A C J n j hCJ).comap (wholeLastSelect M P A C J n)
        (measurable_wholeLastSelect M P A C J n)).comap
          (revealSelect M P A C J n j hC hJ) (measurable_revealSelect M P A C J n j hC hJ)) := by
    ext p : 1
    change Measure.pi _ = Measure.pi _
    congr 1
    funext a
    change (condDistrib _ _ _) (rowData M n j a p.1) =
      (condDistrib _ _ _) (groupLastData M A C J n j hCJ a
        (wholeLastSelect M P A C J n (revealSelect M P A C J n j hC hJ p)))
    congr 1
    apply Prod.ext
    · funext v
      simp [groupLastData, wholeLastSelect, groupSelect, revealSelect, rowData,
        revealParent, parameterEquiv, revealToRoll, plane, Fin.insertNth_zero']
    · funext k
      simp only [groupLastData, wholeLastSelect, groupSelect, columnRestrict, revealSelect, rowData]
      split_ifs <;> rfl
  rw [he] at h
  have hh := h.comp_right
  rw [revealSelect_observation] at hh
  exact hh

end ArrayObjects.Object.Rolled

namespace ConditionalScreens
variable {Ω D E Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace D]
  [MeasurableSpace E] [MeasurableSpace Y] [MeasurableSpace Z]

lemma compProd_comap (κ : Kernel E Y) (η : Kernel (E × Y) Z)
    [IsMarkovKernel κ] [IsMarkovKernel η] (f : D → E) (hf : Measurable f) :
    κ.comap f hf ⊗ₖ η.comap (Prod.map f id) (hf.prodMap measurable_id) =
      (κ ⊗ₖ η).comap f hf := by
  ext d s hs
  rw [Kernel.compProd_apply hs]
  change (∫⁻ y, η (f d, y) (Prod.mk y ⁻¹' s) ∂κ (f d)) = (κ ⊗ₖ η) (f d) s
  exact (Kernel.compProd_apply hs κ η (f d)).symm

theorem canonical_screen [StandardBorelSpace Y] [Nonempty Y]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {y : Ω → Y} {d : Ω → D}
    (hd : Measurable d) (f : D → E) (hf : Measurable f)
    {κ : Kernel E Y} [IsMarkovKernel κ]
    (h : HasCondDistrib y d (κ.comap f hf) μ) :
    HasCondDistrib y d ((condDistrib y (f ∘ d) μ).comap f hf) μ := by
  have hκ := h.comp_right
  have he : κ =ᵐ[μ.map (f ∘ d)] condDistrib y (f ∘ d) μ :=
    (condDistrib_ae_eq_of_measure_eq_compProd hκ.aemeasurable_fst hκ.aemeasurable_snd hκ.map_eq).symm
  rw [← Measure.map_map hf hd] at he
  refine ⟨h.aemeasurable, h.map_eq.trans (Measure.compProd_congr ?_)⟩
  exact ae_of_ae_map hf.aemeasurable he
end ConditionalScreens

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def joinOutput (A J : Finset I) (n : ℕ) (j : I)
    (p : (J → A → Arr I M.Y n) × (A → Arr I M.Y n)) :
    ↥(insert j J) → A → Arr I M.Y n := fun k =>
  if h : (k : I) = j then p.2 else p.1 ⟨k, (Finset.mem_insert.mp k.property).resolve_left h⟩
@[fun_prop] lemma measurable_joinOutput (A J : Finset I) (n : ℕ) (j : I) :
    Measurable (joinOutput M A J n j) := by
  unfold joinOutput
  apply Measurable.of_eval
  intro k
  split_ifs <;> fun_prop
lemma joinOutput_observation (A J : Finset I) (n : ℕ) (j : I) :
    joinOutput M A J n j ∘ (fun y => (cells M A J n y, fun a : A => missingRow M n j a y)) =
      cells M A (insert j J) n := by
  funext y k a
  simp only [Function.comp_apply, joinOutput, cells]
  split_ifs with h
  · simp [h]
  · rfl

theorem grouped_cell_locality (hM : M.IsSaturated) (P A C J : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A)
    (hcard : P.card + A.card + 1 ≤ Fintype.card I)
    (hproper : P ∪ A ≠ Finset.univ) (hdisj : Disjoint C J)
    (n : ℕ) (j : I) (hCJ : C ∪ J = Outside j) :
    HasCondDistrib (cells M A (insert j J) n) (wholeGroupData M P C n)
      ((condDistrib (cells M A (insert j J) n) (groupData M A C n) (M.law (n + 2))).comap
        (groupSelect M P A C n) (measurable_groupSelect M P A C n)) (M.law (n + 2)) := by
  have hcols : C ∪ J ≠ Finset.univ := by
    rw [hCJ]
    simp [Outside]
  have hW := group_intermediate_marginal M hM P A C J hP hPA hproper hdisj hcols n
  have hZ := grouped_missing_after_retain M hM P A C J hPA hcard n j hCJ
  have h := ConditionalScreens.chain hW hZ
  have hke : (((groupMarginal M A J n).prodMkRight (P → Arr I M.Y (n + 1))).prodMkRight
        (C → Arr I M.Y (n + 1))) =
      ((groupMarginal M A J n).prodMkRight (C → A → Arr I M.Y n)).comap
        (groupSelect M P A C n) (measurable_groupSelect M P A C n) := by
    ext p : 1
    rfl
  rw [hke] at h
  change HasCondDistrib _ (wholeGroupData M P C n)
    (((groupMarginal M A J n).prodMkRight (C → A → Arr I M.Y n)).comap
      (groupSelect M P A C n) (measurable_groupSelect M P A C n) ⊗ₖ
      (groupLastKernel M A C J n j hCJ).comap (Prod.map (groupSelect M P A C n) id)
        ((measurable_groupSelect M P A C n).prodMap measurable_id)) _ at h
  rw [ConditionalScreens.compProd_comap] at h
  have hh := h.comp_left (measurable_joinOutput M A J n j)
  rw [joinOutput_observation, ← Kernel.comap_map_comm _ _ (measurable_joinOutput M A J n j)] at hh
  have : IsMarkovKernel
      (((groupMarginal M A J n).prodMkRight (C → A → Arr I M.Y n) ⊗ₖ
        groupLastKernel M A C J n j hCJ).map (joinOutput M A J n j)) :=
    Kernel.IsMarkovKernel.map _ (measurable_joinOutput M A J n j)
  have hv := ConditionalScreens.canonical_screen (measurable_wholeGroupData M P C n)
    (groupSelect M P A C n) (measurable_groupSelect M P A C n) hh
  rw [groupSelect_observation] at hv
  exact hv

end ArrayObjects.Object.Rolled
end

section
open MeasureTheory ProbabilityTheory
variable {Ω U : Type*} [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace.CountablyGenerated Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (u : Ω → U) (hu : Measurable u)
  (κ : Kernel U Ω) [IsMarkovKernel κ]

include hu in

lemma conditional_kernel_equivariant
    (hκ : HasCondDistrib id u κ μ) (T : Ω ≃ᵐ Ω) (S : U ≃ᵐ U)
    (hT : MeasurePreserving T μ μ) (hfactor : u ∘ T = S ∘ u) :
    κ.map T =ᵐ[μ.map u] κ.comap S S.measurable := by
  have h₁ : HasCondDistrib T (u ∘ T) κ μ := by
    refine ⟨(hu.comp T.measurable |>.prodMk T.measurable).aemeasurable,?_⟩
    have hp : μ.map (u ∘ T) = μ.map u := by
      rw [←Measure.map_map hu T.measurable,hT.map_eq]
    rw [hp]
    calc
      μ.map (fun x => (u (T x),T x)) =
          (μ.map T).map (fun x => (u x,x)) := by
        exact (Measure.map_map (μ := μ) (hu.prodMk measurable_id) T.measurable).symm
      _ = μ.map u ⊗ₘ κ := by rw [hT.map_eq]; exact hκ.map_eq
  have h₂ := h₁.measurableEquiv_comp_right S.symm
  have hc : S.symm ∘ (u ∘ T) = u := by
    rw [hfactor]
    funext x
    exact S.symm_apply_apply _
  rw [hc] at h₂
  have h₃ := hκ.comp_left T.measurable
  exact Kernel.ae_eq_of_compProd_eq (h₃.map_eq.symm.trans h₂.map_eq)
end

namespace ArrayObjects
open MeasureTheory ProbabilityTheory
universe u
variable {I Y Z : Type u} [MeasurableSpace Y] [MeasurableSpace Z]

def amapEquiv (E : Y ≃ᵐ Z) (n : ℕ) : Arr I Y n ≃ᵐ Arr I Z n where
  toFun := amap E n
  invFun := amap E.symm n
  left_inv x := by funext a; exact E.symm_apply_apply _
  right_inv x := by funext a; exact E.apply_symm_apply _
  measurable_toFun := measurable_amap E.measurable n
  measurable_invFun := measurable_amap E.symm.measurable n

namespace Object
variable [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T} (M : Object I base)

lemma parameterLaw_invariant (n : ℕ) :
    MeasurePreserving (amap M.timeU n) (M.parameterLaw n) (M.parameterLaw n) := by
  refine ⟨measurable_amap M.timeU.measurable n,?_⟩
  change ((M.law n).map (amap M.par n)).map (amap M.timeU n) = _
  rw [Measure.map_map (measurable_amap M.timeU.measurable _) (measurable_amap M.measurable_par _)]
  have he : amap (I := I) M.timeU n ∘ amap M.par n = amap M.par n ∘ amap M.timeY n := by
    rw [←amap_comp,←amap_comp,M.time_par]
  rw [he,←Measure.map_map (measurable_amap M.measurable_par _) (measurable_amap M.timeY.measurable _),
    (M.invariant n).map_eq]
  rfl

lemma ownKernel_time_equivariant (n : ℕ) :
    (M.ownKernel n).map (amap M.timeY n) =ᵐ[M.parameterLaw n]
      (M.ownKernel n).comap (amap M.timeU n) (measurable_amap M.timeU.measurable n) := by
  apply conditional_kernel_equivariant (M.law n) (amap M.par n)
    (measurable_amap M.measurable_par _) (M.ownKernel n) (M.ownKernel_conditional n)
    (amapEquiv M.timeY n) (amapEquiv M.timeU n) (M.invariant n)
  change amap M.par n ∘ amap M.timeY n = amap M.timeU n ∘ amap M.par n
  rw [←amap_comp,←amap_comp,M.time_par]

lemma ownKernel_time_preserving (n : ℕ) :
    ∀ᵐ p ∂M.parameterLaw n, MeasurePreserving (amap M.timeY n)
      (M.ownKernel n p) (M.ownKernel n (amap M.timeU n p)) := by
  filter_upwards [M.ownKernel_time_equivariant n] with p hp
  exact ⟨measurable_amap M.timeY.measurable n,
    (Kernel.map_apply _ (measurable_amap M.timeY.measurable n) _).symm.trans hp⟩
end Object
end ArrayObjects

open MeasureTheory ProbabilityTheory

namespace ConditionalFibres
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [StandardBorelSpace Y]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {u : Ω → U} {x : Ω → X} {y : Ω → Y}
  {η : Kernel U Ω} [IsMarkovKernel η] {κ : Kernel (U × X) Y} [IsMarkovKernel κ]

omit [StandardBorelSpace X] [StandardBorelSpace Y] [IsProbabilityMeasure μ] [IsMarkovKernel κ] in
lemma chain {α : Kernel U X} [IsMarkovKernel α]
    (hx : HasCondDistrib x u α μ)
    (hy : HasCondDistrib y (fun ω => (u ω, x ω)) κ μ) :
    HasCondDistrib (fun ω => (x ω, y ω)) u (α ⊗ₖ κ) μ := by
  refine ⟨hx.aemeasurable_fst.prodMk
    (hx.aemeasurable_snd.prodMk hy.aemeasurable_snd), ?_⟩
  calc
    μ.map (fun ω => (u ω, x ω, y ω)) =
        (μ.map (fun ω => ((u ω, x ω), y ω))).map MeasurableEquiv.prodAssoc := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hy.aemeasurable]
      rfl
    _ = ((μ.map u ⊗ₘ α) ⊗ₘ κ).map MeasurableEquiv.prodAssoc := by
      rw [hy.map_eq, hx.map_eq]
    _ = μ.map u ⊗ₘ (α ⊗ₖ κ) := Measure.compProd_assoc'

theorem disintegrate (hx : Measurable x) (hy : Measurable y)
    (hη : HasCondDistrib id u η μ)
    (hκ : HasCondDistrib y (fun ω => (u ω, x ω)) κ μ) :
    ∀ᵐ a ∂μ.map u, HasCondDistrib y x (κ.sectR a) (η a) := by
  let : IsMarkovKernel (η.map x) := Kernel.IsMarkovKernel.map η hx
  let : IsMarkovKernel (η.map (fun ω => (x ω, y ω))) :=
    Kernel.IsMarkovKernel.map η (hx.prodMk hy)
  have hpair := chain (hη.comp_left hx) hκ
  have hother := hη.comp_left (hx.prodMk hy)
  have he : η.map (fun ω => (x ω, y ω)) =ᵐ[μ.map u] (η.map x) ⊗ₖ κ :=
    Kernel.ae_eq_of_compProd_eq (hother.map_eq.symm.trans hpair.map_eq)
  filter_upwards [he] with a ha
  refine ⟨(hx.prodMk hy).aemeasurable, ?_⟩
  rw [Kernel.map_apply _ (hx.prodMk hy), Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.map_apply _ hx] at ha
  exact ha

theorem marginal (hx : Measurable x) (hη : HasCondDistrib id u η μ)
    {α : Kernel U X} [IsMarkovKernel α] (hα : HasCondDistrib x u α μ) :
    ∀ᵐ a ∂μ.map u, MeasurePreserving x (η a) (α a) := by
  let : IsMarkovKernel (η.map x) := Kernel.IsMarkovKernel.map η hx
  have he : η.map x =ᵐ[μ.map u] α :=
    Kernel.ae_eq_of_compProd_eq ((hη.comp_left hx).map_eq.symm.trans hα.map_eq)
  filter_upwards [he] with a ha
  exact ⟨hx, (Kernel.map_apply η hx a).symm.trans ha⟩

end ConditionalFibres

end Rokhlin

end

end OAI
