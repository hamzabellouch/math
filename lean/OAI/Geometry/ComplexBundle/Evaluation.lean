import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.Module

namespace OAI

noncomputable section

/-! Smooth generating sections, evaluation maps, and complex-linear bundle maps. -/

section
open scoped ContDiff
namespace Kaplansky

section
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {q : ℕ}

def tupleEvaluation (L : V →L[ℂ] W) : (Fin q → V) →L[ℂ] (Fin q → W) :=
  ContinuousLinearMap.pi (fun i => L.comp (ContinuousLinearMap.proj i))

@[simp] theorem tupleEvaluation_apply (L : V →L[ℂ] W) (v : Fin q → V) (i : Fin q) :
    tupleEvaluation L v i=L (v i) := rfl

theorem tupleEvaluation_surjective (L : V →L[ℂ] W) (hL : Function.Surjective L) :
    Function.Surjective (tupleEvaluation (q := q) L) := by
  intro w
  choose v hv using fun i => hL (w i)
  exact ⟨v,funext hv⟩

def tupleEvaluationLinear : (V →L[ℂ] W) →ₗ[ℂ] ((Fin q → V) →L[ℂ] (Fin q → W)) where
  toFun := tupleEvaluation
  map_add' L K := by ext v i; rfl
  map_smul' c L := by ext v i; rfl

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

def tupleEvaluationMap : (V →L[ℂ] W) →L[ℂ] ((Fin q → V) →L[ℂ] (Fin q → W)) :=
  tupleEvaluationLinear.toContinuousLinearMap

theorem tupleEvaluation_smooth : ContDiff ℝ ∞ (tupleEvaluation (V := V) (W := W) (q := q)) :=
  ((tupleEvaluationMap (V := V) (W := W) (q := q)).restrictScalars ℝ).contDiff

end

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem complex_smul_decomposition (c : ℂ) (v : E) :
    c • v=c.re • v+c.im • (Complex.I • v) := by
  calc
    c • v=((c.re : ℂ)+(c.im : ℂ)*Complex.I) • v := by rw [Complex.re_add_im]
    _ = _ := by rw [add_smul,mul_smul,Complex.coe_smul,Complex.coe_smul]

/-- Upgrade a real-linear map commuting with the complex structure. -/
def complexOfCommuteI (f : E →ₗ[ℝ] F) (hI : ∀ v, f (Complex.I • v)=Complex.I • f v) :
    E →ₗ[ℂ] F where
  toFun := f
  map_add' := f.map_add
  map_smul' c v := by
    rw [complex_smul_decomposition, map_add, map_smul, map_smul,hI]
    exact (complex_smul_decomposition c (f v)).symm

/-- The canonical projection from real-linear maps to complex-linear maps. -/
def realComplexPart (f : E →ₗ[ℝ] F) : E →ₗ[ℝ] F where
  toFun v := (1/2 : ℂ) • (f v-Complex.I • f (Complex.I • v))
  map_add' v w := by simp only [smul_add,map_add]; module
  map_smul' c v := by
    change (1/2 : ℂ) • (f (c • v)-Complex.I • f (Complex.I • (c • v))) = c • ((1/2 : ℂ) • (f v-Complex.I • f (Complex.I • v)))
    simp only [smul_comm Complex.I c,map_smul,← smul_sub,smul_comm (1/2 : ℂ) c]

theorem realComplexPart_commute_I (f : E →ₗ[ℝ] F) (v : E) :
    realComplexPart f (Complex.I • v)=Complex.I • realComplexPart f v := by
  change (1/2 : ℂ) • (f (Complex.I • v)-Complex.I • f (Complex.I • (Complex.I • v))) = Complex.I • ((1/2 : ℂ) • (f v-Complex.I • f (Complex.I • v)))
  rw [smul_comm Complex.I (1/2 : ℂ)]
  simp only [smul_sub,smul_smul,Complex.I_mul_I,neg_one_smul,map_neg,smul_neg,sub_neg_eq_add]
  rw [add_comm]

def complexPart (f : E →L[ℝ] F) : E →L[ℂ] F :=
  { complexOfCommuteI (realComplexPart f.toLinearMap) (realComplexPart_commute_I f.toLinearMap) with
    cont := continuous_const.smul (f.continuous.sub
      (continuous_const.smul (f.continuous.comp (continuous_const.smul continuous_id)))) }

@[simp] theorem complexPart_apply (f : E →L[ℝ] F) (v : E) :
    complexPart f v=(1/2 : ℂ) • (f v-Complex.I • f (Complex.I • v)) := rfl

theorem complexPart_restrict (f : E →L[ℂ] F) : complexPart (f.restrictScalars ℝ)=f := by
  ext v
  change (1/2 : ℂ) • (f v-Complex.I • f (Complex.I • v))=f v
  rw [map_smul,smul_smul,Complex.I_mul_I,neg_one_smul]
  module

def complexProjectionLinear : (E →L[ℝ] F) →ₗ[ℝ] (E →L[ℂ] F) where
  toFun := complexPart
  map_add' f g := by ext v; simp only [complexPart_apply,add_apply]; module
  map_smul' c f := by
    ext v
    change (1/2 : ℂ) • (c • f v-Complex.I • (c • f (Complex.I • v))) = c • ((1/2 : ℂ) • (f v-Complex.I • f (Complex.I • v)))
    simp only [smul_comm Complex.I c,← smul_sub,smul_comm (1/2 : ℂ) c]

theorem complexPart_natural
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (g : G →L[ℂ] E) (f : E →L[ℝ] F) (h : F →L[ℂ] H) :
    complexPart ((h.restrictScalars ℝ).comp (f.comp (g.restrictScalars ℝ))) =
      h.comp ((complexPart f).comp g) := by
  ext v
  change (1/2 : ℂ) • (h (f (g v))-Complex.I • h (f (g (Complex.I • v)))) =
    h ((1/2 : ℂ) • (f (g v)-Complex.I • f (Complex.I • g v)))
  simp only [map_smul,map_sub]

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

def complexProjection : (E →L[ℝ] F) →L[ℝ] (E →L[ℂ] F) :=
  complexProjectionLinear.toContinuousLinearMap

theorem complexProjection_surjective : Function.Surjective (complexProjection (E := E) (F := F)) :=
  fun f => ⟨f.restrictScalars ℝ,complexPart_restrict f⟩

theorem complexProjection_smooth : ContDiff ℝ ∞ (complexProjection (E := E) (F := F)) :=
  (complexProjection (E := E) (F := F)).contDiff

end Kaplansky

end

section
open Bundle Function Set Module
open scoped Topology Manifold ContDiff
namespace Kaplansky

section
variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace H] (I : ModelWithCorners ℝ X H)
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  [T2Space B] [CompactSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℝ F E] [ContMDiffVectorBundle ∞ F E I]

/-- A finite family of actual global smooth sections spanning every fiber.
The sections are local frame vectors multiplied by a constructed subordinate
partition of unity, so no global generation hypothesis is used. -/
theorem exists_finite_smooth_spanning_sections :
    ∃ (n : ℕ) (s : Fin n → ∀ x, E x),
      (∀ i, ContMDiff I (I.prod 𝓘(ℝ,F)) ∞ (fun x => TotalSpace.mk' F x (s i x))) ∧
      ∀ x, Submodule.span ℝ (Set.range (fun i => s i x)) = ⊤ := by
  classical
  let U (x : B) := (trivializationAt F E x).baseSet
  obtain ⟨ι, f, hf⟩ := SmoothBumpCovering.exists_isSubordinate I isClosed_univ
    (U := U) (fun x _ => (trivializationAt F E x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F E x))
  let : Fintype ι := f.fintype
  let ρ := f.toSmoothPartitionOfUnity
  have hρ := hf.toSmoothPartitionOfUnity
  let b := finBasis ℝ F
  let e (i : ι) := trivializationAt F E (f.c i)
  let s (i : ι × Fin (finrank ℝ F)) (x : B) : E x :=
    ρ i.1 x • (e i.1).symm x (b i.2)
  have hs : ∀ i, ContMDiff I (I.prod 𝓘(ℝ,F)) ∞
      (fun x => TotalSpace.mk' F x (s i x)) := by
    intro i
    apply ContMDiffOn.smul_section_of_tsupport (ρ i.1).contMDiff.contMDiffOn
      (e i.1).open_baseSet (hρ i.1)
    apply ((e i.1).contMDiffOn_section_baseSet_iff).mpr
    apply (contMDiffOn_const (c := b i.2)).congr
    intro x hx
    simp only [(e i.1).apply_mk_symm hx]
  have hspan : ∀ x, Submodule.span ℝ (Set.range (fun i => s i x)) = ⊤ := by
    intro x
    obtain ⟨i, hi⟩ := ρ.exists_pos_of_mem (mem_univ x)
    have hx : x ∈ (e i).baseSet := hρ i (subset_closure (show x ∈ support (ρ i) from ne_of_gt hi))
    let W := Submodule.span ℝ (Set.range (fun i => s i x))
    have hb : ∀ j, (e i).symm x (b j) ∈ W := by
      intro j
      have hm : s (i,j) x ∈ W := Submodule.subset_span ⟨(i,j),rfl⟩
      have := W.smul_mem ((ρ i x)⁻¹) hm
      simpa only [s, smul_smul, inv_mul_cancel₀ (ne_of_gt hi), one_smul] using this
    rw [Submodule.eq_top_iff']
    intro v
    have heq : v = ∑ j, (b.repr ((e i) ⟨x,v⟩).2 j) • (e i).symm x (b j) := by
      have h := b.sum_repr ((e i) ⟨x,v⟩).2
      have hh := congrArg ((e i).symm x) h
      rw [(e i).symm_apply_apply_mk hx] at hh
      simpa only [← (e i).symmL_apply (R := ℝ) hx, map_sum, map_smul] using hh.symm
    rw [heq]
    exact W.sum_mem (fun j _ => W.smul_mem _ (hb j))
  let a := Fintype.equivFin (ι × Fin (finrank ℝ F))
  refine ⟨Fintype.card (ι × Fin (finrank ℝ F)),fun j => s (a.symm j),fun j => hs _,?_⟩
  intro x
  have hr : Set.range (fun j => s (a.symm j) x) = Set.range (fun i => s i x) := by
    ext v
    constructor
    · rintro ⟨j,rfl⟩; exact ⟨a.symm j,rfl⟩
    · rintro ⟨i,rfl⟩; exact ⟨a i,by simp⟩
  rw [hr]
  exact hspan x

end

section Algebra
variable {B : Type*} {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  {n : ℕ}
/-- Evaluation of the complex coefficients of a finite family of sections. -/
def sectionEvaluation (s : Fin n → ∀ x, E x) (x : B) : (Fin n → ℂ) →ₗ[ℂ] E x where
  toFun c := ∑ i, c i • s i x
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

@[simp] theorem sectionEvaluation_single (s : Fin n → ∀ x, E x) (x : B) (i : Fin n) :
    sectionEvaluation s x (Pi.single i 1) = s i x := by
  classical
  simp [sectionEvaluation, Pi.single_apply]

/-- Real spanning suffices for surjectivity of the complex-linear evaluation. -/
theorem sectionEvaluation_surjective [∀ x, Module ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
    (s : Fin n → ∀ x, E x)
    (hs : ∀ x, Submodule.span ℝ (Set.range (fun i => s i x)) = ⊤) (x : B) :
    Function.Surjective (sectionEvaluation s x) := by
  have h : Submodule.span ℝ (Set.range (fun i => s i x)) ≤
      (LinearMap.range (sectionEvaluation s x)).restrictScalars ℝ := by
    apply Submodule.span_le.mpr
    rintro v ⟨i,rfl⟩
    exact ⟨Pi.single i 1,sectionEvaluation_single s x i⟩
  rw [hs x] at h
  intro v
  exact h (Submodule.mem_top : v ∈ (⊤ : Submodule ℝ (E x)))
end Algebra

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace H] (I : ModelWithCorners ℝ X H)
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  [T2Space B] [CompactSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℂ F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ∞ F E I]

/-- The evaluation family in an actual bundle frame, with complex parameter
space and real-smooth dependence on the base. -/
def sectionEvaluationCoordinates {n : ℕ} (s : Fin n → ∀ x, E x)
    (e : Trivialization F (π F E)) (x : B) : (Fin n → ℂ) →L[ℂ] F :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight ((e ⟨x,s i x⟩).2)

omit [T2Space B] [CompactSpace B] [FiniteDimensional ℂ F]
  [∀ x, IsScalarTower ℝ ℂ (E x)] [VectorBundle ℝ F E] [∀ x, Module ℝ (E x)] in
theorem sectionEvaluationCoordinates_apply {n : ℕ} (s : Fin n → ∀ x, E x)
    (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    (x : B) (hx : x ∈ e.baseSet) (c : Fin n → ℂ) :
    sectionEvaluationCoordinates E s e x c = (e ⟨x,sectionEvaluation s x c⟩).2 := by
  change (∑ i, (ContinuousLinearMap.proj i).smulRight ((e ⟨x,s i x⟩).2)) c =
    ((e.linear ℂ hx).mk' _) (∑ i, c i • s i x)
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, map_sum, map_smul, IsLinearMap.mk'_apply]

omit [FiniteDimensional ℝ X] [IsManifold I ∞ B] [T2Space B] [CompactSpace B]
  [FiniteDimensional ℂ F] [∀ x, IsScalarTower ℝ ℂ (E x)] [VectorBundle ℂ F E]
  [∀ x, Module ℂ (E x)] in
theorem sectionEvaluationCoordinates_smooth {n : ℕ} (s : Fin n → ∀ x, E x)
    (hs : ∀ i, ContMDiff I (I.prod 𝓘(ℝ,F)) ∞ (fun x => TotalSpace.mk' F x (s i x)))
    (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    ContMDiffOn I 𝓘(ℝ,(Fin n → ℂ) →L[ℂ] F) ∞
      (sectionEvaluationCoordinates E s e) e.baseSet := by
  apply contMDiffOn_finsetSum
  intro i _
  have hc := ((e.contMDiffOn_section_baseSet_iff).mp (hs i).contMDiffOn)
  exact (((ContinuousLinearMap.smulRightL ℂ (Fin n → ℂ) F) (ContinuousLinearMap.proj i)).restrictScalars ℝ).contMDiff.comp_contMDiffOn hc

omit [T2Space B] [CompactSpace B] [FiniteDimensional ℂ F] [VectorBundle ℝ F E] in
theorem sectionEvaluationCoordinates_surjective {n : ℕ} (s : Fin n → ∀ x, E x)
    (hs : ∀ x, Submodule.span ℝ (Set.range (fun i => s i x)) = ⊤)
    (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    (x : B) (hx : x ∈ e.baseSet) :
    Function.Surjective (sectionEvaluationCoordinates E s e x) := by
  intro v
  obtain ⟨c,hc⟩ := sectionEvaluation_surjective s hs x (e.symm x v)
  refine ⟨c,?_⟩
  rw [sectionEvaluationCoordinates_apply E s e x hx, hc]
  exact congrArg Prod.snd (e.apply_mk_symm hx v)

omit [FiniteDimensional ℝ X] [IsManifold I ∞ B] [T2Space B] [CompactSpace B]
  [FiniteDimensional ℂ F] [∀ x, IsScalarTower ℝ ℂ (E x)] in
/-- Every fixed complex parameter gives an actual global smooth section. -/
theorem sectionEvaluation_smooth {n : ℕ} (s : Fin n → ∀ x, E x)
    (hs : ∀ i, ContMDiff I (I.prod 𝓘(ℝ,F)) ∞ (fun x => TotalSpace.mk' F x (s i x)))
    (c : Fin n → ℂ) :
    ContMDiff I (I.prod 𝓘(ℝ,F)) ∞ (fun x => TotalSpace.mk' F x (sectionEvaluation s x c)) := by
  intro x
  let e := trivializationAt F E x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F E x
  apply (e.contMDiffAt_section_iff hx).mpr
  have hc := ((sectionEvaluationCoordinates_smooth I E s hs e) x hx).contMDiffAt
    (e.open_baseSet.mem_nhds hx)
  have happ : ContDiff ℂ ∞ (fun L : (Fin n → ℂ) →L[ℂ] F => L c) :=
    contDiff_id.clm_apply contDiff_const
  apply (((happ.restrict_scalars ℝ).contDiffAt.contMDiffAt).comp x hc).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact (sectionEvaluationCoordinates_apply E s e y hy c).symm

/-- A constructed finite complex parameter space, with surjective evaluation
and smooth coordinate maps in every bundle frame. -/
theorem exists_finite_complex_smooth_evaluation :
    ∃ (n : ℕ) (s : Fin n → ∀ x, E x),
      (∀ i, ContMDiff I (I.prod 𝓘(ℝ,F)) ∞ (fun x => TotalSpace.mk' F x (s i x))) ∧
      (∀ x, Function.Surjective (sectionEvaluation s x)) ∧
      ∀ (e : Trivialization F (π F E)) [MemTrivializationAtlas e],
        ContMDiffOn I 𝓘(ℝ,(Fin n → ℂ) →L[ℂ] F) ∞
          (sectionEvaluationCoordinates E s e) e.baseSet ∧
        ∀ x ∈ e.baseSet, Function.Surjective (sectionEvaluationCoordinates E s e x) := by
  obtain ⟨n,s,hs,hspan⟩ := exists_finite_smooth_spanning_sections (F := F) I E
  exact ⟨n,s,hs,sectionEvaluation_surjective s hspan,fun e _ =>
    ⟨sectionEvaluationCoordinates_smooth I E s hs e,
      sectionEvaluationCoordinates_surjective E s hspan e⟩⟩

end Kaplansky

end

section
open Bundle Module Set
open scoped Topology Manifold ContDiff
namespace Kaplansky

section
variable {X H B F₁ F₂ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace H] (I : ModelWithCorners ℝ X H)
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  [T2Space B] [CompactSpace B]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [FiniteDimensional ℂ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [FiniteDimensional ℂ F₂]
  (E₁ E₂ : B → Type*)
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [∀ x, NormedAddCommGroup (E₂ x)] [∀ x, NormedSpace ℂ (E₂ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]
  [VectorBundle ℝ F₁ E₁] [VectorBundle ℂ F₁ E₁]
  [VectorBundle ℝ F₂ E₂] [VectorBundle ℂ F₂ E₂]
  [ContMDiffVectorBundle ∞ F₁ E₁ I] [ContMDiffVectorBundle ∞ F₂ E₂ I]

def complexHomCoordinates
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂]
    (s : ∀ x, E₁ x →L[ℂ] E₂ x) (x : B) : F₁ →L[ℂ] F₂ :=
  (e₂.continuousLinearMapAt ℂ x).comp ((s x).comp (e₁.symmL ℂ x))

omit [T2Space B] [CompactSpace B] [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂] in
theorem complexHomCoordinates_projected
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂]
    (s : ∀ x, E₁ x →L[ℝ] E₂ x) (x : B) (hx : x ∈ e₁.baseSet ∩ e₂.baseSet) :
    complexHomCoordinates E₁ E₂ e₁ e₂ (fun x => complexPart (s x)) x =
      complexPart (((e₁.continuousLinearMap (RingHom.id ℝ) e₂) ⟨x,s x⟩).2) := by
  have h₁ : (e₁.symmL ℂ x).restrictScalars ℝ=e₁.symmL ℝ x := by
    ext v
    change e₁.symmL ℂ x v=e₁.symmL ℝ x v
    rw [e₁.symmL_apply hx.1,e₁.symmL_apply hx.1]
  have h₂ : (e₂.continuousLinearMapAt ℂ x).restrictScalars ℝ=e₂.continuousLinearMapAt ℝ x := by
    ext v
    change e₂.continuousLinearMapAt ℂ x v=e₂.continuousLinearMapAt ℝ x v
    simp only [Trivialization.continuousLinearMapAt_apply,e₂.coe_linearMapAt_of_mem hx.2]
  have hn := complexPart_natural (e₁.symmL ℂ x) (s x) (e₂.continuousLinearMapAt ℂ x)
  rw [h₁,h₂] at hn
  exact hn.symm

omit [FiniteDimensional ℝ X] [IsManifold I ∞ B] [T2Space B] [CompactSpace B] in
theorem complexHomCoordinates_projected_smooth
    (s : ∀ x, E₁ x →L[ℝ] E₂ x)
    (hs : ContMDiff I (I.prod 𝓘(ℝ,F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x (s x)))
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂] :
    ContMDiffOn I 𝓘(ℝ,F₁ →L[ℂ] F₂) ∞
      (complexHomCoordinates E₁ E₂ e₁ e₂ (fun x => complexPart (s x)))
      (e₁.baseSet ∩ e₂.baseSet) := by
  let e := e₁.continuousLinearMap (RingHom.id ℝ) e₂
  have hc := (e.contMDiffOn_section_baseSet_iff).mp hs.contMDiffOn
  have hp := (complexProjection (E := F₁) (F := F₂)).contMDiff.comp_contMDiffOn hc
  apply hp.congr
  intro x hx
  exact complexHomCoordinates_projected E₁ E₂ e₁ e₂ s x hx

/-- Finite global Hom sections are constructed using the ordinary smooth
real Hom bundle and the canonical complex-linear projection. Evaluation is
surjective onto actual complex-linear fiber maps, and the projected sections
are real-smooth in every pair of actual complex bundle frames. -/
theorem exists_finite_smooth_complex_hom_generators :
    ∃ (n : ℕ) (s : Fin n → ∀ x, E₁ x →L[ℂ] E₂ x),
      (∀ x, Function.Surjective (sectionEvaluation s x)) ∧
      ∀ i (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
        [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂],
        ContMDiffOn I 𝓘(ℝ,F₁ →L[ℂ] F₂) ∞ (complexHomCoordinates E₁ E₂ e₁ e₂ (s i))
          (e₁.baseSet ∩ e₂.baseSet) := by
  obtain ⟨n,s,hs,hspan⟩ := exists_finite_smooth_spanning_sections
    (F := F₁ →L[ℝ] F₂) I (fun x => E₁ x →L[ℝ] E₂ x)
  let t (i : Fin n) (x : B) := complexPart (s i x)
  have ht : ∀ x, Submodule.span ℝ (Set.range (fun i => t i x))=⊤ := by
    intro x
    let P : (E₁ x →L[ℝ] E₂ x) →ₗ[ℝ] (E₁ x →L[ℂ] E₂ x) := complexProjectionLinear
    have hp : Function.Surjective P := fun f => ⟨f.restrictScalars ℝ,complexPart_restrict f⟩
    have hh := congrArg (Submodule.map P) (hspan x)
    rw [Submodule.map_span,Submodule.map_top,LinearMap.range_eq_top.mpr hp] at hh
    have he : P '' Set.range (fun i => s i x)=Set.range (fun i => t i x) := by
      ext v
      constructor
      · rintro ⟨_,⟨i,rfl⟩,rfl⟩; exact ⟨i,rfl⟩
      · rintro ⟨i,rfl⟩; exact ⟨s i x,⟨i,rfl⟩,rfl⟩
    rw [he] at hh
    exact hh
  exact ⟨n,t,sectionEvaluation_surjective t ht,fun i e₁ e₂ _ _ =>
    complexHomCoordinates_projected_smooth I E₁ E₂ (s i) (hs i) e₁ e₂⟩

end

variable {X H B F₁ F₂ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace H] (I : ModelWithCorners ℝ X H)
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  [T2Space B] [CompactSpace B]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [FiniteDimensional ℂ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [FiniteDimensional ℂ F₂]
  (E₁ E₂ : B → Type*)
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [∀ x, NormedAddCommGroup (E₂ x)] [∀ x, NormedSpace ℂ (E₂ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]
  [VectorBundle ℝ F₁ E₁] [VectorBundle ℂ F₁ E₁]
  [VectorBundle ℝ F₂ E₂] [VectorBundle ℂ F₂ E₂]
  [ContMDiffVectorBundle ∞ F₁ E₁ I] [ContMDiffVectorBundle ∞ F₂ E₂ I]

omit [T2Space B] [CompactSpace B] [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂] in
theorem realHomCoordinates_restrict
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂]
    (s : ∀ x, E₁ x →L[ℂ] E₂ x) (x : B) (hx : x ∈ e₁.baseSet ∩ e₂.baseSet) :
    (((e₁.continuousLinearMap (RingHom.id ℝ) e₂) ⟨x,(s x).restrictScalars ℝ⟩).2) =
      (complexHomCoordinates E₁ E₂ e₁ e₂ s x).restrictScalars ℝ := by
  ext v
  change e₂.continuousLinearMapAt ℝ x (s x (e₁.symmL ℝ x v)) =
    e₂.continuousLinearMapAt ℂ x (s x (e₁.symmL ℂ x v))
  simp only [e₁.symmL_apply hx.1,Trivialization.continuousLinearMapAt_apply,
    e₂.coe_linearMapAt_of_mem hx.2]

omit [FiniteDimensional ℝ X] [IsManifold I ∞ B] [T2Space B] [CompactSpace B]
  [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂] in
/-- Complex frame-coordinate smoothness implies genuine smoothness of the
section of the ordinary real Hom bundle. It is not merely a named predicate. -/
theorem smooth_realHom_of_complex_coordinates
    (s : ∀ x, E₁ x →L[ℂ] E₂ x)
    (hs : ∀ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂],
      ContMDiffOn I 𝓘(ℝ,F₁ →L[ℂ] F₂) ∞ (complexHomCoordinates E₁ E₂ e₁ e₂ s)
        (e₁.baseSet ∩ e₂.baseSet)) :
    ContMDiff I (I.prod 𝓘(ℝ,F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x ((s x).restrictScalars ℝ)) := by
  intro x
  let e₁ := trivializationAt F₁ E₁ x
  let e₂ := trivializationAt F₂ E₂ x
  let e := e₁.continuousLinearMap (RingHom.id ℝ) e₂
  have hx : x ∈ e₁.baseSet ∩ e₂.baseSet :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ x,mem_baseSet_trivializationAt F₂ E₂ x⟩
  apply (e.contMDiffAt_section_iff hx).mpr
  have ho := e₁.open_baseSet.inter e₂.open_baseSet
  have hc := ((hs e₁ e₂) x hx).contMDiffAt (ho.mem_nhds hx)
  have hh := (ContinuousLinearMap.restrictScalarsL ℂ F₁ F₂ ℝ ℝ).contDiff.contDiffAt.contMDiffAt.comp x hc
  apply hh.congr_of_eventuallyEq
  filter_upwards [ho.mem_nhds hx] with y hy
  exact realHomCoordinates_restrict E₁ E₂ e₁ e₂ s y hy

end Kaplansky

end

open Bundle Module Set
open scoped Topology Manifold ContDiff
namespace Kaplansky
variable {X H B F₁ F₂ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace H] (I : ModelWithCorners ℝ X H)
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  [T2Space B] [CompactSpace B]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [FiniteDimensional ℂ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [FiniteDimensional ℂ F₂]
  (E₁ E₂ : B → Type*)
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [∀ x, NormedAddCommGroup (E₂ x)] [∀ x, NormedSpace ℂ (E₂ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]
  [VectorBundle ℝ F₁ E₁] [VectorBundle ℂ F₁ E₁]
  [VectorBundle ℝ F₂ E₂] [VectorBundle ℂ F₂ E₂]
  [ContMDiffVectorBundle ∞ F₁ E₁ I] [ContMDiffVectorBundle ∞ F₂ E₂ I]

def homFrameLinear
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂] (x : B) :
    (E₁ x →L[ℂ] E₂ x) →ₗ[ℂ] (F₁ →L[ℂ] F₂) where
  toFun T := (e₂.continuousLinearMapAt ℂ x).comp (T.comp (e₁.symmL ℂ x))
  map_add' T S := by ext v; simp
  map_smul' c T := by ext v; simp

omit [T2Space B] [CompactSpace B] [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂]
  [VectorBundle ℝ F₁ E₁] [VectorBundle ℝ F₂ E₂] in
theorem homFrameLinear_surjective
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂] (x : B)
    (hx : x ∈ e₁.baseSet ∩ e₂.baseSet) :
    Function.Surjective (homFrameLinear E₁ E₂ e₁ e₂ x) := by
  intro T
  refine ⟨(e₂.symmL ℂ x).comp (T.comp (e₁.continuousLinearMapAt ℂ x)),?_⟩
  ext v
  change e₂.continuousLinearMapAt ℂ x (e₂.symmL ℂ x
    (T (e₁.continuousLinearMapAt ℂ x (e₁.symmL ℂ x v))))=T v
  simp only [Trivialization.continuousLinearMapAt_apply,e₁.coe_linearMapAt_of_mem hx.1,
    e₂.coe_linearMapAt_of_mem hx.2,e₁.symmL_apply hx.1,e₂.symmL_apply hx.2,
    e₁.apply_mk_symm hx.1,e₂.apply_mk_symm hx.2]

omit [T2Space B] [CompactSpace B] [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂]
  [VectorBundle ℝ F₁ E₁] [VectorBundle ℝ F₂ E₂] in
theorem homFrameLinear_commutes
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂] (x : B)
    (hx : x ∈ e₁.baseSet ∩ e₂.baseSet) (T : E₁ x →L[ℂ] E₂ x) (v : E₁ x) :
    (e₂.toPretrivialization.linearEquivAt ℂ x hx.2) (T v)=
      homFrameLinear E₁ E₂ e₁ e₂ x T ((e₁.toPretrivialization.linearEquivAt ℂ x hx.1) v) := by
  change (e₂ ⟨x,T v⟩).2=e₂.continuousLinearMapAt ℂ x (T (e₁.symmL ℂ x ((e₁ ⟨x,v⟩).2)))
  simp only [e₁.symmL_apply hx.1,e₁.symm_apply_apply_mk hx.1,
    Trivialization.continuousLinearMapAt_apply,e₂.coe_linearMapAt_of_mem hx.2]

def homEvaluationCoordinates {n : ℕ} (s : Fin n → ∀ x, E₁ x →L[ℂ] E₂ x)
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂] (x : B) :
    (Fin n → ℂ) →L[ℂ] (F₁ →L[ℂ] F₂) :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (complexHomCoordinates E₁ E₂ e₁ e₂ (s i) x)

omit [T2Space B] [CompactSpace B] [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂]
  [VectorBundle ℝ F₁ E₁] [VectorBundle ℝ F₂ E₂] in
theorem homEvaluationCoordinates_apply {n : ℕ} (s : Fin n → ∀ x, E₁ x →L[ℂ] E₂ x)
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂] (x : B) (c : Fin n → ℂ) :
    homEvaluationCoordinates E₁ E₂ s e₁ e₂ x c=
      homFrameLinear E₁ E₂ e₁ e₂ x (sectionEvaluation s x c) := by
  change (∑ i, (ContinuousLinearMap.proj i).smulRight (complexHomCoordinates E₁ E₂ e₁ e₂ (s i) x)) c =
    homFrameLinear E₁ E₂ e₁ e₂ x (∑ i, c i • s i x)
  simp only [sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply,map_sum,map_smul]
  rfl

omit [FiniteDimensional ℝ X] [IsManifold I ∞ B] [T2Space B] [CompactSpace B]
  [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂] [VectorBundle ℝ F₁ E₁]
  [VectorBundle ℝ F₂ E₂] [ContMDiffVectorBundle ∞ F₁ E₁ I]
  [ContMDiffVectorBundle ∞ F₂ E₂ I] in
theorem homEvaluationCoordinates_smooth {n : ℕ} (s : Fin n → ∀ x, E₁ x →L[ℂ] E₂ x)
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂]
    (hs : ∀ i, ContMDiffOn I 𝓘(ℝ,F₁ →L[ℂ] F₂) ∞
      (complexHomCoordinates E₁ E₂ e₁ e₂ (s i)) (e₁.baseSet ∩ e₂.baseSet)) :
    ContMDiffOn I 𝓘(ℝ,(Fin n → ℂ) →L[ℂ] (F₁ →L[ℂ] F₂)) ∞
      (homEvaluationCoordinates E₁ E₂ s e₁ e₂) (e₁.baseSet ∩ e₂.baseSet) := by
  apply contMDiffOn_finsetSum
  intro i _
  have hh : ContDiff ℂ ∞ (fun A : F₁ →L[ℂ] F₂ => (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).smulRight A) :=
    contDiff_clm_apply_iff.mpr (fun c => contDiff_const.smul contDiff_id)
  exact (hh.restrict_scalars ℝ).contMDiff.comp_contMDiffOn (hs i)

theorem exists_finite_smooth_hom_evaluation :
    ∃ (n : ℕ) (s : Fin n → ∀ x, E₁ x →L[ℂ] E₂ x),
      (∀ x, Function.Surjective (sectionEvaluation s x)) ∧
      ∀ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
        [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂],
        ContMDiffOn I 𝓘(ℝ,(Fin n → ℂ) →L[ℂ] (F₁ →L[ℂ] F₂)) ∞
          (homEvaluationCoordinates E₁ E₂ s e₁ e₂) (e₁.baseSet ∩ e₂.baseSet) ∧
        ∀ x ∈ e₁.baseSet ∩ e₂.baseSet,
          Function.Surjective (homEvaluationCoordinates E₁ E₂ s e₁ e₂ x) := by
  obtain ⟨n,s,hs,hsm⟩ := exists_finite_smooth_complex_hom_generators (F₁ := F₁) (F₂ := F₂) I E₁ E₂
  refine ⟨n,s,hs,fun e₁ e₂ _ _ => ⟨homEvaluationCoordinates_smooth I E₁ E₂ s e₁ e₂
    (fun i => hsm i e₁ e₂),fun x hx T => ?_⟩⟩
  obtain ⟨R,hR⟩ := homFrameLinear_surjective E₁ E₂ e₁ e₂ x hx T
  obtain ⟨c,hc⟩ := hs x R
  refine ⟨c,?_⟩
  rw [homEvaluationCoordinates_apply E₁ E₂ s e₁ e₂ x c,hc,hR]

end Kaplansky

end

end OAI
