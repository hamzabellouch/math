import Mathlib.Tactic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Convex.Contractible

namespace OAI

noncomputable section

open Classical Set Topology

/-! Low-dimensional normalized cubical singular chains for the actual
cellular comparison of arbitrary ordinary two-dimensional CW spaces. Neither
cellular exactness nor a presentation theorem is included as an assumption. -/
open Classical Set
namespace EilenbergGanea.CubicalSingular
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
abbrev I := unitInterval
abbrev Cube₁ (X : Type*) [TopologicalSpace X] := C(I,X)
abbrev Cube₂ (X : Type*) [TopologicalSpace X] := C(I × I,X)
abbrev Cube₃ (X : Type*) [TopologicalSpace X] := C(I × I × I,X)
abbrev C₀ (X : Type*) := X →₀ ℤ
abbrev C₁ (X : Type*) [TopologicalSpace X] := Cube₁ X →₀ ℤ
abbrev C₂ (X : Type*) [TopologicalSpace X] := Cube₂ X →₀ ℤ
abbrev C₃ (X : Type*) [TopologicalSpace X] := Cube₃ X →₀ ℤ

def edge₁ (σ : Cube₂ X) (a : I) : Cube₁ X := ⟨fun t => σ (a,t),by fun_prop⟩
def edge₂ (σ : Cube₂ X) (a : I) : Cube₁ X := ⟨fun t => σ (t,a),by fun_prop⟩
def face₁ (σ : Cube₃ X) (a : I) : Cube₂ X := ⟨fun t => σ (a,t),by fun_prop⟩
def face₂ (σ : Cube₃ X) (a : I) : Cube₂ X := ⟨fun t => σ (t.1,a,t.2),by fun_prop⟩
def face₃ (σ : Cube₃ X) (a : I) : Cube₂ X := ⟨fun t => σ (t.1,t.2,a),by fun_prop⟩

def b₁ : C₁ X →ₗ[ℤ] C₀ X := Finsupp.linearCombination ℤ
  (fun σ => Finsupp.single (σ 1) 1 - Finsupp.single (σ 0) 1)
def b₂ : C₂ X →ₗ[ℤ] C₁ X := Finsupp.linearCombination ℤ
  (fun σ => Finsupp.single (edge₁ σ 1) 1 - Finsupp.single (edge₁ σ 0) 1 -
      Finsupp.single (edge₂ σ 1) 1 + Finsupp.single (edge₂ σ 0) 1)
def b₃ : C₃ X →ₗ[ℤ] C₂ X := Finsupp.linearCombination ℤ
  (fun σ => Finsupp.single (face₁ σ 1) 1 - Finsupp.single (face₁ σ 0) 1 -
      Finsupp.single (face₂ σ 1) 1 + Finsupp.single (face₂ σ 0) 1 +
      Finsupp.single (face₃ σ 1) 1 - Finsupp.single (face₃ σ 0) 1)

@[simp] theorem b₁_single (σ : Cube₁ X) (a : ℤ) :
    b₁ (Finsupp.single σ a) = a • (Finsupp.single (σ 1) 1 - Finsupp.single (σ 0) 1) := by
  simp [b₁]
@[simp] theorem b₂_single (σ : Cube₂ X) (a : ℤ) :
    b₂ (Finsupp.single σ a) = a • (Finsupp.single (edge₁ σ 1) 1 -
      Finsupp.single (edge₁ σ 0) 1 - Finsupp.single (edge₂ σ 1) 1 + Finsupp.single (edge₂ σ 0) 1) := by
  simp [b₂]
@[simp] theorem b₃_single (σ : Cube₃ X) (a : ℤ) :
    b₃ (Finsupp.single σ a) = a • (Finsupp.single (face₁ σ 1) 1 -
      Finsupp.single (face₁ σ 0) 1 - Finsupp.single (face₂ σ 1) 1 +
      Finsupp.single (face₂ σ 0) 1 + Finsupp.single (face₃ σ 1) 1 - Finsupp.single (face₃ σ 0) 1) := by
  simp [b₃]

theorem b₁_b₂ : (b₁ : C₁ X →ₗ[ℤ] C₀ X).comp b₂ = 0 := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [LinearMap.comp_apply,b₂_single,one_smul,map_add,map_sub,map_smul,b₁_single,edge₁,edge₂,
    ContinuousMap.coe_mk,LinearMap.zero_apply]
  abel_nf

@[simp] theorem edge₁_face₂ (σ : Cube₃ X) (a b : I) : edge₁ (face₂ σ a) b = edge₁ (face₁ σ b) a := rfl
@[simp] theorem edge₁_face₃ (σ : Cube₃ X) (a b : I) : edge₁ (face₃ σ a) b = edge₂ (face₁ σ b) a := rfl
@[simp] theorem edge₂_face₃ (σ : Cube₃ X) (a b : I) : edge₂ (face₃ σ a) b = edge₂ (face₂ σ b) a := rfl

theorem b₂_b₃ : (b₂ : C₂ X →ₗ[ℤ] C₁ X).comp b₃ = 0 := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [LinearMap.comp_apply,b₃_single,one_smul,map_add,map_sub,map_smul,b₂_single,
    edge₁_face₂,edge₁_face₃,edge₂_face₃,LinearMap.zero_apply]
  abel_nf

def constant₁ (x : X) : Cube₁ X := ContinuousMap.const _ x
def degenerate₁ (σ : Cube₁ X) : Cube₂ X := ⟨fun t => σ t.1,by fun_prop⟩
def degenerate₂ (σ : Cube₁ X) : Cube₂ X := ⟨fun t => σ t.2,by fun_prop⟩
@[simp] theorem edge₁_degenerate₁ (σ : Cube₁ X) (a : I) :
    edge₁ (degenerate₁ σ) a = constant₁ (σ a) := ContinuousMap.ext (fun _ => rfl)
@[simp] theorem edge₂_degenerate₁ (σ : Cube₁ X) (a : I) :
    edge₂ (degenerate₁ σ) a = σ := ContinuousMap.ext (fun _ => rfl)
@[simp] theorem edge₁_degenerate₂ (σ : Cube₁ X) (a : I) :
    edge₁ (degenerate₂ σ) a = σ := ContinuousMap.ext (fun _ => rfl)
@[simp] theorem edge₂_degenerate₂ (σ : Cube₁ X) (a : I) :
    edge₂ (degenerate₂ σ) a = constant₁ (σ a) := ContinuousMap.ext (fun _ => rfl)
def D₁ (X : Type*) [TopologicalSpace X] : Submodule ℤ (C₁ X) :=
  Submodule.span ℤ (Set.range (fun x : X => Finsupp.single (constant₁ x) 1))
def D₂ (X : Type*) [TopologicalSpace X] : Submodule ℤ (C₂ X) :=
  Submodule.span ℤ (Set.range (fun σ : Cube₁ X => Finsupp.single (degenerate₁ σ) 1) ∪
    Set.range (fun σ : Cube₁ X => Finsupp.single (degenerate₂ σ) 1))
abbrev N₁ (X : Type*) [TopologicalSpace X] := C₁ X ⧸ D₁ X
abbrev N₂ (X : Type*) [TopologicalSpace X] := C₂ X ⧸ D₂ X

theorem D₁_le_ker : D₁ X ≤ LinearMap.ker (b₁ : C₁ X →ₗ[ℤ] C₀ X) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x,rfl⟩
  simp [constant₁]

theorem b₂_D₂ : D₂ X ≤ (D₁ X).comap (b₂ : C₂ X →ₗ[ℤ] C₁ X) := by
  apply Submodule.span_le.mpr
  rintro _ (⟨σ,rfl⟩ | ⟨σ,rfl⟩)
  · change b₂ (Finsupp.single (degenerate₁ σ) 1) ∈ D₁ X
    have h₁ (x : X) : Finsupp.single (constant₁ x) 1 ∈ D₁ X :=
      Submodule.subset_span ⟨x,rfl⟩
    simpa using (D₁ X).sub_mem (h₁ (σ 1)) (h₁ (σ 0))
  · change b₂ (Finsupp.single (degenerate₂ σ) 1) ∈ D₁ X
    have h₁ (x : X) : Finsupp.single (constant₁ x) 1 ∈ D₁ X :=
      Submodule.subset_span ⟨x,rfl⟩
    have he : b₂ (Finsupp.single (degenerate₂ σ) 1) =
        Finsupp.single (constant₁ (σ 0)) 1 - Finsupp.single (constant₁ (σ 1)) 1 := by
      simp [sub_eq_add_neg]
      abel
    rw [he]
    exact (D₁ X).sub_mem (h₁ (σ 0)) (h₁ (σ 1))

def d₁ : N₁ X →ₗ[ℤ] C₀ X := (D₁ X).liftQ b₁ D₁_le_ker
def d₂ : N₂ X →ₗ[ℤ] N₁ X := (D₂ X).mapQ (D₁ X) b₂ b₂_D₂
def d₃ : C₃ X →ₗ[ℤ] N₂ X := (D₂ X).mkQ.comp b₃

@[simp] theorem d₁_mk (c : C₁ X) : d₁ ((D₁ X).mkQ c) = b₁ c := rfl
@[simp] theorem d₂_mk (c : C₂ X) : d₂ ((D₂ X).mkQ c) = (D₁ X).mkQ (b₂ c) := rfl

theorem d₁_d₂ (c : N₂ X) : d₁ (d₂ c) = 0 := by
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (D₂ X) c
  exact LinearMap.congr_fun b₁_b₂ c

theorem d₂_d₃ (c : C₃ X) : d₂ (d₃ c) = 0 := by
  change (D₁ X).mkQ ((b₂ : C₂ X →ₗ[ℤ] C₁ X) (b₃ c)) = 0
  have h := LinearMap.congr_fun b₂_b₃ c
  change b₂ (b₃ c) = 0 at h
  rw [h]
  exact map_zero _


def push₀ (f : C(X,Y)) : C₀ X →ₗ[ℤ] C₀ Y :=
  Finsupp.linearCombination ℤ (fun x => Finsupp.single (f x) 1)
def push₁ (f : C(X,Y)) : C₁ X →ₗ[ℤ] C₁ Y :=
  Finsupp.linearCombination ℤ (fun σ => Finsupp.single (f.comp σ) 1)
def push₂ (f : C(X,Y)) : C₂ X →ₗ[ℤ] C₂ Y :=
  Finsupp.linearCombination ℤ (fun σ => Finsupp.single (f.comp σ) 1)
def push₃ (f : C(X,Y)) : C₃ X →ₗ[ℤ] C₃ Y :=
  Finsupp.linearCombination ℤ (fun σ => Finsupp.single (f.comp σ) 1)

@[simp] theorem push₀_single (f : C(X,Y)) (x : X) (a : ℤ) :
    push₀ f (Finsupp.single x a) = Finsupp.single (f x) a := by simp [push₀]
@[simp] theorem push₁_single (f : C(X,Y)) (σ : Cube₁ X) (a : ℤ) :
    push₁ f (Finsupp.single σ a) = Finsupp.single (f.comp σ) a := by simp [push₁]
@[simp] theorem push₂_single (f : C(X,Y)) (σ : Cube₂ X) (a : ℤ) :
    push₂ f (Finsupp.single σ a) = Finsupp.single (f.comp σ) a := by simp [push₂]
@[simp] theorem push₃_single (f : C(X,Y)) (σ : Cube₃ X) (a : ℤ) :
    push₃ f (Finsupp.single σ a) = Finsupp.single (f.comp σ) a := by simp [push₃]

@[simp] theorem edge₁_comp (f : C(X,Y)) (σ : Cube₂ X) (a : I) :
    edge₁ (f.comp σ) a = f.comp (edge₁ σ a) := rfl
@[simp] theorem edge₂_comp (f : C(X,Y)) (σ : Cube₂ X) (a : I) :
    edge₂ (f.comp σ) a = f.comp (edge₂ σ a) := rfl
@[simp] theorem face₁_comp (f : C(X,Y)) (σ : Cube₃ X) (a : I) :
    face₁ (f.comp σ) a = f.comp (face₁ σ a) := rfl
@[simp] theorem face₂_comp (f : C(X,Y)) (σ : Cube₃ X) (a : I) :
    face₂ (f.comp σ) a = f.comp (face₂ σ a) := rfl
@[simp] theorem face₃_comp (f : C(X,Y)) (σ : Cube₃ X) (a : I) :
    face₃ (f.comp σ) a = f.comp (face₃ σ a) := rfl

theorem b₁_push (f : C(X,Y)) : b₁.comp (push₁ f) = (push₀ f).comp b₁ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem b₂_push (f : C(X,Y)) : b₂.comp (push₂ f) = (push₁ f).comp b₂ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem b₃_push (f : C(X,Y)) : b₃.comp (push₃ f) = (push₂ f).comp b₃ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

section Prism
variable {f g : C(X,Y)} (H : f.Homotopy g)
def prism₀ (x : X) : Cube₁ Y := ⟨fun t => H (t,x),by fun_prop⟩
def prism₁ (σ : Cube₁ X) : Cube₂ Y := ⟨fun t => H (t.1,σ t.2),by fun_prop⟩
def prism₂ (σ : Cube₂ X) : Cube₃ Y := ⟨fun t => H (t.1,σ t.2),by fun_prop⟩

def P₀ : C₀ X →ₗ[ℤ] C₁ Y := Finsupp.linearCombination ℤ
  (fun x => Finsupp.single (prism₀ H x) 1)
def P₁ : C₁ X →ₗ[ℤ] C₂ Y := Finsupp.linearCombination ℤ
  (fun σ => Finsupp.single (prism₁ H σ) 1)
def P₂ : C₂ X →ₗ[ℤ] C₃ Y := Finsupp.linearCombination ℤ
  (fun σ => Finsupp.single (prism₂ H σ) 1)
@[simp] theorem P₀_single (x : X) (a : ℤ) :
    P₀ H (Finsupp.single x a) = Finsupp.single (prism₀ H x) a := by simp [P₀]
@[simp] theorem P₁_single (σ : Cube₁ X) (a : ℤ) :
    P₁ H (Finsupp.single σ a) = Finsupp.single (prism₁ H σ) a := by simp [P₁]
@[simp] theorem P₂_single (σ : Cube₂ X) (a : ℤ) :
    P₂ H (Finsupp.single σ a) = Finsupp.single (prism₂ H σ) a := by simp [P₂]
@[simp] theorem prism₀_zero (x : X) : prism₀ H x 0 = f x := H.apply_zero x
@[simp] theorem prism₀_one (x : X) : prism₀ H x 1 = g x := H.apply_one x
@[simp] theorem prism₁_edge₁_zero (σ : Cube₁ X) : edge₁ (prism₁ H σ) 0 = f.comp σ :=
  ContinuousMap.ext (fun _ => H.apply_zero _)
@[simp] theorem prism₁_edge₁_one (σ : Cube₁ X) : edge₁ (prism₁ H σ) 1 = g.comp σ :=
  ContinuousMap.ext (fun _ => H.apply_one _)
@[simp] theorem prism₁_edge₂ (σ : Cube₁ X) (a : I) : edge₂ (prism₁ H σ) a = prism₀ H (σ a) := rfl
@[simp] theorem prism₂_face₁_zero (σ : Cube₂ X) : face₁ (prism₂ H σ) 0 = f.comp σ :=
  ContinuousMap.ext (fun _ => H.apply_zero _)
@[simp] theorem prism₂_face₁_one (σ : Cube₂ X) : face₁ (prism₂ H σ) 1 = g.comp σ :=
  ContinuousMap.ext (fun _ => H.apply_one _)
@[simp] theorem prism₂_face₂ (σ : Cube₂ X) (a : I) : face₂ (prism₂ H σ) a = prism₁ H (edge₁ σ a) := rfl
@[simp] theorem prism₂_face₃ (σ : Cube₂ X) (a : I) : face₃ (prism₂ H σ) a = prism₁ H (edge₂ σ a) := rfl

theorem prism_boundary₀ : b₁.comp (P₀ H) = push₀ g - push₀ f := by
  apply Finsupp.lhom_ext
  intro x a
  simp [smul_sub,Finsupp.smul_single]

theorem prism_boundary₁ : b₂.comp (P₁ H) + (P₀ H).comp b₁ = push₁ g - push₁ f := by
  apply Finsupp.lhom_ext
  intro σ a
  simp [smul_add,smul_sub,Finsupp.smul_single]

theorem prism_boundary₂ : b₃.comp (P₂ H) + (P₁ H).comp b₂ = push₂ g - push₂ f := by
  apply Finsupp.lhom_ext
  intro σ a
  simp [smul_add,smul_sub,Finsupp.smul_single]

theorem P₁_D₁ : D₁ X ≤ (D₂ Y).comap (P₁ H) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x,rfl⟩
  change P₁ H (Finsupp.single (constant₁ x) 1) ∈ D₂ Y
  rw [P₁_single]
  have he : prism₁ H (constant₁ x) = degenerate₁ (prism₀ H x) :=
    ContinuousMap.ext (fun _ => rfl)
  rw [he]
  exact Submodule.subset_span (Or.inl ⟨_,rfl⟩)
end Prism

@[simp] theorem push₁_id : push₁ (ContinuousMap.id X) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro σ a
  simp
@[simp] theorem push₂_id : push₂ (ContinuousMap.id X) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem push₁_const_mem (x : X) (c : C₁ X) : push₁ (ContinuousMap.const X x) c ∈ D₁ X := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using (D₁ X).add_mem hc hd
  | single σ a =>
    rw [push₁_single]
    have he : (ContinuousMap.const X x).comp σ = constant₁ x := ContinuousMap.ext (fun _ => rfl)
    rw [he,← Finsupp.smul_single_one]
    exact (D₁ X).smul_mem a (Submodule.subset_span ⟨x,rfl⟩)

theorem push₂_const_mem (x : X) (c : C₂ X) : push₂ (ContinuousMap.const X x) c ∈ D₂ X := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using (D₂ X).add_mem hc hd
  | single σ a =>
    rw [push₂_single]
    have he : (ContinuousMap.const X x).comp σ = degenerate₁ (constant₁ x) :=
      ContinuousMap.ext (fun _ => rfl)
    rw [he,← Finsupp.smul_single_one]
    exact (D₂ X).smul_mem a (Submodule.subset_span (Or.inl ⟨_,rfl⟩))

theorem exact₁_of_contractible [ContractibleSpace X] (c : N₁ X) (hc : d₁ c = 0) :
    ∃ b : N₂ X, d₂ b = c := by
  obtain ⟨x,⟨H⟩⟩ := id_nullhomotopic X
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  change b₁ c = 0 at hc
  refine ⟨(D₂ X).mkQ (-P₁ H c),?_⟩
  have he := LinearMap.congr_fun (prism_boundary₁ H) c
  change b₂ (P₁ H c) + P₀ H (b₁ c) = push₁ (ContinuousMap.const X x) c -
    push₁ (ContinuousMap.id X) c at he
  simp only [hc,map_zero,add_zero,push₁_id,LinearMap.id_apply] at he
  rw [d₂_mk,map_neg,he,map_neg,map_sub]
  have hz : (D₁ X).mkQ (push₁ (ContinuousMap.const X x) c) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (push₁_const_mem x c)
  rw [hz,zero_sub,neg_neg]

theorem exact₂_of_contractible [ContractibleSpace X] (c : N₂ X) (hc : d₂ c = 0) :
    ∃ b : C₃ X, d₃ b = c := by
  obtain ⟨x,⟨H⟩⟩ := id_nullhomotopic X
  obtain ⟨c,rfl⟩ := (D₂ X).mkQ_surjective c
  change (D₁ X).mkQ (b₂ c) = 0 at hc
  have hc' : b₂ c ∈ D₁ X := (Submodule.Quotient.mk_eq_zero _).mp hc
  refine ⟨-P₂ H c,?_⟩
  have he := LinearMap.congr_fun (prism_boundary₂ H) c
  change b₃ (P₂ H c) + P₁ H (b₂ c) = push₂ (ContinuousMap.const X x) c -
    push₂ (ContinuousMap.id X) c at he
  rw [push₂_id,LinearMap.id_apply] at he
  have hP : (D₂ X).mkQ (P₁ H (b₂ c)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (P₁_D₁ H hc')
  have hz : (D₂ X).mkQ (push₂ (ContinuousMap.const X x) c) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (push₂_const_mem x c)
  have hn := congrArg (D₂ X).mkQ he
  simp only [map_add,map_sub,hP,hz,add_zero,zero_sub] at hn
  change (D₂ X).mkQ (b₃ (-P₂ H c)) = _
  rw [map_neg,map_neg,hn,neg_neg]


@[simp] theorem comp_constant₁ (f : C(X,Y)) (x : X) :
    f.comp (constant₁ x) = constant₁ (f x) := ContinuousMap.ext (fun _ => rfl)
@[simp] theorem comp_degenerate₁ (f : C(X,Y)) (σ : Cube₁ X) :
    f.comp (degenerate₁ σ) = degenerate₁ (f.comp σ) := rfl
@[simp] theorem comp_degenerate₂ (f : C(X,Y)) (σ : Cube₁ X) :
    f.comp (degenerate₂ σ) = degenerate₂ (f.comp σ) := rfl

theorem push₁_D₁ (f : C(X,Y)) : D₁ X ≤ (D₁ Y).comap (push₁ f) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x,rfl⟩
  change push₁ f (Finsupp.single (constant₁ x) 1) ∈ D₁ Y
  simp only [push₁_single,comp_constant₁]
  exact Submodule.subset_span ⟨_,rfl⟩

theorem push₂_D₂ (f : C(X,Y)) : D₂ X ≤ (D₂ Y).comap (push₂ f) := by
  apply Submodule.span_le.mpr
  rintro _ (⟨σ,rfl⟩ | ⟨σ,rfl⟩)
  · change push₂ f (Finsupp.single (degenerate₁ σ) 1) ∈ D₂ Y
    simp only [push₂_single,comp_degenerate₁]
    exact Submodule.subset_span (Or.inl ⟨_,rfl⟩)
  · change push₂ f (Finsupp.single (degenerate₂ σ) 1) ∈ D₂ Y
    simp only [push₂_single,comp_degenerate₂]
    exact Submodule.subset_span (Or.inr ⟨_,rfl⟩)

def pushN₁ (f : C(X,Y)) : N₁ X →ₗ[ℤ] N₁ Y := (D₁ X).mapQ (D₁ Y) (push₁ f) (push₁_D₁ f)
def pushN₂ (f : C(X,Y)) : N₂ X →ₗ[ℤ] N₂ Y := (D₂ X).mapQ (D₂ Y) (push₂ f) (push₂_D₂ f)
@[simp] theorem pushN₁_mk (f : C(X,Y)) (c : C₁ X) :
    pushN₁ f ((D₁ X).mkQ c) = (D₁ Y).mkQ (push₁ f c) := rfl
@[simp] theorem pushN₂_mk (f : C(X,Y)) (c : C₂ X) :
    pushN₂ f ((D₂ X).mkQ c) = (D₂ Y).mkQ (push₂ f c) := rfl

theorem d₁_push (f : C(X,Y)) (c : N₁ X) : d₁ (pushN₁ f c) = push₀ f (d₁ c) := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  exact LinearMap.congr_fun (b₁_push f) c

theorem d₂_push (f : C(X,Y)) (c : N₂ X) : d₂ (pushN₂ f c) = pushN₁ f (d₂ c) := by
  obtain ⟨c,rfl⟩ := (D₂ X).mkQ_surjective c
  change (D₁ Y).mkQ (b₂ (push₂ f c)) = (D₁ Y).mkQ (push₁ f (b₂ c))
  exact congrArg (D₁ Y).mkQ (LinearMap.congr_fun (b₂_push f) c)

theorem d₃_push (f : C(X,Y)) (c : C₃ X) : d₃ (push₃ f c) = pushN₂ f (d₃ c) := by
  change (D₂ Y).mkQ (b₃ (push₃ f c)) = (D₂ Y).mkQ (push₂ f (b₃ c))
  exact congrArg (D₂ Y).mkQ (LinearMap.congr_fun (b₃_push f) c)

theorem push₁_comp (g : C(Y,Z)) (f : C(X,Y)) : push₁ (g.comp f) = (push₁ g).comp (push₁ f) := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem push₂_comp (g : C(Y,Z)) (f : C(X,Y)) : push₂ (g.comp f) = (push₂ g).comp (push₂ f) := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem push₃_comp (g : C(Y,Z)) (f : C(X,Y)) : push₃ (g.comp f) = (push₃ g).comp (push₃ f) := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem pushN₁_comp (g : C(Y,Z)) (f : C(X,Y)) (c : N₁ X) :
    pushN₁ (g.comp f) c = pushN₁ g (pushN₁ f c) := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  simp only [pushN₁_mk,push₁_comp,LinearMap.comp_apply]

theorem pushN₂_comp (g : C(Y,Z)) (f : C(X,Y)) (c : N₂ X) :
    pushN₂ (g.comp f) c = pushN₂ g (pushN₂ f c) := by
  obtain ⟨c,rfl⟩ := (D₂ X).mkQ_surjective c
  simp only [pushN₂_mk,push₂_comp,LinearMap.comp_apply]

@[simp] theorem pushN₁_id (c : N₁ X) : pushN₁ (ContinuousMap.id X) c = c := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  rw [pushN₁_mk,push₁_id]
  rfl
@[simp] theorem pushN₂_id (c : N₂ X) : pushN₂ (ContinuousMap.id X) c = c := by
  obtain ⟨c,rfl⟩ := (D₂ X).mkQ_surjective c
  rw [pushN₂_mk,push₂_id]
  rfl

@[simp] theorem pushN₁_const (y : Y) (c : N₁ X) : pushN₁ (ContinuousMap.const X y) c = 0 := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  rw [pushN₁_mk]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using (D₁ Y).add_mem hc hd
  | single σ a =>
    rw [push₁_single]
    have he : (ContinuousMap.const X y).comp σ = constant₁ y := ContinuousMap.ext (fun _ => rfl)
    rw [he,← Finsupp.smul_single_one]
    exact (D₁ Y).smul_mem a (Submodule.subset_span ⟨y,rfl⟩)

@[simp] theorem pushN₂_const (y : Y) (c : N₂ X) : pushN₂ (ContinuousMap.const X y) c = 0 := by
  obtain ⟨c,rfl⟩ := (D₂ X).mkQ_surjective c
  rw [pushN₂_mk]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using (D₂ Y).add_mem hc hd
  | single σ a =>
    rw [push₂_single]
    have he : (ContinuousMap.const X y).comp σ = degenerate₁ (constant₁ y) :=
      ContinuousMap.ext (fun _ => rfl)
    rw [he,← Finsupp.smul_single_one]
    exact (D₂ Y).smul_mem a (Submodule.subset_span (Or.inl ⟨_,rfl⟩))

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.CubicalSingular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def half (b : Bool) : C(I,I) where
  toFun t := if b then ⟨(1 + t.val) / 2,by constructor <;> linarith [t.property.1,t.property.2]⟩
    else ⟨t.val / 2,by constructor <;> linarith [t.property.1,t.property.2]⟩
  continuous_toFun := by cases b <;> dsimp <;> fun_prop
@[simp] theorem half_false_zero : half false 0 = 0 := Subtype.ext (by norm_num [half])
@[simp] theorem half_true_one : half true 1 = 1 := Subtype.ext (by norm_num [half])
theorem half_mid : half false 1 = half true 0 := Subtype.ext (by norm_num [half])

def cut₁ (σ : Cube₁ X) (i : Bool) : Cube₁ X := σ.comp (half i)
def cut₂ (σ : Cube₂ X) (i j : Bool) : Cube₂ X :=
  ⟨fun t => σ (half i t.1,half j t.2),by fun_prop⟩
def cut₃ (σ : Cube₃ X) (i j k : Bool) : Cube₃ X :=
  ⟨fun t => σ (half i t.1,half j t.2.1,half k t.2.2),by fun_prop⟩

def S₁ : C₁ X →ₗ[ℤ] C₁ X := Finsupp.linearCombination ℤ
  (fun σ => ∑ i : Bool, Finsupp.single (cut₁ σ i) 1)
def S₂ : C₂ X →ₗ[ℤ] C₂ X := Finsupp.linearCombination ℤ
  (fun σ => ∑ i : Bool, ∑ j : Bool, Finsupp.single (cut₂ σ i j) 1)
def S₃ : C₃ X →ₗ[ℤ] C₃ X := Finsupp.linearCombination ℤ
  (fun σ => ∑ i : Bool, ∑ j : Bool, ∑ k : Bool, Finsupp.single (cut₃ σ i j k) 1)

@[simp] theorem S₁_single (σ : Cube₁ X) (a : ℤ) :
    S₁ (Finsupp.single σ a) = ∑ i : Bool, Finsupp.single (cut₁ σ i) a := by
  simp [S₁,Finsupp.smul_single]
@[simp] theorem S₂_single (σ : Cube₂ X) (a : ℤ) :
    S₂ (Finsupp.single σ a) = ∑ i : Bool, ∑ j : Bool, Finsupp.single (cut₂ σ i j) a := by
  simp [S₂,Finsupp.smul_single]
@[simp] theorem S₃_single (σ : Cube₃ X) (a : ℤ) :
    S₃ (Finsupp.single σ a) = ∑ i : Bool, ∑ j : Bool, ∑ k : Bool, Finsupp.single (cut₃ σ i j k) a := by
  simp [S₃,Finsupp.smul_single]

@[simp] theorem edge₁_cut₂ (σ : Cube₂ X) (i j : Bool) (a : I) :
    edge₁ (cut₂ σ i j) a = cut₁ (edge₁ σ (half i a)) j := rfl
@[simp] theorem edge₂_cut₂ (σ : Cube₂ X) (i j : Bool) (a : I) :
    edge₂ (cut₂ σ i j) a = cut₁ (edge₂ σ (half j a)) i := rfl
@[simp] theorem face₁_cut₃ (σ : Cube₃ X) (i j k : Bool) (a : I) :
    face₁ (cut₃ σ i j k) a = cut₂ (face₁ σ (half i a)) j k := rfl
@[simp] theorem face₂_cut₃ (σ : Cube₃ X) (i j k : Bool) (a : I) :
    face₂ (cut₃ σ i j k) a = cut₂ (face₂ σ (half j a)) i k := rfl
@[simp] theorem face₃_cut₃ (σ : Cube₃ X) (i j k : Bool) (a : I) :
    face₃ (cut₃ σ i j k) a = cut₂ (face₃ σ (half k a)) i j := rfl

theorem b₁_subdivision : b₁.comp (S₁ : C₁ X →ₗ[ℤ] C₁ X) = b₁ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp [cut₁,half_mid,smul_sub,Finsupp.smul_single]

theorem b₂_subdivision : b₂.comp (S₂ : C₂ X →ₗ[ℤ] C₂ X) = S₁.comp b₂ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [LinearMap.comp_apply,S₂_single,Fintype.sum_bool,map_add,b₂_single,edge₁_cut₂,
    edge₂_cut₂,half_false_zero,half_true_one,half_mid,map_sub,S₁_single,
    smul_add,smul_sub,Finsupp.smul_single,smul_eq_mul,mul_one]
  abel

theorem b₃_subdivision : b₃.comp (S₃ : C₃ X →ₗ[ℤ] C₃ X) = S₂.comp b₃ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [LinearMap.comp_apply,S₃_single,Fintype.sum_bool,map_add,b₃_single,face₁_cut₃,
    face₂_cut₃,face₃_cut₃,half_false_zero,half_true_one,half_mid,map_sub,S₂_single,
    smul_add,smul_sub,Finsupp.smul_single,smul_eq_mul,mul_one]
  abel

@[simp] theorem cut₁_comp (f : C(X,Y)) (σ : Cube₁ X) (i : Bool) :
    cut₁ (f.comp σ) i = f.comp (cut₁ σ i) := rfl
@[simp] theorem cut₂_comp (f : C(X,Y)) (σ : Cube₂ X) (i j : Bool) :
    cut₂ (f.comp σ) i j = f.comp (cut₂ σ i j) := rfl
@[simp] theorem cut₃_comp (f : C(X,Y)) (σ : Cube₃ X) (i j k : Bool) :
    cut₃ (f.comp σ) i j k = f.comp (cut₃ σ i j k) := rfl

theorem S₁_push (f : C(X,Y)) : S₁.comp (push₁ f) = (push₁ f).comp S₁ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem S₂_push (f : C(X,Y)) : S₂.comp (push₂ f) = (push₂ f).comp S₂ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem S₃_push (f : C(X,Y)) : S₃.comp (push₃ f) = (push₃ f).comp S₃ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

@[simp] theorem cut₁_constant (x : X) (i : Bool) : cut₁ (constant₁ x) i = constant₁ x :=
  ContinuousMap.ext (fun _ => rfl)
@[simp] theorem cut₂_degenerate₁ (σ : Cube₁ X) (i j : Bool) :
    cut₂ (degenerate₁ σ) i j = degenerate₁ (cut₁ σ i) := rfl
@[simp] theorem cut₂_degenerate₂ (σ : Cube₁ X) (i j : Bool) :
    cut₂ (degenerate₂ σ) i j = degenerate₂ (cut₁ σ j) := rfl

theorem S₁_D₁ : D₁ X ≤ (D₁ X).comap S₁ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x,rfl⟩
  change S₁ (Finsupp.single (constant₁ x) 1) ∈ D₁ X
  rw [S₁_single]
  apply Submodule.sum_mem
  intro i hi
  simp only [cut₁_constant]
  exact Submodule.subset_span ⟨x,rfl⟩

theorem S₂_D₂ : D₂ X ≤ (D₂ X).comap S₂ := by
  apply Submodule.span_le.mpr
  rintro _ (⟨σ,rfl⟩ | ⟨σ,rfl⟩)
  · change S₂ (Finsupp.single (degenerate₁ σ) 1) ∈ D₂ X
    rw [S₂_single]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.sum_mem
    intro j hj
    simp only [cut₂_degenerate₁]
    exact Submodule.subset_span (Or.inl ⟨_,rfl⟩)
  · change S₂ (Finsupp.single (degenerate₂ σ) 1) ∈ D₂ X
    rw [S₂_single]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.sum_mem
    intro j hj
    simp only [cut₂_degenerate₂]
    exact Submodule.subset_span (Or.inr ⟨_,rfl⟩)

def SN₁ : N₁ X →ₗ[ℤ] N₁ X := (D₁ X).mapQ (D₁ X) S₁ S₁_D₁
def SN₂ : N₂ X →ₗ[ℤ] N₂ X := (D₂ X).mapQ (D₂ X) S₂ S₂_D₂
@[simp] theorem SN₁_mk (c : C₁ X) : SN₁ ((D₁ X).mkQ c) = (D₁ X).mkQ (S₁ c) := rfl
@[simp] theorem SN₂_mk (c : C₂ X) : SN₂ ((D₂ X).mkQ c) = (D₂ X).mkQ (S₂ c) := rfl

theorem d₁_subdivision (c : N₁ X) : d₁ (SN₁ c) = d₁ c := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  exact LinearMap.congr_fun b₁_subdivision c

theorem d₂_subdivision (c : N₂ X) : d₂ (SN₂ c) = SN₁ (d₂ c) := by
  obtain ⟨c,rfl⟩ := (D₂ X).mkQ_surjective c
  change (D₁ X).mkQ (b₂ (S₂ c)) = (D₁ X).mkQ (S₁ (b₂ c))
  exact congrArg (D₁ X).mkQ (LinearMap.congr_fun b₂_subdivision c)

theorem d₃_subdivision (c : C₃ X) : d₃ (S₃ c) = SN₂ (d₃ c) := by
  change (D₂ X).mkQ (b₃ (S₃ c)) = (D₂ X).mkQ (S₂ (b₃ c))
  exact congrArg (D₂ X).mkQ (LinearMap.congr_fun b₃_subdivision c)

theorem SN₁_push (f : C(X,Y)) (c : N₁ X) : SN₁ (pushN₁ f c) = pushN₁ f (SN₁ c) := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  change (D₁ Y).mkQ (S₁ (push₁ f c)) = (D₁ Y).mkQ (push₁ f (S₁ c))
  exact congrArg (D₁ Y).mkQ (LinearMap.congr_fun (S₁_push f) c)

theorem SN₂_push (f : C(X,Y)) (c : N₂ X) : SN₂ (pushN₂ f c) = pushN₂ f (SN₂ c) := by
  obtain ⟨c,rfl⟩ := (D₂ X).mkQ_surjective c
  change (D₂ Y).mkQ (S₂ (push₂ f c)) = (D₂ Y).mkQ (push₂ f (S₂ c))
  exact congrArg (D₂ Y).mkQ (LinearMap.congr_fun (S₂_push f) c)

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.CubicalSingular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def gen₁ (σ : Cube₁ X) : N₁ X := (D₁ X).mkQ (Finsupp.single σ 1)
def gen₂ (σ : Cube₂ X) : N₂ X := (D₂ X).mkQ (Finsupp.single σ 1)
@[simp] theorem pushN₁_gen (f : C(X,Y)) (σ : Cube₁ X) : pushN₁ f (gen₁ σ) = gen₁ (f.comp σ) := by
  rw [gen₁,pushN₁_mk,push₁_single]
  rfl
@[simp] theorem pushN₂_gen (f : C(X,Y)) (σ : Cube₂ X) : pushN₂ f (gen₂ σ) = gen₂ (f.comp σ) := by
  rw [gen₂,pushN₂_mk,push₂_single]
  rfl

local instance : ContractibleSpace I :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by norm_num⟩

def subdivisionFiller₁ : N₂ I :=
  (exact₁_of_contractible (SN₁ (gen₁ (ContinuousMap.id I)) - gen₁ (ContinuousMap.id I))
    (by rw [map_sub,d₁_subdivision,sub_self])).choose

theorem subdivisionFiller₁_boundary : d₂ subdivisionFiller₁ =
    SN₁ (gen₁ (ContinuousMap.id I)) - gen₁ (ContinuousMap.id I) :=
  (exact₁_of_contractible (SN₁ (gen₁ (ContinuousMap.id I)) - gen₁ (ContinuousMap.id I))
    (by rw [map_sub,d₁_subdivision,sub_self])).choose_spec

def H₁raw : C₁ X →ₗ[ℤ] N₂ X := Finsupp.linearCombination ℤ
  (fun σ => pushN₂ σ subdivisionFiller₁)
@[simp] theorem H₁raw_single (σ : Cube₁ X) (a : ℤ) :
    H₁raw (Finsupp.single σ a) = a • pushN₂ σ subdivisionFiller₁ := by simp [H₁raw]

theorem H₁raw_D₁ : D₁ X ≤ LinearMap.ker H₁raw := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x,rfl⟩
  change H₁raw (Finsupp.single (constant₁ x) 1) = 0
  simp [constant₁]

def H₁ : N₁ X →ₗ[ℤ] N₂ X := (D₁ X).liftQ H₁raw H₁raw_D₁
@[simp] theorem H₁_mk (c : C₁ X) : H₁ ((D₁ X).mkQ c) = H₁raw c := rfl

theorem subdivision_homotopy₁ (c : N₁ X) : d₂ (H₁ c) = SN₁ c - c := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  have he : d₂.comp (H₁raw : C₁ X →ₗ[ℤ] N₂ X) =
      (SN₁ - LinearMap.id).comp (D₁ X).mkQ := by
    apply Finsupp.lhom_ext
    intro σ a
    simp only [LinearMap.comp_apply,H₁raw_single,map_smul,d₂_push,subdivisionFiller₁_boundary,
      map_sub,← SN₁_push,pushN₁_gen,ContinuousMap.comp_id]
    change a • (SN₁ (gen₁ σ) - gen₁ σ) = SN₁ ((D₁ X).mkQ (Finsupp.single σ a)) -
      (D₁ X).mkQ (Finsupp.single σ a)
    rw [← Finsupp.smul_single_one σ a,map_smul,map_smul,smul_sub]
    rfl
  exact LinearMap.congr_fun he c

theorem H₁raw_push (f : C(X,Y)) : H₁raw.comp (push₁ f) = (pushN₂ f).comp H₁raw := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [LinearMap.comp_apply,push₁_single,H₁raw_single,map_smul,pushN₂_comp]

theorem H₁_push (f : C(X,Y)) (c : N₁ X) : H₁ (pushN₁ f c) = pushN₂ f (H₁ c) := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  exact LinearMap.congr_fun (H₁raw_push f) c

def subdivisionCycle₂ : N₂ (I × I) :=
  SN₂ (gen₂ (ContinuousMap.id (I × I))) - gen₂ (ContinuousMap.id (I × I)) -
    H₁ (d₂ (gen₂ (ContinuousMap.id (I × I))))

theorem subdivisionCycle₂_cycle : d₂ subdivisionCycle₂ = 0 := by
  simp [subdivisionCycle₂,d₂_subdivision,subdivision_homotopy₁]

def subdivisionFiller₂ : C₃ (I × I) :=
  (exact₂_of_contractible subdivisionCycle₂ subdivisionCycle₂_cycle).choose

theorem subdivisionFiller₂_boundary : d₃ subdivisionFiller₂ = subdivisionCycle₂ :=
  (exact₂_of_contractible subdivisionCycle₂ subdivisionCycle₂_cycle).choose_spec

def H₂raw : C₂ X →ₗ[ℤ] C₃ X := Finsupp.linearCombination ℤ
  (fun σ => push₃ σ subdivisionFiller₂)
@[simp] theorem H₂raw_single (σ : Cube₂ X) (a : ℤ) :
    H₂raw (Finsupp.single σ a) = a • push₃ σ subdivisionFiller₂ := by simp [H₂raw]

theorem subdivision_homotopy₂ (c : C₂ X) : d₃ (H₂raw c) =
    SN₂ ((D₂ X).mkQ c) - (D₂ X).mkQ c - H₁ (d₂ ((D₂ X).mkQ c)) := by
  have he : d₃.comp (H₂raw : C₂ X →ₗ[ℤ] C₃ X) =
      (SN₂ - LinearMap.id - H₁.comp d₂).comp (D₂ X).mkQ := by
    apply Finsupp.lhom_ext
    intro σ a
    simp only [LinearMap.comp_apply,H₂raw_single,map_smul,d₃_push,subdivisionFiller₂_boundary,
      subdivisionCycle₂,map_sub,← SN₂_push,← H₁_push,← d₂_push,pushN₂_gen,ContinuousMap.comp_id]
    change a • (SN₂ (gen₂ σ) - gen₂ σ - H₁ (d₂ (gen₂ σ))) =
      SN₂ ((D₂ X).mkQ (Finsupp.single σ a)) - (D₂ X).mkQ (Finsupp.single σ a) -
        H₁ (d₂ ((D₂ X).mkQ (Finsupp.single σ a)))
    rw [← Finsupp.smul_single_one σ a]
    simp only [map_smul,smul_sub]
    rfl
  exact LinearMap.congr_fun he c

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.CubicalSingular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def bad₁ (X : Type*) [TopologicalSpace X] : Set (Cube₁ X) := Set.range constant₁
def bad₂ (X : Type*) [TopologicalSpace X] : Set (Cube₂ X) :=
  Set.range degenerate₁ ∪ Set.range degenerate₂

theorem D₁_supported : D₁ X = Finsupp.supported ℤ ℤ (bad₁ X) := by
  rw [Finsupp.supported_eq_span_single]
  unfold D₁ bad₁
  congr 1
  ext c
  simp only [Set.mem_range,Set.mem_image]
  aesop

theorem D₂_supported : D₂ X = Finsupp.supported ℤ ℤ (bad₂ X) := by
  rw [Finsupp.supported_eq_span_single]
  unfold D₂ bad₂
  rw [Set.image_union]
  congr 1
  ext c
  simp only [Set.mem_union,Set.mem_range,Set.mem_image]
  aesop

def cubeSet (D : Type*) [TopologicalSpace D] (U : Set X) : Set C(D,X) :=
  {σ | Set.range σ ⊆ U}

theorem cubeSet_mono {D : Type*} [TopologicalSpace D] {U V : Set X} (h : U ⊆ V) :
    cubeSet D U ⊆ cubeSet D V := fun _ hσ => hσ.trans h

@[simp] theorem cubeSet_inter (D : Type*) [TopologicalSpace D] (U V : Set X) :
    cubeSet D (U ∩ V) = cubeSet D U ∩ cubeSet D V := by
  ext σ
  exact Set.subset_inter_iff

@[simp] theorem cubeSet_univ (D : Type*) [TopologicalSpace D] :
    cubeSet D (Set.univ : Set X) = Set.univ := by ext; simp [cubeSet]

def inc (U : Set X) : C(U,X) := ⟨Subtype.val,continuous_subtype_val⟩

theorem range_comp_inc (D : Type*) [TopologicalSpace D] (U : Set X) :
    Set.range (fun σ : C(D,U) => (inc U).comp σ) = cubeSet D U := by
  ext σ
  constructor
  · rintro ⟨σ,rfl⟩ _ ⟨t,rfl⟩
    exact (σ t).property
  · intro hσ
    refine ⟨⟨fun t => ⟨σ t,hσ ⟨t,rfl⟩⟩,σ.continuous.subtype_mk _⟩,?_⟩
    rfl

def L₀ (U : Set X) : Submodule ℤ (C₀ X) := Finsupp.supported ℤ ℤ U
def raw₁ (U : Set X) : Submodule ℤ (C₁ X) := Finsupp.supported ℤ ℤ (cubeSet I U)
def raw₂ (U : Set X) : Submodule ℤ (C₂ X) := Finsupp.supported ℤ ℤ (cubeSet (I × I) U)
def L₁ (U : Set X) : Submodule ℤ (N₁ X) := (raw₁ U).map (D₁ X).mkQ
def L₂ (U : Set X) : Submodule ℤ (N₂ X) := (raw₂ U).map (D₂ X).mkQ
def L₃ (U : Set X) : Submodule ℤ (C₃ X) := Finsupp.supported ℤ ℤ (cubeSet (I × I × I) U)

theorem supported_quotient_inter {A : Type*} (D : Submodule ℤ (A →₀ ℤ))
    (bad s t : Set A) (hD : D = Finsupp.supported ℤ ℤ bad) :
    (Finsupp.supported ℤ ℤ (s ∩ t)).map D.mkQ =
      (Finsupp.supported ℤ ℤ s).map D.mkQ ⊓ (Finsupp.supported ℤ ℤ t).map D.mkQ := by
  apply Submodule.comap_injective_of_surjective D.mkQ_surjective
  rw [Submodule.comap_inf,Submodule.comap_map_eq,Submodule.comap_map_eq,
    Submodule.comap_map_eq,Submodule.ker_mkQ,hD,← Finsupp.supported_union,
    ← Finsupp.supported_union,← Finsupp.supported_union,← Finsupp.supported_inter]
  congr 1
  ext x
  simp only [mem_union,mem_inter_iff]
  tauto

omit [TopologicalSpace X] in
@[simp] theorem L₀_inter (U V : Set X) : L₀ (U ∩ V) = L₀ U ⊓ L₀ V := Finsupp.supported_inter _ _
@[simp] theorem L₁_inter (U V : Set X) : L₁ (U ∩ V) = L₁ U ⊓ L₁ V := by
  unfold L₁ raw₁
  rw [cubeSet_inter]
  exact supported_quotient_inter _ _ _ _ D₁_supported
@[simp] theorem L₂_inter (U V : Set X) : L₂ (U ∩ V) = L₂ U ⊓ L₂ V := by
  unfold L₂ raw₂
  rw [cubeSet_inter]
  exact supported_quotient_inter _ _ _ _ D₂_supported
@[simp] theorem L₃_inter (U V : Set X) : L₃ (U ∩ V) = L₃ U ⊓ L₃ V := by
  unfold L₃
  rw [cubeSet_inter,Finsupp.supported_inter]

omit [TopologicalSpace X] in
theorem L₀_mono {U V : Set X} (h : U ⊆ V) : L₀ U ≤ L₀ V := Finsupp.supported_mono h
theorem L₁_mono {U V : Set X} (h : U ⊆ V) : L₁ U ≤ L₁ V :=
  Submodule.map_mono (Finsupp.supported_mono (cubeSet_mono h))
theorem L₂_mono {U V : Set X} (h : U ⊆ V) : L₂ U ≤ L₂ V :=
  Submodule.map_mono (Finsupp.supported_mono (cubeSet_mono h))
theorem L₃_mono {U V : Set X} (h : U ⊆ V) : L₃ U ≤ L₃ V := Finsupp.supported_mono (cubeSet_mono h)

theorem L₁_span (U : Set X) : L₁ U = Submodule.span ℤ (gen₁ '' cubeSet I U) := by
  rw [L₁,raw₁,Finsupp.supported_eq_span_single,Submodule.map_span,← Set.image_comp]
  rfl

theorem L₂_span (U : Set X) : L₂ U = Submodule.span ℤ (gen₂ '' cubeSet (I × I) U) := by
  rw [L₂,raw₂,Finsupp.supported_eq_span_single,Submodule.map_span,← Set.image_comp]
  rfl

theorem gen₁_mem {U : Set X} {σ : Cube₁ X} (hσ : σ ∈ cubeSet I U) : gen₁ σ ∈ L₁ U := by
  rw [L₁_span]
  exact Submodule.subset_span ⟨σ,hσ,rfl⟩
theorem gen₂_mem {U : Set X} {σ : Cube₂ X} (hσ : σ ∈ cubeSet (I × I) U) : gen₂ σ ∈ L₂ U := by
  rw [L₂_span]
  exact Submodule.subset_span ⟨σ,hσ,rfl⟩

theorem d₁_support (U : Set X) : L₁ U ≤ (L₀ U).comap d₁ := by
  rw [L₁_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ,hσ,rfl⟩
  change b₁ (Finsupp.single σ 1) ∈ L₀ U
  rw [b₁_single,one_smul]
  exact Submodule.sub_mem _ (Finsupp.single_mem_supported _ _ (hσ ⟨1,rfl⟩))
    (Finsupp.single_mem_supported _ _ (hσ ⟨0,rfl⟩))

theorem d₂_support (U : Set X) : L₂ U ≤ (L₁ U).comap d₂ := by
  rw [L₂_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ,hσ,rfl⟩
  change (D₁ X).mkQ (b₂ (Finsupp.single σ 1)) ∈ L₁ U
  rw [b₂_single,one_smul,map_add,map_sub,map_sub]
  apply Submodule.add_mem
  · apply Submodule.sub_mem
    · apply Submodule.sub_mem
      · exact gen₁_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(1,t),rfl⟩)
      · exact gen₁_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(0,t),rfl⟩)
    · exact gen₁_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(t,1),rfl⟩)
  · exact gen₁_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(t,0),rfl⟩)

theorem d₃_support (U : Set X) : L₃ U ≤ (L₂ U).comap d₃ := by
  rw [L₃,Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ,hσ,rfl⟩
  change (D₂ X).mkQ (b₃ (Finsupp.single σ 1)) ∈ L₂ U
  simp only [b₃_single,one_smul,map_sub,map_add]
  apply Submodule.sub_mem
  · apply Submodule.add_mem
    · apply Submodule.add_mem
      · apply Submodule.sub_mem
        · apply Submodule.sub_mem
          · exact gen₂_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(1,t),rfl⟩)
          · exact gen₂_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(0,t),rfl⟩)
        · exact gen₂_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(t.1,1,t.2),rfl⟩)
      · exact gen₂_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(t.1,0,t.2),rfl⟩)
    · exact gen₂_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(t.1,t.2,1),rfl⟩)
  · exact gen₂_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(t.1,t.2,0),rfl⟩)

end EilenbergGanea.CubicalSingular


open Classical Set
namespace EilenbergGanea.NormalizedSupport
variable {A : Type*}
abbrev Chains (A : Type*) := A →₀ ℤ
abbrev Q (bad : Set A) := Chains A ⧸ Finsupp.supported ℤ ℤ bad

def supported (bad s : Set A) : Submodule ℤ (Q bad) :=
  (Finsupp.supported ℤ ℤ s).map (Finsupp.supported ℤ ℤ bad).mkQ

theorem comap_supported (bad s : Set A) :
    (supported bad s).comap (Finsupp.supported ℤ ℤ bad).mkQ = Finsupp.supported ℤ ℤ (s ∪ bad) := by
  rw [supported,Submodule.comap_map_eq,Submodule.ker_mkQ,Finsupp.supported_union]

theorem supported_mono (bad : Set A) {s t : Set A} (h : s ⊆ t) : supported bad s ≤ supported bad t :=
  Submodule.map_mono (Finsupp.supported_mono h)

theorem supported_inter (bad s t : Set A) :
    supported bad (s ∩ t) = supported bad s ⊓ supported bad t := by
  apply Submodule.comap_injective_of_surjective (Finsupp.supported ℤ ℤ bad).mkQ_surjective
  rw [Submodule.comap_inf,comap_supported,comap_supported,comap_supported,← Finsupp.supported_inter]
  congr 1
  ext x
  simp only [mem_union,mem_inter_iff]
  tauto

theorem supported_union (bad s t : Set A) :
    supported bad (s ∪ t) = supported bad s ⊔ supported bad t := by
  simp only [supported,Finsupp.supported_union,Submodule.map_sup]

@[simp] theorem supported_empty (bad : Set A) : supported bad ∅ = ⊥ := by
  simp [supported]
@[simp] theorem supported_univ (bad : Set A) : supported bad univ = ⊤ := by
  simp [supported,LinearMap.range_eq_top.mpr (Finsupp.supported ℤ ℤ bad).mkQ_surjective]

theorem mk_mem_supported (bad : Set A) {s : Set A} {c : Chains A}
    (hc : c ∈ Finsupp.supported ℤ ℤ s) :
    (Finsupp.supported ℤ ℤ bad).mkQ c ∈ supported bad s := ⟨c,hc,rfl⟩

theorem mem_supported_mk (bad s : Set A) (c : Chains A) :
    (Finsupp.supported ℤ ℤ bad).mkQ c ∈ supported bad s ↔
      ∀ a, a ∉ bad → c a ≠ 0 → a ∈ s := by
  change c ∈ (supported bad s).comap (Finsupp.supported ℤ ℤ bad).mkQ ↔ _
  rw [comap_supported,Finsupp.mem_supported]
  simp only [Set.subset_def,Finset.mem_coe,Finsupp.mem_support_iff,mem_union]
  constructor
  · intro h a ha hc
    exact (h a hc).resolve_right ha
  · intro h a hc
    by_cases ha : a ∈ bad
    · exact Or.inr ha
    · exact Or.inl (h a ha hc)

/-- The hypothesis is on actual normalized basis support, not homology. -/
theorem exists_split (bad s t : Set A) {c : Q bad} (hc : c ∈ supported bad s ⊔ supported bad t) :
    ∃ a ∈ supported bad s, ∃ b ∈ supported bad t, a + b = c :=
  Submodule.mem_sup.mp hc


variable {B : Type*}
theorem comap_supported_of_injective (f : A → B) (hf : Function.Injective f) (s : Set B) :
    (Finsupp.supported ℤ ℤ s).comap (Finsupp.lmapDomain ℤ ℤ f) =
      Finsupp.supported ℤ ℤ (f ⁻¹' s) := by
  ext c
  change Finsupp.mapDomain f c ∈ Finsupp.supported ℤ ℤ s ↔
    c ∈ Finsupp.supported ℤ ℤ (f ⁻¹' s)
  rw [Finsupp.mem_supported,Finsupp.mem_supported,Finsupp.mapDomain_support_of_injective hf]
  simp

theorem normalized_injective (badA : Set A) (badB : Set B) (f : A → B)
    (hf : Function.Injective f) (hbad : f ⁻¹' badB = badA)
    (h : Finsupp.supported ℤ ℤ badA ≤ (Finsupp.supported ℤ ℤ badB).comap (Finsupp.lmapDomain ℤ ℤ f)) :
    Function.Injective ((Finsupp.supported ℤ ℤ badA).mapQ (Finsupp.supported ℤ ℤ badB)
      (Finsupp.lmapDomain ℤ ℤ f) h) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.ker_mapQ,comap_supported_of_injective f hf,hbad]
  simp

end EilenbergGanea.NormalizedSupport

namespace EilenbergGanea.CubicalSingular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem compose_injective {D : Type*} [TopologicalSpace D] (f : C(X,Y))
    (hf : Function.Injective f) : Function.Injective (fun σ : C(D,X) => f.comp σ) := by
  intro σ τ h
  exact ContinuousMap.ext (fun x => hf (congrArg (fun a : C(D,Y) => a x) h))

theorem preimage_bad₁ (f : C(X,Y)) (hf : Function.Injective f) :
    (fun σ : Cube₁ X => f.comp σ) ⁻¹' bad₁ Y = bad₁ X := by
  ext σ
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨σ 0,ContinuousMap.ext (fun t => ?_)⟩
    apply hf
    have h₀ := congrArg (fun a : Cube₁ Y => a 0) hy
    have ht := congrArg (fun a : Cube₁ Y => a t) hy
    exact h₀.symm.trans ht
  · rintro ⟨x,rfl⟩
    exact ⟨f x,rfl⟩

theorem preimage_bad₂ (f : C(X,Y)) (hf : Function.Injective f) :
    (fun σ : Cube₂ X => f.comp σ) ⁻¹' bad₂ Y = bad₂ X := by
  ext σ
  constructor
  · rintro (⟨τ,hτ⟩ | ⟨τ,hτ⟩)
    · left
      refine ⟨edge₂ σ 0,ContinuousMap.ext (fun t => ?_)⟩
      apply hf
      have h₀ := congrArg (fun a : Cube₂ Y => a (t.1,0)) hτ
      have ht := congrArg (fun a : Cube₂ Y => a t) hτ
      exact h₀.symm.trans ht
    · right
      refine ⟨edge₁ σ 0,ContinuousMap.ext (fun t => ?_)⟩
      apply hf
      have h₀ := congrArg (fun a : Cube₂ Y => a (0,t.2)) hτ
      have ht := congrArg (fun a : Cube₂ Y => a t) hτ
      exact h₀.symm.trans ht
  · rintro (⟨τ,rfl⟩ | ⟨τ,rfl⟩)
    · exact Or.inl ⟨f.comp τ,rfl⟩
    · exact Or.inr ⟨f.comp τ,rfl⟩

theorem push₀_lmapDomain (f : C(X,Y)) :
    push₀ f = Finsupp.lmapDomain ℤ ℤ (f) := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem push₁_lmapDomain (f : C(X,Y)) :
    push₁ f = Finsupp.lmapDomain ℤ ℤ (fun σ => f.comp σ) := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem push₂_lmapDomain (f : C(X,Y)) :
    push₂ f = Finsupp.lmapDomain ℤ ℤ (fun σ => f.comp σ) := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem push₃_lmapDomain (f : C(X,Y)) :
    push₃ f = Finsupp.lmapDomain ℤ ℤ (fun σ => f.comp σ) := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem push₀_injective (f : C(X,Y)) (hf : Function.Injective f) :
    Function.Injective (push₀ f) := by
  rw [push₀_lmapDomain]
  exact Finsupp.mapDomain_injective hf

theorem pushN₁_injective (f : C(X,Y)) (hf : Function.Injective f) :
    Function.Injective (pushN₁ f) := by
  apply LinearMap.ker_eq_bot.mp
  change LinearMap.ker ((D₁ X).mapQ (D₁ Y) (push₁ f) _) = ⊥
  rw [Submodule.ker_mapQ]
  have h : (D₁ Y).comap (push₁ f) = D₁ X := by
    rw [D₁_supported,D₁_supported]
    rw [push₁_lmapDomain]
    rw [NormalizedSupport.comap_supported_of_injective _ (compose_injective f hf),preimage_bad₁ f hf]
  rw [h]
  simp

theorem pushN₂_injective (f : C(X,Y)) (hf : Function.Injective f) :
    Function.Injective (pushN₂ f) := by
  apply LinearMap.ker_eq_bot.mp
  change LinearMap.ker ((D₂ X).mapQ (D₂ Y) (push₂ f) _) = ⊥
  rw [Submodule.ker_mapQ]
  have h : (D₂ Y).comap (push₂ f) = D₂ X := by
    rw [D₂_supported,D₂_supported]
    rw [push₂_lmapDomain]
    rw [NormalizedSupport.comap_supported_of_injective _ (compose_injective f hf),preimage_bad₂ f hf]
  rw [h]
  simp

theorem range_push₁_inc (U : Set X) : (push₁ (inc U)).range = raw₁ U := by
  rw [push₁_lmapDomain]
  have h := Finsupp.lmapDomain_supported ℤ ℤ (fun σ : Cube₁ U => (inc U).comp σ) Set.univ
  rw [Finsupp.supported_univ,Submodule.map_top,Set.image_univ,range_comp_inc] at h
  exact h

theorem range_push₂_inc (U : Set X) : (push₂ (inc U)).range = raw₂ U := by
  rw [push₂_lmapDomain]
  have h := Finsupp.lmapDomain_supported ℤ ℤ (fun σ : Cube₂ U => (inc U).comp σ) Set.univ
  rw [Finsupp.supported_univ,Submodule.map_top,Set.image_univ,range_comp_inc] at h
  exact h

theorem range_push₃_inc (U : Set X) : (push₃ (inc U)).range = L₃ U := by
  rw [push₃_lmapDomain]
  have h := Finsupp.lmapDomain_supported ℤ ℤ (fun σ : Cube₃ U => (inc U).comp σ) Set.univ
  rw [Finsupp.supported_univ,Submodule.map_top,Set.image_univ,range_comp_inc] at h
  exact h

theorem range_pushN₁_inc (U : Set X) : (pushN₁ (inc U)).range = L₁ U := by
  ext z
  constructor
  · rintro ⟨c,rfl⟩
    obtain ⟨c,rfl⟩ := (D₁ U).mkQ_surjective c
    rw [pushN₁_mk]
    refine ⟨push₁ (inc U) c,?_,rfl⟩
    rw [← range_push₁_inc]
    exact ⟨c,rfl⟩
  · rintro ⟨c,hc,rfl⟩
    rw [← range_push₁_inc] at hc
    obtain ⟨c,rfl⟩ := hc
    exact ⟨(D₁ U).mkQ c,rfl⟩

theorem range_pushN₂_inc (U : Set X) : (pushN₂ (inc U)).range = L₂ U := by
  ext z
  constructor
  · rintro ⟨c,rfl⟩
    obtain ⟨c,rfl⟩ := (D₂ U).mkQ_surjective c
    rw [pushN₂_mk]
    refine ⟨push₂ (inc U) c,?_,rfl⟩
    rw [← range_push₂_inc]
    exact ⟨c,rfl⟩
  · rintro ⟨c,hc,rfl⟩
    rw [← range_push₂_inc] at hc
    obtain ⟨c,rfl⟩ := hc
    exact ⟨(D₂ U).mkQ c,rfl⟩

theorem pushN₁_support (f : C(X,Y)) {U : Set Y} (hf : Set.range f ⊆ U) (c : N₁ X) :
    pushN₁ f c ∈ L₁ U := by
  let f' : C(X,U) := ⟨fun x => ⟨f x,hf ⟨x,rfl⟩⟩,f.continuous.subtype_mk _⟩
  have h : f = (inc U).comp f' := rfl
  rw [h,pushN₁_comp,← range_pushN₁_inc]
  exact ⟨pushN₁ f' c,rfl⟩

theorem pushN₂_support (f : C(X,Y)) {U : Set Y} (hf : Set.range f ⊆ U) (c : N₂ X) :
    pushN₂ f c ∈ L₂ U := by
  let f' : C(X,U) := ⟨fun x => ⟨f x,hf ⟨x,rfl⟩⟩,f.continuous.subtype_mk _⟩
  have h : f = (inc U).comp f' := rfl
  rw [h,pushN₂_comp,← range_pushN₂_inc]
  exact ⟨pushN₂ f' c,rfl⟩

theorem push₃_support (f : C(X,Y)) {U : Set Y} (hf : Set.range f ⊆ U) (c : C₃ X) :
    push₃ f c ∈ L₃ U := by
  let f' : C(X,U) := ⟨fun x => ⟨f x,hf ⟨x,rfl⟩⟩,f.continuous.subtype_mk _⟩
  have h : f = (inc U).comp f' := rfl
  rw [h,push₃_comp,← range_push₃_inc]
  exact ⟨push₃ f' c,rfl⟩

theorem H₁_support (U : Set X) : L₁ U ≤ (L₂ U).comap H₁ := by
  rw [L₁_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ,hσ,rfl⟩
  change H₁raw (Finsupp.single σ 1) ∈ L₂ U
  rw [H₁raw_single,one_smul]
  exact pushN₂_support σ hσ _

theorem H₂raw_support (U : Set X) : raw₂ U ≤ (L₃ U).comap H₂raw := by
  rw [raw₂,Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ,hσ,rfl⟩
  change H₂raw (Finsupp.single σ 1) ∈ L₃ U
  rw [H₂raw_single,one_smul]
  exact push₃_support σ hσ _

theorem exact₁_on_contractible (U : Set X) [ContractibleSpace U]
    {c : N₁ X} (hc : c ∈ L₁ U) (hz : d₁ c = 0) : ∃ b ∈ L₂ U, d₂ b = c := by
  rw [← range_pushN₁_inc] at hc
  obtain ⟨c,rfl⟩ := hc
  have hz' : d₁ c = 0 := by
    apply push₀_injective (inc U) Subtype.val_injective
    simpa only [d₁_push,map_zero] using hz
  obtain ⟨b,hb⟩ := exact₁_of_contractible c hz'
  refine ⟨pushN₂ (inc U) b,?_,?_⟩
  · rw [← range_pushN₂_inc]
    exact ⟨b,rfl⟩
  · rw [d₂_push,hb]

theorem exact₂_on_contractible (U : Set X) [ContractibleSpace U]
    {c : N₂ X} (hc : c ∈ L₂ U) (hz : d₂ c = 0) : ∃ b ∈ L₃ U, d₃ b = c := by
  rw [← range_pushN₂_inc] at hc
  obtain ⟨c,rfl⟩ := hc
  have hz' : d₂ c = 0 := by
    apply pushN₁_injective (inc U) Subtype.val_injective
    simpa only [d₂_push,map_zero] using hz
  obtain ⟨b,hb⟩ := exact₂_of_contractible c hz'
  refine ⟨push₃ (inc U) b,?_,?_⟩
  · rw [← range_push₃_inc]
    exact ⟨b,rfl⟩
  · rw [d₃_push,hb]

end EilenbergGanea.CubicalSingular

open Classical Set
namespace EilenbergGanea.CubicalMesh
variable {D X : Type*} [MetricSpace D] [CompactSpace D] [Nonempty D] [TopologicalSpace X]
variable {κ : Type*} [Fintype κ]

abbrev Chains (D X : Type*) [TopologicalSpace D] [TopologicalSpace X] := C(D,X) →₀ ℤ

def small (U : Set (Set X)) : Set C(D,X) := {σ | ∃ u ∈ U, Set.range σ ⊆ u}
def subchains (U : Set (Set X)) : Submodule ℤ (Chains D X) := Finsupp.supported ℤ ℤ (small U)

def subdivision (a : κ → C(D,D)) : Chains D X →ₗ[ℤ] Chains D X :=
  Finsupp.linearCombination ℤ (fun σ => ∑ i, Finsupp.single (σ.comp (a i)) 1)

omit [CompactSpace D] [Nonempty D] in
@[simp] theorem subdivision_single (a : κ → C(D,D)) (σ : C(D,X)) (z : ℤ) :
    subdivision a (Finsupp.single σ z) = ∑ i, Finsupp.single (σ.comp (a i)) z := by
  simp [subdivision,Finset.smul_sum,Finsupp.smul_single]

omit [CompactSpace D] [Nonempty D] in
theorem subdivision_preserves (a : κ → C(D,D)) (U : Set (Set X)) :
    subchains (D := D) U ≤ (subchains U).comap (subdivision a) := by
  apply le_trans (le_of_eq (Finsupp.supported_eq_span_single ℤ (small (D := D) U)))
  apply Submodule.span_le.mpr
  rintro _ ⟨σ,⟨u,hu,hσ⟩,rfl⟩
  change subdivision a (Finsupp.single σ 1) ∈ subchains U
  rw [subdivision_single]
  apply Submodule.sum_mem
  intro i hi
  apply Finsupp.single_mem_supported
  exact ⟨u,hu,by rintro _ ⟨t,rfl⟩; exact hσ ⟨a i t,rfl⟩⟩

def shrinking (r : ℝ) (σ : C(D,X)) (n : ℕ) : Set C(D,X) :=
  {τ | ∃ f : C(D,D), (∀ x y, dist (f x) (f y) ≤ r ^ n * dist x y) ∧ τ = σ.comp f}

omit [CompactSpace D] [Nonempty D] in
theorem iterate_parametrized (a : κ → C(D,D)) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ i x y, dist (a i x) (a i y) ≤ r * dist x y) (σ : C(D,X)) (n : ℕ) :
    ((subdivision a)^[n]) (Finsupp.single σ 1) ∈ Finsupp.supported ℤ ℤ (shrinking r σ n) := by
  induction n with
  | zero =>
    apply Finsupp.single_mem_supported
    refine ⟨ContinuousMap.id D,?_,?_⟩
    · intro x y
      simp
    · simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hm : Finsupp.supported ℤ ℤ (shrinking r σ n) ≤
        (Finsupp.supported ℤ ℤ (shrinking r σ (n+1))).comap (subdivision a) := by
      apply le_trans (le_of_eq (Finsupp.supported_eq_span_single ℤ (shrinking r σ n)))
      apply Submodule.span_le.mpr
      rintro _ ⟨τ,⟨f,hf,rfl⟩,rfl⟩
      change subdivision a (Finsupp.single (σ.comp f) 1) ∈ Finsupp.supported ℤ ℤ (shrinking r σ (n+1))
      rw [subdivision_single]
      apply Submodule.sum_mem
      intro i hi
      apply Finsupp.single_mem_supported
      refine ⟨f.comp (a i),?_,rfl⟩
      intro x y
      calc
        dist (f (a i x)) (f (a i y)) ≤ r ^ n * dist (a i x) (a i y) := hf _ _
        _ ≤ r ^ n * (r * dist x y) := mul_le_mul_of_nonneg_left (ha i x y) (pow_nonneg hr n)
        _ = r ^ (n+1) * dist x y := by rw [pow_succ,mul_assoc]
    exact hm ih

theorem shrinking_small (hD : ∀ x y : D, dist x y ≤ 1) {r : ℝ} (hr : r < 1)
    (U : Set (Set X)) (hU : ∀ u ∈ U, IsOpen u) (hcover : ⋃₀ U = Set.univ) (σ : C(D,X)) :
    ∃ N : ℕ, ∀ n, N ≤ n → 0 ≤ r → shrinking r σ n ⊆ small U := by
  obtain ⟨δ,hδ,hLeb⟩ := lebesgue_number_lemma_of_metric (s := Set.univ)
    (c := fun u : U => σ ⁻¹' (u : Set X)) isCompact_univ
    (fun u => (hU u u.property).preimage σ.continuous) (by
      intro x hx
      have : σ x ∈ ⋃₀ U := hcover ▸ Set.mem_univ _
      obtain ⟨u,hu,hx⟩ := this
      exact Set.mem_iUnion.mpr ⟨⟨u,hu⟩,hx⟩)
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one hδ hr
  refine ⟨N,fun n hn hr0 τ hτ => ?_⟩
  obtain ⟨f,hf,rfl⟩ := hτ
  let x₀ : D := Classical.choice inferInstance
  obtain ⟨u,hu⟩ := hLeb (f x₀) trivial
  refine ⟨u,u.property,?_⟩
  rintro _ ⟨x,rfl⟩
  apply hu
  change dist (f x) (f x₀) < δ
  calc
    dist (f x) (f x₀) ≤ r ^ n * dist x x₀ := hf _ _
    _ ≤ r ^ n * 1 := mul_le_mul_of_nonneg_left (hD _ _) (pow_nonneg hr0 n)
    _ = r ^ n := mul_one _
    _ ≤ r ^ N := pow_le_pow_of_le_one hr0 hr.le hn
    _ < δ := hN

theorem single_eventually_small (a : κ → C(D,D)) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (ha : ∀ i x y, dist (a i x) (a i y) ≤ r * dist x y)
    (hD : ∀ x y : D, dist x y ≤ 1)
    (U : Set (Set X)) (hU : ∀ u ∈ U, IsOpen u) (hcover : ⋃₀ U = Set.univ) (σ : C(D,X)) :
    ∃ N : ℕ, ∀ n, N ≤ n → ((subdivision a)^[n]) (Finsupp.single σ 1) ∈ subchains U := by
  obtain ⟨N,hN⟩ := shrinking_small hD hr U hU hcover σ
  exact ⟨N,fun n hn => Finsupp.supported_mono (hN n hn hr0) (iterate_parametrized a hr0 ha σ n)⟩

theorem chain_eventually_small (a : κ → C(D,D)) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (ha : ∀ i x y, dist (a i x) (a i y) ≤ r * dist x y)
    (hD : ∀ x y : D, dist x y ≤ 1)
    (U : Set (Set X)) (hU : ∀ u ∈ U, IsOpen u) (hcover : ⋃₀ U = Set.univ) (c : Chains D X) :
    ∃ N : ℕ, ∀ n, N ≤ n → ((subdivision a)^[n]) c ∈ subchains U := by
  classical
  induction c using Finsupp.induction_linear with
  | zero =>
    refine ⟨0,fun n hn => ?_⟩
    have hz : ((subdivision a)^[n]) (0 : Chains D X) = 0 := by
      clear hn
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply',ih,map_zero]
    rw [hz]
    exact Submodule.zero_mem _
  | add c d hc hd =>
    obtain ⟨N,hN⟩ := hc
    obtain ⟨M,hM⟩ := hd
    refine ⟨max N M,fun n hn => ?_⟩
    have hadd : ((subdivision a)^[n]) (c+d) =
        ((subdivision a)^[n]) c + ((subdivision a)^[n]) d := by
      clear hn
      induction n with
      | zero => rfl
      | succ n ih => simp only [Function.iterate_succ_apply',ih,map_add]
    rw [hadd]
    exact Submodule.add_mem _ (hN n ((le_max_left _ _).trans hn)) (hM n ((le_max_right _ _).trans hn))
  | single σ z =>
    obtain ⟨N,hN⟩ := single_eventually_small a hr0 hr ha hD U hU hcover σ
    refine ⟨N,fun n hn => ?_⟩
    have hsmul : ((subdivision a)^[n]) (Finsupp.single σ z) =
        z • ((subdivision a)^[n]) (Finsupp.single σ 1) := by
      clear hn
      induction n with
      | zero => simp [Finsupp.smul_single]
      | succ n ih => simp only [Function.iterate_succ_apply',ih,map_smul]
    rw [hsmul]
    exact Submodule.smul_mem _ z (hN n hn)

end EilenbergGanea.CubicalMesh

namespace EilenbergGanea.CubicalSingular
variable {X : Type*} [TopologicalSpace X]

theorem half_dist (b : Bool) (x y : I) : dist (half b x) (half b y) = (1/2:ℝ) * dist x y := by
  have h : (half b x : ℝ) - (half b y : ℝ) = (1/2:ℝ) * ((x:ℝ) - (y:ℝ)) := by
    cases b <;> simp only [half,Bool.false_eq_true,ite_false,ite_true,ContinuousMap.coe_mk] <;> ring
  change |(half b x : ℝ) - (half b y : ℝ)| = (1/2:ℝ) * |(x:ℝ) - (y:ℝ)|
  rw [h,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 1/2)]

theorem interval_diameter (x y : I) : dist x y ≤ 1 := by
  rw [Subtype.dist_eq,Real.dist_eq,abs_le]
  constructor <;> linarith [x.property.1,x.property.2,y.property.1,y.property.2]

def half₂ (b : Bool × Bool) : C(I × I,I × I) :=
  ⟨fun t => (half b.1 t.1,half b.2 t.2),by fun_prop⟩
def half₃ (b : Bool × Bool × Bool) : C(I × I × I,I × I × I) :=
  ⟨fun t => (half b.1 t.1,half b.2.1 t.2.1,half b.2.2 t.2.2),by fun_prop⟩

theorem half₂_dist (b : Bool × Bool) (x y : I × I) :
    dist (half₂ b x) (half₂ b y) ≤ (1/2:ℝ) * dist x y := by
  simp only [half₂,ContinuousMap.coe_mk,Prod.dist_eq,half_dist]
  rw [max_le_iff]
  exact ⟨mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num),
    mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)⟩

theorem half₃_dist (b : Bool × Bool × Bool) (x y : I × I × I) :
    dist (half₃ b x) (half₃ b y) ≤ (1/2:ℝ) * dist x y := by
  simp only [half₃,ContinuousMap.coe_mk,Prod.dist_eq,half_dist]
  rw [max_le_iff,max_le_iff]
  exact ⟨mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num),
    mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_right _ _)) (by norm_num),
    mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (le_max_right _ _)) (by norm_num)⟩

theorem S₁_mesh : (S₁ : C₁ X →ₗ[ℤ] C₁ X) = CubicalMesh.subdivision half := rfl

theorem S₂_mesh : (S₂ : C₂ X →ₗ[ℤ] C₂ X) = CubicalMesh.subdivision half₂ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [S₂_single,CubicalMesh.subdivision_single,Fintype.sum_prod_type]
  rfl

theorem S₃_mesh : (S₃ : C₃ X →ₗ[ℤ] C₃ X) = CubicalMesh.subdivision half₃ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [S₃_single,CubicalMesh.subdivision_single,Fintype.sum_prod_type]
  rfl

theorem small_pair (D : Type*) [MetricSpace D] (U V : Set X) :
    CubicalMesh.small (D := D) {U,V} = cubeSet D U ∪ cubeSet D V := by
  ext σ
  simp only [CubicalMesh.small,Set.mem_ofPred_eq,Set.mem_insert_iff,Set.mem_singleton_iff,
    Set.mem_union,cubeSet,exists_eq_or_imp,exists_eq_left]

theorem S₁_eventually_small (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (c : C₁ X) : ∃ N : ℕ, ∀ n, N ≤ n → (S₁^[n]) c ∈ raw₁ U ⊔ raw₁ V := by
  have h := CubicalMesh.chain_eventually_small half (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
    (fun b x y => (half_dist b x y).le) interval_diameter {U,V}
    (by intro u hu; rcases hu with rfl | hu; exact hU; obtain rfl := hu; exact hV)
    (by simpa using hUV) c
  simpa only [← S₁_mesh,CubicalMesh.subchains,small_pair,Finsupp.supported_union,raw₁] using h

theorem S₂_eventually_small (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (c : C₂ X) : ∃ N : ℕ, ∀ n, N ≤ n → (S₂^[n]) c ∈ raw₂ U ⊔ raw₂ V := by
  have h := CubicalMesh.chain_eventually_small half₂ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
    half₂_dist (fun x y => max_le (interval_diameter x.1 y.1) (interval_diameter x.2 y.2)) {U,V}
    (by intro u hu; rcases hu with rfl | hu; exact hU; obtain rfl := hu; exact hV)
    (by simpa using hUV) c
  simpa only [← S₂_mesh,CubicalMesh.subchains,small_pair,Finsupp.supported_union,raw₂] using h

theorem S₃_eventually_small (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (c : C₃ X) : ∃ N : ℕ, ∀ n, N ≤ n → (S₃^[n]) c ∈ L₃ U ⊔ L₃ V := by
  have h := CubicalMesh.chain_eventually_small half₃ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
    half₃_dist (fun x y => max_le (interval_diameter x.1 y.1)
      (max_le (interval_diameter x.2.1 y.2.1) (interval_diameter x.2.2 y.2.2))) {U,V}
    (by intro u hu; rcases hu with rfl | hu; exact hU; obtain rfl := hu; exact hV)
    (by simpa using hUV) c
  simpa only [← S₃_mesh,CubicalMesh.subchains,small_pair,Finsupp.supported_union,L₃] using h

theorem SN₁_iter_mk (c : C₁ X) (n : ℕ) :
    (SN₁^[n]) ((D₁ X).mkQ c) = (D₁ X).mkQ ((S₁^[n]) c) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply',ih,SN₁_mk]

theorem SN₂_iter_mk (c : C₂ X) (n : ℕ) :
    (SN₂^[n]) ((D₂ X).mkQ c) = (D₂ X).mkQ ((S₂^[n]) c) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply',ih,SN₂_mk]

theorem SN₁_eventually_small (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (c : N₁ X) : ∃ N : ℕ, ∀ n, N ≤ n → (SN₁^[n]) c ∈ L₁ U ⊔ L₁ V := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  obtain ⟨N,hN⟩ := S₁_eventually_small U V hU hV hUV c
  refine ⟨N,fun n hn => ?_⟩
  rw [SN₁_iter_mk,L₁,L₁,← Submodule.map_sup]
  exact ⟨_,hN n hn,rfl⟩

theorem SN₂_eventually_small (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (c : N₂ X) : ∃ N : ℕ, ∀ n, N ≤ n → (SN₂^[n]) c ∈ L₂ U ⊔ L₂ V := by
  obtain ⟨c,rfl⟩ := (D₂ X).mkQ_surjective c
  obtain ⟨N,hN⟩ := S₂_eventually_small U V hU hV hUV c
  refine ⟨N,fun n hn => ?_⟩
  rw [SN₂_iter_mk,L₂,L₂,← Submodule.map_sup]
  exact ⟨_,hN n hn,rfl⟩

theorem SN₁_support (U : Set X) : L₁ U ≤ (L₁ U).comap SN₁ := by
  intro c hc
  rw [← range_pushN₁_inc] at hc
  obtain ⟨c,rfl⟩ := hc
  change SN₁ (pushN₁ (inc U) c) ∈ L₁ U
  rw [SN₁_push,← range_pushN₁_inc]
  exact ⟨SN₁ c,rfl⟩

theorem SN₂_support (U : Set X) : L₂ U ≤ (L₂ U).comap SN₂ := by
  intro c hc
  rw [← range_pushN₂_inc] at hc
  obtain ⟨c,rfl⟩ := hc
  change SN₂ (pushN₂ (inc U) c) ∈ L₂ U
  rw [SN₂_push,← range_pushN₂_inc]
  exact ⟨SN₂ c,rfl⟩

theorem S₃_support (U : Set X) : L₃ U ≤ (L₃ U).comap S₃ := by
  intro c hc
  rw [← range_push₃_inc] at hc
  obtain ⟨c,rfl⟩ := hc
  change S₃ (push₃ (inc U) c) ∈ L₃ U
  rw [← range_push₃_inc]
  refine ⟨S₃ c,?_⟩
  exact (LinearMap.congr_fun (S₃_push (inc U)) c).symm

theorem SN₁_iter_support (U : Set X) {c : N₁ X} (hc : c ∈ L₁ U) (n : ℕ) : (SN₁^[n]) c ∈ L₁ U := by
  induction n with
  | zero => exact hc
  | succ n ih => rw [Function.iterate_succ_apply']; exact SN₁_support U ih

theorem SN₂_iter_support (U : Set X) {c : N₂ X} (hc : c ∈ L₂ U) (n : ℕ) : (SN₂^[n]) c ∈ L₂ U := by
  induction n with
  | zero => exact hc
  | succ n ih => rw [Function.iterate_succ_apply']; exact SN₂_support U ih

theorem d₁_SN₁_iter (c : N₁ X) (n : ℕ) : d₁ ((SN₁^[n]) c) = d₁ c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',d₁_subdivision,ih]

theorem d₂_SN₂_iter (c : N₂ X) (n : ℕ) : d₂ ((SN₂^[n]) c) = (SN₁^[n]) (d₂ c) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply',d₂_subdivision,ih]

theorem d₃_S₃_iter (c : C₃ X) (n : ℕ) : d₃ ((S₃^[n]) c) = (SN₂^[n]) (d₃ c) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply',d₃_subdivision,ih]

def K₁ : ℕ → N₁ X →ₗ[ℤ] N₂ X
  | 0 => 0
  | n+1 => H₁.comp (SN₁ ^ n) + K₁ n

theorem K₁_boundary (n : ℕ) (c : N₁ X) : d₂ (K₁ n c) = (SN₁^[n]) c - c := by
  induction n with
  | zero => simp [K₁]
  | succ n ih =>
    simp only [K₁,LinearMap.add_apply,LinearMap.comp_apply,map_add,subdivision_homotopy₁,ih]
    rw [Module.End.pow_apply,Function.iterate_succ_apply']
    abel

theorem K₁_support (U : Set X) {c : N₁ X} (hc : c ∈ L₁ U) (n : ℕ) : K₁ n c ∈ L₂ U := by
  induction n with
  | zero => exact Submodule.zero_mem _
  | succ n ih =>
    change H₁ ((SN₁ ^ n) c) + K₁ n c ∈ L₂ U
    rw [Module.End.pow_apply]
    exact Submodule.add_mem _ (H₁_support U (SN₁_iter_support U hc n)) ih

end EilenbergGanea.CubicalSingular


end

end OAI
