import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.ProjectionRanks
import OAI.Analysis.JiangSu.MatrixAlgebras.ContinuousMatrixTraceIdeal

namespace OAI


noncomputable section
namespace JiangSuConstruction
open ContinuousMatrixTraceIdeal
open scoped Kronecker CStarAlgebra ComplexOrder

variable {X I : Type*} [TopologicalSpace X] [Fintype I] [DecidableEq I]

local instance (priority := 2000) matrixPathSemiring : Semiring C(X,CStarMatrix I I ℂ) :=
  (inferInstance : Ring C(X,CStarMatrix I I ℂ)).toSemiring

def matrixPathEquiv : C(X,Matrix I I ℂ) ≃ₐ[ℂ] C(X,CStarMatrix I I ℂ) where
  toFun f := ⟨fun x => CStarMatrix.ofMatrix (f x), CStarMatrix.ofMatrixL.continuous.comp f.continuous⟩
  invFun f := ⟨fun x => CStarMatrix.ofMatrix.symm (f x), CStarMatrix.ofMatrixL.symm.continuous.comp f.continuous⟩
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
  map_mul' f g := by ext; rfl
  map_add' f g := by ext; rfl
  commutes' z := rfl

def pointwiseHom {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) : C(X,A) →ₐ[ℂ] C(X,B) where
  toFun f := ⟨fun x => φ (f x), (map_continuous φ).comp f.continuous⟩
  map_one' := by ext; exact map_one φ
  map_zero' := by ext; exact map_zero φ
  map_add' f g := by ext x; exact map_add φ _ _
  map_mul' f g := by ext x; exact map_mul φ _ _
  commutes' z := by ext; exact φ.commutes z

def scalarMatrixPath (z : C(X,ℂ)) : C(X,CStarMatrix I I ℂ) :=
  matrixPathEquiv (scalarPath z)

def normalizedTracePath : C(X,CStarMatrix I I ℂ) →ₗ[ℂ] C(X,ℂ) where
  toFun f := ⟨fun x => (Fintype.card I : ℂ)⁻¹*matrixTrace (f x),
    continuous_const.mul (matrixTrace_continuous.comp f.continuous)⟩
  map_add' f g := by ext x; simp [map_add,mul_add]
  map_smul' c f := by ext x; simp [mul_left_comm]

lemma normalizedTracePath_eq (f : C(X,Matrix I I ℂ)) :
    normalizedTracePath (matrixPathEquiv f)=(Fintype.card I : ℂ)⁻¹ • tracePath f := by
  ext x
  simp only [normalizedTracePath,matrixPathEquiv,tracePath,entry,
    LinearMap.coe_mk,AddHom.coe_mk,ContinuousMap.coe_mk,ContinuousMap.smul_apply,ContinuousMap.sum_apply]
  rfl

lemma scalarMatrixPath_add (z w : C(X,ℂ)) :
    scalarMatrixPath (I := I) (z+w)=scalarMatrixPath z+scalarMatrixPath w := by
  simp only [scalarMatrixPath]
  apply ContinuousMap.ext
  intro x
  change (z x + w x) • (1 : CStarMatrix I I ℂ) = z x • 1 + w x • 1
  exact add_smul _ _ _

lemma scalarMatrixPath_sub (z w : C(X,ℂ)) :
    scalarMatrixPath (I := I) (z-w)=scalarMatrixPath z-scalarMatrixPath w := by
  apply ContinuousMap.ext
  intro x
  change (z x - w x) • (1 : CStarMatrix I I ℂ) = z x • 1 - w x • 1
  exact sub_smul _ _ _

lemma scalarization_ambient (T : C(X,CStarMatrix I I ℂ) →ₗ[ℂ] ℂ) (E : Set X)
    (hT : ∀ u v : C(X,CStarMatrix I I ℂ),
      (∀ x∈E,u x=0) → (∀ x∈E,v x=0) → T (u*v)=T (v*u))
    [Nonempty I] (f : C(X,CStarMatrix I I ℂ)) (hf : ∀ x∈E,f x=0) :
    T f=T (scalarMatrixPath (normalizedTracePath f)) := by
  let L := T.comp matrixPathEquiv.toLinearMap
  have hL : ∀ u v : C(X,Matrix I I ℂ),
      (∀ x∈E,u x=0) → (∀ x∈E,v x=0) → L (u*v)=L (v*u) := by
    intro u v hu hv
    change T (matrixPathEquiv (u*v))=T (matrixPathEquiv (v*u))
    rw [map_mul matrixPathEquiv u v,map_mul matrixPathEquiv v u]
    exact hT _ _ (fun x hx => by change CStarMatrix.ofMatrix (u x)=0; rw [hu x hx]; rfl)
      (fun x hx => by change CStarMatrix.ofMatrix (v x)=0; rw [hv x hx]; rfl)
  have h := ContinuousMatrixTraceIdeal.scalarization L E hL (matrixPathEquiv.symm f)
    (fun x hx => by change CStarMatrix.ofMatrix.symm (f x)=0; rw [hf x hx]; rfl)
  change T (matrixPathEquiv (matrixPathEquiv.symm f))=T (matrixPathEquiv _) at h
  rw [AlgEquiv.apply_symm_apply] at h
  convert h using 1
  congr 2
  simpa using normalizedTracePath_eq (matrixPathEquiv.symm f)

variable {p q : ℕ}
local instance (priority := 2000) traceDropSemiring (p q : ℕ) : Semiring (DimensionDrop p q) :=
  (inferInstance : CStarAlgebra (DimensionDrop p q)).toSemiring

lemma interior_mem {f : C(Interval,TensorMat p q)}
    (h0 : f leftEndpoint=0) (h1 : f rightEndpoint=0) : f∈dimensionDrop p q := by
  constructor
  · exact ⟨0,by change (leftAmplification p q) 0=f leftEndpoint; rw [map_zero,h0]⟩
  · exact ⟨0,by change (rightAmplification p q) 0=f rightEndpoint; rw [map_zero,h1]⟩

lemma leftPath_mem {f : C(Interval,Mat p)} (hf : f rightEndpoint=0) :
    pointwiseHom (leftAmplification p q) f∈dimensionDrop p q := by
  constructor
  · exact ⟨f leftEndpoint,rfl⟩
  · exact ⟨0,by change (rightAmplification p q) 0=(leftAmplification p q) (f rightEndpoint); simp [hf]⟩

lemma rightPath_mem {f : C(Interval,Mat q)} (hf : f leftEndpoint=0) :
    pointwiseHom (rightAmplification p q) f∈dimensionDrop p q := by
  constructor
  · exact ⟨0,by change (leftAmplification p q) 0=(rightAmplification p q) (f leftEndpoint); simp [hf]⟩
  · exact ⟨f rightEndpoint,rfl⟩

lemma pointwise_scalar {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (z : C(X,ℂ)) :
    pointwiseHom φ ⟨fun x => z x • (1:A),by fun_prop⟩ =
      (⟨fun x => z x • (1:B),by fun_prop⟩ : C(X,B)) := by
  ext x
  exact by change φ (z x • (1:A))=z x • (1:B); rw [map_smul,map_one]

lemma normalizedTracePath_left [NeZero p] [NeZero q] (f : C(X,Mat p)) :
    normalizedTracePath (pointwiseHom (leftAmplification p q) f)=normalizedTracePath f := by
  ext x
  change ((Fintype.card (Fin p×Fin q) : ℂ)⁻¹)*matrixTrace ((leftAmplification p q) (f x))=(Fintype.card (Fin p) : ℂ)⁻¹*matrixTrace (f x)
  rw [matrixTrace_left]
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
  change ((p:ℂ)*(q:ℂ))⁻¹*(matrixTrace (f x)*(q:ℂ))=(p:ℂ)⁻¹*matrixTrace (f x)
  have hp : (p:ℂ)≠0 := by exact_mod_cast NeZero.ne p
  have hq : (q:ℂ)≠0 := by exact_mod_cast NeZero.ne q
  field_simp

lemma normalizedTracePath_right [NeZero p] [NeZero q] (f : C(X,Mat q)) :
    normalizedTracePath (pointwiseHom (rightAmplification p q) f)=normalizedTracePath f := by
  ext x
  change ((Fintype.card (Fin p×Fin q) : ℂ)⁻¹)*matrixTrace ((rightAmplification p q) (f x))=(Fintype.card (Fin q) : ℂ)⁻¹*matrixTrace (f x)
  rw [matrixTrace_right]
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
  change ((p:ℂ)*(q:ℂ))⁻¹*((p:ℂ)*matrixTrace (f x))=(q:ℂ)⁻¹*matrixTrace (f x)
  have hp : (p:ℂ)≠0 := by exact_mod_cast NeZero.ne p
  have hq : (q:ℂ)≠0 := by exact_mod_cast NeZero.ne q
  field_simp

end JiangSuConstruction

end


noncomputable section
namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder

variable {X I J : Type*} [TopologicalSpace X] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

lemma scalarMatrixPath_apply (z : C(X,ℂ)) (x : X) :
    scalarMatrixPath (I := I) z x=z x • (1:CStarMatrix I I ℂ) := rfl

lemma pointwiseHom_scalarMatrixPath (φ : CStarMatrix I I ℂ →⋆ₐ[ℂ] CStarMatrix J J ℂ)
    (z : C(X,ℂ)) : pointwiseHom φ (scalarMatrixPath z)=scalarMatrixPath z := by
  apply ContinuousMap.ext
  intro x
  change φ (z x • (1:CStarMatrix I I ℂ))=z x • (1:CStarMatrix J J ℂ)
  rw [map_smul,map_one]

variable {p q : ℕ} [NeZero p] [NeZero q]

local instance (priority := 2000) factorDropSemiring (p q : ℕ) : Semiring (DimensionDrop p q) :=
  (inferInstance : CStarAlgebra (DimensionDrop p q)).toSemiring

variable (T : C(Interval,TensorMat p q) →ₗ[ℂ] ℂ)
variable (hT : ∀ u v : C(Interval,TensorMat p q), u∈dimensionDrop p q → v∈dimensionDrop p q →
  T (u*v)=T (v*u))

include hT in
lemma trace_scalarization_interior (f : C(Interval,TensorMat p q))
    (h0 : f leftEndpoint=0) (h1 : f rightEndpoint=0) :
    T f=T (scalarMatrixPath (normalizedTracePath f)) := by
  apply scalarization_ambient T ({leftEndpoint,rightEndpoint} : Set Interval)
  · intro u v hu hv
    exact hT u v (interior_mem (hu _ (by simp)) (hu _ (by simp)))
      (interior_mem (hv _ (by simp)) (hv _ (by simp)))
  · intro x hx
    rcases Set.mem_insert_iff.1 hx with rfl|hx
    · exact h0
    · simpa only [Set.mem_singleton_iff] using hx ▸ h1

include hT in
lemma trace_scalarization_left (f : C(Interval,Mat p)) (hf : f rightEndpoint=0) :
    T (pointwiseHom (leftAmplification p q) f)=
      T (scalarMatrixPath (normalizedTracePath (pointwiseHom (leftAmplification p q) f))) := by
  let L := T.comp (pointwiseHom (leftAmplification p q)).toLinearMap
  have hL : ∀ u v : C(Interval,Mat p), (∀ x∈({rightEndpoint}:Set Interval),u x=0) →
      (∀ x∈({rightEndpoint}:Set Interval),v x=0) → L (u*v)=L (v*u) := by
    intro u v hu hv
    change T (pointwiseHom (leftAmplification p q) (u*v))=T (pointwiseHom (leftAmplification p q) (v*u))
    rw [map_mul (pointwiseHom (leftAmplification p q)),map_mul (pointwiseHom (leftAmplification p q))]
    exact hT _ _ (leftPath_mem (hu _ (by simp))) (leftPath_mem (hv _ (by simp)))
  have h := scalarization_ambient L ({rightEndpoint}:Set Interval) hL f (by simpa using hf)
  change T (pointwiseHom (leftAmplification p q) f)=
    T (pointwiseHom (leftAmplification p q) (scalarMatrixPath (normalizedTracePath f))) at h
  rw [pointwiseHom_scalarMatrixPath] at h
  rw [normalizedTracePath_left]
  exact h

include hT in
lemma trace_scalarization_right (f : C(Interval,Mat q)) (hf : f leftEndpoint=0) :
    T (pointwiseHom (rightAmplification p q) f)=
      T (scalarMatrixPath (normalizedTracePath (pointwiseHom (rightAmplification p q) f))) := by
  let L := T.comp (pointwiseHom (rightAmplification p q)).toLinearMap
  have hL : ∀ u v : C(Interval,Mat q), (∀ x∈({leftEndpoint}:Set Interval),u x=0) →
      (∀ x∈({leftEndpoint}:Set Interval),v x=0) → L (u*v)=L (v*u) := by
    intro u v hu hv
    change T (pointwiseHom (rightAmplification p q) (u*v))=T (pointwiseHom (rightAmplification p q) (v*u))
    rw [map_mul (pointwiseHom (rightAmplification p q)),map_mul (pointwiseHom (rightAmplification p q))]
    exact hT _ _ (rightPath_mem (hu _ (by simp))) (rightPath_mem (hv _ (by simp)))
  have h := scalarization_ambient L ({leftEndpoint}:Set Interval) hL f (by simpa using hf)
  change T (pointwiseHom (rightAmplification p q) f)=
    T (pointwiseHom (rightAmplification p q) (scalarMatrixPath (normalizedTracePath f))) at h
  rw [pointwiseHom_scalarMatrixPath] at h
  rw [normalizedTracePath_right]
  exact h

include hT in
lemma trace_scalarization_on_drop (f : C(Interval,TensorMat p q)) (hf : f∈dimensionDrop p q) :
    T f=T (scalarMatrixPath (normalizedTracePath f)) := by
  obtain ⟨a,ha⟩ := hf.1
  obtain ⟨b,hb⟩ := hf.2
  change (leftAmplification p q) a=f leftEndpoint at ha
  change (rightAmplification p q) b=f rightEndpoint at hb
  let l : C(Interval,Mat p) := ⟨fun t => ((1-(t:ℝ):ℝ):ℂ) • a,by fun_prop⟩
  let r : C(Interval,Mat q) := ⟨fun t => ((t:ℝ):ℂ) • b,by fun_prop⟩
  let fl := pointwiseHom (leftAmplification p q) l
  let fr := pointwiseHom (rightAmplification p q) r
  have hl : l rightEndpoint=0 := by simp [l,rightEndpoint]
  have hr : r leftEndpoint=0 := by
    change (0 : ℂ) • b = 0
    exact zero_smul ℂ b
  have hfl : T fl=T (scalarMatrixPath (normalizedTracePath fl)) := trace_scalarization_left T hT l hl
  have hfr : T fr=T (scalarMatrixPath (normalizedTracePath fr)) := trace_scalarization_right T hT r hr
  have h0 : (f-(fl+fr)) leftEndpoint=0 := by
    change f leftEndpoint-((leftAmplification p q) (l leftEndpoint)+(rightAmplification p q) (r leftEndpoint))=0
    rw [hr,map_zero,add_zero]
    simp [l,leftEndpoint,ha]
  have h1 : (f-(fl+fr)) rightEndpoint=0 := by
    change f rightEndpoint-((leftAmplification p q) (l rightEndpoint)+(rightAmplification p q) (r rightEndpoint))=0
    rw [hl,map_zero,zero_add]
    change f rightEndpoint - (rightAmplification p q) ((1 : ℂ) • b) = 0
    rw [one_smul ℂ b, hb, sub_self]
  have h := trace_scalarization_interior T hT (f-(fl+fr)) h0 h1
  simp only [map_sub,map_add,scalarMatrixPath_sub,scalarMatrixPath_add] at h
  rw [hfl,hfr] at h
  exact sub_left_inj.mp h

omit [NeZero p] [NeZero q] in
lemma scalarMatrixPath_mem (z : C(Interval,ℂ)) : scalarMatrixPath (I := Fin p×Fin q) z∈dimensionDrop p q := by
  constructor
  · refine ⟨z leftEndpoint • (1:Mat p),?_⟩
    change (leftAmplification p q) (z leftEndpoint • (1:Mat p))=z leftEndpoint • (1:TensorMat p q)
    rw [map_smul,map_one]
  · refine ⟨z rightEndpoint • (1:Mat q),?_⟩
    change (rightAmplification p q) (z rightEndpoint • (1:Mat q))=z rightEndpoint • (1:TensorMat p q)
    rw [map_smul,map_one]

def scalarDrop (z : C(Interval,ℂ)) : DimensionDrop p q :=
  ⟨scalarMatrixPath z,scalarMatrixPath_mem z⟩

theorem dimensionDrop_trace_factorization (τ : DimensionDrop p q →ₗ[ℂ] ℂ)
    (hτ : ∀ a b, τ (a*b)=τ (b*a)) (f : DimensionDrop p q) :
    τ f=τ (scalarDrop (normalizedTracePath f.val)) := by
  let V := (dimensionDrop p q).toSubalgebra.toSubmodule
  let τ' : V →ₗ[ℂ] ℂ := τ
  obtain ⟨L,hL⟩ := LinearMap.exists_extend τ'
  have hLval (g : DimensionDrop p q) : L g.val=τ g := by
    exact congrArg (fun k : V →ₗ[ℂ] ℂ => k g) hL
  have hcomm (u v : C(Interval,TensorMat p q)) (hu : u∈dimensionDrop p q) (hv : v∈dimensionDrop p q) :
      L (u*v)=L (v*u) := by
    have hh := hτ ⟨u,hu⟩ ⟨v,hv⟩
    rw [←hLval,←hLval] at hh
    exact hh
  have h := trace_scalarization_on_drop L hcomm f.val f.property
  rw [hLval] at h
  exact h.trans (hLval (scalarDrop (normalizedTracePath f.val)))

end JiangSuConstruction

end

end OAI
