import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI

section

noncomputable section
namespace JiangSuConstruction
open scoped Kronecker
open LinearMap

section Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

def matrixTrace : CStarMatrix I I ℂ →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap I ℂ ℂ).comp (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.toLinearMap

omit [DecidableEq I] in
lemma matrixTrace_continuous : Continuous (matrixTrace (I := I)) := by
  let : FiniteDimensional ℂ (CStarMatrix I I ℂ) :=
    FiniteDimensional.of_injective (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.toLinearMap
      (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.injective
  exact LinearMap.continuous_of_finiteDimensional _

lemma matrixTrace_idempotent {e : CStarMatrix I I ℂ} (he : IsIdempotentElem e) :
    ∃ r : ℕ, r ≤ Fintype.card I ∧ matrixTrace e=(r:ℂ) := by
  let M := CStarMatrix.ofMatrix.symm e
  have hm : IsIdempotentElem M := by exact he
  have hL : IsIdempotentElem M.toLin' := hm.map Matrix.toLinAlgEquiv'
  refine ⟨Module.finrank ℂ (LinearMap.range M.toLin'),?_,?_⟩
  · simpa using (LinearMap.range M.toLin').finrank_le
  · change M.trace = _
    rw [←Matrix.trace_toLin'_eq]
    exact hL.isProj_range.trace

lemma matrixTrace_idempotent_zero {e : CStarMatrix I I ℂ} (he : IsIdempotentElem e)
    (ht : matrixTrace e=0) : e=0 := by
  let M := CStarMatrix.ofMatrix.symm e
  have hm : IsIdempotentElem M := by exact he
  have hL : IsIdempotentElem M.toLin' := hm.map Matrix.toLinAlgEquiv'
  have hz : M.toLin'=0 := hL.eq_zero_of_trace_eq_zero (by
    rw [Matrix.trace_toLin'_eq]
    exact ht)
  have hz' : M=0 := Matrix.toLinAlgEquiv'.injective (by simpa using hz)
  exact hz'

lemma matrixTrace_idempotent_one {e : CStarMatrix I I ℂ} (he : IsIdempotentElem e)
    (ht : matrixTrace e=(Fintype.card I:ℂ)) : e=1 := by
  have hcomp : IsIdempotentElem (1-e) := he.one_sub
  have hzero := matrixTrace_idempotent_zero hcomp (by
    rw [map_sub]
    change (1 : Matrix I I ℂ).trace - matrixTrace e = 0
    rw [Matrix.trace_one,ht,sub_self])
  exact (sub_eq_zero.mp hzero).symm

end Matrix

lemma matrixTrace_idempotent_path_constant {I : Type*} [Fintype I] [DecidableEq I]
    (f : C(Interval, CStarMatrix I I ℂ)) (hf : ∀ t, IsIdempotentElem (f t))
    (s t : Interval) : matrixTrace (f s)=matrixTrace (f t) := by
  let g : Interval → ℂ := fun u => matrixTrace (f u)
  have hg : Continuous g := matrixTrace_continuous.comp f.continuous
  have hfinite : (Set.range g).Finite := by
    apply (Set.finite_Iic (Fintype.card I)).image (fun n : ℕ => (n:ℂ)) |>.subset
    rintro z ⟨u,rfl⟩
    obtain ⟨r,hr,he⟩ := matrixTrace_idempotent (hf u)
    exact ⟨r,hr,he.symm⟩
  have hpre : IsPreconnected (Set.range g) := isPreconnected_range hg
  by_contra hne
  exact hpre.infinite_of_nontrivial ⟨g s,Set.mem_range_self s,g t,Set.mem_range_self t,hne⟩ hfinite

end JiangSuConstruction

end
end

section

noncomputable section
namespace JiangSuConstruction
open scoped Kronecker

lemma leftAmplification_injective {p q : ℕ} (hq : 0<q) :
    Function.Injective (leftAmplification p q) := by
  intro x y h
  ext i k
  have he := congrArg (fun z : TensorMat p q => z (i,⟨0,hq⟩) (k,⟨0,hq⟩)) h
  change x i k * (1 : Matrix (Fin q) (Fin q) ℂ) ⟨0,hq⟩ ⟨0,hq⟩ =
    y i k * (1 : Matrix (Fin q) (Fin q) ℂ) ⟨0,hq⟩ ⟨0,hq⟩ at he
  simpa using he

lemma rightAmplification_injective {p q : ℕ} (hp : 0<p) :
    Function.Injective (rightAmplification p q) := by
  intro x y h
  ext j l
  have he := congrArg (fun z : TensorMat p q => z (⟨0,hp⟩,j) (⟨0,hp⟩,l)) h
  change (1 : Matrix (Fin p) (Fin p) ℂ) ⟨0,hp⟩ ⟨0,hp⟩ * x j l =
    (1 : Matrix (Fin p) (Fin p) ℂ) ⟨0,hp⟩ ⟨0,hp⟩ * y j l at he
  simpa using he

lemma matrixTrace_left (p q : ℕ) (x : Mat p) :
    matrixTrace ((leftAmplification p q) x)=matrixTrace x*(q:ℂ) := by
  change (CStarMatrix.ofMatrix.symm x ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)).trace = _
  rw [Matrix.trace_kronecker,Matrix.trace_one,Fintype.card_fin]
  rfl

lemma matrixTrace_right (p q : ℕ) (x : Mat q) :
    matrixTrace ((rightAmplification p q) x)=(p:ℂ)*matrixTrace x := by
  change ((1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm x).trace = _
  rw [Matrix.trace_kronecker,Matrix.trace_one,Fintype.card_fin]
  rfl

local instance (priority := 2000) dropSemiring (p q : ℕ) : Semiring (DimensionDrop p q) :=
  (inferInstance : CStarAlgebra (DimensionDrop p q)).toSemiring

theorem primeDrop_idempotent_trivial {p q : ℕ} (hp : 0<p) (hq : 0<q)
    (hc : p.Coprime q) (e : DimensionDrop p q) (he : IsIdempotentElem e) : e=0 ∨ e=1 := by
  have hf : ∀ t, IsIdempotentElem (e.val t) := fun t =>
    congrArg (fun x : DimensionDrop p q => x.val t) he
  obtain ⟨r,hr,hrt⟩ := matrixTrace_idempotent (hf leftEndpoint)
  have hbound : r≤p*q := by simpa using hr
  have htrace : ∀ t, matrixTrace (e.val t)=(r:ℂ) := fun t =>
    (matrixTrace_idempotent_path_constant e.val hf t leftEndpoint).trans hrt
  obtain ⟨x,hx⟩ := e.property.1
  obtain ⟨y,hy⟩ := e.property.2
  change (leftAmplification p q) x=e.val leftEndpoint at hx
  change (rightAmplification p q) y=e.val rightEndpoint at hy
  have hxid : IsIdempotentElem x := by
    apply leftAmplification_injective hq
    rw [map_mul,hx]
    exact hf leftEndpoint
  have hyid : IsIdempotentElem y := by
    apply rightAmplification_injective hp
    rw [map_mul,hy]
    exact hf rightEndpoint
  obtain ⟨rx,_,hrx⟩ := matrixTrace_idempotent hxid
  obtain ⟨ry,_,hry⟩ := matrixTrace_idempotent hyid
  have hqdiv : q ∣ r := by
    refine ⟨rx,?_⟩
    apply Nat.cast_injective (R := ℂ)
    push_cast
    rw [←hrt,←hx,matrixTrace_left,hrx,mul_comm]
  have hpdiv : p ∣ r := by
    refine ⟨ry,?_⟩
    apply Nat.cast_injective (R := ℂ)
    push_cast
    rw [←htrace rightEndpoint,←hy,matrixTrace_right,hry]
  have hdiv := hc.mul_dvd_of_dvd_of_dvd hpdiv hqdiv
  by_cases hz : r=0
  · left
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    exact matrixTrace_idempotent_zero (hf t) (by rw [htrace t,hz,Nat.cast_zero])
  · have heq : r=p*q := Nat.le_antisymm hbound (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hdiv)
    right
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    apply matrixTrace_idempotent_one (hf t)
    simpa [heq] using htrace t

end JiangSuConstruction

end
end

end OAI
