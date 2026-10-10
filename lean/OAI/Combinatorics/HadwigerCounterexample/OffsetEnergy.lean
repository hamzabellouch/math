import OAI.Combinatorics.HadwigerCounterexample.OffsetRecords

namespace OAI

/-! # Offset Energy -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {p : Shape} {r n N : ℕ}
variable {q t : Place p→ℕ} {S : Cov p N}

def unary (i : Bool) : Party := Pi.single i 1

def heat (p : Shape) {n N} (x : UnitType p n N) (v : Party) (z : Place p) :
    Mat (Fin N) (Fin N) :=
  ∑ i : Bool,v i • (fyAt p (onSide x i) z * (fyAt p (onSide x i) (flipZ p z))ᵀ)
def thermal (p : Shape) {n N} (x : UnitType p n N) (v : Party) {q : Place p→ℕ}
    (A : DTuple (p:=p) q N) : DTuple (p:=p) q N :=
  fun z => heat p x v z * A z

def sparks (p : Shape) {n N} (x : UnitType p n N) (v : Party) {q : Place p→ℕ}
    (A : DTuple (p:=p) q N) (i : Bool) : DTuple (p:=p) q p.h :=
  fun z => v i • ((fyAt p (onSide x i) (flipZ p z))ᵀ * A z)

def glimpse (p : Shape) {n N} (x : UnitType p n N) (i : Bool) {q : Place p→ℕ}
    (A : DTuple (p:=p) q N) :=
  ∀ z,Injective ((fyAt p (onSide x i) (flipZ p z))ᵀ * A z).mulVec

def hfused (p : Shape) (n : ℕ) (r : Place p→ℕ) (A : Bool→DTuple (p:=p) r p.h) :
    WTuple (p:=p) r n :=
  fun z => ∑ i : Bool, IH p n i * A i z

theorem heat_flip (p : Shape) {n N} (x : UnitType p n N) (v : Party) (z : Place p) :
    (heat p x v (flipZ p z))ᵀ=heat p x v z := by
  simp only [heat,Matrix.transpose_sum,Matrix.transpose_smul,Matrix.transpose_mul,
    Matrix.transpose_transpose,flipZ_flip]

theorem heat_unary (x : UnitType p n N) (i) (z : Place p) :
    heat p x (unary i) z=fyAt p (onSide x i) z * (fyAt p (onSide x i) (flipZ p z))ᵀ := by
  rw [heat,Finset.sum_eq_single i]
  · simp [unary]
  · intro j _ hj; simp [unary,hj]
  simp

theorem fuse_val (x : UnitType p n N) (v : Party) (A : DTuple (p:=p) q N) (z : Place p) :
    images x z * hfused p n q (sparks p x v A) z=thermal p x v A z := by
  classical
  unfold hfused thermal heat sparks
  rw [Fintype.sum_bool,Fintype.sum_bool]
  simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.add_mul,Matrix.mul_add]
  have he (i : Bool) :
      images x z * (IH p n i * ((fyAt p (onSide x i) (flipZ p z))ᵀ * A z))=
        fyAt p (onSide x i) z*(fyAt p (onSide x i) (flipZ p z))ᵀ * A z := by
    rw [← Matrix.mul_assoc (images x z),images_ih]
    change _ * (_ * _) = _ * _ * _
    exact (Matrix.mul_assoc ..).symm
  rw [he,he]

theorem fused_support (B : Bool→DTuple (p:=p) q p.h) (z : Place p) :
    colSp (hfused p n q B z)≤channels p n := by
  unfold hfused
  rw [Fintype.sum_bool]
  rintro x ⟨y,rfl⟩
  rw [mulVecLin_apply,Matrix.add_mulVec,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  exact Submodule.add_mem _ (ih_le_channels true ⟨_,rfl⟩) (ih_le_channels false ⟨_,rfl⟩)

theorem fused_inj (A : Bool→DTuple (p:=p) q p.h) (z : Place p) (i : Bool)
    (h : Injective (A i z).mulVec) :
    Injective (hfused p n q A z).mulVec := by
  have hh : (IH p n i)ᵀ*hfused p n q A z=A i z := by
    unfold hfused
    rw [Fintype.sum_bool,Matrix.mul_add]
    simp only [← Matrix.mul_assoc]
    cases i <;>
      simp only [IH_self,IH_cross (show false≠true by decide),IH_cross (show true≠false by decide),
        Matrix.zero_mul,Matrix.one_mul,add_zero,zero_add]
  intro x y hx
  apply h
  rw [←hh, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,hx]

theorem hotfused (x : UnitType p n N) (v : Party) (A : DTuple (p:=p) q N)
    (i : Bool) (h : v i=1) (hh : glimpse p x i A) (z) :
    Injective (hfused p n q (sparks p x v A) z).mulVec := by
  refine fused_inj _ _ i ?_
  unfold sparks; rw [h,one_smul]
  exact hh z

theorem tone_heat (x : UnitType p n N) (v : Party) (T : Ambient p N) :
    tone p x v T = ∑ e : Comp p.g, mpair (heat p x v (e,false)) (T e) := by
  classical
  simp only [tone,joinPhase,uPhase,heat,mpair_sum,mpair_smul,LinearMap.sum_apply,
    LinearMap.comp_apply,LinearMap.smul_apply,smul_eq_mul,mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  cases i <;> rfl

variable {I J : Type} [Fintype I] [Fintype J]

private theorem trace_shift_l (M : Mat I I) (A V : Mat I J) :
    mpair M (A*Vᵀ)=mpair V (Mᵀ*A) := by
  rw [mpair_comm V]
  change (M*(A*Vᵀ)ᵀ).trace=((Mᵀ*A)* Vᵀ).trace
  rw [Matrix.transpose_mul,Matrix.transpose_transpose,
    ←Matrix.trace_transpose ((Mᵀ*A) * Vᵀ),Matrix.transpose_mul,Matrix.transpose_mul,
      Matrix.transpose_transpose,Matrix.transpose_transpose,←Matrix.mul_assoc V,
      Matrix.trace_mul_comm _ M]

private theorem trace_shift_r (M : Mat I I) (A V : Mat I J) :
    mpair M (V*Aᵀ)=mpair V (M*A) := by
  rw [mpair_comm V]
  change (M*(V*Aᵀ)ᵀ).trace=((M*A)* Vᵀ).trace
  rw [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]

theorem tone_offset (x : UnitType p n N) (v : Party) (M : Atlas p r S) (A : Batch M N) :
    tone p x v (spelled M A)=tupleB p (breadth M) N A (thermal p x v (src M))+
      tone p x v (edgeCost M) := by
  rw [tone_heat,tone_heat,tupleB_val,Fintype.sum_prod_type]
  simp only [spelled,map_add,Finset.sum_add_distrib,Fintype.sum_bool]
  refine congrArg (fun z => z+_) (congrArg₂ (·+·) ?_ ?_)
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [trace_shift_l,show (heat p x v (e,false))ᵀ=heat p x v (e,true) from
      heat_flip p x v (e,true)]
    rfl
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [trace_shift_r]; rfl
end HadwigerCounterexample

end

end OAI
