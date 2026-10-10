import OAI.Combinatorics.HadwigerCounterexample.ImageCharacterBounds

namespace OAI

/-! # Gram Character Quotients -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

def cpDual (p : Shape) {n} (A : Cross p n) :
    Cross p n →ₗ[F] F :=
  ∑ z : Place p, mpair (A z) ∘ₗ LinearMap.proj z

theorem cpDual_val (A B : Cross p n) :
    cpDual p A B=∑ z,mpair (A z) (B z) := by
  unfold cpDual; rw [LinearMap.sum_apply]; rfl

variable {I J L U : Type} [Fintype I] [Fintype J] [Fintype L] [Fintype U]

private theorem pair_trace (A B : Mat I J) : mpair A B=(A*Bᵀ).trace := by
  change ∑ i:I, ∑ j:J,A i j * B i j = _
  rfl

private theorem pair_transfer (X : Mat U I) (Y : Mat U J) (A : Mat I L) (B : Mat J L) :
    mpair (A*Bᵀ) (Xᵀ*Y)=mpair (X*A) (Y*B) := by
  rw [pair_trace,pair_trace,Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose]
  rw [← Matrix.mul_assoc _ Yᵀ X,Matrix.trace_mul_comm _ X]
  simp only [Matrix.mul_assoc]

private theorem proj_opposite [DecidableEq I] (S : Space (Vec I)) :
    ∃ A : Mat I I,(∀ x,x-A *ᵥ x∈S) ∧ Disjoint (colSp A) S := by
  classical
  obtain ⟨B,hB⟩ := proj_exists S ⊥ disjoint_bot_right
  refine ⟨1-B,fun x => ?_,?_⟩
  · rw [Matrix.sub_mulVec,Matrix.one_mulVec,sub_sub_cancel]
    exact hB.onto x
  rw [disjoint_iff_inf_le]
  rintro x ⟨⟨y,rfl⟩,hy⟩
  rw [mulVecLin_apply,Matrix.sub_mulVec,Matrix.one_mulVec] at hy ⊢
  have hx := hB.fixes _ hy
  rw [Matrix.mulVec_sub,hB.fixes (B *ᵥ y) (hB.onto _),sub_self] at hx
  rw [←hx]; exact Submodule.zero_mem _

private theorem free_pull (p : Shape) {n} (A : Cross p n) (s t : Plan p n) :
    ∃ P : Cross p n,(∀ z, Disjoint (colSp (P z)) (s z) ∧
        Disjoint (colSp (P z)ᵀ) (t (flipZ p z))) ∧
      ∀ X Y, rowAgree s X Y → rowAgree t (reciprocal p X) (reciprocal p Y) →
        cpDual p A (X-Y) = cpDual p P (X-Y) := by
  classical
  choose S hS hL using fun z => proj_opposite (s z)
  choose T hT hR using fun z => proj_opposite (t (flipZ p z))
  let P (z : Place p) := liftM (S z) (T z) (A z)
  refine ⟨P,fun z => ⟨(hL z).mono_left (colSp_lift_le ..),by
    unfold P; rw [liftM_transpose]; exact (hR z).mono_left (colSp_lift_le ..)⟩,fun X Y hX hY => ?_⟩
  rw [cpDual_val,cpDual_val]
  refine Finset.sum_congr rfl fun z _ => ?_
  let M := X z-Y z
  have he : pullM (S z) (T z) M=M := by
    apply evmat_ext; intro x y
    rw [evmat_pull]
    let x' := S z *ᵥ x
    let y' := T z *ᵥ y
    have hL : evmat M (x-x') y=0 := by
      rw [show M=X z-Y z from rfl,evmat_subM,hX z _ (hS z x),sub_self]
    have hR : evmat M x' (y-y')=0 := by
      have h := hY (flipZ p z) _ (hT z y) x'
      simp only [reciprocal,flipZ_flip,evmat_transpose] at h
      rw [show M=X z-Y z from rfl,evmat_subM,h,sub_self]
    unfold evmat at hL hR ⊢
    rw [sub_dotProduct,sub_eq_zero] at hL
    rw [Matrix.mulVec_sub, dotProduct_sub,sub_eq_zero] at hR
    exact hR.symm.trans hL.symm
  change mpair (A z) M=mpair (liftM _ _ _) M
  rw [mpair_comm (A z)]
  rw [mpair_comm (liftM _ _ _),mpair_liftM,show liftM (S z)ᵀ (T z)ᵀ M=M from he]

theorem factor_free {A : Cross p n} (s t : Plan p n)
    (h : ∀ z, Disjoint (colSp (A z)) (s z) ∧ Disjoint (colSp (A z)ᵀ) (t (flipZ p z))) :
    ∃ (r : Place p→ℕ) (B C : WTuple (p:=p) r n), (∀ z,r z=(A z).rank) ∧
      (∀ z,Function.Injective (B z).mulVec ∧ Disjoint (colSp (B z)) (s z)) ∧
      (∀ z,Function.Injective (C z).mulVec ∧ Disjoint (colSp (C z)) (t (flipZ p z))) ∧
      (∀ z,A z=B z * (C z)ᵀ) := by
  classical
  choose B C hB hC hA using fun z => rank_product (A z)
  let G (z : Place p) := (C z)ᵀ
  have ht z : Function.Injective (G z).mulVec :=
    transpose_surj_iff.mp (by unfold G; rw [Matrix.transpose_transpose]; exact hC _)
  refine ⟨_,B,G,fun _ => rfl,fun z => ⟨hB z,(h z).1.mono_left ?_⟩,
     fun z => ⟨ht z,(h z).2.mono_left ?_⟩,
     fun z => by unfold G; rw [Matrix.transpose_transpose,hA]⟩
  · rintro x ⟨v,rfl⟩
    obtain ⟨w,rfl⟩ := hC z v
    refine ⟨w,?_⟩
    rw [mulVecLin_apply,mulVecLin_apply,Matrix.mulVec_mulVec,hA]
  · rintro x ⟨v,rfl⟩
    obtain ⟨w,rfl⟩ := (transpose_surj_iff.mpr (hB z)) v
    refine ⟨w,?_⟩
    rw [mulVecLin_apply,mulVecLin_apply]
    unfold G; rw [Matrix.mulVec_mulVec,← transpose_mul,hA]

theorem gramCharacter (Q M : Cross p n) {u w : Wgt (UnitType p n N)}
    (hu : IsLaw u) (hw : IsLaw w) {f b : Pin p n N}
    (hc : f.clear 0.05 u) (hd : b.clear 0.05 w)
    (h : ∀ x,u x≠0 → ∀ y,w y≠0 → rowAgree f.sp (actual p x y) Q ∧
      rowAgree b.sp (actual p y x) (reciprocal p Q)) :
    let Y := avg (pairW u w) (fun x =>
      wsign (cpDual p M (actual p x.1 x.2-Q)))
    Y=1 ∨ |Y| ≤ bp (-0.45*N) := by
  classical
  dsimp only
  obtain ⟨P,hP,hX⟩ := free_pull p M f.sp b.sp
  obtain ⟨r,B,C,hr,hB,hC,hY⟩ := factor_free f.sp b.sp hP
  let s := pairW u w
  have he :
      avg s (fun x => wsign (cpDual p M (actual p x.1 x.2-Q))) =
      avg s (fun x => wsign (cpDual p P (actual p x.1 x.2-Q))) := by
    refine avg_congr fun ⟨x,y⟩ hxy => ?_
    rw [show cpDual p M (actual p x y-Q)=_ from hX _ _ _ _]
    · exact (h x (left_ne_zero_of_mul hxy) y (right_ne_zero_of_mul hxy)).1
    rw [reciprocal_actual]; exact (h x (left_ne_zero_of_mul hxy) y (right_ne_zero_of_mul hxy)).2
  rw [he]
  by_cases hh : 1≤∑ z,r z
  · right
    let g := projTuple p r B (Equiv.refl _) (N:=N)
    let g' := projTuple p r C (flipEquiv p) (N:=N)
    let X (x : UnitType p n N × UnitType p n N) := tupleB p r N (g x.1) (g' x.2)
    have hi x :
        wsign (cpDual p P (actual p x.1 x.2-Q))=wsign (X x) * wsign (cpDual p P Q) := by
      simp only [ZModModule.sub_eq_add,map_add,wsign_add]
      have hv : cpDual p P (actual p x.1 x.2)=X x := by
        unfold X; rw [cpDual_val,tupleB_val]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [hY,actual,pair_transfer]; rfl
      rw [hv]
    simp_rw [hi]; rw [avg_mul,abs_mul,wsign_abs,mul_one]
    exact charImages p r B C hu hw hc hd hB hC hh
  left
  have hZ z : P z=0 := by
    have hc : r z ≤ ∑ i,r i := Finset.single_le_sum (fun z _ => Nat.zero_le (r z))
      (Finset.mem_univ _)
    rw [hY]
    have hz : r z=0 := by omega
    have : IsEmpty (Fin (r z)) := hz ▸ Fin.isEmpty'
    ext i j; simp [Matrix.mul_apply]
  have hk x : wsign (cpDual p P x)=1 := by
    rw [cpDual_val]
    have hf z : mpair (P z) (x z)=0 := by rw [hZ,mpair_comm,map_zero]
    simp_rw [hf]
    simp
  simp_rw [hk]; exact (pairW_law hu hw).avg_const _

end HadwigerCounterexample

end

end OAI
