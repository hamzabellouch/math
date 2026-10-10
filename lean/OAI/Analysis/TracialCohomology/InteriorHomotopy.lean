import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.HilbertNormalParts

namespace OAI

/-! Interior homotopy for bounded Hochschild cohomology. -/

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma firstSliceN_add' {n : ℕ} (f g : Cochain M (n+1)) (v : Fin n → M) :
    firstSliceN (f+g) v=firstSliceN f v+firstSliceN g v := by
  ext a
  simp only [firstSliceN_apply,add_apply]

lemma firstSliceN_smul' {n : ℕ} (c : ℂ) (f : Cochain M (n+1)) (v : Fin n → M) :
    firstSliceN (c • f) v=c • firstSliceN f v := by
  ext a
  simp only [firstSliceN_apply,smul_apply]

lemma normalFirst_add' {n : ℕ} (f g : Cochain M (n+1)) :
    normalFirst e (f+g)=normalFirst e f+normalFirst e g := by
  ext v
  rw [← Fin.cons_self_tail v]
  simp only [normalFirst_cons,firstSliceN_add',map_add,add_apply]

lemma normalFirst_smul' {n : ℕ} (c : ℂ) (f : Cochain M (n+1)) :
    normalFirst e (c • f)=c • normalFirst e f := by
  ext v
  rw [← Fin.cons_self_tail v]
  simp only [normalFirst_cons,firstSliceN_smul',map_smul,smul_apply]

def normalFirstCLM (n : ℕ) : Cochain M (n+1) →L[ℂ] Cochain M (n+1) :=
  LinearMap.mkContinuous
    { toFun := normalFirst e
      map_add' := normalFirst_add' e
      map_smul' := normalFirst_smul' e }
    4 (normalFirst_norm e)

@[simp] lemma normalFirstCLM_apply (n : ℕ) (f : Cochain M (n+1)) :
    normalFirstCLM e n f=normalFirst e f := rfl

def normalSecond {n : ℕ} (f : Cochain M (n+2)) : Cochain M (n+2) :=
  ((normalFirstCLM e n).comp f.curryLeft).uncurryLeft

@[simp] lemma normalSecond_cons {n : ℕ} (f : Cochain M (n+2))
    (a : M) (v : Fin (n+1) → M) :
    normalSecond e f (Fin.cons a v)=normalFirst e (f.curryLeft a) v := rfl

def secondInsertion {n : ℕ} (f : Cochain M (n+2)) : Cochain M (n+1) :=
  ((((continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (n+1) => M) M).toContinuousLinearEquiv.toContinuousLinearMap).comp
      ((normalFirstCLM e n).comp f.curryLeft)).flip 1).uncurryLeft

@[simp] lemma secondInsertion_cons {n : ℕ} (f : Cochain M (n+2))
    (a : M) (v : Fin n → M) :
    secondInsertion e f (Fin.cons a v)=normalFirst e (f.curryLeft a) (Fin.cons 1 v) := rfl

def secondRemainder {n : ℕ} (f : Cochain M (n+2)) : Cochain M (n+2) :=
  f+differential (secondInsertion e f)

lemma secondRemainder_identity {n : ℕ} (f : Cochain M (n+2)) (v : Fin (n+2) → M) :
    f v=secondRemainder e f v+differentialValue (-secondInsertion e f) v := by
  simp only [secondRemainder,add_apply,differential_apply]
  rw [show -secondInsertion e f=(-1:ℂ) • secondInsertion e f by simp,
    differentialValue_smul]
  simp

lemma secondRemainder_cocycle {n : ℕ} (f : Cochain M (n+2))
    (hf : ∀ v,differentialValue f v=0) (v : Fin (n+3) → M) :
    differentialValue (secondRemainder e f) v=0 := by
  rw [secondRemainder,differentialValue_add,hf,differential_is_cocycle,add_zero]

lemma normalSecond_norm {n : ℕ} (f : Cochain M (n+2)) :
    ‖normalSecond e f‖≤4*‖f‖ := by
  have hN : ‖normalFirstCLM e n‖≤4 :=
    LinearMap.mkContinuous_norm_le _ (by norm_num) (normalFirst_norm e)
  rw [normalSecond,ContinuousLinearMap.uncurryLeft_norm]
  calc
    _ ≤ ‖normalFirstCLM e n‖*‖f.curryLeft‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 4*‖f‖ := by rw [ContinuousMultilinearMap.curryLeft_norm]; gcongr

lemma differentialValue_cons_cons {n : ℕ} (f : Cochain M (n+2))
    (a b : M) (v : Fin (n+1) → M) :
    differentialValue f (Fin.cons a (Fin.cons b v))=
      a*f (Fin.cons b v)-f (Fin.cons (a*b) v)+
      f (Fin.cons a (Fin.cons (b*v 0) (fun i : Fin n => v i.succ)))+
      (∑ j : Fin n,((-1:ℂ)^(j.val+3)) •
        f (Fin.cons a (Fin.cons b (mergeInputs v j))))+
      ((-1:ℂ)^(n+3)) •
        (f (Fin.cons a (Fin.cons b (fun i : Fin n => v i.castSucc)))*v (Fin.last n)) := by
  rw [differentialValue_cons,Fin.sum_univ_succ]
  have hinit : (fun i : Fin (n+1) => (Fin.cons b v : Fin (n+2) → M) i.castSucc)=
      Fin.cons b (fun i : Fin n => v i.castSucc) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hlast : (Fin.cons b v : Fin (n+2) → M) (Fin.last (n+1))=v (Fin.last n) := by
    change (Fin.cons b v : Fin (n+2) → M) (Fin.last n).succ=_
    simp
  simp only [Fin.cons_zero,Fin.cons_succ,mergeInputs_cons_zero,mergeInputs_cons_succ,
    Fin.val_zero,Fin.val_succ,zero_add,Nat.add_assoc,hinit,hlast]
  norm_num only [neg_sq,one_pow,one_smul]
  abel

lemma normalSecond_cocycle_identity {n : ℕ} (f : Cochain M (n+2))
    (hf : ∀ z,differentialValue f z=0)
    (hfirst : ∀ v,HasPreadjoint e (firstSliceN f v))
    (a b : M) (v : Fin (n+1) → M) :
    a*f (Fin.cons b v)-f (Fin.cons (a*b) v)+
      normalSecond e f (Fin.cons a (Fin.cons (b*v 0) (fun i : Fin n => v i.succ)))+
      (∑ j : Fin n,((-1:ℂ)^(j.val+3)) •
        normalSecond e f (Fin.cons a (Fin.cons b (mergeInputs v j))))+
      ((-1:ℂ)^(n+3)) •
        (normalSecond e f (Fin.cons a (Fin.cons b (fun i : Fin n => v i.castSucc)))*v (Fin.last n))=0 := by
  let L := ContinuousLinearMap.mul ℂ M
  let R := (ContinuousLinearMap.mul ℂ M).flip
  have hop :
      (L a).comp (firstSliceN f v)-(firstSliceN f v).comp (L a)+
      (firstSliceN (f.curryLeft a) (fun i : Fin n => v i.succ)).comp (R (v 0))+
      (∑ j : Fin n,((-1:ℂ)^(j.val+3)) • firstSliceN (f.curryLeft a) (mergeInputs v j))+
      ((-1:ℂ)^(n+3)) •
        (R (v (Fin.last n))).comp (firstSliceN (f.curryLeft a) (fun i : Fin n => v i.castSucc))=0 := by
    ext x
    simpa only [L,R,ContinuousLinearMap.comp_apply,ContinuousLinearMap.mul_apply',
      ContinuousLinearMap.flip_apply,firstSliceN_apply,sub_apply,add_apply,sum_apply,
      smul_apply,zero_apply,ContinuousMultilinearMap.curryLeft_apply,
      differentialValue_cons_cons] using hf (Fin.cons a (Fin.cons x v))
  have h := congrArg (fun T : M →L[ℂ] M => operatorNormalPart e T b) hop
  dsimp only [L,R] at h
  simp only [map_sub,map_add,map_sum,map_smul,map_zero,sub_apply,add_apply,sum_apply,
    smul_apply,zero_apply,
    operatorNormalPart_comp_normal e _ _ ((HochschildSakai.abstract_multiplication_normal e).1 a),
    operatorNormalPart_comp_normal e _ _ ((HochschildSakai.abstract_multiplication_normal e).2 (v (Fin.last n))),
    operatorNormalPart_comp_left,operatorNormalPart_comp_right,
    operatorNormalPart_fixes e _ (hfirst v),ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply',ContinuousLinearMap.flip_apply,firstSliceN_apply,
    ← normalFirst_cons] at h
  simpa only [normalSecond_cons] using h

lemma secondRemainder_apply {n : ℕ} (f : Cochain M (n+2))
    (hf : ∀ z,differentialValue f z=0)
    (hfirst : ∀ v,HasPreadjoint e (firstSliceN f v))
    (a : M) (v : Fin (n+1) → M) :
    secondRemainder e f (Fin.cons a v)=
      normalSecond e f (Fin.cons a v)+a*f (Fin.cons 1 v)+
      a*secondInsertion e f v-
      secondInsertion e f (Fin.cons (a*v 0) (fun i : Fin n => v i.succ)) := by
  have h := normalSecond_cocycle_identity e f hf hfirst a 1 v
  have hv : Fin.cons (v 0) (fun i : Fin n => v i.succ)=v := Fin.cons_self_tail v
  simp only [one_mul,mul_one,hv,normalSecond_cons,← secondInsertion_cons] at h
  simp only [secondRemainder,add_apply,differential_apply,differentialValue_cons]
  rw [sign_succ (n+2)] at h
  have hsign (j : Fin n) : (-1:ℂ)^(j.val+3) = -((-1:ℂ)^(j.val+2)) := sign_succ _
  simp only [hsign,neg_smul,Finset.sum_neg_distrib] at h
  simp only [normalSecond_cons]
  linear_combination (norm := module) -h

lemma secondInsertion_norm {n : ℕ} (f : Cochain M (n+2)) :
    ‖secondInsertion e f‖≤4*‖f‖ := by
  have h1 : ‖(1:M)‖≤1 := by
    rcases subsingleton_or_nontrivial M with h|h
    · simp [Subsingleton.elim (1:M) 0]
    · simp
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  rw [← Fin.cons_self_tail v,secondInsertion_cons]
  calc
    _ ≤ ‖normalFirst e (f.curryLeft (v 0))‖*‖(1:M)‖*
        ∏ i : Fin n,‖v i.succ‖ :=
      ContinuousMultilinearMap.norm_map_cons_le _ _ _
    _ ≤ (4*‖f.curryLeft (v 0)‖)*1*∏ i : Fin n,‖v i.succ‖ := by
      gcongr
      exact normalFirst_norm e _
    _ ≤ (4*(‖f‖*‖v 0‖))*∏ i : Fin n,‖v i.succ‖ := by
      rw [mul_one]
      gcongr
      simpa only [ContinuousMultilinearMap.curryLeft_norm] using
        f.curryLeft.le_opNorm (v 0)
    _ = _ := by simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,Fin.tail]; ring

lemma firstNormalRemainderN_one {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v,differentialValue f v=0) (v : Fin n → M) :
    firstNormalRemainderN e f (Fin.cons 1 v)=0 := by
  rw [firstNormalRemainderN_apply e f hf]
  simp only [Fin.cons_zero,Fin.cons_succ,one_mul,sub_self]

lemma normalSecond_first_one {n : ℕ} (f : Cochain M (n+2))
    (hu : ∀ v,f (Fin.cons 1 v)=0) (v : Fin (n+1) → M) :
    normalSecond e f (Fin.cons 1 v)=0 := by
  have hz : f.curryLeft 1=0 := by
    ext v
    exact hu v
  rw [normalSecond_cons,hz]
  rw [← Fin.cons_self_tail v,normalFirst_cons]
  have hslice : firstSliceN (0 : Cochain M (n+1)) (fun i => v i.succ)=0 := by
    ext a
    simp
  change operatorNormalPart e (firstSliceN (0 : Cochain M (n+1)) (fun i => v i.succ)) (v 0)=0
  rw [hslice,map_zero,zero_apply]

lemma secondInsertion_first_one {n : ℕ} (f : Cochain M (n+2))
    (hu : ∀ v,f (Fin.cons 1 v)=0) (v : Fin n → M) :
    secondInsertion e f (Fin.cons 1 v)=0 :=
  normalSecond_first_one e f hu (Fin.cons 1 v)

lemma secondRemainder_first_one {n : ℕ} (f : Cochain M (n+2))
    (hf : ∀ v,differentialValue f v=0)
    (hfirst : ∀ v,HasPreadjoint e (firstSliceN f v))
    (hu : ∀ v,f (Fin.cons 1 v)=0) (v : Fin (n+1) → M) :
    secondRemainder e f (Fin.cons 1 v)=0 := by
  have hv : Fin.cons (v 0) (fun i : Fin n => v i.succ)=v := Fin.cons_self_tail v
  rw [secondRemainder_apply e f hf hfirst,normalSecond_first_one e f hu,hu,
    mul_zero,zero_add,one_mul,one_mul,hv,zero_add,sub_self]

lemma secondRemainder_second_one {n : ℕ} (f : Cochain M (n+2))
    (hf : ∀ v,differentialValue f v=0)
    (hfirst : ∀ v,HasPreadjoint e (firstSliceN f v))
    (hu : ∀ v,f (Fin.cons 1 v)=0) (a : M) (v : Fin n → M) :
    secondRemainder e f (Fin.cons a (Fin.cons 1 v))=0 := by
  rw [secondRemainder_apply e f hf hfirst,hu,secondInsertion_first_one e f hu]
  simp only [normalSecond_cons,← secondInsertion_cons,mul_zero,add_zero,
    Fin.cons_zero,Fin.cons_succ,mul_one,sub_self]

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def firstSliceCLM {n : ℕ} (v : Fin n → M) :
    Cochain M (n+1) →L[ℂ] M →L[ℂ] M :=
  LinearMap.mkContinuous
    { toFun := fun f => firstSliceN f v
      map_add' := fun f g => firstSliceN_add' f g v
      map_smul' := fun c f => firstSliceN_smul' c f v }
    (∏ i,‖v (Fin.rev i)‖) (by
      intro f
      change ‖firstSliceN f v‖ ≤ _
      have h := (reverseArguments f).curryRight.le_opNorm (v ∘ Fin.rev)
      simpa only [firstSliceN,ContinuousMultilinearMap.curryRight_norm,reverseArguments_norm,
        Function.comp_apply,mul_comm] using h)

@[simp] lemma firstSliceCLM_apply {n : ℕ} (v : Fin n → M)
    (f : Cochain M (n+1)) : firstSliceCLM v f=firstSliceN f v := rfl

def firstTwoSlice {n : ℕ} (f : Cochain M (n+2)) (v : Fin n → M) :
    M →L[ℂ] M →L[ℂ] M := (firstSliceCLM v).comp f.curryLeft

@[simp] lemma firstTwoSlice_apply {n : ℕ} (f : Cochain M (n+2))
    (v : Fin n → M) (a b : M) :
    firstTwoSlice f v a b=f (Fin.cons a (Fin.cons b v)) := by
  exact firstSliceN_apply (f.curryLeft a) v b

lemma firstTwoSlice_flip {n : ℕ} (f : Cochain M (n+2)) (v : Fin n → M) (b : M) :
    (firstTwoSlice f v).flip b=firstSliceN f (Fin.cons b v) := by
  ext a
  simp

lemma normalSecond_first_slice {n : ℕ} (f : Cochain M (n+2))
    (v : Fin n → M) (b : M) :
    firstSliceN (normalSecond e f) (Fin.cons b v)=
      (((operatorNormalPart e).comp (firstTwoSlice f v)).flip b) := by
  ext a
  simp only [firstSliceN_apply,normalSecond_cons,normalFirst_cons]
  rfl

lemma normalSecond_second_normal {n : ℕ} (f : Cochain M (n+2))
    (a : M) (v : Fin n → M) :
    HasPreadjoint e (firstSliceN ((normalSecond e f).curryLeft a) v) := by
  have heq : firstSliceN ((normalSecond e f).curryLeft a) v=
      operatorNormalPart e (firstSliceN (f.curryLeft a) v) := by
    ext b
    simp only [firstSliceN_apply]
    exact normalFirst_cons e (f.curryLeft a) b v
  rw [heq]
  exact operatorNormalPart_normal e _

lemma normalSecond_first_normal_factored {n : ℕ} (f : Cochain M (n+2))
    (v : Fin n → M)
    (H : X → Type v) [∀ z,NormedAddCommGroup (H z)] [∀ z,InnerProductSpace ℂ (H z)]
    [∀ z,CompleteSpace (H z)]
    (α : ∀ z,H z →L[ℂ] StrongDual ℂ M) (β : ∀ z,M →L[ℂ] H z)
    (hfac : ∀ z a b,predualEmbedding e z (f (Fin.cons a (Fin.cons b v)))=
      α z (β z b) a)
    (hfirst : ∀ v,HasPreadjoint e (firstSliceN f v)) (b : M) :
    HasPreadjoint e (firstSliceN (normalSecond e f) (Fin.cons b v)) := by
  rw [normalSecond_first_slice]
  apply operator_bilinear_normalization e (firstTwoSlice f v) H α β
  · simpa only [firstTwoSlice_apply] using hfac
  · intro c
    rw [firstTwoSlice_flip]
    exact hfirst _

lemma secondInsertion_first_slice {n : ℕ} (f : Cochain M (n+2)) (v : Fin n → M) :
    firstSliceN (secondInsertion e f) v=
      firstSliceN (normalSecond e f) (Fin.cons 1 v) := by
  ext a
  simp only [firstSliceN_apply,secondInsertion_cons,normalSecond_cons]

omit [CompleteSpace X] in
lemma HasPreadjoint.add {S T : M →L[ℂ] M}
    (hS : HasPreadjoint e S) (hT : HasPreadjoint e T) : HasPreadjoint e (S+T) := by
  intro z
  obtain ⟨w,hw⟩ := hS z
  obtain ⟨y,hy⟩ := hT z
  refine ⟨w+y,fun a => ?_⟩
  simp only [add_apply,map_add,hw,hy]

omit [CompleteSpace X] in
lemma HasPreadjoint.sub {S T : M →L[ℂ] M}
    (hS : HasPreadjoint e S) (hT : HasPreadjoint e T) : HasPreadjoint e (S-T) := by
  intro z
  obtain ⟨w,hw⟩ := hS z
  obtain ⟨y,hy⟩ := hT z
  refine ⟨w-y,fun a => ?_⟩
  simp only [sub_apply,map_sub,hw,hy]

omit [CompleteSpace X] in
lemma HasPreadjoint.comp {S T : M →L[ℂ] M}
    (hS : HasPreadjoint e S) (hT : HasPreadjoint e T) : HasPreadjoint e (S.comp T) := by
  intro z
  obtain ⟨w,hw⟩ := hS z
  obtain ⟨y,hy⟩ := hT w
  exact ⟨y,fun a => (hw (T a)).trans (hy a)⟩

lemma secondRemainder_first_normal {n : ℕ} (f : Cochain M (n+2))
    (hf : ∀ z,differentialValue f z=0)
    (hfirst : ∀ v,HasPreadjoint e (firstSliceN f v))
    (hN : ∀ v,HasPreadjoint e (firstSliceN (normalSecond e f) v))
    (v : Fin (n+1) → M) :
    HasPreadjoint e (firstSliceN (secondRemainder e f) v) := by
  let R := (ContinuousLinearMap.mul ℂ M).flip
  let h := secondInsertion e f
  have hh : HasPreadjoint e (firstSliceN h (fun i : Fin n => v i.succ)) := by
    rw [show h=secondInsertion e f from rfl,secondInsertion_first_slice]
    exact hN _
  have hR := (HochschildSakai.abstract_multiplication_normal e).2
  have heq : firstSliceN (secondRemainder e f) v=
      firstSliceN (normalSecond e f) v+R (f (Fin.cons 1 v))+R (h v)-
        (firstSliceN h (fun i : Fin n => v i.succ)).comp (R (v 0)) := by
    ext a
    simpa only [R,h,firstSliceN_apply,add_apply,
      sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply',Fin.tail]
      using secondRemainder_apply e f hf hfirst a v
  rw [heq]
  exact (((hN v).add e (hR _)).add e (hR _)).sub e (hh.comp e (hR _))

lemma secondRemainder_second_normal {n : ℕ} (f : Cochain M (n+2))
    (hf : ∀ z,differentialValue f z=0)
    (hfirst : ∀ v,HasPreadjoint e (firstSliceN f v))
    (hu : ∀ v,f (Fin.cons 1 v)=0)
    (hh : ∀ v,HasPreadjoint e (firstSliceN (secondInsertion e f) v))
    (a : M) (v : Fin n → M) :
    HasPreadjoint e (firstSliceN ((secondRemainder e f).curryLeft a) v) := by
  let L := ContinuousLinearMap.mul ℂ M a
  let h := secondInsertion e f
  have heq : firstSliceN ((secondRemainder e f).curryLeft a) v=
      firstSliceN ((normalSecond e f).curryLeft a) v+
        L.comp (firstSliceN h v)-(firstSliceN h v).comp L := by
    ext b
    have hh := secondRemainder_apply e f hf hfirst a (Fin.cons b v)
    rw [hu,mul_zero,add_zero] at hh
    simpa only [L,h,firstSliceN_apply,add_apply,
      sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mul_apply',ContinuousMultilinearMap.curryLeft_apply,
      Fin.cons_zero,Fin.cons_succ] using hh
  rw [heq]
  have hL := (HochschildSakai.abstract_multiplication_normal e).1 a
  exact ((normalSecond_second_normal e f a v).add e (hL.comp e (hh v))).sub e
    ((hh v).comp e hL)

theorem second_slot_step_of_factors {n : ℕ} (f : Cochain M (n+2))
    (hf : ∀ z,differentialValue f z=0)
    (hfirst : ∀ v,HasPreadjoint e (firstSliceN f v))
    (hu : ∀ v,f (Fin.cons 1 v)=0)
    (H : (Fin n → M) → X → Type v)
    [∀ v z,NormedAddCommGroup (H v z)] [∀ v z,InnerProductSpace ℂ (H v z)]
    [∀ v z,CompleteSpace (H v z)]
    (α : ∀ v z,H v z →L[ℂ] StrongDual ℂ M) (β : ∀ v z,M →L[ℂ] H v z)
    (hfac : ∀ v z a b,predualEmbedding e z (f (Fin.cons a (Fin.cons b v)))=
      α v z (β v z b) a) :
    ∃ (R : Cochain M (n+2)) (h : Cochain M (n+1)),
      (∀ v,differentialValue R v=0) ∧
      (∀ v,f v=R v+differentialValue h v) ∧
      ‖h‖≤4*‖f‖ ∧
      (∀ v,HasPreadjoint e (firstSliceN R v)) ∧
      (∀ a v,HasPreadjoint e (firstSliceN (R.curryLeft a) v)) ∧
      (∀ v,R (Fin.cons 1 v)=0) ∧
      (∀ a v,R (Fin.cons a (Fin.cons 1 v))=0) := by
  have hN (w : Fin (n+1) → M) :
      HasPreadjoint e (firstSliceN (normalSecond e f) w) := by
    rw [← Fin.cons_self_tail w]
    exact normalSecond_first_normal_factored e f (fun i => w i.succ)
      (H _) (α _) (β _) (hfac _) hfirst (w 0)
  have hh (v : Fin n → M) :
      HasPreadjoint e (firstSliceN (secondInsertion e f) v) := by
    rw [secondInsertion_first_slice]
    exact hN _
  exact ⟨secondRemainder e f,-secondInsertion e f,
    secondRemainder_cocycle e f hf,secondRemainder_identity e f,
    by simpa only [norm_neg] using secondInsertion_norm e f,
    secondRemainder_first_normal e f hf hfirst hN,
    secondRemainder_second_normal e f hf hfirst hu hh,
    secondRemainder_first_one e f hf hfirst hu,
    secondRemainder_second_one e f hf hfirst hu⟩

end BoundedHochschild

end

end OAI
