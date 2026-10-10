import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropSquareDensity

namespace OAI


noncomputable section
namespace JiangSuConstruction
open MatrixTensor FourEdgeSurgery
open scoped CStarAlgebra ComplexOrder

variable {p q : ℕ}

lemma left_le_dropFiber {t : Interval} (ht : t≠rightEndpoint) : (MatrixTensor.left (I := Fin p) (J := Fin q)).range≤dropFiber p q t := by
  unfold dropFiber
  split_ifs with h
  · rw [leftAmplification_eq]
  · exact le_top
lemma right_le_dropFiber {t : Interval} (ht : t≠leftEndpoint) : (MatrixTensor.right (I := Fin p) (J := Fin q)).range≤dropFiber p q t := by
  unfold dropFiber
  rw [ite_eq_right ht]
  split_ifs
  · rw [rightAmplification_eq]
  · exact le_top

lemma pFlow_mem_drop (s t : Interval) (r : ℝ)
    (hr : s=rightEndpoint ∨ t=rightEndpoint → r=0) :
    ((pFlow (I := Fin p) (J := Fin q)) r:(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q))))∈fiberAlgebra (dropFiber p q s) (dropFiber p q t) := by
  by_cases h : r=0
  · simp [h]
  · apply fiberAlgebra_mono (left_le_dropFiber (fun e => h (hr (Or.inl e))))
      (left_le_dropFiber (fun e => h (hr (Or.inr e))))
    exact pFlow_mem r
lemma qFlow_mem_drop (s t : Interval) (r : ℝ)
    (hr : s=leftEndpoint ∨ t=leftEndpoint → r=0) :
    ((qFlow (I := Fin p) (J := Fin q)) r:(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q))))∈fiberAlgebra (dropFiber p q s) (dropFiber p q t) := by
  by_cases h : r=0
  · simp [h]
  · apply fiberAlgebra_mono (right_le_dropFiber (fun e => h (hr (Or.inl e))))
      (right_le_dropFiber (fun e => h (hr (Or.inr e))))
    exact qFlow_mem r

lemma squareUnitary_continuous {X : Type*} [TopologicalSpace X]
    (U : X → C(Interval×Interval,unitary (MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q)))))
    (h : ∀ x s t,(U x (s,t):(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q))))∈fiberAlgebra (dropFiber p q s) (dropFiber p q t))
    (hU : Continuous (fun z : X×(Interval×Interval) => U z.1 z.2)) :
    Continuous (fun x => squareUnitary (U x) (h x)) := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_subtype_val.comp hU

variable (a b : C(Interval,ℝ))
variable (ha0 : a leftEndpoint=1) (ha1 : a rightEndpoint=0)
variable (hb0 : b leftEndpoint=0) (hb1 : b rightEndpoint=1)

def residualSection (τ : Interval) : C(Interval×Interval,unitary (MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q)))) :=
  ⟨fun z => (pFlow (I := Fin p) (J := Fin q)) ((τ:ℝ)*(1+b z.1+b z.2*(1-b z.1)-2))*
     (qFlow (I := Fin p) (J := Fin q)) ((τ:ℝ)*(1+a z.1+a z.2*(1-a z.1)-2)),by
    have hp := pFlow_continuous (I := Fin p) (J := Fin q)
    have hq := qFlow_continuous (I := Fin p) (J := Fin q)
    fun_prop⟩

include ha0 hb1 in
lemma residualSection_mem (τ s t : Interval) :
    (residualSection (p := p) (q := q) a b τ (s,t):(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q))))∈
      fiberAlgebra (dropFiber p q s) (dropFiber p q t) := by
  apply mul_mem
  · apply pFlow_mem_drop
    rintro (h|h) <;> subst_vars <;> simp [hb1] <;> norm_num
  · apply qFlow_mem_drop
    rintro (h|h) <;> subst_vars <;> simp [ha0] <;> norm_num

def residualUnitary (τ : Interval) : unitary (Square p q p q) :=
  squareUnitary (residualSection a b τ) (residualSection_mem a b ha0 hb1 τ)

lemma residualUnitary_continuous : Continuous (residualUnitary (p := p) (q := q) a b ha0 hb1) := by
  apply squareUnitary_continuous
  change Continuous (fun z : Interval×(Interval×Interval) =>
    (pFlow (I := Fin p) (J := Fin q)) ((z.1:ℝ)*(1+b z.2.1+b z.2.2*(1-b z.2.1)-2))*
    (qFlow (I := Fin p) (J := Fin q)) ((z.1:ℝ)*(1+a z.2.1+a z.2.2*(1-a z.2.1)-2)))
  have hp := pFlow_continuous (I := Fin p) (J := Fin q)
  have hq := qFlow_continuous (I := Fin p) (J := Fin q)
  fun_prop

lemma residualUnitary_zero : residualUnitary (p := p) (q := q) a b ha0 hb1 leftEndpoint=1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change (((pFlow (I := Fin p) (J := Fin q)) ((0:ℝ)*_)*(qFlow (I := Fin p) (J := Fin q)) ((0:ℝ)*_) : unitary (MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q)))):(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q))))=1
  simp

lemma residualUnitary_one : residualUnitary (p := p) (q := q) a b ha0 hb1 rightEndpoint=
    surgeryUnitary (ContinuousMap.const _ (1 : unitary (TensorMat p q))) a b ha0 ha1 hb0 hb1 rfl rfl := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  rintro ⟨s,t⟩
  change (((pFlow (I := Fin p) (J := Fin q)) ((1:ℝ)*(1+b s+b t*(1-b s)-2))*(qFlow (I := Fin p) (J := Fin q)) ((1:ℝ)*(1+a s+a t*(1-a s)-2)) : unitary (MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q)))):(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q))))=
    ((surgery (pFlow (I := Fin p) (J := Fin q)) (qFlow (I := Fin p) (J := Fin q)) (rightUnitary 1) (rightUnitary 1) (rightUnitary 1) (a s) (b s) (a t) (b t) : unitary (MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q)))) : (MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q))))
  simp only [one_mul,rightUnitary_one]
  rw [surgery_trivial (pFlow (I := Fin p) (J := Fin q)) (qFlow (I := Fin p) (J := Fin q)) flows_commute]
  have hp := pFlow_period (I := Fin p) (J := Fin q) (1+b s+b t*(1-b s)-2)
  have hq := qFlow_period (I := Fin p) (J := Fin q) (1+a s+a t*(1-a s)-2)
  simp only [sub_add_cancel] at hp hq
  rw [hp,hq]

def contractInterval (τ s : Interval) : Interval :=
  ⟨(τ:ℝ)*(s:ℝ),mul_nonneg τ.property.1 s.property.1,
    (mul_le_mul_of_nonneg_right τ.property.2 s.property.1).trans (by simpa using s.property.2)⟩
lemma contractInterval_continuous : Continuous (fun z : Interval×Interval => contractInterval z.1 z.2) := by
  apply continuous_induced_rng.mpr
  exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
@[simp] lemma contractInterval_zero (s : Interval) : contractInterval leftEndpoint s=leftEndpoint := by
  apply Subtype.ext; simp [contractInterval,leftEndpoint]
@[simp] lemma contractInterval_one (s : Interval) : contractInterval rightEndpoint s=s := by
  apply Subtype.ext; simp [contractInterval,rightEndpoint]

variable (W : C(Interval×Interval,unitary (TensorMat p q))) (hWd : ∀ s,W (s,s)=1)
def contractedMatching (τ : Interval) : C(Interval×Interval,unitary (TensorMat p q)) :=
  W.comp ⟨fun z => (contractInterval τ z.1,contractInterval τ z.2),by
    have hc := contractInterval_continuous
    exact (hc.comp (continuous_const.prodMk continuous_fst)).prodMk
      (hc.comp (continuous_const.prodMk continuous_snd))⟩
include hWd in
lemma contractedMatching_diag (τ s : Interval) : contractedMatching W τ (s,s)=1 := hWd _

def contractedSurgery (τ : Interval) : unitary (Square p q p q) :=
  surgeryUnitary (contractedMatching W τ) a b ha0 ha1 hb0 hb1
    (contractedMatching_diag W hWd τ _) (contractedMatching_diag W hWd τ _)

lemma contractedSurgery_continuous : Continuous (contractedSurgery a b ha0 ha1 hb0 hb1 W hWd) := by
  apply squareUnitary_continuous
  change Continuous (fun z : Interval×(Interval×Interval) =>
    surgery (pFlow (I := Fin p) (J := Fin q)) (qFlow (I := Fin p) (J := Fin q))
      (rightUnitary (W (contractInterval z.1 z.2.1,contractInterval z.1 leftEndpoint)))
      (rightUnitary (W (contractInterval z.1 z.2.1,contractInterval z.1 rightEndpoint)))
      (rightUnitary (W (contractInterval z.1 z.2.1,contractInterval z.1 z.2.2)))
      (a z.2.1) (b z.2.1) (a z.2.2) (b z.2.2))
  have hp := pFlow_continuous (I := Fin p) (J := Fin q)
  have hq := qFlow_continuous (I := Fin p) (J := Fin q)
  have hv := rightUnitary_continuous (p := p) (q := q)
  have hc := contractInterval_continuous
  apply surgery_continuous
  · exact hp
  · exact hq
  · apply hv.comp; apply W.continuous.comp
    exact (hc.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
      (hc.comp (continuous_fst.prodMk continuous_const))
  · apply hv.comp; apply W.continuous.comp
    exact (hc.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
      (hc.comp (continuous_fst.prodMk continuous_const))
  · apply hv.comp; apply W.continuous.comp
    exact (hc.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
      (hc.comp (continuous_fst.prodMk continuous_snd.snd))
  · exact a.continuous.comp continuous_snd.fst
  · exact b.continuous.comp continuous_snd.fst
  · exact a.continuous.comp continuous_snd.snd
  · exact b.continuous.comp continuous_snd.snd

lemma contractedSurgery_zero : contractedSurgery a b ha0 ha1 hb0 hb1 W hWd leftEndpoint=
    surgeryUnitary (ContinuousMap.const _ (1 : unitary (TensorMat p q))) a b ha0 ha1 hb0 hb1 rfl rfl := by
  have he : contractedMatching W leftEndpoint=ContinuousMap.const _ 1 := by
    apply ContinuousMap.ext
    rintro ⟨s,t⟩
    change W (contractInterval leftEndpoint s,contractInterval leftEndpoint t)=1
    simp only [contractInterval_zero,hWd]
  simp only [contractedSurgery,he]
lemma contractedSurgery_one : contractedSurgery a b ha0 ha1 hb0 hb1 W hWd rightEndpoint=
    surgeryUnitary W a b ha0 ha1 hb0 hb1 (hWd _) (hWd _) := by
  have he : contractedMatching W rightEndpoint=W := by
    apply ContinuousMap.ext
    rintro ⟨s,t⟩
    change W (contractInterval rightEndpoint s,contractInterval rightEndpoint t)=W (s,t)
    simp only [contractInterval_one]
  simp only [contractedSurgery,he]

theorem surgeryUnitary_joined : Joined 1 (surgeryUnitary W a b ha0 ha1 hb0 hb1 (hWd _) (hWd _)) := by
  let γ : Path 1 (surgeryUnitary (ContinuousMap.const _ (1 : unitary (TensorMat p q))) a b ha0 ha1 hb0 hb1 rfl rfl) :=
    ⟨⟨residualUnitary a b ha0 hb1,residualUnitary_continuous a b ha0 hb1⟩,
      residualUnitary_zero a b ha0 hb1,residualUnitary_one a b ha0 ha1 hb0 hb1⟩
  let ζ : Path (surgeryUnitary (ContinuousMap.const _ (1 : unitary (TensorMat p q))) a b ha0 ha1 hb0 hb1 rfl rfl)
      (surgeryUnitary W a b ha0 ha1 hb0 hb1 (hWd _) (hWd _)) :=
    ⟨⟨contractedSurgery a b ha0 ha1 hb0 hb1 W hWd,
       contractedSurgery_continuous a b ha0 ha1 hb0 hb1 W hWd⟩,
      contractedSurgery_zero a b ha0 ha1 hb0 hb1 W hWd,
      contractedSurgery_one a b ha0 ha1 hb0 hb1 W hWd⟩
  exact ⟨γ.trans ζ⟩

end JiangSuConstruction

end

end OAI
