import Mathlib
import OAI.Algebra.FiniteTensor.TensorForms

namespace OAI

/-! Odd coordinate operators, tensor signs and naturality. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor
noncomputable section
open scoped TensorProduct
variable {K ι : Type*} [Field K] [Fintype ι] [LinearOrder ι]
variable {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

def oddCoordinate (g f : ∀ i, V i →ₗ[K] V i) (i j : ι) : V j →ₗ[K] V j :=
  if j < i then g j else if j=i then f j else LinearMap.id

def oddTensor (g f : ∀ i, V i →ₗ[K] V i) :
    (⨂[K] i, V i) →ₗ[K] (⨂[K] i, V i) :=
  ∑ i, PiTensorProduct.map (oddCoordinate g f i)

omit [Fintype ι] in
private theorem tprod_neg_at (x y : ∀ i, V i) (i : ι)
    (hi : x i = -y i) (h : ∀ j, j≠i → x j=y j) :
    PiTensorProduct.tprod K x = -PiTensorProduct.tprod K y := by
  have hx : x=Function.update y i (-y i) := by
    funext j
    by_cases hji : j=i
    · subst j; simpa using hi
    · simpa [hji] using h j hji
  rw [hx,(PiTensorProduct.tprod K).map_update_neg,Function.update_eq_self]

omit [Fintype ι] in
private theorem odd_term_lt (g f e : ∀ i, V i →ₗ[K] V i)
    (hfg : ∀ i v, f i (g i v) = -g i (f i v))
    (i j : ι) (hij : i < j) (v : ∀ i, V i) :
    PiTensorProduct.tprod K (fun k => oddCoordinate g f i k (oddCoordinate g e j k (v k))) =
      -PiTensorProduct.tprod K (fun k => oddCoordinate g e j k (oddCoordinate g f i k (v k))) := by
  apply tprod_neg_at _ _ i
  · simp [oddCoordinate,hij,hfg]
  · intro k hki
    by_cases hkj : k=j
    · subst k; simp [oddCoordinate,hij.not_gt,hki]
    · by_cases hkin : k < i
      · simp [oddCoordinate,hkin,hkin.trans hij]
      · by_cases hkjn : k < j
        · simp [oddCoordinate,hkin,hkjn,hki]
        · simp [oddCoordinate,hkin,hkjn,hki,hkj]

 
omit [Fintype ι] in
theorem odd_term_anticommute (g f e : ∀ i, V i →ₗ[K] V i)
    (hfg : ∀ i v, f i (g i v) = -g i (f i v))
    (heg : ∀ i v, e i (g i v) = -g i (e i v))
    (hfe : ∀ i v, f i (e i v) = -e i (f i v))
    (i j : ι) :
    (PiTensorProduct.map (oddCoordinate g f i)).comp (PiTensorProduct.map (oddCoordinate g e j)) +
    (PiTensorProduct.map (oddCoordinate g e j)).comp (PiTensorProduct.map (oddCoordinate g f i))=0 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply,LinearMap.add_apply,
    LinearMap.comp_apply,PiTensorProduct.map_tprod,LinearMap.zero_apply]
  rcases lt_trichotomy i j with hij|rfl|hji
  · rw [odd_term_lt g f e hfg i j hij v,neg_add_cancel]
  · have h := tprod_neg_at (K := K)
      (fun k => oddCoordinate g f i k (oddCoordinate g e i k (v k)))
      (fun k => oddCoordinate g e i k (oddCoordinate g f i k (v k))) i
      (by simp [oddCoordinate,hfe]) (by
        intro k hki
        by_cases hlt : k < i <;> simp [oddCoordinate,hki,hlt])
    rw [h,neg_add_cancel]
  · rw [odd_term_lt g e f heg j i hji v,add_neg_cancel]

 
theorem oddTensor_anticommute (g f e : ∀ i, V i →ₗ[K] V i)
    (hfg : ∀ i v, f i (g i v) = -g i (f i v))
    (heg : ∀ i v, e i (g i v) = -g i (e i v))
    (hfe : ∀ i v, f i (e i v) = -e i (f i v)) (v : ⨂[K] i, V i) :
    oddTensor g f (oddTensor g e v) + oddTensor g e (oddTensor g f v)=0 := by
  simp only [oddTensor,LinearMap.sum_apply,map_sum]
  rw [Finset.sum_comm,← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  exact LinearMap.congr_fun (odd_term_anticommute g f e hfg heg hfe i j) v

variable {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

 
theorem tensorMap_oddTensor_zero (g f : ∀ i, V i →ₗ[K] V i)
    (q : ∀ i, V i →ₗ[K] W i) (hq : ∀ i v, q i (f i v)=0) :
    (PiTensorProduct.map q).comp (oddTensor g f)=0 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,
    oddTensor,LinearMap.sum_apply,map_sum,PiTensorProduct.map_tprod,LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply (PiTensorProduct.tprod K).map_coord_zero i
  simp [oddCoordinate,hq]

 
theorem oddTensor_tensorMap_zero (g f : ∀ i, V i →ₗ[K] V i)
    (a : ∀ i, W i →ₗ[K] V i) (ha : ∀ i v, f i (a i v)=0) :
    (oddTensor g f).comp (PiTensorProduct.map a)=0 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,
    oddTensor,LinearMap.sum_apply,PiTensorProduct.map_tprod,LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply (PiTensorProduct.tprod K).map_coord_zero i
  simp [oddCoordinate,ha]

 
theorem oddTensor_sandwich (g f : ∀ i, V i →ₗ[K] V i)
    (q : ∀ i, V i →ₗ[K] W i) (a : ∀ i, W i →ₗ[K] V i)
    (hqa : ∀ i v, q i (a i v)=v) :
    (PiTensorProduct.map q).comp ((oddTensor g f).comp (PiTensorProduct.map a)) =
    oddTensor (fun i => (q i).comp ((g i).comp (a i)))
      (fun i => (q i).comp ((f i).comp (a i))) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,
    oddTensor,LinearMap.sum_apply,map_sum,PiTensorProduct.map_tprod]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  by_cases hji : j < i
  · simp [oddCoordinate,hji]
  · by_cases heq : j=i <;> simp [oddCoordinate,hji,heq,hqa]

 
theorem oddTensor_naturality (g f : ∀ i, V i →ₗ[K] V i)
    (g' f' : ∀ i, W i →ₗ[K] W i) (q : ∀ i, V i →ₗ[K] W i)
    (hqg : ∀ i v, q i (g i v)=g' i (q i v))
    (hqf : ∀ i v, q i (f i v)=f' i (q i v)) :
    (PiTensorProduct.map q).comp (oddTensor g f) =
      (oddTensor g' f').comp (PiTensorProduct.map q) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,
    oddTensor,LinearMap.sum_apply,map_sum,PiTensorProduct.map_tprod]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  by_cases hji : j < i
  · simp [oddCoordinate,hji,hqg]
  · by_cases heq : j=i <;> simp [oddCoordinate,hji,heq,hqf]

end
end PD4Tensor

namespace PD4Tensor
noncomputable section
open scoped TensorProduct BigOperators
variable {K : Type*} [Field K] {n : ℕ} {V : Fin (n+1) → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

theorem headTail_map (f : ∀ i, V i →ₗ[K] V i) :
    (headTailEquiv K V).toLinearMap.comp (PiTensorProduct.map f) =
      (TensorProduct.map (f 0) (PiTensorProduct.map (fun i : Fin n => f i.succ))).comp
        (headTailEquiv K V).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,
    PiTensorProduct.map_tprod,LinearEquiv.coe_coe,headTailEquiv_tprod,TensorProduct.map_tmul]

theorem headTail_oddTensor (g f : ∀ i, V i →ₗ[K] V i) :
    (headTailEquiv K V).toLinearMap.comp (oddTensor g f) =
      (TensorProduct.map (f 0) LinearMap.id +
        TensorProduct.map (g 0) (oddTensor (fun i : Fin n => g i.succ)
          (fun i : Fin n => f i.succ))).comp (headTailEquiv K V).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,
    oddTensor,LinearMap.sum_apply,map_sum,PiTensorProduct.map_tprod,
    LinearEquiv.coe_coe,headTailEquiv_tprod,LinearMap.add_apply,
    TensorProduct.map_tmul,LinearMap.id_apply,TensorProduct.tmul_sum]
  rw [Fin.sum_univ_succ]
  congr 1
  · simp [oddCoordinate]

end
end PD4Tensor
end

end OAI
