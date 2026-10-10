import Mathlib
import OAI.Algebra.FrobeniusObstruction.SignedTensor
import OAI.Algebra.FrobeniusObstruction.BlockCohomology

namespace OAI

noncomputable section
open scoped BigOperators TensorProduct

namespace BoundaryOnly.FormalObstruction.SignedTensor
variable {k ι : Type*} [Field k] [Fintype ι] [LinearOrder ι]
variable {V W : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]

                                                                           
                     
omit [Fintype ι] in
theorem tensor_map_zero_at (f : ∀ i, V i →ₗ[k] W i) (i : ι) (hi : f i = 0) :
    PiTensorProduct.map f = 0 := by
  have hf : f = Function.update f i 0 := (Function.update_eq_self_iff.mpr hi.symm).symm
  rw [hf]
  exact (PiTensorProduct.mapMultilinear k V W).map_update_zero f i

                                                      
theorem representatives_cycles (P D : EndFamily (k := k) V)
    (j : ∀ i, W i →ₗ[k] V i) (hj : ∀ i, (D i).comp (j i) = 0) :
    (differential V P D).comp (PiTensorProduct.map j) = 0 := by
  change (∑ i, PiTensorProduct.map (dSlot V P D i)).comp (PiTensorProduct.map j) = 0
  rw [show (∑ i, PiTensorProduct.map (dSlot V P D i)).comp (PiTensorProduct.map j) =
    ∑ i, (PiTensorProduct.map (dSlot V P D i)).comp (PiTensorProduct.map j) from by
      ext x; simp]
  apply Finset.sum_eq_zero
  intro i _
  rw [← PiTensorProduct.map_comp]
  apply tensor_map_zero_at _ i
  simpa [dSlot] using hj i

                                                    
theorem projection_boundaries (P D : EndFamily (k := k) V)
    (p : ∀ i, V i →ₗ[k] W i) (hp : ∀ i, (p i).comp (D i) = 0) :
    (PiTensorProduct.map p).comp (differential V P D) = 0 := by
  change (PiTensorProduct.map p).comp (∑ i, PiTensorProduct.map (dSlot V P D i)) = 0
  rw [show (PiTensorProduct.map p).comp (∑ i, PiTensorProduct.map (dSlot V P D i)) =
    ∑ i, (PiTensorProduct.map p).comp (PiTensorProduct.map (dSlot V P D i)) from by
      ext x; simp]
  apply Finset.sum_eq_zero
  intro i _
  rw [← PiTensorProduct.map_comp]
  apply tensor_map_zero_at _ i
  simpa [dSlot] using hp i

                                                                              
                                                                                
                                                                                   
theorem tensor_cycle_decomposition (P D : EndFamily (k := k) V)
    (j : ∀ i, W i →ₗ[k] V i) (p : ∀ i, V i →ₗ[k] W i)
    (h : EndFamily (k := k) V)
    (hP2 : ∀ i, P i * P i = 1) (hDP : ∀ i, D i * P i = -(P i * D i))
    (hDj : ∀ i, (D i).comp (j i) = 0) (hpD : ∀ i, (p i).comp (D i) = 0)
    (hjP : ∀ i, P i * ((j i).comp (p i)) = ((j i).comp (p i)) * P i)
    (hPh : ∀ i, P i * h i = -(h i * P i))
    (hDh : ∀ i, D i * h i + h i * D i = 1 - ((j i).comp (p i)))
    (z : ⨂[k] i, V i) (hz : differential V P D z = 0) :
    ∃ y : ⨂[k] i, V i,
      z - PiTensorProduct.map j (PiTensorProduct.map p z) = differential V P D y := by
  let r : EndFamily (k := k) V := fun i => (j i).comp (p i)
  have hdr (i : ι) : D i * r i = r i * D i := by
    change (D i).comp ((j i).comp (p i)) = ((j i).comp (p i)).comp (D i)
    rw [← LinearMap.comp_assoc, hDj, LinearMap.zero_comp,
      LinearMap.comp_assoc, hpD, LinearMap.comp_zero]
  have H := tensor_homotopy P D r h hP2 hDP hdr hjP hPh hDh
  have He := LinearMap.congr_fun H z
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    Module.End.one_apply, hz, map_zero, add_zero] at He
  refine ⟨homotopy V P r h z, ?_⟩
  change z - ((PiTensorProduct.map j).comp (PiTensorProduct.map p)) z = _
  rw [← PiTensorProduct.map_comp]
  exact He.symm

                                                                            
                                                                             
theorem tensor_representatives_injective_mod_boundaries (P D : EndFamily (k := k) V)
    (j : ∀ i, W i →ₗ[k] V i) (p : ∀ i, V i →ₗ[k] W i)
    (hpj : ∀ i, (p i).comp (j i) = LinearMap.id)
    (hpD : ∀ i, (p i).comp (D i) = 0)
    (w : ⨂[k] i, W i) (z : ⨂[k] i, V i)
    (hwz : PiTensorProduct.map j w = differential V P D z) : w = 0 := by
  have h := congrArg (PiTensorProduct.map p) hwz
  have hpj' : (PiTensorProduct.map p).comp (PiTensorProduct.map j) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simpa only [hpj] using (PiTensorProduct.map_id (R := k) (s := W))
  change ((PiTensorProduct.map p).comp (PiTensorProduct.map j)) w =
    ((PiTensorProduct.map p).comp (differential V P D)) z at h
  rw [hpj', projection_boundaries P D p hpD] at h
  exact h

end BoundaryOnly.FormalObstruction.SignedTensor

namespace BoundaryOnly.FormalObstruction.SignedTensor
variable {k ι : Type*} [Field k] [Fintype ι] [LinearOrder ι]
variable {V W : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]

                                                                            
                                                               
theorem project_differential (P D : EndFamily (k := k) V)
    (Q E : EndFamily (k := k) W)
    (j : ∀ i, W i →ₗ[k] V i) (p : ∀ i, V i →ₗ[k] W i)
    (hpj : ∀ i, (p i).comp (j i) = LinearMap.id)
    (hP : ∀ i, (p i).comp ((P i).comp (j i)) = Q i)
    (hD : ∀ i, (p i).comp ((D i).comp (j i)) = E i) :
    (PiTensorProduct.map p).comp ((differential V P D).comp (PiTensorProduct.map j)) =
      differential W Q E := by
  apply PiTensorProduct.ext
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    differential, LinearMap.sum_apply, PiTensorProduct.map_tprod, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext a
  change p a (dSlot V P D i a (j a (v a))) = dSlot W Q E i a (v a)
  by_cases hlt : a < i
  · simp only [dSlot, ite_eq_left hlt]
    exact LinearMap.congr_fun (hP a) (v a)
  · by_cases heq : a = i
    · simp only [dSlot, ite_eq_right hlt, ite_eq_left heq]
      exact LinearMap.congr_fun (hD a) (v a)
    · simp only [dSlot, ite_eq_right hlt, ite_eq_right heq, Module.End.one_apply]
      exact LinearMap.congr_fun (hpj a) (v a)

                                                                       
                               
omit [Fintype ι] [LinearOrder ι] in
theorem project_tensor_map (S : EndFamily (k := k) V) (T : EndFamily (k := k) W)
    (j : ∀ i, W i →ₗ[k] V i) (p : ∀ i, V i →ₗ[k] W i)
    (hS : ∀ i, (p i).comp ((S i).comp (j i)) = T i) :
    (PiTensorProduct.map p).comp ((PiTensorProduct.map S).comp (PiTensorProduct.map j)) =
      PiTensorProduct.map T := by
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  congr 1
  funext i
  exact hS i

end BoundaryOnly.FormalObstruction.SignedTensor

end

end OAI
