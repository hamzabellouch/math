import Mathlib
import OAI.Algebra.FiniteTensor.FiniteObstruction

namespace OAI

/-! Complementary graph matrices and tangent invertibility. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (R υ σ τ : Type*) [CommRing R] (p : ℕ) (e : υ ≃ σ ⊕ τ)

 
def planeRestriction (hp : 0<p) :
    Ring R υ (fun _ => p) →ₐ[R] Ring R σ (fun _ => p) :=
  (uniformLeft R σ τ p hp).comp (reindexEquiv R υ (σ ⊕ τ) p e).toAlgHom

@[simp] theorem planeRestriction_coord (hp : 0<p) (i : υ) :
    planeRestriction R υ σ τ p e hp (coord R υ (fun _ => p) i)=
      Sum.elim (coord R σ (fun _ => p)) (fun _ => 0) (e i) := by
  simp only [planeRestriction,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,
    reindexEquiv_coord,uniformLeft_coord]

 
variable [Fintype σ] [Fintype τ]

def combinedGraph (H : υ → MvPowerSeries σ R) (G : υ → MvPowerSeries τ R) :
    υ → MvPowerSeries υ R :=
  fun i => MvPowerSeries.rename (fun j => e.symm (Sum.inl j)) (H i) +
    MvPowerSeries.rename (fun j => e.symm (Sum.inr j)) (G i)

 

theorem combinedGraph_eval_left [Fintype υ] (hp : 0<p)
    (H : υ → MvPowerSeries σ R) (G : υ → MvPowerSeries τ R)
    (hG : ∀ i, MvPowerSeries.constantCoeff (G i)=0) (i : υ) :
    planeRestriction R υ σ τ p e hp
      (nilEval R (coord R υ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩)
        (combinedGraph R υ σ τ e H G i)) =
      nilEval R (coord R σ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩) (H i) := by
  have hh := nilEval_map (planeRestriction R υ σ τ p e hp)
    (coord R υ (fun _ => p)) (fun j => (show IsNilpotent (coord R υ (fun _ => p) j) from
      ⟨p,coord_pow _ _ _ j⟩)) (combinedGraph R υ σ τ e H G i)
  rw [hh]
  simp only [combinedGraph,map_add,nilEval_rename,Function.comp_def,
    planeRestriction_coord,Equiv.apply_symm_apply,Sum.elim_inl,Sum.elim_inr]
  rw [nilEval_zero,hG,map_zero,add_zero]

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor
noncomputable section
open scoped BigOperators
variable {K υ σ τ : Type*} [Field K] [Fintype υ]
  [Fintype σ] [Fintype τ]

def joinedMatrix (e : υ ≃ σ ⊕ τ) (L : Matrix υ σ K) (R : Matrix υ τ K) : Matrix υ υ K :=
  fun i j => Sum.elim (L i) (R i) (e j)

theorem joinedMatrix_mulVec (e : υ ≃ σ ⊕ τ) (L : Matrix υ σ K) (R : Matrix υ τ K)
    (v : υ → K) :
    (joinedMatrix e L R).mulVec v=
      L.mulVec (fun j => v (e.symm (Sum.inl j))) + R.mulVec (fun j => v (e.symm (Sum.inr j))) := by
  ext i
  simp only [Matrix.mulVec,dotProduct,joinedMatrix,Pi.add_apply]
  rw [←e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]

 

theorem joinedMatrix_det_ne_zero [DecidableEq υ]
    (e : υ ≃ σ ⊕ τ) (L : Matrix υ σ K) (R : Matrix υ τ K)
    (hL : Function.Injective L.mulVec) (hR : Function.Injective R.mulVec)
    (hcomp : IsCompl (Matrix.mulVecLin L).range (Matrix.mulVecLin R).range) :
    (joinedMatrix e L R).det≠0 := by
  suffices hi : Function.Injective (joinedMatrix e L R).mulVec by
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero
  change Function.Injective (Matrix.mulVecLin (joinedMatrix e L R))
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change (joinedMatrix e L R).mulVec v=0 at hv
  rw [joinedMatrix_mulVec] at hv
  have hzero : L.mulVec (fun j => v (e.symm (Sum.inl j)))=0 := by
    apply (Submodule.disjoint_def.mp hcomp.disjoint)
    · exact ⟨fun j => v (e.symm (Sum.inl j)),rfl⟩
    · refine ⟨-(fun j => v (e.symm (Sum.inr j))),?_⟩
      rw [map_neg]
      exact (eq_neg_of_add_eq_zero_left hv).symm
  have hzL : (fun j => v (e.symm (Sum.inl j)))=0 :=
    hL (by simpa using hzero)
  have hzR : (fun j => v (e.symm (Sum.inr j)))=0 := hR (by simpa [hzero] using hv)
  ext i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j with
  | inl j => exact congr_fun hzL j
  | inr j => exact congr_fun hzR j

end
end PD4Tensor

namespace PD4Tensor
noncomputable section
variable {R σ τ : Type*} [CommRing R]

@[simp] theorem coeff_single_rename_embedding (e : σ ↪ τ) (f : MvPowerSeries σ R) (i : σ) :
    MvPowerSeries.coeff (Finsupp.single (e i) 1) (MvPowerSeries.rename e f)=
      MvPowerSeries.coeff (Finsupp.single i 1) f := by
  simpa only [Finsupp.embDomain_single] using
    (MvPowerSeries.coeff_embDomain_rename e f (Finsupp.single i 1))

theorem coeff_single_rename_outside [Fintype σ] (e : σ → τ) (f : MvPowerSeries σ R)
    (i : τ) (hi : i∉Set.range e) :
    MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.rename e f)=0 := by
  classical
  apply MvPowerSeries.coeff_rename_eq_zero
  rintro ⟨a,ha⟩
  apply hi
  apply Finsupp.mem_range_of_mapDomain_ne_zero (x:=a)
  rw [ha,Finsupp.single_eq_same]
  exact one_ne_zero

end
end PD4Tensor

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (R υ σ τ : Type*) [CommRing R]
  [Fintype σ] [Fintype τ]
  (e : υ ≃ σ ⊕ τ)

@[simp] theorem combinedGraph_constantCoeff
    (H : υ → MvPowerSeries σ R) (G : υ → MvPowerSeries τ R) (i : υ) :
    MvPowerSeries.constantCoeff (combinedGraph R υ σ τ e H G i)=
      MvPowerSeries.constantCoeff (H i)+MvPowerSeries.constantCoeff (G i) := by
  simp [combinedGraph]

theorem combinedGraph_coeff (H : υ → MvPowerSeries σ R) (G : υ → MvPowerSeries τ R)
    (i j : υ) :
    MvPowerSeries.coeff (Finsupp.single j 1) (combinedGraph R υ σ τ e H G i)=
      Sum.elim (fun k => MvPowerSeries.coeff (Finsupp.single k 1) (H i))
        (fun k => MvPowerSeries.coeff (Finsupp.single k 1) (G i)) (e j) := by
  let el : σ ↪ υ := ⟨fun j => e.symm (Sum.inl j),e.symm.injective.comp Sum.inl_injective⟩
  let er : τ ↪ υ := ⟨fun j => e.symm (Sum.inr j),e.symm.injective.comp Sum.inr_injective⟩
  obtain ⟨j,rfl⟩ := e.symm.surjective j
  cases j with
  | inl j =>
    change MvPowerSeries.coeff (Finsupp.single (el j) 1)
      (MvPowerSeries.rename el (H i)+MvPowerSeries.rename er (G i))=_
    rw [map_add,coeff_single_rename_embedding]
    rw [coeff_single_rename_outside er _ (el j) (by
      rintro ⟨k,hk⟩
      have hh := e.symm.injective hk
      cases hh)]
    simp
  | inr j =>
    change MvPowerSeries.coeff (Finsupp.single (er j) 1)
      (MvPowerSeries.rename el (H i)+MvPowerSeries.rename er (G i))=_
    rw [map_add,coeff_single_rename_embedding]
    rw [coeff_single_rename_outside el _ (er j) (by
      rintro ⟨k,hk⟩
      have hh := e.symm.injective hk
      cases hh)]
    simp

variable {K : Type*} [Field K] [Fintype υ] [DecidableEq υ]

theorem combinedGraph_central_tangent
    (a : R →+* K) (H : υ → MvPowerSeries σ R) (G : υ → MvPowerSeries τ R)
    (hH : Function.Injective (Matrix.mulVecLin
      (fun i j => a (MvPowerSeries.coeff (Finsupp.single j 1) (H i)))))
    (hG : Function.Injective (Matrix.mulVecLin
      (fun i j => a (MvPowerSeries.coeff (Finsupp.single j 1) (G i)))))
    (hcomp : IsCompl (Matrix.mulVecLin
      (fun i j => a (MvPowerSeries.coeff (Finsupp.single j 1) (H i)))).range
      (Matrix.mulVecLin (fun i j => a (MvPowerSeries.coeff (Finsupp.single j 1) (G i)))).range) :
    Matrix.det (fun i j => a (MvPowerSeries.coeff (Finsupp.single j 1)
      (combinedGraph R υ σ τ e H G i)))≠0 := by
  have heq : (fun i j => a (MvPowerSeries.coeff (Finsupp.single j 1)
      (combinedGraph R υ σ τ e H G i)))=
      joinedMatrix e (fun i j => a (MvPowerSeries.coeff (Finsupp.single j 1) (H i)))
        (fun i j => a (MvPowerSeries.coeff (Finsupp.single j 1) (G i))) := by
    funext i j
    rw [combinedGraph_coeff]
    unfold joinedMatrix
    cases e j <;> rfl
  rw [heq]
  exact joinedMatrix_det_ne_zero e _ _ hH hG hcomp

end
end PD4Tensor.FiniteCoordinates
end

end OAI
