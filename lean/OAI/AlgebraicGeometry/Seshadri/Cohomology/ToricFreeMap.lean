import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.LaurentSupport

namespace OAI


                                      
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

lemma smul_supported_mem (V : Submodule K M) (S : Set (ℤ × ℤ)) (e : M)
    (h : ∀ z ∈ S, T (K := K) z • e ∈ V)
    (r : LaurentPlane.Ring K) (hr : r ∈ laurentSupported S) : r • e ∈ V := by
  rw [laurentSupported_eq_span] at hr
  induction hr using Submodule.span_induction with
  | mem r hr => obtain ⟨z,hz,rfl⟩ := hr; exact h z hz
  | zero => simp
  | add r s hr hs ih ih' => simpa only [add_smul] using V.add_mem ih ih'
  | smul a r hr ih => simpa only [smul_assoc] using V.smul_mem a ih

def freeMap {ι : Type*} [Fintype ι] (e : ι → M) :
    (ι → LaurentPlane.Ring K) →ₗ[LaurentPlane.Ring K] M where
  toFun m := ∑ i, m i • e i
  map_add' := by intros; simp [add_smul,Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.smul_sum,smul_smul]

lemma freeMap_supported {ι : Type*} [Fintype ι] (e : ι → M) (S : Set (ℤ × ℤ))
    (V : Submodule K M) (he : ∀ i z, z ∈ S → T (K := K) z • e i ∈ V)
    (m : ι → LaurentPlane.Ring K)
    (hm : ∀ i, m i ∈ laurentSupported S) : freeMap e m ∈ V := by
  apply Submodule.sum_mem
  intro i hi
  exact smul_supported_mem V S (e i) (he i) (m i) (hm i)

omit [Module K M] [IsScalarTower K (LaurentPlane.Ring K) M] in
lemma freeMap_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → M) (i : ι) (r : LaurentPlane.Ring K) :
    freeMap e (Pi.single i r) = r • e i := by
  simp [freeMap,Pi.single_apply]

lemma single_monomial_mem {ι : Type*} [DecidableEq ι] (S : Set (ℤ × ℤ))
    (i : ι) (z : ℤ × ℤ) (hz : z ∈ S) :
    Pi.single i (T (K := K) z) ∈ Submodule.pi Set.univ (fun _ => laurentSupported S) := by
  intro j hj
  by_cases h : j=i
  · subst j
    simp only [Pi.single_eq_same]
    rw [laurentSupported_eq_span]
    exact Submodule.subset_span ⟨z,hz,rfl⟩
  · simp [Pi.single_eq_of_ne h]

theorem freeMap_supported_range {ι : Type*} [Fintype ι] (e : ι → M)
    (S : Set (ℤ × ℤ)) :
    (Submodule.pi Set.univ (fun _ : ι => laurentSupported (K := K) S)).map
      ((freeMap e).restrictScalars K) =
    Submodule.span K {v | ∃ i z, z ∈ S ∧ v = T (K := K) z • e i} := by
  classical
  apply le_antisymm
  · rintro _ ⟨m,hm,rfl⟩
    apply freeMap_supported e S
    · intro i z hz
      exact Submodule.subset_span ⟨i,z,hz,rfl⟩
    · exact fun i => hm i (Set.mem_univ i)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,z,hz,rfl⟩
    exact Submodule.mem_map.mpr ⟨Pi.single i (T (K := K) z),single_monomial_mem S i z hz,
      freeMap_single e i (T z)⟩

end
end MaximalSeshadri.PlaneCech

end


end OAI
