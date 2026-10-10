import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutationCoordinates

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)

lemma coefficient_simple_expansion (a:I → ℤ) : C a=∑i,a i • simpleRoot C i := by
  have ha : a=∑i,a i • (Pi.single i 1:I → ℤ):=by
    ext j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij; simp [Ne.symm hij]
    · simp
  conv_lhs=>rw [ha,map_sum]
  simp only [map_zsmul,simpleRoot]

lemma realRootCoordinates_exists (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) :
    ∃D:E →ₗ[ℝ] (I → ℝ),∀a,D (e (C a))=fun i=>(a i:ℝ) := by
  let f:=Finsupp.linearCombination ℝ (fun i=>e (simpleRoot C i))
  obtain ⟨g,hg⟩:=f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hC)
  let D:E →ₗ[ℝ] (I → ℝ):=LinearMap.pi (fun i=>(Finsupp.lapply i).comp g)
  have hd (i:I) : D (e (simpleRoot C i))=Pi.single i 1:=by
    have H:=LinearMap.congr_fun hg (Finsupp.single i 1)
    simp only [LinearMap.comp_apply,LinearMap.id_apply,f,Finsupp.linearCombination_single,one_smul] at H
    funext j
    change g (e (simpleRoot C i)) j=(Pi.single i 1:I → ℝ) j
    rw [H]
    simp [Finsupp.single_apply,Pi.single_apply,eq_comm]
  refine ⟨D,fun a=>?_⟩
  rw [coefficient_simple_expansion C,map_sum,map_sum]
  simp only [map_zsmul,hd]
  ext j
  simp only [Finset.sum_apply,zsmul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij; simp [Ne.symm hij]
  · simp

lemma covector_root_eval (h:Module.Dual ℝ E) (hh:∀i,h (e (simpleRoot C i))=1)
    {n:ℕ} {m:M} (hm:HasRootDegree C n m) : h (e m)=(n:ℝ) := by
  obtain ⟨a,ha,rfl⟩:=hm
  rw [coefficient_simple_expansion C,map_sum,map_sum]
  simp only [map_zsmul,hh,zsmul_eq_mul,mul_one]
  exact_mod_cast ha

omit [Fintype I] in
lemma real_coordinate_simple (D:E →ₗ[ℝ] (I → ℝ))
    (hD:∀a,D (e (C a))=fun i=>(a i:ℝ)) (i:I) : D (e (simpleRoot C i))=Pi.single i 1 := by
  rw [simpleRoot,hD]
  ext j
  simp [Pi.single_apply]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
