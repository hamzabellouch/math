import Mathlib
import OAI.Probability.SKRatio.Calculus.PairUpdate

namespace OAI

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SKRatio.Fields
open Real Matrix TwoSpin
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma heatBathLinear_kernel (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    heatBathLinear g h f=0 ↔ ∀ x y,f x=f y := by
  constructor
  · intro hf
    apply (dirichlet_eq_zero_iff g h f).mp
    rw [← heatBathGenerator_form]
    change expectation g h (fun x=>f x*(heatBathLinear g h f) x)=0
    rw [hf]
    simp only [Pi.zero_apply,mul_zero,expectation_const]
  · intro hf
    have he : f=(fun _=>f (fun _=>false)) := funext (fun x=>hf x (fun _=>false))
    rw [he,heatBathLinear_const]

lemma heatBath_curvature_poincare (g : Disorder n) (h : Fin n→ℝ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ∀ f : Spin n→ℝ,ρ*dirichlet g h f ≤
      expectation g h (fun x=>heatBathGenerator g h f x^2)) (f : Spin n→ℝ) :
    ρ*variance g h f ≤ dirichlet g h f := by
  let S := gibbsScale g h
  let H : EuclideanSpace ℝ (Spin n) →ₗ[ℝ] EuclideanSpace ℝ (Spin n) :=
    S.toLinearMap ∘ₗ heatBathLinear g h ∘ₗ S.symm.toLinearMap
  have hHS (k : Spin n→ℝ) : H (S k)=S (heatBathLinear g h k) := by simp [H]
  have hH : H.IsSymmetric := by
    intro u v
    obtain ⟨u,rfl⟩ := S.surjective u
    obtain ⟨v,rfl⟩ := S.surjective v
    rw [hHS,hHS]
    exact (gibbsScale_inner g h _ _).trans ((heatBathGenerator_adjoint g h u v).trans
      (gibbsScale_inner g h _ _).symm)
  have hform (k : Spin n→ℝ) : ⟪S k,H (S k)⟫=dirichlet g h k := by
    rw [hHS,gibbsScale_inner]
    exact heatBathGenerator_form g h k
  have hpos : ∀ v,0 ≤ ⟪v,H v⟫ := by
    intro v
    obtain ⟨k,rfl⟩ := S.surjective v
    rw [hform]
    exact dirichlet_nonneg g h k
  have hcurv : ∀ v,ρ*⟪v,H v⟫ ≤ ⟪H v,H v⟫ := by
    intro v
    obtain ⟨k,rfl⟩ := S.surjective v
    rw [hform,hHS,gibbsScale_inner]
    simpa only [sq,heatBathLinear,LinearMap.coe_mk,AddHom.coe_mk] using hc k
  let f₀ := f-(fun _=>expectation g h f)
  have hm : expectation g h f₀=0 := by
    change expectation g h (fun x=>f x-expectation g h f)=0
    rw [expectation_sub,expectation_const,sub_self]
  have hker : S f₀ ∈ (LinearMap.ker H)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    obtain ⟨k,rfl⟩ := S.surjective v
    have hk : heatBathLinear g h k=0 := by
      have hh := LinearMap.mem_ker.mp hv
      rw [hHS] at hh
      exact S.injective (by simpa using hh)
    have hk' := (heatBathLinear_kernel g h k).mp hk
    have he : k=(fun _=>k (fun _=>false)) := funext (fun x=>hk' x (fun _=>false))
    rw [gibbsScale_inner,he,expectation_const_mul,hm,mul_zero]
  have hh := curvature_poincare_on_kernel_orthogonal H hH hpos hρ hcurv (S f₀) hker
  rw [gibbsScale_inner,hform] at hh
  have hd : dirichlet g h f₀=dirichlet g h f := by
    rw [← heatBathGenerator_form,← heatBathGenerator_form]
    have he : heatBathLinear g h f₀=heatBathLinear g h f := by
      simp only [f₀,map_sub,heatBathLinear_const,sub_zero]
    change expectation g h (fun x=>f₀ x*(heatBathLinear g h f₀) x)=_
    rw [he]
    have hz : expectation g h (heatBathLinear g h f)=0 := by
      change expectation g h (fun x=>∑ i,(f x-conditionalExpectation g h i f x))=0
      rw [expectation_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [expectation_sub,expectation_conditionalExpectation,sub_self]
    simp only [f₀,Pi.sub_apply,sub_mul]
    rw [expectation_sub,expectation_const_mul,hz,mul_zero,sub_zero]
    rfl
  rw [hd] at hh
  simpa only [variance,f₀,Pi.sub_apply,sq] using hh

end SKRatio.Fields

end
end

end OAI
