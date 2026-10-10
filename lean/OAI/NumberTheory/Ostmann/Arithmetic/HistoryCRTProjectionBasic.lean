import OAI.NumberTheory.Ostmann.Arithmetic.ResidueHaar

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryCRTProjection
open scoped BigOperators
open ResidueHaar

noncomputable def sectionOfSurjective {G H : Type*} [Group G] [Group H]
    (f : G→*H) (hf : Function.Surjective f) (y : H) : G := Classical.choose (hf y)

@[simp] theorem sectionOfSurjective_spec {G H : Type*} [Group G] [Group H]
    (f : G→*H) (hf : Function.Surjective f) (y : H) : f (sectionOfSurjective f hf y)=y :=
  Classical.choose_spec (hf y)

noncomputable def kernelProductEquiv {G H : Type*} [Group G] [Group H]
    (f : G→*H) (hf : Function.Surjective f) : G≃H×f.ker where
  toFun x := (f x,⟨x*(sectionOfSurjective f hf (f x))⁻¹,by simp⟩)
  invFun z := z.2.val*sectionOfSurjective f hf z.1
  left_inv x := by simp
  right_inv z := by
    rcases z with ⟨y,k⟩
    have hk : f k.val=1 := k.property
    apply Prod.ext
    · simp [hk]
    · apply Subtype.ext
      simp [hk,mul_assoc]

noncomputable def fiberEquivKernel {G H : Type*} [Group G] [Group H]
    (f : G→*H) (hf : Function.Surjective f) (y : H) : {x:G // f x=y}≃f.ker where
  toFun x := ⟨x.val*(sectionOfSurjective f hf y)⁻¹,by simp [x.property]⟩
  invFun z := ⟨z.val*sectionOfSurjective f hf y,by
    have hz : f z.val=1 := z.property
    simp [hz]⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp [mul_assoc]

theorem card_fiber_eq_kernel {G H : Type*} [Group G] [Group H] [Fintype G]
    (f : G→*H) (hf : Function.Surjective f) (y : H) :
    Nat.card {x:G // f x=y}=Nat.card f.ker := Nat.card_congr (fiberEquivKernel f hf y)

theorem average_surjective_hom {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (f : G→*H) (hf : Function.Surjective f) (F : H→ℂ) :
    average (fun x=>F (f x))=average F := by
  classical
  have he := average_equiv (kernelProductEquiv f hf) (fun z : H×f.ker=>F z.1)
  have hone : average (fun _ : f.ker=>(1:ℂ))=1 := by
    simp only [average,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  have hp : average (fun z : H×f.ker=>F z.1)=average F := by
    simpa only [mul_one,hone] using average_product F (fun _ : f.ker=>(1:ℂ))
  exact he.trans hp

end Ostmann.Arithmetic.HistoryCRTProjection

end

end OAI
