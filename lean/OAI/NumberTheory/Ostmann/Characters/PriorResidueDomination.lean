import OAI.NumberTheory.Ostmann.Characters.BinaryExposure
import OAI.NumberTheory.Ostmann.Characters.WordSelection

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
open Construction
attribute [local instance] Classical.propDecidable

def pushForwardPrior {α β:Type*} [Fintype α] [Fintype β]
    (μ:FinitePrior α) (f:α→β) : FinitePrior β where
  mass b := ∑a:α with f a=b,μ.mass a
  mass_nonneg b := Finset.sum_nonneg (fun a _=>μ.mass_nonneg a)
  mass_total := by
    exact (Finset.sum_fiberwise (Finset.univ:Finset α) f μ.mass).trans μ.mass_total

theorem pushForwardPrior_mean {α β:Type*} [Fintype α] [Fintype β]
    (μ:FinitePrior α) (f:α→β) (F:β→ℝ) :
    (pushForwardPrior μ f).mean F=μ.mean (fun a=>F (f a)) := by
  unfold FinitePrior.mean pushForwardPrior
  simp only [Finset.sum_mul]
  calc
    _ = ∑b:β,∑a:α with f a=b,μ.mass a*F (f a) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ := Finset.sum_fiberwise (Finset.univ:Finset α) f (fun a=>μ.mass a*F (f a))

theorem pushForwardPrior_product_mass {ι α β:Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]
    (μ:ι→FinitePrior α) (f:ι→α→β) (y:ι→β) :
    (pushForwardPrior (productPrior μ) (fun x i=>f i (x i))).mass y =
      ∏i,(pushForwardPrior (μ i) (f i)).mass (y i) := by
  classical
  have he (x:ι→α) :
      (∏i,if f i (x i)=y i then (μ i).mass (x i) else 0)=
        if (fun i=>f i (x i))=y then ∏i,(μ i).mass (x i) else 0 := by
    by_cases h:(fun i=>f i (x i))=y
    · have hi i : f i (x i)=y i := congrFun h i
      simp only [hi,ite_true]
    · rw [ite_eq_right h]
      have hn : ∃i,f i (x i)≠y i := by
        by_contra hnot
        apply h
        funext i
        exact not_not.mp (not_exists.mp hnot i)
      obtain ⟨i,hi⟩ := hn
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  simp only [pushForwardPrior,productPrior,Finset.sum_filter]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl (fun x _=>(he x).symm)

theorem mean_le_uniform_of_fiber_mass {α β:Type*} [Fintype α] [Fintype β]
    (μ:FinitePrior α) (f:α→β) (D:ℝ)
    (hf:∀b,(pushForwardPrior μ f).mass b≤D/(Fintype.card β:ℝ))
    (F:β→ℝ) (hF:∀b,0≤F b) :
    μ.mean (fun a=>F (f a))≤D*BinaryExposure.avg F := by
  rw [← pushForwardPrior_mean]
  calc
    _ ≤ ∑b:β,(D/(Fintype.card β:ℝ))*F b :=
      Finset.sum_le_sum (fun b _=>mul_le_mul_of_nonneg_right (hf b) (hF b))
    _ = _ := by rw [← Finset.mul_sum]; unfold BinaryExposure.avg; ring

theorem productPrior_mean_le_uniform {ι α β:Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]
    (μ:ι→FinitePrior α) (f:ι→α→β) (D:ι→ℝ)
    (hf:∀i b,(pushForwardPrior (μ i) (f i)).mass b≤D i/(Fintype.card β:ℝ))
    (F:(ι→β)→ℝ) (hF:∀y,0≤F y) :
    (productPrior μ).mean (fun x=>F (fun i=>f i (x i)))≤
      (∏i,D i)*BinaryExposure.avg F := by
  apply mean_le_uniform_of_fiber_mass
  · intro y
    rw [pushForwardPrior_product_mass]
    calc
      _ ≤ ∏i,D i/(Fintype.card β:ℝ) :=
        Finset.prod_le_prod₀ (fun i _=>(pushForwardPrior (μ i) (f i)).mass_nonneg _)
          (fun i _=>hf i (y i))
      _ = _ := by
        rw [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fun]
        norm_cast
  · exact hF

end Ostmann.Characters

end

end OAI
