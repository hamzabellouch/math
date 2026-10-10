import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalEstimate

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateSupportRemoval
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullProductMean (S : ι → Finset ℤ) (μ : ι → ℤ → ℝ) (f : (ι → ℤ) → ℂ) : ℂ :=
  ∑ a ∈ Fintype.piFinset S, ((∏ i, μ i (a i) : ℝ) : ℂ)*f a

private theorem insert_prior_product (i : ι) (μ : ι → ℤ → ℝ) (x : Other i → ℤ) (b : ℤ) :
    (∏ j, μ j (insertCoordinate i x b j)) = (∏ j : Other i, μ j.val (x j))*μ i b := by
  have hrest : (∏ j ∈ (Finset.univ : Finset ι).erase i, μ j (insertCoordinate i x b j)) =
      ∏ j : Other i, μ j.val (x j) := by
    rw [Finset.prod_subtype (p := fun j => j ≠ i) (F := inferInstance) _ (fun j => by simp)]
    simp only [insertCoordinate_other]
  have h := Finset.prod_erase_mul (Finset.univ : Finset ι)
    (fun j => μ j (insertCoordinate i x b j)) (Finset.mem_univ i)
  rw [hrest,insertCoordinate_self] at h
  exact h.symm

theorem fullProductMean_eq_independentPrimeMean (i : ι)
    (S : ι → Finset ℤ) (μ : ι → ℤ → ℝ) (B : Finset ℕ)
    (hS : S i=B.image (fun p : ℕ => (p:ℤ))) (f : (ι → ℤ) → ℂ) :
    fullProductMean S μ f = independentPrimeMean (fun j : Other i => S j.val)
      (fun j => μ j.val) B (fun p => μ i (p:ℤ))
      (fun x p => f (insertCoordinate i x (p:ℤ))) := by
  classical
  symm
  unfold independentPrimeMean fullProductMean
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun xp _ => insertCoordinate i xp.1 (xp.2:ℤ))
  · intro xp hxp
    obtain ⟨hx,hp⟩ := Finset.mem_product.mp hxp
    apply Fintype.mem_piFinset.mpr
    intro j
    by_cases hj : j=i
    · subst j
      rw [insertCoordinate_self,hS]
      exact Finset.mem_image.mpr ⟨xp.2,hp,rfl⟩
    · simpa only [insertCoordinate,dite_eq_right hj] using Fintype.mem_piFinset.mp hx ⟨j,hj⟩
  · intro xp hxp yp hyp hxy
    apply Prod.ext
    · funext j
      have h := congrFun hxy j.val
      simpa only [insertCoordinate_other] using h
    · have h := congrFun hxy i
      simpa only [insertCoordinate_self,Int.natCast_inj] using h
  · intro a ha
    have hai : a i ∈ B.image (fun p : ℕ => (p:ℤ)) := hS ▸ Fintype.mem_piFinset.mp ha i
    obtain ⟨p,hp,hpa⟩ := Finset.mem_image.mp hai
    refine ⟨((fun j : Other i => a j.val),p),?_,?_⟩
    · exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr
        (fun j => Fintype.mem_piFinset.mp ha j.val),hp⟩
    · funext j
      by_cases hj : j=i
      · subst j
        simpa only [insertCoordinate_self] using hpa
      · simp only [insertCoordinate,dite_eq_right hj]
  · intro xp hxp
    rw [insert_prior_product]
    push_cast
    ring

end Ostmann.Characters.TemplateSupportRemoval

end

end OAI
