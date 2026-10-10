import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPrimaryCompletion

namespace OAI

/-! Finite collection of actual primary cube fibers. Compact norm
weights remove the output cutoff without adding any support assumption
on the arithmetic coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma sum_primary_fin_two (S : Finset Eisenstein) (f : Eisenstein → Eisenstein → ℂ) :
    (∑ n ∈ Fintype.piFinset (fun _ : Fin 2 => S), f (n 0) (n 1)) =
      ∑ c ∈ S, ∑ u ∈ S, f c u := by
  rw [←Finset.sum_product' S S f]
  apply Finset.sum_bij (fun n _ => (n 0,n 1))
  · intro n hn
    exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mp hn 0,Fintype.mem_piFinset.mp hn 1⟩
  · intro n _ m _ he
    funext i
    fin_cases i
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  · intro cu hcu
    refine ⟨![cu.1,cu.2],Fintype.mem_piFinset.mpr ?_,?_⟩
    · intro i
      fin_cases i
      · exact (Finset.mem_product.mp hcu).1
      · exact (Finset.mem_product.mp hcu).2
    · rfl
  · intro n _
    rfl

theorem primary_cube_fiber_weighted_sum (F : ℝ) (W : ℝ → ℂ)
    (hW : ∀ x : ℝ, F < x → W x = 0) (f : Eisenstein → Eisenstein → ℂ) :
    (∑ b ∈ primaryElementBall F, W (norm b)*
      ∑ n ∈ primaryCubeFiber F b, f (n 0) (n 1)) =
      ∑ c ∈ primaryElementBall F, ∑ u ∈ primaryElementBall F,
        W (norm (c^3*u))*f c u := by
  let S := Fintype.piFinset (fun _ : Fin 2 => primaryElementBall F)
  let g := fun n : Fin 2 → Eisenstein => n 0^3*n 1
  let w := fun n : Fin 2 → Eisenstein => W (norm (g n))*f (n 0) (n 1)
  have hreplace (b : Eisenstein) : W (norm b)*
      (∑ n ∈ primaryCubeFiber F b, f (n 0) (n 1)) =
      ∑ n ∈ S with g n = b, w n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have he := (Finset.mem_filter.mp hn).2
    dsimp [w,g]
    rw [he]
  simp_rw [hreplace]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  have he : (∑ n ∈ S with g n ∈ primaryElementBall F, w n) = ∑ n ∈ S, w n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnot
    have hn0 := (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp hn 0)).1
    have hn1 := (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp hn 1)).1
    have hgp : primary (g n) := primary_mul (primary_cube hn0) hn1
    have hgt : F < norm (g n) := by
      by_contra h
      have hgn : g n ∈ primaryElementBall F := mem_primaryElementBall.mpr ⟨hgp,le_of_not_gt h⟩
      exact hnot (Finset.mem_filter.mpr ⟨hn,hgn⟩)
    simp only [w,hW _ hgt,zero_mul]
  rw [he]
  exact sum_primary_fin_two (primaryElementBall F) (fun c u => W (norm (c^3*u))*f c u)

end CubicFirstMoment

end

end OAI
