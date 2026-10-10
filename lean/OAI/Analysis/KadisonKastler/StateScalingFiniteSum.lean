import OAI.Analysis.KadisonKastler.StateScalingPartialIsometry

namespace OAI

/-! # Finite orthogonal sums of state-scaling partial isometries -/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem StateScales.sum {ι : Type*} (s : Finset ι) {r : ℝ}
    (a : ι → H →L[ℂ] H) (ha : ∀ i ∈ s, StateScales M Ω r (a i)) :
    StateScales M Ω r (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro x hx; simp [productVectorState]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (ha i (by simp)).add (ih (fun j hj => ha j (by simp [hj])))

theorem partialIsometry_sum_coisometry {ι : Type*} [Fintype ι]
    (v : ι → PartialIsometry M)
    (horth : ∀ i j, i ≠ j → (v i).support.val*(v j).support.val=0)
    (htotal : ∑ i, (v i).target.val=1) :
    (∑ i, (v i).val)*star (∑ i, (v i).val)=1 := by
  classical
  have hadj (i : ι) : (v i).adjoint.target=(v i).support := by
    apply Subtype.ext
    change star (v i).val*star (star (v i).val)=(v i).support.val
    rw [star_star,(v i).initial]
  have hcross (i j : ι) (hij : i ≠ j) : (v i).val*star (v j).val=0 :=
    (v i).mul_eq_zero (v j).adjoint (by rw [hadj]; exact horth i j hij)
  rw [star_sum,Finset.sum_mul]
  have he (i : ι) : (v i).val*(∑ j, star (v j).val)=(v i).target.val := by
    rw [Finset.mul_sum,Finset.sum_eq_single i]
    · rfl
    · intro j hj hji
      exact hcross i j hji.symm
    · simp
  simpa only [he] using htotal

end

end KadisonKastler

end OAI
