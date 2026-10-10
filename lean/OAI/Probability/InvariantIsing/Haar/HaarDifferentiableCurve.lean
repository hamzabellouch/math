import OAI.Probability.InvariantIsing.Haar.HaarCurveBound

namespace OAI

/-! Finite-coordinate differentiable curves and their polynomial oscillation bounds. -/
noncomputable section
open Matrix Set
open scoped BigOperators
namespace InvariantIsing

structure HaarDifferentiableCurve (N : ℕ) where
  value : ℝ → SpecialOrthogonal N
  velocity : ℝ → Matrix (Fin N) (Fin N) ℝ
  hasDeriv : ∀ t ∈ Icc (0:ℝ) 1, ∀ i j,
    HasDerivAt (fun s => (value s : Matrix (Fin N) (Fin N) ℝ) i j) (velocity t i j) t
  continuous_velocity : ∀ i j, ContinuousOn (fun t => velocity t i j) (Icc (0:ℝ) 1)

namespace HaarDifferentiableCurve

lemma continuous_entry {N : ℕ} (γ : HaarDifferentiableCurve N) (i j : Fin N) :
    ContinuousOn (fun t => (γ.value t : Matrix (Fin N) (Fin N) ℝ) i j) (Icc (0:ℝ) 1) :=
  fun t ht => (γ.hasDeriv t ht i j).continuousAt.continuousWithinAt

def constant {N : ℕ} (U : SpecialOrthogonal N) : HaarDifferentiableCurve N where
  value := fun _ => U
  velocity := fun _ => 0
  hasDeriv := fun t _ _ _ => hasDerivAt_const t _
  continuous_velocity := fun _ _ => continuousOn_const

def mul {N : ℕ} (γ η : HaarDifferentiableCurve N) : HaarDifferentiableCurve N where
  value := fun t => γ.value t*η.value t
  velocity := fun t => γ.velocity t*(η.value t : Matrix (Fin N) (Fin N) ℝ)+
    (γ.value t : Matrix (Fin N) (Fin N) ℝ)*η.velocity t
  hasDeriv := by
    intro t ht i j
    have hd := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (γ.hasDeriv t ht i k).mul (η.hasDeriv t ht k j)
    convert hd using 1
    · rfl
    · simp only [Matrix.add_apply,Matrix.mul_apply,Finset.sum_add_distrib]
  continuous_velocity := by
    intro i j
    simp only [Matrix.add_apply,Matrix.mul_apply]
    exact (continuousOn_finsetSum _ fun k _ =>
      (γ.continuous_velocity i k).mul (η.continuous_entry k j)).add
        (continuousOn_finsetSum _ fun k _ =>
          (γ.continuous_entry i k).mul (η.continuous_velocity k j))

lemma polynomial_bound {N : ℕ} (γ : HaarDifferentiableCurve N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (p : MatrixPolynomial N) (δ : ℝ), 0 ≤ δ →
      (∀ V : SpecialOrthogonal N, haarPolynomialValue (haarPolynomialGamma p p) V ≤ δ^2) →
      |haarPolynomialValue p (γ.value 1)-haarPolynomialValue p (γ.value 0)| ≤ K*δ := by
  let F := fun t => ∑ i : Fin N, ∑ j : Fin N,
    |(γ.velocity t*(γ.value t : Matrix (Fin N) (Fin N) ℝ).transpose) i j|
  have hF : ContinuousOn F (Icc (0:ℝ) 1) := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    apply ContinuousOn.abs
    change ContinuousOn (fun t => ∑ k, γ.velocity t i k*
      (γ.value t : Matrix (Fin N) (Fin N) ℝ) j k) _
    exact continuousOn_finsetSum _ fun k _ =>
      (γ.continuous_velocity i k).mul (γ.continuous_entry j k)
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image hF
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro p δ hδ hp
  have hk (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : F t ≤ max C 0 :=
    (hC (mem_image_of_mem F ht)).trans (le_max_left _ _)
  have hb := haarPolynomial_curve_bound p γ.value γ.velocity (max C 0) δ hδ γ.hasDeriv hk hp
  exact hb.trans (by nlinarith [mul_nonneg (le_max_right C 0) hδ])

end HaarDifferentiableCurve
end InvariantIsing

end

end OAI
