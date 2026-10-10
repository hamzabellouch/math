import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExpansionDifferentiation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorAllOrders
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialODEGrowthBound
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialODEGrowthRegularity

namespace OAI

/-! All differentiated asymptotic expansions of the actual canonical outgoing solution. -/

open Set Filter Polynomial
open scoped ContDiff BoundedContinuousFunction
namespace DefocusingNLS

theorem radialExteriorExpansion_difference_succ_dvd (ν : ℂ) (n : ℕ) (m : ℂ)
    (j k : ℕ) (hjk : j ≤ k) :
    X^(j+1) ∣ radialExteriorExpansion ν n m k-radialExteriorExpansion ν n m j := by
  apply X_pow_dvd_iff.mpr
  intro i hi
  rw [coeff_sub,radialExteriorExpansion_coeff_initial ν n m j k i hjk (by omega),sub_self]

theorem radialExteriorCanonical_derivative_selection (ν m : ℂ) (n : ℕ) (L : ℝ)
    (hX : HasRadialExterior ν n m L) (hm : m ≠ 0) (k : ℕ) (R : ℝ)
    (hR : 0 ≤ R) (J : ℕ) :
    ∃ j : ℕ, J ≤ j ∧ ∃ A T : ℝ, 0 ≤ A ∧ ∀ t, T ≤ t →
      ‖iteratedDeriv k ((fun s => (radialExteriorCanonical ν n m L s).1)-
        radialExteriorPolynomialFunction (radialExteriorExpansion ν n m j)) t‖ ≤
          A*Real.exp (-R*t) := by
  let Z := radialExteriorCanonical ν n m L
  have hZ : ∀ t, L < t → HasDerivAt Z (radialExteriorODEField ν n t (Z t)) t :=
    fun t ht => ((radialExteriorCanonical_spec hX).2.2 t ht.le).2
  apply radial_expansion_derivative_selection (fun t => (Z t).1)
    (radialExteriorExpansion ν n m) L
    (radialExteriorODE_position_contDiffOn ν n Z L hZ) _ _ k R hR J
  · intro q
    obtain ⟨C,B,T,hC,hB,_hLT,hb⟩ :=
      (radialExteriorCanonical_spec hX).2.1.derivatives_exponential_bound L hZ q
    exact ⟨C,B,T,hC,hB,hb⟩
  · intro K
    obtain ⟨j,hj,v,T,hT⟩ := radialExteriorCanonical_allOrders ν m n L hX hm K
    refine ⟨j,hj,‖v‖,T,norm_nonneg _,?_⟩
    intro t ht
    have he : (Z t).1-radialExteriorPolynomialFunction
        (radialExteriorExpansion ν n m j) t =
        (radialExteriorUnweight (2*(j : ℝ)) v t).1 := by
      dsimp only [Z]
      rw [hT t ht]
      simp only [Prod.fst_add,radialPolynomialJet,add_sub_cancel_left]
    rw [he]
    exact (norm_fst_le _).trans ((radialExteriorUnweight_norm _ t v ‖v‖
      (v.norm_coe_le_norm t)).trans_eq (mul_comm _ _))

theorem radialExteriorCanonical_derivative_expansion (ν m : ℂ) (n : ℕ) (L : ℝ)
    (hX : HasRadialExterior ν n m L) (hm : m ≠ 0) (j k : ℕ) :
    ∃ A T : ℝ, 0 ≤ A ∧ ∀ t, T ≤ t →
      ‖iteratedDeriv k ((fun s => (radialExteriorCanonical ν n m L s).1)-
        radialExteriorPolynomialFunction (radialExteriorExpansion ν n m j)) t‖ ≤
          A*Real.exp (-(2*((j+1 : ℕ) : ℝ))*t) := by
  let F := fun s => (radialExteriorCanonical ν n m L s).1
  let P := radialExteriorExpansion ν n m
  have hZ : ∀ t, L < t → HasDerivAt (radialExteriorCanonical ν n m L)
      (radialExteriorODEField ν n t (radialExteriorCanonical ν n m L t)) t :=
    fun t ht => ((radialExteriorCanonical_spec hX).2.2 t ht.le).2
  have hF : ContDiffOn ℝ ∞ F (Ioi L) :=
    radialExteriorODE_position_contDiffOn ν n _ L hZ
  obtain ⟨q,hq,A,T,hA,hb⟩ := radialExteriorCanonical_derivative_selection ν m n L hX hm
    k (2*((j+1 : ℕ) : ℝ)) (by positivity) j
  obtain ⟨B,hB,hp⟩ := radialExteriorPolynomial_deriv_decay (P q-P j) (j+1) k
    (radialExteriorExpansion_difference_succ_dvd ν n m j q hq)
  refine ⟨A+B,max T (max 0 (L+1)),add_nonneg hA hB,?_⟩
  intro t ht
  have htT : T ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 ≤ t := (le_max_left 0 _).trans ((le_max_right _ _).trans ht)
  have hLt : L < t := lt_of_lt_of_le (by linarith : L < L+1)
    ((le_max_right 0 _).trans ((le_max_right _ _).trans ht))
  have hf : ContDiffAt ℝ k F t :=
    ((hF t hLt).contDiffAt (Ioi_mem_nhds hLt)).of_le (by simp)
  have hpoly (p : ℂ[X]) : ContDiffAt ℝ k (radialExteriorPolynomialFunction p) t :=
    (radialPolynomialFunction_contDiff p).contDiffAt.of_le (by simp)
  have he : F-radialExteriorPolynomialFunction (P j) =
      (F-radialExteriorPolynomialFunction (P q))+
        radialExteriorPolynomialFunction (P q-P j) := by
    funext s
    simp only [Pi.sub_apply,Pi.add_apply,radialExteriorPolynomialFunction,eval_sub]
    ring
  have hsub : ContDiffAt ℝ k (F-radialExteriorPolynomialFunction (P q)) t :=
    hf.sub (hpoly (P q))
  rw [he,iteratedDeriv_add hsub (hpoly (P q-P j))]
  calc
    _ ≤ ‖iteratedDeriv k (F-radialExteriorPolynomialFunction (P q)) t‖+
        ‖iteratedDeriv k (radialExteriorPolynomialFunction (P q-P j)) t‖ := norm_add_le _ _
    _ ≤ A*Real.exp (-(2*((j+1 : ℕ) : ℝ))*t)+
        B*Real.exp (-(2*((j+1 : ℕ) : ℝ))*t) := add_le_add (hb t htT) (hp t ht0)
    _ = _ := by ring

end DefocusingNLS

end OAI
