import OAI.Probability.InvariantIsing.Haar.HaarHeatPositivity

namespace OAI

/-! Preservation of constants by the constructed polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma continuousLinearMap_exp_apply_of_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E) (v : E) (hv : A v=0) :
    NormedSpace.exp A v = v := by
  have hp (n : ℕ) : (A^(n+1)) v=0 := by
    induction n with
    | zero => simpa only [zero_add,pow_one] using hv
    | succ n ih =>
      rw [show n+1+1=(n+1)+1 by omega,pow_succ',mul_apply_eq_comp,ih,map_zero]
  have hn (n : ℕ) : ((n.factorial⁻¹ : ℝ) • A^n) v = if n=0 then v else 0 := by
    cases n with
    | zero => simp
    | succ n => simp only [_root_.smul_apply,hp,smul_zero,
        Nat.succ_ne_zero,ite_false]
  have hs := (ContinuousLinearMap.apply ℝ E v).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A)
  have ht : HasSum (fun n : ℕ => if n=0 then v else 0) (NormedSpace.exp A v) := by
    simpa only [ContinuousLinearMap.apply_apply,hn] using hs
  exact ht.unique (hasSum_ite_eq 0 v)

lemma haarPolynomialHeat_eq_of_laplacian_zero {N d : ℕ}
    (p : haarPolynomialSpace N d) (hp : haarPolynomialLaplacian N (p : MatrixPolynomial N)=0)
    (t : ℝ) : haarPolynomialHeat N d t p = p := by
  have hr : haarPolynomialRestrictedLaplacian N d p=0 := by
    apply Subtype.ext
    exact hp
  have hc : haarPolynomialCoordinateLaplacian N d (haarPolynomialCoordinates N d p)=0 := by
    rw [haarPolynomialCoordinateLaplacian_apply,hr,map_zero]
  apply (haarPolynomialCoordinates N d).injective
  rw [haarPolynomialCoordinates_heat]
  apply continuousLinearMap_exp_apply_of_zero
  simp only [_root_.smul_apply,hc,smul_zero]

lemma haarPolynomialLaplacian_one (N : ℕ) :
    haarPolynomialLaplacian N (1 : MatrixPolynomial N) = 0 := by
  simp only [haarPolynomialLaplacian_apply,Derivation.map_one_eq_zero,map_zero,
    Finset.sum_const_zero]

lemma haarPolynomialHeat_one (N d : ℕ) (t : ℝ) :
    haarPolynomialHeat N d t ⟨1,one_mem_haarPolynomialSpace N d⟩ =
      ⟨1,one_mem_haarPolynomialSpace N d⟩ :=
  haarPolynomialHeat_eq_of_laplacian_zero _ (haarPolynomialLaplacian_one N) t

end InvariantIsing

end

end OAI
