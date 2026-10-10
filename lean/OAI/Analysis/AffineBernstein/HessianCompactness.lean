import Mathlib
import OAI.Analysis.AffineBernstein.GlobalHessianBound

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section HessianCompactness
open Matrix

lemma constant_det_directional_subsolution {n : ℕ} (hn : 1 ≤ n) {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hD : ∀ x y, (hessian u x).det=(hessian u y).det) (e x : Space n) :
    0 ≤ inverseHessianTrace u (dirDeriv e (dirDeriv e u)) x := by
  by_cases he : e=0
  · subst e
    have heq : dirDeriv (0:Space n) (dirDeriv 0 u) = fun _ => 0 := by
      funext y
      simp [dirDeriv]
    rw [heq,inverseHessianTrace_constant]
  have hf : 0 < dirDeriv e (dirDeriv e u) x := by
    rw [dirDeriv_eq_second hu.contDiffAt]
    exact second_fderiv_pos hu.contDiffAt (hp x) he
  have hcoeff : 0 < (n:ℝ)*dirDeriv e (dirDeriv e u) x :=
    mul_pos (by exact_mod_cast hn) hf
  have hQ := inverseHessianPair_self_nonneg (hp x) (dirDeriv e (dirDeriv e u))
  have H := constant_det_directional_jacobi hn hu hp hD e x
  have Hpos : 0 ≤ (n:ℝ)*dirDeriv e (dirDeriv e u) x*inverseHessianTrace u (dirDeriv e (dirDeriv e u)) x :=
    (mul_nonneg (by positivity : 0 ≤ (n:ℝ)+1) hQ).trans H
  by_contra Hneg
  have HH := mul_neg_of_pos_of_neg hcoeff (lt_of_not_ge Hneg)
  linarith

lemma posSemidef_entry_abs_le_diagonals {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (i j : Fin n) : |A i j| ≤ (A i i+A j j)/2 := by
  have hsym : A j i = A i j := (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian).apply i j
  have hp := hA.dotProduct_mulVec_nonneg (Pi.single i 1+Pi.single j 1)
  have hm := hA.dotProduct_mulVec_nonneg (Pi.single i 1-Pi.single j 1)
  simp only [star_trivial,Matrix.mulVec_add,Matrix.mulVec_sub,add_dotProduct,sub_dotProduct,
    dotProduct_add,dotProduct_sub,Matrix.mulVec_single_one,single_dotProduct,Matrix.col_apply,
    one_mul,hsym] at hp hm
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma balanced_hessian_range_compact {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hbal : SectionBalance univ u ρ) : IsCompact (closure (range (hessian u))) := by
  classical
  have hb := fun i : Fin n => balanced_global_directional_bddAbove hn hu hp hm hρ hρ1 hbal (coordinateVector n i)
  choose C hC using hb
  have hc (x : Space n) (i : Fin n) : hessian u x i i ≤ C i := hC i ⟨x,rfl⟩
  let D : Matrix (Fin n) (Fin n) ℝ := fun i j => (C i+C j)/2
  let K := univ.pi (fun i : Fin n => univ.pi (fun j : Fin n => Icc (-D i j) (D i j)))
  have hK : IsCompact K := isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_Icc
  have hsub : range (hessian u) ⊆ K := by
    rintro A ⟨x,rfl⟩ i hi j hj
    have H := (posSemidef_entry_abs_le_diagonals (hp x).posSemidef i j).trans
      (show (hessian u x i i+hessian u x j j)/2 ≤ D i j by dsimp [D]; linarith [hc x i,hc x j])
    exact abs_le.mp H
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hsub hK.isClosed)

lemma hessian_closure_isSymm {n : ℕ} {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ closure (range (hessian u))) : A.IsSymm := by
  have hc : IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.transpose=A} :=
    isClosed_eq continuous_id.matrix_transpose continuous_id
  have hs : range (hessian u) ⊆ {B | B.transpose=B} := by
    rintro B ⟨x,rfl⟩
    exact hessian_isSymm hu.contDiffAt
  exact closure_minimal hs hc hA

lemma hessian_closure_det {n : ℕ} {u : Space n → ℝ}
    (hD : ∀ x y, (hessian u x).det=(hessian u y).det)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ closure (range (hessian u))) : A.det=(hessian u 0).det := by
  have hc : IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.det=(hessian u 0).det} :=
    isClosed_eq continuous_id.matrix_det continuous_const
  have hs : range (hessian u) ⊆ {B | B.det=(hessian u 0).det} := by
    rintro B ⟨x,rfl⟩
    exact hD x 0
  exact closure_minimal hs hc hA

end HessianCompactness


end
end AffineBernstein
end

end OAI
