import OAI.Geometry.NodalSets.Elliptic.PolynomialEvaluation

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

def FlatAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f : Coord → F) (x : Coord) : Prop :=
  ∀ k, k ≤ n → iteratedFDeriv ℝ k f x = 0

lemma FlatAt.mono {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n m : ℕ} {f : Coord → F} {x : Coord} (h : FlatAt n f x) (hm : m ≤ n) :
    FlatAt m f x := fun k hk ↦ h k (hk.trans hm)

lemma FlatAt.add {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {f g : Coord → F} {x : Coord}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (h : FlatAt n f x) (h' : FlatAt n g x) : FlatAt n (fun y ↦ f y + g y) x := by
  intro k hk
  change iteratedFDeriv ℝ k (f + g) x = 0
  rw [iteratedFDeriv_add_apply (hf.of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    (hg.of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt, h k hk, h' k hk, add_zero]

lemma FlatAt.sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} (s : Finset ι) {n : ℕ} {f : ι → Coord → F} {x : Coord}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (h : ∀ i ∈ s, FlatAt n (f i) x) :
    FlatAt n (fun y ↦ ∑ i ∈ s, f i y) x := by
  intro k hk
  rw [iteratedFDeriv_fun_sum_apply (fun i hi ↦ ((hf i hi).of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt)]
  exact Finset.sum_eq_zero (fun i hi ↦ h i hi k hk)

theorem FlatAt.mul {n : ℕ} {f g : Coord → ℂ} {x : Coord}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (h : FlatAt n f x) :
    FlatAt n (fun y ↦ f y * g y) x := by
  intro k hk
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have hb := norm_iteratedFDeriv_mul_le hf hg x (n := k) (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
  calc
    _ ≤ _ := hb
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [h i (by have := Finset.mem_range.mp hi; omega), norm_zero]
      ring

lemma FlatAt.fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {f : Coord → F} {x : Coord} (h : FlatAt (n + 1) f x) :
    FlatAt n (fderiv ℝ f) x := by
  intro k hk
  apply norm_eq_zero.mp
  rw [norm_iteratedFDeriv_fderiv, h (k + 1) (by omega), norm_zero]

lemma FlatAt.clm_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ} {f : Coord → F} {x : Coord}
    (hf : ContDiff ℝ ∞ f) (h : FlatAt n f x) (L : F →L[ℝ] G) :
    FlatAt n (L ∘ f) x := by
  intro k hk
  rw [L.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)), h k hk]
  ext v
  simp

lemma coordPartial_contDiff {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
    ContDiff ℝ ∞ (coordPartial i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem FlatAt.coordPartial {n : ℕ} {f : Coord → ℂ} {x : Coord}
    (hf : ContDiff ℝ ∞ f) (h : FlatAt (n + 1) f x) (i : Fin 4) :
    FlatAt n (coordPartial i f) x := by
  let L : (Coord →L[ℝ] ℂ) →L[ℝ] ℂ :=
    ContinuousLinearMap.apply ℝ ℂ (Pi.single i 1)
  exact h.fderiv.clm_comp (hf.fderiv_right (by simp)) L

lemma fderiv_reval_eq (p : CPoly) :
    fderiv ℝ (reval p) = fun x ↦ ∑ i, reval (pderiv i p) x • coordCLM i := by
  funext x
  ext v
  simp [fderiv_reval, coordCLM, smul_eq_mul]

theorem flatAt_reval {p : CPoly} {n : ℕ}
    (h : ∀ k, k ≤ n → homogeneousComponent k p = 0) : FlatAt n (reval p) 0 := by
  induction n generalizing p with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    apply norm_eq_zero.mp
    rw [norm_iteratedFDeriv_zero]
    have hc := congrArg (fun polynomial : CPoly ↦ polynomial.coeff 0) (h 0 le_rfl)
    simpa [reval, eval_zero, constantCoeff_eq, coeff_homogeneousComponent] using congrArg norm hc
  | succ n ih =>
    have hp (i : Fin 4) : FlatAt n (reval (pderiv i p)) 0 := by
      apply ih
      intro k hk
      rw [homogeneousComponent_pderiv, h (k + 1) (by omega), map_zero]
    have hd : FlatAt n (fderiv ℝ (reval p)) 0 := by
      rw [fderiv_reval_eq]
      apply FlatAt.sum Finset.univ
      · intro i _
        exact (reval_contDiff _).smul contDiff_const
      · intro i _ k hk
        rw [iteratedFDeriv_smul_const_apply ((reval_contDiff _).of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt,
          hp i k hk]
        ext v
        simp
    intro k hk
    cases k with
    | zero =>
      exact (ih (fun j hj ↦ h j (by omega))) 0 (by omega)
    | succ k =>
      apply norm_eq_zero.mp
      rw [← norm_iteratedFDeriv_fderiv, hd k (by omega), norm_zero]

end
end Yau.Jets

end OAI
