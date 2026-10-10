import Mathlib

namespace OAI

noncomputable section
open scoped Topology ContDiff Laplacian
open Set Filter MeasureTheory
namespace ClassicalIBP
section DerivativeBounds
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def D (v : V) (f : V → ℂ) (x : V) : ℂ := fderiv ℝ f x v

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma contDiff_D (v : V) (f : V → ℂ) {n : ℕ∞ω} (hf : ContDiff ℝ (n+1) f) :
    ContDiff ℝ n (D v f) :=
  (hf.fderiv_right le_rfl).clm_apply contDiff_const

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma D_D_eq (v w : V) (f : V → ℂ) (hf : ContDiff ℝ 2 f) (x : V) :
    D v (D w f) x = fderiv ℝ (fderiv ℝ f) x v w := by
  unfold D
  rw [fderiv_clm_apply ((hf.fderiv_right (by norm_num : (1 : ℕ∞ω)+1≤2)).differentiable
    (by norm_num)).differentiableAt (differentiableAt_const w)]
  simp

lemma integral_D_right (v : V) (φ u : V → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (hu : ContDiff ℝ 1 u) :
    (∫ x, φ x * D v u x) = -(∫ x, D v φ x * u x) := by
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℂ)
  · exact ((contDiff_D (n := 0) v φ hφ).continuous.mul hu.continuous).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_right
  · exact (hφ.continuous.mul (contDiff_D (n := 0) v u hu).continuous).integrable_of_hasCompactSupport
      hc.mul_right
  · exact (hφ.continuous.mul hu.continuous).integrable_of_hasCompactSupport hc.mul_right
  · intro x _
    exact ((hφ.differentiable (by norm_num)).differentiableAt.hasFDerivAt).hasLineDerivAt v
  · intro x _
    exact ((hu.differentiable (by norm_num)).differentiableAt.hasFDerivAt).hasLineDerivAt v

lemma integral_D_D_right (v : V) (φ u : V → ℂ) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (hu : ContDiff ℝ 2 u) :
    (∫ x, φ x * D v (D v u) x) = ∫ x, D v (D v φ) x * u x := by
  rw [integral_D_right v φ (D v u) (hφ.of_le (by norm_num)) hc (contDiff_D v u hu),
    integral_D_right v (D v φ) u (contDiff_D v φ hφ) (hc.fderiv_apply ℝ v)
      (hu.of_le (by norm_num)),neg_neg]

omit [MeasurableSpace V] [BorelSpace V] in
lemma laplacian_eq_sum_D (f : V → ℂ) (hf : ContDiff ℝ 2 f) :
    Δ f = fun x => ∑ i, D (stdOrthonormalBasis ℝ V i) (D (stdOrthonormalBasis ℝ V i) f) x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  funext x
  apply Finset.sum_congr rfl
  intro i _
  rw [D_D_eq _ _ f hf x,iteratedFDeriv_two_apply]
  rfl

lemma integral_laplacian_right (φ u : V → ℂ) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (hu : ContDiff ℝ 2 u) :
    (∫ x, φ x * Δ u x) = ∫ x, Δ φ x * u x := by
  rw [laplacian_eq_sum_D u hu,laplacian_eq_sum_D φ hφ]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  rw [integral_finsetSum,integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ => integral_D_D_right _ _ _ hφ hc hu)
  · intro i _
    exact ((contDiff_D (n := 0) _ _ (contDiff_D (n := 1) _ _ hφ)).continuous.mul hu.continuous).integrable_of_hasCompactSupport
      ((hc.fderiv_apply ℝ _).fderiv_apply ℝ _).mul_right
  · intro i _
    exact (hφ.continuous.mul (contDiff_D (n := 0) _ _ (contDiff_D (n := 1) _ _ hu)).continuous).integrable_of_hasCompactSupport
      hc.mul_right

omit [MeasurableSpace V] [BorelSpace V] in
lemma contDiff_laplacian (f : V → ℂ) (n : ℕ) (hf : ContDiff ℝ (n+2) f) :
    ContDiff ℝ n (Δ f) := by
  rw [laplacian_eq_sum_D f (hf.of_le (by exact_mod_cast Nat.le_add_left 2 n))]
  apply ContDiff.sum
  intro i _
  apply contDiff_D
  apply contDiff_D
  convert hf using 1
  ring

omit [MeasurableSpace V] [BorelSpace V] in
lemma compactSupport_laplacian (φ : V → ℂ) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) : HasCompactSupport (Δ φ) := by
  rw [laplacian_eq_sum_D φ hφ]
  classical
  have hsum (s : Finset (Fin (Module.finrank ℝ V))) :
      HasCompactSupport (fun x => ∑ i ∈ s,
        D (stdOrthonormalBasis ℝ V i) (D (stdOrthonormalBasis ℝ V i) φ) x) := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        exact HasCompactSupport.zero
    | @insert i s his ih =>
        simp only [Finset.sum_insert his]
        exact ((hc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V i)).fderiv_apply ℝ
            (stdOrthonormalBasis ℝ V i)).add ih
  simpa using hsum Finset.univ

lemma integral_bilaplacian_right (φ u : V → ℂ) (hφ : ContDiff ℝ 4 φ)
    (hc : HasCompactSupport φ) (hu : ContDiff ℝ 4 u) :
    (∫ x, φ x * Δ (Δ u) x) = ∫ x, Δ (Δ φ) x * u x := by
  rw [integral_laplacian_right φ (Δ u) (hφ.of_le (by norm_num)) hc
      (contDiff_laplacian u 2 hu),
    integral_laplacian_right (Δ φ) u (contDiff_laplacian φ 2 hφ)
      (compactSupport_laplacian φ (hφ.of_le (by norm_num)) hc) (hu.of_le (by norm_num))]
end DerivativeBounds

open scoped BigOperators
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

def directional : (n : ℕ) → (Fin n → V) → (V → ℂ) → (V → ℂ)
  | 0, _, f => f
  | n+1, m, f => D (m 0) (directional n (Fin.tail m) f)

omit [FiniteDimensional ℝ V] in
lemma iteratedFDeriv_eq_directional (n : ℕ) (f : V → ℂ)
    (hf : ContDiff ℝ n f) (m : Fin n → V) (x : V) :
    iteratedFDeriv ℝ n f x m = directional n m f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
      hf.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
    rw [hd.differentiableAt.iteratedFDeriv_succ_apply_left']
    have he : (fun y => iteratedFDeriv ℝ n f y (Fin.tail m)) =
        directional n (Fin.tail m) f :=
      funext (fun y => ih (hf.of_le (by exact_mod_cast Nat.le_succ n)) (Fin.tail m) y)
    rw [he]
    rfl

omit [FiniteDimensional ℝ V] in
lemma D_sum {ι : Type*} (s : Finset ι) (g : ι → V → ℂ) (v : V)
    (hg : ∀ i ∈ s, Differentiable ℝ (g i)) :
    D v (fun x => ∑ i ∈ s, g i x) = fun x => ∑ i ∈ s, D v (g i) x := by
  funext x
  unfold D
  rw [fderiv_fun_sum (fun i hi => (hg i hi).differentiableAt)]
  simp

lemma laplacian_sum {ι : Type*} (s : Finset ι) (g : ι → V → ℂ)
    (hg : ∀ i ∈ s, ContDiff ℝ 2 (g i)) :
    Δ (fun x => ∑ i ∈ s, g i x) = fun x => ∑ i ∈ s, Δ (g i) x := by
  simp_rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  funext x
  simp_rw [iteratedFDeriv_fun_sum_apply (fun i hi => (hg i hi).contDiffAt)]
  simp only [sum_apply]
  exact Finset.sum_comm

def traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ :=
  ∑ i : Fin (Module.finrank ℝ V), ∑ j : Fin (Module.finrank ℝ V),
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 4 => V) ℂ
      ![stdOrthonormalBasis ℝ V i, stdOrthonormalBasis ℝ V i,
        stdOrthonormalBasis ℝ V j, stdOrthonormalBasis ℝ V j]

lemma bilaplacian_eq_traceFour (f : V → ℂ) (hf : ContDiff ℝ 4 f) (x : V) :
    Δ (Δ f) x = traceFour (iteratedFDeriv ℝ 4 f x) := by
  rw [laplacian_eq_sum_D f (hf.of_le (by norm_num))]
  have hg : ∀ j : Fin (Module.finrank ℝ V), ContDiff ℝ 2
      (D (stdOrthonormalBasis ℝ V j) (D (stdOrthonormalBasis ℝ V j) f)) :=
    fun j => contDiff_D _ _ (contDiff_D _ _ hf)
  rw [laplacian_sum Finset.univ _ (fun j _ => hg j)]
  simp only [traceFour,sum_apply,ContinuousMultilinearMap.apply_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [laplacian_eq_sum_D _ (hg i)]
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedFDeriv_eq_directional 4 f hf]
  rfl
end ClassicalIBP

end

end OAI
