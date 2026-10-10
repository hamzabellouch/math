import Mathlib
import OAI.Probability.SKRatio.Calculus.SpectralLower
import OAI.Probability.SKRatio.Calculus.Curvature

namespace OAI

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SKRatio.Fields
open Real Matrix Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma coupling_smul (g : Disorder n) (s : ℝ) (i j : Fin n) :
    coupling (s • g) i j = s*coupling g i j := by
  unfold coupling
  split_ifs <;> simp

lemma euclideanOpNorm_smul (T : Interaction n) (s : ℝ) :
    euclideanOpNorm (fun i j => s*T i j) = |s| *euclideanOpNorm T := by
  have he : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (fun i j => s*T i j) =
      s • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) T := by
    ext z i
    change (∑ j, s*T i j*z j) = s*(∑ j, T i j*z j)
    simp only [Finset.mul_sum,mul_assoc]
  unfold euclideanOpNorm
  rw [he,norm_smul,Real.norm_eq_abs]

theorem scaled_poincare_of_matrix_bounds (g : Disorder n) {K B δ ρ : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/1000)
    (hρ : 0 < ρ) (hmargin : ρ ≤ 1-(K+δ*B/3)-3840000*(δ*B))
    (hBK : 2*B ≤ K) (hnorm : euclideanOpNorm (coupling g) ≤ K)
    (he : ∀ i j, |coupling g i j| ≤ δ) (hrow : ∀ i, ∑ j, coupling g i j^2 ≤ B)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    ρ*variance (s • g) h f ≤ dirichlet (s • g) h f := by
  apply poincare_of_matrix_bounds (s • g) hK hB hδ hδsmall hρ hmargin hBK
  · simp only [show coupling (s • g) = fun i j => s*coupling g i j by
      funext i j; exact coupling_smul g s i j,euclideanOpNorm_smul,abs_of_nonneg hs]
    exact (mul_le_mul_of_nonneg_left hnorm hs).trans (by nlinarith [hK,hs1])
  · intro i j
    rw [coupling_smul,abs_mul,abs_of_nonneg hs]
    exact (mul_le_mul_of_nonneg_left (he i j) hs).trans (by nlinarith [hδ,hs1])
  · intro i
    simp only [coupling_smul,mul_pow,←Finset.mul_sum]
    apply le_trans (mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg s))
    have hs2 : s^2 ≤ 1 := by nlinarith [mul_nonneg hs (sub_nonneg.mpr hs1)]
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hs2)]

def linearObservable (a : Fin n → ℝ) (x : Spin n) : ℝ := ∑ i, a i*spinValue (x i)

lemma spinGradient_linearObservable (a : Fin n → ℝ) (i : Fin n) (x : Spin n) :
    spinGradient i (linearObservable a) x = a i := by
  unfold spinGradient linearObservable
  rw [←Finset.sum_sub_distrib]
  have he : (∑ j, (a j*spinValue (Function.update x i true j)-
      a j*spinValue (Function.update x i false j))) = 2*a i := by
    rw [Finset.sum_eq_single i]
    · simp;ring
    · intro j _ hji
      simp [Function.update_of_ne hji]
    · simp
  rw [he];ring

lemma dirichlet_linearObservable (g : Disorder n) (h a : Fin n → ℝ) :
    dirichlet g h (linearObservable a) ≤ ∑ i, a i^2 := by
  rw [dirichlet_weighted]
  apply Finset.sum_le_sum
  intro i _
  simp only [spinGradient_linearObservable]
  calc
    _ ≤ expectation g h (fun _ => a i^2) := by
      apply SKRatio.Fields.expectation_mono
      intro x
      exact mul_le_of_le_one_left (sq_nonneg (a i)) (siteVariance_le_one g h i x)
    _ = _ := expectation_const g h _

theorem covariance_bound_of_poincare (g : Disorder n) (h : Fin n → ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) (hgap : ∀ f, ρ*variance g h f ≤ dirichlet g h f) (a : Fin n → ℝ) :
    variance g h (linearObservable a) ≤ ρ⁻¹*(∑ i, a i^2) := by
  have hg := (hgap (linearObservable a)).trans (dirichlet_linearObservable g h a)
  rw [inv_mul_eq_div,le_div_iff₀ hρ]
  simpa only [mul_comm ρ] using hg

lemma heatBathGenerator_zero_field (g : Disorder n) (f : Spin n → ℝ) (x : Spin n) :
    heatBathGenerator g 0 f x = -generator (coupling g) f x := by
  simp only [heatBathGenerator,conditionalDifference_local,generator,
    ←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (spinValue (x i)-tanh (0+field (coupling g) x i))*halfDiff i f x =
    -((tanh (field (coupling g) x i)-spinValue (x i))*halfDiff i f x)
  rw [zero_add];ring

lemma variance_eq_finiteLaw (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    variance g h f = FiniteLaw.variance (mass g h) f := rfl

lemma dirichlet_zero_eq_stationaryEnergy (g : Disorder n) (f : Spin n → ℝ) :
    dirichlet g 0 f = stationaryEnergy g f := by
  rw [←heatBathGenerator_form,stationaryEnergy_eq]
  simp only [heatBathGenerator_zero_field,expectation,FiniteLaw.mean,mul_neg,
    Finset.sum_neg_distrib]

theorem stationary_poincare_of_matrix_bounds (g : Disorder n) {K B δ ρ : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/1000)
    (hρ : 0 < ρ) (hmargin : ρ ≤ 1-(K+δ*B/3)-3840000*(δ*B))
    (hBK : 2*B ≤ K) (hnorm : euclideanOpNorm (coupling g) ≤ K)
    (he : ∀ i j, |coupling g i j| ≤ δ) (hrow : ∀ i, ∑ j, coupling g i j^2 ≤ B)
    (f : Observables n) : ρ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f := by
  simpa only [variance_eq_finiteLaw,dirichlet_zero_eq_stationaryEnergy] using
    poincare_of_matrix_bounds g hK hB hδ hδsmall hρ hmargin hBK hnorm he hrow 0 f

theorem exists_uniform_gap_tolerance {β : ℝ} (hβ : 0 ≤ β) (hβhalf : β < 1/2) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∀ n : ℕ, ∀ g : Disorder n,
        euclideanOpNorm (coupling g) ≤ 2*β+δ →
        (∀ i j, |coupling g i j| ≤ δ) →
        (∀ i, ∑ j, coupling g i j^2 ≤ β^2+δ) →
        ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ h : Fin n → ℝ,
          (∀ f, ρ*variance (s • g) h f ≤ dirichlet (s • g) h f) ∧
          (∀ a, variance (s • g) h (linearObservable a) ≤ ρ⁻¹*(∑ i, a i^2)) := by
  let δ := min (1/1000:ℝ) ((1-2*β)/16000000)
  let ρ := (1-2*β)/2
  have hd : 0 < δ := lt_min (by norm_num) (div_pos (by linarith) (by norm_num))
  have hdsmall : δ ≤ 1/1000 := min_le_left _ _
  have hdt : δ ≤ (1-2*β)/16000000 := min_le_right _ _
  have hr : 0 < ρ := by dsimp [ρ];linarith
  refine ⟨δ,ρ,hd,hr,?_⟩
  intro n g hnorm he hrow s hs h
  have hB : 0 ≤ β^2+δ := add_nonneg (sq_nonneg β) hd.le
  have hB1 : β^2+δ ≤ 1 := by
    nlinarith [mul_nonneg hβ (show 0 ≤ 1/2-β by linarith)]
  have hBK : 2*(β^2+δ) ≤ 2*β+2*δ := by
    nlinarith [mul_nonneg hβ (show 0 ≤ 1-β by linarith)]
  have hmargin : ρ ≤ 1-(2*β+2*δ+δ*(β^2+δ)/3)-3840000*(δ*(β^2+δ)) := by
    have he₁ : δ*(β^2+δ) ≤ δ := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hB1)]
    dsimp [ρ]
    nlinarith only [he₁,hdt,hd.le]
  have hg : ∀ f, ρ*variance (s • g) h f ≤ dirichlet (s • g) h f := fun f =>
    scaled_poincare_of_matrix_bounds g (by positivity : 0 ≤ 2*β+2*δ)
      hB hd.le hdsmall hr hmargin hBK (hnorm.trans (by linarith))
      he hrow hs.1 hs.2 h f
  exact ⟨hg,covariance_bound_of_poincare (s • g) h hr hg⟩

end SKRatio.Fields

end
end

end OAI
