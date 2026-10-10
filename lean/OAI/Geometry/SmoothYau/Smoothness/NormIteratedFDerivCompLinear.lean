import Mathlib
import OAI.Geometry.SmoothYau.Estimates.FiniteGaussianSuperpositionSmallBall

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

def realWaveJet (n W : ℝ) (u : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    (Fin 1 ⊕ Fin 3) → ℝ :=
  Sum.elim (fun _ => W⁻¹*u x)
    (fun i => n⁻¹*W⁻¹*fderiv ℝ u x (Pi.single i 1))

lemma realWaveJet_add (n W : ℝ) {u v : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    realWaveJet n W (fun y => u y+v y) x = realWaveJet n W u x+realWaveJet n W v x := by
  ext i
  rcases i with i|i <;> simp [realWaveJet,fderiv_fun_add hu hv,mul_add]

lemma realWaveJet_sum {I : Type*} [Fintype I] (n W : ℝ)
    {u : I → (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) :
    realWaveJet n W (fun y => ∑ i, u i y) x = ∑ i, realWaveJet n W (u i) x := by
  ext j
  rcases j with j|j <;>
    simp [realWaveJet,fderiv_fun_sum (fun i _ => hu i),Finset.mul_sum]

lemma fderiv_re_const_mul {u : (Fin 3 → ℝ) → ℂ} {x : Fin 3 → ℝ}
    (hu : DifferentiableAt ℝ u x) (γ : ℂ) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun y => (γ*u y).re) x v = (γ*fderiv ℝ u x v).re := by
  have h := (Complex.reCLM.hasFDerivAt.comp x (hu.hasFDerivAt.const_mul γ)).fderiv
  exact congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L v) h

lemma realWaveJet_re_const_mul (n W : ℝ) {u : (Fin 3 → ℝ) → ℂ} {x : Fin 3 → ℝ}
    (hu : DifferentiableAt ℝ u x) (γ : ℂ) :
    realWaveJet n W (fun y => (γ*u y).re) x =
      fun i => (γ*complexWaveJet n (W : ℂ) u x i).re := by
  ext i
  rcases i with i|i
  · simp only [realWaveJet,complexWaveJet,Sum.elim_inl,←Complex.ofReal_inv]
    simp [Complex.mul_re,Complex.mul_im]
    ring
  · simp only [realWaveJet,complexWaveJet,Sum.elim_inr,←Complex.ofReal_inv,
      fderiv_re_const_mul hu γ,waveDeriv]
    simp [Complex.mul_re,Complex.mul_im]
    ring

lemma realWaveJet_three (n W : ℝ) (U : Fin 3 → (Fin 3 → ℝ) → ℂ)
    {x : Fin 3 → ℝ} (hU : ∀ ℓ, DifferentiableAt ℝ (U ℓ) x) (γ : Fin 3 → ℂ) :
    realWaveJet n W (fun y => ∑ ℓ, (γ ℓ*U ℓ y).re) x =
      complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) γ := by
  have hd (ℓ : Fin 3) : DifferentiableAt ℝ (fun y => (γ ℓ*U ℓ y).re) x :=
    Complex.reCLM.differentiableAt.comp x ((hU ℓ).const_mul (γ ℓ))
  rw [realWaveJet_sum n W hd]
  ext i
  simp only [Finset.sum_apply,realWaveJet_re_const_mul n W (hU _) _,complexRealResponse]

lemma realWaveJet_comp_bound (n W : ℝ) {u : (Fin 3 → ℝ) → ℝ}
    {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {x : Fin 3 → ℝ}
    (hu : DifferentiableAt ℝ u (F x)) (hF : DifferentiableAt ℝ F x) :
    ‖realWaveJet n W (u ∘ F) x‖ ≤
      max 1 (3*‖fderiv ℝ F x‖)*‖realWaveJet n W u (F x)‖ := by
  let J := realWaveJet n W u (F x)
  have hJ0 : 0 ≤ ‖J‖ := norm_nonneg _
  have hconst : 1 ≤ max 1 (3*‖fderiv ℝ F x‖) := le_max_left _ _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by linarith) hJ0)).mpr
  intro i
  rcases i with i|i
  · change ‖W⁻¹*u (F x)‖ ≤ _
    exact (norm_le_pi_norm J (Sum.inl i)).trans (le_mul_of_one_le_left hJ0 hconst)
  · rw [realWaveJet,Sum.elim_inr,fderiv_comp x hu hF,ContinuousLinearMap.comp_apply]
    have hv : fderiv ℝ F x (Pi.single i 1) =
        ∑ j : Fin 3, (fderiv ℝ F x (Pi.single i 1) j) • Pi.single j 1 := by
      ext j
      simp [Pi.single_apply]
    rw [hv,map_sum,Finset.mul_sum]
    have hsum : ‖∑ j : Fin 3, n⁻¹*W⁻¹*fderiv ℝ u (F x)
        (fderiv ℝ F x (Pi.single i 1) j • Pi.single j 1)‖ ≤
        ∑ _j : Fin 3, ‖fderiv ℝ F x‖*‖J‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [map_smul,smul_eq_mul]
      have heq : n⁻¹*W⁻¹*(fderiv ℝ F x (Pi.single i 1) j*
          fderiv ℝ u (F x) (Pi.single j 1)) =
          fderiv ℝ F x (Pi.single i 1) j * J (Sum.inr j) := by dsimp [J,realWaveJet]; ring
      rw [heq,norm_mul]
      apply mul_le_mul (le_trans (norm_le_pi_norm _ j) ?_) (norm_le_pi_norm J (.inr j))
        (norm_nonneg _) (norm_nonneg _)
      simpa only [Pi.norm_single,norm_one,mul_one] using (fderiv ℝ F x).le_opNorm (Pi.single i 1)
    calc
      _ ≤ ∑ _j : Fin 3, ‖fderiv ℝ F x‖*‖J‖ := hsum
      _ = (3*‖fderiv ℝ F x‖)*‖J‖ := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hJ0

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

def finiteWaveSuperposition {E I : Type*} [Fintype I]
    (w : E → ℝ) (U : I → Fin 3 → E → ℂ) (γ : I → Fin 3 → ℂ) (x : E) : ℝ :=
  w x+∑ i, ∑ ℓ, (γ i ℓ*U i ℓ x).re

lemma contDiff_finiteWaveSuperposition {E I : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : E → ℝ} {U : I → Fin 3 → E → ℂ}
    (hw : ContDiff ℝ ∞ w) (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (γ : I → Fin 3 → ℂ) : ContDiff ℝ ∞ (finiteWaveSuperposition w U γ) :=
  hw.add (ContDiff.sum (fun i _ => ContDiff.sum (fun ℓ _ =>
    Complex.reCLM.contDiff.comp (contDiff_const.mul (hU i ℓ)))))

lemma realWaveJet_finiteWaveSuperposition {I : Type*} [Fintype I]
    (n W : ℝ) (w : (Fin 3 → ℝ) → ℝ) (U : I → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hw : ContDiff ℝ ∞ w) (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (γ : I → Fin 3 → ℂ) (x : Fin 3 → ℝ) :
    realWaveJet n W (finiteWaveSuperposition w U γ) x =
      (∑ i, complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U i ℓ) x) (γ i))+
        realWaveJet n W w x := by
  have hd (i) : DifferentiableAt ℝ (fun y => ∑ ℓ, (γ i ℓ*U i ℓ y).re) x :=
    DifferentiableAt.fun_sum (fun ℓ _ => Complex.reCLM.differentiableAt.comp x
      (((hU i ℓ).differentiable (by simp) x).const_mul (γ i ℓ)))
  unfold finiteWaveSuperposition
  rw [realWaveJet_add n W (hw.differentiable (by simp) x)
    (DifferentiableAt.fun_sum (fun i _ => hd i)),realWaveJet_sum n W hd]
  simp only [realWaveJet_three n W _ (fun ℓ => (hU _ ℓ).differentiable (by simp) x) _]
  exact add_comm _ _

theorem finite_superposition_pullback_smallBall {I : Type} [Fintype I]
    (n W : ℝ) (w : (Fin 3 → ℝ) → ℝ) (U : I → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hw : ContDiff ℝ ∞ w) (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (hF : ContDiff ℝ ∞ F) (x : Fin 3 → ℝ)
    (M : ℝ) (hM : max 1 (3*‖fderiv ℝ F x‖) ≤ M)
    (i₀ : I) (r : ℝ) (q : ℝ≥0∞)
    (hsmall : ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise →
      (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U i₀ ℓ ∘ F) x) v.2+
          noise v.1 ∈ Metric.closedBall 0 (M*r)} ≤ q) :
    (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
      {γ | ‖realWaveJet n W (finiteWaveSuperposition w U γ) (F x)‖ ≤ r} ≤ q := by
  let J : I → Fin 3 → ((Fin 1 ⊕ Fin 3) → ℂ) :=
    fun i ℓ => complexWaveJet n (W : ℂ) (U i ℓ ∘ F) x
  have h := finite_gaussian_superposition_smallBall J (realWaveJet n W (w ∘ F) x)
    i₀ (M*r) q hsmall
  apply le_trans (measure_mono ?_) h
  intro γ hγ
  change (∑ i, complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U i ℓ ∘ F) x) (γ i))+
    realWaveJet n W (w ∘ F) x ∈ Metric.closedBall 0 (M*r)
  rw [←realWaveJet_finiteWaveSuperposition n W (w ∘ F) (fun i ℓ => U i ℓ ∘ F)
    (hw.comp hF) (fun i ℓ => (hU i ℓ).comp hF)]
  rw [Metric.mem_closedBall,dist_zero_right]
  change ‖realWaveJet n W ((finiteWaveSuperposition w U γ) ∘ F) x‖ ≤ M*r
  have hb := realWaveJet_comp_bound n W
    ((contDiff_finiteWaveSuperposition hw hU γ).differentiable (by simp) (F x))
    (hF.differentiable (by simp) x)
  exact hb.trans ((mul_le_mul_of_nonneg_right hM (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hγ (le_trans (by norm_num) ((le_max_left _ _).trans hM))))

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_iteratedFDeriv_real_complex_mul {u : E → ℂ}
    (hu : ContDiff ℝ ∞ u) (a : ℂ) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => (a*u y).re) x‖ ≤
      ‖a‖*‖iteratedFDeriv ℝ j u x‖ := by
  have h : ContDiff ℝ ∞ (fun y => a*u y) := contDiff_const.mul hu
  have hh := Complex.reCLM.norm_iteratedFDeriv_comp_left h.contDiffAt (x := x) (n := j) (show (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))
  have he : iteratedFDeriv ℝ j (fun y => a*u y) x = a • iteratedFDeriv ℝ j u x :=
    by simpa only [smul_eq_mul] using iteratedFDeriv_const_smul_apply' (a := a) (x := x) (hu.of_le (show (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt
  simpa only [Complex.reCLM_norm,one_mul,he,norm_smul,Function.comp_def,Complex.reCLM_apply] using hh

lemma norm_iteratedFDeriv_finiteWaveSum {I : Type*} [Fintype I]
    {U : I → Fin 3 → E → ℂ} (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (γ : I → Fin 3 → ℂ) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => ∑ i, ∑ ℓ, (γ i ℓ*U i ℓ y).re) x‖ ≤
      ∑ i, ∑ ℓ, ‖γ i ℓ‖*‖iteratedFDeriv ℝ j (U i ℓ) x‖ := by
  classical
  have hs (i) (ℓ) : ContDiff ℝ ∞ (fun y => (γ i ℓ*U i ℓ y).re) :=
    Complex.reCLM.contDiff.comp (contDiff_const.mul (hU i ℓ))
  rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
    ((ContDiff.sum (fun ℓ _ => hs i ℓ)).of_le (show (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt)]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [iteratedFDeriv_fun_sum_apply (fun ℓ _ => ((hs i ℓ).of_le (show (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt)]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun ℓ _ =>
    norm_iteratedFDeriv_real_complex_mul (hU i ℓ) (γ i ℓ) j x))

theorem finiteWaveSum_derivative_bound {I : Type*} [Fintype I]
    {U : I → Fin 3 → E → ℂ} (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (γ : I → Fin 3 → ℂ) {n Q T W : ℝ} (hn : 0 ≤ n) (hT : 0 ≤ T) (hW : 0 ≤ W)
    (hcard : (Fintype.card I : ℝ) ≤ Q*n^3) (hγ : ∀ i ℓ, ‖γ i ℓ‖ ≤ n)
    (j : ℕ) (x : E) (hbound : ∀ i ℓ, ‖iteratedFDeriv ℝ j (U i ℓ) x‖ ≤ T*n^j*W) :
    ‖iteratedFDeriv ℝ j (fun y => ∑ i, ∑ ℓ, (γ i ℓ*U i ℓ y).re) x‖ ≤
      (3*Q*T)*n^(j+4)*W := by
  classical
  calc
    _ ≤ ∑ i, ∑ ℓ, ‖γ i ℓ‖*‖iteratedFDeriv ℝ j (U i ℓ) x‖ :=
      norm_iteratedFDeriv_finiteWaveSum hU γ j x
    _ ≤ ∑ _i : I, ∑ _ℓ : Fin 3, n*(T*n^j*W) := by
      apply Finset.sum_le_sum; intro i _
      exact Finset.sum_le_sum (fun ℓ _ =>
        mul_le_mul (hγ i ℓ) (hbound i ℓ) (norm_nonneg _) hn)
    _ = (Fintype.card I : ℝ)*3*(n*(T*n^j*W)) := by simp; ring
    _ ≤ (Q*n^3)*3*(n*(T*n^j*W)) := by gcongr
    _ = _ := by rw [pow_add]; ring
end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma normalized_scalar_derivative_bound {f W : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hW : DifferentiableAt ℝ W x) (hW0 : 0 < W x)
    {B₀ B₁ H : ℝ} (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hH : 0 ≤ H)
    (h₀ : ‖f x‖ ≤ B₀*W x) (h₁ : ‖fderiv ℝ f x‖ ≤ B₁*W x)
    (hlog : ‖fderiv ℝ W x‖ ≤ H*W x) :
    DifferentiableAt ℝ (fun y => (W y)⁻¹*f y) x ∧
      ‖fderiv ℝ (fun y => (W y)⁻¹*f y) x‖ ≤ B₁+B₀*H := by
  have hi := (hasDerivAt_inv hW0.ne').comp_hasFDerivAt x hW.hasFDerivAt
  have hd := hi.mul hf.hasFDerivAt
  refine ⟨hd.differentiableAt,?_⟩
  change ‖fderiv ℝ (((fun z : ℝ => z⁻¹) ∘ W)*f) x‖ ≤ _
  rw [hd.fderiv]
  calc
    _ ≤ ‖(W x)⁻¹ • fderiv ℝ f x‖ +
        ‖f x • (-(W x^2)⁻¹ • fderiv ℝ W x)‖ := norm_add_le _ _
    _ = (W x)⁻¹*‖fderiv ℝ f x‖ + ‖f x‖*((W x^2)⁻¹*‖fderiv ℝ W x‖) := by
      simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_neg,
        abs_of_pos hW0,abs_of_pos (pow_pos hW0 2)]
    _ ≤ (W x)⁻¹*(B₁*W x)+(B₀*W x)*((W x^2)⁻¹*(H*W x)) := by
      apply add_le_add
      · simpa only [mul_comm] using
          mul_le_mul h₁ (le_refl ((W x)⁻¹))
            (inv_nonneg.mpr hW0.le) (mul_nonneg hB₁ hW0.le)
      · apply mul_le_mul h₀ _
          (mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (norm_nonneg _))
          (mul_nonneg hB₀ hW0.le)
        simpa only [mul_comm] using
          mul_le_mul hlog (le_refl ((W x^2)⁻¹))
            (inv_nonneg.mpr (sq_nonneg _)) (mul_nonneg hH hW0.le)
    _ = _ := by field_simp

lemma normalized_scalar_lipschitz {f W : E → ℝ}
    (hf : Differentiable ℝ f) (hW : Differentiable ℝ W) (hW0 : ∀ x, 0 < W x)
    {B₀ B₁ H : ℝ} (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hH : 0 ≤ H)
    (h₀ : ∀ x, ‖f x‖ ≤ B₀*W x) (h₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ B₁*W x)
    (hlog : ∀ x, ‖fderiv ℝ W x‖ ≤ H*W x) (x y : E) :
    ‖(W x)⁻¹*f x-(W y)⁻¹*f y‖ ≤ (B₁+B₀*H)*dist x y := by
  have hb (z : E) := normalized_scalar_derivative_bound (hf z) (hW z) (hW0 z)
    hB₀ hB₁ hH (h₀ z) (h₁ z) (hlog z)
  simpa only [dist_eq_norm] using
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z (_ : z ∈ (Set.univ : Set E)) => (hb z).1)
      (fun z _ => (hb z).2) convex_univ (Set.mem_univ y) (Set.mem_univ x)

lemma norm_fderiv_evaluation {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (v : E) :
    ‖fderiv ℝ (fun y => fderiv ℝ u y v) x‖ ≤ ‖v‖*‖fderiv ℝ (fderiv ℝ u) x‖ := by
  let L := ContinuousLinearMap.apply ℝ ℝ v
  have hL : ‖L‖ ≤ ‖v‖ := L.opNorm_le_bound (norm_nonneg _) (fun f => by
    simpa only [L,ContinuousLinearMap.apply_apply,mul_comm] using f.le_opNorm v)

  change ‖fderiv ℝ (L ∘ fderiv ℝ u) x‖ ≤ _
  rw [fderiv_comp x L.differentiableAt hu,L.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

theorem realWaveJet_lipschitz_of_relative_bounds
    {u W : (Fin 3 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u)
    (hW : Differentiable ℝ W) (hW0 : ∀ x, 0 < W x)
    {n B₀ B₁ B₂ H L : ℝ} (hn : 0 < n)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hH : 0 ≤ H)
    (h₀ : ∀ x, ‖u x‖ ≤ B₀*W x)
    (h₁ : ∀ x, ‖fderiv ℝ u x‖ ≤ B₁*W x)
    (h₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B₂*W x)
    (hlog : ∀ x, ‖fderiv ℝ W x‖ ≤ H*W x)
    (hL₀ : B₁+B₀*H ≤ L) (hL₁ : n⁻¹*(B₂+B₁*H) ≤ L) (x y : Fin 3 → ℝ) :
    ‖realWaveJet n (W x) u x-realWaveJet n (W y) u y‖ ≤ L*dist x y := by
  have hL : 0 ≤ L := (by positivity : 0 ≤ B₁+B₀*H).trans hL₀
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hL dist_nonneg)).mpr
  intro i
  rcases i with i|i
  · exact (normalized_scalar_lipschitz (hu.differentiable (by simp)) hW hW0
      hB₀ hB₁ hH h₀ h₁ hlog x y).trans (mul_le_mul_of_nonneg_right hL₀ dist_nonneg)
  · let v : Fin 3 → ℝ := Pi.single i 1
    have hv : ‖v‖ = 1 := by simp [v,Pi.norm_single]
    have hd := (hu.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ (∞ : ℕ∞ω) by simp)).differentiable (by simp)
    have hfv : Differentiable ℝ (fun z => fderiv ℝ u z v) :=
      (ContinuousLinearMap.apply ℝ ℝ v).differentiable.comp hd
    have hv₀ (z) : ‖fderiv ℝ u z v‖ ≤ B₁*W z := by
      exact ((fderiv ℝ u z).le_opNorm v).trans (by simpa [hv] using h₁ z)
    have hv₁ (z) : ‖fderiv ℝ (fun z => fderiv ℝ u z v) z‖ ≤ B₂*W z :=
      (norm_fderiv_evaluation (hd z) v).trans (by simpa [hv] using h₂ z)
    have hh := normalized_scalar_lipschitz hfv hW hW0 hB₁ hB₂ hH hv₀ hv₁ hlog x y
    change ‖n⁻¹*(W x)⁻¹*fderiv ℝ u x v-n⁻¹*(W y)⁻¹*fderiv ℝ u y v‖ ≤ _
    rw [mul_assoc,mul_assoc,←mul_sub,norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
    exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hn.le)).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hL₁ (dist_nonneg : 0 ≤ dist x y))
end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma normalized_scalar_lipschitz_on {f W : E → ℝ} {S : Set E} (hS : Convex ℝ S)
    (hf : Differentiable ℝ f) (hW : Differentiable ℝ W) (hW0 : ∀ x, 0 < W x)
    {B₀ B₁ H : ℝ} (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hH : 0 ≤ H)
    (h₀ : ∀ x ∈ S, ‖f x‖ ≤ B₀*W x) (h₁ : ∀ x ∈ S, ‖fderiv ℝ f x‖ ≤ B₁*W x)
    (hlog : ∀ x ∈ S, ‖fderiv ℝ W x‖ ≤ H*W x) (x y : E) (hx : x ∈ S) (hy : y ∈ S) :
    ‖(W x)⁻¹*f x-(W y)⁻¹*f y‖ ≤ (B₁+B₀*H)*dist x y := by
  have hb (z : E) (hz : z ∈ S) := normalized_scalar_derivative_bound (hf z) (hW z) (hW0 z)
    hB₀ hB₁ hH (h₀ z hz) (h₁ z hz) (hlog z hz)
  simpa only [dist_eq_norm] using
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hb z hz).1)
      (fun z hz => (hb z hz).2) hS hy hx

theorem realWaveJet_lipschitz_of_relative_bounds_on
    {S : Set (Fin 3 → ℝ)} (hS : Convex ℝ S)
    {u W : (Fin 3 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u)
    (hW : Differentiable ℝ W) (hW0 : ∀ x, 0 < W x)
    {n B₀ B₁ B₂ H L : ℝ} (hn : 0 < n)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hH : 0 ≤ H)
    (h₀ : ∀ x ∈ S, ‖u x‖ ≤ B₀*W x)
    (h₁ : ∀ x ∈ S, ‖fderiv ℝ u x‖ ≤ B₁*W x)
    (h₂ : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B₂*W x)
    (hlog : ∀ x ∈ S, ‖fderiv ℝ W x‖ ≤ H*W x)
    (hL₀ : B₁+B₀*H ≤ L) (hL₁ : n⁻¹*(B₂+B₁*H) ≤ L) (x y : Fin 3 → ℝ) (hx : x ∈ S) (hy : y ∈ S) :
    ‖realWaveJet n (W x) u x-realWaveJet n (W y) u y‖ ≤ L*dist x y := by
  have hL : 0 ≤ L := (by positivity : 0 ≤ B₁+B₀*H).trans hL₀
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hL dist_nonneg)).mpr
  intro i
  rcases i with i|i
  · exact (normalized_scalar_lipschitz_on hS (hu.differentiable (by simp)) hW hW0
      hB₀ hB₁ hH h₀ h₁ hlog x y hx hy).trans (mul_le_mul_of_nonneg_right hL₀ dist_nonneg)
  · let v : Fin 3 → ℝ := Pi.single i 1
    have hv : ‖v‖ = 1 := by simp [v,Pi.norm_single]
    have hd := (hu.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ (∞ : ℕ∞ω) by simp)).differentiable (by simp)
    have hfv : Differentiable ℝ (fun z => fderiv ℝ u z v) :=
      (ContinuousLinearMap.apply ℝ ℝ v).differentiable.comp hd
    have hv₀ (z) (hz : z ∈ S) : ‖fderiv ℝ u z v‖ ≤ B₁*W z := by
      exact ((fderiv ℝ u z).le_opNorm v).trans (by simpa [hv] using h₁ z hz)
    have hv₁ (z) (hz : z ∈ S) : ‖fderiv ℝ (fun z => fderiv ℝ u z v) z‖ ≤ B₂*W z :=
      (norm_fderiv_evaluation (hd z) v).trans (by simpa [hv] using h₂ z hz)
    have hh := normalized_scalar_lipschitz_on hS hfv hW hW0 hB₁ hB₂ hH hv₀ hv₁ hlog x y hx hy
    change ‖n⁻¹*(W x)⁻¹*fderiv ℝ u x v-n⁻¹*(W y)⁻¹*fderiv ℝ u y v‖ ≤ _
    rw [mul_assoc,mul_assoc,←mul_sub,norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
    exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hn.le)).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hL₁ (dist_nonneg : 0 ≤ dist x y))
end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set
open scoped ContDiff

lemma norm_iteratedFDeriv_comp_linear {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] F) {u : F → G} (hu : ContDiff ℝ ∞ u) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (u ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ j u (L x)‖*‖L‖^j := by
  rw [L.iteratedFDeriv_comp_right hu x (show (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) from
    le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ j u (L x)) (fun _ : Fin j => L)

lemma physical_packet_low_derivative {u : NormalWaveSpace → ℂ}
    (hu : ContDiff ℝ ∞ u) {T n W : ℝ} (hn : 0 ≤ n) (hT : 0 ≤ T) (hW : 0 ≤ W)
    {j : ℕ} (hj : j ≤ 2) (x : Fin 3 → ℝ)
    (hbound : ‖iteratedFDeriv ℝ j u (normalWaveEquiv x)‖ ≤ T*n^j*W) :
    ‖iteratedFDeriv ℝ j (u ∘ normalWaveEquiv) x‖ ≤
      (T*(max 1 ‖normalWaveEquiv.toContinuousLinearMap‖)^2)*n^j*W := by
  have hp : ‖normalWaveEquiv.toContinuousLinearMap‖^j ≤
      (max 1 ‖normalWaveEquiv.toContinuousLinearMap‖)^2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hj)
  exact (norm_iteratedFDeriv_comp_linear normalWaveEquiv.toContinuousLinearMap hu j x).trans
    ((mul_le_mul hbound hp (pow_nonneg (norm_nonneg _) _) (by positivity)).trans_eq (by ring))

theorem finiteWaveSuperposition_relative_derivative {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    {w : E → ℝ} {U : I → Fin 3 → E → ℂ}
    (hw : ContDiff ℝ ∞ w) (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (γ : I → Fin 3 → ℂ) {n Q T T₀ W : ℝ}
    (hn : 1 ≤ n) (hT : 0 ≤ T) (hT₀ : 0 ≤ T₀) (hW : 0 ≤ W)
    (hcard : (Fintype.card I : ℝ) ≤ Q*n^3) (hγ : ∀ i ℓ, ‖γ i ℓ‖ ≤ n)
    (j : ℕ) (x : E)
    (hwbound : ‖iteratedFDeriv ℝ j w x‖ ≤ T₀*n^j*W)
    (hbound : ∀ i ℓ, ‖iteratedFDeriv ℝ j (U i ℓ) x‖ ≤ T*n^j*W) :
    ‖iteratedFDeriv ℝ j (finiteWaveSuperposition w U γ) x‖ ≤
      (T₀+3*Q*T)*n^(j+4)*W := by
  classical
  have hs : ContDiff ℝ ∞ (fun y => ∑ i, ∑ ℓ, (γ i ℓ*U i ℓ y).re) :=
    ContDiff.sum (fun i _ => ContDiff.sum (fun ℓ _ =>
      Complex.reCLM.contDiff.comp (contDiff_const.mul (hU i ℓ))))
  have hle : (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
  unfold finiteWaveSuperposition
  rw [fun_iteratedFDeriv_add_apply (hw.of_le hle).contDiffAt (hs.of_le hle).contDiffAt]
  apply (norm_add_le _ _).trans
  have hsum := finiteWaveSum_derivative_bound hU γ (zero_le_one.trans hn) hT hW hcard hγ j x hbound
  have hp : n^j ≤ n^(j+4) := pow_le_pow_right₀ hn (by omega)
  calc
    _ ≤ T₀*n^j*W+(3*Q*T)*n^(j+4)*W := add_le_add hwbound hsum
    _ ≤ T₀*n^(j+4)*W+(3*Q*T)*n^(j+4)*W := by gcongr
    _ = _ := by ring

theorem finiteWaveSuperposition_normalized_lipschitz {I : Type*} [Fintype I]
    {S : Set (Fin 3 → ℝ)} (hS : Convex ℝ S)
    {w W : (Fin 3 → ℝ) → ℝ} {U : I → Fin 3 → (Fin 3 → ℝ) → ℂ}
    (hw : ContDiff ℝ ∞ w) (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (hW : Differentiable ℝ W) (hW0 : ∀ x, 0 < W x)
    (γ : I → Fin 3 → ℂ) {n Q T T₀ H : ℝ}
    (hn : 1 ≤ n) (hQ : 0 ≤ Q) (hT : 0 ≤ T) (hT₀ : 0 ≤ T₀) (hH : 0 ≤ H)
    (hcard : (Fintype.card I : ℝ) ≤ Q*n^3) (hγ : ∀ i ℓ, ‖γ i ℓ‖ ≤ n)
    (hwbound : ∀ x ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j w x‖ ≤ T₀*n^j*W x)
    (hbound : ∀ x ∈ S, ∀ j ≤ 2, ∀ i ℓ, ‖iteratedFDeriv ℝ j (U i ℓ) x‖ ≤ T*n^j*W x)
    (hlog : ∀ x ∈ S, ‖fderiv ℝ W x‖ ≤ H*n*W x)
    (x y : Fin 3 → ℝ) (hx : x ∈ S) (hy : y ∈ S) :
    ‖realWaveJet n (W x) (finiteWaveSuperposition w U γ) x-
      realWaveJet n (W y) (finiteWaveSuperposition w U γ) y‖ ≤
      ((T₀+3*Q*T)*(1+H)*n^6)*dist x y := by
  let A := T₀+3*Q*T
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hb (z) (hz : z ∈ S) (j) (hj : j ≤ 2) :
      ‖iteratedFDeriv ℝ j (finiteWaveSuperposition w U γ) z‖ ≤ A*n^(j+4)*W z :=
    finiteWaveSuperposition_relative_derivative hw hU γ hn hT hT₀ (hW0 z).le hcard hγ j z
      (hwbound z hz j hj) (hbound z hz j hj)
  apply realWaveJet_lipschitz_of_relative_bounds_on hS
    (contDiff_finiteWaveSuperposition hw hU γ) hW hW0 hn0
    (B₀ := A*n^4) (B₁ := A*n^5) (B₂ := A*n^6) (H := H*n)
    (by positivity) (by positivity) (by positivity) (by positivity)
    ?_ ?_ ?_ hlog ?_ ?_ x y hx hy
  · intro z hz
    simpa only [norm_iteratedFDeriv_zero,zero_add] using hb z hz 0 (by omega)
  · intro z hz
    simpa only [norm_iteratedFDeriv_one] using hb z hz 1 (by omega)
  · intro z hz
    have he : ‖fderiv ℝ (fderiv ℝ (finiteWaveSuperposition w U γ)) z‖ =
        ‖iteratedFDeriv ℝ 2 (finiteWaveSuperposition w U γ) z‖ := by
      rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
    rw [he]
    exact hb z hz 2 (by omega)
  · calc
      A*n^5+(A*n^4)*(H*n) = A*(1+H)*n^5 := by ring
      _ ≤ A*(1+H)*n^6 := by gcongr; norm_num
  · calc
      n⁻¹*(A*n^6+(A*n^5)*(H*n)) = A*(1+H)*n^5 := by field_simp
      _ ≤ A*(1+H)*n^6 := by gcongr; norm_num

end YauCounterexamples
end

end OAI
