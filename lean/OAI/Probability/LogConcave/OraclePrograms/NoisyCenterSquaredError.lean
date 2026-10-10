import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.TerminalMean
import OAI.Probability.LogConcave.Numerics.NormSubSqTwo

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.SeedCompiler
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators

variable {Ω A ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem noisy_center_squared_error (κ : Measure Ω) [SFinite κ]
    (μ : Measure A) [SFinite μ] (anchor : Ω → A) (noise center : Ω → E)
    (ha : Measurable anchor) (hz : Measurable noise) (hc : Measurable center)
    (hlaw : κ.map (fun w => (anchor w,noise w))=μ.prod (stdGaussian E))
    (x : A → E) (hx : Measurable x) {r D K S B : ℝ}
    (hD : 0<D) (hK : 0≤K) (v : ι → ℝ) (hv : (∑i,v i^2)≤D^2)
    (M : E → (ι → E) → E) (hm : Measurable (uncurry M))
    (hshift : ShiftInvariant r v M)
    (hLip : ∀x y g,‖M x g-M y g‖≤K*‖x-y‖)
    (Q : A × (ι → E) → E) (hQ : Measurable Q)
    (hci : Integrable (fun w => ‖center w-(x (anchor w)+(r/(2*D)) • noise w)‖^2) κ)
    (hce : (∫w,‖center w-(x (anchor w)+(r/(2*D)) • noise w)‖^2 ∂κ)≤S)
    (hbi : Integrable (fun z : A × (ι → E) => ‖M (x z.1) z.2-Q z‖^2)
      (μ.prod (Measure.pi fun _ : ι => stdGaussian E)))
    (hbe : (∫z : A × (ι → E),‖M (x z.1) z.2-Q z‖^2
      ∂μ.prod (Measure.pi fun _ : ι => stdGaussian E))≤B) :
    let a := fun i => v i/(2*D)
    let T := fun z : Ω × (ι → E) => (anchor z.1,restored (sqrtCoefficient a) a (z.2,noise z.1))
    Integrable (fun z : Ω × (ι → E) =>
      ‖M (center z.1) (slotTransform (sqrtCoefficient a) a z.2)-Q (T z)‖^2)
      (κ.prod (Measure.pi fun _ : ι => stdGaussian E)) ∧
    (∫z : Ω × (ι → E),‖M (center z.1) (slotTransform (sqrtCoefficient a) a z.2)-Q (T z)‖^2
      ∂κ.prod (Measure.pi fun _ : ι => stdGaussian E))≤2*K^2*S+2*B := by
  dsimp only
  let a : ι → ℝ := fun i => v i/(2*D)
  let γ : Measure (ι → E) := Measure.pi fun _ => stdGaussian E
  let T : Ω × (ι → E) → A × (ι → E) := fun z =>
    (anchor z.1,restored (sqrtCoefficient a) a (z.2,noise z.1))
  let C : Ω → ℝ := fun w => ‖center w-(x (anchor w)+(r/(2*D)) • noise w)‖^2
  let J : A × (ι → E) → ℝ := fun z => ‖M (x z.1) z.2-Q z‖^2
  let F : Ω × (ι → E) → ℝ := fun z =>
    ‖M (center z.1) (slotTransform (sqrtCoefficient a) a z.2)-Q (T z)‖^2
  have ha2 : (∑i,a i^2)≤1 := (normalized_shift_bound hD v hv).trans (by norm_num)
  have measurableError : Measurable J :=
    ((hm.comp ((hx.comp measurable_fst).prodMk measurable_snd)).sub hQ).norm.pow_const 2
  have hJ := restored_error_integral κ μ anchor noise ha hz hlaw a ha2 J
    ⟨measurableError.aestronglyMeasurable, hbi.hasFiniteIntegral⟩
  have hC : Integrable (fun z : Ω × (ι → E) => C z.1) (κ.prod γ) := hci.comp_fst γ
  have hJ' : Integrable (fun z => J (T z)) (κ.prod γ) := hJ.1
  have hdom : Integrable (fun z : Ω × (ι → E) => 2*K^2*C z.1+2*J (T z)) (κ.prod γ) :=
    (hC.const_mul _).add (hJ'.const_mul _)
  have hTm : Measurable T := (ha.comp measurable_fst).prodMk
    ((restored (sqrtCoefficient a) a).measurable.comp
      (measurable_snd.prodMk (hz.comp measurable_fst)))
  have hPm : Measurable (slotTransform (sqrtCoefficient a) a : (ι → E) → (ι → E)) := by
    unfold slotTransform slotSum
    fun_prop
  have hFm : Measurable F := by
    exact ((hm.comp ((hc.comp measurable_fst).prodMk (hPm.comp measurable_snd))).sub
      (hQ.comp hTm)).norm.pow_const 2
  have hb (z : Ω × (ι → E)) : F z≤2*K^2*C z.1+2*J (T z) := by
    let u := M (center z.1) (slotTransform (sqrtCoefficient a) a z.2)
    let w := M (x (anchor z.1)) (T z).2
    have hw : M (x (anchor z.1)+(r/(2*D)) • noise z.1)
        (slotTransform (sqrtCoefficient a) a z.2)=w :=
      absorption_pathwise v M hshift (x (anchor z.1)) _ z.2 (noise z.1)
    have hd : ‖u-w‖≤K*‖center z.1-(x (anchor z.1)+(r/(2*D)) • noise z.1)‖ := by
      rw [←hw]
      exact hLip _ _ _
    have hsq := (sq_le_sq₀ (norm_nonneg (u-w))
      (mul_nonneg hK (norm_nonneg _))).2 hd
    rw [mul_pow] at hsq
    have ht := RMSIntegral.norm_sub_sq_le_two (u-w) (Q (T z)-w)
    rw [show u-w-(Q (T z)-w)=u-Q (T z) from by abel,norm_sub_rev (Q (T z)) w] at ht
    change ‖u-Q (T z)‖^2≤2*K^2*C z.1+2*‖w-Q (T z)‖^2
    dsimp only [C] at *
    nlinarith
  have hi : Integrable F (κ.prod γ) := hdom.mono' hFm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by simpa only [F,Real.norm_eq_abs,abs_sq] using hb z))
  refine ⟨hi,(integral_mono hi hdom hb).trans ?_⟩
  rw [integral_add (hC.const_mul _) (hJ'.const_mul _),integral_const_mul,integral_const_mul]
  have hCeq : (∫z : Ω × (ι → E),C z.1 ∂κ.prod γ)=∫w,C w ∂κ := by
    rw [integral_prod _ hC]
    simp only [integral_const,probReal_univ,one_smul]
  rw [hCeq,hJ.2]
  exact add_le_add (mul_le_mul_of_nonneg_left hce (by positivity))
    (mul_le_mul_of_nonneg_left hbe (by norm_num))
end LogConcaveSampling.SeedCompiler

end

end

end

end OAI
