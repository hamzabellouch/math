import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.FrozenCoefficient
import OAI.Geometry.TamingCompatibility.DifferentialForms.QuantitativeInterior

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private lemma norm_comp_three {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (a b c : V →L[ℂ] V) : ‖a ∘L b ∘L c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := by
  have h := (ContinuousLinearMap.opNorm_comp_le a (b ∘L c)).trans
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le b c) (norm_nonneg a))
  simpa only [mul_assoc] using h

lemma matrixLowerH_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ] (n : ℕ)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) :
    ‖matrixLowerH n b L v c K‖ ≤
      (∑ i, ‖product (F := F) n (b i)‖ * ‖fiberOperator (E := E) n (L i)‖ *
        ‖derivative (F := F) ((n:ℝ)+1) (v i)‖) +
      ∑ i, ‖product (F := F) n (c i)‖ * ‖fiberOperator (E := E) n (K i)‖ *
        ‖inclusion (E := E) (F := F) (s := (n:ℝ)+1) (t := (n:ℝ)) (by linarith : (n:ℝ) ≤ n+1)‖ := by
  apply (norm_add_le _ _).trans
  apply add_le_add <;> apply (norm_sum_le _ _).trans <;> apply Finset.sum_le_sum
  · intro i _
    exact norm_comp_three (product (F := F) n (b i)) (fiberOperator (E := E) n (L i))
      (derivative (F := F) ((n:ℝ)+1) (v i))
  · intro i _
    exact norm_comp_three (product (F := F) n (c i)) (fiberOperator (E := E) n (K i))
      (inclusion (E := E) (F := F) (s := (n:ℝ)+1) (t := (n:ℝ)) (by linarith : (n:ℝ) ≤ n+1))

lemma localizationErrorH_norm_le (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (g : 𝓢(E,ℂ)) :
    ‖localizationErrorH (F := F) n a g‖ ≤
      |((2*Real.pi)^2)⁻¹| * ∑ i, ‖secondCommutatorH (F := F) n g
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)‖ +
      ∑ i, ∑ j, ‖product (F := F) n (a i j)‖ * ‖secondCommutatorH (F := F) n g
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)‖ := by
  apply (norm_add_le _ _).trans
  apply add_le_add
  · have hs (A : H E F ((n:ℝ)+1) →L[ℂ] H E F n) (t : ℝ) : ‖t • A‖ ≤ |t| * ‖A‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg t) (norm_nonneg A))
      intro u
      change ‖t • A u‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (A.le_opNorm u) (abs_nonneg t)).trans_eq (by ring)
    apply (hs _ _).trans
    rw [abs_neg]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg _)
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    exact fun j _ => ContinuousLinearMap.opNorm_comp_le _ _

def scaledCoefficient (k : ℕ) (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p : E) (r : ℝ) : 𝓢(E,ℂ) :=
  (hχ.mul_right (f' := fun x => (r:ℂ)^k * f (p + r • x))).toSchwartzMap
    ((χ.smooth ⊤).mul (contDiff_const.mul
      (hf.comp (contDiff_const.add (contDiff_const.smul contDiff_id)))))

omit [MeasurableSpace E] [BorelSpace E] in
lemma scaledCoefficient_size_continuous (n k : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p : E) :
    Continuous (fun r => coefficientSize n (scaledCoefficient k χ hχ f hf p r)) := by
  apply coefficientSize_continuous_family n _ hχ
    (fun _ => tsupport_mul_subset_left)
  change ContDiff ℝ ∞ (fun q : ℝ × E =>
    χ q.2 * ((q.1:ℂ)^k * f (p + q.1 • q.2)))
  exact ((χ.smooth ⊤).comp contDiff_snd).mul
    (((Complex.ofRealCLM.contDiff.comp contDiff_fst).pow k).mul
      (hf.comp (contDiff_const.add (contDiff_fst.smul contDiff_snd))))

lemma matrixLowerH_eventually_bounded {ι κ : Type*} [Fintype ι] [Fintype κ] (n : ℕ)
    (b : ℝ → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : ℝ → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (hb : ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) 0)
    (hc : ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝 (0:ℝ), ‖matrixLowerH n (b r) L v (c r) K‖ ≤ C := by
  obtain ⟨A,hA,hprod⟩ := product_operator_estimate (E := E) (F := F) n
  let S : ℝ → ℝ := fun r =>
      (∑ i, (A * coefficientSize n (b r i)) * ‖fiberOperator (E := E) n (L i)‖ *
        ‖derivative (F := F) ((n:ℝ)+1) (v i)‖) +
      ∑ i, (A * coefficientSize n (c r i)) * ‖fiberOperator (E := E) n (K i)‖ *
        ‖inclusion (E := E) (F := F) (s := (n:ℝ)+1) (t := (n:ℝ)) (by linarith : (n:ℝ) ≤ n+1)‖
  have hS : ContinuousAt S 0 := by
    apply ContinuousAt.add <;> apply tendsto_finsetSum <;> intro i _
    · exact (((hb i).const_mul A).mul_const _).mul_const _
    · exact (((hc i).const_mul A).mul_const _).mul_const _
  have hbnd (r : ℝ) : ‖matrixLowerH n (b r) L v (c r) K‖ ≤ S r := by
    apply (matrixLowerH_norm_le n (b r) L v (c r) K).trans
    dsimp only [S]
    gcongr
    · exact hprod _
    · exact hprod _
  refine ⟨|S 0|+1, by positivity, ?_⟩
  have he : ∀ᶠ r in 𝓝 (0:ℝ), S r < |S 0|+1 :=
    hS.eventually (gt_mem_nhds (by linarith [le_abs_self (S 0)]))
  exact he.mono fun r hr => (hbnd r).trans hr.le

lemma localizationErrorH_eventually_bounded (n : ℕ)
    (a : ℝ → basisIndex E → basisIndex E → 𝓢(E,ℂ)) (g : 𝓢(E,ℂ))
    (ha : ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝 (0:ℝ), ‖localizationErrorH (F := F) n (a r) g‖ ≤ C := by
  obtain ⟨A,hA,hprod⟩ := product_operator_estimate (E := E) (F := F) n
  let S : ℝ → ℝ := fun r =>
      |((2*Real.pi)^2)⁻¹| * ∑ i, ‖secondCommutatorH (F := F) n g
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)‖ +
      ∑ i, ∑ j, (A * coefficientSize n (a r i j)) * ‖secondCommutatorH (F := F) n g
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)‖
  have hS : ContinuousAt S 0 := by
    apply ContinuousAt.add continuousAt_const
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact ((ha i j).const_mul A).mul_const _
  have hbnd (r : ℝ) : ‖localizationErrorH (F := F) n (a r) g‖ ≤ S r := by
    apply (localizationErrorH_norm_le n (a r) g).trans
    dsimp only [S]
    gcongr
    exact hprod _
  refine ⟨|S 0|+1, by positivity, ?_⟩
  have he : ∀ᶠ r in 𝓝 (0:ℝ), S r < |S 0|+1 :=
    hS.eventually (gt_mem_nhds (by linarith [le_abs_self (S 0)]))
  exact he.mono fun r hr => (hbnd r).trans hr.le
end TamingCompatibility.HilbertSobolev

end

end OAI
