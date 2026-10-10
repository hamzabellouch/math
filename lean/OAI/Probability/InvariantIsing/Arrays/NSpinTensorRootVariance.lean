import OAI.Probability.InvariantIsing.Arrays.NSpinTensorCascade
import OAI.Probability.InvariantIsing.Core.FiniteGaussianVariance

namespace OAI

/-! The root Gaussian contribution for the finite spectral-tensor model. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal InnerProductSpace

namespace InvariantIsing

abbrev TensorGaussianSpace {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) :=
  EuclideanSpace ℝ (Fin (Fintype.card (SpinTensorIndex I degree)))

/-- Reindex independent standard Euclidean coordinates, then apply the
coordinate square roots of the prescribed root variances. -/
def tensorRootMark {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (root : SpinTensorIndex I degree → ℝ≥0)
    (g : TensorGaussianSpace I degree) : SpinTensorIndex I degree → ℝ :=
  fun i => (NNReal.sqrt (root i) : ℝ) * g (Fintype.equivFin (SpinTensorIndex I degree) i)

lemma measurable_tensorRootMark {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (root : SpinTensorIndex I degree → ℝ≥0) :
    Measurable (tensorRootMark I degree root) := by
  unfold tensorRootMark
  fun_prop

theorem tensorRootMark_measurePreserving {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (root : SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (tensorRootMark I degree root)
      (stdGaussian (TensorGaussianSpace I degree))
      (tensorGaussianLaw I degree root : Measure (SpinTensorIndex I degree → ℝ)) := by
  let J := SpinTensorIndex I degree
  let d := Fintype.card J
  have hto : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin d → ℝ))
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have hfrom := MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin d → ℝ)) hto
  have hindex := measurePreserving_piCongrLeft
    (α := fun _ : J => ℝ) (fun _ : J => gaussianReal 0 1) (Fintype.equivFin J).symm
  have hscale : MeasurePreserving (fun z : J → ℝ => fun i => (NNReal.sqrt (root i) : ℝ) * z i)
      (Measure.pi (fun _ : J => gaussianReal 0 1))
      (Measure.pi (fun i : J => gaussianReal 0 (root i))) := by
    apply measurePreserving_pi
    intro i
    refine ⟨by fun_prop, ?_⟩
    have hs : NNReal.mk ((NNReal.sqrt (root i) : ℝ) ^ 2) (sq_nonneg _) = root i := by
      apply Subtype.ext
      change (NNReal.sqrt (root i) : ℝ) ^ 2 = (root i : ℝ)
      exact_mod_cast NNReal.sq_sqrt (root i)
    simpa only [hs, mul_zero, mul_one] using
      gaussianReal_map_const_mul (μ := 0) (v := 1) (NNReal.sqrt (root i) : ℝ)
  convert hscale.comp (hindex.comp hfrom) using 1
  · ext g i
    simp [tensorRootMark, Function.comp_def, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft, J]
  · rfl

def tensorRootCoefficient {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (root : SpinTensorIndex I degree → ℝ≥0) (σ : Spin N) : TensorGaussianSpace I degree :=
  WithLp.toLp 2 (fun j =>
    (NNReal.sqrt (root ((Fintype.equivFin (SpinTensorIndex I degree)).symm j)) : ℝ) *
      spinTensorFeature U I degree amplitude σ ((Fintype.equivFin (SpinTensorIndex I degree)).symm j))

lemma spinTensorEnergy_tensorRootMark {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (root : SpinTensorIndex I degree → ℝ≥0) (σ : Spin N) (g : TensorGaussianSpace I degree) :
    spinTensorEnergy U I degree amplitude (tensorRootMark I degree root g) σ =
      ⟪tensorRootCoefficient U I degree amplitude root σ, g⟫_ℝ := by
  classical
  unfold spinTensorEnergy tensorRootMark tensorRootCoefficient
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply', conj_trivial]
  rw [← (Fintype.equivFin (SpinTensorIndex I degree)).symm.sum_comp
    (fun i => (NNReal.sqrt (root i) : ℝ) *
      g (Fintype.equivFin (SpinTensorIndex I degree) i) * spinTensorFeature U I degree amplitude σ i)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Equiv.apply_symm_apply]
  ring

lemma tensorRootCoefficient_norm_sq_le {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : ℝ≥0) (monomial : Fin k → ℝ≥0) (σ : Spin N) :
    ‖tensorRootCoefficient U I degree amplitude (tensorVarianceProfile I degree site monomial) σ‖ ^ 2 ≤
      (site : ℝ) * N + ∑ j, (monomial j : ℝ) * amplitude j ^ 2 := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ j, ((NNReal.sqrt (tensorVarianceProfile I degree site monomial
      ((Fintype.equivFin (SpinTensorIndex I degree)).symm j)) : ℝ) *
    spinTensorFeature U I degree amplitude σ ((Fintype.equivFin (SpinTensorIndex I degree)).symm j)) ^ 2) ≤ _
  have hs (i : SpinTensorIndex I degree) :
      (NNReal.sqrt (tensorVarianceProfile I degree site monomial i) : ℝ) ^ 2 =
        tensorVarianceProfile I degree site monomial i := by
    exact_mod_cast NNReal.sq_sqrt (tensorVarianceProfile I degree site monomial i)
  simp only [mul_pow, hs]
  rw [(Fintype.equivFin (SpinTensorIndex I degree)).symm.sum_comp
    (fun i => (tensorVarianceProfile I degree site monomial i : ℝ) *
      spinTensorFeature U I degree amplitude σ i ^ 2)]
  exact spinTensorFeature_variance_le U I degree amplitude site monomial σ

private theorem tensorCascade_shift_comparison {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (x y : SpinTensorIndex I degree → ℝ) {C : ℝ}
    (hxy : ∀ z, |spinTensorTerminal eig U c I degree amplitude (x + z) -
      spinTensorTerminal eig U c I degree amplitude (y + z)| ≤ C) :
    |tensorCascadeValue eig U c I degree amplitude n b v x -
      tensorCascadeValue eig U c I degree amplitude n b v y| ≤ C := by
  induction n generalizing b v x y with
  | zero => simpa only [tensorCascadeValue, IsingPerceptron.cascadeRecursion, add_zero] using hxy 0
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    let G := tensorCascadeValue eig U c I degree amplitude n bs vs
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    have hm : Measurable G := IsingPerceptron.measurable_cascadeRecursion n bs
      (fun i => tensorGaussianLaw I degree (vs i)) (fun _ => measurable_fst.add measurable_snd)
      (measurable_spinTensorTerminal eig U c I degree amplitude)
    have hg : IsingPerceptron.HasLinearGrowth G :=
      IsingPerceptron.cascadeRecursion_linearGrowth n bs (fun i => tensorGaussianLaw I degree (vs i))
        (fun i _ => tensorGaussianLaw_moments hN I degree (vs i))
        (measurable_spinTensorTerminal eig U c I degree amplitude)
        (spinTensorTerminal_linearGrowth eig U c I degree amplitude) hbs
    have hi (z : SpinTensorIndex I degree → ℝ) : Integrable (fun a => Real.exp (b 0 * G (z + a)))
        (tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)) :=
      IsingPerceptron.integrable_exp_of_linearGrowth _ (tensorGaussianLaw_moments hN I degree (v 0))
        (hm.comp (measurable_const.add measurable_id)) (hg.add_left z) (b 0)
    apply IsingPerceptron.logMean_abs_sub_le _ (hb 0 (by omega)) (hi x) (hi y)
    intro a
    exact ih bs vs hbs (x + a) (y + a) (fun z => by simpa only [add_assoc] using hxy (a + z))

lemma spinTensorEnergy_add {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (x y : SpinTensorIndex I degree → ℝ) (σ : Spin N) :
    spinTensorEnergy U I degree amplitude (x + y) σ =
      spinTensorEnergy U I degree amplitude x σ + spinTensorEnergy U I degree amplitude y σ := by
  simp only [spinTensorEnergy, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The actual backward cascade recursion remains Lipschitz in the common
root Gaussian mark, with the Euclidean coefficient bound of the model. -/
theorem tensorCascadeValue_root_lipschitz {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (site : ℝ≥0) (monomial : Fin k → ℝ≥0)
    (z : SpinTensorIndex I degree → ℝ) :
    let B : ℝ≥0 := ⟨(site : ℝ) * N + ∑ j, (monomial j : ℝ) * amplitude j ^ 2,
      add_nonneg (mul_nonneg (NNReal.coe_nonneg _) (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun _j _ => mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _))⟩
    LipschitzWith (NNReal.sqrt B)
      (fun g => tensorCascadeValue eig U c I degree amplitude n b v
        (z + tensorRootMark I degree (tensorVarianceProfile I degree site monomial) g)) := by
  intro B
  have hs : ((NNReal.sqrt B : ℝ≥0) : ℝ) ^ 2 = B := by exact_mod_cast NNReal.sq_sqrt B
  have hn (σ : Spin N) :
      ‖tensorRootCoefficient U I degree amplitude (tensorVarianceProfile I degree site monomial) σ‖ ≤
        (NNReal.sqrt B : ℝ) := by
    have hcap := tensorRootCoefficient_norm_sq_le U I degree amplitude site monomial σ
    change ‖tensorRootCoefficient U I degree amplitude (tensorVarianceProfile I degree site monomial) σ‖ ^ 2 ≤ (B : ℝ) at hcap
    nlinarith [norm_nonneg (tensorRootCoefficient U I degree amplitude (tensorVarianceProfile I degree site monomial) σ),
      NNReal.coe_nonneg (NNReal.sqrt B)]
  apply LipschitzWith.of_dist_le_mul
  intro g h
  simp only [dist_eq_norm]
  apply tensorCascade_shift_comparison hN eig U c I degree amplitude n b v
    (fun i hi => (hb.1 i hi).1)
  intro a
  apply abs_logPartition_sub_le
  intro σ
  have he : (rotatedEnergy eig U σ + fieldEnergy c σ +
      spinTensorEnergy U I degree amplitude ((z + tensorRootMark I degree
        (tensorVarianceProfile I degree site monomial) g) + a) σ) -
      (rotatedEnergy eig U σ + fieldEnergy c σ +
      spinTensorEnergy U I degree amplitude ((z + tensorRootMark I degree
        (tensorVarianceProfile I degree site monomial) h) + a) σ) =
      ⟪tensorRootCoefficient U I degree amplitude (tensorVarianceProfile I degree site monomial) σ, g - h⟫_ℝ := by
    rw [spinTensorEnergy_add, spinTensorEnergy_add, spinTensorEnergy_add, spinTensorEnergy_add,
      spinTensorEnergy_tensorRootMark, spinTensorEnergy_tensorRootMark, inner_sub_right]
    ring
  rw [he]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hn σ) (norm_nonneg _))

/-- Root Gaussian variance of the existing tensor recursion. This is
conditional only on the explicitly cited finite Gaussian Poincaré input. -/
theorem tensorCascadeValue_root_variance_le (hpub : GaussianLipschitzVarianceInput)
    {N m k : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) :
    variance (tensorCascadeValue eig U c I degree amplitude n b v)
      (tensorGaussianLaw I degree (tensorVarianceProfile I degree site monomial) :
        Measure (SpinTensorIndex I degree → ℝ)) ≤
      (site : ℝ) * N + ∑ j, (monomial j : ℝ) * amplitude j ^ 2 := by
  let B : ℝ≥0 := ⟨(site : ℝ) * N + ∑ j, (monomial j : ℝ) * amplitude j ^ 2,
    add_nonneg (mul_nonneg (NNReal.coe_nonneg _) (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun j _ => mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _))⟩
  have hLip := tensorCascadeValue_root_lipschitz hN eig U c I degree amplitude n b v hb site monomial 0
  simp only [zero_add] at hLip
  have hm : Measurable (tensorCascadeValue eig U c I degree amplitude n b v) :=
    IsingPerceptron.measurable_cascadeRecursion n b (fun i => tensorGaussianLaw I degree (v i))
      (fun _ => measurable_fst.add measurable_snd) (measurable_spinTensorTerminal eig U c I degree amplitude)
  have hv := hpub (Fintype.card (SpinTensorIndex I degree)) (NNReal.sqrt B) _ hLip
  rw [(tensorRootMark_measurePreserving I degree (tensorVarianceProfile I degree site monomial)).variance_fun_comp
    hm.aemeasurable] at hv
  have hs : ((NNReal.sqrt B : ℝ≥0) : ℝ) ^ 2 = B := by exact_mod_cast NNReal.sq_sqrt B
  exact hv.trans_eq hs

theorem normalized_tensorCascadeValue_root_variance_le (hpub : GaussianLipschitzVarianceInput)
    {N m k : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) :
    variance (fun z => (N : ℝ)⁻¹ * tensorCascadeValue eig U c I degree amplitude n b v z)
      (tensorGaussianLaw I degree (tensorVarianceProfile I degree site monomial) :
        Measure (SpinTensorIndex I degree → ℝ)) ≤
      ((site : ℝ) * N + ∑ j, (monomial j : ℝ) * amplitude j ^ 2) / (N : ℝ) ^ 2 := by
  rw [variance_const_mul]
  have hv := tensorCascadeValue_root_variance_le hpub hN eig U c I degree amplitude n b v hb site monomial
  have he : (N : ℝ)⁻¹ ^ 2 * ((site : ℝ) * N + ∑ j, (monomial j : ℝ) * amplitude j ^ 2) =
      ((site : ℝ) * N + ∑ j, (monomial j : ℝ) * amplitude j ^ 2) / (N : ℝ) ^ 2 := by
    ring
  exact (mul_le_mul_of_nonneg_left hv (sq_nonneg _)).trans_eq he

end InvariantIsing

end

end OAI
