import Mathlib
import OAI.Probability.SKValue.GroundState.StandardGaussian

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma gaussian_gibbs_derivative_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (c d : ι → Fin n → ℝ)
    (h : ∀ i j, 0 ≤ ∑ k, (d i k-d j k)*(c i k-c j k)) :
    0 ≤ ∫ z, ∑ i, gibbsWeight (linearProcess c z) i*linearProcess d z i ∂gaussianProduct (Fin n) := by
  have hi : ∀ i, Integrable (fun z ↦ gibbsWeight (linearProcess c z) i*linearProcess d z i)
      (gaussianProduct (Fin n)) := fun i ↦ gibbsWeight_mul_integrable c i (linearProcess_integrable d i)
  have hi' : ∀ i, Integrable (fun z ↦ gibbsWeight (linearProcess c z) i *
      ((∑ k, d i k*c i k)-∑ j, gibbsWeight (linearProcess c z) j*(∑ k, d i k*c j k)))
      (gaussianProduct (Fin n)) := by
    intro i
    apply gibbsWeight_mul_integrable
    exact (integrable_const _).sub (integrable_finsetSum _ (fun j _ ↦ (integrable_linear_gibbsWeight c j).mul_const _))
  rw [integral_finsetSum _ (fun i _ ↦ hi i)]
  simp_rw [gaussian_linear_gibbsWeight]
  rw [← integral_finsetSum _ (fun i _ ↦ hi' i)]
  apply integral_nonneg
  intro z
  change (0 : ℝ) ≤ ∑ i, gibbsWeight (linearProcess c z) i *
    ((∑ k, d i k*c i k)-∑ j, gibbsWeight (linearProcess c z) j*(∑ k, d i k*c j k))
  rw [weighted_covariance_pairs _ (fun i j ↦ ∑ k, d i k*c j k) (sum_gibbsWeight (linearProcess c z))]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (mul_nonneg (gibbsWeight_nonneg _ _) (gibbsWeight_nonneg _ _))
  have he : (∑ k, d i k*c i k)+(∑ k, d j k*c j k)-
      (∑ k, d i k*c j k)-(∑ k, d j k*c i k) = ∑ k, (d i k-d j k)*(c i k-c j k) := by
    rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  exact h i j

noncomputable def rotatedCoefficients {ι κ : Type*} (a b : ι → κ → ℝ) (t : ℝ) (i : ι) (k : κ) : ℝ :=
  Real.cos t*a i k + Real.sin t*b i k

noncomputable def rotationVelocity {ι κ : Type*} (a b : ι → κ → ℝ) (t : ℝ) (i : ι) (k : κ) : ℝ :=
  -Real.sin t*a i k + Real.cos t*b i k

lemma hasDerivAt_rotatedProcess {ι κ : Type*} [Fintype κ] (a b : ι → κ → ℝ)
    (t : ℝ) (z : κ → ℝ) (i : ι) :
    HasDerivAt (fun s ↦ linearProcess (rotatedCoefficients a b s) z i)
      (linearProcess (rotationVelocity a b t) z i) t := by
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦
    (((Real.hasDerivAt_cos t).mul_const (a i k)).add ((Real.hasDerivAt_sin t).mul_const (b i k))).mul_const (z k))

lemma abs_rotationVelocity_le {ι κ : Type*} (a b : ι → κ → ℝ) (t : ℝ) (i : ι) (k : κ) :
    |rotationVelocity a b t i k| ≤ |a i k|+|b i k| := by
  calc
    _ ≤ |-Real.sin t*a i k| + |Real.cos t*b i k| := abs_add_le _ _
    _ = |Real.sin t| *|a i k| + |Real.cos t| *|b i k| := by rw [abs_mul,abs_neg,abs_mul]
    _ ≤ 1*|a i k| + 1*|b i k| := add_le_add
      (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (abs_nonneg _))
      (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one t) (abs_nonneg _))
    _ = _ := by ring

lemma rotation_derivative_bound {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (a b : ι → κ → ℝ) (t : ℝ) (z : κ → ℝ) :
    |∑ i, gibbsWeight (linearProcess (rotatedCoefficients a b t) z) i *
        linearProcess (rotationVelocity a b t) z i| ≤
      ∑ i, ∑ k, (|a i k|+|b i k|)*|z k| := by
  apply abs_gibbsMean_le
  intro i
  calc
    _ ≤ ∑ k, |rotationVelocity a b t i k*z k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (|a i k|+|b i k|)*|z k| := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_rotationVelocity_le _ _ _ _ _) (abs_nonneg _)
    _ ≤ _ := Finset.single_le_sum (f := fun j ↦ ∑ k, (|a j k|+|b j k|)*|z k|) (fun j _ ↦ Finset.sum_nonneg (fun k _ ↦ mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))) (Finset.mem_univ i)

lemma hasDerivAt_expected_rotated_logPartition {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (a b : ι → Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ ∫ z, logPartition (linearProcess (rotatedCoefficients a b s) z) ∂gaussianProduct (Fin n))
      (∫ z, ∑ i, gibbsWeight (linearProcess (rotatedCoefficients a b t) z) i *
        linearProcess (rotationVelocity a b t) z i ∂gaussianProduct (Fin n)) t := by
  have hb : Integrable (fun z : Fin n → ℝ ↦ ∑ i, ∑ k, (|a i k|+|b i k|)*|z k|)
      (gaussianProduct (Fin n)) :=
    integrable_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun k _ ↦
      (gaussian_coordinate_integrable k).abs.const_mul _))
  have hmc : Continuous (fun z : Fin n → ℝ ↦ ∑ i,
      gibbsWeight (linearProcess (rotatedCoefficients a b t) z) i *
      linearProcess (rotationVelocity a b t) z i) := by
    apply continuous_finsetSum
    intro i _
    apply (continuous_linear_gibbsWeight _ _).mul
    exact (continuous_apply i).comp (continuous_linearProcess _)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ) (μ := gaussianProduct (Fin n))
    (F := fun s z ↦ logPartition (linearProcess (rotatedCoefficients a b s) z))
    (F' := fun s z ↦ ∑ i, gibbsWeight (linearProcess (rotatedCoefficients a b s) z) i *
      linearProcess (rotationVelocity a b s) z i)
    (bound := fun z ↦ ∑ i, ∑ k, (|a i k|+|b i k|)*|z k|)
    (Filter.univ_mem)
    (Eventually.of_forall (fun s ↦ (continuous_logPartition.comp (continuous_linearProcess _)).aestronglyMeasurable))
    (logPartition_integrable _) hmc.aestronglyMeasurable
    (Eventually.of_forall (fun z s _ ↦ by simpa only [Real.norm_eq_abs] using rotation_derivative_bound a b s z)) hb
    (Eventually.of_forall (fun z s _ ↦ hasDerivAt_logPartition (hasDerivAt_rotatedProcess a b s z)))).2

lemma rotation_pair_covariance {ι κ : Type*} [Fintype κ] (a b : ι → κ → ℝ) (t : ℝ) (i j : ι) :
    (∑ k, (rotationVelocity a b t i k-rotationVelocity a b t j k)*
      (rotatedCoefficients a b t i k-rotatedCoefficients a b t j k)) =
    Real.sin t*Real.cos t*((∑ k, (b i k-b j k)^2)-(∑ k, (a i k-a j k)^2)) +
      ((Real.cos t)^2-(Real.sin t)^2)*∑ k, (a i k-a j k)*(b i k-b j k) := by
  simp only [rotationVelocity,rotatedCoefficients,← Finset.sum_sub_distrib,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma expected_logPartition_le_of_pair_distances {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (a b : ι → Fin n → ℝ)
    (horth : ∀ i j, (∑ k, (a i k-a j k)*(b i k-b j k)) = 0)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, logPartition (linearProcess a z) ∂gaussianProduct (Fin n)) ≤
    ∫ z, logPartition (linearProcess b z) ∂gaussianProduct (Fin n) := by
  let F := fun t ↦ ∫ z, logPartition (linearProcess (rotatedCoefficients a b t) z) ∂gaussianProduct (Fin n)
  have hd : ∀ t, HasDerivAt F (∫ z, ∑ i, gibbsWeight (linearProcess (rotatedCoefficients a b t) z) i *
      linearProcess (rotationVelocity a b t) z i ∂gaussianProduct (Fin n)) t :=
    hasDerivAt_expected_rotated_logPartition a b
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun t ↦ (hd t).continuousAt)
  have hm : MonotoneOn F (Icc (0 : ℝ) (Real.pi/2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hc.continuousOn
      (fun t _ ↦ (hd t).differentiableAt.differentiableWithinAt)
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) (Real.pi/2) := interior_subset ht
    rw [(hd t).deriv]
    apply gaussian_gibbs_derivative_nonneg
    intro i j
    rw [rotation_pair_covariance,horth,mul_zero,add_zero]
    exact mul_nonneg (mul_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi ht'.1 (ht'.2.trans (by linarith [Real.pi_pos])))
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, ht'.1],ht'.2⟩)) (sub_nonneg.mpr (hdist i j))
  have hπ : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have hh := hm ⟨le_rfl,hπ⟩ ⟨hπ,le_rfl⟩ hπ
  have ha0 : rotatedCoefficients a b 0 = a := by funext i k; simp [rotatedCoefficients]
  have hb0 : rotatedCoefficients a b (Real.pi/2) = b := by funext i k; simp [rotatedCoefficients]
  simpa only [F,ha0,hb0] using hh

noncomputable def finiteMaximum {ι : Type*} (x : ι → ℝ) : ℝ := sSup (Set.range x)

lemma le_finiteMaximum {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) : x i ≤ finiteMaximum x :=
  le_csSup (Set.finite_range x).bddAbove (Set.mem_range_self i)

lemma exists_finiteMaximum {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    ∃ i, x i = finiteMaximum x := (Set.range_nonempty x).csSup_mem (Set.finite_range x)

lemma continuous_finiteMaximum {ι : Type*} [Fintype ι] [Nonempty ι] :
    Continuous (@finiteMaximum ι) := by
  have he (x : ι → ℝ) : finiteMaximum x = Finset.univ.sup' Finset.univ_nonempty x := by
    rw [Finset.sup'_eq_csSup_image]
    simp only [Finset.coe_univ,Set.image_univ,finiteMaximum]
  simp_rw [funext he]
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ ↦ continuous_apply i)

lemma abs_finiteMaximum_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    |finiteMaximum x| ≤ ∑ i, |x i| := by
  obtain ⟨i,hi⟩ := exists_finiteMaximum x
  rw [← hi]
  exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (x j)) (Finset.mem_univ i)

lemma finiteMaximum_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) : Integrable (fun z ↦ finiteMaximum (linearProcess c z)) (gaussianProduct κ) := by
  apply (integrable_finsetSum Finset.univ (fun i _ ↦ (linearProcess_integrable c i).abs)).mono'
    ((continuous_finiteMaximum.comp (continuous_linearProcess c)).aestronglyMeasurable)
  exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs,Function.comp_def] using abs_finiteMaximum_le (linearProcess c z))

lemma scaled_max_le_logPartition {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ)
    (β : ℝ) : β*finiteMaximum x ≤ logPartition (fun i ↦ β*x i) := by
  obtain ⟨i,hi⟩ := exists_finiteMaximum x
  rw [← hi]
  exact le_logPartition (fun i ↦ β*x i) i

lemma logPartition_le_scaled_max {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ)
    {β : ℝ} (hβ : 0 ≤ β) : logPartition (fun i ↦ β*x i) ≤ β*finiteMaximum x+Real.log (Fintype.card ι) := by
  exact (logPartition_le _ (fun i ↦ mul_le_mul_of_nonneg_left (le_finiteMaximum x i) hβ)).trans_eq (add_comm _ _)

lemma linearProcess_scaled {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) (β : ℝ) (z : κ → ℝ) :
    linearProcess (fun i k ↦ β*c i k) z = fun i ↦ β*linearProcess c z i := by
  funext i
  simp only [linearProcess,Finset.mul_sum,mul_assoc]

lemma expected_max_le_of_pair_distances_orthogonal {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (a b : ι → Fin n → ℝ)
    (horth : ∀ i j, (∑ k, (a i k-a j k)*(b i k-b j k)) = 0)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct (Fin n)) ≤
    ∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct (Fin n) := by
  have hb (β : ℝ) (hβ : 0 ≤ β) :
      β*(∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct (Fin n)) ≤
      β*(∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct (Fin n)) + Real.log (Fintype.card ι) := by
    have hiA := logPartition_integrable (fun i k ↦ β*a i k)
    have hiB := logPartition_integrable (fun i k ↦ β*b i k)
    have hcomp := expected_logPartition_le_of_pair_distances
      (fun i k ↦ β*a i k) (fun i k ↦ β*b i k)
      (fun i j ↦ by
        calc
          (∑ k, (β*a i k-β*a j k)*(β*b i k-β*b j k)) =
              β^2*(∑ k, (a i k-a j k)*(b i k-b j k)) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
          _ = 0 := by rw [horth,mul_zero])
      (fun i j ↦ by
        have he (c : ι → Fin n → ℝ) : (∑ k, (β*c i k-β*c j k)^2) = β^2*∑ k, (c i k-c j k)^2 := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
        rw [he,he]
        exact mul_le_mul_of_nonneg_left (hdist i j) (sq_nonneg β))
    calc
      _ = ∫ z, β*finiteMaximum (linearProcess a z) ∂gaussianProduct (Fin n) := by rw [integral_const_mul]
      _ ≤ ∫ z, logPartition (linearProcess (fun i k ↦ β*a i k) z) ∂gaussianProduct (Fin n) := by
        apply integral_mono ((finiteMaximum_integrable a).const_mul _) hiA
        intro z
        change β*finiteMaximum (linearProcess a z) ≤ logPartition (linearProcess (fun i k ↦ β*a i k) z)
        rw [linearProcess_scaled]
        exact scaled_max_le_logPartition _ _
      _ ≤ _ := hcomp
      _ ≤ ∫ z, β*finiteMaximum (linearProcess b z)+Real.log (Fintype.card ι) ∂gaussianProduct (Fin n) := by
        apply integral_mono hiB (((finiteMaximum_integrable b).const_mul _).add (integrable_const _))
        intro z
        change logPartition (linearProcess (fun i k ↦ β*b i k) z) ≤ β*finiteMaximum (linearProcess b z)+Real.log (Fintype.card ι)
        rw [linearProcess_scaled]
        exact logPartition_le_scaled_max _ hβ
      _ = _ := by rw [integral_add ((finiteMaximum_integrable b).const_mul _) (integrable_const _),integral_const_mul,integral_const]; simp
  by_contra hh
  have hΔ : 0 < (∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct (Fin n)) -
      (∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct (Fin n)) := sub_pos.mpr (lt_of_not_ge hh)
  let Δ := (∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct (Fin n)) -
      (∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct (Fin n))
  let β := (|Real.log (Fintype.card ι)|+1)/Δ
  have hβ : 0 < β := div_pos (by positivity) hΔ
  have hh' := hb β hβ.le
  have he : β*Δ = |Real.log (Fintype.card ι)|+1 := div_mul_cancel₀ _ hΔ.ne'
  have hlog := le_abs_self (Real.log (Fintype.card ι))
  dsimp [Δ] at he
  nlinarith

lemma gaussian_integral_reindex {κ ν : Type*} [Fintype κ] [Fintype ν] (e : κ ≃ ν)
    (f : (κ → ℝ) → ℝ) :
    (∫ z : ν → ℝ, f (fun k ↦ z (e k)) ∂gaussianProduct ν) = ∫ z, f z ∂gaussianProduct κ := by
  have he := measurePreserving_piCongrLeft (α := fun _ : κ ↦ ℝ)
    (fun _ : κ ↦ standardGaussian) e.symm
  have hf (z : ν → ℝ) : (MeasurableEquiv.piCongrLeft (π := fun _ : κ ↦ ℝ) e.symm) z = fun k ↦ z (e k) := by
    funext k
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  simpa only [gaussianProduct,hf] using he.integral_comp' f

lemma linearProcess_reindex {ι κ ν : Type*} [Fintype κ] [Fintype ν]
    (c : ι → κ → ℝ) (e : κ ≃ ν) (z : ν → ℝ) :
    linearProcess c (fun k ↦ z (e k)) = linearProcess (fun i l ↦ c i (e.symm l)) z := by
  funext i
  simpa only [linearProcess, Equiv.symm_apply_apply] using e.sum_comp (fun l ↦ c i (e.symm l)*z l)

lemma expected_max_reindex {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (c : ι → κ → ℝ) (e : κ ≃ ν) :
    (∫ z, finiteMaximum (linearProcess (fun i l ↦ c i (e.symm l)) z) ∂gaussianProduct ν) =
    ∫ z, finiteMaximum (linearProcess c z) ∂gaussianProduct κ := by
  simpa only [linearProcess_reindex] using gaussian_integral_reindex e (fun z ↦ finiteMaximum (linearProcess c z))

lemma expected_max_le_of_pair_distances_orthogonal_fintype {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ι → κ → ℝ)
    (horth : ∀ i j, (∑ k, (a i k-a j k)*(b i k-b j k)) = 0)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct κ) ≤
    ∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct κ := by
  let e := Fintype.equivFin κ
  have hh := expected_max_le_of_pair_distances_orthogonal
    (fun i k ↦ a i (e.symm k)) (fun i k ↦ b i (e.symm k))
    (fun i j ↦ by
      rw [e.symm.sum_comp (fun k ↦ (a i k-a j k)*(b i k-b j k))]
      exact horth i j)
    (fun i j ↦ by
      rw [e.symm.sum_comp (fun k ↦ (a i k-a j k)^2), e.symm.sum_comp (fun k ↦ (b i k-b j k)^2)]
      exact hdist i j)
  simpa only [expected_max_reindex] using hh

noncomputable def embedLeft {ι κ ν : Type*} (a : ι → κ → ℝ) (i : ι) : κ ⊕ ν → ℝ :=
  Sum.elim (a i) (fun _ ↦ 0)
noncomputable def embedRight {ι κ ν : Type*} (b : ι → ν → ℝ) (i : ι) : κ ⊕ ν → ℝ :=
  Sum.elim (fun _ ↦ 0) (b i)

lemma expected_max_embedLeft {ι κ ν : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype ν]
    (a : ι → κ → ℝ) :
    (∫ z, finiteMaximum (linearProcess (embedLeft (ν := ν) a) z) ∂gaussianProduct (κ ⊕ ν)) =
    ∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct κ := by
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ ν ↦ standardGaussian)
  change (∫ z, finiteMaximum (linearProcess (embedLeft a) z) ∂Measure.pi (fun _ : κ ⊕ ν ↦ standardGaussian)) = _
  rw [← he.integral_comp' (fun z ↦ finiteMaximum (linearProcess (embedLeft a) z))]
  have hlin (p : (κ → ℝ) × (ν → ℝ)) :
      linearProcess (embedLeft a) ((MeasurableEquiv.sumPiEquivProdPi (fun _ : κ ⊕ ν ↦ ℝ)).symm p) =
      linearProcess a p.1 := by
    funext i
    simp [linearProcess,embedLeft,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  simp only [hlin]
  simpa [gaussianProduct] using integral_fun_fst (μ := gaussianProduct κ) (ν := gaussianProduct ν) (fun z ↦ finiteMaximum (linearProcess a z))

lemma expected_max_embedRight {ι κ ν : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype ν]
    (b : ι → ν → ℝ) :
    (∫ z, finiteMaximum (linearProcess (embedRight (κ := κ) b) z) ∂gaussianProduct (κ ⊕ ν)) =
    ∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct ν := by
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ ν ↦ standardGaussian)
  change (∫ z, finiteMaximum (linearProcess (embedRight b) z) ∂Measure.pi (fun _ : κ ⊕ ν ↦ standardGaussian)) = _
  rw [← he.integral_comp' (fun z ↦ finiteMaximum (linearProcess (embedRight b) z))]
  have hlin (p : (κ → ℝ) × (ν → ℝ)) :
      linearProcess (embedRight b) ((MeasurableEquiv.sumPiEquivProdPi (fun _ : κ ⊕ ν ↦ ℝ)).symm p) =
      linearProcess b p.2 := by
    funext i
    simp [linearProcess,embedRight,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  simp only [hlin]
  simpa [gaussianProduct] using integral_fun_snd (μ := gaussianProduct κ) (ν := gaussianProduct ν) (fun z ↦ finiteMaximum (linearProcess b z))

lemma expected_max_le_of_pair_distances {ι κ ν : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype ν]
    (a : ι → κ → ℝ) (b : ι → ν → ℝ)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct κ) ≤
    ∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct ν := by
  have h := expected_max_le_of_pair_distances_orthogonal_fintype
    (embedLeft (ν := ν) a) (embedRight (κ := κ) b)
    (fun i j ↦ by simp [embedLeft,embedRight,Fintype.sum_sum_type])
    (fun i j ↦ by simpa only [Fintype.sum_sum_type,embedLeft,embedRight,
      Sum.elim_inl,Sum.elim_inr,sub_self,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero,zero_add,add_zero] using hdist i j)
  simpa only [expected_max_embedLeft,expected_max_embedRight] using h

noncomputable def spin (b : Bool) : ℝ := if b then 1 else -1
noncomputable def hamiltonian (n : ℕ) (J : (Fin n × Fin n) → ℝ)
    (σ : Fin n → Bool) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ *
    ∑ i : Fin n, ∑ j : Fin n, if i < j then J (i,j) * spin (σ i) * spin (σ j) else 0
noncomputable def groundStateSequence (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∫ J, sSup (range (hamiltonian n J)) ∂gaussianProduct (Fin n × Fin n)
noncomputable def groundStateValue : ℝ := limUnder atTop groundStateSequence

noncomputable def hamCoeff (n : ℕ) (σ : Fin n → Bool) (k : Fin n × Fin n) : ℝ :=
  if k.1 < k.2 then (Real.sqrt (n : ℝ))⁻¹ * spin (σ k.1) * spin (σ k.2) else 0
noncomputable def expectedMaximum (n : ℕ) : ℝ :=
  ∫ J, finiteMaximum (linearProcess (hamCoeff n) J) ∂gaussianProduct (Fin n × Fin n)

lemma spin_sq (b : Bool) : spin b ^ 2 = 1 := by cases b <;> norm_num [spin]
lemma abs_spin (b : Bool) : |spin b| = 1 := by cases b <;> norm_num [spin]

lemma linearProcess_hamCoeff (n : ℕ) (J : (Fin n × Fin n) → ℝ) :
    linearProcess (hamCoeff n) J = hamiltonian n J := by
  funext σ
  simp only [linearProcess,hamCoeff,hamiltonian,Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma groundStateSequence_eq (n : ℕ) : groundStateSequence n = (n : ℝ)⁻¹ * expectedMaximum n := by
  simp only [groundStateSequence,expectedMaximum,linearProcess_hamCoeff,finiteMaximum]

lemma twice_upper_sum {ι : Type*} [Fintype ι] [LinearOrder ι] (f : ι → ι → ℝ)
    (hsymm : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    2*(∑ i, ∑ j, if i < j then f i j else 0) = ∑ i, ∑ j, f i j := by
  have hs : (∑ i, ∑ j, if j < i then f i j else 0) = ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm j i]
  have hsplit (i j : ι) : f i j = (if i < j then f i j else 0)+(if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,not_lt_of_ge h.le]
    · subst j; simp [hdiag]
    · simp [h,not_lt_of_ge h.le]
  conv_rhs => arg 2; ext i; arg 2; ext j; rw [hsplit i j]
  simp only [Finset.sum_add_distrib,hs]
  ring

lemma spin_pair_difference {dimension : ℕ} (σ τ : Fin dimension → Bool) (i j : Fin dimension) :
    (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2 =
      2-2*(spin (σ i)*spin (τ i))*(spin (σ j)*spin (τ j)) := by
  have h1 := spin_sq (σ i)
  have h2 := spin_sq (σ j)
  have h3 := spin_sq (τ i)
  have h4 := spin_sq (τ j)
  calc
    _ = (spin (σ i))^2*(spin (σ j))^2+(spin (τ i))^2*(spin (τ j))^2 -
      2*(spin (σ i)*spin (τ i))*(spin (σ j)*spin (τ j)) := by ring
    _ = _ := by rw [h1,h2,h3,h4]; ring

end SKValueG
end

end OAI
