import Mathlib
import OAI.Probability.SKValue.GroundState.RotatedCoefficients

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma expected_logPartition_reindex {ι κ ν : Type*} [Fintype ι] [Fintype κ]
    [Fintype ν] (e : κ ≃ ν) (a : ι → κ → ℝ) :
    (∫ z, logPartition (linearProcess (fun i k ↦ a i (e.symm k)) z)
      ∂gaussianProduct ν) = ∫ z, logPartition (linearProcess a z) ∂gaussianProduct κ := by
  simpa only [linearProcess_reindex] using gaussian_integral_reindex e
    (fun z ↦ logPartition (linearProcess a z))

lemma expected_logPartition_le_orthogonal {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ι → κ → ℝ)
    (horth : ∀ i j, (∑ k, (a i k-a j k)*(b i k-b j k)) = 0)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, logPartition (linearProcess a z) ∂gaussianProduct κ) ≤
      ∫ z, logPartition (linearProcess b z) ∂gaussianProduct κ := by
  let e := Fintype.equivFin κ
  have h := expected_logPartition_le_of_pair_distances
    (fun i k ↦ a i (e.symm k)) (fun i k ↦ b i (e.symm k))
    (fun i j ↦ by
      rw [e.symm.sum_comp (fun k ↦ (a i k-a j k)*(b i k-b j k))]
      exact horth i j)
    (fun i j ↦ by
      rw [e.symm.sum_comp (fun k ↦ (a i k-a j k)^2),
        e.symm.sum_comp (fun k ↦ (b i k-b j k)^2)]
      exact hdist i j)
  simpa only [expected_logPartition_reindex] using h

lemma expected_logPartition_embedLeft {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (a : ι → κ → ℝ) :
    (∫ z, logPartition (linearProcess (embedLeft (ν := ν) a) z) ∂gaussianProduct (κ ⊕ ν)) =
      ∫ z, logPartition (linearProcess a z) ∂gaussianProduct κ := by
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ ν ↦ standardGaussian)
  change (∫ z, logPartition (linearProcess (embedLeft a) z)
    ∂Measure.pi (fun _ : κ ⊕ ν ↦ standardGaussian)) = _
  rw [← he.integral_comp' (fun z ↦ logPartition (linearProcess (embedLeft a) z))]
  have hlin (p : (κ → ℝ) × (ν → ℝ)) :
      linearProcess (embedLeft a) ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : κ ⊕ ν ↦ ℝ)).symm p) = linearProcess a p.1 := by
    funext i
    simp [linearProcess,embedLeft,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  simp only [hlin]
  simpa [gaussianProduct] using integral_fun_fst (μ := gaussianProduct κ)
    (ν := gaussianProduct ν) (fun z ↦ logPartition (linearProcess a z))

lemma expected_logPartition_embedRight {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (b : ι → ν → ℝ) :
    (∫ z, logPartition (linearProcess (embedRight (κ := κ) b) z) ∂gaussianProduct (κ ⊕ ν)) =
      ∫ z, logPartition (linearProcess b z) ∂gaussianProduct ν := by
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ ν ↦ standardGaussian)
  change (∫ z, logPartition (linearProcess (embedRight b) z)
    ∂Measure.pi (fun _ : κ ⊕ ν ↦ standardGaussian)) = _
  rw [← he.integral_comp' (fun z ↦ logPartition (linearProcess (embedRight b) z))]
  have hlin (p : (κ → ℝ) × (ν → ℝ)) :
      linearProcess (embedRight b) ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : κ ⊕ ν ↦ ℝ)).symm p) = linearProcess b p.2 := by
    funext i
    simp [linearProcess,embedRight,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  simp only [hlin]
  simpa [gaussianProduct] using integral_fun_snd (μ := gaussianProduct κ)
    (ν := gaussianProduct ν) (fun z ↦ logPartition (linearProcess b z))

lemma expected_logPartition_le {ι κ ν : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype ν]
    (a : ι → κ → ℝ) (b : ι → ν → ℝ)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, logPartition (linearProcess a z) ∂gaussianProduct κ) ≤
      ∫ z, logPartition (linearProcess b z) ∂gaussianProduct ν := by
  have h := expected_logPartition_le_orthogonal
    (embedLeft (ν := ν) a) (embedRight (κ := κ) b)
    (fun i j ↦ by simp [embedLeft,embedRight,Fintype.sum_sum_type])
    (fun i j ↦ by simpa only [Fintype.sum_sum_type,embedLeft,embedRight,
      Sum.elim_inl,Sum.elim_inr,sub_self,zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero,zero_add,add_zero] using hdist i j)
  simpa only [expected_logPartition_embedLeft,expected_logPartition_embedRight] using h

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma finiteMaximum_mono {ι : Type*} [Fintype ι] [Nonempty ι] {x y : ι → ℝ}
    (h : ∀ i, x i ≤ y i) : finiteMaximum x ≤ finiteMaximum y := by
  obtain ⟨i,hi⟩ := exists_finiteMaximum x
  rw [← hi]
  exact (h i).trans (le_finiteMaximum y i)

lemma finiteMaximum_add_const {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (c : ℝ) : finiteMaximum (fun i ↦ x i+c)=finiteMaximum x+c := by
  obtain ⟨i,hi⟩ := exists_finiteMaximum x
  obtain ⟨j,hj⟩ := exists_finiteMaximum (fun i ↦ x i+c)
  apply le_antisymm
  · rw [← hj]
    linarith [le_finiteMaximum x j]
  · rw [← hi]
    exact le_finiteMaximum (fun i ↦ x i+c) i

lemma affineMaximum_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (a : ι → κ → ℝ) (d : ι → ℝ) :
    Integrable (fun z ↦ finiteMaximum (fun i ↦ linearProcess a z i+d i)) (gaussianProduct κ) := by
  apply (integrable_finsetSum Finset.univ (fun i _ ↦
    ((linearProcess_integrable a i).add (integrable_const (d i))).abs)).mono'
  · exact (continuous_finiteMaximum.comp ((continuous_linearProcess a).add continuous_const)).aestronglyMeasurable
  · exact Eventually.of_forall (fun z ↦ by
      simpa only [Real.norm_eq_abs,Pi.add_apply] using abs_finiteMaximum_le
        (fun i ↦ linearProcess a z i + d i))

lemma replicated_partition_bounds {ι : Type*} [Fintype ι] [Nonempty ι]
    (x d : ι → ℝ) (β : ℝ) (hβ : 0≤β) (m : ι → ℕ)
    (hl : ∀ i, Real.exp (β*d i) ≤ (m i : ℝ))
    (hu : ∀ i, (m i : ℝ) ≤ 2*Real.exp (β*d i)) :
    β*finiteMaximum (fun i ↦ x i+d i) ≤
        logPartition (fun i : (Σ i, Fin (m i)) ↦ β*x i.1) ∧
      logPartition (fun i : (Σ i, Fin (m i)) ↦ β*x i.1) ≤
        β*finiteMaximum (fun i ↦ x i+d i)+Real.log (2*(Fintype.card ι : ℝ)) := by
  have hp : partition (fun i : (Σ i, Fin (m i)) ↦ β*x i.1) =
      ∑ i, (m i : ℝ)*Real.exp (β*x i) := by
    simp [partition,Fintype.sum_sigma]
  have hlo : Real.exp (β*finiteMaximum (fun i ↦ x i+d i)) ≤
      partition (fun i : (Σ i, Fin (m i)) ↦ β*x i.1) := by
    obtain ⟨i,hi⟩ := exists_finiteMaximum (fun i ↦ x i+d i)
    rw [← hi,hp]
    calc
      _ = Real.exp (β*d i)*Real.exp (β*x i) := by rw [←Real.exp_add]; congr 1; ring
      _ ≤ (m i : ℝ)*Real.exp (β*x i) := mul_le_mul_of_nonneg_right (hl i) (Real.exp_pos _).le
      _ ≤ _ := Finset.single_le_sum (f := fun j ↦ (m j : ℝ)*Real.exp (β*x j)) (fun j _ ↦ by positivity) (Finset.mem_univ i)
  have hup : partition (fun i : (Σ i, Fin (m i)) ↦ β*x i.1) ≤
      2*(Fintype.card ι : ℝ)*Real.exp (β*finiteMaximum (fun i ↦ x i+d i)) := by
    rw [hp]
    calc
      _ ≤ ∑ i : ι, 2*Real.exp (β*finiteMaximum (fun i ↦ x i+d i)) := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ 2*Real.exp (β*d i)*Real.exp (β*x i) :=
            mul_le_mul_of_nonneg_right (hu i) (Real.exp_pos _).le
          _ = 2*Real.exp (β*(x i+d i)) := by rw [mul_assoc,←Real.exp_add]; congr 2; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_finiteMaximum (fun i ↦ x i+d i) i) hβ)) (by norm_num)
      _ = _ := by simp; ring
  refine ⟨?_,?_⟩
  · simpa only [Real.log_exp,logPartition] using Real.log_le_log (Real.exp_pos _) hlo
  · have hc : 0<2*(Fintype.card ι : ℝ) := by positivity
    have hh := Real.log_le_log ((Real.exp_pos _).trans_le hlo) hup
    simpa only [logPartition,Real.log_mul hc.ne' (Real.exp_pos _).ne',
      Real.log_exp,add_comm] using hh

end SKValueG

end

end OAI
