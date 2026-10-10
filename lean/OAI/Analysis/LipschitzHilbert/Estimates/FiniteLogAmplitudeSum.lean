import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeClassBound
import OAI.Analysis.LipschitzHilbert.Estimates.MeasureClassLog
import OAI.Analysis.LipschitzHilbert.Estimates.FiniteClassRegroup

namespace OAI

/-! The numerical core of the restricted-to-strong lemma: logarithmic
decay sums over finitely many amplitude levels with a uniform constant. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem finite_log_amplitude_sum (I J : Finset ℤ) (m n : ℤ → ℝ) (ci cj : ℤ → ℤ)
    (hm : ∀ i∈I, 0<m i) (hn : ∀ j∈J, 0<n j)
    (hml : ∀ i∈I, (2:ℝ)^(ci i)≤m i) (hmu : ∀ i∈I, m i≤(2:ℝ)^(ci i+1))
    (hnl : ∀ j∈J, (2:ℝ)^(cj j)≤n j) (hnu : ∀ j∈J, n j≤(2:ℝ)^(cj j+1)) :
    (∑ i∈I, ∑ j∈J, ((1+|Real.log (m i/n j)|)^3)⁻¹*
      ((2:ℝ)^i*Real.sqrt (m i))*((2:ℝ)^j*Real.sqrt (n j)))≤
    (32*measureClassLogConstant*(∑' k, measureClassKernel k))*
      Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (m i))^2)*
      Real.sqrt (∑ j∈J, ((2:ℝ)^j*Real.sqrt (n j))^2) := by
  classical
  let a := fun i : ℤ => (2:ℝ)^i*Real.sqrt (m i)
  let b := fun j : ℤ => (2:ℝ)^j*Real.sqrt (n j)
  let A := fun k : ℤ => ∑ i∈I.filter (fun i => ci i=k), a i
  let B := fun l : ℤ => ∑ j∈J.filter (fun j => cj j=l), b j
  let E := fun k : ℤ => ∑ i∈I.filter (fun i => ci i=k), (a i)^2
  let F := fun l : ℤ => ∑ j∈J.filter (fun j => cj j=l), (b j)^2
  have hA (k : ℤ) : A k≤4*Real.sqrt 2*Real.sqrt (E k) := by
    apply amplitude_class_bound (I.filter (fun i => ci i=k)) m ((2:ℝ)^k)
    · intro i hi
      obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
      simpa only [he] using hml i hi
    · intro i hi
      obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
      calc
        _ ≤ (2:ℝ)^(k+1) := by simpa only [he] using hmu i hi
        _ = 2*(2:ℝ)^k := by rw [zpow_add₀ (by norm_num : (2:ℝ)≠0)]; norm_num; ring
  have hB (l : ℤ) : B l≤4*Real.sqrt 2*Real.sqrt (F l) := by
    apply amplitude_class_bound (J.filter (fun j => cj j=l)) n ((2:ℝ)^l)
    · intro j hj
      obtain ⟨hj,he⟩ := Finset.mem_filter.mp hj
      simpa only [he] using hnl j hj
    · intro j hj
      obtain ⟨hj,he⟩ := Finset.mem_filter.mp hj
      calc
        _ ≤ (2:ℝ)^(l+1) := by simpa only [he] using hnu j hj
        _ = 2*(2:ℝ)^l := by rw [zpow_add₀ (by norm_num : (2:ℝ)≠0)]; norm_num; ring
  have hA0 (k : ℤ) : 0≤A k := Finset.sum_nonneg (fun i _ => by dsimp only [a]; positivity)
  have hB0 (l : ℤ) : 0≤B l := Finset.sum_nonneg (fun j _ => by dsimp only [b]; positivity)
  have hclasses : (∑ k∈I.image ci, ∑ l∈J.image cj, measureClassKernel (k-l)*A k*B l)≤
      32*(∑' k, measureClassKernel k)*Real.sqrt (∑ i∈I, (a i)^2)*Real.sqrt (∑ j∈J, (b j)^2) := by
    have hdom (k l : ℤ) : measureClassKernel (k-l)*A k*B l≤
        32*(measureClassKernel (k-l)*Real.sqrt (E k)*Real.sqrt (F l)) := by
      calc
        _ ≤ measureClassKernel (k-l)*(4*Real.sqrt 2*Real.sqrt (E k))*(4*Real.sqrt 2*Real.sqrt (F l)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (hA k) (measureClassKernel_nonneg _)) (hB l)
            (hB0 l) (mul_nonneg (measureClassKernel_nonneg _) (by positivity))
        _ = 16*(Real.sqrt 2)^2*(measureClassKernel (k-l)*Real.sqrt (E k)*Real.sqrt (F l)) := by ring
        _ = _ := by rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]; ring
    have hE : (∑ k∈I.image ci, E k)=∑ i∈I, (a i)^2 :=
      Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem ci hi) (fun i => (a i)^2)
    have hF : (∑ l∈J.image cj, F l)=∑ j∈J, (b j)^2 :=
      Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem cj hj) (fun j => (b j)^2)
    calc
      _ ≤ ∑ k∈I.image ci, ∑ l∈J.image cj, 32*(measureClassKernel (k-l)*Real.sqrt (E k)*Real.sqrt (F l)) :=
        Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => hdom k l))
      _ = 32*(∑ k∈I.image ci, ∑ l∈J.image cj, measureClassKernel (k-l)*Real.sqrt (E k)*Real.sqrt (F l)) := by
        simp only [Finset.mul_sum]
      _ ≤ 32*((∑' k, measureClassKernel k)*Real.sqrt (∑ k∈I.image ci, (Real.sqrt (E k))^2)*
          Real.sqrt (∑ l∈J.image cj, (Real.sqrt (F l))^2)) :=
        mul_le_mul_of_nonneg_left (measure_class_convolution_bound (I.image ci) (J.image cj)
          (fun k => Real.sqrt (E k)) (fun l => Real.sqrt (F l))
          (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _)) (by norm_num)
      _ = _ := by
        have he (k : ℤ) : (Real.sqrt (E k))^2=E k := Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        have hf (l : ℤ) : (Real.sqrt (F l))^2=F l := Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        simp_rw [he,hf,hE,hF]
        ring
  calc
    _ ≤ ∑ i∈I, ∑ j∈J, (measureClassLogConstant*measureClassKernel (ci i-cj j))*a i*b j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (measure_class_log_bound (m i) (n j) (ci i) (cj j) (hm i hi) (hn j hj)
          (hml i hi) (hmu i hi) (hnl j hj) (hnu j hj)) (by positivity))
        (by positivity)
    _ = measureClassLogConstant*(∑ k∈I.image ci, ∑ l∈J.image cj, measureClassKernel (k-l)*A k*B l) := by
      rw [finite_class_bilinear_sum I J ci cj a b (fun k l => measureClassKernel (k-l))]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ measureClassLogConstant*(32*(∑' k, measureClassKernel k)*
        Real.sqrt (∑ i∈I, (a i)^2)*Real.sqrt (∑ j∈J, (b j)^2)) :=
      mul_le_mul_of_nonneg_left hclasses (by dsimp only [measureClassLogConstant]; positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
