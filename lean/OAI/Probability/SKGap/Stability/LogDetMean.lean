import Mathlib
import OAI.Probability.SKGap.Brownian.LogDetPath

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_mul_diagonal_right (M : Matrix ι ι ℝ) (a : ι → ℝ) :
    (M*diagonal a).trace=∑ i,M i i*a i := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_diagonal]

lemma integral_trace_diagonal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (F : Ω → Matrix ι ι ℝ) (a : ι → ℝ) (hF : ∀ i, Integrable (fun g => F g i i) μ) :
    (∫ g, (F g*diagonal a).trace ∂μ)=∑ i,(∫ g, F g i i ∂μ)*a i := by
  simp_rw [trace_mul_diagonal_right]
  rw [integral_finsetSum Finset.univ (fun i _ => (hF i).mul_const (a i))]
  simp only [integral_mul_const]

omit [DecidableEq ι] in
lemma weighted_average_bias [Nonempty ι] {a t : ι → ℝ} {c δ : ℝ}
    (hδ : 0 ≤ δ) (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) (ht : ∀ i, |t i-c| ≤ δ) :
    |(∑ i,t i*a i)/(Fintype.card ι:ℝ)-c*((∑ i,a i)/(Fintype.card ι:ℝ))| ≤ δ := by
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have he : (∑ i,t i*a i)/(Fintype.card ι:ℝ)-c*((∑ i,a i)/(Fintype.card ι:ℝ))=
      (∑ i,(t i-c)*a i)/(Fintype.card ι:ℝ) := by
    simp_rw [sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum]
    ring
  rw [he,abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    show |(t i-c)*a i| ≤ δ from by rw [abs_mul,abs_of_nonneg (ha i)]; exact (mul_le_mul (ht i) (ha1 i) (ha i) hδ).trans_eq (mul_one δ))
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm] using hh

lemma logPathCutoffDerivative_mean_error [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j C : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hC : 0 ≤ C) {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1)
    (hK : ∀ i, |pathExpected f R hR j a z i-1| ≤ C/(Fintype.card ι:ℝ))
    (hWK : ∀ i, |(∫ g, (realProject R hR (goeMatrix (j/(Fintype.card ι:ℝ)) g)*
      pathK f R hR j a z (goeMatrix (j/(Fintype.card ι:ℝ)) g)) i i
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-z*((j/(Fintype.card ι:ℝ))*∑ b,a b)| ≤ C/(Fintype.card ι:ℝ)) :
    |(∫ g, logPathCutoffDerivative f R hR j a (goeMatrix (j/(Fintype.card ι:ℝ)) g) z
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-
      z*j*((∑ i,a i)/(Fintype.card ι:ℝ))^2| ≤ (2*j+1)*C/(Fintype.card ι:ℝ) := by
  let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  let KG := fun g : MatrixCoordinates ι → ℝ => pathK f R hR j a z (goeMatrix (j/(Fintype.card ι:ℝ)) g)
  let WG := fun g : MatrixCoordinates ι → ℝ => realProject R hR (goeMatrix (j/(Fintype.card ι:ℝ)) g)*KG g
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hB := (path_constants_nonneg f hR hj (by norm_num : (0:ℝ)≤1)).1
  have hbnd := (pathK_bounds f hR hj (by norm_num : (0:ℝ)≤1) ha ha1 hz).1
  have hcontK : Continuous KG := (pathK_continuous f hR hj (by norm_num : (0:ℝ)≤1) ha ha1 hz).comp (goeMatrix_pi_lipschitz _).continuous
  have hcontW : Continuous WG := ((realProject_lipschitz hR).continuous.comp (goeMatrix_pi_lipschitz _).continuous).mul hcontK
  have hiK (i : ι) : Integrable (fun g => KG g i i) μ :=
    Integrable.mono' (integrable_const (pathBound f R j 1)) (hcontK.matrix_elem i i).aestronglyMeasurable
      (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using (matrix_entry_le_opNorm _ i i).trans (hbnd _)))
  have hiW (i : ι) : Integrable (fun g => WG g i i) μ :=
    Integrable.mono' (integrable_const (R*pathBound f R j 1)) (hcontW.matrix_elem i i).aestronglyMeasurable
      (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using (matrix_entry_le_opNorm _ i i).trans (realProjectedProduct_opNorm hR _ hbnd _)))
  have htK : Integrable (fun g => (KG g*diagonal a).trace) μ := by
    simp_rw [trace_mul_diagonal_right]
    exact integrable_finsetSum _ (fun i _ => (hiK i).mul_const (a i))
  have htW : Integrable (fun g => (WG g*diagonal a).trace) μ := by
    simp_rw [trace_mul_diagonal_right]
    exact integrable_finsetSum _ (fun i _ => (hiW i).mul_const (a i))
  have heK := weighted_average_bias (div_nonneg hC hn.le) ha ha1 (t := fun i => ∫ g, KG g i i ∂μ) hK
  have heW := weighted_average_bias (div_nonneg hC hn.le) ha ha1 (t := fun i => ∫ g, WG g i i ∂μ) hWK
  rw [← integral_trace_diagonal KG a hiK] at heK
  rw [← integral_trace_diagonal WG a hiW] at heW
  have hq := diagonal_mean_bounds hj ha ha1
  simp only [mul_one] at hq
  have hcoef : |2*z*((j/(Fintype.card ι:ℝ))*∑ i,a i)| ≤ 2*j := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hz.1) hq.1)]
    nlinarith [mul_le_mul hz.2 hq.2 hq.1 (by norm_num : (0:ℝ)≤1)]
  change |(∫ g, (2*z*((j/(Fintype.card ι:ℝ))*∑ i,a i)*(KG g*diagonal a).trace-(WG g*diagonal a).trace)/(Fintype.card ι:ℝ) ∂μ)-_| ≤ _
  rw [integral_div,integral_sub (htK.const_mul _) htW,integral_const_mul]
  have he : (2*z*((j/(Fintype.card ι:ℝ))*∑ i,a i)*(∫ g, (KG g*diagonal a).trace ∂μ)-(∫ g, (WG g*diagonal a).trace ∂μ))/(Fintype.card ι:ℝ)-z*j*((∑ i,a i)/(Fintype.card ι:ℝ))^2=
      (2*z*((j/(Fintype.card ι:ℝ))*∑ i,a i))*((∫ g, (KG g*diagonal a).trace ∂μ)/(Fintype.card ι:ℝ)-1*((∑ i,a i)/(Fintype.card ι:ℝ)))-
      ((∫ g, (WG g*diagonal a).trace ∂μ)/(Fintype.card ι:ℝ)-z*((j/(Fintype.card ι:ℝ))*∑ i,a i)*((∑ i,a i)/(Fintype.card ι:ℝ))) := by ring
  rw [he]
  apply (abs_sub _ _).trans
  have hm := mul_le_mul hcoef heK (abs_nonneg _) (by positivity : 0 ≤ 2*j)
  rw [← abs_mul] at hm
  exact (add_le_add hm heW).trans_eq (by ring)
end SKGap
end
end

end OAI
