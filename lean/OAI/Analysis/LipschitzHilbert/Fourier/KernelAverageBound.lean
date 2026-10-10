import OAI.Analysis.LipschitzHilbert.Fourier.LineConvolutionLocal
import OAI.Analysis.LipschitzHilbert.Estimates.GeometricScaleWeights

namespace OAI

/-! A kernel with a zeroth and a second decay bound is controlled by
centered interval averages. Finite annular sums retain a uniform constant. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem kernel_average_bound (K f : ℝ → ℂ) (hK : Integrable K)
    (hfm : Measurable f) (B : ℝ) (hfb : ∀ x, ‖f x‖≤B)
    (A D R M x : ℝ) (hA : 0≤A) (hD : 0≤D) (hR : 0<R) (hM : 0≤M)
    (hzero : ∀ t, ‖K t‖≤A) (hsecond : ∀ t, |t|^2*‖K t‖≤D)
    (hmean : ∀ r, R≤r → (∫ t in Icc (-r) r, ‖f (x-t)‖)≤12*r*M) :
    ‖lineConvolution K f x‖≤12*A*R*M+48*D/R*M := by
  let g := fun t => ‖K t‖*‖f (x-t)‖
  have hg : Integrable g := by
    simpa only [norm_mul] using
      (lineConvolution_integrand_of_bounded K f hK hfm B hfb x).norm
  let r := fun n : ℕ => (2:ℝ)^n*R
  let S := fun n => Icc (-r n) (r n)
  have hr (n : ℕ) : 0<r n := by dsimp [r]; positivity
  have hRr (n : ℕ) : R≤r n := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) hR.le
  have hsucc (n : ℕ) : r (n+1)=2*r n := by dsimp [r]; rw [pow_succ]; ring
  have hmono : Monotone S := by
    intro n m hnm
    have hm : r n≤r m := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hnm) hR.le
    intro t ht
    exact ⟨by linarith [ht.1],ht.2.trans hm⟩
  have hbase : (∫ t in S 0, g t)≤12*A*R*M := by
    have hfi : IntegrableOn (fun t => ‖f (x-t)‖) (S 0) := by
      have : IsFiniteMeasure (volume.restrict (S 0)) := isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
      exact (MemLp.of_bound (p:=1)
        (hfm.comp (show Measurable (fun t : ℝ => x-t) by fun_prop)).norm.aestronglyMeasurable.restrict B
        (Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_of_nonneg (norm_nonneg _),Function.comp_def] using hfb (x-t)))).integrable (by norm_num)
    calc
      _ ≤ ∫ t in S 0, A*‖f (x-t)‖ := integral_mono hg.integrableOn (hfi.const_mul A)
        (fun t => mul_le_mul_of_nonneg_right (hzero t) (norm_nonneg _))
      _ = A*(∫ t in Icc (-R) R, ‖f (x-t)‖) := by simp only [S,r,pow_zero,one_mul,integral_const_mul]
      _ ≤ A*(12*R*M) := mul_le_mul_of_nonneg_left (hmean R le_rfl) hA
      _ = _ := by ring
  have hstep (n : ℕ) : (∫ t in S (n+1)\S n, g t)≤24*D/R*M*(1/2:ℝ)^n := by
    have hfi : IntegrableOn (fun t => ‖f (x-t)‖) (S (n+1)) := by
      have : IsFiniteMeasure (volume.restrict (S (n+1))) := isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
      exact (MemLp.of_bound (p:=1)
        (hfm.comp (show Measurable (fun t : ℝ => x-t) by fun_prop)).norm.aestronglyMeasurable.restrict B
        (Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_of_nonneg (norm_nonneg _),Function.comp_def] using hfb (x-t)))).integrable (by norm_num)
    have hb (t : ℝ) (ht : t∈S (n+1)\S n) : ‖K t‖≤D/(r n)^2 := by
      have htabs : r n≤|t| := by
        by_contra hh
        apply ht.2
        have hh' := abs_le.mp (le_of_lt (lt_of_not_ge hh))
        exact hh'
      have hp := pow_le_pow_left₀ (hr n).le htabs 2
      apply (le_div_iff₀ (sq_pos_of_pos (hr n))).mpr
      calc
        ‖K t‖*(r n)^2 ≤ ‖K t‖*|t|^2 := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
        _ ≤ D := by simpa only [mul_comm] using hsecond t
    calc
      _ ≤ ∫ t in S (n+1)\S n, (D/(r n)^2)*‖f (x-t)‖ := by
        apply integral_mono_ae hg.integrableOn ((hfi.const_mul (D/(r n)^2)).mono_measure (Measure.restrict_mono sdiff_subset le_rfl))
        filter_upwards [ae_restrict_mem (measurableSet_Icc.diff measurableSet_Icc)] with t ht
        exact mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg _)
      _ ≤ ∫ t in S (n+1), (D/(r n)^2)*‖f (x-t)‖ :=
        setIntegral_mono_set (hfi.const_mul _) (Filter.Eventually.of_forall fun _ => by positivity)
          (Filter.Eventually.of_forall sdiff_subset)
      _ = (D/(r n)^2)*(∫ t in S (n+1), ‖f (x-t)‖) := by rw [integral_const_mul]
      _ ≤ (D/(r n)^2)*(12*r (n+1)*M) :=
        mul_le_mul_of_nonneg_left (hmean _ (hRr _)) (by positivity)
      _ = _ := by
        rw [hsucc]
        dsimp [r]
        rw [div_pow,one_pow]
        field_simp
        ring
  have hfinite (n : ℕ) : (∫ t in S n, g t)≤
      12*A*R*M+(24*D/R*M)*(∑ k∈Finset.range n, (1/2:ℝ)^k) := by
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
      have he := integral_inter_add_sdiff (s:=S (n+1)) (t:=S n) measurableSet_Icc hg.integrableOn
      rw [inter_eq_right.mpr (hmono (Nat.le_succ n))] at he
      rw [Finset.sum_range_succ]
      linarith [hstep n]
  have hall (n : ℕ) : (∫ t in S n, g t)≤12*A*R*M+48*D/R*M := by
    have hh := mul_le_mul_of_nonneg_left (sum_half_powers_le_two n)
      (show 0≤24*D/R*M by positivity)
    calc
      _ ≤ 12*A*R*M+(24*D/R*M)*(∑ k∈Finset.range n, (1/2:ℝ)^k) := hfinite n
      _ ≤ 12*A*R*M+(24*D/R*M)*2 := add_le_add le_rfl hh
      _ = _ := by ring
  have hcover : (⋃ n, S n)=(univ : Set ℝ) := by
    apply Set.eq_univ_of_forall
    intro t
    obtain ⟨n,hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).eventually
      (eventually_gt_atTop (|t|/R))).exists
    apply mem_iUnion.mpr
    refine ⟨n,?_⟩
    have ht : |t|≤r n := by
      dsimp [r]
      exact le_of_lt ((div_lt_iff₀ hR).mp hn)
    exact abs_le.mp ht
  have hlim := tendsto_setIntegral_of_monotone (fun _ => measurableSet_Icc) hmono
    hg.integrableOn
  rw [hcover] at hlim
  simp only [Measure.restrict_univ] at hlim
  have htotal := le_of_tendsto hlim (Filter.Eventually.of_forall hall)
  exact (norm_integral_le_integral_norm _).trans (by simpa only [g,norm_mul] using htotal)

end LipschitzHilbert.PacketRepresentation

end

end OAI
