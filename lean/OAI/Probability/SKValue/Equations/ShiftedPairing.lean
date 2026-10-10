import Mathlib

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
namespace SKValue

lemma abs_sum_mul_le_of_sq_bounds {ι : Type*} [Fintype ι]
    {x y : ι → ℝ} {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hx : (∑ i, (x i)^2)≤a^2) (hy : (∑ i, (y i)^2)≤b^2) :
    |∑ i, x i*y i|≤a*b := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hmul := mul_le_mul hx hy (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (y i))) (sq_nonneg a)
  have hs : |∑ i, x i*y i|^2≤(a*b)^2 := by simpa only [sq_abs, mul_pow] using hcs.trans hmul
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg ha hb)).1 hs

lemma sum_fin_castSucc_sq_le {N : ℕ} (f : Fin (N+1) → ℝ) :
    (∑ i : Fin N, (f i.castSucc)^2)≤∑ i, (f i)^2 := by
  rw [Fin.sum_univ_castSucc]
  exact le_add_of_nonneg_right (sq_nonneg _)

lemma sum_fin_succ_sq_le {N : ℕ} (f : Fin (N+1) → ℝ) :
    (∑ i : Fin N, (f i.succ)^2)≤∑ i, (f i)^2 := by
  rw [Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (sq_nonneg _)

lemma pointwise_le_sqrt_sum_sq {ι : Type*} [Fintype ι] (f : ι → ℝ) (j : ι) :
    |f j|≤Real.sqrt (∑ i, (f i)^2) := by
  have hsq : (f j)^2≤∑ i, (f i)^2 :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg (f i)) (Finset.mem_univ j)
  exact (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (f i)))).2
    (by simpa only [sq_abs] using hsq)

def shiftedPairing {N : ℕ} (A B : Fin (N+1) → ℝ) (bstar : ℝ) : ℝ :=
  (∑ i : Fin N, A i.castSucc*B i.succ)+A (Fin.last N)*bstar

lemma shiftedPairing_error {N : ℕ} {A B α β : Fin (N+1) → ℝ} {bstar e C : ℝ}
    (he : 0≤e) (hC : 0≤C)
    (hA : (∑ i, (A i-α i)^2)≤e) (hB : (∑ i, (B i-β i)^2)≤e)
    (hBn : (∑ i, (B i)^2)≤1) (hαn : (∑ i, (α i)^2)≤C^2)
    (hb : |bstar|≤1) :
    |shiftedPairing A B bstar-∑ i : Fin N, α i.castSucc*β i.succ| ≤
      (2+C)*Real.sqrt e+|α (Fin.last N)| := by
  have hAe : (∑ i : Fin N, (A i.castSucc-α i.castSucc)^2)≤(Real.sqrt e)^2 := by
    rw [Real.sq_sqrt he]
    exact (sum_fin_castSucc_sq_le (fun i ↦ A i-α i)).trans hA
  have hBe : (∑ i : Fin N, (B i.succ-β i.succ)^2)≤(Real.sqrt e)^2 := by
    rw [Real.sq_sqrt he]
    exact (sum_fin_succ_sq_le (fun i ↦ B i-β i)).trans hB
  have hBns : (∑ i : Fin N, (B i.succ)^2)≤(1 : ℝ)^2 := by
    simpa using (sum_fin_succ_sq_le B).trans hBn
  have hαns : (∑ i : Fin N, (α i.castSucc)^2)≤C^2 := (sum_fin_castSucc_sq_le α).trans hαn
  have hfirst := abs_sum_mul_le_of_sq_bounds (Real.sqrt_nonneg e) (by norm_num : (0:ℝ)≤1) hAe hBns
  have hsecond := abs_sum_mul_le_of_sq_bounds hC (Real.sqrt_nonneg e) hαns hBe
  have hAend : |A (Fin.last N)-α (Fin.last N)|≤Real.sqrt e :=
    (pointwise_le_sqrt_sum_sq (fun i ↦ A i-α i) (Fin.last N)).trans (Real.sqrt_le_sqrt hA)
  have hend : |A (Fin.last N)*bstar|≤Real.sqrt e+|α (Fin.last N)| := by
    rw [abs_mul]
    calc
      _ ≤ |A (Fin.last N)| *1 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ (|A (Fin.last N)-α (Fin.last N)|+|α (Fin.last N)|)*1 := by
        gcongr
        simpa only [sub_add_cancel] using
          abs_add_le (A (Fin.last N)-α (Fin.last N)) (α (Fin.last N))
      _ ≤ _ := by simpa only [mul_one] using add_le_add hAend le_rfl
  have hdecomp : shiftedPairing A B bstar-∑ i : Fin N, α i.castSucc*β i.succ =
      (∑ i : Fin N, (A i.castSucc-α i.castSucc)*B i.succ)+
      (∑ i : Fin N, α i.castSucc*(B i.succ-β i.succ))+A (Fin.last N)*bstar := by
    unfold shiftedPairing
    rw [← Finset.sum_add_distrib]
    ring_nf
    simp only [Finset.sum_sub_distrib]
    ring
  rw [hdecomp]
  calc
    _ ≤ |∑ i : Fin N, (A i.castSucc-α i.castSucc)*B i.succ|+
        |∑ i : Fin N, α i.castSucc*(B i.succ-β i.succ)|+|A (Fin.last N)*bstar| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ Real.sqrt e*1+C*Real.sqrt e+(Real.sqrt e+|α (Fin.last N)|) := by
      exact add_le_add (add_le_add hfirst hsecond) hend
    _ = _ := by ring

lemma shiftedPairing_tendsto_error_zero
    {A B α β : (N : ℕ) → Fin (N+1) → ℝ} {bstar e r : ℕ → ℝ} {C : ℝ}
    (he : ∀ N, 0≤e N) (hC : 0≤C)
    (hA : ∀ᶠ N in atTop, (∑ i, (A N i-α N i)^2)≤e N)
    (hB : ∀ᶠ N in atTop, (∑ i, (B N i-β N i)^2)≤e N)
    (hBn : ∀ᶠ N in atTop, (∑ i, (B N i)^2)≤1)
    (hαn : ∀ᶠ N in atTop, (∑ i, (α N i)^2)≤C^2)
    (hb : ∀ᶠ N in atTop, |bstar N|≤1)
    (hend : ∀ᶠ N in atTop, |α N (Fin.last N)|≤r N)
    (he0 : Tendsto e atTop (𝓝 0)) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun N ↦ shiftedPairing (A N) (B N) (bstar N)-
      ∑ i : Fin N, α N i.castSucc*β N i.succ) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun N ↦ (2+C)*Real.sqrt (e N)+r N)
  · filter_upwards [hA,hB,hBn,hαn,hb,hend] with N hA hB hBn hαn hb hend
    rw [Real.norm_eq_abs]
    exact (shiftedPairing_error (he N) hC hA hB hBn hαn hb).trans (add_le_add le_rfl hend)
  · simpa only [Real.sqrt_zero, mul_zero, add_zero, Function.comp_apply] using
      ((Real.continuous_sqrt.tendsto 0).comp he0 |>.const_mul (2+C)).add hr0

end SKValue

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace SKValue

lemma integral_sq_le_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, f ω ∂μ)^2 ≤ ∫ ω, (f ω)^2 ∂μ := by
  have h := variance_nonneg f μ
  rw [variance_eq_sub hf] at h
  exact sub_nonneg.mp h

lemma integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, |f ω| ∂μ) ≤ Real.sqrt (∫ ω, (f ω)^2 ∂μ) := by
  have hab : MemLp (fun ω ↦ |f ω|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have h := integral_sq_le_integral_sq hab
  simp only [sq_abs] at h
  exact (Real.le_sqrt (integral_nonneg (fun _ ↦ abs_nonneg _))
    (integral_nonneg (fun _ ↦ sq_nonneg _))).mpr h

lemma square_difference_bound {x y K L e : ℝ}
    (_hK : 0≤K) (hL : 0≤L) (he : 0≤e)
    (hx : |x|≤K) (hy : |y|≤K) (hxy : |x-y|≤L*e) :
    |x^2-y^2| ≤ (2*K*L)*e := by
  have hs : |x+y|≤2*K := (abs_add_le _ _).trans (by linarith)
  calc
    |x^2-y^2| = |x-y| * |x+y| := by rw [← abs_mul]; congr 1; ring
    _ ≤ (L*e)*(2*K) := mul_le_mul hxy hs (abs_nonneg _) (mul_nonneg hL he)
    _ = _ := by ring

lemma second_moment_perturbation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f g e : Ω → ℝ} {K L : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (he : MemLp e 2 μ)
    (hK : 0≤K) (hL : 0≤L)
    (hbound : ∀ᵐ ω ∂μ, |f ω|≤K ∧ |g ω|≤K ∧ |f ω-g ω|≤L*|e ω|) :
    |(∫ ω, (f ω)^2 ∂μ)-(∫ ω, (g ω)^2 ∂μ)| ≤
      (2*K*L)*Real.sqrt (∫ ω, (e ω)^2 ∂μ) := by
  have hfi : Integrable (fun ω ↦ (f ω)^2) μ := hf.integrable_sq
  have hgi : Integrable (fun ω ↦ (g ω)^2) μ := hg.integrable_sq
  have hei : Integrable (fun ω ↦ |e ω|) μ := by
    simpa only [Real.norm_eq_abs] using (he.integrable (by norm_num : (1 : ENNReal)≤2)).norm
  calc
    _ = |∫ ω, (f ω)^2-(g ω)^2 ∂μ| := by rw [integral_sub hfi hgi]
    _ ≤ ∫ ω, |(f ω)^2-(g ω)^2| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (2*K*L)*|e ω| ∂μ := by
      apply integral_mono_ae
      · exact (hfi.sub hgi).abs
      · exact hei.const_mul _
      · filter_upwards [hbound] with ω hω
        exact square_difference_bound hK hL (abs_nonneg _) hω.1 hω.2.1 hω.2.2
    _ = (2*K*L)*(∫ ω, |e ω| ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_le_sqrt_integral_sq he) (by positivity)

lemma uniform_moment_positive {q : ℕ → ℕ → ℝ} {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0))
    (hq : ∀ N j, j<N → |q N j-1|≤r N) :
    ∀ᶠ N in atTop, ∀ j<N, 0<q N j := by
  filter_upwards [hr.eventually_lt_const (by norm_num : (0 : ℝ)<1)] with N hN j hj
  have h := (abs_le.mp (hq N j hj)).1
  linarith

lemma uniform_normalizer_convergence {q : ℕ → ℕ → ℝ} {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0))
    (hq : ∀ N j, j<N → |q N j-1|≤r N) :
    ∀ ε>0, ∀ᶠ N in atTop, ∀ j<N, |(Real.sqrt (q N j))⁻¹-1|<ε := by
  have hc : ContinuousAt (fun x : ℝ ↦ (Real.sqrt x)⁻¹) 1 :=
    (Real.continuous_sqrt.continuousAt).inv₀ (by norm_num)
  intro ε hε
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp hc ε hε
  filter_upwards [hr.eventually_lt_const hδ] with N hN j hj
  have hd : dist (q N j) 1 < δ := by
    simpa only [Real.dist_eq] using (hq N j hj).trans_lt hN
  have h := hcont hd
  simpa only [Real.sqrt_one, inv_one, Real.dist_eq] using h

lemma uniform_inverse_normalizer_convergence {q : ℕ → ℕ → ℝ} {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0))
    (hq : ∀ N j, j<N → |q N j-1|≤r N) :
    ∀ ε>0, ∀ᶠ N in atTop, ∀ j<N, |Real.sqrt (q N j)-1|<ε := by
  intro ε hε
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp
    Real.continuous_sqrt.continuousAt ε hε
  filter_upwards [hr.eventually_lt_const hδ] with N hN j hj
  have hd : dist (q N j) 1 < δ := by
    simpa only [Real.dist_eq] using (hq N j hj).trans_lt hN
  have h := hcont hd
  simpa only [Real.sqrt_one, Real.dist_eq] using h

end SKValue

open MeasureTheory Set Filter
open scoped Topology BigOperators

end

end OAI
