import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace OAI

/-! # Passing local cutoff integral limits to the whole space -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem integral_cutoff_error_le_tail {F φ : X → ℝ} {S : Set X}
    (hF : Integrable F μ) (hφ : AEStronglyMeasurable φ μ)
    (hφ01 : ∀ x, φ x ∈ Icc (0:ℝ) 1) (hone : ∀ x ∈ S, φ x=1) :
    |(∫ x, F x ∂μ)-(∫ x, φ x*F x ∂μ)| ≤ ∫ x in Sᶜ, |F x| ∂μ := by
  have hφb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ (1:ℝ) := Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hφ01 x).1]
    exact (hφ01 x).2
  have hi := hF.bdd_mul hφ hφb
  rw [← integral_sub hF hi]
  have he : (∫ x, F x-φ x*F x ∂μ)=∫ x in Sᶜ, F x-φ x*F x ∂μ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hm : x ∈ S := by simpa only [mem_compl_iff,not_not] using hx
    rw [hone x hm,one_mul,sub_self]
  rw [he]
  calc
    _ ≤ ∫ x in Sᶜ, |F x-φ x*F x| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ.restrict Sᶜ) (fun x => F x-φ x*F x)
    _ ≤ ∫ x in Sᶜ, |F x| ∂μ := by
      apply integral_mono_ae (hF.sub hi).abs.integrableOn hF.abs.integrableOn
      exact Eventually.of_forall fun x => by
        change |F x-φ x*F x| ≤ |F x|
        rw [show F x-φ x*F x=(1-φ x)*F x by ring,abs_mul,
          abs_of_nonneg (sub_nonneg.mpr (hφ01 x).2)]
        exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [(hφ01 x).1])

theorem exists_integral_limit_of_cutoffs (F φ : ℕ → X → ℝ) (S : ℕ → Set X)
    (hF : ∀ k, Integrable (F k) μ) (hφ : ∀ N, AEStronglyMeasurable (φ N) μ)
    (hφ01 : ∀ N x, φ N x ∈ Icc (0:ℝ) 1) (hone : ∀ N x, x ∈ S N → φ N x=1)
    (hlocal : ∀ N, ∃ I : ℝ, Tendsto (fun k => ∫ x, φ N x*F k x ∂μ) atTop (𝓝 I))
    (htail : TendstoUniformly (fun N k => ∫ x in (S N)ᶜ, |F k x| ∂μ) (fun _ => 0) atTop) :
    ∃ I : ℝ, Tendsto (fun k => ∫ x, F k x ∂μ) atTop (𝓝 I) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro e he
  have he6 : 0 < e/6 := by positivity
  obtain ⟨N,hN⟩ := ((Metric.tendstoUniformly_iff.mp htail) (e/6) he6).exists
  obtain ⟨I,hI⟩ := hlocal N
  obtain ⟨K,hK⟩ := Metric.tendsto_atTop.mp hI (e/6) he6
  refine ⟨K,?_⟩
  intro i hi j hj
  have htail' (k : ℕ) : (∫ x in (S N)ᶜ, |F k x| ∂μ) < e/6 := by
    have ht := hN k
    rw [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at ht
    exact ht
  have hiE := (integral_cutoff_error_le_tail μ (hF i) (hφ N) (hφ01 N) (hone N)).trans_lt (htail' i)
  have hjE := (integral_cutoff_error_le_tail μ (hF j) (hφ N) (hφ01 N) (hone N)).trans_lt (htail' j)
  have hiI := hK i hi
  have hjI := hK j hj
  rw [Real.dist_eq] at hiI hjI ⊢
  obtain ⟨hiL,hiR⟩ := abs_lt.mp hiE
  obtain ⟨hjL,hjR⟩ := abs_lt.mp hjE
  obtain ⟨hiIL,hiIR⟩ := abs_lt.mp hiI
  obtain ⟨hjIL,hjIR⟩ := abs_lt.mp hjI
  apply abs_lt.mpr
  constructor <;> linarith

theorem integral_tendsto_of_cutoffs (F φ : ℕ → X → ℝ) (S : ℕ → Set X) (I : ℝ)
    (hF : ∀ k, Integrable (F k) μ) (hφ : ∀ N, AEStronglyMeasurable (φ N) μ)
    (hφ01 : ∀ N x, φ N x ∈ Icc (0:ℝ) 1) (hone : ∀ N x, x ∈ S N → φ N x=1)
    (hlocal : ∀ N, Tendsto (fun k => ∫ x, φ N x*F k x ∂μ) atTop (𝓝 I))
    (htail : TendstoUniformly (fun N k => ∫ x in (S N)ᶜ, |F k x| ∂μ) (fun _ => 0) atTop) :
    Tendsto (fun k => ∫ x, F k x ∂μ) atTop (𝓝 I) := by
  apply Metric.tendsto_atTop.mpr
  intro e he
  obtain ⟨N,hN⟩ := ((Metric.tendstoUniformly_iff.mp htail) (e/2) (half_pos he)).exists
  obtain ⟨K,hK⟩ := Metric.tendsto_atTop.mp (hlocal N) (e/2) (half_pos he)
  refine ⟨K,fun k hk => ?_⟩
  have htail' : (∫ x in (S N)ᶜ, |F k x| ∂μ) < e/2 := by
    have h := hN k
    rw [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at h
    exact h
  have herr := (integral_cutoff_error_le_tail μ (hF k) (hφ N) (hφ01 N) (hone N)).trans_lt htail'
  calc
    _ ≤ dist (∫ x, F k x ∂μ) (∫ x, φ N x*F k x ∂μ)+
        dist (∫ x, φ N x*F k x ∂μ) I := dist_triangle _ _ _
    _ < e/2+e/2 := add_lt_add (by simpa only [Real.dist_eq] using herr) (hK k hk)
    _ = e := by ring

end RegularPointCoordinates

end

end OAI
