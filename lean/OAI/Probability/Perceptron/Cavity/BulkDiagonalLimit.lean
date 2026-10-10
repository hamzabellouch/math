import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkSingleEmpiricalLimit
import OAI.Probability.Perceptron.Cavity.BulkTimeLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkMarkedArray_limit_diagonal_const (M : ℕ → ℕ) (g : Jet3) (v : ℕ → ℕ → ℝ)
    (s : ℕ → ℕ) (K : ℝ) (hK : ∀ n, (M (s n):ℝ)/(s n+1:ℕ)*‖g.d1‖^2 ≤ K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hlim : Tendsto (fun n => bulkMarkedArrayLaw (s n) (M (s n)) g (v (s n)) K (hK n)) atTop (𝓝 μ))
    (d : ℝ) (hL2 : Tendsto (fun n => bulkReplicaMean (s n) (M (s n)) g.f (v (s n)) 1
      (fun a x => (bulkB (s n+1) (M (s n)) g a.1 (x 0) (x 0)-d)^2)) atTop (𝓝 0)) :
    ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i, (Q i i).2.val = d := by
  let F : CompactBlock (BulkPairRange K) 1 →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun Q => ((Q 0 0).2.val-d)^2,by fun_prop⟩
  let G : CompactArray (BulkPairRange K) →ᵇ ℝ := F.compContinuous ⟨compactBlock 1,compactBlock_continuous 1⟩
  have hzero : (∫ Q, G Q ∂(μ : Measure (CompactArray (BulkPairRange K)))) = 0 := by
    have ht := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction G).continuousAt.tendsto.comp hlim
    have hfn n : (∫ Q, G Q ∂(bulkMarkedArrayLaw (s n) (M (s n)) g (v (s n)) K (hK n) : Measure _)) =
      bulkReplicaMean (s n) (M (s n)) g.f (v (s n)) 1
        (fun a x => (bulkB (s n+1) (M (s n)) g a.1 (x 0) (x 0)-d)^2) :=
      bulkMarkedArray_block (s n) (M (s n)) g (v (s n)) K (hK n) 1 F
    exact tendsto_nhds_unique (by simpa only [Function.comp_def,hfn] using ht) hL2
  have hz : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), (Q 0 0).2.val = d := by
    have ha := (integral_eq_zero_iff_of_nonneg
      (fun Q => show 0 ≤ G Q from sq_nonneg _) (G.integrable _)).mp hzero
    filter_upwards [ha] with Q hQ
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hQ)
  apply ae_all_iff.mpr
  intro i
  have he := compact_exchangeability_limit hlim (Equiv.swap 0 i)
    (fun n => bulkMarkedArray_exchangeable (s n) (M (s n)) g (v (s n)) K (hK n) _)
  simpa only [compactRelabel,Equiv.swap_apply_left] using he.quasiMeasurePreserving.ae hz

theorem bulkMarkedArray_diagonal_producer (M : ℕ → ℕ) (g : Jet3) (v : ℕ → ℕ → ℝ)
    (hv : ∀ᶠ n in atTop, ∀ p, 1 ≤ v n p)
    (hdO : ∀ p, Tendsto (fun n => bulkDeviationAt n (M n) g.f p (v n)) atTop (𝓝 0))
    (s : ℕ → ℕ) (hs : StrictMono s) (α : ℝ) (hα : 0 ≤ α)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (ho : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (K : ℝ) (hK : ∀ n, ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)*‖g.d1‖^2 ≤ K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hf : Tendsto (fun n => bulkMarkedArrayLaw (s n) (M (s n)+2) g (v (s n)) K (hK n)) atTop (𝓝 μ)) :
    ∃ d : ℝ, 0 ≤ d ∧ d ≤ K ∧ d ≤ α*‖g.d1‖^2 ∧
      (∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i, (Q i i).2.val = d) ∧
      (∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i j, (Q i j).2.val ≤ d) := by
  have hg := bulk_limit_geometry M g.f v hv hdO hs ho
  obtain ⟨c,hc,hL2⟩ := bulk_single_L2_concentration M g v s hs.tendsto_atTop α hd ho
    hg.2.2 hg.1 hg.2.1 (g.d1*g.d1)
  let d := α*c
  have hdia := bulkMarkedArray_limit_diagonal_const (fun n => M n+2) g v s K hK μ hf d hL2
  have hmg := bulkMarkedArray_limit_mark_geometry (fun n => M n+2) g v s K hK hf
  obtain ⟨Q,hQ,hpos⟩ := (hdia.and hmg.1).exists
  have hd0 : 0 ≤ d := by simpa only [hQ 0] using hpos 0
  have hdK : d ≤ K := by simpa only [hQ 0] using (Q 0 0).2.property.2
  have hdA : d ≤ α*‖g.d1‖^2 := by
    exact mul_le_mul_of_nonneg_left ((le_abs_self c).trans (hc.trans
      ((norm_mul_le _ _).trans_eq (by ring)))) hα
  refine ⟨d,hd0,hdK,hdA,hdia,?_⟩
  filter_upwards [hdia,hmg.2] with Q hD hB
  intro i j
  have h := hB i j
  rw [hD i,hD j] at h
  linarith

end SphericalPerceptronFreeEnergy

end

end OAI
