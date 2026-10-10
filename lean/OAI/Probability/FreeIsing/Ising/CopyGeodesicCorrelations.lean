import OAI.Probability.FreeIsing.Ising.CopyEdgeCorrelations

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def cavityLogDifference (hbeta : 0 ≤ beta) (t : ℝ≥0) (v w : TreeVertex d)
    (q : Paths d × (Paths d × Paths d)) : ℝ :=
  cavityLogObservable hbeta t v w q.2.1 - cavityLogObservable hbeta t v w q.2.2

omit [IsProbabilityMeasure μ] in
theorem cavityLogObservable_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun x => cavityLogObservable hbeta t v w (relabel g x)) =ᵐ[observationLaw μ]
      cavityLogObservable hbeta t (g.toEquiv.symm v) (g.toEquiv.symm w) := by
  filter_upwards [cavityObservable_relabel_ae hμ hbeta g t v w] with x hx
  exact congrArg (fun z => Real.log (responseAttenuation (Real.tanh beta) z)) hx

theorem cavityLogDifference_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun q => cavityLogDifference hbeta t v w (copyRelabel g q)) =ᵐ[copies beta μ]
      cavityLogDifference hbeta t (g.toEquiv.symm v) (g.toEquiv.symm w) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  filter_upwards [hl.quasiMeasurePreserving.ae
    (cavityLogObservable_relabel_ae hμ hbeta g t v w),
    hr.quasiMeasurePreserving.ae
    (cavityLogObservable_relabel_ae hμ hbeta g t v w)] with q hq hq'
  exact congrArg₂ (fun x y : ℝ => x - y) hq hq'

theorem memLp_cavityLogDifference
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) :
    MemLp (cavityLogDifference hbeta t v w) 2 (copies beta μ) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  exact ((memLp_cavityLogObservable hμ hbeta t v w).comp_measurePreserving hl).sub
    ((memLp_cavityLogObservable hμ hbeta t v w).comp_measurePreserving hr)

theorem integral_cavityLogDifference_eq_zero
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) :
    (∫ q, cavityLogDifference hbeta t v w q ∂copies beta μ) = 0 := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  have hf := memLp_cavityLogObservable hμ hbeta t v w
  have hi₁ : Integrable (fun q => cavityLogObservable hbeta t v w q.2.1)
      (copies beta μ) := (hf.comp_measurePreserving hl).integrable (by norm_num)
  have hi₂ : Integrable (fun q => cavityLogObservable hbeta t v w q.2.2)
      (copies beta μ) := (hf.comp_measurePreserving hr).integrable (by norm_num)
  unfold cavityLogDifference
  rw [integral_sub hi₁ hi₂]
  have he₁ := hl.hasLaw.integral_comp hf.aestronglyMeasurable
  have he₂ := hr.hasLaw.integral_comp hf.aestronglyMeasurable
  simp only [Function.comp_def] at he₁ he₂
  rw [he₁, he₂, sub_self]

def cavityLogVector
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) : differenceSpace beta μ :=
  observableDifference (beta := beta) (memLp_cavityLogObservable hμ hbeta t v w)

theorem cavityLogVector_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) :
    (cavityLogVector hμ hbeta t v w : Lp ℝ 2 (copies beta μ)) =ᵐ[copies beta μ]
      cavityLogDifference hbeta t v w :=
  observableDifference_ae (beta := beta) (memLp_cavityLogObservable hμ hbeta t v w)

theorem inner_cavityLogVector_eq_integral
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w u z : TreeVertex d) :
    inner ℝ (cavityLogVector hμ hbeta t v w) (cavityLogVector hμ hbeta t u z) =
      ∫ q, cavityLogDifference hbeta t v w q * cavityLogDifference hbeta t u z q
        ∂copies beta μ := by
  change inner ℝ (cavityLogVector hμ hbeta t v w : Lp ℝ 2 (copies beta μ))
    (cavityLogVector hμ hbeta t u z : Lp ℝ 2 (copies beta μ)) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cavityLogVector_ae hμ hbeta t v w,
    cavityLogVector_ae hμ hbeta t u z] with q hq hq'
  simp [hq, hq', mul_comm]

theorem covariance_cavityLogDifference_eq_inner
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w u z : TreeVertex d) :
    covariance (cavityLogDifference hbeta t v w) (cavityLogDifference hbeta t u z)
      (copies beta μ) =
      inner ℝ (cavityLogVector hμ hbeta t v w) (cavityLogVector hμ hbeta t u z) := by
  rw [covariance_eq_sub (memLp_cavityLogDifference hμ hbeta t v w)
    (memLp_cavityLogDifference hμ hbeta t u z),
    integral_cavityLogDifference_eq_zero hμ hbeta t v w,
    integral_cavityLogDifference_eq_zero hμ hbeta t u z,
    zero_mul, sub_zero, inner_cavityLogVector_eq_integral]
  rfl

theorem inner_cavityLogVector_map
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w u z : TreeVertex d) :
    inner ℝ (cavityLogVector hμ hbeta t (g.toEquiv v) (g.toEquiv w))
      (cavityLogVector hμ hbeta t (g.toEquiv u) (g.toEquiv z)) =
    inner ℝ (cavityLogVector hμ hbeta t v w) (cavityLogVector hμ hbeta t u z) := by
  rw [inner_cavityLogVector_eq_integral, inner_cavityLogVector_eq_integral]
  have hmem := (memLp_cavityLogDifference hμ hbeta t v w).integrable_mul
    (memLp_cavityLogDifference hμ hbeta t u z)
  calc
    _ = ∫ q, cavityLogDifference hbeta t v w (copyRelabel g.symm q) *
        cavityLogDifference hbeta t u z (copyRelabel g.symm q) ∂copies beta μ := by
      apply integral_congr_ae
      filter_upwards [cavityLogDifference_relabel_ae hμ hbeta g.symm t v w,
        cavityLogDifference_relabel_ae hμ hbeta g.symm t u z] with q hq hq'
      exact (congrArg₂ (fun x y : ℝ => x * y) hq hq').symm
    _ = _ := (measurePreserving_copies_relabel hμ g.symm).hasLaw.integral_comp
      hmem.aestronglyMeasurable

theorem differenceReflection_cavityLogVector
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (c : Fin d) (t : ℝ≥0) (v w : TreeVertex d) :
    differenceReflection hμ c (cavityLogVector hμ hbeta t v w) =
      cavityLogVector hμ hbeta t (prefixFlip c v) (prefixFlip c w) := by
  apply Subtype.ext
  change koopmanL2 (copyRelabel (prefixTreeAut c))
    (measurePreserving_copies_relabel hμ (prefixTreeAut c))
    (cavityLogVector hμ hbeta t v w : Lp ℝ 2 (copies beta μ)) = _
  apply Lp.ext
  have hp := measurePreserving_copies_relabel hμ (prefixTreeAut c)
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (cavityLogVector hμ hbeta t v w : Lp ℝ 2 (copies beta μ)) hp,
    hp.quasiMeasurePreserving.ae (cavityLogVector_ae hμ hbeta t v w),
    cavityLogDifference_relabel_ae hμ hbeta (prefixTreeAut c) t v w,
    cavityLogVector_ae hμ hbeta t (prefixFlip c v) (prefixFlip c w)]
    with q hq hq' hq'' hq'''
  exact hq.trans (hq'.trans (hq''.trans hq'''.symm))

end Problem367.IsingCopySpectral

end

end OAI
