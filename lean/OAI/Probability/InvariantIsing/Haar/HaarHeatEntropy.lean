import OAI.Probability.InvariantIsing.Haar.HaarLogIntegration
import OAI.Probability.InvariantIsing.Haar.HaarHeatLogGradient
import OAI.Probability.InvariantIsing.Haar.HaarHeatTestLimit

namespace OAI

/-! Entropy dissipation along the actual positive polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

def haarHeatEntropy {N d : ℕ} (μ : Measure (SpecialOrthogonal N))
    (p : haarPolynomialSpace N d) (t : ℝ) : ℝ :=
  ∫ U, haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U*
    Real.log (haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U) ∂μ

theorem haarHeatEntropy_hasDerivAt {N d : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (p : haarPolynomialSpace N d)
    (ε : ℝ) (hε : 0 < ε)
    (hp : ∀ U : SpecialOrthogonal N, ε ≤ haarPolynomialValue (p : MatrixPolynomial N) U)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (haarHeatEntropy μ p)
      (-(∫ U, haarPolynomialValue (haarPolynomialGamma
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)) U/
        haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U ∂μ)) t := by
  let q (s : ℝ) : MatrixPolynomial N := (haarPolynomialHeat N d s p : haarPolynomialSpace N d)
  let u (s : ℝ) (U : SpecialOrthogonal N) := haarPolynomialValue (q s) U
  let L (s : ℝ) (U : SpecialOrthogonal N) := haarPolynomialValue (haarPolynomialLaplacian N (q s)) U
  let F' (s : ℝ) (U : SpecialOrthogonal N) := L s U*(Real.log (u s U)+1)
  obtain ⟨P,hP⟩ := haarPolynomialValue_bound (p : MatrixPolynomial N)
  have hpos (s : ℝ) (hs : 0 ≤ s) (U : SpecialOrthogonal N) : 0 < u s U :=
    hε.trans_le ((haarPolynomialHeat_bounds p ε P hp (fun V => (le_abs_self _).trans (hP V)) hs U).1)
  have hcont : ContinuousOn (fun z : ℝ × SpecialOrthogonal N => F' z.1 z.2)
      (Icc (t/2) (t+1) ×ˢ (Set.univ : Set (SpecialOrthogonal N))) := by
    apply ((continuous_haarPolynomialHeat_operator_value (haarPolynomialLaplacian N) p).continuousOn).mul
    apply ContinuousOn.add _ continuousOn_const
    apply (continuous_haarPolynomialHeat_value p).continuousOn.log
    intro z hz
    exact (hpos z.1 (by linarith [hz.1.1]) z.2).ne'
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set (SpecialOrthogonal N)))).exists_bound_of_continuousOn hcont
  have hnb : Ioo (t/2) (t+1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hlog : Continuous (fun U : SpecialOrthogonal N => Real.log (u t U)) :=
    (continuous_haarPolynomialValue _).log (fun U => (hpos t ht.le U).ne')
  have hdi : HasDerivAt (haarHeatEntropy μ p) (∫ U, F' t U ∂μ) t := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (s := Ioo (t/2) (t+1)) (F' := F') (bound := fun _ => B) hnb
      (Eventually.of_forall fun s => (Real.continuous_mul_log.comp (continuous_haarPolynomialValue (q s))).measurable.aestronglyMeasurable)
      (continuous_haar_integrable μ _ (Real.continuous_mul_log.comp (continuous_haarPolynomialValue (q t))))
      (((continuous_haarPolynomialValue _).mul (hlog.add continuous_const)).measurable.aestronglyMeasurable)
      (ae_of_all μ fun U s hs => hB (s,U) ⟨⟨hs.1.le,hs.2.le⟩,mem_univ U⟩)
      (integrable_const B) ?_).2
    apply ae_of_all
    intro U s hs
    have hu := haarPolynomialHeat_hasDerivAt p (U : Matrix (Fin N) (Fin N) ℝ) s
    have hh := (Real.hasDerivAt_mul_log (hpos s (by linarith [hs.1]) U).ne').comp s hu
    convert hh using 1
    · rfl
    · dsimp only [F',L,u,haarPolynomialValue,q]
      ring
  apply hdi.congr_deriv
  have hmul (U : SpecialOrthogonal N) : F' t U = L t U*Real.log (u t U)+L t U := by
    dsimp only [F']
    ring
  simp_rw [hmul]
  have hi1 : Integrable (fun U => L t U*Real.log (u t U)) μ :=
    continuous_haar_integrable μ _ ((continuous_haarPolynomialValue _).mul hlog)
  have hi2 : Integrable (L t) μ := haarPolynomialValue_integrable _ μ
  rw [integral_add hi1 hi2]
  rw [integral_haar_laplacian_log μ (q t) (hpos t ht.le)]
  change _+haarPolynomialMean μ (haarPolynomialLaplacian N (q t)) = _
  rw [haarPolynomialMean_laplacian,add_zero]

end InvariantIsing

end

end OAI
