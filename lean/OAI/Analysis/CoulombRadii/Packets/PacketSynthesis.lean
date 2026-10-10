import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.Space

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
namespace Coulomb

def packetSynthesis (g : Space → ℂ) (f : Space × Space → ℂ) (x : Space) : ℂ :=
  ∫ yp : Space × Space, f yp * (Complex.exp ((2*Real.pi*inner ℝ x yp.2 : ℝ)*Complex.I) * g (x-yp.1))

lemma packetSynthesis_contDiff (g : Space → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (f : Space × Space → ℂ) (hf : LocallyIntegrable f volume)
    (P : ℝ) (hP : ∀ yp, f yp ≠ 0 → ‖yp.2‖ ≤ P) :
    ContDiff ℝ (⊤ : ℕ∞) (packetSynthesis g f) := by
  let χ : ContDiffBump (0 : Space) :=
    ⟨max 1 P, max 1 P+1, lt_of_lt_of_le (by norm_num) (le_max_left _ _), by linarith⟩
  let G : Space → Space × Space → ℂ := fun x z =>
    Complex.exp ((-2*Real.pi*inner ℝ z.2 x : ℝ)*Complex.I) * g z.1 * (χ z.2 : ℂ)
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space × (Space × Space) => G z.1 z.2) := by
    dsimp only [G]
    have hphase : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space × (Space × Space) =>
        ((-2*Real.pi*inner ℝ z.2.2 z.1 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_snd.snd.inner ℝ contDiff_fst))
    have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space × (Space × Space) => (χ z.2.2 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (χ.contDiff.comp (contDiff_snd.snd))
    fun_prop
  have hs (x : Space) (z : Space × Space) (_ : x ∈ (univ : Set Space))
      (hz : z ∉ tsupport g ×ˢ tsupport χ) : G x z = 0 := by
    have hh : z.1 ∉ tsupport g ∨ z.2 ∉ tsupport χ := by simpa only [mem_prod, not_and_or] using hz
    rcases hh with hz | hz
    · simp [G, image_eq_zero_of_notMem_tsupport hz]
    · simp [G, image_eq_zero_of_notMem_tsupport hz]
  have hc := contDiffOn_convolution_right_with_param_comp
    (ContinuousLinearMap.mul ℝ ℂ) (s := (univ : Set Space))
    (v := fun x : Space => (x, (0 : Space))) (f := f) (g := G)
    (by fun_prop) isOpen_univ (hgc.isCompact.prod χ.hasCompactSupport.isCompact) hs hf hG.contDiffOn
  rw [contDiffOn_univ] at hc
  convert hc using 1
  funext x
  rw [packetSynthesis, convolution_def]
  apply integral_congr_ae
  filter_upwards [] with yp
  by_cases hz : f yp = 0
  · simp [hz]
  · have hχ : χ (-yp.2) = 1 := χ.one_of_mem_closedBall (by
      simp only [mem_closedBall, dist_zero_right, norm_neg]
      exact (hP yp hz).trans (le_max_right _ _))
    simp only [G, Prod.fst_sub, Prod.snd_sub, zero_sub, hχ, Complex.ofReal_one, mul_one]
    congr 2
    congr 1
    rw [inner_neg_left, real_inner_comm]
    push_cast
    ring

lemma packetSynthesis_compactSupport (g : Space → ℂ) (hgc : HasCompactSupport g)
    (f : Space × Space → ℂ) (K : Set Space) (hK : IsCompact K)
    (hfK : ∀ yp, yp.1 ∉ K → f yp = 0) : HasCompactSupport (packetSynthesis g f) := by
  apply HasCompactSupport.intro (hK.add hgc.isCompact)
  intro x hx
  apply integral_eq_zero_of_ae
  filter_upwards [] with yp
  by_cases hy : yp.1 ∈ K
  · have hz : x-yp.1 ∉ tsupport g := by
      intro hz
      exact hx ⟨yp.1, hy, x-yp.1, hz, by abel_nf⟩
    simp [image_eq_zero_of_notMem_tsupport hz]
  · simp [hfK yp hy]
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate

end

end OAI
