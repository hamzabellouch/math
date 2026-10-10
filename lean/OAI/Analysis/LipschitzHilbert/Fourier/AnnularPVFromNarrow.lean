import OAI.Analysis.LipschitzHilbert.Estimates.NarrowPartitionBound
import OAI.Analysis.LipschitzHilbert.Fourier.AnnularEnlargement

namespace OAI

/-! A fixed finite frequency covering converts the narrow-band
hypothesis into uniform bounds for all dilated annular inputs. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def fixedAnnulus : Set ℝ := {x | 1≤|x| ∧ |x|≤2}

theorem fixedAnnulus_compact : IsCompact fixedAnnulus := by
  apply (isCompact_Icc : IsCompact (Set.Icc (-2:ℝ) 2)).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  · intro x hx
    exact abs_le.mp hx.2

theorem exists_annular_PV_constant : ∃ D : ℝ, 0<D ∧
    ∀ (u : (ℝ×ℝ) → ℝ) (R : ℝ), 0<R → R≤1/4 →
    ∀ B : ℝ, 0≤B →
      (∀ w : ℝ, 0<w → ∀ g : SchwartzMap (ℝ×ℝ) ℂ,
        MemLp (productSlopePrincipalValue u R (schwartzVerticalProjection narrowBandProfile w 0 g))
          2 planeMeasure ∧
        eLpNorm (productSlopePrincipalValue u R (schwartzVerticalProjection narrowBandProfile w 0 g))
          2 planeMeasure≤ENNReal.ofReal (B*‖g.toLp 2 planeMeasure‖)) →
    ∀ (W : ℝ), 0<W → ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
      (∀ omega, planarFourier f omega≠0 → W*omega.2∈fixedAnnulus) →
      MemLp (productSlopePrincipalValue u R f) 2 planeMeasure ∧
      eLpNorm (productSlopePrincipalValue u R f) 2 planeMeasure≤
        ENNReal.ofReal ((B*D)*‖f.toLp 2 planeMeasure‖) := by
  obtain ⟨l,habs,hpartition⟩ := exists_finite_narrow_partition fixedAnnulus fixedAnnulus_compact
    (fun x hx => by intro he; norm_num [he,fixedAnnulus] at hx)
  refine ⟨1+narrowPartitionCost l,by linarith [narrowPartitionCost_nonneg l],?_⟩
  intro u R hR hRs B hB hband W hW f hsupport
  have h := narrowPartition_PV_bound l fixedAnnulus habs hpartition u R hR hRs B hB
    hband W hW f hsupport
  refine ⟨h.1,h.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  nlinarith only [mul_nonneg hB (norm_nonneg (f.toLp 2 planeMeasure))]

theorem annularProjection_fourier_support (p : SchwartzMap ℝ ℂ)
    (hp : ∀ x, p x≠0 → x∈fixedAnnulus) (W : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ)
    (h : planarFourier (schwartzVerticalProjection p W 0 f) omega≠0) :
    W*omega.2∈fixedAnnulus := by
  rw [schwartzVerticalProjection_fourier,sub_zero] at h
  exact hp _ (mul_ne_zero_iff.mp h).1

theorem reassemblyDifference_fixedAnnulus (x : ℝ) (hx : reassemblyDifferenceSchwartz x≠0) :
    x∈fixedAnnulus := by
  change 1≤|x| ∧ |x|≤2
  have hsmall : 9/8 < |x| := lt_of_not_ge (fun h => hx (reassemblyDifference_small x h))
  have hlarge : |x| < 117/64 := lt_of_not_ge (fun h => hx (reassemblyDifference_large x h))
  constructor <;> linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
