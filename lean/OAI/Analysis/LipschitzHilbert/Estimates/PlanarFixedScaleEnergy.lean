import OAI.Analysis.LipschitzHilbert.Packets.WeightedPacketEnergy
import OAI.Analysis.LipschitzHilbert.Estimates.SlicedIntegral
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

namespace OAI

/-! The fixed-length synthesis estimate in section 3. A single translated
box lattice has bounded overlap. Summing squared bin components gives a
constant independent of the number of packets and frequency bins. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

def planarFixedSynthesis {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ i, c i k * f i k z)

theorem planarFixedSynthesis_memLp {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (planarFixedSynthesis c f) 2 (volume.prod volume) := by
  apply memLp_piLp_iff.mpr
  intro k
  exact memLp_finsetSum _ (fun i _ => ((f i k).memLp 2 (volume.prod volume)).const_mul (c i k))

theorem planarFixedSynthesis_pointwise {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (z : ℝ×ℝ) (weight : ι → ℝ) (hw : ∀ i, 0 < weight i)
    {C D : ℝ} (hD : 0 ≤ D) (hover : ∑ i, weight i ≤ D)
    (henv : ∀ i k, ‖f i k z‖ ≤ C*weight i) :
    ‖planarFixedSynthesis c f z‖^2 ≤ D*C^2*∑ i, ‖c i‖^2*weight i := by
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ k, D*C^2*∑ i, ‖c i k‖^2*weight i := by
      apply Finset.sum_le_sum
      intro k _
      exact envelope_synthesis_square (fun i => c i k) (fun i => f i k z)
        weight hw hD hover (fun i => henv i k)
    _ = _ := by
      rw [← Finset.mul_sum,weighted_component_energy]

theorem planar_envelope_integrable (x y l W slope : ℝ) (hl : 0 < l) (hW : 0 < W) :
    Integrable (fun z : ℝ×ℝ =>
      lineEnvelope x l 1 z.1*lineEnvelope y W 1 (z.2-slope*z.1)) (volume.prod volume) := by
  have hprod := (integrable_lineEnvelope_one x l hl).mul_prod
    (integrable_lineEnvelope_one y W hW)
  simpa [slopeShear,Function.comp_def,sub_eq_add_neg] using
    (slopeShear_measurePreserving (-slope)).integrable_comp_of_integrable hprod

theorem integral_planar_envelope (x y l W slope : ℝ) (hl : 0 < l) (hW : 0 < W) :
    (∫ z : ℝ×ℝ, lineEnvelope x l 1 z.1*lineEnvelope y W 1 (z.2-slope*z.1)
      ∂volume.prod volume) = Real.pi^2*l*W := by
  have heq : (fun z : ℝ×ℝ =>
      lineEnvelope x l 1 z.1*lineEnvelope y W 1 (z.2-slope*z.1)) =
      (fun z : ℝ×ℝ => lineEnvelope x l 1 z.1*lineEnvelope y W 1 z.2) ∘
        slopeShear (-slope) := by
    funext z
    simp [slopeShear,sub_eq_add_neg]
  rw [heq]
  change (∫ z, (fun p : ℝ×ℝ => lineEnvelope x l 1 p.1*lineEnvelope y W 1 p.2)
    (slopeShear (-slope) z) ∂volume.prod volume) = _
  rw [integral_slopeShear (-slope)
    (fun p : ℝ×ℝ => lineEnvelope x l 1 p.1*lineEnvelope y W 1 p.2),integral_prod_mul,
    integral_lineEnvelope_one x l hl,integral_lineEnvelope_one y W hW]
  ring

theorem planar_fixed_scale_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (site : ι → ℤ×ℤ) (hinj : Function.Injective site)
    (a b l W slope C : ℝ) (hl : 0 < l) (hW : 0 < W)
    (henv : ∀ i k z, ‖f i k z‖ ≤ C*
      (lineEnvelope (a+l*(site i).1) l 1 z.1*
        lineEnvelope (b+W*(site i).2) W 1 (z.2-slope*z.1))) :
    (∫ z, ‖planarFixedSynthesis c f z‖^2 ∂volume.prod volume) ≤
      ((4*Real.pi)^2*C^2*Real.pi^2)*∑ i, ‖c i‖^2*l*W := by
  let weight := fun (i : ι) (z : ℝ×ℝ) =>
    lineEnvelope (a+l*(site i).1) l 1 z.1*
      lineEnvelope (b+W*(site i).2) W 1 (z.2-slope*z.1)
  have hi (i : ι) : Integrable (fun z => ‖c i‖^2*weight i z) (volume.prod volume) :=
    (planar_envelope_integrable _ _ l W slope hl hW).const_mul _
  have hp (z : ℝ×ℝ) : ‖planarFixedSynthesis c f z‖^2 ≤
      (4*Real.pi)^2*C^2*∑ i, ‖c i‖^2*weight i z := by
    apply planarFixedSynthesis_pointwise c f z (fun i => weight i z)
    · intro i
      dsimp [weight,lineEnvelope]
      positivity
    · positivity
    · exact injective_tile_lattice_overlap site hinj a b l W z.1
        (z.2-slope*z.1) hl.ne' hW.ne' (by decide) (by decide)
    · exact fun i k => henv i k z
  calc
    _ ≤ ∫ z, (4*Real.pi)^2*C^2*∑ i, ‖c i‖^2*weight i z ∂volume.prod volume :=
      integral_mono ((planarFixedSynthesis_memLp c f).integrable_norm_pow (by decide))
        ((integrable_finsetSum _ (fun i _ => hi i)).const_mul _) hp
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi i)]
      simp_rw [integral_const_mul]
      simp only [weight,integral_planar_envelope _ _ l W slope hl hW]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end LipschitzHilbert

end

end OAI
