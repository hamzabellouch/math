import OAI.Analysis.LipschitzHilbert.Estimates.DyadicSmoothEmbedding
import OAI.Analysis.LipschitzHilbert.Fourier.LineLowpassCell

namespace OAI

/-! The smooth Carleson product bound on every finite collection of
actual dyadic cells, with the actual smooth low-pass convolution. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem finite_smooth_product {ι : Type*} [Fintype ι]
    (grid : ℤ) (level pos : ι → ℤ)
    (hinj : ∀ i j, level i=level j → pos i=pos j → i=j)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B)
    (ratio : ℝ) (hratio : 0<ratio) (h : SchwartzMap ℝ ℂ) :
    (∑ i, ∫⁻ x in cell grid (level i) (pos i),
      ENNReal.ofReal (‖lineConvolution (lineProjectionKernel dyadicDifference (scale (level i))
        (scale_pos _).ne') f x‖^2)*
      ENNReal.ofReal (‖lineConvolution (lineProjectionKernel reassemblyLow (ratio*scale (level i))
        (mul_pos hratio (scale_pos _)).ne') h x‖^2))≤
      ENNReal.ofReal (dyadicCarlesonConstant*B^2)*
        ENNReal.ofReal (lineCellMaximalConstant reassemblyLow ratio)^2*
        ENNReal.ofReal (36*(∫ x, ‖h x‖^2)) := by
  let Q := fun i => cell grid (level i) (pos i)
  let low := fun i => lineConvolution
    (lineProjectionKernel reassemblyLow (ratio*scale (level i)) (mul_pos hratio (scale_pos _)).ne') h
  let E := lineCellMaximalConstant reassemblyLow ratio
  let M := threeGridMaximal (fun x => ‖h x‖)
  let v := fun i => sSup ((fun x => ‖low i x‖) '' Q i)
  have hE : 0≤E := lineCellMaximalConstant_nonneg _ _ hratio
  have hBdd (i : ι) : BddAbove ((fun x => ‖low i x‖) '' Q i) := by
    refine ⟨(∫ t, ‖lineProjectionKernel reassemblyLow (ratio*scale (level i))
      (mul_pos hratio (scale_pos _)).ne' t‖)*SchwartzMap.seminorm ℝ 0 0 h,?_⟩
    rintro _ ⟨x,_,rfl⟩
    exact lineConvolution_bound _ h (lineProjectionKernel _ _ _).integrable _
      (fun x => h.norm_le_seminorm ℝ x) x
  have hne (i : ι) : ((fun x => ‖low i x‖) '' Q i).Nonempty :=
    (cell_nonempty grid (level i) (pos i)).image _
  have hv (i : ι) : 0≤v i := by
    obtain ⟨x,hx⟩ := cell_nonempty grid (level i) (pos i)
    exact (norm_nonneg (low i x)).trans (le_csSup (hBdd i) ⟨x,hx,rfl⟩)
  have hlow (i : ι) (x : ℝ) (hx : x∈Q i) : ‖low i x‖≤v i :=
    le_csSup (hBdd i) ⟨x,hx,rfl⟩
  have hmax := lineProjection_cell_maximal reassemblyLow ratio hratio h h.continuous.measurable
    (h.memLp 2 volume) (SchwartzMap.seminorm ℝ 0 0 h) (fun x => h.norm_le_seminorm ℝ x)
  have hvM (i : ι) : ∀ᵐ x ∂volume.restrict (Q i), v i≤E*M x := by
    filter_upwards [ae_restrict_of_ae hmax,ae_restrict_mem (cell_measurable grid (level i) (pos i))] with x hx hxQ
    apply csSup_le (hne i)
    rintro _ ⟨y,hy,rfl⟩
    exact hx grid (level i) (pos i) hxQ y hy
  have hbound := dyadic_smooth_product_embedding grid level pos hinj f hfm B hB hfb
    low v hv (fun x => E*M x) ((threeGridMaximal_measurable _).const_mul E) hlow hvM
  apply hbound.trans
  have hm := threeGridMaximal_energy (h.memLp 2 volume).norm
  have he : (∫⁻ x, ENNReal.ofReal ((E*M x)^2))=
      ENNReal.ofReal E^2*(∫⁻ x, ENNReal.ofReal (M x^2)) := by
    simp_rw [mul_pow,ENNReal.ofReal_mul (sq_nonneg E),ENNReal.ofReal_pow hE]
    exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  rw [he]
  rw [mul_assoc]
  apply mul_le_mul' le_rfl
  apply mul_le_mul' le_rfl
  rw [←ofReal_integral_eq_lintegral_ofReal hm.1.integrable_sq
    (Filter.Eventually.of_forall (fun x => sq_nonneg (M x)))]
  exact ENNReal.ofReal_le_ofReal hm.2

end LipschitzHilbert.PacketRepresentation

end

end OAI
