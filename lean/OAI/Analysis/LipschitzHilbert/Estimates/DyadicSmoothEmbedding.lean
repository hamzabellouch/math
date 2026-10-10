import OAI.Analysis.LipschitzHilbert.Geometry.DyadicProjectionPacking
import OAI.Analysis.LipschitzHilbert.Estimates.CarlesonProductEnergy

namespace OAI

/-! The actual smooth projection Carleson coefficients in the finite
product embedding. The low-pass majorant is allowed to hold almost everywhere. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem dyadic_smooth_product_embedding {ι : Type*} [Fintype ι]
    (q : ℤ) (level pos : ι → ℤ)
    (hinj : ∀ i j, level i=level j → pos i=pos j → i=j)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B)
    (h : ι → ℝ → ℂ) (v : ι → ℝ) (hv : ∀ i, 0≤v i)
    (G : ℝ → ℝ) (hG : Measurable G)
    (hh : ∀ i, ∀ x∈cell q (level i) (pos i), ‖h i x‖≤v i)
    (hvG : ∀ i, ∀ᵐ x ∂volume.restrict (cell q (level i) (pos i)), v i≤G x) :
    (∑ i, ∫⁻ x in cell q (level i) (pos i),
      ENNReal.ofReal (‖lineConvolution (lineProjectionKernel dyadicDifference (scale (level i))
        (scale_pos _).ne') f x‖^2)*ENNReal.ofReal (‖h i x‖^2))≤
      ENNReal.ofReal (dyadicCarlesonConstant*B^2)*∫⁻ x, ENNReal.ofReal (G x^2) := by
  classical
  let Q := fun i => cell q (level i) (pos i)
  let w := fun i x => ‖lineConvolution
    (lineProjectionKernel dyadicDifference (scale (level i)) (scale_pos _).ne') f x‖^2
  have hw (i : ι) : IntegrableOn (w i) (Q i) :=
    lineConvolution_integrableOn_sq _ f hfm B hfb _ measure_Ico_lt_top.ne
  have he (i : ι) : (∫⁻ x in Q i, ENNReal.ofReal (w i x))=ENNReal.ofReal (∫ x in Q i, w i x) :=
    (ofReal_integral_eq_lintegral_ofReal (hw i) (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
  have hcar (j : ι) : (∑ i, if Q i⊆Q j then ∫⁻ x in Q i, ENNReal.ofReal (w i x) else 0)≤
      ENNReal.ofReal (dyadicCarlesonConstant*B^2)*volume (Q j) := by
    let I := Finset.univ.filter (fun i => Q i⊆Q j)
    have hr := dyadic_projection_carleson_packing I q (level j) (pos j) level pos
      (fun i _ k _ => hinj i k) (fun i hi => (Finset.mem_filter.mp hi).2) f hfm B hB hfb
    have hs : (∑ i, if Q i⊆Q j then ∫⁻ x in Q i, ENNReal.ofReal (w i x) else 0)=
        ENNReal.ofReal (∑ i∈I, ∫ x in Q i, w i x) := by
      simp only [he,←Finset.sum_filter]
      exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg (fun _ => sq_nonneg _))).symm
    rw [hs]
    apply (ENNReal.ofReal_le_ofReal hr).trans_eq
    rw [ENNReal.ofReal_mul (mul_nonneg dyadicCarlesonConstant_pos.le (sq_nonneg B))]
    congr 1
    rw [←cell_length q (level j) (pos j)]
    exact ENNReal.ofReal_toReal measure_Ico_lt_top.ne
  exact carleson_product_energy_ae Q volume (fun i => cell_measurable q (level i) (pos i))
    (fun i j => cells_nested_or_disjoint q (level i) (level j) (pos i) (pos j))
    (fun i x => ENNReal.ofReal (w i x)) (ENNReal.ofReal (dyadicCarlesonConstant*B^2))
    hcar h v hv G hG hh hvG

end LipschitzHilbert.PacketRepresentation

end

end OAI
