import Mathlib
import OAI.Computability.VertexCover.Analysis.PoincareOne
import OAI.Computability.VertexCover.Analysis.RoundingError

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.GridCoupling
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem intervalLaw_eq_Ico : VertexCover.Cube.intervalLaw =
    (1/2 : ℝ≥0∞) • volume.restrict (Set.Ico (-1:ℝ) 1) := by
  unfold VertexCover.Cube.intervalLaw
  rw [Measure.restrict_congr_set (Ico_ae_eq_Icc (μ := volume)).symm]

theorem index_atom (p : ℕ) (hp : 0 < p) (i : Fin p) :
    VertexCover.Cube.intervalLaw (index p hp ⁻¹' {i}) = (p:ℝ≥0∞)⁻¹ := by
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  rw [intervalLaw_eq_Ico, Measure.smul_apply,
    Measure.restrict_apply ((index_measurable p hp) (measurableSet_singleton i)),
    preimage_cell p hp i, Real.volume_Ico]
  have he : (-1 + 2*((i:ℝ)+1)/p) - (-1 + 2*(i:ℝ)/p) = 2/p := by ring
  rw [he]
  have hpE : (p:ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.ne'
  have hpT : (p:ℝ≥0∞) ≠ ⊤ := by finiteness
  simp only [smul_eq_mul]
  rw [ENNReal.ofReal_div_of_pos hpR]
  simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast, div_eq_mul_inv]
  rw [one_mul, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

theorem index_measurePreserving (p : ℕ) (hp : 0 < p) :
    MeasurePreserving (index p hp) VertexCover.Cube.intervalLaw
      (uniformOn (Set.univ : Set (Fin p))) := by
  refine ⟨index_measurable p hp, Measure.ext_of_singleton (fun i => ?_)⟩
  rw [Measure.map_apply (index_measurable p hp) (measurableSet_singleton i),
    index_atom p hp i, uniformOn_univ]
  simp

theorem rounding_error_ae (p : ℕ) (hp : 0 < p) :
    ∀ᵐ x ∂VertexCover.Cube.intervalLaw, |x - midpoint p (index p hp x)| ≤ 1/p := by
  have ha : ∀ᵐ x ∂VertexCover.Cube.intervalLaw, x ∈ Set.Ico (-1:ℝ) 1 := by
    rw [intervalLaw_eq_Ico]
    exact (Measure.ae_ennreal_smul_measure_iff (by norm_num : (1/2:ℝ≥0∞) ≠ 0)).mpr
      (ae_restrict_mem measurableSet_Ico)
  filter_upwards [ha] with x hx
  exact rounding_error p hp hx

end VertexCover.GridCoupling
namespace VertexCover.Cube
open MeasureTheory
open scoped ENNReal

instance intervalLaw_negInvariant : intervalLaw.IsNegInvariant := by
  have he : (Neg.neg : ℝ → ℝ) ⁻¹' Set.Icc (-1:ℝ) 1 = Set.Icc (-1:ℝ) 1 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage (s := Set.Icc (-1:ℝ) 1) measurableSet_Icc
  rw [he] at h
  exact ⟨(h.smul_measure (1/2 : ℝ≥0∞)).map_eq⟩

instance law_negInvariant (ι : Type*) [Fintype ι] : (law ι).IsNegInvariant := by
  unfold law
  infer_instance

end VertexCover.Cube

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
