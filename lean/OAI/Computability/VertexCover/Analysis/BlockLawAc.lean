import Mathlib
import OAI.Computability.VertexCover.Analysis.PoincareOne

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
namespace VertexCover.Cube
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem law_eq_restrict_volume (ι : Type*) [Fintype ι] :
    law ι = (1/2 : ℝ≥0∞) ^ Fintype.card ι •
    volume.restrict (Set.univ.pi (fun _ : ι => Set.Icc (-1 : ℝ) 1)) := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs),
    ← Set.pi_inter_distrib, volume_pi_pi]
  simp only [intervalLaw, Measure.smul_apply, Measure.restrict_apply (hs _),
    smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem law_ac (ι : Type*) [Fintype ι] : law ι ≪ volume := by
  rw [law_eq_restrict_volume]
  intro s hs
  have hz : volume.restrict (Set.univ.pi (fun _ : ι => Set.Icc (-1 : ℝ) 1)) s = 0 :=
    le_antisymm ((Measure.restrict_le_self s).trans_eq hs) zero_le
  simp only [Measure.smul_apply, hz, smul_zero]

end VertexCover.Cube

namespace VertexCover.Cube
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def blockLaw (ι κ : Type*) [Fintype ι] [Fintype κ] :
    Measure (ι → κ → ℝ) := Measure.pi (fun _ : ι => law κ)

instance blockLaw_probability (ι κ : Type*) [Fintype ι] [Fintype κ] :
    IsProbabilityMeasure (blockLaw ι κ) := by
  unfold blockLaw
  infer_instance

theorem blockLaw_eq_restrict_volume (ι κ : Type*) [Fintype ι] [Fintype κ] :
    blockLaw ι κ = ((1/2 : ℝ≥0∞) ^ Fintype.card κ) ^ Fintype.card ι •
      volume.restrict (Set.univ.pi (fun _ : ι =>
        Set.univ.pi (fun _ : κ => Set.Icc (-1 : ℝ) 1))) := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs),
    ← Set.pi_inter_distrib, volume_pi_pi]
  simp only [law_eq_restrict_volume, Measure.smul_apply,
    Measure.restrict_apply (hs _), smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

theorem blockLaw_ac (ι κ : Type*) [Fintype ι] [Fintype κ] :
    blockLaw ι κ ≪ volume := by
  rw [blockLaw_eq_restrict_volume]
  intro s hs
  have hz : volume.restrict (Set.univ.pi (fun _ : ι =>
      Set.univ.pi (fun _ : κ => Set.Icc (-1 : ℝ) 1))) s = 0 :=
    le_antisymm ((Measure.restrict_le_self s).trans_eq hs) zero_le
  simp only [Measure.smul_apply, hz, smul_zero]

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
