import Mathlib
import OAI.Computability.VertexCover.Analysis.OwnPrivateListsDecoding
import OAI.Computability.VertexCover.Analysis.OwnFiberTower

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
namespace VertexCover.Average
open MeasureTheory

theorem selected_sum_measurable {Ω K : Type*} [MeasurableSpace Ω] [Fintype K] [DecidableEq K]
    (L : Ω → List K) (hL : ∀ k, MeasurableSet {x | k ∈ L x})
    (f : Ω → K → ℝ) (hf : ∀ k, Measurable (fun x => f x k)) :
    Measurable (fun x => ∑ k ∈ (L x).toFinset, f x k) := by
  classical
  have he : ∀ x, (L x).toFinset = Finset.univ.filter (fun k => k ∈ L x) := by
    intro x; ext k; simp
  simp_rw [he, Finset.sum_filter]
  exact Finset.measurable_sum _ (fun k _ => Measurable.ite (hL k) (hf k) measurable_const)

end VertexCover.Average

namespace VertexCover.LabelCover
open MeasureTheory

noncomputable def privateMass (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (β : ℝ)
    (hidden : Φ.HiddenSeeds J) (s : Φ.BatchWeights J) (j : J) : ℝ := by
  classical
  let i := Φ.query (Φ.spliceSeeds J frozen hidden) j
  exact ∑ a ∈ (Φ.ownList J frozen c0 A hA j i (s j) β).toFinset,
    |Φ.canonicalGradient (Φ.spliceSeeds J frozen hidden) J c0 A hA s j (i.slot a)|

theorem privateMass_nonneg (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (β : ℝ)
    (hidden : Φ.HiddenSeeds J) (s : Φ.BatchWeights J) (j : J) :
    0 ≤ Φ.privateMass J frozen c0 A hA β hidden s j := by
  unfold privateMass
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem privateMass_le_one (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (β : ℝ)
    (hidden : Φ.HiddenSeeds J) (s : Φ.BatchWeights J) (j : J) :
    Φ.privateMass J frozen c0 A hA β hidden s j ≤ 1 := by
  classical
  let i := Φ.query (Φ.spliceSeeds J frozen hidden) j
  let L := (Φ.ownList J frozen c0 A hA j i (s j) β).toFinset
  change (∑ a ∈ L, |Φ.canonicalGradient _ J c0 A hA s j (i.slot a)|) ≤ 1
  calc
    _ = ∑ k ∈ L.image i.slot, |Φ.canonicalGradient _ J c0 A hA s j k| := by
      rw [Finset.sum_image i.slot_injective.injOn]
    _ ≤ ∑ k, |Φ.canonicalGradient _ J c0 A hA s j k| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => abs_nonneg _)
    _ ≤ 1 := Φ.canonicalGradient_block_bound _ J c0 A hA s j

theorem privateMass_measurable (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (β : ℝ)
    (hidden : Φ.HiddenSeeds J) (j : J) :
    Measurable (fun s => Φ.privateMass J frozen c0 A hA β hidden s j) := by
  classical
  let i := Φ.query (Φ.spliceSeeds J frozen hidden) j
  apply VertexCover.Average.selected_sum_measurable
  · intro a
    exact (Φ.ownList_membership_measurable J frozen c0 A hA j i β a).preimage
      (measurable_pi_apply j)
  · intro a
    exact ((measurable_pi_apply (i.slot a)).comp ((measurable_pi_apply j).comp
      (Φ.canonicalGradient_measurable _ J c0 A hA))).abs

theorem privateMass_integrable (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (β : ℝ)
    (hidden : Φ.HiddenSeeds J) (j : J) :
    Integrable (fun s => Φ.privateMass J frozen c0 A hA β hidden s j) (Φ.batchLaw J) := by
  apply Integrable.of_bound (Φ.privateMass_measurable J frozen c0 A hA β hidden j).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro s
  rw [Real.norm_eq_abs, abs_of_nonneg (Φ.privateMass_nonneg J frozen c0 A hA β hidden s j)]
  exact Φ.privateMass_le_one J frozen c0 A hA β hidden s j

theorem ownEnergy_le_resampled_mass (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (s : Fin (Φ.WeightDimension d) → ℝ) {β : ℝ} (hβ : 0 < β) :
    VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      ∑ k, (Φ.ownGradient J frozen c0 A hA j
        (Φ.query (Φ.spliceSeeds J frozen hidden) j) s k)^2) ≤ β/2 +
    VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      ∫ other, Φ.privateMass J frozen c0 A hA β hidden
        (Function.update other j s) j ∂Φ.batchLaw J) := by
  classical
  let : Nonempty (Fin Φ.M) := ⟨⟨0, Φ.M_pos⟩⟩
  let F : Φ.Query d → Φ.HiddenSeeds J → ℝ := fun i hidden =>
    ∫ other, ∑ a ∈ (Φ.ownList J frozen c0 A hA j i s β).toFinset,
      |Φ.canonicalGradient (Φ.spliceSeeds J frozen hidden) J c0 A hA
        (Function.update other j s) j (i.slot a)| ∂Φ.batchLaw J
  have h := VertexCover.finiteMean_mono (fun hidden : Φ.HiddenSeeds J =>
    Φ.ownGradient_energy_le_averaged_mass J frozen c0 A hA j
      (Φ.query (Φ.spliceSeeds J frozen hidden) j) s hβ)
  rw [VertexCover.finiteMean_add, VertexCover.finiteMean_const] at h
  change _ ≤ β/2 + VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
    VertexCover.finiteMean (fun hidden' : Φ.ownFiber J frozen j
      (Φ.query (Φ.spliceSeeds J frozen hidden) j) =>
      F (Φ.query (Φ.spliceSeeds J frozen hidden) j) hidden')) at h
  rw [Φ.ownFiber_tower] at h
  simpa only [privateMass, Function.update_self] using h

theorem privateMass_sum_le_hits (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (β : ℝ)
    (hidden : Φ.HiddenSeeds J) (s : Φ.BatchWeights J) :
    (∑ j : J, Φ.privateMass J frozen c0 A hA β hidden s j) ≤
      Φ.listHitMaximum (Φ.ownPrivateLists J frozen c0 A hA s β)
        (Φ.spliceSeeds J frozen hidden) J := by
  classical
  have h := Φ.canonicalGradient_listMass (Φ.spliceSeeds J frozen hidden) J c0 A hA s
    (Φ.ownPrivateLists J frozen c0 A hA s β)
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  unfold privateMass ownPrivateLists
  have hpos : (Φ.query (Φ.spliceSeeds J frozen hidden) j).1 ∈ J := j.property
  rw [dite_eq_left hpos]
  rw [show (⟨(Φ.query (Φ.spliceSeeds J frozen hidden) j).1, hpos⟩ : J) = j from Subtype.ext rfl]

end VertexCover.LabelCover


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
