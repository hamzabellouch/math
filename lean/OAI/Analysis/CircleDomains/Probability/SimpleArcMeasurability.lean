import OAI.Analysis.CircleDomains.Probability.PathHitLaws
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Borel simple-path and image-containment relations for the measurable
terminal-arc selection used in the stream construction. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def pathsWithSeparatedCollision (r : ℝ) : Set C(PathTime, X) :=
  {γ | ∃ s t : PathTime, r ≤ dist s t ∧ γ s = γ t}

theorem isClosed_pathsWithSeparatedCollision (r : ℝ) :
    IsClosed (pathsWithSeparatedCollision (X := X) r) := by
  let K : Set (C(PathTime, X) × (PathTime × PathTime)) :=
    {p | r ≤ dist p.2.1 p.2.2 ∧ p.1 p.2.1 = p.1 p.2.2}
  have hK : IsClosed K :=
    (isClosed_le continuous_const
      ((continuous_fst.comp continuous_snd).dist (continuous_snd.comp continuous_snd))).inter
      (isClosed_eq
        (continuous_eval.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
        (continuous_eval.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
  have he : Prod.fst '' K = pathsWithSeparatedCollision (X := X) r := by
    ext γ
    constructor
    · rintro ⟨⟨δ, s, t⟩, h, rfl⟩
      exact ⟨s, t, h⟩
    · rintro ⟨s, t, h⟩
      exact ⟨(γ, s, t), h, rfl⟩
  rw [← he]
  exact isClosedMap_fst_of_compactSpace K hK

theorem injective_path_iff_no_separated_collision (γ : C(PathTime, X)) :
    Injective γ ↔ ∀ n : ℕ, γ ∉ pathsWithSeparatedCollision (1 / ((n : ℝ) + 1)) := by
  constructor
  · intro h n ⟨s, t, hst, he⟩
    rw [h he, dist_self] at hst
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact hp.not_ge hst
  · intro h s t he
    by_contra hn
    have hd : 0 < dist s t := dist_pos.mpr hn
    obtain ⟨n, hn⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (gt_mem_nhds hd)).exists
    exact h n ⟨s, t, hn.le, he⟩

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_injective_paths : MeasurableSet {γ : C(PathTime, X) | Injective γ} := by
  have he : {γ : C(PathTime, X) | Injective γ} =
      ⋂ n : ℕ, (pathsWithSeparatedCollision (1 / ((n : ℝ) + 1)))ᶜ := by
    ext γ
    simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff,
      injective_path_iff_no_separated_collision]
  rw [he]
  exact MeasurableSet.iInter fun n => (isClosed_pathsWithSeparatedCollision _).measurableSet.compl

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem isClosed_path_image_containment :
    IsClosed {p : C(PathTime, X) × C(PathTime, X) | range p.2 ⊆ range p.1} := by
  have he : {p : C(PathTime, X) × C(PathTime, X) | range p.2 ⊆ range p.1} =
      ⋂ t : PathTime, {p | (p.1, p.2 t) ∈ pathHitSet} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, range_subset_iff, pathHitSet, mem_range]
  rw [he]
  exact isClosed_iInter fun t => isClosed_pathHitSet.preimage
    (continuous_fst.prodMk ((continuous_eval_const t).comp continuous_snd))

end CircleDomainRigidity

end

end OAI
