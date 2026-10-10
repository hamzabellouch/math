import OAI.Analysis.KadisonKastler.RandomWalkPathAction
import Mathlib.Probability.Independence.InfinitePi

namespace OAI

/-! # Independence of the first increment and the remaining random walk -/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable {G : Type*} [MeasurableSpace G]

theorem independent_first_increment_tail (μ : Measure G) [IsProbabilityMeasure μ] :
    IndepFun (fun x : ℕ → G => x 0) (fun x : ℕ → G => fun n => x (n + 1))
      (Measure.infinitePi (fun _ : ℕ => μ)) := by
  let m : ℕ → MeasurableSpace (ℕ → G) := fun n =>
    MeasurableSpace.comap (fun x => x n) inferInstance
  have hi : iIndep m (Measure.infinitePi (fun _ : ℕ => μ)) :=
    iIndepFun_infinitePi (X := fun _ (x : G) => x) (fun _ => measurable_id)
  have hm (n : ℕ) : m n ≤ (inferInstance : MeasurableSpace (ℕ → G)) :=
    (measurable_pi_apply n).comap_le
  have hh := indep_iSup_of_disjoint hm hi
    (show Disjoint ({0} : Set ℕ) {n | n ≠ 0} by simp)
  have hleft : m 0 ≤ ⨆ n ∈ ({0} : Set ℕ), m n :=
    le_iSup_of_le 0 (le_iSup_of_le (Set.mem_singleton 0) le_rfl)
  have hright : MeasurableSpace.comap (fun x : ℕ → G => fun n => x (n + 1)) inferInstance ≤
      ⨆ n ∈ {n : ℕ | n ≠ 0}, m n := by
    rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro n
    exact le_iSup_of_le (n + 1) (le_iSup_of_le (by change n + 1 ≠ 0; omega) le_rfl)
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hh hleft) hright

theorem iid_first_increment_tail_law (μ : Measure G) [IsProbabilityMeasure μ] :
    (Measure.infinitePi (fun _ : ℕ => μ)).map
      (fun x : ℕ → G => (x 0, fun n => x (n + 1))) =
      μ.prod (Measure.infinitePi (fun _ : ℕ => μ)) := by
  have htail : Measurable (fun x : ℕ → G => fun n => x (n + 1)) :=
    Measurable.of_eval (fun n => measurable_pi_apply (n + 1))
  rw [(independent_first_increment_tail μ).map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable htail.aemeasurable]
  rw [Measure.infinitePi_map_eval]
  congr 1
  exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h => Nat.add_right_cancel h)

variable [Group G] [Countable G] [MeasurableSingletonClass G]

def randomWalkSplit (x : RandomWalkPath G) : (G × G) × (ℕ → G) :=
  ((x.1, x.2 0), fun n => x.2 (n + 1))

omit [Group G] [Countable G] [MeasurableSingletonClass G] in
theorem randomWalkSplit_measurable : Measurable (randomWalkSplit (G := G)) := by
  exact (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)).prodMk
    (Measurable.of_eval (fun n => (measurable_pi_apply (n + 1)).comp measurable_snd))

theorem randomWalkSplit_law :
    (randomWalkPathLaw G).map randomWalkSplit =
      ((symmetricRandomWalkLaw G).prod (symmetricRandomWalkLaw G)).prod
        (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)) := by
  let μ := symmetricRandomWalkLaw G
  let ν := Measure.infinitePi (fun _ : ℕ => μ)
  let h : (ℕ → G) → G × (ℕ → G) := fun x => (x 0, fun n => x (n + 1))
  have hh : Measurable h := by fun_prop
  have he : (μ.prod ν).map (Prod.map id h) = μ.prod (μ.prod ν) := by
    rw [← Measure.map_prod_map μ ν measurable_id hh, Measure.map_id]
    exact congrArg (Measure.prod μ) (iid_first_increment_tail_law μ)
  have ha : (μ.prod (μ.prod ν)).map MeasurableEquiv.prodAssoc.symm = (μ.prod μ).prod ν := by
    rw [← Measure.prodAssoc_prod, Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [MeasurableEquiv.symm_comp_self, Measure.map_id]
  change (μ.prod ν).map (MeasurableEquiv.prodAssoc.symm ∘ Prod.map id h) = _
  rw [← Measure.map_map (by fun_prop) (measurable_id.prodMap hh), he]
  exact ha

theorem randomWalkAdvance_law :
    (randomWalkPathLaw G).map (randomWalkAdvance G) =
      (randomWalkConvolution G).prod
        (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)) := by
  let μ := symmetricRandomWalkLaw G
  let ν := Measure.infinitePi (fun _ : ℕ => μ)
  let m : G × G → G := fun p => p.1 * p.2
  have hm : Measurable m := measurable_of_countable _
  change (randomWalkPathLaw G).map (Prod.map m id ∘ randomWalkSplit) = _
  rw [← Measure.map_map (hm.prodMap measurable_id) randomWalkSplit_measurable,
    randomWalkSplit_law, ← Measure.map_prod_map (μ.prod μ) ν hm measurable_id, Measure.map_id]
  rfl

theorem randomWalkAdvance_quasi :
    Measure.QuasiMeasurePreserving (randomWalkAdvance G) (randomWalkPathLaw G)
      (randomWalkPathLaw G) := by
  refine ⟨randomWalkAdvance_measurable G, ?_⟩
  rw [randomWalkAdvance_law]
  exact Measure.AbsolutelyContinuous.prod (randomWalkConvolution_absolutelyContinuous_law (G := G))
    (Measure.AbsolutelyContinuous.refl _)

end

end KadisonKastler

end OAI
