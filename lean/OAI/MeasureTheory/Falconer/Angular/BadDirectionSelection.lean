import OAI.MeasureTheory.Falconer.Angular.BadDirectionEnvelope

namespace OAI

/-! # A measurable incidence witnessing every direction in the finite envelope -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem exists_finite_bad_incidence (μ : Measure (Space d)) [SFinite μ]
    (G : Finset (Space d)) (N : ℕ) (D R : ℝ) (a : ℝ≥0∞) :
    ∃ J : Sphere d → Finset (Space d), ∃ F : Set (Space d × Sphere d),
      MeasurableSet F ∧ (∀ w, J w ⊆ G ∧ (J w).card ≤ N) ∧
      (∀ x, MeasurableSet {w | x ∈ J w}) ∧
      (∀ p ∈ F, ‖p.1‖ ≤ D) ∧
      (∀ p ∈ F, ∃ x ∈ J p.2, ‖perpendicularPart (p.2:Space d) (p.1-x)‖ ≤ R) ∧
      ∀ (ν : Measure (Sphere d)) [SFinite ν],
        a*ν (finiteBadDirections μ G N D R a) ≤ (μ.prod ν) F := by
  classical
  let B := finiteBadDirections μ G N D R a
  have hB : MeasurableSet B := finiteBadDirections_measurable μ G N D R a
  obtain ⟨C,hC,hCs⟩ := bounded_finset_enumeration G N
  have hfind : ∀ w : Sphere d, ∃ n : ℕ,
      w ∉ B ∨ a ≤ μ (boundedTubeUnion D R (C n) w) := by
    intro w
    by_cases hw : w ∈ B
    · obtain ⟨J,hJG,hJN,hm⟩ := hw
      obtain ⟨n,rfl⟩ := hCs J (Finset.mem_powerset.mp hJG) hJN
      exact ⟨n,Or.inr hm⟩
    · exact ⟨0,Or.inl hw⟩
  let j : Sphere d → ℕ := fun w => Nat.find (hfind w)
  have hj : Measurable j := measurable_find hfind (fun n => hB.compl.union
    (measurableSet_le measurable_const (boundedTubeUnion_mass_measurable μ D R (C n))))
  let J : Sphere d → Finset (Space d) := fun w => C (j w)
  have hJ (x : Space d) : MeasurableSet {w | x ∈ J w} :=
    hj ((Set.to_countable {n | x ∈ C n}).measurableSet)
  let F : Set (Space d × Sphere d) := {p | p.2 ∈ B ∧ p.1 ∈ boundedTubeUnion D R (J p.2) p.2}
  have hF : MeasurableSet F := by
    have ht := finite_tube_cover_relation_measurable G J hJ (fun w => (hC (j w)).1) R
    have hb : MeasurableSet {p : Space d × Sphere d | ‖p.1‖ ≤ D} :=
      measurableSet_le (by fun_prop) measurable_const
    exact (hB.preimage measurable_snd).inter (hb.inter ht)
  refine ⟨J,F,hF,(fun w => hC (j w)),hJ,(fun _ hp => hp.2.1),(fun _ hp => hp.2.2),?_⟩
  intro ν _
  have hbound (w : Sphere d) : B.indicator (fun _ => a) w ≤ μ {x | (x,w) ∈ F} := by
    by_cases hw : w ∈ B
    · rw [indicator_of_mem hw]
      have hm := (Nat.find_spec (hfind w)).resolve_left (not_not.mpr hw)
      have he : {x | (x,w) ∈ F} = boundedTubeUnion D R (J w) w := by
        ext x
        simp only [F,mem_ofPred_eq,hw,true_and]
      rw [he]
      exact hm
    · rw [indicator_of_notMem hw]
      exact bot_le
  rw [Measure.prod_apply_symm hF]
  calc
    _ = ∫⁻ w, B.indicator (fun _ => a) w ∂ν := by
      rw [lintegral_indicator hB,lintegral_const,Measure.restrict_apply_univ]
    _ ≤ _ := lintegral_mono hbound

end Falconer

end OAI
