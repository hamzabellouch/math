import OAI.Analysis.CircleDomains.Selection.VisitCardinality

namespace OAI

/-! Measurable multiplicity in a closed time relation. This allows visits to
be restricted to a tagged path's residual times and to a closed test interval. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section

namespace CircleDomainRigidity

variable {Z : Type*}

def timeCount (R : Set (Z × PathTime)) (z : Z) : ℝ≥0∞ :=
  ∑' t : PathTime, if (z, t) ∈ R then (1 : ℝ≥0∞) else 0

def timeWitnessSet (R : Set (Z × PathTime)) (n : ℕ) : Set Z :=
  {z | ∃ t : Fin n → PathTime, Injective t ∧ ∀ i, (z, t i) ∈ R}

def separatedTimeWitnessSet (R : Set (Z × PathTime)) (n : ℕ) (r : ℝ) : Set Z :=
  {z | ∃ t : SeparatedTimes n r, ∀ i, (z, t.val i) ∈ R}

theorem timeCount_eq_iSup (R : Set (Z × PathTime)) (z : Z) :
    timeCount R z = ⨆ n : ℕ, if z ∈ timeWitnessSet R n then (n : ℝ≥0∞) else 0 := by
  apply le_antisymm
  · rw [timeCount, ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    let E := F.filter (fun t => (z, t) ∈ R)
    let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
    have ht : z ∈ timeWitnessSet R (Fintype.card E) := by
      refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
      intro i
      exact (Finset.mem_filter.mp (e i).property).2
    have hb : (Fintype.card E : ℝ≥0∞) ≤
        ⨆ n : ℕ, if z ∈ timeWitnessSet R n then (n : ℝ≥0∞) else 0 := by
      exact (ite_eq_left ht).symm.le.trans (le_iSup
        (fun n : ℕ => if z ∈ timeWitnessSet R n then (n : ℝ≥0∞) else 0) _)
    simpa only [Finset.sum_boole, Fintype.card_coe] using hb
  · apply iSup_le
    intro n
    split
    · rename_i hn
      obtain ⟨t, ht, hR⟩ := hn
      calc
        (n : ℝ≥0∞) = ∑' i : Fin n, if (z, t i) ∈ R then (1 : ℝ≥0∞) else 0 := by
          simp only [hR, ite_true, tsum_fintype, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one]
        _ ≤ timeCount R z := ENNReal.tsum_comp_le_tsum_of_injective ht
          (fun t : PathTime => if (z, t) ∈ R then 1 else 0)
    · exact bot_le

theorem timeWitnessSet_eq_iUnion (R : Set (Z × PathTime)) (n : ℕ) :
    timeWitnessSet R n = ⋃ m : ℕ, separatedTimeWitnessSet R n (1 / ((m : ℝ) + 1)) := by
  ext z
  constructor
  · rintro ⟨t, ht, hR⟩
    obtain ⟨m, hm⟩ := exists_reciprocal_separation t ht
    exact mem_iUnion.mpr ⟨m, ⟨⟨t, hm⟩, hR⟩⟩
  · intro h
    obtain ⟨m, t, hR⟩ := mem_iUnion.mp h
    refine ⟨t.val, ?_, hR⟩
    intro i j hij
    by_contra hne
    have hd := t.property i j hne
    rw [hij, dist_self] at hd
    have hp : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith

variable [TopologicalSpace Z]

theorem isClosed_separatedTimeWitnessSet {R : Set (Z × PathTime)} (hR : IsClosed R)
    (n : ℕ) (r : ℝ) : IsClosed (separatedTimeWitnessSet R n r) := by
  let H : Set (Z × SeparatedTimes n r) := {q | ∀ i, (q.1, q.2.val i) ∈ R}
  have hH : IsClosed H := by
    change IsClosed {q : Z × SeparatedTimes n r | ∀ i, (q.1, q.2.val i) ∈ R}
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => hR.preimage (continuous_fst.prodMk
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))
  have hproj : Prod.fst '' H = separatedTimeWitnessSet R n r := by
    ext z
    constructor
    · rintro ⟨⟨z, t⟩, ht, rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨(z, t), ht, rfl⟩
  rw [← hproj]
  exact isClosedMap_fst_of_compactSpace H hH

variable [MeasurableSpace Z] [BorelSpace Z]

theorem measurable_timeCount {R : Set (Z × PathTime)} (hR : IsClosed R) :
    Measurable (timeCount R) := by
  change Measurable (fun z => timeCount R z)
  simp_rw [timeCount_eq_iSup]
  apply Measurable.iSup
  intro n
  apply measurable_const.piecewise _ measurable_const
  rw [timeWitnessSet_eq_iUnion]
  exact MeasurableSet.iUnion fun m =>
    (isClosed_separatedTimeWitnessSet hR n (1 / ((m : ℝ) + 1))).measurableSet

end CircleDomainRigidity

end

end OAI
