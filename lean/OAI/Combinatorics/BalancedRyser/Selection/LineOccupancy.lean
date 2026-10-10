import OAI.Combinatorics.BalancedRyser.Candidates.Candidates
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Probability.VacantBins

namespace OAI

namespace Balanced.LineOccupancy

open scoped BigOperators

variable {F : Type*} [Field F]

def transverseHitEquiv (l : Line F) (d : Direction F) (hne : l.1 ≠ d) :
    F ≃ {p : Point F // OnLine p l} where
  toFun a := ⟨lineIntersection l (d, a), onLine_lineIntersection_left l (d, a) hne⟩
  invFun p := lineEval d p.val
  left_inv a := onLine_lineIntersection_right l (d, a) hne
  right_inv p := by
    apply Subtype.ext
    apply common_point_eq_of_lines_ne l (d, lineEval d p.val)
      (fun h => hne (congrArg Prod.fst h))
    · exact onLine_lineIntersection_left _ _ hne
    · exact onLine_lineIntersection_right _ _ hne
    · exact p.property
    · rfl

theorem transverseHitEquiv_eq_iff (l : Line F) (d : Direction F)
    (hne : l.1 ≠ d) (a : F) (p : {p : Point F // OnLine p l}) :
    transverseHitEquiv l d hne a = p ↔ OnLine p.val (d, a) := by
  rw [← Equiv.eq_symm_apply]
  change a = lineEval d p.val ↔ lineEval d p.val = a
  exact eq_comm

variable [Fintype F] [DecidableEq F]

abbrev TransverseDirections (l : Line F) := {d : Direction F // d ≠ l.1}

omit [Field F] in
@[simp] theorem card_transverseDirections (l : Line F) :
    Fintype.card (TransverseDirections l) = Fintype.card F := by
  simp [TransverseDirections, Fintype.card_subtype_compl]

def hitAssignmentsEquiv (l : Line F) :
    (TransverseDirections l → F) ≃
      (TransverseDirections l → {p : Point F // OnLine p l}) :=
  Equiv.piCongrRight fun d => transverseHitEquiv l d.val (Ne.symm d.property)

noncomputable def unhitCount (l : Line F) (a : TransverseDirections l → F) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : {p : Point F // OnLine p l} =>
    ∀ d : TransverseDirections l, ¬ OnLine p.val (d.val, a d))).card

theorem unhitCount_eq_missedCount (l : Line F) (a : TransverseDirections l → F) :
    unhitCount l a = VacantBins.missedCount (hitAssignmentsEquiv l a) := by
  classical
  unfold unhitCount VacantBins.missedCount
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, VacantBins.mem_missed]
  apply forall_congr'
  intro d
  exact not_congr (transverseHitEquiv_eq_iff l d.val (Ne.symm d.property) (a d) p).symm

theorem unhitCount_eq_filter_card (l : Line F) (a : TransverseDirections l → F) :
    unhitCount l a = ((linePoints l).filter
      (fun p => ∀ d : TransverseDirections l, ¬ OnLine p (d.val, a d))).card := by
  classical
  unfold unhitCount
  refine Finset.card_bij (fun p _ => p.val) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_filter, linePoints, Finset.mem_univ, true_and]
    exact ⟨p.property, hp⟩
  · intro p hp r hr h
    exact Subtype.ext h
  · intro p hp
    simp only [Finset.mem_filter, linePoints, Finset.mem_univ, true_and] at hp
    refine ⟨⟨p, hp.1⟩, ?_, rfl⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hp.2

def transverseOffsets (l : Line F) (M : MergedPairs F) : TransverseDirections l → F :=
  fun d => M d.val true

theorem unhitCount_eq_initiallyRetained (l : Line F) (M : MergedPairs F)
    (hl : l ∉ initialDeletedLines M) :
    unhitCount l (transverseOffsets l M) = (linePoints l ∩ initiallyRetained M).card := by
  classical
  rw [unhitCount_eq_filter_card]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_inter, initiallyRetained,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, ht⟩
    refine ⟨hp, ?_⟩
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨d, _, rfl⟩
    by_cases hd : d = l.1
    · intro hpd
      have hpl : OnLine p l := (Finset.mem_filter.mp hp).2
      have heq : l = constituent M d true :=
        eq_of_onLine_same_direction p l (constituent M d true) hd.symm hpl hpd
      apply hl
      rw [heq]
      exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩
    · exact ht ⟨d, hd⟩
  · rintro ⟨hp, ht⟩
    refine ⟨hp, ?_⟩
    intro d
    exact ht (constituent M d.val true)
      (Finset.mem_image.mpr ⟨d.val, Finset.mem_univ _, rfl⟩)

theorem uniformMean_unhitCount (l : Line F) :
    VacantBins.uniformMean (fun a : TransverseDirections l → F => (unhitCount l a : ℝ)) =
      (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F := by
  classical
  let : Nonempty {p : Point F // OnLine p l} := ⟨(linePointsEquiv l).symm 0⟩
  simp_rw [unhitCount_eq_missedCount]
  rw [VacantBins.uniformMean_equiv (hitAssignmentsEquiv l)
    (fun f => (VacantBins.missedCount f : ℝ))]
  rw [VacantBins.uniformMean_missedCount, card_transverseDirections,
    Fintype.card_congr (linePointsEquiv l)]

theorem integral_unhitCount (l : Line F)
    [MeasurableSpace (TransverseDirections l → F)]
    [MeasurableSingletonClass (TransverseDirections l → F)] :
    (∫ a : TransverseDirections l → F, (unhitCount l a : ℝ)
      ∂(PMF.uniformOfFintype (TransverseDirections l → F)).toMeasure) =
      (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F := by
  rw [VacantBins.integral_uniform_eq_uniformMean, uniformMean_unhitCount]

theorem abs_unhitCount_sub_le_one (l : Line F)
    (a b : TransverseDirections l → F) (j : TransverseDirections l)
    (hab : ∀ i, i ≠ j → a i = b i) :
    |(unhitCount l a : ℝ) - (unhitCount l b : ℝ)| ≤ 1 := by
  simp_rw [unhitCount_eq_missedCount]
  apply VacantBins.abs_missedCount_sub_le_one _ _ j
  intro i hi
  change transverseHitEquiv l i.val (Ne.symm i.property) (a i) =
    transverseHitEquiv l i.val (Ne.symm i.property) (b i)
  rw [hab i hi]

end Balanced.LineOccupancy

end OAI
