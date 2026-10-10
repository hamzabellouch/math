import Mathlib
import OAI.Probability.Ballisticity.Estimates.BudgetMeasurable

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

def separateTuple {d k : ℕ} (f : Direction d) (M : ℕ) (x : Fin k → Lattice d) : Fin k → Lattice d :=
  fun j => Function.update (x j) f.1 ((j:ℕ)*M)

lemma separateTuple_separated {d k : ℕ} (f : Direction d) (M : ℕ) (x : Fin k → Lattice d) :
    TupleSeparated f (M:ℝ) (separateTuple f M x) := by
  rw [tupleSeparated_coordinate]
  intro i j hij
  simp only [separateTuple,Function.update_self]
  have hn : (i:ℤ)≠(j:ℤ) := by exact_mod_cast (Fin.val_ne_of_ne hij)
  have hh : (1:ℤ)≤|(i:ℤ)-(j:ℤ)| := Int.one_le_abs (sub_ne_zero.mpr hn)
  rw [← sub_mul,abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
  nlinarith [Int.natCast_nonneg M]

lemma separateTuple_height {d k : ℕ} (e f : Direction d) (hef : e.1≠f.1)
    (M : ℕ) (a : ℝ) (x : Fin k → Lattice d) (hx : x∈TupleAtHeight (realPosition (step e)) a) :
    separateTuple f M x∈TupleAtHeight (realPosition (step e)) a := by
  intro j
  rw [dot_signed_direction]
  simpa only [signedCoordinate,separateTuple,Function.update_of_ne hef] using
    (show signedCoordinate e (x j)=a by simpa only [dot_signed_direction] using hx j)

noncomputable def seedSeparatedRaw {d k : ℕ} (e f : Direction d) (H : ℕ) (G : ℝ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) : Measure (Fin k → Lattice d) :=
  (rawTupleMixture (realPosition (step e)) H π ω).restrict {y | TupleSeparated f G y}

lemma seedSeparatedRaw_univ {d k : ℕ} (e f : Direction d) (H : ℕ) (G : ℝ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    seedSeparatedRaw e f H G π ω Set.univ=
      rawTupleMixture (realPosition (step e)) H π ω {y | TupleSeparated f G y} := by
  simp [seedSeparatedRaw]

instance seedSeparatedRaw_finite {d k : ℕ} (e f : Direction d) (H : ℕ) (G : ℝ)
    (π : Measure (Fin k → Lattice d)) [IsFiniteMeasure π] (ω : Environment d) :
    IsFiniteMeasure (seedSeparatedRaw e f H G π ω) := by unfold seedSeparatedRaw; infer_instance

lemma seedSeparatedRaw_support {d k : ℕ} (e f : Direction d) (H : ℕ) (G a : ℝ)
    (π : LayerTupleProfile (k:=k) e a) (ω : Environment d) :
    ∀ᵐ y ∂seedSeparatedRaw e f H G π.val ω,
      y∈TupleAtHeight (realPosition (step e)) (a+H) ∧ TupleSeparated f G y := by
  exact (ae_restrict_of_ae (rawTupleMixture_support e H a π.val ω π.property.2)).and
    (ae_restrict_mem ((Set.to_countable _).measurableSet))

noncomputable def seedSeparatedProfile {d k : ℕ} (e f : Direction d) (hef : e.1≠f.1)
    (a G : ℝ) (H : ℕ) (π : LayerTupleProfile (k:=k) e a) (ω : Environment d) :
    BudgetProfile (k:=k) e f (a+H) G := by
  let M : ℕ := Nat.ceil (max G 0)+1
  let μ := seedSeparatedRaw e f H G π.val ω
  let ρ := π.val.map (fun x => separateTuple f M (tupleShiftUp e H x))
  have : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).2 inferInstance
  refine ⟨normalizeOr μ ρ,normalizeOr_probability μ ρ,?_⟩
  apply normalizeOr_ae
  · exact seedSeparatedRaw_support e f H G a π ω
  · rw [ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
    apply π.property.2.mono
    intro x hx
    have hg : TupleSeparated e 0 x := fun _ _ _ => abs_nonneg _
    have hM : G≤(M:ℝ) := by
      have hh := Nat.le_ceil (max G 0)
      dsimp [M]; push_cast; linarith [le_max_left G 0]
    exact ⟨separateTuple_height e f hef M _ _ (tupleShiftUp_support e e H a 0 x ⟨hx,hg⟩).1,
      tupleSeparated_mono f hM _ (separateTuple_separated f M _)⟩

lemma seedSeparatedProfile_mass {d k : ℕ} (e f : Direction d) (hef : e.1≠f.1)
    (a G : ℝ) (H : ℕ) (π : LayerTupleProfile (k:=k) e a) (ω : Environment d) :
    seedSeparatedRaw e f H G π.val ω Set.univ •
      (seedSeparatedProfile e f hef a G H π ω).val=seedSeparatedRaw e f H G π.val ω :=
  normalizeOr_mass _ _

lemma seedSeparatedRaw_joint_rows {d k : ℕ} (e f : Direction d) (H : ℕ) (G a : ℝ)
    (S : Set (Lattice d)) (hS : ∀ x∈TupleAtHeight (k:=k) (realPosition (step e)) a,
      ∀ j, Strip (realPosition (step e)) (x j) H⊆S) :
    @Measurable (LayerTupleProfile (k:=k) e a×Environment d) (Measure (Fin k → Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => seedSeparatedRaw e f H G p.1.val p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  have hm := (rawTupleMixture_joint_rows _ H _ S hS).comp
    (((LayerTupleProfile.measurable_toSupported e a).comp measurable_fst).prodMk measurable_snd)
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [seedSeparatedRaw,Measure.restrict_apply hU]
  exact (Measure.measurable_coe ((Set.to_countable _).measurableSet)).comp hm

lemma seedSeparatedProfile_measurable {d k : ℕ} (e f : Direction d) (hef : e.1≠f.1)
    (a G : ℝ) (H : ℕ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+H))) _
      (fun ω => seedSeparatedProfile e f hef a G H (π ω) ω) := by
  have hle : rowSigma (BelowHeight (realPosition (step e)) a)≤rowSigma (BelowHeight (realPosition (step e)) (a+H)) :=
    rowSigma_mono (by
      intro x hx
      change dot (realPosition x) (realPosition (step e)) < a+H
      exact lt_of_lt_of_le hx (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  let : MeasurableSpace (Environment d) := rowSigma (BelowHeight (realPosition (step e)) (a+H))
  apply Measurable.subtype_mk
  apply measurable_normalizeOr
  · apply (seedSeparatedRaw_joint_rows e f H G a _ ?_).comp ((hπ.mono hle le_rfl).prodMk measurable_id)
    intro x hx j y hy
    change dot (realPosition y) (realPosition (step e))<a+H
    simpa only [hx j] using hy.2
  · exact (Measure.measurable_map _ (measurable_of_countable _)).comp (measurable_subtype_coe.comp (hπ.mono hle le_rfl))

end DirectionalTransience

end

end OAI
