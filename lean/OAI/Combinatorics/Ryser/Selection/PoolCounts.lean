import OAI.Combinatorics.Ryser.Selection.SmallCertificates
import Mathlib.Data.Finset.Prod

namespace OAI

open scoped BigOperators
namespace RyserCoveringCounterexample.Selection

variable {n K : ℕ}

def targetPositions (I : Finset (Fin n)) (K : ℕ) : Finset (Position n K) :=
  I.product Finset.univ

@[simp] theorem mem_targetPositions {I : Finset (Fin n)} {e : Position n K} :
    e ∈ targetPositions I K ↔ e.1 ∈ I := by
  simp only [targetPositions, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_univ, and_true]

@[simp] theorem card_targetPositions (I : Finset (Fin n)) (K : ℕ) :
    (targetPositions I K).card = I.card * K := by
  simp only [targetPositions, Finset.product_eq_sprod, Finset.card_product,
    Finset.card_univ, Fintype.card_fin]

theorem image_freshTargets_val (I : Finset (Fin n)) (T : Finset (Position n K)) :
    (freshTargets I T).image (fun e => e.val) = targetPositions I K \ T := by
  ext e
  constructor
  · intro he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_sdiff.mpr
      ⟨mem_targetPositions.mpr (Finset.mem_filter.mp hz).2, z.property⟩
  · intro he
    obtain ⟨hi, hn⟩ := Finset.mem_sdiff.mp he
    refine Finset.mem_image.mpr ⟨⟨e, hn⟩, ?_, rfl⟩
    simp only [freshTargets, Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_targetPositions.mp hi

theorem card_freshTargets_eq_sdiff (I : Finset (Fin n)) (T : Finset (Position n K)) :
    (freshTargets I T).card = (targetPositions I K \ T).card := by
  calc
    (freshTargets I T).card = ((freshTargets I T).image (fun e => e.val)).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = (targetPositions I K \ T).card := congrArg Finset.card (image_freshTargets_val I T)

theorem card_freshTargets {I : Finset (Fin n)} {T : Finset (Position n K)}
    (hT : T ⊆ targetPositions I K) :
    (freshTargets I T).card = I.card * K - T.card := by
  rw [card_freshTargets_eq_sdiff, Finset.card_sdiff_of_subset hT, card_targetPositions]

theorem card_freshTargets_add_card {I : Finset (Fin n)} {T : Finset (Position n K)}
    (hT : T ⊆ targetPositions I K) :
    (freshTargets I T).card + T.card = I.card * K := by
  rw [card_freshTargets_eq_sdiff, Finset.card_sdiff_add_card_eq_card hT,
    card_targetPositions]

theorem freshTargets_card_lower {I : Finset (Fin n)} {T : Finset (Position n K)}
    (hT : T ⊆ targetPositions I K) (hcard : T.card ≤ 2 * I.card) :
    (K - 2) * I.card ≤ (freshTargets I T).card := by
  rw [card_freshTargets hT, Nat.sub_mul, Nat.mul_comm K I.card]
  exact Nat.sub_le_sub_left hcard (I.card * K)

theorem sum_exposedCount {I : Finset (Fin n)} {T : Finset (Position n K)}
    (hT : T ⊆ targetPositions I K) :
    (∑ i ∈ I, exposedCount T i) = T.card := by
  have hmap : (T : Set (Position n K)).MapsTo Prod.fst I := by
    intro e he
    exact mem_targetPositions.mp (hT he)
  simpa only [exposedCount] using (Finset.card_eq_sum_card_fiberwise hmap).symm

theorem targetPositions_eq_filter (I : Finset (Fin n)) (K : ℕ) :
    targetPositions I K = Finset.univ.filter (fun e : Position n K => e.1 ∈ I) := by
  ext e
  simp only [mem_targetPositions, Finset.mem_filter, Finset.mem_univ, true_and]

theorem exposedCount_le (T : Finset (Position n K)) (i : Fin n) :
    exposedCount T i ≤ K := by
  classical
  unfold exposedCount
  calc
    (T.filter (fun e => e.1 = i)).card ≤
        (Finset.univ : Finset (Fin K)).card := by
      refine Finset.card_le_card_of_injOn
        (fun e : Position n K => e.2) ?_ ?_
      · intro e _
        exact Finset.mem_univ _
      · intro e he f hf hef
        exact Prod.ext
          ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
          hef
    _ = K := by simp

theorem card_freshTargets_fiber (I : Finset (Fin n))
    (T : Finset (Position n K)) (i : Fin n) (hi : i ∈ I) :
    ((freshTargets I T).filter (fun e => e.val.1 = i)).card =
      K - exposedCount T i := by
  classical
  let used : Finset (Fin K) := Finset.univ.filter (fun j => (i, j) ∈ T)
  let unused : Finset (Fin K) := Finset.univ.filter (fun j => (i, j) ∉ T)
  have hused : exposedCount T i = used.card := by
    unfold exposedCount
    refine Finset.card_bij (fun (e : Position n K) _ => e.2) ?_ ?_ ?_
    · intro e he
      have hepair : e = (i, e.2) :=
        Prod.ext (Finset.mem_filter.mp he).2 rfl
      have hmem : (i, e.2) ∈ T := by
        rw [← hepair]
        exact (Finset.mem_filter.mp he).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
    · intro e he f hf hef
      exact Prod.ext
        ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
        hef
    · intro j hj
      refine ⟨(i, j), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).2, rfl⟩
  have hfresh :
      ((freshTargets I T).filter (fun e => e.val.1 = i)).card = unused.card := by
    refine Finset.card_bij
      (fun (e : {e : Position n K // e ∉ T}) _ => e.val.2) ?_ ?_ ?_
    · intro e he
      have hepair : e.val = (i, e.val.2) :=
        Prod.ext (Finset.mem_filter.mp he).2 rfl
      have hnot : (i, e.val.2) ∉ T := by
        rw [← hepair]
        exact e.property
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩
    · intro e he f hf hef
      apply Subtype.ext
      exact Prod.ext
        ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
        hef
    · intro j hj
      have hjT : (i, j) ∉ T := (Finset.mem_filter.mp hj).2
      refine ⟨⟨(i, j), hjT⟩, ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨?_, rfl⟩
      simpa only [freshTargets, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  have hsplit : used.card + unused.card = K := by
    simpa only [used, unused, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin K)))
        (fun j : Fin K => (i, j) ∈ T))
  rw [hfresh, hused]
  exact Nat.eq_sub_of_add_eq' hsplit

theorem sum_freshTargets (I : Finset (Fin n))
    (T : Finset (Position n K)) (f : Fin n → ℝ) :
    (∑ e ∈ freshTargets I T, f e.val.1) =
      ∑ i ∈ I, ((K - exposedCount T i : ℕ) : ℝ) * f i := by
  classical
  have hmaps : ∀ e ∈ freshTargets I T, e.val.1 ∈ I := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  calc
    (∑ e ∈ freshTargets I T, f e.val.1) =
        ∑ i ∈ I, ∑ e ∈ (freshTargets I T).filter (fun e => e.val.1 = i), f i :=
      (Finset.sum_fiberwise_of_maps_to'
        (s := freshTargets I T) (t := I)
        (g := fun e : {e : Position n K // e ∉ T} => e.val.1) hmaps f).symm
    _ = ∑ i ∈ I, ((K - exposedCount T i : ℕ) : ℝ) * f i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_const, nsmul_eq_mul, card_freshTargets_fiber I T i hi]

end RyserCoveringCounterexample.Selection

end OAI
