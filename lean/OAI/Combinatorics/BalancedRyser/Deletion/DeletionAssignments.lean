import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Tactic

namespace OAI

open scoped BigOperators ENNReal
open MeasureTheory

namespace Balanced
open scoped _root_.Balanced
namespace DeletionAssignments

theorem card_three_assignments {α : Type*} [DecidableEq α] (s : Finset α) (hs : s.card = 3) :
    Fintype.card (Fin 3 ≃ s) = 6 := by
  classical
  let e : Fin 3 ≃ s :=
    (Fintype.equivFinOfCardEq (by simpa using hs : Fintype.card s = 3)).symm
  rw [Fintype.card_equiv e]
  norm_num

theorem card_direction_assignments {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (D : ι → Finset α) (hD : ∀ i, (D i).card = 3) :
    Fintype.card (∀ i, Fin 3 ≃ D i) = 6 ^ Fintype.card ι := by
  classical
  rw [Fintype.card_pi]
  simp_rw [card_three_assignments _ (hD _)]
  simp

theorem exists_assignment_of_image {α : Type*} [DecidableEq α]
    (s : Finset α) (f : Fin 3 → α) (hf : Function.Injective f)
    (hs : Finset.univ.image f = s) :
    ∃ e : Fin 3 ≃ s, ∀ j, (e j).val = f j := by
  let g : Fin 3 → s := fun j => ⟨f j, by rw [← hs]; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro j k h
      exact hf (congrArg Subtype.val h)
    · intro x
      have hx : x.val ∈ Finset.univ.image f := by rw [hs]; exact x.property
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
      exact ⟨j, Subtype.ext hj⟩
  exact ⟨Equiv.ofBijective g hg, fun _ => rfl⟩

theorem exists_assignment_of_three_image {α : Type*} [DecidableEq α]
    (s : Finset α) (hcard : s.card = 3) (f : Fin 3 → α)
    (hs : Finset.univ.image f = s) :
    ∃ e : Fin 3 ≃ s, ∀ j, (e j).val = f j := by
  have hi : Set.InjOn f (Finset.univ : Finset (Fin 3)) :=
    Finset.card_image_iff.mp (by simp [hs, hcard])
  exact exists_assignment_of_image s f
    (fun j k h => hi (Finset.mem_univ j) (Finset.mem_univ k) h) hs

theorem weighted_union_bound {Ω I : Type*} [Fintype Ω] [Fintype I]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (P : Ω → Prop) (Q : I → Ω → Prop)
    [DecidablePred P] [∀ i, DecidablePred (Q i)]
    (hcover : ∀ ω, P ω → ∃ i, Q i ω)
    (c : ℝ) (hbound : ∀ i, (∑ ω, if Q i ω then w ω else 0) ≤ c) :
    (∑ ω, if P ω then w ω else 0) ≤ (Fintype.card I : ℝ) * c := by
  classical
  have hpoint : ∀ ω, (if P ω then w ω else 0) ≤
      ∑ i, if Q i ω then w ω else 0 := by
    intro ω
    by_cases hP : P ω
    · obtain ⟨i, hi⟩ := hcover ω hP
      simp only [ite_eq_left hP]
      calc
        w ω = (if Q i ω then w ω else 0) := (ite_eq_left hi).symm
        _ ≤ ∑ j, if Q j ω then w ω else 0 :=
          Finset.single_le_sum (f := fun j => if Q j ω then w ω else 0)
            (fun j _ => by split_ifs; exact hw ω; exact le_rfl) (Finset.mem_univ i)
    · simp only [ite_eq_right hP]
      exact Finset.sum_nonneg (fun i _ => by split_ifs; exact hw ω; exact le_rfl)
  calc
    (∑ ω, if P ω then w ω else 0)
        ≤ ∑ ω, ∑ i, if Q i ω then w ω else 0 := Finset.sum_le_sum (fun ω _ => hpoint ω)
    _ = ∑ i, ∑ ω, if Q i ω then w ω else 0 := Finset.sum_comm
    _ ≤ ∑ _i : I, c := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (Fintype.card I : ℝ) * c := by simp

theorem weighted_unordered_deletion_le {Ω ι α : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (A : Ω → Prop) [DecidablePred A] (roles : Ω → ι → Fin 3 → α)
    (D : ι → Finset α) (hD : ∀ i, (D i).card = 3)
    (c : ℝ)
    (hbound : ∀ e : ∀ i, Fin 3 ≃ D i,
      (∑ ω, if A ω ∧ (∀ i j, roles ω i j = (e i j).val) then w ω else 0) ≤ c) :
    (∑ ω, if A ω ∧ (∀ i, Finset.univ.image (roles ω i) = D i) then w ω else 0) ≤
      (6 : ℝ) ^ Fintype.card ι * c := by
  classical
  have hcover : ∀ ω, (A ω ∧ ∀ i, Finset.univ.image (roles ω i) = D i) →
      ∃ e : ∀ i, Fin 3 ≃ D i, A ω ∧ ∀ i j, roles ω i j = (e i j).val := by
    intro ω hω
    have he : ∀ i, ∃ e : Fin 3 ≃ D i, ∀ j, (e j).val = roles ω i j :=
      fun i => exists_assignment_of_three_image (D i) (hD i) (roles ω i) (hω.2 i)
    choose e he using he
    exact ⟨e, hω.1, fun i j => (he i j).symm⟩
  simpa only [card_direction_assignments D hD, Nat.cast_pow, Nat.cast_ofNat] using
    weighted_union_bound w hw _ _ hcover c hbound

theorem weighted_unordered_deletion_le_of_injective_roles {Ω ι α : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (roles : Ω → ι → Fin 3 → α) (hroles : Function.Injective roles)
    (D : ι → Finset α) (hD : ∀ i, (D i).card = 3)
    (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ ω, w ω ≤ c) :
    (∑ ω, if (∀ i, Finset.univ.image (roles ω i) = D i) then w ω else 0) ≤
      (6 : ℝ) ^ Fintype.card ι * c := by
  classical
  have hprescribed : ∀ e : ∀ i, Fin 3 ≃ D i,
      (∑ ω, if True ∧ (∀ i j, roles ω i j = (e i j).val) then w ω else 0) ≤ c := by
    intro e
    by_cases hex : ∃ ω, ∀ i j, roles ω i j = (e i j).val
    · obtain ⟨ω₀, hω₀⟩ := hex
      have hsingle : (∑ ω, if True ∧ (∀ i j, roles ω i j = (e i j).val) then w ω else 0) =
          w ω₀ := by
        rw [Finset.sum_eq_single ω₀]
        · simp [hω₀]
        · intro ω _ hne
          have hn : ¬ ∀ i j, roles ω i j = (e i j).val := by
            intro heq
            apply hne
            apply hroles
            funext i j
            exact (heq i j).trans (hω₀ i j).symm
          simp [hn]
        · simp
      rw [hsingle]
      exact hbound ω₀
    · have hn : ∀ ω, ¬ ∀ i j, roles ω i j = (e i j).val := by simpa using hex
      simpa [hn] using hc
  simpa using weighted_unordered_deletion_le w hw (fun _ => True) roles D hD c hprescribed

theorem measure_unordered_deletion_le {Ω ι α : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq α]
    (μ : Measure Ω) (A : Set Ω) (roles : Ω → ι → Fin 3 → α)
    (D : ι → Finset α) (hD : ∀ i, (D i).card = 3)
    (hinj : ∀ ω ∈ A, ∀ i, Function.Injective (roles ω i))
    (c : ℝ≥0∞)
    (hbound : ∀ e : ∀ i, Fin 3 ≃ D i,
      μ {ω | ω ∈ A ∧ ∀ i j, roles ω i j = (e i j).val} ≤ c) :
    μ {ω | ω ∈ A ∧ ∀ i, Finset.univ.image (roles ω i) = D i} ≤
      (6 : ℝ≥0∞) ^ Fintype.card ι * c := by
  classical
  let E := fun e : ∀ i, Fin 3 ≃ D i =>
    {ω | ω ∈ A ∧ ∀ i j, roles ω i j = (e i j).val}
  have hsub : {ω | ω ∈ A ∧ ∀ i, Finset.univ.image (roles ω i) = D i} ⊆
      ⋃ e, E e := by
    intro ω hω
    have he : ∀ i, ∃ e : Fin 3 ≃ D i, ∀ j, (e j).val = roles ω i j :=
      fun i => exists_assignment_of_image (D i) (roles ω i) (hinj ω hω.1 i) (hω.2 i)
    choose e he using he
    exact Set.mem_iUnion.mpr ⟨e, hω.1, fun i j => (he i j).symm⟩
  calc
    μ {ω | ω ∈ A ∧ ∀ i, Finset.univ.image (roles ω i) = D i}
        ≤ μ (⋃ e, E e) := measure_mono hsub
    _ ≤ ∑ e, μ (E e) := measure_iUnion_fintype_le μ E
    _ ≤ ∑ _e : ∀ i, Fin 3 ≃ D i, c := Finset.sum_le_sum fun e _ => hbound e
    _ = (6 : ℝ≥0∞) ^ Fintype.card ι * c := by
      simp [card_direction_assignments D hD, nsmul_eq_mul]

end DeletionAssignments
end Balanced

end OAI
