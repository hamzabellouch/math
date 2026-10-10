import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.BlockIndependence

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma fewOpenBonds_probability_le (p : unitInterval) (S : Set E) (hS : S.Finite)
    (N L : ℕ) (hcard : (N+1)*L ≤ S.ncard) :
    (law (fun _ : E => p)).real {ω | (S∩ω).ncard ≤ N} ≤
      (N+1 : ℝ)*(1-(p:ℝ))^L := by
  let : Fintype S := hS.fintype
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin (N+1) × Fin L) (β := S)
    (show Fintype.card (Fin (N+1) × Fin L) ≤ Fintype.card S by
      rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]
      simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] using hcard)
  let f : Fin (N+1) × Fin L → E := fun x => (e x).val
  have hf : Function.Injective f := fun x y h => e.injective (Subtype.ext h)
  let B : Fin (N+1) → Set E := fun i => Set.range (fun j : Fin L => f (i,j))
  have hBfinite (i : Fin (N+1)) : (B i).Finite := Set.finite_range _
  have hBcard (i : Fin (N+1)) : (B i).ncard = L := by
    rw [Set.ncard_range_of_injective (fun a b h => (Prod.mk.inj (hf h)).2)]
    simp
  have hcover : {ω : Set E | (S∩ω).ncard ≤ N} ⊆ ⋃ i, closedBlock (B i) := by
    intro ω hω
    by_contra hn
    have hopen : ∀ i : Fin (N+1), ∃ j : Fin L, f (i,j)∈ω := by
      intro i
      have hi : ¬ Disjoint (B i) ω := fun hh => hn (Set.mem_iUnion.mpr ⟨i,hh⟩)
      obtain ⟨b,hb,hbω⟩ := Set.not_disjoint_iff.mp hi
      obtain ⟨j,rfl⟩ := hb
      exact ⟨j,hbω⟩
    choose j hj using hopen
    have hinj : Function.Injective (fun i : Fin (N+1) => f (i,j i)) :=
      fun a b h => (Prod.mk.inj (hf h)).1
    have hsub : Set.range (fun i : Fin (N+1) => f (i,j i)) ⊆ S∩ω := by
      rintro x ⟨i,rfl⟩
      exact ⟨(e (i,j i)).property,hj i⟩
    have hh := Set.ncard_le_ncard hsub (hS.subset Set.inter_subset_left)
    rw [Set.ncard_range_of_injective hinj] at hh
    simp only [Nat.card_eq_fintype_card,Fintype.card_fin] at hh
    exact Nat.not_succ_le_self N (hh.trans hω)
  have hreal : (bitMeasure p {False}).toReal = 1-(p:ℝ) := by
    simpa only [Measure.real,bitWeight,ite_false] using bitMeasure_real_singleton p False
  calc
    _ ≤ (law (fun _ : E => p)).real (⋃ i, closedBlock (B i)) := measureReal_mono hcover
    _ ≤ ∑ i, (law (fun _ : E => p)).real (closedBlock (B i)) :=
      measureReal_iUnion_fintype_le _
    _ = ∑ _i : Fin (N+1), (1-(p:ℝ))^L := by
      apply Finset.sum_congr rfl
      intro i _
      rw [measureReal_def,law_closedBlock_const p _ (hBfinite i),hBcard,
        ENNReal.toReal_pow,hreal]
    _ = _ := by simp [Nat.cast_add,Nat.cast_one]

end CriticalPercolation.BernoulliProduct
end
end

end OAI
