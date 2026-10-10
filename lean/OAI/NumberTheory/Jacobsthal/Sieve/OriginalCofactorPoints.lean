import OAI.NumberTheory.Jacobsthal.Estimates.NonstructuredCounts
import OAI.NumberTheory.Jacobsthal.Partitions.SourceLabelCount
import OAI.NumberTheory.Jacobsthal.Paths.ActualSampleWitness

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseRefinement
open ErdosInverseSampling
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def selectedRow (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (q : ℕ) : Finset ℕ :=
  P.filter (fun p => ∀ i : Fin h,witness (p,q) (s i).val)

noncomputable def rowReward (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (q : ℕ) : ℝ := (selectedRow P U witness h s q).card/(P.card : ℝ)

theorem selected_pairs_card_by_rows (P C U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) :
    (selectedPairs (P.product C) U witness h s).card = ∑ q ∈ C,(selectedRow P U witness h s q).card := by
  calc
    _ = ∑ p ∈ P,∑ q ∈ C,if (∀ i : Fin h,witness (p,q) (s i).val) then (1 : ℕ) else 0 := by
      simp only [selectedPairs,Finset.card_eq_sum_ones,Finset.sum_filter]
      exact Finset.sum_product P C (fun v : ℕ × ℕ => if (∀ i : Fin h,witness v (s i).val) then (1 : ℕ) else 0)
    _ = ∑ q ∈ C,∑ p ∈ P,if (∀ i : Fin h,witness (p,q) (s i).val) then (1 : ℕ) else 0 := Finset.sum_comm
    _ = _ := by simp only [selectedRow,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem rowReward_bounds (P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (q : ℕ) (hP : 0 < P.card) :
    0 ≤ rowReward P U witness h s q ∧ rowReward P U witness h s q ≤ 1 := by
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast hP
  refine ⟨div_nonneg (Nat.cast_nonneg _) hPpos.le,?_⟩
  apply (div_le_iff₀ hPpos).mpr
  simpa only [one_mul] using (show ((selectedRow P U witness h s q).card : ℝ) ≤ P.card by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _))

theorem rowReward_sum (P C U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (hP : 0 < P.card) (hC : 0 < C.card) :
    (∑ q ∈ C,rowReward P U witness h s q) = selectedFraction (P.product C) U witness h s*(C.card : ℝ) := by
  have hp : (P.card : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have hc : (C.card : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  unfold rowReward selectedFraction
  rw [← Finset.sum_div,selected_pairs_card_by_rows,Nat.cast_sum,Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul]
  field_simp

end ErdosInverseRefinement

end

section

namespace ErdosInverseRefinement
open ErdosInverseSampling
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def richCofactors (D P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (gamma : ℝ) : Finset ℕ :=
  D.filter (fun q => gamma/8 ≤ rowReward P U witness h s q)

theorem richCofactors_subset (D P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (gamma : ℝ) : richCofactors D P U witness h s gamma ⊆ D :=
  Finset.filter_subset _ _

theorem richCofactors_card_lower (D P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (gamma : ℝ) (hg : 0 ≤ gamma) (hP : 0 < P.card)
    (hdense : (gamma/4)*(D.card : ℝ) ≤ ∑ q ∈ D,rowReward P U witness h s q) :
    (gamma/8)*(D.card : ℝ) ≤ ((richCofactors D P U witness h s gamma).card : ℝ) := by
  have hh := many_large_weights D (rowReward P U witness h s) (gamma/4) (by positivity)
    (fun q _ => (rowReward_bounds P U witness h s q hP).2) hdense
  simpa only [div_div,show (4 : ℝ)*2 = 8 by norm_num,richCofactors] using hh

theorem richCofactor_row_card (D P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (gamma : ℝ) (hP : 0 < P.card) (q : ℕ)
    (hq : q ∈ richCofactors D P U witness h s gamma) :
    (gamma/8)*(P.card : ℝ) ≤ ((selectedRow P U witness h s q).card : ℝ) := by
  have hp : (0 : ℝ) < P.card := by exact_mod_cast hP
  have hh := (Finset.mem_filter.mp hq).2
  exact (le_div_iff₀ hp).mp hh

theorem richCofactors_source_size (D P U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (h : ℕ) (s : Sample U h) (gamma S Z : ℝ) (hg : 0 < gamma) (hS : 0 ≤ S) (hZ : 0 < Z)
    (hP : 0 < P.card) (hD : S/Z^3 ≤ (D.card : ℝ)) (hInv : 1/Z ≤ gamma/8)
    (hdense : (gamma/4)*(D.card : ℝ) ≤ ∑ q ∈ D,rowReward P U witness h s q) :
    S/Z^4 ≤ ((richCofactors D P U witness h s gamma).card : ℝ) := by
  calc
    _ = (1/Z)*(S/Z^3) := by field_simp
    _ ≤ (gamma/8)*(S/Z^3) := mul_le_mul_of_nonneg_right hInv (by positivity)
    _ ≤ (gamma/8)*(D.card : ℝ) := mul_le_mul_of_nonneg_left hD (by positivity)
    _ ≤ _ := richCofactors_card_lower D P U witness h s gamma hg.le hP hdense

end ErdosInverseRefinement

end

section

namespace ErdosInverseRefinement
open ErdosInverseCells ErdosConvexGraph
attribute [local instance] Classical.decEq

noncomputable def cofactorPoint (a : ℕ → ℕ) (q : ℕ) : ℤ × ℤ :=
  ((q : ℤ),(cofactorHit q a : ℤ))

noncomputable def cofactorPoints (D : Finset ℕ) (a : ℕ → ℕ) : Finset (ℤ × ℤ) :=
  D.image (cofactorPoint a)

theorem cofactorPoint_injective (a : ℕ → ℕ) : Function.Injective (cofactorPoint a) := by
  intro q r he
  have hh := congrArg Prod.fst he
  change (q : ℤ) = (r : ℤ) at hh
  exact_mod_cast hh

theorem cofactorPoints_card (D : Finset ℕ) (a : ℕ → ℕ) :
    (cofactorPoints D a).card = D.card :=
  Finset.card_image_of_injective D (cofactorPoint_injective a)

theorem cofactorPoints_x_injective (D : Finset ℕ) (a : ℕ → ℕ) :
    Set.InjOn Prod.fst (cofactorPoints D a : Set (ℤ × ℤ)) := by
  rintro v hv w hw he
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hw
  have hqr : q = r := by
    change (q : ℤ) = (r : ℤ) at he
    exact_mod_cast he
  exact congrArg (cofactorPoint a) hqr

theorem cofactorPoints_square (D : Finset ℕ) (a : ℕ → ℕ) (S : ℝ)
    (hq : ∀ q ∈ D,Squarefree q ∧ (q : ℝ) ≤ S) :
    ∀ v ∈ cofactorPoints D a,InSquare S v := by
  intro v hv
  obtain ⟨q,hqD,rfl⟩ := Finset.mem_image.mp hv
  have hb := cofactorHit_spec q (hq q hqD).1 a
  have hbq : (cofactorHit q a : ℝ) ≤ q := by exact_mod_cast hb.2.1
  change (0 ≤ ((q : ℤ) : ℝ) ∧ ((q : ℤ) : ℝ) ≤ S) ∧
    (0 ≤ ((cofactorHit q a : ℤ) : ℝ) ∧ ((cofactorHit q a : ℤ) : ℝ) ≤ S)
  push_cast
  exact ⟨⟨Nat.cast_nonneg _,(hq q hqD).2⟩,⟨Nat.cast_nonneg _,hbq.trans (hq q hqD).2⟩⟩

theorem cofactorPoints_prime_hits (D : Finset ℕ) (a : ℕ → ℕ)
    (hq : ∀ q ∈ D,Squarefree q) :
    ∀ v ∈ cofactorPoints D a,∀ p ∈ v.1.toNat.primeFactors,
      (v.2 : ZMod p) = (a p : ZMod p) := by
  intro v hv
  obtain ⟨q,hqD,rfl⟩ := Finset.mem_image.mp hv
  intro p hp
  have hh := (cofactorHit_spec q (hq q hqD) a).2.2 p hp
  change ((cofactorHit q a : ℤ) : ZMod p) = (a p : ZMod p)
  rw [Int.cast_natCast]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hh

theorem rich_points_source_size (D P U : Finset ℕ) (a : ℕ → ℕ)
    (witness : (ℕ × ℕ) → ℕ → Prop) (h : ℕ) (s : ErdosInverseSampling.Sample U h)
    (gamma S Z : ℝ) (hg : 0 < gamma) (hS : 0 ≤ S) (hZ : 0 < Z)
    (hP : 0 < P.card) (hD : S/Z^3 ≤ (D.card : ℝ)) (hInv : 1/Z ≤ gamma/8)
    (hdense : (gamma/4)*(D.card : ℝ) ≤ ∑ q ∈ D,rowReward P U witness h s q) :
    S/Z^4 ≤ ((cofactorPoints (richCofactors D P U witness h s gamma) a).card : ℝ) := by
  rw [cofactorPoints_card]
  exact richCofactors_source_size D P U witness h s gamma S Z hg hS hZ hP hD hInv hdense

end ErdosInverseRefinement

end

end Erdos970

end OAI
