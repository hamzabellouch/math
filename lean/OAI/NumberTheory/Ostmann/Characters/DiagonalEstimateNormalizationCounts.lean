import OAI.NumberTheory.Ostmann.Characters.SourceTemplatePriors
import OAI.NumberTheory.Ostmann.Characters.TemplateAdaptedCoordinates
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorSources

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable

lemma sum_subtype_nat_eq_ite {I : Type*} [Fintype I] (P : I → Prop) [DecidablePred P] (f : I → ℕ) :
    (∑ i : {i // P i}, f i.val) = ∑ i, if P i then f i else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

theorem role_weight_step_le (T : Layout) (j : ℕ) (f : Role → ℕ) :
    (∑ i : (T.step j).Slot, f ((T.step j).role i)) ≤
      2 * ∑ i : T.Slot, f (T.role i) := by
  have hs : (∑ i : {i : T.Slot // T.IsCopied j i}, f (T.role i.val)) +
      (∑ i : {i : T.Slot // T.IsOutside j i}, f (T.role i.val)) ≤
        ∑ i : T.Slot, f (T.role i) := by
    rw [sum_subtype_nat_eq_ite (T.IsCopied j) (fun i => f (T.role i)),
      sum_subtype_nat_eq_ite (T.IsOutside j) (fun i => f (T.role i)), ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hc : T.IsCopied j i
    · have ho : ¬T.IsOutside j i := fun h => h.2 hc
      simp only [hc,ho,ite_true,ite_false,add_zero,le_refl]
    · by_cases ho : T.IsOutside j i <;> simp only [hc,ho,ite_true,ite_false,zero_add,
        Nat.zero_le,le_refl]
  change (∑ i : ({i : T.Slot // T.IsCopied j i} × Bool) ⊕
    {i : T.Slot // T.IsOutside j i}, f ((T.step j).role i)) ≤ _
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Layout.step, Fintype.sum_bool, Finset.sum_add_distrib]
  omega

theorem role_weight_schedule_le (k j : ℕ) (f : Role → ℕ) :
    (∑ i : (schedule k j).Slot, f ((schedule k j).role i)) ≤
      2 ^ j * ∑ i : (schedule k 0).Slot, f ((schedule k 0).role i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    exact (role_weight_step_le (schedule k j) j f).trans (by
      rw [pow_succ]
      nlinarith)

def nonwordWeight {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) (r : Role) : ℕ :=
  if r = .word then 0 else sourceWidth cfg m r

theorem sourceWidth_initial_sum {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :
    (∑ r : InitialRole k, sourceWidth cfg m r.role) = m+1+configCellCount cfg := by
  have h := Fintype.card_congr (halfRoleCoordinateEquiv cfg m)
  simpa only [HalfRoleConstituent,HalfSourceCoordinates,Fintype.card_sigma,
    Fintype.card_sum,Fintype.card_fin,configCellCount_eq,Nat.add_assoc] using h

theorem nonwordWeight_initial_half_sum {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :
    (∑ r : InitialRole k, nonwordWeight cfg m r.role) = configCellCount cfg := by
  have hrole (r : InitialRole k) : r.role = .word ↔ r = .word := by
    cases r <;> simp [InitialRole.role]
  have hs : (∑ r : InitialRole k, sourceWidth cfg m r.role) =
      (m+1) + ∑ r : InitialRole k, nonwordWeight cfg m r.role := by
    calc
      _ = ∑ r : InitialRole k, ((if r = .word then m+1 else 0) +
          nonwordWeight cfg m r.role) := by
        apply Finset.sum_congr rfl
        intro r hr
        by_cases h : r = .word
        · subst r; simp [nonwordWeight,InitialRole.role,sourceWidth]
        · simp [nonwordWeight,hrole,h]
      _ = _ := by simp [Finset.sum_add_distrib]
  rw [sourceWidth_initial_sum] at hs
  omega

theorem nonwordWeight_initial_sum {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :
    (∑ i : (schedule k 0).Slot, nonwordWeight cfg m ((schedule k 0).role i)) =
      2 * configCellCount cfg := by
  change (∑ i : InitialRole k × Bool, nonwordWeight cfg m i.1.role) = _
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,Finset.sum_add_distrib,nonwordWeight_initial_half_sum]
  omega

theorem copied_nonword_weight_le {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) :
    (∑ i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i},
      nonwordWeight cfg m ((schedule k j).role i.val)) ≤
        2 ^ j * (2 * configCellCount cfg) := by
  have hs := role_weight_schedule_le k j (nonwordWeight cfg m)
  rw [nonwordWeight_initial_sum] at hs
  apply le_trans _ hs
  rw [sum_subtype_nat_eq_ite ((schedule k j).IsCopied j)
    (fun i => nonwordWeight cfg m ((schedule k j).role i))]
  exact Finset.sum_le_sum (fun i hi => by split_ifs <;> omega)

end Ostmann.Characters.DiagonalEstimate

end

end OAI
