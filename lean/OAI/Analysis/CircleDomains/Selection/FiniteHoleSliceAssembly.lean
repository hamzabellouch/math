import OAI.Analysis.CircleDomains.Rigidity.GapFluxTelescoping
import OAI.Analysis.CircleDomains.Sobolev.ClosedGapIntegrals
import OAI.Analysis.CircleDomains.Selection.FiniteGapTollSum

namespace OAI

/-! Summing the actual retained-gap estimates gives the outer increment
minus the removed-hole increments, with each tail disk paid twice. -/
open Set Function Filter MeasureTheory
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity

 theorem finite_hole_slice_payment {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hvalid : ∀ i, (H i).1 ≤ (H i).2) (hfirst : Monotone (fun i => (H i).1))
    {κ : Type*} [Countable κ] (J : κ → Set ℝ) (w : κ → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => if (J j).Nonempty then w j else 0))
    (hJ : ∀ j, OrdConnected (J j))
    (hone : ∀ j i k, (J j ∩ Icc (H i).1 (H i).2).Nonempty →
      (J j ∩ Icc (H k).1 (H k).2).Nonempty → i = k)
    (v : ℝ → ℝ) (ρ : ℝ → ℝ) {B V : Set ℝ} (hB : MeasurableSet B) (hV : MeasurableSet V)
    (hi : IntegrableOn ρ B volume) (hρ : ∀ x ∈ B, 0 ≤ ρ x)
    (hsub : ∀ i, Icc (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ∩ V ⊆ B)
    (hpay : ∀ i,
      v (gapsAfterHoles a b H i).2-v (gapsAfterHoles a b H i).1 ≤
        (∫ x in Icc (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ∩ V, ρ x) +
        ∑' j, if (J j ∩ Icc (gapsAfterHoles a b H i).1
          (gapsAfterHoles a b H i).2).Nonempty then w j else 0) :
    v b-v a-∑ i, (v (H i).2-v (H i).1) ≤
      (∫ x in B, ρ x)+2*∑' j, if (J j).Nonempty then w j else 0 := by
  rw [← sum_gap_increments a b H v]
  calc
    _ ≤ ∑ i, ((∫ x in Icc (gapsAfterHoles a b H i).1
        (gapsAfterHoles a b H i).2 ∩ V, ρ x) +
        ∑' j, if (J j ∩ Icc (gapsAfterHoles a b H i).1
          (gapsAfterHoles a b H i).2).Nonempty then w j else 0) :=
      Finset.sum_le_sum (fun i _ => hpay i)
    _ = (∑ i, ∫ x in Icc (gapsAfterHoles a b H i).1
        (gapsAfterHoles a b H i).2 ∩ V, ρ x) +
        ∑ i, ∑' j, if (J j ∩ Icc (gapsAfterHoles a b H i).1
          (gapsAfterHoles a b H i).2).Nonempty then w j else 0 := Finset.sum_add_distrib
    _ ≤ _ := add_le_add
      (closed_gap_integrals_le_of_nonstrict a b H hvalid hfirst hB hV hi hρ hsub)
      (finite_gap_toll_sum_le _ J w hw hs (fun j =>
        at_most_two_gaps_of_at_most_one_hole a b H hvalid hfirst (hJ j) (hone j)))

end CircleDomainRigidity

end

end OAI
