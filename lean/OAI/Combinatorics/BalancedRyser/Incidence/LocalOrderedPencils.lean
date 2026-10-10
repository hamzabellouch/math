import OAI.Combinatorics.BalancedRyser.Local.LocalConfigurationPattern
import OAI.Combinatorics.BalancedRyser.Local.LocalTupleReindex
import OAI.Combinatorics.BalancedRyser.Probability.OrderedEventCounting

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def BadLocalCoverAt (b : ℕ) (p : Point F) (C : Configuration F) : Prop :=
  ∃ A : Finset (LocalPiece F), A.card ≤ b - 1 ∧
    (∀ x ∈ A, C.AllowedLocalPiece p x) ∧
    C.designatedAt p ⊆ C.partnerSet p ∪ A.biUnion C.localPiecePoints

def OrderedBadPencil (b κ : ℕ) (p : Point F) (used : Fin b → Slot F)
    (C : Configuration F) : Prop :=
  Function.Injective used ∧
    ∃ (P : EqualityPattern b κ) (a : DirectionAssignment F b κ) (bits : Bits b),
      Eligible P a ∧ AdmissibleBadCover P a bits p C.merged ∧
        ∀ i, (used i).1 = a.1 i ∧
          (C.choice (used i)).tuple = prescribedTuple P a bits i ∧
          (C.choice (used i)).line = lineThrough (a.1 i) p

theorem bad_local_cover_all_orders (C : Configuration F)
    (hV : C.Valid) (hC : C.Compatible) (p : Point F)
    (hcap : ∀ x, constituentMultiplicity C.merged x ≤ logBudget F)
    {b κ : ℕ} (hb : C.splitMultiplicity p = b) (hb2 : 2 ≤ b)
    (hk : reuseCount C p = κ) (hbad : BadLocalCoverAt b p C) :
    ∃ f : Fin b → Slot F, Function.Injective f ∧
      ∀ σ : Equiv.Perm (Fin b), OrderedBadPencil b κ p (f ∘ σ) C := by
  subst b
  subst κ
  refine ⟨ConfigurationPattern.slot C hV hC p,
    ConfigurationPattern.slot_injective C hV hC p, ?_⟩
  intro σ
  let P := ConfigurationPattern.pattern C hV hC p
  let a := ConfigurationPattern.assignment C hV hC p
  let bits := ConfigurationPattern.bits C hV hC p
  have he : Eligible P a := ConfigurationPattern.assignment_eligible C hV hC p
  have ha : AdmissibleBadCover P a bits p C.merged :=
    ⟨ConfigurationPattern.admissible C hV hC p hb2 hcap,
      (ConfigurationPattern.badCover_iff C hV hC p).mpr hbad⟩
  refine ⟨(ConfigurationPattern.slot_injective C hV hC p).comp σ.injective,
    P.reindex σ, reindexAssignment σ a, reindexBits σ bits,
    (eligible_reindex P σ a).mpr he,
    (admissibleBadCover_reindex P σ a bits p C.merged).mpr ha, ?_⟩
  intro i
  refine ⟨rfl, ?_, ?_⟩
  · exact (ConfigurationPattern.prescribedTuple_eq C hV hC p (σ i)).symm
  · exact ConfigurationPattern.slot_line_eq C hV hC p (σ i)

theorem selectedProbability_le_order_sum (w : Kernel F)
    (hw : ∀ M v, 0 ≤ w M v) {b : ℕ}
    (E : Configuration F → Prop)
    (R : (Fin b → Slot F) → Configuration F → Prop)
    (hcover : ∀ M v, 0 < w M v → E (configuration M v) →
      ∃ f : Fin b → Slot F, Function.Injective f ∧
        ∀ σ : Equiv.Perm (Fin b), R (f ∘ σ) (configuration M v)) :
    selectedProbability w E ≤
      (∑ f : Fin b → Slot F, selectedProbability w (R f)) / (b.factorial : ℝ) := by
  have h := OrderedEventCounting.weighted_order_bound
    (fun z : MergedPairs F × Output F => w z.1 z.2)
    (fun z => hw z.1 z.2)
    (fun z => E (configuration z.1 z.2))
    (fun f z => R f (configuration z.1 z.2))
    (fun z => hcover z.1 z.2)
  simp only [Fintype.sum_prod_type] at h
  have hd := div_le_div_of_nonneg_right h
    (show (0 : ℝ) ≤ Fintype.card (MergedPairs F) by positivity)
  simpa only [selectedProbability, Finset.sum_div, div_div, mul_comm] using hd

theorem bad_pencil_probability_le_order_sum
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hK : KernelConditions Q w K) (p : Point F) (b κ : ℕ) (hb : 2 ≤ b) :
    selectedProbability w (fun C => C.splitMultiplicity p = b ∧
      reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤
      (∑ f : Fin b → Slot F,
        selectedProbability w (OrderedBadPencil b κ p f)) / (b.factorial : ℝ) := by
  apply selectedProbability_le_order_sum w hK.1
  intro M v hv hbad
  obtain ⟨hV, hC, _, hcap⟩ := hK.2.2.1 M v hv
  exact bad_local_cover_all_orders (configuration M v) hV hC p hcap
    hbad.1 hb hbad.2.1 hbad.2.2

end
end Balanced.Local

end OAI
