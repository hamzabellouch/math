import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantCompensationErrorAverage

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion Filter Construction.CanonicalOccurrenceTransport
open HistoryPairBulkTransport HistoryGiantCompensationProduct
open HistoryBulkFibreGiantApproximation HistoryBulkReferencePeriodicMeanSource
variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz depth L E)

def choiceCompensation
    (c : HistoryChoices C.sources (Template.initial (2*(bulkSize depth L/2)) depth)
      (frequencyBound Bs BD Bz depth L) l) : ℝ :=
  ((∏ i : Internal (Template.initial (2*(bulkSize depth L/2)) depth) l,
    (historyDraws C.sources (Template.initial (2*(bulkSize depth L/2)) depth)
      (frequencyBound Bs BD Bz depth L) l c i).val : ℕ) : ℝ)

def pairedChoiceCompensation
    (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize depth L/2)) depth)
      (frequencyBound Bs BD Bz depth L) l) : ℝ :=
  choiceCompensation C c * choiceCompensation C e

theorem choiceCompensation_nonneg
    (c : HistoryChoices C.sources (Template.initial (2*(bulkSize depth L/2)) depth)
      (frequencyBound Bs BD Bz depth L) l) : 0 ≤ choiceCompensation C c :=
  Nat.cast_nonneg _

theorem pairedChoiceCompensation_nonneg
    (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize depth L/2)) depth)
      (frequencyBound Bs BD Bz depth L) l) : 0 ≤ pairedChoiceCompensation C c e :=
  mul_nonneg (choiceCompensation_nonneg C c) (choiceCompensation_nonneg C e)

theorem assigned_compensationProduct (s : ℤ) (gp gm : ℕ)
    (x : SourceAssignment C.sources
      (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l))
    (c : HistoryChoices C.sources (Template.initial (2*(bulkSize depth L/2)) depth)
      (frequencyBound Bs BD Bz depth L) l) :
    ((assignedHistory C.sources (Template.initial (2*(bulkSize depth L/2)) depth)
      (frequencyBound Bs BD Bz depth L) l s gp gm x c).compensationProduct : ℝ) =
      choiceCompensation C c := by
  exact congrArg (fun n : ℕ => (n : ℝ))
    (decoded_compensationProduct_eq_draws C.sources _ _ l
      (assignedRoot C.sources _ s gp gm x) c (assignedRoot_matches C.sources _ s gp gm x))

theorem frame_left_compensation {outside : List ℕ} (r : Frame (l:=l) C outside) :
    (r.left.compensationProduct : ℝ) = choiceCompensation C r.leftChoices :=
  assigned_compensationProduct C r.s r.P.toNat r.Q.toNat r.leftSource r.leftChoices

theorem frame_right_compensation {outside : List ℕ} (r : Frame (l:=l) C outside) :
    (r.right.compensationProduct : ℝ) = choiceCompensation C r.rightChoices :=
  assigned_compensationProduct C r.t r.P.toNat r.Q.toNat r.rightSource r.rightChoices

theorem frame_oldCompensation {outside : List ℕ} (r : Frame (l:=l) C outside) :
    oldCompensation r.left r.right =
      (pairedChoiceCompensation C r.leftChoices r.rightChoices : ℂ) := by
  have hl := congrArg (fun x : ℝ => (x : ℂ)) (frame_left_compensation C r)
  have hr := congrArg (fun x : ℝ => (x : ℂ)) (frame_right_compensation C r)
  simpa only [oldCompensation, pairedChoiceCompensation, Complex.ofReal_mul,
    Complex.ofReal_natCast] using congrArg₂ (fun x y : ℂ => x*y) hl hr

theorem frame_norm_oldCompensation {outside : List ℕ} (r : Frame (l:=l) C outside) :
    ‖oldCompensation r.left r.right‖ =
      pairedChoiceCompensation C r.leftChoices r.rightChoices := by
  rw [frame_oldCompensation, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pairedChoiceCompensation_nonneg C _ _)]

theorem selected_pairedChoiceCompensation_error_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {depth : ℕ} (hk : 0 < depth) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz depth L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l ≤ depth,
      let seed := Template.initial (2*(bulkSize depth L/2)) depth
      let V := frequencyBound Bs BD Bz depth L
      (∑ c : HistoryChoices C.sources seed V l, ∑ e : HistoryChoices C.sources seed V l,
        choicesMass C.sources seed V l c * choicesMass C.sources seed V l e *
          (pairedChoiceCompensation C c e *
            (30*Real.exp (-Real.exp (ScaleBudget.giant.target*L))))) ≤
        Real.exp (-Real.exp ((21/2000 : ℝ)*L)) := by
  classical
  filter_upwards [HistoryGiantCompensationError.selected_choices_average_error_eventually
    d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd l hl
  let T := Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l
  let μ := assignmentPrior C.sources T
  have hm : 0 < ∑ x, μ.mass x := by rw [μ.mass_total]; norm_num
  obtain ⟨x, _, _hx⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun x _ => μ.mass_nonneg x)).mp hm
  let a := assignedRoot C.sources T 0 1 1 x
  have ha := assignedRoot_matches C.sources T 0 1 1 x
  have herr := hL E C hG hcl hcu hb hd (2*(bulkSize depth L/2)) l hl a a ha ha
  simpa only [pairedChoiceCompensation, choiceCompensation,
    decoded_compensationProduct_eq_draws C.sources _ _ l a _ ha] using herr

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
