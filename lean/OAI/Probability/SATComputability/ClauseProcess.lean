import OAI.Probability.SATComputability.ActiveMaskCounts
import OAI.Probability.SATComputability.PoissonGrid
import OAI.Probability.SATComputability.FiniteProductPushforward

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

theorem countsMask_restored {A : Type*} [Fintype A] {n : ℕ}
    (B F T : A → Finset (DeletionCandidate n)) (c : A → ℕ) :
    countsMask (fun a => restoredMask (B a) (F a) (T a)) c =
      restoredMask (countsMask B c) (countsMask F c) (countsMask T c) := by
  ext x
  simp only [countsMask, restoredMask, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases x 0 with _ | (_ | _)
  all_goals simp only [and_true, or_and_left, forall_and]

def splitActiveGrid (n M : ℕ) : ActiveClause n × Fin M ≃
    (Triple (SignedLiteral n) × Fin M) ⊕
      ((IncidentClass n × Fin M) ⊕ (IncidentClass n × Fin M)) where
  toFun p := match p.1 with
    | .inl a => .inl (a,p.2)
    | .inr (false,a) => .inr (.inl (a,p.2))
    | .inr (true,a) => .inr (.inr (a,p.2))
  invFun p := match p with
    | .inl (a,j) => (.inl a,j)
    | .inr (.inl (a,j)) => (.inr (false,a),j)
    | .inr (.inr (a,j)) => (.inr (true,a),j)
  left_inv := by rintro ⟨a,j⟩; rcases a with a | ⟨(_ | _),a⟩ <;> rfl
  right_inv := by rintro (⟨a,j⟩ | (⟨a,j⟩ | ⟨a,j⟩)) <;> rfl

noncomputable def maskGrid {A : Type*} [Fintype A] {n M : ℕ}
    (mask : A → Finset (DeletionCandidate n)) (c : A × Fin M → ℕ) :
    Fin M → Finset (DeletionCandidate n) := fun j => countsMask mask (fun a => c (a,j))

local instance clauseProcessCandidateMeasurable (n : ℕ) :
    MeasurableSpace (DeletionCandidate n) := ⊤
local instance clauseProcessCandidateSingleton (n : ℕ) :
    MeasurableSingletonClass (DeletionCandidate n) := ⟨fun _ => trivial⟩

noncomputable def gridMaskLaw {A : Type*} [Fintype A] {n : ℕ}
    (M : ℕ) (r : ℝ≥0) (mask : A → Finset (DeletionCandidate n)) :
    FiniteLaw (Fin M → Finset (DeletionCandidate n)) :=
  finitePushforward (poissonCountLaw (A × Fin M) r) (maskGrid mask)
    (measurable_of_countable _)

theorem gridMaskLaw_expect {A : Type*} [Fintype A] {n M : ℕ}
    (r : ℝ≥0) (mask : A → Finset (DeletionCandidate n))
    (f : (Fin M → Finset (DeletionCandidate n)) → ℝ) :
    (gridMaskLaw M r mask).expect f =
      ∫ c, f (maskGrid mask c) ∂poissonCountLaw (A × Fin M) r :=
  finitePushforward_expect _ _ _ _

theorem gridMaskLaw_frontload {A : Type*} [Fintype A] {n M : ℕ}
    (r : ℝ≥0) (mask : A → Finset (DeletionCandidate n))
    (f : Finset (DeletionCandidate n) → ℝ) :
    (gridMaskLaw M r mask).expect (fun xs => f (frontloadMask xs)) =
      ∫ c, f (countsMask mask c) ∂poissonCountLaw A (M*r) := by
  rw [gridMaskLaw_expect]
  have hfront (c : A × Fin M → ℕ) : frontloadMask (maskGrid mask c) =
      countsMask mask (fun a => ∑ j, c (a,j)) :=
    frontload_countsMask mask (fun j a => c (a,j))
  simp only [hfront]
  rw [← poissonCountLaw_uncurry_integral]
  have hh := poissonCountLaw_row_sums (A := A) (B := Fin M) r
  have h := integral_map (φ := fun c : A → Fin M → ℕ => fun a => ∑ j, c a j)
    (μ := Measure.pi (fun _ : A => poissonCountLaw (Fin M) r))
    (f := fun c => f (countsMask mask c))
    (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable
  rw [hh] at h
  simpa only [Fintype.card_fin] using h.symm

end FixedClauseThreshold.Computability

end OAI
