import OAI.Combinatorics.BalancedRyser.Probability.ConditionalRestriction
import OAI.Combinatorics.BalancedRyser.Probability.FreshCoordinatePrescription
import OAI.Combinatorics.BalancedRyser.Probability.RootSuccess

namespace OAI

namespace Balanced.FreshTupleWitness

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
theorem tuplePoint_update_fresh (T : FourTuple F) (d : Direction F)
    (hd : ∀ i, T.generator i ≠ d) (M : MergedPairs F) (a : Bool → F) :
    tuplePoint (Function.update M d a) T = tuplePoint M T := by
  funext i
  simp only [tuplePoint, constituent, Function.update_of_ne (hd i),
    Function.update_of_ne (hd (i + 1))]

def pairPrescription (d : Direction F) (p r : Point F) (σ : Bool) : Bool → F :=
  fun b => if b = σ then lineEval d p else lineEval d r

omit [Fintype F] [DecidableEq F] in
theorem pairPrescription_iff (M : MergedPairs F) (d : Direction F)
    (p r : Point F) (σ : Bool) :
    M d = pairPrescription d p r σ ↔
      OnLine p (constituent M d σ) ∧ OnLine r (constituent M d (!σ)) := by
  constructor
  · intro h
    constructor
    · simpa [pairPrescription, OnLine, constituent] using
        (congrFun h σ).symm
    · simpa [pairPrescription, OnLine, constituent] using
        (congrFun h (!σ)).symm
  · rintro ⟨hp, hr⟩
    funext b
    cases σ <;> cases b <;>
      simp_all [pairPrescription, OnLine, constituent]

theorem oriented_pair_probability_of_update_invariant (T : FourTuple F) (d : Direction F)
    (hd : ∀ i, T.generator i ≠ d) (i j : Fin 4) (σ : Bool)
    (E : MergedPairs F → Prop)
    (hE : ∀ M a, E (Function.update M d a) ↔ E M) :
    offsetEventProbability {M | E M ∧
      OnLine (tuplePoint M T i) (constituent M d σ) ∧
      OnLine (tuplePoint M T j) (constituent M d (!σ))} =
      offsetEventProbability {M | E M} /
        (Fintype.card F : ℝ)^2 := by
  have h := FreshCoordinate.probability_prescription d
    E
    (fun M => pairPrescription d (tuplePoint M T i) (tuplePoint M T j) σ)
    hE
    (by intro M a; rw [tuplePoint_update_fresh T d hd])
  simp_rw [pairPrescription_iff] at h
  have hcard : (Fintype.card (Bool → F) : ℝ) = (Fintype.card F : ℝ)^2 := by
    simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow]
  rw [hcard] at h
  have hoff : offsetLaw F = PMF.uniformOfFintype (Direction F → Bool → F) := by
    ext M
    simp only [offsetLaw, PMF.uniformOfFintype_apply, Fintype.card_fun,
      Fintype.card_option, Fintype.card_bool]
  unfold offsetEventProbability
  rw [hoff]
  exact h

theorem oriented_pair_probability (T : FourTuple F) (d : Direction F)
    (hd : ∀ i, T.generator i ≠ d) (i j : Fin 4) (σ : Bool)
    (E : (Fin 4 → Point F) → Prop) :
    offsetEventProbability {M | E (tuplePoint M T) ∧
      OnLine (tuplePoint M T i) (constituent M d σ) ∧
      OnLine (tuplePoint M T j) (constituent M d (!σ))} =
      offsetEventProbability {M | E (tuplePoint M T)} /
        (Fintype.card F : ℝ)^2 := by
  exact oriented_pair_probability_of_update_invariant T d hd i j σ
    (fun M => E (tuplePoint M T))
    (by intro M a; rw [tuplePoint_update_fresh T d hd])

theorem oriented_pair_probability_on_event (T : FourTuple F) (d : Direction F)
    (hd : ∀ i, T.generator i ≠ d) (i j : Fin 4) (σ : Bool)
    (G : MergedPairs F → Prop) [Nonempty {M : MergedPairs F // G M}]
    (hG : ∀ M v, G (Function.update M d v) ↔ G M)
    (E : (Fin 4 → Point F) → Prop) :
    ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
      {M | E (tuplePoint M.1 T) ∧
        OnLine (tuplePoint M.1 T i) (constituent M.1 d σ) ∧
        OnLine (tuplePoint M.1 T j) (constituent M.1 d (!σ))}).toReal =
    ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
      {M | E (tuplePoint M.1 T)}).toReal / (Fintype.card F : ℝ)^2 := by
  have h := FreshCoordinate.probability_prescription_on_subtype d G
    (fun M => E (tuplePoint M T))
    (fun M => pairPrescription d (tuplePoint M T i) (tuplePoint M T j) σ)
    hG (by intro M v; rw [tuplePoint_update_fresh T d hd])
    (by intro M v; rw [tuplePoint_update_fresh T d hd])
  simp_rw [pairPrescription_iff] at h
  have hcard : (Fintype.card (Bool → F) : ℝ) = (Fintype.card F : ℝ)^2 := by
    simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow]
  rw [hcard] at h
  exact h

omit [Field F] [Fintype F] in
theorem fixed_coordinates_update_invariant (P : Direction F → Prop)
    (a : MergedPairs F) (d : Direction F) (hPd : ¬ P d)
    (M : MergedPairs F) (v : Bool → F) :
    (∀ t, P t → Function.update M d v t = a t) ↔
      (∀ t, P t → M t = a t) := by
  apply forall_congr'
  intro t
  by_cases ht : P t
  · have htd : t ≠ d := by intro heq; exact hPd (heq ▸ ht)
    simp only [Function.update_of_ne htd]
  · simp only [ht, false_implies]

theorem successful_oriented_pair_probability (T : FourTuple F)
    (hT : Function.Injective T.generator) (g d : Direction F)
    (hd : ∀ i, T.generator i ≠ d) (i j : Fin 4) (σ : Bool) :
    offsetEventProbability {M |
      ((∃ c, ∀ k, OnLine (tuplePoint M T k) (g,c)) ∧
        Function.Injective (tuplePoint M T)) ∧
      OnLine (tuplePoint M T i) (constituent M d σ) ∧
      OnLine (tuplePoint M T j) (constituent M d (!σ))} =
      ((Fintype.card F).descFactorial 4 : ℝ) / (Fintype.card F : ℝ)^9 := by
  rw [oriented_pair_probability T d hd i j σ
      (fun p => (∃ c, ∀ k, OnLine (p k) (g,c)) ∧ Function.Injective p),
    TupleAlignment.tuplePoint_success_probability T hT g]
  ring

theorem successful_oriented_pair_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g d : Direction F)
    (hd : ∀ i, T.generator i ≠ d) (i j : Fin 4) (σ : Bool) :
    offsetEventProbability {M |
      ((∃ c, ∀ k, OnLine (tuplePoint M T k) (g,c)) ∧
        Function.Injective (tuplePoint M T)) ∧
      OnLine (tuplePoint M T i) (constituent M d σ) ∧
      OnLine (tuplePoint M T j) (constituent M d (!σ))} ≤
      1 / (Fintype.card F : ℝ)^5 := by
  rw [successful_oriented_pair_probability T hT g d hd i j σ]
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hdesc : ((Fintype.card F).descFactorial 4 : ℝ) ≤
      (Fintype.card F : ℝ)^4 := by
    exact_mod_cast Nat.descFactorial_le_pow (Fintype.card F) 4
  calc
    _ ≤ (Fintype.card F : ℝ)^4 / (Fintype.card F : ℝ)^9 :=
      div_le_div_of_nonneg_right hdesc (by positivity)
    _ = _ := by field_simp

end
end Balanced.FreshTupleWitness

end OAI
