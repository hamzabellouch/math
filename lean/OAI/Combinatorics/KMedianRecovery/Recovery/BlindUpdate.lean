import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplingRate

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open MetricKMedianRecovery RadiusMenus Guided FixedDyadic FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable local instance (D : Finset V) (M E J : ℕ) : DecidableEq (Action D M E J) := Classical.decEq _

noncomputable abbrev blindUpdate (D F S : Finset V) (hD : D.Nonempty)
    (Δ P : ℝ) (m : ℕ) :=
  update D F S hD Δ P mainKappa m (firstSize mainKappa)
    (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa m)

noncomputable def blindPrecision (D F S : Finset V) (hD : D.Nonempty)
    (Δ P : ℝ) (m : ℕ) : ℕ :=
  Classical.choose (FixedDyadic.exists_precision (blindUpdate D F S hD Δ P m)
    (mainActual D S Δ m) (2*m) (some State.initial))

lemma blindPrecision_spec (D F S : Finset V) (hD : D.Nonempty)
    (Δ P : ℝ) (m : ℕ) :
    Precise (blindUpdate D F S hD Δ P m) (mainActual D S Δ m)
      (blindPrecision D F S hD Δ P m) (2*m) (some State.initial) :=
  Classical.choose_spec (FixedDyadic.exists_precision (blindUpdate D F S hD Δ P m)
    (mainActual D S Δ m) (2*m) (some State.initial))

noncomputable abbrev BlindBits (D F S : Finset V) (hD : D.Nonempty)
    (Δ P : ℝ) (m : ℕ) := Fin (2*m) → Fin (blindPrecision D F S hD Δ P m) → Bool

noncomputable def blindActions (D F S : Finset V) (hD : D.Nonempty)
    (Δ P : ℝ) (m : ℕ) (bits : BlindBits D F S hD Δ P m) : Fin (2*m) → MainAction D m :=
  actions (blindUpdate D F S hD Δ P m) (mainActual D S Δ m)
    (blindPrecision D F S hD Δ P m) (Sum.inl ()) (2*m) (some State.initial) bits

theorem fair_records_success {D S O : Finset V}
    (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    (1/2:ℝ)^(2*C.bad.card) * samplingBound C.bad.card ≤
      probability (fun bits => Hits
        (blindUpdate D F S hD Δ (comparisonCost D C.assign) C.bad.card)
        (C.stop hD Δ) (2*C.bad.card) (some State.initial)
        (blindActions D F S hD Δ (comparisonCost D C.assign) C.bad.card bits)) := by
  have hh := event_lower
    (blindUpdate D F S hD Δ (comparisonCost D C.assign) C.bad.card)
    (mainActual D S Δ C.bad.card)
    (blindPrecision D F S hD Δ (comparisonCost D C.assign) C.bad.card)
    (Sum.inl ()) (2*C.bad.card) (some State.initial)
    (blindPrecision_spec D F S hD Δ (comparisonCost D C.assign) C.bad.card)
    (Hits (blindUpdate D F S hD Δ (comparisonCost D C.assign) C.bad.card)
      (C.stop hD Δ) (2*C.bad.card) (some State.initial))
  exact (mul_le_mul_of_nonneg_left (C.actual_records_success hD F hOF Δ hΔ hP hm)
    (by positivity)).trans hh

theorem fair_prefix_exponential : ∃ c : ℝ, 0 < c ∧
    ∀ {D S O : Finset V} (C : Comparison D S O) (hD : D.Nonempty)
      (F : Finset V), O ⊆ F → ∀ Δ : ℝ, 0 ≤ Δ →
      0 < comparisonCost D C.assign → 0 < C.bad.card →
      Real.exp (-c*C.bad.card) ≤ probability (fun bits => Hits
        (blindUpdate D F S hD Δ (comparisonCost D C.assign) C.bad.card)
        (C.stop hD Δ) (2*C.bad.card) (some State.initial)
        (blindActions D F S hD Δ (comparisonCost D C.assign) C.bad.card bits)) := by
  obtain ⟨c,hc,h⟩ := sampling_exponential
  exact ⟨c,hc,fun C hD F hOF Δ hΔ hP hm =>
    (h C.bad.card).trans (C.fair_records_success hD F hOF Δ hΔ hP hm)⟩

end MetricKMedianRecovery.Sampling.Comparison

namespace MetricKMedianRecovery.Sampling.Precision
open RadiusMenus Guided FixedDyadic FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

def Good (s : Option (State V)) : Prop :=
  ∀ t, s = some t → ∀ z ∈ t.leaves, (1:ℝ) ≤ z.2

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma good_initial : Good (some (State.initial : State V)) := by
  intro s hs
  cases Option.some.inj hs
  simp [State.initial]

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma good_retain (m : ℕ) (s : State V) (hs : ∀ z ∈ s.leaves, (1:ℝ) ≤ z.2) :
    Good (retain m s) := by
  intro t ht
  unfold retain at ht
  split_ifs at ht
  cases Option.some.inj ht
  exact hs

lemma good_update (D F S : Finset V) (hD : D.Nonempty) (Δ P kappa : ℝ)
    (m M E J : ℕ) (s : Option (State V)) (a : Action D M E J)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f) (hs : Good s) :
    Good (update D F S hD Δ P kappa m M E J s a) := by
  cases s with
  | none => simp only [update,Good,reduceCtorEq,IsEmpty.forall_iff,implies_true]
  | some s =>
    have hrad := hs s rfl
    simp only [update]
    split_ifs with hw
    · rcases a with u | (w | ⟨w,e⟩)
      · simp [Good]
      · cases he : ofLex (chosen S Δ s w) with
        | inl v =>
          simp only [he]
          apply good_retain
          simpa only [State.remove] using hrad
        | inr j => simp [he,Good]
      · cases hr : menuRadius D hD P kappa m M E J s w e with
        | none => simp [hr,Good]
        | some R =>
          simp only [hr]
          split_ifs with hb
          · apply good_retain
            obtain ⟨f,hf⟩ := hb
            have hR := (hsep w w.property f (Finset.mem_filter.mp hf).1).trans
              (Finset.mem_filter.mp hf).2
            intro z hz
            simp only [State.add,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
            rcases hz with hz | hz
            · exact hrad z hz
            · simpa only [hz] using hR
          · simp [Good]
    · simp [Good]

lemma client_lower (D F S : Finset V) (hSF : S ⊆ F) (Δ : ℝ) (hΔ : 1 ≤ Δ)
    (s : State V) (hs : ∀ z ∈ s.leaves, (1:ℝ) ≤ z.2)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f)
    (w : V) (hw : w ∈ D) : 1 ≤ clientWeight S Δ s w := by
  apply le_trans _ (le_max_right _ _)
  unfold reference tagDistance
  have hc := chosen_mem S Δ s w
  cases he : ofLex (chosen S Δ s w) with
  | inl v =>
    have hc' : v ∈ S \ s.deleted := by
      apply (real_mem_tags S s v).mp
      simpa only [realTag,← he,toLex_ofLex] using hc
    exact hsep w hw v (hSF (Finset.mem_sdiff.mp hc').1)
  | inr j =>
    cases j with
    | zero => exact hΔ
    | succ j =>
      cases hz : s.leaves[j]? with
      | none => simpa only [hz] using hΔ
      | some z =>
        have hzmem : z ∈ s.leaves := List.mem_of_getElem? hz
        simpa only [hz] using (hs z hzmem).trans
          (le_add_of_nonneg_left (dist_nonneg : 0 ≤ dist w z.1))

lemma total_upper (D S : Finset V) (Δ : ℝ) (hΔ : 0 ≤ Δ) (s : State V) :
    totalWeight D S Δ s ≤ (D.card:ℝ)*Δ := by
  unfold totalWeight
  calc
    ∑ w ∈ D, clientWeight S Δ s w ≤ ∑ _w ∈ D, Δ := by
      apply Finset.sum_le_sum
      intro w _
      exact max_le hΔ (reference_le_diameter S Δ s w)
    _ = (D.card:ℝ)*Δ := by simp

end MetricKMedianRecovery.Sampling.Precision

end OAI
