import Mathlib
import OAI.Probability.SphericalField.Positivity.ReplicaMean

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
def triangleEvent (a b c t : ℝ) : Set OverlapArray :=
  {Q | Q 0 1 < a ∧ b < Q 0 2 ∧ Q 0 2 < t ∧ c < Q 1 2 ∧ Q 1 2 < t}

lemma triangleEvent_pattern {a b c t : ℝ} (hat : a ≤ t) (Q : OverlapArray)
    (hSym : ∀ i j, Q i j = Q j i) (hQ : Q ∈ triangleEvent a b c t) :
    overlapBlock id 3 Q ∈ patternMatrices (tripleLabels 3) (triangleConstraints a b c t) := by
  have h10 := hSym 1 0
  have h20 := hSym 2 0
  have h21 := hSym 2 1
  have hQt : Q 0 1 < t := hQ.1.trans_le hat
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [overlapBlock, tripleLabels, triangleConstraints, triangleEvent]

lemma gg_triangleEvent_null (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1)
    {a b c t : ℝ} (hab : a ≤ b) (hat : a ≤ t) (hgap : 2 * (t - c) < (b - a) ^ 2) :
    μ (triangleEvent a b c t) = 0 := by
  by_contra hne
  have hpos : 0 < μ.real (triangleEvent a b c t) :=
    ENNReal.toReal_pos hne (measure_ne_top _ _)
  have hle : μ.real (triangleEvent a b c t) ≤ μ.real
      (overlapBlock id 3 ⁻¹' patternMatrices (tripleLabels 3) (triangleConstraints a b c t)) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hSym] with Q hQ
    exact triangleEvent_pattern hat Q hQ
  exact hgap.not_ge (gg_triangle_pattern_bound μ hEx hGG hSym hGram hdiag hab hat (hpos.trans_le hle))

lemma exists_rational_triangle_box {x y z : ℝ} (hxy : x < y) (hyz : y ≤ z) :
    ∃ a b c t : ℚ, (a : ℝ) ≤ b ∧ (a : ℝ) ≤ t ∧
      2 * ((t : ℝ) - c) < ((b : ℝ) - a) ^ 2 ∧
      x < a ∧ (b : ℝ) < y ∧ y < t ∧ (c : ℝ) < z ∧ z < t := by
  obtain ⟨a, hxa, hay⟩ := exists_rat_btwn hxy
  obtain ⟨b, hab, hby⟩ := exists_rat_btwn hay
  have hδ : 0 < ((b : ℝ) - a) ^ 2 / 8 := by positivity
  obtain ⟨c, hzc, hcz⟩ := exists_rat_btwn (show z - ((b : ℝ) - a) ^ 2 / 8 < z by linarith)
  obtain ⟨t, hzt, htz⟩ := exists_rat_btwn (show z < z + ((b : ℝ) - a) ^ 2 / 8 by linarith)
  refine ⟨a, b, c, t, hab.le, (hay.trans_le hyz).le.trans hzt.le, ?_, hxa, hby,
    hyz.trans_lt hzt, hcz, hzt⟩
  nlinarith

lemma gg_no_ordered_crossing (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1) :
    ∀ᵐ Q ∂μ, ¬ (Q 0 1 < Q 0 2 ∧ Q 0 2 ≤ Q 1 2) := by
  have hBoxes : ∀ᵐ Q ∂μ, ∀ a b c t : ℚ,
      (a : ℝ) ≤ b → (a : ℝ) ≤ t → 2 * ((t : ℝ) - c) < ((b : ℝ) - a) ^ 2 →
      Q ∉ triangleEvent a b c t := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    apply ae_all_iff.mpr
    intro c
    apply ae_all_iff.mpr
    intro t
    by_cases hab : (a : ℝ) ≤ b
    · by_cases hat : (a : ℝ) ≤ t
      · by_cases hgap : 2 * ((t : ℝ) - c) < ((b : ℝ) - a) ^ 2
        · filter_upwards [measure_eq_zero_iff_ae_notMem.mp
            (gg_triangleEvent_null μ hEx hGG hSym hGram hdiag hab hat hgap)] with Q hQ
          exact fun _ _ _ => hQ
        · exact Eventually.of_forall fun _ _ _ h => (hgap h).elim
      · exact Eventually.of_forall fun _ _ h => (hat h).elim
    · exact Eventually.of_forall fun _ h => (hab h).elim
  filter_upwards [hBoxes] with Q hQ
  rintro ⟨hxy, hyz⟩
  obtain ⟨a, b, c, t, hab, hat, hgap, hbox⟩ := exists_rational_triangle_box hxy hyz
  exact hQ a b c t hab hat hgap hbox

lemma gram_array_symmetric (Q : OverlapArray)
    (hGram : ∀ n, Matrix.PosSemidef (overlapBlock id n Q)) : ∀ i j, Q i j = Q j i := by
  intro i j
  let n := max i j + 1
  let a : Fin n := ⟨i, by dsimp [n]; omega⟩
  let b : Fin n := ⟨j, by dsimp [n]; omega⟩
  have h := (hGram n).isHermitian.apply b a
  simpa [overlapBlock, a, b] using h

theorem gg_ultrametric (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1) :
    ∀ᵐ Q ∂μ, min (Q 0 1) (Q 0 2) ≤ Q 1 2 := by
  have hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i :=
    hGram.mono fun Q hQ => gram_array_symmetric Q hQ
  have hno := gg_no_ordered_crossing μ hEx hGG hSym hGram hdiag
  have hno' := (hEx 0 1).quasiMeasurePreserving.ae hno
  have hsmall : ∀ᵐ Q ∂μ, min (Q 0 2) (Q 1 2) ≤ Q 0 1 := by
    filter_upwards [hno, hno', hSym] with Q hQ hQ' hs
    simp only [relabelArray, Equiv.swap_apply_left, Equiv.swap_apply_right,
      show Equiv.swap (0 : ℕ) 1 2 = 2 from by decide] at hQ'
    rw [hs 1 0] at hQ'
    by_cases h : Q 0 2 ≤ Q 1 2
    · rw [min_eq_left h]
      exact le_of_not_gt fun hh => hQ ⟨hh, h⟩
    · have h' := le_of_lt (lt_of_not_ge h)
      rw [min_eq_right h']
      exact le_of_not_gt fun hh => hQ' ⟨hh, h'⟩
  have hsmall' := (hEx 0 2).quasiMeasurePreserving.ae hsmall
  filter_upwards [hsmall', hSym] with Q hQ hs
  simp only [relabelArray, Equiv.swap_apply_left, Equiv.swap_apply_right,
    show Equiv.swap (0 : ℕ) 2 1 = 1 from by decide] at hQ
  simpa only [hs 2 0, hs 1 0, hs 2 1, min_comm] using hQ

abbrev PairedOverlapArray := ℕ → ℕ → ℝ × ℝ
abbrev PairedOverlapBlock (n : ℕ) := Fin n → Fin n → ℝ × ℝ

def pairedBlock (n : ℕ) (Q : PairedOverlapArray) : PairedOverlapBlock n :=
  fun i j => Q i j

def pairedRelabel (π : Equiv.Perm ℕ) (Q : PairedOverlapArray) : PairedOverlapArray :=
  fun i j => Q (π i) (π j)

def PairedSwapInvariant (μ : Measure PairedOverlapArray) : Prop :=
  ∀ i j : ℕ, MeasurePreserving (pairedRelabel (Equiv.swap i j)) μ μ

def JointGhirlandaGuerra (μ : Measure PairedOverlapArray) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (i : Fin n) (s : Set (PairedOverlapBlock n)), MeasurableSet s →
    ∀ t : Set (ℝ × ℝ), MeasurableSet t →
    μ.real (pairedBlock n ⁻¹' s ∩ {Q | Q i n ∈ t}) =
      μ.real (pairedBlock n ⁻¹' s) * μ.real {Q | Q 0 1 ∈ t} / n +
      (∑ j ∈ (Finset.univ.erase i),
        μ.real (pairedBlock n ⁻¹' s ∩ {Q | Q i j ∈ t})) / n

def scalarArray (f : ℝ × ℝ → ℝ) (Q : PairedOverlapArray) : OverlapArray :=
  fun i j => f (Q i j)

def scalarBlock (f : ℝ × ℝ → ℝ) {n : ℕ} (Q : PairedOverlapBlock n) : OverlapBlock n :=
  fun i j => f (Q i j)

lemma scalarArray_measurable {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    Measurable (scalarArray f) := by
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hf.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

lemma scalarBlock_measurable {f : ℝ × ℝ → ℝ} (hf : Measurable f) {n : ℕ} :
    Measurable (scalarBlock f (n := n)) := by
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hf.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

lemma scalarArray_swap_invariant (μ : Measure PairedOverlapArray)
    (hEx : PairedSwapInvariant μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    OverlapSwapInvariant (μ.map (scalarArray f)) := by
  intro i j
  have heq : relabelArray (Equiv.swap i j) ∘ scalarArray f =
      scalarArray f ∘ pairedRelabel (Equiv.swap i j) := rfl
  refine ⟨Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _), ?_⟩
  rw [Measure.map_map _ (scalarArray_measurable hf), heq,
    ← Measure.map_map (scalarArray_measurable hf) (hEx i j).measurable,
    (hEx i j).map_eq]
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma scalarArray_gg (μ : Measure PairedOverlapArray)
    (hGG : JointGhirlandaGuerra μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    GhirlandaGuerra (μ.map (scalarArray f)) id := by
  intro n hn i s hs t ht
  have hblock : Measurable (overlapBlock (id : OverlapArray → OverlapArray) n) :=
    Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
      (measurable_pi_apply _).comp (measurable_pi_apply _)
  have hedge (i j : ℕ) : Measurable (fun Q : OverlapArray => Q i j) :=
    (measurable_pi_apply _).comp (measurable_pi_apply _)
  have hmap (u : Set OverlapArray) (hu : MeasurableSet u) :
      (μ.map (scalarArray f)).real u = μ.real (scalarArray f ⁻¹' u) := by
    exact map_measureReal_apply (scalarArray_measurable hf) hu
  simp only [id_eq]
  rw [hmap (overlapBlock id n ⁻¹' s ∩ {Q | Q i n ∈ t})
      ((hs.preimage hblock).inter (ht.preimage (hedge i n))),
    hmap _ (hs.preimage hblock), hmap {Q | Q 0 1 ∈ t} (ht.preimage (hedge 0 1))]
  have hmj (j : Fin n) := hmap (overlapBlock id n ⁻¹' s ∩ {Q | Q i j ∈ t})
    ((hs.preimage hblock).inter (ht.preimage (hedge i j)))
  simp_rw [hmj]
  exact hGG n hn i (scalarBlock f ⁻¹' s) (hs.preimage (scalarBlock_measurable hf))
    (f ⁻¹' t) (ht.preimage hf)

end SphericalPerceptron
end
end

end OAI
