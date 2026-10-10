import Mathlib
import OAI.Probability.SphericalField.Control.HeatChain

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma expected_intervalControlCost_full (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    (∫ ω, intervalControlCost m v 0 1 ω ∂P) = (controlCost P m v).toReal := by
  simp only [intervalControlCost_full m v _ (progressive_time_measurable P hv _)]
  exact integral_pathControlCost P m hv hc

lemma Jet3.lipschitz (g : Jet3) : LipschitzWith ‖g.d1‖₊ g.f := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (g.has1 x).differentiableAt)
  intro x
  rw [g.deriv_eq]
  exact_mod_cast g.d1.norm_coe_le_norm x

lemma HeatChain.controlValue_eq {m : Trial} {g h : Jet3}
    (H : HeatChain m g 0 1 h) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) : controlValue P g.f m = h.f 0 := by
  apply le_antisymm
  · apply controlValue_le_of_bounded_controls P g.f m ‖g.d1‖₊ g.lipschitz
    intro v hv hc hL
    have hh := H.upper P hB ‖g.d1‖₊ hv hL
    have he : (∫ ω, h.f (controlledPrefix m v 0 ω) ∂P) = h.f 0 := by
      calc
        _ = ∫ _ω : BrownianPath, h.f 0 ∂P := integral_congr_ae (by
          filter_upwards [controlledPrefix_zero P hB m v] with ω hω
          rw [hω])
        _ = _ := by simp
    rw [he,expected_intervalControlCost_full P m hv hc] at hh
    simp only [controlledPrefix_one] at hh
    exact hh
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨K,w,hw,hwK,_,hwval⟩ := H.lower P hB 0 (fun _ _ => 0) (progressive_zero P)
      (by simp) hε
    have hc : controlCost P m w < ∞ := (controlCost_le_bound P m K hwK).trans_lt (by finiteness)
    have he : (∫ ω, h.f (controlledPrefix m (fun _ _ => 0) 0 ω) ∂P) = h.f 0 := by
      calc
        _ = ∫ _ω : BrownianPath, h.f 0 ∂P := integral_congr_ae (by
          filter_upwards [controlledPrefix_zero P hB m (fun _ _ => 0)] with ω hω
          rw [hω])
        _ = _ := by simp
    rw [he,expected_intervalControlCost_full P m hw hc] at hwval
    simp only [controlledPrefix_one] at hwval
    have hsup : controlPayoff P g.f m w ≤ controlValue P g.f m :=
      le_csSup (controlPayoffs_bddAbove P g.f m) ⟨w,hw,hc,rfl⟩
    change h.f 0 - ε ≤ controlPayoff P g.f m w at hwval
    linarith

lemma ultrametric_extension_row {ι L : Type*} [LinearOrder L]
    (A : ι → ι → L) (v : ι → L) (i : ι)
    (hmax : ∀ j, v j ≤ v i)
    (hlo : ∀ j, min (v i) (A i j) ≤ v j)
    (hhi : ∀ j, min (v i) (v j) ≤ A i j) :
    ∀ j, v j = min (v i) (A i j) := by
  intro j
  apply le_antisymm
  · apply le_min (hmax j)
    simpa only [min_eq_right (hmax j)] using hhi j
  · exact hlo j

lemma finite_measure_eq_of_maximal_coordinates
    {ι L : Type*} [Fintype ι] [Nonempty ι] [Fintype L] [LinearOrder L]
    [MeasurableSpace L] [MeasurableSingletonClass L]
    (μ ν : Measure (ι → L)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (S : Set (ι → L)) (hμ : ∀ᵐ v ∂μ, v ∈ S) (hν : ∀ᵐ v ∂ν, v ∈ S)
    (htri : ∀ v ∈ S, ∀ i, (∀ j, v j ≤ v i) → ∀ w ∈ S,
      w i = v i → (∀ j, w j ≤ v i) → w = v)
    (hcoord : ∀ i c, μ.real {v | v i = c} = ν.real {v | v i = c}) : μ = ν := by
  classical
  have hout (v : ι → L) (hv : v ∉ S) : μ.real {v} = 0 ∧ ν.real {v} = 0 := by
    have he (ρ : Measure (ι → L)) (hρ : ∀ᵐ w ∂ρ, w ∈ S) : ρ {v} = 0 :=
      measure_mono_null (by simpa using hv) (ae_iff.mp hρ)
    simp only [measureReal_def,he μ hμ,he ν hν,ENNReal.toReal_zero,and_self]
  have hmass : ∀ v : ι → L, μ.real {v} = ν.real {v} := by
    by_contra h
    have hex : ∃ v : ι → L, μ.real {v} ≠ ν.real {v} := by simpa only [not_forall] using h
    let D : Finset (ι → L) := Finset.univ.filter fun v => μ.real {v} ≠ ν.real {v}
    have hD : D.Nonempty := by obtain ⟨v,hv⟩ := hex; exact ⟨v,by simp [D,hv]⟩
    let M (v : ι → L) : L := (Finset.univ.image v).max' (Finset.univ_nonempty.image v)
    have hbound (v : ι → L) (i : ι) : v i ≤ M v :=
      Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    obtain ⟨v,hv,hvmax⟩ := D.exists_max_image M hD
    have hvneq : μ.real {v} ≠ ν.real {v} := (Finset.mem_filter.mp hv).2
    have hvS : v ∈ S := by by_contra hh; exact hvneq (by rw [(hout v hh).1,(hout v hh).2])
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.max'_mem (Finset.univ.image v) (Finset.univ_nonempty.image v))
    change v i = M v at hi
    have hpivot : ∀ j, v j ≤ v i := fun j => (hbound v j).trans_eq hi.symm
    have hother (w : ι → L) (hwi : w i = v i) (hwv : w ≠ v) : μ.real {w} = ν.real {w} := by
      by_contra hw
      have hwD : w ∈ D := by simp [D,hw]
      have hwS : w ∈ S := by by_contra hh; exact hw (by rw [(hout w hh).1,(hout w hh).2])
      apply hwv
      apply htri v hvS i hpivot w hwS hwi
      intro j
      exact ((hbound w j).trans (hvmax w hwD)).trans_eq hi.symm
    let T : Finset (ι → L) := Finset.univ.filter fun w => w i = v i
    have hvT : v ∈ T := by simp [T]
    have hT : (T : Set (ι → L)) = {w | w i = v i} := by ext w; simp [T]
    have he := hcoord i (v i)
    rw [← hT,← sum_measureReal_singleton,← sum_measureReal_singleton] at he
    rw [← Finset.sum_erase_add _ _ hvT,← Finset.sum_erase_add _ _ hvT] at he
    have hs : (∑ w ∈ T.erase v, μ.real {w}) = ∑ w ∈ T.erase v, ν.real {w} := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hother w (by simpa [T] using (Finset.mem_erase.mp hw).2) (Finset.mem_erase.mp hw).1
    rw [hs] at he
    exact hvneq (add_left_cancel he)
  exact Measure.ext_of_singleton fun v =>
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp (hmass v)

lemma finite_ultrametric_row_law_unique
    {ι L : Type*} [Fintype ι] [Nonempty ι] [Fintype L] [LinearOrder L]
    [MeasurableSpace L] [MeasurableSingletonClass L]
    (A : ι → ι → L) (μ ν : Measure (ι → L)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ v ∂μ, ∀ i j, min (v i) (A i j) ≤ v j ∧ min (v i) (v j) ≤ A i j)
    (hν : ∀ᵐ v ∂ν, ∀ i j, min (v i) (A i j) ≤ v j ∧ min (v i) (v j) ≤ A i j)
    (hcoord : ∀ i c, μ.real {v | v i = c} = ν.real {v | v i = c}) : μ = ν := by
  apply finite_measure_eq_of_maximal_coordinates μ ν
    {v | ∀ i j, min (v i) (A i j) ≤ v j ∧ min (v i) (v j) ≤ A i j} hμ hν ?_ hcoord
  intro v hv i hmax w hw hwi hwmax
  have hvrow := ultrametric_extension_row A v i hmax
    (fun j => (hv i j).1) (fun j => (hv i j).2)
  have hwrow := ultrametric_extension_row A w i (by simpa only [hwi] using hwmax)
    (fun j => (hw i j).1) (fun j => (hw i j).2)
  funext j
  rw [hwrow j,hvrow j,hwi]

abbrev FiniteOverlap (L : Type*) := ℕ → ℕ → L
abbrev FiniteBlock (L : Type*) (n : ℕ) := Fin n → Fin n → L

def finiteBlock {L : Type*} (n : ℕ) (R : FiniteOverlap L) : FiniteBlock L n :=
  fun i j => R i j

def finiteRow {L : Type*} (n : ℕ) (R : FiniteOverlap L) : Fin n → L :=
  fun i => R i n

def FiniteGG {L : Type*} [MeasurableSpace L] (μ : Measure (FiniteOverlap L)) : Prop :=
  ∀ n, 1 ≤ n → ∀ (i : Fin n) (A : FiniteBlock L n) (c : L),
    μ.real {R | finiteBlock n R = A ∧ R i n = c} =
      μ.real {R | finiteBlock n R = A} * μ.real {R | R 0 1 = c} / n +
      (∑ j ∈ Finset.univ.erase i, μ.real {R | finiteBlock n R = A ∧ R i j = c}) / n

lemma finiteBlock_measurable {L : Type*} [MeasurableSpace L] (n : ℕ) :
    Measurable (finiteBlock (L := L) n) :=
  Measurable.of_eval fun row => Measurable.of_eval fun column =>
    (measurable_pi_apply (column : ℕ)).comp (measurable_pi_apply (row : ℕ))

lemma finiteRow_measurable {L : Type*} [MeasurableSpace L] (n : ℕ) :
    Measurable (finiteRow (L := L) n) :=
  Measurable.of_eval fun row =>
    (measurable_pi_apply n).comp (measurable_pi_apply (row : ℕ))

def finiteFiberRow {L : Type*} [MeasurableSpace L]
    (μ : Measure (FiniteOverlap L)) (n : ℕ) (A : FiniteBlock L n) : Measure (Fin n → L) :=
  (μ.restrict {R | finiteBlock n R = A}).map (finiteRow n)

lemma finiteFiberRow_real {L : Type*} [Fintype L] [MeasurableSpace L]
    [MeasurableSingletonClass L] (μ : Measure (FiniteOverlap L))
    (n : ℕ) (A : FiniteBlock L n) (i : Fin n) (c : L) :
    (finiteFiberRow μ n A).real {v | v i = c} =
      μ.real {R | finiteBlock n R = A ∧ R i n = c} := by
  rw [measureReal_def,finiteFiberRow,Measure.map_apply (finiteRow_measurable n)
    (show MeasurableSet {v : Fin n → L | v i = c} from (Set.to_countable _).measurableSet),
    Measure.restrict_apply ((finiteRow_measurable n) ((Set.to_countable _).measurableSet))]
  congr 1
  congr 1
  ext R
  simp [finiteRow,and_comm]

end SphericalPerceptron
end
end

end OAI
