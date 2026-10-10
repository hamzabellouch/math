import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.MassBounds

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

universe u
namespace CurrentOperations
attribute [local instance] Classical.propDecidable
variable {X : Type u} {Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma boundedLip_comp {b : Y → ℝ} (hb : BoundedLip b) {f : X → Y}
    {K : ℝ≥0} (hf : LipschitzWith K f) : BoundedLip (b ∘ f) := by
  obtain ⟨⟨L, hL⟩, M, hM⟩ := hb
  exact ⟨⟨L*K, hL.comp hf⟩, M, fun x => hM (f x)⟩

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma admissible_comp {k : ℕ} {b : Y → ℝ} {π : Fin k → Y → ℝ}
    (h : Admissible b π) {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Admissible (b ∘ f) (fun i => π i ∘ f) := by
  refine ⟨boundedLip_comp h.1 hf, fun i => ?_⟩
  obtain ⟨L, hL⟩ := h.2 i
  exact ⟨L*K, hL.comp hf⟩

noncomputable def pushCurrent {k : ℕ} (f : X → Y) (T : Functional X k) : Functional Y k :=
  fun b π => if Admissible b π then T (b ∘ f) (fun i => π i ∘ f) else 0

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma pushCurrent_apply {k : ℕ} (f : X → Y) (T : Functional X k)
    {b : Y → ℝ} {π : Fin k → Y → ℝ} (h : Admissible b π) :
    pushCurrent f T b π = T (b ∘ f) (fun i => π i ∘ f) := ite_eq_left h

lemma pushCurrent_controls {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    {μ : Measure X} (hμ : Controls T μ) {f : X → Y} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    Controls (pushCurrent f T) ((↑(K^k) : ℝ≥0∞) • μ.map f) := by
  intro b π hb hπ
  rw [pushCurrent_apply f T ⟨hb, fun i => ⟨1, hπ i⟩⟩,
    integral_smul_measure, integral_map hf.continuous.aemeasurable
      hb.continuous.abs.aestronglyMeasurable]
  have h := hT.mass_bound hμ (boundedLip_comp hb hf) (fun _ => K)
    (fun i => by simpa only [one_mul] using (hπ i).comp hf)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.coe_toReal, NNReal.coe_pow, smul_eq_mul, Function.comp_apply] using h

lemma pushCurrent_isMetricCurrent {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    IsMetricCurrent (pushCurrent f T) where
  offDomain := by intro b π h; exact ite_eq_right h
  linearFirst := by
    intro b c π a d hb hc hπ
    rw [pushCurrent_apply f T ⟨(hb.const_mul a).add (hc.const_mul d), hπ⟩,
      pushCurrent_apply f T ⟨hb, hπ⟩, pushCurrent_apply f T ⟨hc, hπ⟩]
    exact hT.linearFirst (b ∘ f) (c ∘ f) (fun i => π i ∘ f) a d
      (boundedLip_comp hb hf) (boundedLip_comp hc hf) (admissible_comp ⟨hb, hπ⟩ hf).2
  linearCoord := by
    intro b π i g a c h hg
    have hπg : ∀ j, ∃ L : ℝ≥0, LipschitzWith L ((Function.update π i g) j) := by
      intro j
      by_cases hj : j = i
      · simpa only [hj, Function.update_self] using hg
      · simpa only [Function.update_of_ne hj] using h.2 j
    have hl : ∃ L : ℝ≥0, LipschitzWith L (fun y => a * π i y + c * g y) := by
      obtain ⟨L, hL⟩ := h.2 i
      obtain ⟨M, hM⟩ := hg
      exact ⟨_, (lipschitz_mul_real hL a).add (lipschitz_mul_real hM c)⟩
    have hπac : ∀ j, ∃ L : ℝ≥0,
        LipschitzWith L ((Function.update π i (fun y => a * π i y + c * g y)) j) := by
      intro j
      by_cases hj : j = i
      · simpa only [hj, Function.update_self] using hl
      · simpa only [Function.update_of_ne hj] using h.2 j
    rw [pushCurrent_apply f T ⟨h.1, hπac⟩, pushCurrent_apply f T h,
      pushCurrent_apply f T ⟨h.1, hπg⟩]
    have h₁ : (fun j => (Function.update π i (fun y => a * π i y + c * g y)) j ∘ f) =
        Function.update (fun j => π j ∘ f) i (fun x => a * π i (f x) + c * g (f x)) := by
      funext j x
      by_cases hji : j = i <;> simp [hji, Function.update_of_ne]
    have h₂ : (fun j => (Function.update π i g) j ∘ f) =
        Function.update (fun j => π j ∘ f) i (g ∘ f) := by
      funext j x
      by_cases hji : j = i <;> simp [hji, Function.update_of_ne]
    rw [h₁, h₂]
    obtain ⟨L, hL⟩ := hg
    exact hT.linearCoord _ _ i _ a c (admissible_comp h hf) ⟨L*K, hL.comp hf⟩
  sequentialContinuity := by
    intro b π πs hb hLip hpt
    choose L hL using hLip
    have hπ (i) : LipschitzWith (L i) (π i) := by
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro x y
      exact le_of_tendsto ((hpt i x).dist (hpt i y))
        (Eventually.of_forall fun j => (hL i j).dist_le_mul x y)
    simp only [pushCurrent_apply f T ⟨hb, fun i => ⟨L i, hL i _⟩⟩,
      pushCurrent_apply f T ⟨hb, fun i => ⟨L i, hπ i⟩⟩]
    exact hT.sequentialContinuity _ _ _ (boundedLip_comp hb hf)
      (fun i => ⟨L i*K, fun j => (hL i j).comp hf⟩) (fun i x => hpt i (f x))
  locality := by
    intro b π h hloc
    rw [pushCurrent_apply f T h]
    obtain ⟨i, U, c, hU, hbU, hc⟩ := hloc
    apply hT.locality _ _ (admissible_comp h hf)
    refine ⟨i, f ⁻¹' U, c, hU.preimage hf.continuous, ?_, ?_⟩
    · intro x hx; exact hbU hx
    · intro x hx; exact hc (f x) hx
  finiteMass := by
    obtain ⟨μ, hμ, hctrl⟩ := hT.finiteMass
    let := hμ
    refine ⟨(↑(K^k) : ℝ≥0∞) • μ.map f, ⟨?_⟩, pushCurrent_controls hT hctrl hf⟩
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top (μ.map f) univ)

omit [BorelSpace X] in
lemma pushCurrent_id {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T) :
    pushCurrent id T = T := by
  funext b π
  by_cases h : Admissible b π
  · rw [pushCurrent_apply id T h]
    rfl
  · simp only [pushCurrent, ite_eq_right h, hT.offDomain b π h]

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma pushCurrent_comp {Z : Type*} [MetricSpace Z] {k : ℕ} {T : Functional X k}
    {f : X → Y} {g : Y → Z} {L : ℝ≥0} (hg : LipschitzWith L g) :
    pushCurrent (g ∘ f) T = pushCurrent g (pushCurrent f T) := by
  funext b π
  by_cases h : Admissible b π
  · rw [pushCurrent_apply (g ∘ f) T h, pushCurrent_apply g (pushCurrent f T) h,
      pushCurrent_apply f T (admissible_comp h hg)]
    rfl
  · simp only [pushCurrent, ite_eq_right h]

end CurrentOperations
end CAT0Fillings
end
end

end OAI
