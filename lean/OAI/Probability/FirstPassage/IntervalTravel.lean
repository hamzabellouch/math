import OAI.Probability.FirstPassage.BallTravel

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

theorem segmentTube_translate_iff (a p q z : Vertex) (R : ℝ) :
    a+z ∈ SegmentTube (a+p) (a+q) R ↔ z ∈ SegmentTube p q R := by
  simp only [SegmentTube,mem_ofPred_eq,segmentPoint,latticeEmbed_add,
    add_sub_add_left_eq_sub]
  have he (t : ℝ) : latticeEmbed a+latticeEmbed z-
      (latticeEmbed a+latticeEmbed p+t • (latticeEmbed q-latticeEmbed p)) =
      latticeEmbed z-(latticeEmbed p+t • (latticeEmbed q-latticeEmbed p)) := by abel
  simp only [he]

theorem localTravel_translate_iff (μ : Plane → ℝ) (w : Edge → ℝ)
    (a p q : Vertex) (η δ s : ℝ) :
    LocalTravel μ η δ s p q (fun e => w (shiftEdge a e)) ↔
      LocalTravel μ η δ s (a+p) (a+q) w := by
  constructor
  · rintro ⟨ds,hd,hc,hin⟩
    refine ⟨ds,by rw [add_assoc,hd],?_,?_⟩
    · simpa only [pathCost_translate,add_sub_add_left_eq_sub] using hc
    · intro i hi
      rw [add_assoc,segmentTube_translate_iff]
      exact hin i hi
  · rintro ⟨ds,hd,hc,hin⟩
    refine ⟨ds,by simpa only [add_assoc,add_left_cancel_iff] using hd,?_,?_⟩
    · simpa only [pathCost_translate,add_sub_add_left_eq_sub] using hc
    · intro i hi
      have ht := hin i hi
      rw [add_assoc,segmentTube_translate_iff] at ht
      exact ht

theorem measurableSet_ballTravel (μ : Plane → ℝ) (D η δ s : ℝ) :
    MeasurableSet {w | BallTravel μ D η δ s w} := by
  simp only [BallTravel,ofPred_forall]
  exact MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun q =>
    MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ =>
      measurableSet_localTravel μ η δ s p q))))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_ball_travel (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ s : ℝ in atTop, ∀ a : Vertex,
      P.real {ω | ¬BallTravel μ D η δ s (fun e => τ (shiftEdge a e) ω)} < ε := by
  let _ := h.probability
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((exponential_ball_travel_nat h μ hμ ht D (η/2) (δ/2) hD (by linarith) (by linarith)).eventually
      (gt_mem_nhds hε))
  filter_upwards [eventually_ge_atTop (max 1 (N : ℝ))] with s hs
  intro a
  have he := translated_event_probability h a
    {w | ¬BallTravel μ D η δ s w} (measurableSet_ballTravel μ D η δ s).compl
  rw [show P.real {ω | ¬BallTravel μ D η δ s (fun e => τ (shiftEdge a e) ω)} =
      P.real {ω | ¬BallTravel μ D η δ s (fun e => τ e ω)} from congrArg ENNReal.toReal he]
  let n : ℕ := ⌈s⌉₊
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hsn : s ≤ (n : ℝ) := Nat.le_ceil s
  have hnN : N ≤ n := by exact_mod_cast ((le_max_right _ _).trans hs).trans hsn
  have hnupper : (n : ℝ) ≤ 2*s := by
    have hh : (n : ℝ) < s+1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hη' : (η/2)*(n : ℝ) ≤ η*s := by nlinarith
  have hδ' : (δ/2)*(n : ℝ) ≤ δ*s := by nlinarith
  refine (measureReal_mono (show {ω | ¬BallTravel μ D η δ s (fun e => τ e ω)} ⊆
      {ω | ¬BallTravel μ D (η/2) (δ/2) n (fun e => τ e ω)} from ?_)).trans_lt (hN n hnN)
  intro ω hb hg
  apply hb
  intro p q hp hq
  apply localTravel_mono μ _ p q hη' hδ'
  apply hg p q <;> nlinarith

theorem exponential_set_travel (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ s : ℝ in atTop, ∀ I J : Set Vertex,
      (∀ p ∈ I ∪ J, ∀ q ∈ I ∪ J, ‖latticeEmbed (q-p)‖ ≤ D*s) →
      P.real {ω | ¬∀ p ∈ I, ∀ q ∈ J,
        LocalTravel μ η δ s p q (fun e => τ e ω)} < ε := by
  let _ := h.probability
  intro ε hε
  filter_upwards [exponential_ball_travel h μ hμ ht D η δ hD hη hδ ε hε] with s hs
  intro I J hdiam
  by_cases hI : I.Nonempty
  · obtain ⟨a,ha⟩ := hI
    refine (measureReal_mono (show {ω | ¬∀ p ∈ I, ∀ q ∈ J, LocalTravel μ η δ s p q (fun e => τ e ω)} ⊆
        {ω | ¬BallTravel μ D η δ s (fun e => τ (shiftEdge a e) ω)} from ?_)).trans_lt (hs a)
    intro ω hb hg
    apply hb
    intro p hp q hq
    have hgood := hg (p-a) (q-a) (hdiam a (Or.inl ha) p (Or.inl hp))
      (hdiam a (Or.inl ha) q (Or.inr hq))
    have hh := (localTravel_translate_iff μ (fun e => τ e ω) a (p-a) (q-a) η δ s).mp hgood
    simpa only [add_sub_cancel] using hh
  · have he : I=∅ := Set.not_nonempty_iff_eq_empty.mp hI
    simpa [he] using hε

def verticalInterval (x : ℤ) (lo hi : ℝ) : Set Vertex :=
  {p | p.1=x ∧ lo ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ hi}

theorem exponential_interval_travel (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ s : ℝ in atTop, ∀ x₁ x₂ : ℤ, ∀ l₁ u₁ l₂ u₂ : ℝ,
      (∀ p ∈ verticalInterval x₁ l₁ u₁ ∪ verticalInterval x₂ l₂ u₂,
        ∀ q ∈ verticalInterval x₁ l₁ u₁ ∪ verticalInterval x₂ l₂ u₂,
          ‖latticeEmbed (q-p)‖ ≤ D*s) →
      P.real {ω | ¬∀ p ∈ verticalInterval x₁ l₁ u₁, ∀ q ∈ verticalInterval x₂ l₂ u₂,
        LocalTravel μ η δ s p q (fun e => τ e ω)} < ε := by
  intro ε hε
  filter_upwards [exponential_set_travel h μ hμ ht D η δ hD hη hδ ε hε] with s hs
  intro x₁ x₂ l₁ u₁ l₂ u₂
  exact hs _ _

end PlanarFPP

end OAI
