import OAI.Probability.GammaPassage.BallTravelGeometry

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter Metric
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

theorem gamma_badConnections_tendsto_zero
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun n => P.real (gammaBadConnections shape rate τ κ n)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) (h.gammaBadConnections_probability hs hr κ)
  exact (summable_gamma_box_connection_bound hr hκ).tendsto_atTop_zero

theorem gamma_ball_travel_nat (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => P.real {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ n (fun e => τ e ω)})
      atTop (𝓝 0) := by
  classical
  let μ := gammaMeanNorm h hs hr
  have hμ := gammaMeanNorm_laws h hs hr
  let _ := h.probability
  obtain ⟨β,hβ,hlip⟩ := timeConstantNorm_lipschitz_bound μ hμ
  obtain ⟨γ,κ,C,hγ,hκ,hC,hparams⟩ := ballTravel_parameters D β η δ (coordinateAllowance shape rate) (coordinateAllowance_pos hs hr) hD hβ.le hη hδ
  obtain ⟨S,hS⟩ := finite_ball_net D γ hγ
  let A (n : ℕ) := ⋃ uv ∈ S ×ˢ S, {ω | ¬LocalTravel μ (η/4) (δ/2) n
    (latticeFloor ((n : ℝ) • uv.1.val)) (latticeFloor ((n : ℝ) • uv.2.val)) (fun e => τ e ω)}
  have hA : Tendsto (fun n => P.real (A n)) atTop (𝓝 0) := by
    apply (tendsto_order.2 ⟨?_,?_⟩)
    · intro a ha
      exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
    · intro ε hε
      have hden : 0 < ((S ×ˢ S).card : ℝ)+1 := by positivity
      filter_upwards [eventually_ge_atTop 1,
        gamma_tube_travel_nat h hs hr (2*D+4) (η/4) (δ/2)
          (by linarith) (by linarith) (by linarith)
          (ε/(((S ×ˢ S).card : ℝ)+1)) (div_pos hε hden)] with n hn hh
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hbound : P.real (A n) ≤ ((S ×ˢ S).card : ℝ)*(ε/(((S ×ˢ S).card : ℝ)+1)) := by
        refine (measureReal_biUnion_finset_le _ _).trans ?_
        calc
          _ ≤ ∑ _uv ∈ S ×ˢ S, ε/(((S ×ˢ S).card : ℝ)+1) := by
            apply sum_le_sum
            intro uv huv
            apply (hh _ _ ?_).le
            rw [latticeEmbed_sub]
            exact (norm_sub_le _ _).trans (by
              have h1 := scaled_net_norm D uv.1 n
              have h2 := scaled_net_norm D uv.2 n
              nlinarith)
          _ = _ := by simp
      apply hbound.trans_lt
      have he := (div_pos hε hden)
      have hid : ((((S ×ˢ S).card : ℝ)+1))*(ε/(((S ×ˢ S).card : ℝ)+1))=ε := by field_simp
      nlinarith
  have hCn : Tendsto (fun n : ℕ => C*n) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (Nat.le_mul_of_pos_left n hC)
  have hB := (gamma_badConnections_tendsto_zero h hs hr κ hκ).comp hCn
  have hbound : ∀ᶠ n : ℕ in atTop,
      P.real {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ n (fun e => τ e ω)} ≤
        P.real (gammaBadConnections shape rate τ κ (C*n))+P.real (A n) := by
    filter_upwards [hparams] with n hn
    have hsub : {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ n (fun e => τ e ω)} ⊆
        gammaBadConnections shape rate τ κ (C*n) ∪ A n := by
      intro ω hω
      by_contra hb
      have hc : ω ∉ gammaBadConnections shape rate τ κ (C*n) := fun hc => hb (Or.inl hc)
      have hm : ω ∉ A n := fun hm => hb (Or.inr hm)
      apply hω
      apply ballTravel_of_net μ _ D γ β η δ κ (coordinateAllowance shape rate) (coordinateAllowance_pos hs hr) hβ.le hlip S hS C n
        hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
      · intro p hp q hq
        by_contra hh
        exact hc (mem_iUnion₂.mpr ⟨(p,q),mem_product.mpr ⟨hp,hq⟩,le_of_not_gt hh⟩)
      · intro u hu v hv
        by_contra hh
        exact hm (mem_iUnion₂.mpr ⟨(u,v),mem_product.mpr ⟨hu,hv⟩,hh⟩)
    exact (measureReal_mono hsub).trans (measureReal_union_le _ _)
  exact squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) hbound
    (by simpa using hB.add hA)

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

theorem gamma_ball_travel (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ s : ℝ in atTop, ∀ a : Vertex,
      P.real {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s (fun e => τ (shiftEdge a e) ω)} < ε := by
  let _ := h.probability
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((gamma_ball_travel_nat h hs hr D (η/2) (δ/2) hD (by linarith) (by linarith)).eventually
      (gt_mem_nhds hε))
  filter_upwards [eventually_ge_atTop (max 1 (N : ℝ))] with s hscale
  intro a
  have he := h.translated_event_probability a
    {w | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s w} (measurableSet_ballTravel (gammaMeanNorm h hs hr) D η δ s).compl
  rw [show P.real {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s (fun e => τ (shiftEdge a e) ω)} =
      P.real {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s (fun e => τ e ω)} from congrArg ENNReal.toReal he]
  let n : ℕ := ⌈s⌉₊
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hscale
  have hsn : s ≤ (n : ℝ) := Nat.le_ceil s
  have hnN : N ≤ n := by exact_mod_cast ((le_max_right _ _).trans hscale).trans hsn
  have hnupper : (n : ℝ) ≤ 2*s := by
    have hh : (n : ℝ) < s+1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hη' : (η/2)*(n : ℝ) ≤ η*s := by nlinarith
  have hδ' : (δ/2)*(n : ℝ) ≤ δ*s := by nlinarith
  refine (measureReal_mono (show {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s (fun e => τ e ω)} ⊆
      {ω | ¬BallTravel (gammaMeanNorm h hs hr) D (η/2) (δ/2) n (fun e => τ e ω)} from ?_)).trans_lt (hN n hnN)
  intro ω hb hg
  apply hb
  intro p q hp hq
  apply localTravel_mono (gammaMeanNorm h hs hr) _ p q hη' hδ'
  apply hg p q <;> nlinarith

/-- Simultaneous travel for arbitrary deterministic lattice endpoint sets of
bounded combined diameter. This stronger statement includes vertical intervals. -/
theorem gamma_set_travel (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ s : ℝ in atTop, ∀ I J : Set Vertex,
      (∀ p ∈ I ∪ J, ∀ q ∈ I ∪ J, ‖latticeEmbed (q-p)‖ ≤ D*s) →
      P.real {ω | ¬∀ p ∈ I, ∀ q ∈ J,
        LocalTravel (gammaMeanNorm h hs hr) η δ s p q (fun e => τ e ω)} < ε := by
  let _ := h.probability
  intro ε hε
  filter_upwards [gamma_ball_travel h hs hr D η δ hD hη hδ ε hε] with s hscale
  intro I J hdiam
  by_cases hI : I.Nonempty
  · obtain ⟨a,ha⟩ := hI
    refine (measureReal_mono (show {ω | ¬∀ p ∈ I, ∀ q ∈ J, LocalTravel (gammaMeanNorm h hs hr) η δ s p q (fun e => τ e ω)} ⊆
        {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s (fun e => τ (shiftEdge a e) ω)} from ?_)).trans_lt (hscale a)
    intro ω hb hg
    apply hb
    intro p hp q hq
    have hgood := hg (p-a) (q-a) (hdiam a (Or.inl ha) p (Or.inl hp))
      (hdiam a (Or.inl ha) q (Or.inr hq))
    have hh := (localTravel_translate_iff (gammaMeanNorm h hs hr) (fun e => τ e ω) a (p-a) (q-a) η δ s).mp hgood
    simpa only [add_sub_cancel] using hh
  · have he : I=∅ := Set.not_nonempty_iff_eq_empty.mp hI
    simpa [he] using hε

def verticalInterval (x : ℤ) (lo hi : ℝ) : Set Vertex :=
  {p | p.1=x ∧ lo ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ hi}

/-- Travel between vertical intervals of bounded combined Euclidean diameter,
including empty and singleton intervals (Lemma `cr:interval-travel`). -/
theorem gamma_interval_travel (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ s : ℝ in atTop, ∀ x₁ x₂ : ℤ, ∀ l₁ u₁ l₂ u₂ : ℝ,
      (∀ p ∈ verticalInterval x₁ l₁ u₁ ∪ verticalInterval x₂ l₂ u₂,
        ∀ q ∈ verticalInterval x₁ l₁ u₁ ∪ verticalInterval x₂ l₂ u₂,
          ‖latticeEmbed (q-p)‖ ≤ D*s) →
      P.real {ω | ¬∀ p ∈ verticalInterval x₁ l₁ u₁, ∀ q ∈ verticalInterval x₂ l₂ u₂,
        LocalTravel (gammaMeanNorm h hs hr) η δ s p q (fun e => τ e ω)} < ε := by
  intro ε hε
  filter_upwards [gamma_set_travel h hs hr D η δ hD hη hδ ε hε] with s hscale
  intro x₁ x₂ l₁ u₁ l₂ u₂
  exact hscale _ _

end GammaFPP.IntervalTravelBridge

end OAI
