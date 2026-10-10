import OAI.Analysis.HenonEmden.ComponentWeights

namespace OAI

section ShortComponents

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.LineComponents

lemma dist_le_component_volume {I : Set ℝ} (hI : IsPreconnected I)
    {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    ENNReal.ofReal (dist x y) ≤ volume I := by
  have hs : uIcc x y ⊆ I := hI.ordConnected.uIcc_subset hx hy
  have hm := measure_mono (μ := (volume : Measure ℝ)) hs
  rcases le_total x y with hxy|hyx
  · simpa only [uIcc_of_le hxy,Real.volume_Icc,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub] using hm
  · simpa only [uIcc_of_ge hyx,Real.volume_Icc,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hyx)] using hm

lemma dist_le_of_volume_le {I : Set ℝ} (hI : IsPreconnected I)
    {x y l : ℝ} (hx : x ∈ I) (hy : y ∈ I) (hl : 0 ≤ l)
    (hv : volume I ≤ ENNReal.ofReal l) : dist x y ≤ l :=
  (ENNReal.ofReal_le_ofReal_iff hl).mp ((dist_le_component_volume hI hx hy).trans hv)

lemma setInf_lower {f : ℝ → ℝ} {I : Set ℝ} {b : ℝ}
    (hb : ∀ y ∈ I, b ≤ f y) : ENNReal.ofReal b ≤ setInf f I := by
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  exact ENNReal.ofReal_le_ofReal (hb y hy)

/-- Every short component passes the component length test. The bound
on `d` is kept intrinsic, so no choice of coordinates enters the statement. -/
lemma short_setWeight_eq {I : Set ℝ} (hI : I.Nonempty)
    {h d : ℝ → ℝ} {δ d₀ l : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (hd₀ : 0 ≤ d₀) (_hl : 0 ≤ l) (hl' : l ≤ δ*d₀)
    (hv : volume I ≤ ENNReal.ofReal l) (hd : ∀ y ∈ I, d₀-l ≤ d y) :
    setWeight h d δ I = setInf h I := by
  have hlow : 0 ≤ d₀-l := by nlinarith
  have hlen : l ≤ 2*δ*(d₀-l) := by
    have h1 : l ≤ d₀/2 := by nlinarith
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr h1)]
  have htest : volume I ≤ ENNReal.ofReal (2*δ)*setInf d I := by
    calc
      _ ≤ ENNReal.ofReal l := hv
      _ ≤ ENNReal.ofReal (2*δ*(d₀-l)) := ENNReal.ofReal_le_ofReal hlen
      _ = ENNReal.ofReal (2*δ)*ENNReal.ofReal (d₀-l) := ENNReal.ofReal_mul (by positivity)
      _ ≤ _ := mul_le_mul_right (setInf_lower hd) _
  exact ite_eq_left ⟨hI,ne_top_of_le_ne_top ENNReal.ofReal_ne_top hv,htest⟩

lemma setInf_oscillation {I : Set ℝ} {h : ℝ → ℝ} {x ε : ℝ}
    (hx : x ∈ I) (_hh : 0 ≤ h x) (hb : ∀ y ∈ I, |h x-h y| ≤ ε) :
    h x-(setInf h I).toReal ≤ ε := by
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (setInf_le (f := h) hx)
  have hlo : ENNReal.ofReal (h x-ε) ≤ setInf h I := by
    apply setInf_lower
    intro y hy
    have := (abs_le.mp (hb y hy)).2
    linarith
  have ht := ENNReal.toReal_mono hfin hlo
  rw [ENNReal.toReal_ofReal'] at ht
  have hm := le_max_left (h x-ε) 0
  linarith

lemma short_component_loss {U : Set ℝ} (_hU : IsOpen U) {x : ℝ} (hx : x ∈ U)
    {h d : ℝ → ℝ} {δ l ε : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (hd₀ : 0 ≤ d x) (hh : 0 ≤ h x) (hl : 0 ≤ l) (hl' : l ≤ δ*d x)
    (hv : volume (connectedComponentIn U x) ≤ ENNReal.ofReal l)
    (hd : ∀ y, dist y x ≤ l → d x-dist y x ≤ d y)
    (hosc : ∀ y, dist y x ≤ l → |h x-h y| ≤ ε) :
    h x-(setWeight h d δ (connectedComponentIn U x)).toReal ≤ ε := by
  have hxi := mem_connectedComponentIn hx
  have hdist (y : ℝ) (hy : y ∈ connectedComponentIn U x) : dist y x ≤ l :=
    dist_le_of_volume_le isPreconnected_connectedComponentIn hy hxi hl hv
  rw [short_setWeight_eq ⟨x,hxi⟩ hδ hδ' hd₀ hl hl' hv (by
    intro y hy
    have hh := hd y (hdist y hy)
    linarith [hdist y hy])]
  exact setInf_oscillation hxi hh (fun y hy => hosc y (hdist y hy))

end HenonLaneEmden.LineComponents
end
end ShortComponents

end OAI
