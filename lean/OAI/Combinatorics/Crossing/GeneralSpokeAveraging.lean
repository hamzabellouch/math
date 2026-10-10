import OAI.Combinatorics.Crossing.GeneralOrderAveraging

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {ι : Type*}

theorem small_perturbation_injective (node f : ι → ℝ)
    (ε : ℝ) (hgap : ∀ i j, i ≠ j → 2*ε < |node i-node j|)
    (hf : ∀ i, |f i-node i| < ε) : Function.Injective f := by
  intro i j hij
  by_contra hne
  have h₀ := hf i
  have h₁ := hf j
  have hh := abs_sub_le (node i) (f i) (node j)
  rw [abs_sub_comm (node i) (f i),hij] at hh
  have hg := hgap i j hne
  rw [hij] at h₀
  linarith

theorem fixed_node_ne_small_perturbation (node f : ι → ℝ)
    (ε : ℝ) (hε : 0<ε) (hgap : ∀ i j, i ≠ j → 2*ε < |node i-node j|)
    (hf : ∀ i, |f i-node i| < ε) (hself : ∀ i, node i ≠ f i) (i j : ι) : node i ≠ f j := by
  by_cases hij : i=j
  · subst j
    exact hself i
  · intro he
    have hg := hgap i j hij
    have hh := hf j
    rw [← he] at hh
    linarith

theorem local_spoke_straddling_average (node plus minus : ι → ℝ) (hn : Function.Injective node)
    (ε : ℝ) (hε : 0<ε) (hgap : ∀ i j, i ≠ j → 2*ε < |node i-node j|)
    (hp : ∀ i, |plus i-node i| < ε) (hm : ∀ i, |minus i-node i| < ε)
    (hs : ∀ i, (plus i<node i ∧ node i<minus i) ∨ (minus i<node i ∧ node i<plus i))
    (a b c d : ι) (hab : a ≠ b) (hcd : c ≠ d) :
    (segmentCrossingSign (circlePoint (node a)) (circlePoint (node b))
        (circlePoint (plus c)) (circlePoint (plus d)) +
      segmentCrossingSign (circlePoint (node a)) (circlePoint (node b))
        (circlePoint (minus c)) (circlePoint (minus d))) / 2 =
      chordEndpointPairing (node a) (node b) (node c) (node d) := by
  have hpne (i : ι) : node i ≠ plus i := by
    rcases hs i with h | h
    · exact ne_of_gt h.1
    · exact ne_of_lt h.2
  have hmne (i : ι) : node i ≠ minus i := by
    rcases hs i with h | h
    · exact ne_of_lt h.2
    · exact ne_of_gt h.1
  have hpall := fixed_node_ne_small_perturbation node plus ε hε hgap hp hpne
  have hmall := fixed_node_ne_small_perturbation node minus ε hε hgap hm hmne
  have hpinj := small_perturbation_injective node plus ε hgap hp
  have hminj := small_perturbation_injective node minus ε hgap hm
  rw [circle_chord_pairing _ _ _ _ (hn.ne hab) (hpinj.ne hcd) (hpall a c) (hpall a d) (hpall b c) (hpall b d),
    circle_chord_pairing _ _ _ _ (hn.ne hab) (hminj.ne hcd) (hmall a c) (hmall a d) (hmall b c) (hmall b d)]
  have hav (i j : ι) : (orderSign (node i) (plus j)+orderSign (node i) (minus j))/2 = orderSign (node i) (node j) := by
    apply orderSign_straddling_average _ _ _ _ ε _ (hp j) (hm j) (hs j)
    intro hne
    have hg := hgap i j (fun he => hne (congrArg node he))
    linarith
  have h₁ := hav a c
  have h₂ := hav a d
  have h₃ := hav b c
  have h₄ := hav b d
  unfold chordEndpointPairing
  linarith

end Zarankiewicz

end

end OAI
