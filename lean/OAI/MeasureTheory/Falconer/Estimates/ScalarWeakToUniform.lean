import OAI.MeasureTheory.Falconer.Measures.ScalarDensityRadius

namespace OAI

/-! Uniform local regularity extracted from a weak scalar Frostman bound,
with a lower bound for the rescaling radius. -/
namespace Falconer

 theorem scalar_weak_to_uniform {δ s K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hs : 0 < s) (hK : 1 ≤ K) (E : Finset ℝ) (hE : E.Nonempty)
    (hbound : ∀ x ∈ E, |x| ≤ 1)
    (hsep : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → δ ≤ |x-y|)
    (hweak : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass E u r ≤ K*r^s*(E.card : ℝ)) :
    ∃ z ∈ E, ∃ R : ℝ, δ ≤ R ∧ R ≤ 2 ∧
      (1/((2:ℝ)^(s/2)*K))^(1/(s/2)) ≤ R ∧
      let F := E.filter fun x => |x-z| ≤ R
      let X := scalarZoom z R F
      X.Nonempty ∧ (R/2)^(s/2)*(E.card : ℝ) ≤ (X.card : ℝ) ∧
      (∀ x ∈ X, |x| ≤ 1) ∧
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ/R ≤ |x-y|) ∧
      ∀ u r : ℝ, δ/R ≤ r → scalarBallMass X u r ≤ 2^(s/2)*r^(s/2)*(X.card : ℝ) := by
  obtain ⟨z,hz,R,hRδ,hR2,hne,hsize,hunit,hsep',hballs⟩ :=
    scalar_maximal_density_zoom hδ hδ1 (show 0 ≤ s/2 by positivity) E hE hbound hsep
  let F := E.filter fun x => |x-z| ≤ R
  let X := scalarZoom z R F
  have hR : 0 < R := hδ.trans_le hRδ
  have hN : 0 < (E.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hE)
  have hcard : (X.card : ℝ) = scalarBallMass E z R := by
    rw [show X.card = F.card from scalarZoom_card hR.ne' F]
    rfl
  have hlow : (E.card : ℝ)/(2:ℝ)^(s/2) ≤ scalarBallMass E z R/R^(s/2) := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hR (s/2))).2
    have hh := hsize
    change (R/2)^(s/2)*(E.card : ℝ) ≤ (X.card : ℝ) at hh
    rw [hcard] at hh
    convert hh using 1
    rw [Real.div_rpow hR.le (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hu : R ≤ 1 → scalarBallMass E z R ≤ K*R^(2*(s/2))*(E.card : ℝ) := by
    intro hr
    simpa only [show 2*(s/2) = s by ring] using hweak z R hRδ hr
  have hrbound := scalar_density_radius_lower hR (show 0 < s/2 by positivity)
    (zero_lt_one.trans_le hK) (scalar_density_radius_inequality hR (by positivity) hK hN hlow hu)
  exact ⟨z,hz,R,hRδ,hR2,hrbound,hne,hsize,hunit,hsep',hballs⟩

end Falconer

end OAI
