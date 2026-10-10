import OAI.MeasureTheory.Falconer.Measures.ScalarSmallZoomMass

namespace OAI

/-! Normalize a weak coefficient Frostman bound to a fixed constant in
 [1/3,1], including every radius down to the original fine resolution. -/
namespace Falconer

 theorem scalar_normalized_coefficients_candidate {δ κ K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 0 ≤ κ) (hK : 1 ≤ K) (hbudget : K^2*δ^κ ≤ 1)
    (E : Finset ℝ) (hE : E.Nonempty) (hbound : ∀ x ∈ E, |x| ≤ 1)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass E u r ≤ K*r^(2*κ)*(E.card:ℝ)) :
    ∃ z ∈ E, ∃ R : ℝ, δ ≤ R ∧ R ≤ 2 ∧ (z,R) ∈ scalarBallCandidates δ E ∧
      1 ≤ (2:ℝ)^κ*K*R^κ ∧
      let F := E.filter fun x => |x-z| ≤ R
      let A := scalarZoom (z-3*R) (6*R) F
      A.Nonempty ∧ (∀ t ∈ A, 1/3 ≤ t ∧ t ≤ 1) ∧
      (E.card:ℝ) ≤ (4:ℝ)^κ*K*(A.card:ℝ) ∧
      ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
        scalarBallMass A u r ≤ (12:ℝ)^κ*r^κ*(A.card:ℝ) := by
  classical
  obtain ⟨z,hz,R,hRδ,hR2,hcandidate,hF,hmax,hlocal⟩ :=
    scalar_maximal_density_interval_candidate hδ hδ1 hκ E hE hbound
  have hR : 0 < R := hδ.trans_le hRδ
  have hN : (0:ℝ) < (E.card:ℝ) := by exact_mod_cast hE.card_pos
  have hu : R ≤ 1 → scalarBallMass E z R ≤ K*R^(2*κ)*(E.card:ℝ) :=
    fun hR1 => hball z R hRδ hR1
  have hradius := scalar_density_radius_inequality hR hκ hK hN hmax hu
  have hrelative := scalar_density_relative_mass hR hκ hK hN hmax hu
  let F := E.filter fun x => |x-z| ≤ R
  let A := scalarZoom (z-3*R) (6*R) F
  have hFE : F ⊆ E := Finset.filter_subset _ _
  have hcard : A.card = F.card := scalarZoom_card (by positivity) F
  refine ⟨z,hz,R,hRδ,hR2,hcandidate,hradius,?_,?_,?_,?_⟩
  · exact hF.image _
  · exact scalar_positive_zoom_bounds hR F (fun x hx => (Finset.mem_filter.mp hx).2)
  · rw [hcard]
    exact hrelative
  · intro u r hr _
    by_cases hb : δ ≤ 6*R*r
    · exact scalar_positive_zoom_local_mass hδ hR E hlocal F hFE rfl u r hb
    · apply scalar_positive_zoom_small_mass hδ hκ (by linarith) hR E F hFE hrelative
        (fun u => hball u δ le_rfl hδ1) hbudget u r hr (le_of_not_ge hb)

 theorem scalar_normalized_coefficients {δ κ K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 0 ≤ κ) (hK : 1 ≤ K) (hbudget : K^2*δ^κ ≤ 1)
    (E : Finset ℝ) (hE : E.Nonempty) (hbound : ∀ x ∈ E, |x| ≤ 1)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass E u r ≤ K*r^(2*κ)*(E.card:ℝ)) :
    ∃ z ∈ E, ∃ R : ℝ, δ ≤ R ∧ R ≤ 2 ∧
      1 ≤ (2:ℝ)^κ*K*R^κ ∧
      let F := E.filter fun x => |x-z| ≤ R
      let A := scalarZoom (z-3*R) (6*R) F
      A.Nonempty ∧ (∀ t ∈ A, 1/3 ≤ t ∧ t ≤ 1) ∧
      (E.card:ℝ) ≤ (4:ℝ)^κ*K*(A.card:ℝ) ∧
      ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
        scalarBallMass A u r ≤ (12:ℝ)^κ*r^κ*(A.card:ℝ) := by
  obtain ⟨z,hz,R,hRδ,hR2,_,hradius,hA,hAb,hsize,hlocal⟩ :=
    scalar_normalized_coefficients_candidate hδ hδ1 hκ hK hbudget E hE hbound hball
  exact ⟨z,hz,R,hRδ,hR2,hradius,hA,hAb,hsize,hlocal⟩

end Falconer

end OAI
