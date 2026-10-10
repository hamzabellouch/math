import OAI.MeasureTheory.Falconer.Measures.ScalarDensitySelection
import OAI.MeasureTheory.Falconer.Estimates.ScalarZoom

namespace OAI

/-! A maximal-density scalar interval, rescaled to the unit interval,
has a uniform Frostman constant. -/
namespace Falconer

 theorem scalar_maximal_density_zoom {δ κ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 0 ≤ κ) (E : Finset ℝ) (hE : E.Nonempty)
    (hbound : ∀ x ∈ E, |x| ≤ 1)
    (hsep : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → δ ≤ |x-y|) :
    ∃ z ∈ E, ∃ R : ℝ, δ ≤ R ∧ R ≤ 2 ∧
      let F := E.filter fun x => |x-z| ≤ R
      let X := scalarZoom z R F
      X.Nonempty ∧ (R/2)^κ*(E.card : ℝ) ≤ (X.card : ℝ) ∧
      (∀ x ∈ X, |x| ≤ 1) ∧
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ/R ≤ |x-y|) ∧
      ∀ u r : ℝ, δ/R ≤ r → scalarBallMass X u r ≤ 2^κ*r^κ*(X.card : ℝ) := by
  classical
  obtain ⟨z,hz,R,hRδ,hR2,hF,hsize,hlocal⟩ :=
    scalar_maximal_density_interval hδ hδ1 hκ E hE hbound
  have hR : 0 < R := hδ.trans_le hRδ
  let F := E.filter fun x => |x-z| ≤ R
  let X := scalarZoom z R F
  have hcard : X.card = F.card := scalarZoom_card hR.ne' F
  refine ⟨z,hz,R,hRδ,hR2,Finset.image_nonempty.mpr hF,?_,?_,?_,?_⟩
  · change (R/2)^κ*(E.card : ℝ) ≤ (X.card : ℝ)
    rw [hcard]
    have hh := mul_le_mul_of_nonneg_right hsize (Real.rpow_nonneg hR.le κ)
    have he : scalarBallMass E z R/R^κ*R^κ = (F.card : ℝ) := by
      change (F.card : ℝ)/R^κ*R^κ = _
      exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos hR κ).ne'
    rw [he] at hh
    calc
      _ = ((E.card : ℝ)/2^κ)*R^κ := by
        rw [Real.div_rpow hR.le (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      _ ≤ _ := hh
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    rw [abs_div,abs_of_pos hR]
    exact (div_le_one hR).2 (Finset.mem_filter.mp ha).2
  · exact scalarZoom_separated hR F (fun x hx y hy hxy =>
      hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
  · intro u r hdr
    have hδr : δ ≤ R*r := by
      have hh := (div_le_iff₀ hR).1 hdr
      simpa only [mul_comm] using hh
    change scalarBallMass X u r ≤ _
    rw [show scalarBallMass X u r = scalarBallMass F (z+R*u) (R*r) from scalarZoom_ball_mass hR F u r]
    have hmono : scalarBallMass F (z+R*u) (R*r) ≤ scalarBallMass E (z+R*u) (R*r) := by
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxF,hxB⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxF).1,hxB⟩
    have hh := hmono.trans (hlocal (z+R*u) (R*r) hδr)
    have hr : R*r/R = r := by field_simp
    rw [hr] at hh
    simpa only [X,scalarZoom_card hR.ne',scalarBallMass,F] using hh

end Falconer

end OAI
