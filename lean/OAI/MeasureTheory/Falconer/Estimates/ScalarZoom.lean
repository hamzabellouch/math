import OAI.MeasureTheory.Falconer.Geometry.ScalarBallCandidates

namespace OAI

/-! Exact finite scalar zooming and its ball-count identity. -/
namespace Falconer

noncomputable def scalarZoom (z R : ℝ) (E : Finset ℝ) : Finset ℝ :=
  E.image fun x => (x-z)/R

 theorem scalarZoom_injective {z R : ℝ} (hR : R ≠ 0) :
    Function.Injective (fun x : ℝ => (x-z)/R) := by
  intro x y h
  have hh := congrArg (fun t : ℝ => t*R) h
  simp only [div_mul_cancel₀ _ hR] at hh
  linarith

 theorem scalarZoom_card {z R : ℝ} (hR : R ≠ 0) (E : Finset ℝ) :
    (scalarZoom z R E).card = E.card :=
  Finset.card_image_of_injective _ (scalarZoom_injective hR)

 theorem scalarZoom_ball_iff {z R u r x : ℝ} (hR : 0 < R) :
    |(x-z)/R-u| ≤ r ↔ |x-(z+R*u)| ≤ R*r := by
  have he : (x-z)/R-u = (x-(z+R*u))/R := by field_simp; ring
  rw [he,abs_div,abs_of_pos hR,div_le_iff₀ hR]
  rw [mul_comm r R]

 theorem scalarZoom_ball_mass {z R : ℝ} (hR : 0 < R) (E : Finset ℝ) (u r : ℝ) :
    scalarBallMass (scalarZoom z R E) u r = scalarBallMass E (z+R*u) (R*r) := by
  classical
  have he : (scalarZoom z R E).filter (fun x => |x-u| ≤ r) =
      (E.filter fun x => |x-(z+R*u)| ≤ R*r).image (fun x => (x-z)/R) := by
    ext y
    constructor
    · intro hy
      obtain ⟨hyE,hyB⟩ := Finset.mem_filter.mp hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hyE
      exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,(scalarZoom_ball_iff hR).1 hyB⟩,rfl⟩
    · intro hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hxE,hxB⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,hxE,rfl⟩,(scalarZoom_ball_iff hR).2 hxB⟩
  unfold scalarBallMass
  rw [he,Finset.card_image_of_injective _ (scalarZoom_injective hR.ne')]

 theorem scalarZoom_separated {δ z R : ℝ} (hR : 0 < R) (E : Finset ℝ)
    (hsep : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → δ ≤ |x-y|) :
    ∀ x ∈ scalarZoom z R E, ∀ y ∈ scalarZoom z R E, x ≠ y → δ/R ≤ |x-y| := by
  intro x hx y hy hne
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
  have hab : a ≠ b := by intro h; apply hne; rw [h]
  rw [← sub_div,show (a-z)-(b-z) = a-b by ring,abs_div,abs_of_pos hR]
  exact div_le_div_of_nonneg_right (hsep a ha b hb hab) hR.le

end Falconer

end OAI
