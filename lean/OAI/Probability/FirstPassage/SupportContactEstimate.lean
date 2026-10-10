import OAI.Probability.FirstPassage.PlaneGeometry

namespace OAI

namespace PlanarFPP
open Set Filter
open scoped Topology

theorem derivative_remainder_radius (φ : ℝ → ℝ) (a : ℝ) (S : Set ℝ)
    (ha : HasDerivWithinAt φ a S 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ S, |t| ≤ r → |φ t-φ 0-a*t| ≤ ε*|t| := by
  have hh := ha.isLittleO.bound hε
  simp only [sub_zero,smul_eq_mul,Real.norm_eq_abs] at hh
  obtain ⟨r,hr,hh⟩ := Metric.mem_nhdsWithin_iff.mp hh
  refine ⟨r/2,by linarith,?_⟩
  intro t ht htr
  have hball : t ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    linarith
  simpa only [mem_ofPred_eq,mul_comm t a] using hh ⟨hball,ht⟩

noncomputable def extremeSlope (μ : Plane → ℝ) (b : ℝ) (plus : Bool) : ℝ :=
  if plus then rightSlope (fun t => μ (direction b+t • transverseUnit))
  else leftSlope (fun t => μ (direction b+t • transverseUnit))

def contactSide (plus : Bool) : Set ℝ := if plus then Ioi 0 else Iio 0

theorem norm_extreme_support_contact (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (b : ℝ) (plus : Bool) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ contactSide plus, |t| ≤ r →
      0 ≤ μ (direction b+t • transverseUnit)-μ (direction b)-extremeSlope μ b plus*t ∧
      μ (direction b+t • transverseUnit)-μ (direction b)-extremeSlope μ b plus*t ≤ ε*|t| := by
  let φ := fun t : ℝ => μ (direction b+t • transverseUnit)
  have hφ := convex_transverse_profile μ (direction b) transverseUnit
    hμ.triangle (norm_positive_homogeneous μ hμ)
  have hc := extreme_slopes_contact φ hφ
  have hs := extreme_subgradients φ hφ
  have hd : HasDerivWithinAt φ (extremeSlope μ b plus) (contactSide plus) 0 := by
    cases plus <;> simp only [extremeSlope,contactSide,Bool.false_eq_true,ite_false,ite_true]
    · exact hc.1
    · exact hc.2
  obtain ⟨r,hr,hh⟩ := derivative_remainder_radius φ (extremeSlope μ b plus)
    (contactSide plus) hd ε hε
  refine ⟨r,hr,?_⟩
  intro t ht htr
  have he := (le_abs_self _).trans (hh t ht htr)
  have hl : φ 0+extremeSlope μ b plus*t ≤ φ t := by
    cases plus
    · exact hs.1 t
    · exact hs.2 t
  simp only [φ,zero_smul,add_zero] at he hl
  exact ⟨by linarith,he⟩

theorem connector_support_gap (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (b : ℝ) (plus : Bool) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C) :
    ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ s : ℝ, 0 < s → ∀ z : Plane,
      D0*s ≤ xCoord z → rCoord b z ∈ contactSide plus → |rCoord b z| ≤ 3*C*s →
      μ z-(μ (direction b)*xCoord z+extremeSlope μ b plus*rCoord b z) ≤ ε*s/4 := by
  obtain ⟨r,hr,hcontact⟩ := norm_extreme_support_contact μ hμ b plus
    (ε/(12*C)) (by positivity)
  let D0 := max 1 (3*C/r)
  have hD : 1 ≤ D0 := le_max_left _ _
  have hCr : 3*C ≤ D0*r := (div_le_iff₀ hr).mp (le_max_right _ _)
  refine ⟨D0,hD,?_⟩
  intro s hs z hz hside htrans
  have hx : 0 < xCoord z := by nlinarith
  have hratio : rCoord b z / xCoord z ∈ contactSide plus := by
    cases plus <;> simp only [contactSide,Bool.false_eq_true,ite_false,ite_true,
      mem_Iio,mem_Ioi] at hside ⊢
    · exact div_neg_of_neg_of_pos hside hx
    · exact div_pos hside hx
  have hsmall : |rCoord b z/xCoord z| ≤ r := by
    rw [abs_div,abs_of_pos hx]
    apply (div_le_iff₀ hx).mpr
    have h1 := mul_le_mul_of_nonneg_right hCr hs.le
    have h2 := mul_le_mul_of_nonneg_left hz hr.le
    nlinarith
  have hg := (hcontact _ hratio hsmall).2
  have hrepr : z = xCoord z • (direction b+(rCoord b z/xCoord z) • transverseUnit) := by
    rw [smul_add,smul_smul]
    have he : xCoord z*(rCoord b z/xCoord z)=rCoord b z := by field_simp
    rw [he]
    exact plane_reconstruction b z
  have hnorm : μ z = xCoord z*μ (direction b+(rCoord b z/xCoord z) • transverseUnit) := by
    conv_lhs => rw [hrepr]
    rw [hμ.homogeneous,abs_of_pos hx]
  calc
    _ = xCoord z*(μ (direction b+(rCoord b z/xCoord z) • transverseUnit)-
        μ (direction b)-extremeSlope μ b plus*(rCoord b z/xCoord z)) := by
      rw [hnorm]
      field_simp
      ring
    _ ≤ xCoord z*(ε/(12*C)*|rCoord b z/xCoord z|) :=
      mul_le_mul_of_nonneg_left hg hx.le
    _ = ε/(12*C)*|rCoord b z| := by
      rw [abs_div,abs_of_pos hx]
      field_simp
    _ ≤ ε/(12*C)*(3*C*s) := mul_le_mul_of_nonneg_left htrans (by positivity)
    _ = ε*s/4 := by field_simp; ring

end PlanarFPP

end OAI
