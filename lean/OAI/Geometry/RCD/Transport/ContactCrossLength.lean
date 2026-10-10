import OAI.Geometry.RCD.Transport.OptimalGeodesicLengths

namespace OAI

/-! # Cross endpoints of contacting geodesics retain length and dual contact -/

namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem contacting_geodesics_cross_length {φ ψ : X → ℝ}
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    {γ ζ : C(Time,X)} (hg : IsGeodesic γ) (hz : IsGeodesic ζ)
    (hγ : φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2)
    (hζ : φ (ζ 0)+ψ (ζ 1)=dist (ζ 0) (ζ 1)^2/2)
    {t : Time} (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) (hmeet : γ t=ζ t) :
    dist (γ 0) (ζ 1)=dist (γ 0) (γ 1) ∧
      φ (γ 0)+ψ (ζ 1)=dist (γ 0) (ζ 1)^2/2 := by
  have hlen := contacting_geodesics_equal_length had hg hz hγ hζ ht0 ht1 hmeet
  have hcross0 : dist (γ 0) (ζ 1) ≤ dist (γ 0) (γ 1) := by
    calc
      _ ≤ dist (γ 0) (γ t)+dist (γ t) (ζ 1) := dist_triangle _ _ _
      _ = dist (γ 0) (γ 1) := by
        rw [hg 0 t,hmeet,hz t 1,←hlen]
        change |(0:ℝ)-(t:ℝ)| *dist (γ 0) (γ 1)+|(t:ℝ)-1| *dist (γ 0) (γ 1) = _
        rw [zero_sub,abs_neg,abs_of_pos ht0,abs_of_nonpos (sub_nonpos.mpr ht1.le)]
        ring
  have hcross1 : dist (ζ 0) (γ 1) ≤ dist (γ 0) (γ 1) := by
    calc
      _ ≤ dist (ζ 0) (ζ t)+dist (ζ t) (γ 1) := dist_triangle _ _ _
      _ = dist (γ 0) (γ 1) := by
        rw [hz 0 t,←hmeet,hg t 1,←hlen]
        change |(0:ℝ)-(t:ℝ)| *dist (γ 0) (γ 1)+|(t:ℝ)-1| *dist (γ 0) (γ 1) = _
        rw [zero_sub,abs_neg,abs_of_pos ht0,abs_of_nonpos (sub_nonpos.mpr ht1.le)]
        ring
  have hs0 := pow_le_pow_left₀ dist_nonneg hcross0 2
  have hs1 := pow_le_pow_left₀ dist_nonneg hcross1 2
  have hcost : 2*dist (γ 0) (γ 1)^2 ≤ dist (γ 0) (ζ 1)^2+dist (ζ 0) (γ 1)^2 := by
    rw [←hlen] at hζ
    linarith [had (γ 0) (ζ 1),had (ζ 0) (γ 1)]
  have he : dist (γ 0) (ζ 1)=dist (γ 0) (γ 1) := by
    nlinarith [dist_nonneg (x:=γ 0) (y:=ζ 1),dist_nonneg (x:=γ 0) (y:=γ 1)]
  refine ⟨he,?_⟩
  rw [he]
  rw [←hlen] at hζ
  linarith [had (γ 0) (ζ 1),had (ζ 0) (γ 1)]

end RegularPointCoordinates

end OAI
