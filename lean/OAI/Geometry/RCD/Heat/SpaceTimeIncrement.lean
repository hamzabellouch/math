import OAI.Geometry.RCD.Heat.SpaceTimeSlopeRate

namespace OAI

/-! # Turning the two-time quadratic bound into a spatial increment rate -/

namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem spaceTimeSlopeRate_increment {U : ℝ → X → ℝ} {H : ℝ → ℝ}
    {K N t α ell r : ℝ} {x y : X} (hell : 0 < ell) (hr : 0 < r)
    (hxy : dist x y=r)
    (hb : U (t+α*r) x-U t y ≤ ell*r/2*H (t+α*r)+
      Real.exp (-K*((t+α*r)+t))*(dist x y^2+2*N*(Real.sqrt (t+α*r)-Real.sqrt t)^2)/(2*(ell*r))) :
    U t x-U t y ≤ spaceTimeSlopeRate (fun s => U s x) H K N t α ell r*r := by
  rw [hxy] at hb
  have he : spaceTimeSlopeRate (fun s => U s x) H K N t α ell r*r =
      ell*r/2*H (t+α*r)+
        Real.exp (-K*((t+α*r)+t))*(r^2+2*N*(Real.sqrt (t+α*r)-Real.sqrt t)^2)/(2*(ell*r))-
          (U (t+α*r) x-U t x) := by
    unfold spaceTimeSlopeRate
    field_simp
  rw [he]
  linarith only [hb]

end RegularPointCoordinates

end OAI
