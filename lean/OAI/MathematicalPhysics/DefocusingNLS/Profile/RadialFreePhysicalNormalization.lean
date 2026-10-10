import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeAnnulus
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorOutgoingContinuation

namespace OAI

/-! Boundary normalization for the physical profile, including its radial phase. -/

open Set Filter
namespace DefocusingNLS

noncomputable def radialFreePhysicalBoundaryCoefficient (b h : ℝ) : ℂ :=
  Complex.exp (-(2*Complex.I*(b : ℂ)*(Real.log innerBoundaryRadius : ℂ)))*
    radialFreeBoundaryCoefficient b h

theorem radialFreeSlowValue_mul (q c m : ℂ) (t : ℝ) :
    radialFreeSlowValue q (c*m) t=c*radialFreeSlowValue q m t := by
  unfold radialFreeSlowValue
  ring

theorem radialFreePhysicalBoundaryCoefficient_spec
    (w : Metric.closedBall (0 : ℂ) (ProfileCertificate.radius : ℝ))
    (h : ℝ) (hh : 0 < h) :
    let b := (ProfileCertificate.centerB : ℝ)+w.val.re
    let m := radialFreePhysicalBoundaryCoefficient b h
    m ≠ 0 ∧
      Complex.exp (2*Complex.I*(b : ℂ)*(Real.log innerBoundaryRadius : ℂ))*
        radialFreeSlowValue (-Complex.I*(b : ℂ)) m (Real.log innerBoundaryRadius)=(h : ℂ) ∧
      ‖radialFreeSlowValue (-Complex.I*(b : ℂ)) m (Real.log innerBoundaryRadius)‖=h := by
  intro b m
  obtain ⟨hne,hvalue⟩ := radialFreeBoundaryCoefficient_spec w h hh
  have hexp : Complex.exp (2*Complex.I*(b : ℂ)*(Real.log innerBoundaryRadius : ℂ))*
      Complex.exp (-(2*Complex.I*(b : ℂ)*(Real.log innerBoundaryRadius : ℂ)))=1 := by
    rw [← Complex.exp_add,add_neg_cancel,Complex.exp_zero]
  have hnorm : ‖Complex.exp (-(2*Complex.I*(b : ℂ)*(Real.log innerBoundaryRadius : ℂ)))‖=1 := by
    simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  refine ⟨mul_ne_zero (Complex.exp_ne_zero _) hne,?_,?_⟩
  · change Complex.exp _*radialFreeSlowValue _ (Complex.exp _*radialFreeBoundaryCoefficient b h) _=_
    rw [radialFreeSlowValue_mul,← mul_assoc,hexp,one_mul]
    exact hvalue
  · change ‖radialFreeSlowValue _ (Complex.exp _*radialFreeBoundaryCoefficient b h) _‖=h
    rw [radialFreeSlowValue_mul,norm_mul,hnorm,hvalue,one_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hh]

theorem exists_radialExterior_physical_boundary_limit
    (w : Metric.closedBall (0 : ℂ) (ProfileCertificate.radius : ℝ))
    (h : ℝ) (hh : 0 < h) (hh1 : h < 1) (ν m : ℕ → ℂ)
    (hν : Tendsto ν atTop
      (nhds (2*Complex.I*(((ProfileCertificate.centerB : ℝ)+w.val.re : ℝ) : ℂ))))
    (hm : Tendsto m atTop
      (nhds (radialFreePhysicalBoundaryCoefficient ((ProfileCertificate.centerB : ℝ)+w.val.re) h))) :
    let q := -Complex.I*(((ProfileCertificate.centerB : ℝ)+w.val.re : ℝ) : ℂ)
    let m₀ := radialFreePhysicalBoundaryCoefficient ((ProfileCertificate.centerB : ℝ)+w.val.re) h
    ∃ Z : ℕ → ℝ → ℂ × ℂ,
      TendstoUniformlyOn Z (radialFreeSlowJet q m₀) atTop
        (Ici (Real.log innerBoundaryRadius)) ∧
      (∀ n, Continuous (Z n)) ∧
      (∀ᶠ n in atTop, HasRadialOutgoingExpansion (ν n) n (m n) (Z n)) ∧
      ∀ᶠ n in atTop, ∀ t, Real.log innerBoundaryRadius ≤ t → (Z n t).1 ≠ 0 ∧
        HasDerivAt (Z n) (radialExteriorODEField (ν n) n t (Z n t)) t := by
  intro q m₀
  obtain ⟨hne,_,hvalue⟩ := radialFreePhysicalBoundaryCoefficient_spec w h hh
  obtain ⟨δ,ρ,hd,hdm,hm1,hρ,hupper,hlower⟩ := radialFreeSlow_annulus w m₀ hne (by
    rw [hvalue]
    exact hh1)
  apply exists_radialExterior_outgoing_extended ν m q m₀ (by simp [q]) _ hm δ ρ
    (Real.log innerBoundaryRadius) hd hdm hm1 hρ hupper hlower
  convert hν using 1
  dsimp [q]
  congr 1
  ring

end DefocusingNLS

end OAI
