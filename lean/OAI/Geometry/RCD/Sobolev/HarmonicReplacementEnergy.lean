import OAI.Geometry.RCD.Sobolev.DirichletPoisson

namespace OAI

/-! # The exact energy defect of an actual harmonic replacement -/

open Set MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

theorem harmonic_replacement_energy_identity (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (Ω : Set X) (u h : SobolevSpace μ hQ)
    (hb : h-u∈SobolevSpace.dirichlet μ hQ Ω) (hh : IsSobolevHarmonicOn μ hQ Ω h) :
    energyForm μ hQ (h-u) (h-u)=energyForm μ hQ u u-energyForm μ hQ h h := by
  have hz := hh (h-u) hb
  rw [energyForm_sub_right] at hz
  have hc := energyForm_comm μ hQ u h
  simp only [energyForm_sub_left,energyForm_sub_right]
  linarith

theorem harmonic_replacement_difference_bound (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (Ω : Set X) (u h : SobolevSpace μ hQ)
    (hb : h-u∈SobolevSpace.dirichlet μ hQ Ω) (hh : IsSobolevHarmonicOn μ hQ Ω h)
    {P : ℝ} (hP : 0≤P)
    (hp : ∀ v : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ v.val‖^2≤P*energyForm μ hQ v.val v.val) :
    ‖SobolevSpace.toLp μ hQ (h-u)‖^2≤P*energyForm μ hQ u u := by
  have he : 0≤energyForm μ hQ h h := by
    rw [energyForm_self]
    exact mul_nonneg (by norm_num) (SobolevSpace.energy_nonneg μ hQ h)
  have hv := hp ⟨h-u,hb⟩
  change ‖SobolevSpace.toLp μ hQ (h-u)‖^2≤P*energyForm μ hQ (h-u) (h-u) at hv
  rw [harmonic_replacement_energy_identity μ hQ Ω u h hb hh] at hv
  exact hv.trans (mul_le_mul_of_nonneg_left (sub_le_self _ he) hP)

theorem harmonic_replacement_l2_bound (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (Ω : Set X) (u h : SobolevSpace μ hQ)
    (hb : h-u∈SobolevSpace.dirichlet μ hQ Ω) (hh : IsSobolevHarmonicOn μ hQ Ω h)
    {P : ℝ} (hP : 0≤P)
    (hp : ∀ v : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ v.val‖^2≤P*energyForm μ hQ v.val v.val) :
    ‖SobolevSpace.toLp μ hQ h‖^2≤2*‖SobolevSpace.toLp μ hQ u‖^2+2*P*energyForm μ hQ u u := by
  have hd := harmonic_replacement_difference_bound μ hQ Ω u h hb hh hP hp
  have ht : ‖SobolevSpace.toLp μ hQ h‖≤
      ‖SobolevSpace.toLp μ hQ u‖+‖SobolevSpace.toLp μ hQ (h-u)‖ := by
    convert norm_add_le (SobolevSpace.toLp μ hQ u) (SobolevSpace.toLp μ hQ (h-u)) using 1
    rw [← map_add,add_sub_cancel]
  nlinarith [norm_nonneg (SobolevSpace.toLp μ hQ h),norm_nonneg (SobolevSpace.toLp μ hQ u),
    norm_nonneg (SobolevSpace.toLp μ hQ (h-u)),
    sq_nonneg (‖SobolevSpace.toLp μ hQ u‖-‖SobolevSpace.toLp μ hQ (h-u)‖)]

end RegularPointCoordinates

end

end OAI
