import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicCutoffGeometry
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedLocalBeamBlock
import OAI.MathematicalPhysics.Boltzmann.Branching.LargeOutput
import OAI.MathematicalPhysics.Boltzmann.Branching.SmallFirstGain
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalBeamBlock
import OAI.MathematicalPhysics.Boltzmann.Jets.BeamNormalOutgoing
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricDampedRetention

namespace OAI

section

/-! # Actual geometric cold coefficients are close throughout a short physical cylinder -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem beam_near_on_cylinder {ε C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 1 ≤ C) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ {θ η r α γ ρ t₀ A : ℝ},
      (hθ : 0 < θ) → 0 < η → η ≤ Real.log (1+ε/20) → 0 < r →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ → 0 < ρ → 0 ≤ t₀ →
      t₀ ≤ C*r/2 → 6*A/ρ ≤ (ε/20)*r →
      ∀ x₀ : Velocity, ‖transverse x₀‖ = r → |axial x₀| ≤ C*r/2 →
      ∀ p : ℝ × Velocity, p.1 ∈ Icc t₀ (t₀+A/ρ) → ‖p.2-x₀‖ ≤ 6*A/ρ →
        BeamNear (beamCoefficients hθ hα hγ η r) ε p := by
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  obtain ⟨γ₀,hγ₀,hdensity⟩ := beam_density_tolerance hε hε1 hCpos
  refine ⟨γ₀,hγ₀,?_⟩
  intro θ η r α γ ρ t₀ A hθ hη hηsmall hr hα hαε hγ hγsmall hρ ht₀ ht₀C hshort x₀ hx₀ hz₀ p hpt hpx
  have hdist : ‖p.2-x₀‖ ≤ (ε/20)*r := hpx.trans hshort
  have hδr : (ε/20)*r ≤ C*r/2 := by nlinarith
  have htime : A/ρ ≤ C*r/2 := by
    rw [mul_div_assoc] at hshort
    have hCr : 0 ≤ C*r := mul_nonneg hCpos.le hr.le
    linarith
  have ht : 0 ≤ p.1 := ht₀.trans hpt.1
  have htC : p.1 ≤ C*r := by linarith [hpt.2]
  have htrans : |‖transverse p.2‖-r| ≤ (ε/20)*r := by
    calc
      _ = |‖transverse p.2‖-‖transverse x₀‖| := by rw [hx₀]
      _ ≤ ‖transverse p.2-transverse x₀‖ := abs_norm_sub_norm_le _ _
      _ = ‖transverse (p.2-x₀)‖ := by rw [PlaneChart.transverse_sub]
      _ ≤ ‖p.2-x₀‖ := LargeOutput.transverse_norm_le _
      _ ≤ _ := hdist
  have hxpos : 0 < ‖transverse p.2‖ := by
    have hh := (abs_le.mp htrans).1
    nlinarith
  have hzC : |axial p.2| ≤ C*r := by
    have hh := abs_add_le (axial p.2-axial x₀) (axial x₀)
    rw [sub_add_cancel] at hh
    have hh' : |axial p.2-axial x₀| ≤ (ε/20)*r := by
      rw [← PlaneChart.axial_sub]
      exact (SmallInputGeometry.abs_axial_le_norm _).trans hdist
    linarith
  have hd (σ : ℝ) (hσ : |σ| = 1) : |beamDensity θ η α γ r σ p-1| ≤ ε :=
    hdensity hθ hη hηsmall hr hα (hαε.trans hε1) hγ hγsmall ht htC p.2 hxpos htrans hzC σ hσ
  have hp := (beamVelocity_error hα θ η γ 1 p).trans hαε
  have hm := (beamVelocity_error hα θ η γ (-1) p).trans hαε
  refine ⟨?_,?_,hd 1 (by norm_num),hd (-1) (by norm_num)⟩
  · simpa only [beamCoefficients,one_smul] using hp
  · simpa only [beamCoefficients,neg_one_smul] using hm

theorem cylinder_small_of_density_scale {A K r ε : ℝ} (hK : 0 < K) (hr : 0 < r)
    (hbudget : 480*A ≤ ε*K) : 6*A/(K/(4*r)) ≤ (ε/20)*r := by
  have hρ : 0 < K/(4*r) := by positivity
  apply (div_le_iff₀ hρ).mpr
  have he : (ε/20)*r*(K/(4*r)) = ε*K/80 := by field_simp; ring
  rw [he]
  linarith

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Actual geometric damping bounds on smooth characteristic phase cutoffs -/

noncomputable section

open Set MeasureTheory
open BoltzmannNonuniqueness.EuclideanFlight
open BoltzmannNonuniqueness.ReferenceGeometry
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem exists_characteristic_cutoff_near_clock {ε C : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1/4) (hC : 1 ≤ C) (l : ℝ) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ {θ η r α γ K t₀ Δ R : ℝ},
      (hθ : 0 < θ) → 0 < η → η ≤ Real.log (1+ε/20) → 0 < r →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ → 0 ≤ K →
      0 ≤ t₀ → t₀ ≤ C*r/2 → 0 < Δ → 0 < R → 2*R+7*Δ ≤ (ε/20)*r →
      ∀ x : Velocity, ‖transverse x‖ = r → |axial x| ≤ C*r/2 →
      ∃ β : (Velocity × Velocity) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) β ∧ HasCompactSupport β ∧
        (∀ p, 0 ≤ β p) ∧ (∀ p, β p ≤ 1) ∧
        (∀ p, ‖p.1+t₀ • p.2-x‖ ≤ R → ‖p.2‖ ≤ 6 → β p = 1) ∧
        (∀ u : CharacteristicPhase, u.1 ∈ Icc t₀ (t₀+Δ) → u.2 ∈ tsupport β →
          frequency θ η l K α γ u.1
            (transverse (u.2.1+u.1 • u.2.2),axial (u.2.1+u.1 • u.2.2)) u.2.2 ≤
              (K/(4*r))*(48*Real.pi)) := by
  obtain ⟨γ₀,hγ₀,hnear⟩ := beam_near_on_cylinder hε (by linarith) hC
  refine ⟨γ₀,hγ₀,?_⟩
  intro θ η r α γ K t₀ Δ R hθ hη hηsmall hr hα hαsmall hγ hγsmall hK ht₀ ht₀C hΔ hR hshort x hx hax
  obtain ⟨β,hβ,hβc,hβn,hβ₁,hβcore,hβsupport⟩ := exists_characteristic_phase_cutoff t₀ x hR
  refine ⟨β,hβ,hβc,hβn,hβ₁,hβcore,?_⟩
  intro u hut hus
  have hΔA : Δ ≤ (2*R+7*Δ)/6 := by linarith
  have htime : u.1 ∈ Icc t₀ (t₀+(2*R+7*Δ)/6/1) := by
    constructor
    · exact hut.1
    · simp only [div_one]
      linarith [hut.2]
  have hspace : ‖(u.2.1+u.1 • u.2.2)-x‖ ≤ 6*((2*R+7*Δ)/6)/1 := by
    have hh := phase_displacement_bound hut (hβsupport u.2 hus).1 (hβsupport u.2 hus).2
    convert hh using 1; ring
  have hs : 6*((2*R+7*Δ)/6)/1 ≤ (ε/20)*r := by
    convert hshort using 1; ring
  have hn := hnear hθ hη hηsmall hr hα hαsmall hγ hγsmall (by norm_num : (0:ℝ)<1)
    ht₀ ht₀C hs x hx hax (u.1,u.2.1+u.1 • u.2.2) htime hspace
  exact frequency_le_near_clock_seven hθ hK hα hγ hr (ht₀.trans hut.1) η l _ _
    (hβsupport u.2 hus).2 hεsmall hn

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # A finite growing block for the actual geometric cold coefficients -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem geometric_damped_bounded_block_growth {d κ C : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) (hC : 1 ≤ C) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∀ Dmax : ℝ≥0,
      ∃ N : ℕ, ∃ ε γ₀ : ℝ, 0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ D : ℝ≥0, referenceClock ≤ D → D ≤ Dmax →
      ∀ {θ η r α γ K t₀ A : ℝ}, (hθ : 0 < θ) →
      0 < η → η ≤ Real.log (1+ε/20) → 0 < r →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 < K → 480*T ≤ ε*K → 0 ≤ t₀ → t₀ ≤ C*r/2 → A ∈ Icc A₀ T →
      ∀ (x₀ : Velocity) (v : RetainedState), ‖transverse x₀‖ = r → |axial x₀| ≤ C*r/2 →
      (6 : ℝ≥0∞) < dampedBoundedBlockMass D
        ((beamCoefficients hθ hα hγ η r).normalized (K/(4*r)) t₀ x₀)
        A T (A,(0,v)) κ d N := by
  obtain ⟨A₀,hA₀,hblock⟩ := uniform_damped_bounded_physical_block hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T hT Dmax
  obtain ⟨N,ε₀,hε₀,hgrowth⟩ := hblock T hT Dmax
  let ε := min ε₀ (1/4:ℝ)
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hεsmall : ε ≤ 1/4 := min_le_right _ _
  obtain ⟨γ₀,hγ₀,hnear⟩ := beam_near_on_cylinder hε (by linarith) hC
  refine ⟨N,ε,γ₀,hε,hεsmall,hγ₀,?_⟩
  intro D hD hDmax θ η r α γ K t₀ A hθ hη hηsmall hr hα hαε hγ hγsmall hK hlarge ht₀ ht₀C hA x₀ v hx₀ hz₀
  have hρ : 0 < K/(4*r) := by positivity
  have hbudget : 480*A ≤ ε*K := (mul_le_mul_of_nonneg_left hA.2 (by norm_num)).trans hlarge
  have hshort := cylinder_small_of_density_scale hK hr hbudget
  apply hgrowth D hD hDmax ε ⟨hε.le,min_le_left _ _⟩ A hA v (beamCoefficients hθ hα hγ η r)
    (K/(4*r)) t₀ x₀ hρ
  exact hnear hθ hη hηsmall hr hα hαε hγ hγsmall hρ ht₀ ht₀C hshort x₀ hx₀ hz₀

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # A finite growing block for the actual geometric cold coefficients -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem geometric_damped_finite_block_growth {d κ C : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) (hC : 1 ≤ C) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∀ Dmax : ℝ≥0,
      ∃ N : ℕ, ∃ ε γ₀ : ℝ, 0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ D : ℝ≥0, referenceClock ≤ D → D ≤ Dmax →
      ∀ {θ η r α γ K t₀ A : ℝ}, (hθ : 0 < θ) →
      0 < η → η ≤ Real.log (1+ε/20) → 0 < r →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 < K → 480*T ≤ ε*K → 0 ≤ t₀ → t₀ ≤ C*r/2 → A ∈ Icc A₀ T →
      ∀ (x₀ : Velocity) (v : RetainedState), ‖transverse x₀‖ = r → |axial x₀| ≤ C*r/2 →
      (6 : ℝ≥0∞) < dampedMediumBlockMass D
        ((beamCoefficients hθ hα hγ η r).normalized (K/(4*r)) t₀ x₀)
        A T (A,(0,v)) κ d N := by
  obtain ⟨A₀,hA₀,hblock⟩ := uniform_damped_physical_beam_block hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T hT Dmax
  obtain ⟨N,ε₀,hε₀,hgrowth⟩ := hblock T hT Dmax
  let ε := min ε₀ (1/4:ℝ)
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hεsmall : ε ≤ 1/4 := min_le_right _ _
  obtain ⟨γ₀,hγ₀,hnear⟩ := beam_near_on_cylinder hε (by linarith) hC
  refine ⟨N,ε,γ₀,hε,hεsmall,hγ₀,?_⟩
  intro D hD hDmax θ η r α γ K t₀ A hθ hη hηsmall hr hα hαε hγ hγsmall hK hlarge ht₀ ht₀C hA x₀ v hx₀ hz₀
  have hρ : 0 < K/(4*r) := by positivity
  have hbudget : 480*A ≤ ε*K := (mul_le_mul_of_nonneg_left hA.2 (by norm_num)).trans hlarge
  have hshort := cylinder_small_of_density_scale hK hr hbudget
  apply hgrowth D hD hDmax ε ⟨hε.le,min_le_left _ _⟩ A hA v (beamCoefficients hθ hα hγ η r)
    (K/(4*r)) t₀ x₀ hρ
  exact hnear hθ hη hηsmall hr hα hαε hγ hγsmall hρ ht₀ ht₀C hshort x₀ hx₀ hz₀

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # A finite growing block for the actual geometric cold coefficients -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.ReferenceGeometry BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem geometric_finite_block_growth {d κ C : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) (hC : 1 ≤ C) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T →
      ∃ N : ℕ, ∃ ε γ₀ : ℝ, 0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ {θ η r α γ K t₀ A : ℝ}, (hθ : 0 < θ) →
      0 < η → η ≤ Real.log (1+ε/20) → 0 < r →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 < K → 480*T ≤ ε*K → 0 ≤ t₀ → t₀ ≤ C*r/2 → A ∈ Icc A₀ T →
      ∀ (x₀ : Velocity) (v : RetainedState), ‖transverse x₀‖ = r → |axial x₀| ≤ C*r/2 →
      (6 : ℝ≥0∞) < mediumBlockMass
        ((beamCoefficients hθ hα hγ η r).normalized (K/(4*r)) t₀ x₀)
        A T (A,(0,v)) κ d N := by
  obtain ⟨A₀,hA₀,hblock⟩ := uniform_physical_beam_block hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T hT
  obtain ⟨N,ε₀,hε₀,hgrowth⟩ := hblock T hT
  let ε := min ε₀ (1/4:ℝ)
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hεsmall : ε ≤ 1/4 := min_le_right _ _
  obtain ⟨γ₀,hγ₀,hnear⟩ := beam_near_on_cylinder hε (by linarith) hC
  refine ⟨N,ε,γ₀,hε,hεsmall,hγ₀,?_⟩
  intro θ η r α γ K t₀ A hθ hη hηsmall hr hα hαε hγ hγsmall hK hlarge ht₀ ht₀C hA x₀ v hx₀ hz₀
  have hρ : 0 < K/(4*r) := by positivity
  have hbudget : 480*A ≤ ε*K := (mul_le_mul_of_nonneg_left hA.2 (by norm_num)).trans hlarge
  have hshort := cylinder_small_of_density_scale hK hr hbudget
  apply hgrowth ε ⟨hε.le,min_le_left _ _⟩ A hA v (beamCoefficients hθ hα hγ η r)
    (K/(4*r)) t₀ x₀ hρ
  exact hnear hθ hη hηsmall hr hα hαε hγ hγsmall hρ ht₀ ht₀C hshort x₀ hx₀ hz₀

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # A clock bound across an annulus, using the density scale at each point -/

noncomputable section
open Set
open BoltzmannNonuniqueness.ReferenceGeometry BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem annular_frequency_bound {M : ℝ} (hM : 1 ≤ M) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ {θ η α γ K t r₀ : ℝ},
      (hθ : 0 < θ) → 0 < η → η ≤ Real.log (1+(1/4:ℝ)/20) →
      (hα : 0 ≤ α) → α ≤ 1/4 → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 ≤ K → 0 ≤ t → 0 < r₀ → ∀ l : ℝ, ∀ x v : Velocity,
      r₀ ≤ ‖transverse x‖ → t ≤ M*‖transverse x‖/2 →
      |axial x| ≤ M*‖transverse x‖/2 → ‖v‖ ≤ 7 →
      frequency θ η l K α γ t (transverse x,axial x) v ≤
        (K/(4*r₀))*(48*Real.pi) := by
  obtain ⟨γ₀,hγ₀,hnear⟩ := beam_near_on_cylinder
    (by norm_num : (0:ℝ)<1/4) (by norm_num : (1/4:ℝ)≤1) hM
  refine ⟨γ₀,hγ₀,?_⟩
  intro θ η α γ K t r₀ hθ hη hηsmall hα hαsmall hγ hγsmall hK ht hr₀ l x v hx htime hax hv
  have hr : 0 < ‖transverse x‖ := hr₀.trans_le hx
  have hn := hnear (r := ‖transverse x‖) (ρ := 1) (A := 0)
    hθ hη hηsmall hr hα hαsmall hγ hγsmall (by norm_num)
    ht htime (by simp)
      x rfl hax (t,x) (by simp) (by simp)
  have hf := frequency_le_near_clock_seven hθ hK hα hγ hr ht η l x v hv
    (by norm_num : (1/4:ℝ)≤1/4) hn
  exact hf.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left hK (by positivity) (by nlinarith)) (by positivity))

end BoltzmannNonuniqueness.GeometricBackground

end

end

end OAI
