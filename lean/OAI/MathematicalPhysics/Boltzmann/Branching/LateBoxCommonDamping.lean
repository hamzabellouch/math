import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedGeometricBlock
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedLateBoxPhysicalBlock
import OAI.MathematicalPhysics.Boltzmann.Branching.LateBoxAccessMeasure
import OAI.MathematicalPhysics.Boltzmann.Branching.ScaledBlockMass

namespace OAI

section

/-! # Physical branching growth for a whole interval of durations -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem lateBox_duration_window {κ d t K A₀ Δ : ℝ}
    (hκ : 0 < κ) (ht : 0 < t) (hd : d ≤ 1/2) (hK : 0 < K) (hA₀ : 0 < A₀)
    {p : V × V} (hp : p ∈ lateBox κ d t)
    (hlo : (8*κ*A₀/K)*t ≤ Δ) (hhi : Δ ≤ (16*κ*A₀/K)*t) :
    (K/(4*‖transverse p.1‖))*Δ ∈ Icc A₀ (8*A₀) := by
  have hrad : 0 < ‖transverse p.1‖ := by
    obtain ⟨h,_,_⟩ := lateBox_radius_bounds hκ ht hp
    have hh := mul_le_mul_of_nonneg_right hd (mul_pos hκ ht).le
    nlinarith
  have hρ : 0 ≤ K/(4*‖transverse p.1‖) := by positivity
  have hb := lateBox_block_duration hκ ht hd hK hA₀ hp
  constructor
  · exact hb.1.trans (mul_le_mul_of_nonneg_left hlo hρ)
  · have hh := mul_le_mul_of_nonneg_left hhi hρ
    have he : (16*κ*A₀/K)*t = 2*((8*κ*A₀/K)*t) := by ring
    rw [he,mul_left_comm] at hh
    exact hh.trans (by nlinarith [hb.2])

theorem lateBox_damped_duration_growth {d κ : ℝ}
    (hd : 0 < d) (hdsmall : d ≤ 1/2) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock:ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ Dmax : ℝ≥0, ∃ N : ℕ, ∃ ε γ₀ : ℝ,
      0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ D : ℝ≥0, referenceClock ≤ D → D ≤ Dmax →
      ∀ {θ η α γ K t Δ : ℝ}, (hθ : 0 < θ) →
      0 < η → η ≤ Real.log (1+ε/20) →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 < K → 480*(8*A₀) ≤ ε*K → 0 < t →
      (8*κ*A₀/K)*t ≤ Δ → Δ ≤ (16*κ*A₀/K)*t →
      ∀ (x : V) (v : RetainedState), (x,(v:V)) ∈ lateBox κ d t →
      (6:ℝ≥0∞) < dampedDensityScaledBlockMass D
        (GeometricBackground.beamCoefficients hθ hα hγ η ‖transverse x‖)
        (t+Δ) (K/(4*‖transverse x‖)) x Δ v κ d N := by
  have hM : 1 ≤ 4/κ := (le_div_iff₀ hκ).mpr (by linarith)
  obtain ⟨A₀,hA₀,hblock⟩ := GeometricBackground.geometric_damped_bounded_block_growth
    hd (by linarith) hκ hκsmall hg hM
  refine ⟨A₀,hA₀,?_⟩
  intro Dmax
  obtain ⟨N,ε,γ₀,hε,hεsmall,hγ₀,hgrowth⟩ := hblock (8*A₀) (by linarith) Dmax
  refine ⟨N,ε,γ₀,hε,hεsmall,hγ₀,?_⟩
  intro D hD hDmax θ η α γ K t Δ hθ hη hηsmall hα hαsmall hγ hγsmall hK hKlarge ht hlo hhi x v hp
  have hs := lateBox_geometric_scale hκ hκsmall.le hdsmall ht hp
  have hr := hs.1
  have hρ : 0 < K/(4*‖transverse x‖) := by positivity
  have hA := lateBox_duration_window hκ ht hdsmall hK hA₀ hp hlo hhi
  rw [dampedDensityScaledBlockMass_eq D _ hρ t x Δ v κ d N hA.2]
  exact hgrowth D hD hDmax hθ hη hηsmall hs.1 hα hαsmall hγ hγsmall hK hKlarge
    ht.le hs.2.1 hA x v rfl hs.2.2

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # One finite collision depth works throughout each expanding late box -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem uniform_lateBox_geometric_block {d κ : ℝ}
    (hd : 0 < d) (hdsmall : d ≤ 1/2) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ N : ℕ, ∃ ε γ₀ : ℝ,
      0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ {θ η α γ K t : ℝ}, (hθ : 0 < θ) →
      0 < η → η ≤ Real.log (1+ε/20) →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 < K → 480*(4*A₀) ≤ ε*K → 0 < t →
      ∀ (x : V) (v : RetainedState), (x,(v : V)) ∈ lateBox κ d t →
      let ρ := K/(4*‖transverse x‖)
      let A := ρ*((8*κ*A₀/K)*t)
      (6 : ℝ≥0∞) < boundedMediumBlockMass
        ((GeometricBackground.beamCoefficients hθ hα hγ η ‖transverse x‖).normalized ρ t x)
        A (4*A₀) (A,(0,v)) κ d N := by
  have hC : 1 ≤ 4/κ := (le_div_iff₀ hκ).mpr (by linarith)
  obtain ⟨A₀,hA₀,hblock⟩ := GeometricBackground.geometric_bounded_block_growth
    hd (by linarith) hκ hκsmall hg hC
  obtain ⟨N,ε,γ₀,hε,hεsmall,hγ₀,hgrowth⟩ := hblock (4*A₀) (by linarith)
  refine ⟨A₀,hA₀,N,ε,γ₀,hε,hεsmall,hγ₀,?_⟩
  intro θ η α γ K t hθ hη hηsmall hα hαsmall hγ hγsmall hK hKlarge ht x v hp
  obtain ⟨hr,htime,hax⟩ := lateBox_geometric_scale hκ hκsmall.le hdsmall ht hp
  exact hgrowth hθ hη hηsmall hr hα hαsmall hγ hγsmall hK hKlarge ht.le htime
    (lateBox_block_duration hκ ht hdsmall hK hA₀ hp) x v rfl hax

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform late-box branching growth in physical time -/

noncomputable section

open Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem lateBox_physical_block_growth {d κ : ℝ}
    (hd : 0 < d) (hdsmall : d ≤ 1/2) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ N : ℕ, ∃ ε γ₀ : ℝ,
      0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ {θ η α γ K t : ℝ}, (hθ : 0 < θ) →
      0 < η → η ≤ Real.log (1+ε/20) →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 < K → 480*(4*A₀) ≤ ε*K → 0 < t →
      ∀ (x : V) (v : RetainedState), (x,(v : V)) ∈ lateBox κ d t →
      let Δ := (8*κ*A₀/K)*t
      (6 : ℝ≥0∞) < densityScaledBlockMass
        (GeometricBackground.beamCoefficients hθ hα hγ η ‖transverse x‖)
        (t+Δ) (K/(4*‖transverse x‖)) x Δ v κ d N := by
  obtain ⟨A₀,hA₀,N,ε,γ₀,hε,hεsmall,hγ₀,hblock⟩ :=
    uniform_lateBox_geometric_block hd hdsmall hκ hκsmall hg
  refine ⟨A₀,hA₀,N,ε,γ₀,hε,hεsmall,hγ₀,?_⟩
  intro θ η α γ K t hθ hη hηsmall hα hαsmall hγ hγsmall hK hKlarge ht x v hp
  have hr : 0 < ‖transverse x‖ :=
    (lateBox_geometric_scale hκ hκsmall.le hdsmall ht hp).1
  have hρ : 0 < K/(4*‖transverse x‖) := by positivity
  have hT := (lateBox_block_duration hκ ht hdsmall hK hA₀ hp).2
  dsimp only
  rw [densityScaledBlockMass_eq _ hρ t x _ v κ d N hT]
  exact hblock hθ hη hηsmall hα hαsmall hγ hγsmall hK hKlarge ht x v hp

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A common physical clock for every point of the expanding growth box -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem lateBox_common_clock {κ d t K : ℝ} (hκ : 0 < κ) (ht : 0 < t)
    (hd : d ≤ 1/2) (hK : 0 < K) {p : V × V} (hp : p ∈ lateBox κ d t) :
    Real.toNNReal (K/(4*‖transverse p.1‖)) *
        Real.toNNReal (96*Real.pi*‖transverse p.1‖/(κ*t)) =
      Real.toNNReal (24*Real.pi*K/(κ*t)) := by
  have hr : 0 < ‖transverse p.1‖ := by
    obtain ⟨hlo,_,_⟩ := lateBox_radius_bounds hκ ht hp
    have hh := mul_le_mul_of_nonneg_right hd (mul_pos hκ ht).le
    nlinarith
  have hD := (lateBox_damping_range hκ ht hd hp).1
  have hD0 : 0 ≤ 96*Real.pi*‖transverse p.1‖/(κ*t) :=
    referenceClock.property.trans hD
  apply NNReal.coe_injective
  rw [NNReal.coe_mul,Real.coe_toNNReal _ (by positivity),Real.coe_toNNReal _ hD0,
    Real.coe_toNNReal _ (by positivity)]
  exact lateBox_damping_normalization hκ ht hr

theorem lateBox_common_damping_block {d κ : ℝ}
    (hd : 0 < d) (hdsmall : d ≤ 1/2) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock:ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ N : ℕ, ∃ ε γ₀ : ℝ,
      0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ {θ η α γ K t : ℝ}, (hθ : 0 < θ) →
      0 < η → η ≤ Real.log (1+ε/20) →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 < K → 480*(4*A₀) ≤ ε*K → 0 < t →
      ∀ (x : V) (v : RetainedState), (x,(v:V)) ∈ lateBox κ d t →
      let Δ := (8*κ*A₀/K)*t
      (6:ℝ≥0∞) < dampedDensityScaledBlockMass
        (Real.toNNReal (96*Real.pi*‖transverse x‖/(κ*t)))
        (GeometricBackground.beamCoefficients hθ hα hγ η ‖transverse x‖)
        (t+Δ) (K/(4*‖transverse x‖)) x Δ v κ d N := by
  obtain ⟨A₀,hA₀,hblock⟩ := lateBox_damped_physical_block_growth hd hdsmall hκ hκsmall hg
  obtain ⟨N,ε,γ₀,hε,hεsmall,hγ₀,hgrowth⟩ := hblock (3*referenceClock)
  refine ⟨A₀,hA₀,N,ε,γ₀,hε,hεsmall,hγ₀,?_⟩
  intro θ η α γ K t hθ hη hηsmall hα hαsmall hγ hγsmall hK hKlarge ht x v hp
  have hD := lateBox_damping_range hκ ht hdsmall hp
  have hD0 : 0 ≤ 96*Real.pi*‖transverse x‖/(κ*t) := referenceClock.property.trans hD.1
  have hlo : referenceClock ≤ Real.toNNReal (96*Real.pi*‖transverse x‖/(κ*t)) := by
    apply (NNReal.coe_le_coe).mp
    rw [Real.coe_toNNReal _ hD0]
    exact hD.1
  have hhi : Real.toNNReal (96*Real.pi*‖transverse x‖/(κ*t)) ≤ 3*referenceClock := by
    apply (NNReal.coe_le_coe).mp
    rw [Real.coe_toNNReal _ hD0,NNReal.coe_mul,NNReal.coe_ofNat]
    exact hD.2
  exact hgrowth _ hlo hhi hθ hη hηsmall hα hαsmall hγ hγsmall hK hKlarge ht x v hp

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
