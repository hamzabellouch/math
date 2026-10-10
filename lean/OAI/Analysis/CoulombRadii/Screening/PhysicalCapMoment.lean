import Mathlib
import OAI.Analysis.CoulombRadii.Screening.ScaledFieldCap
import OAI.Analysis.CoulombRadii.Screening.LogTailMoment

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

def physicalFieldCapBase : ℝ := max 1 (2*physicalFieldCapUnit)
lemma physicalFieldCapBase_ge_one : 1 ≤ physicalFieldCapBase := le_max_left _ _
lemma physicalFieldCapBase_ge_unit : 2*physicalFieldCapUnit ≤ physicalFieldCapBase := le_max_right _ _

theorem physical_retained_field_excess_moment : ∃ K : ℝ,0 < K ∧
    ∀ (g₀ : 𝓢(Position,ℝ)), (∀ z,1 < ‖z‖ → g₀ z=0) → (∫ z,g₀ z^2)=1 →
    (∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖)) →
    ∀ {n J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E D : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → 0 ≤ D → ∀ (r : Fin J → ℝ), (∀ k,0 < r k) → ∀ (j : ℕ),
    ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
    c*(1+packetExponent)*s^packetExponent ≤ 1/2 →
    ∀ (y : Position), y≠0 → Coulomb.atomicCellScale y ≤ 1 →
    D*(Coulomb.atomicCellScale y)^7 ≤ 1 →
    2*packetWidth c r₀ s y ≤ 40*Coulomb.atomicCellScale y →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    (∫ z,max (‖y‖^4*((Z:ℝ)*coulombKernel y-
      potentialOf (conditionalPacketDensity P Prod.fst (tailObservation r j) g₀ c r₀ s
        (tailObservation r j z)) y)-2*physicalFieldCapBase) 0 ∂P) ≤
      K*(physicalFieldCapUnit^2*observationEventEnergyConstant*
          observationWidthSquareSum (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ))*
          (Coulomb.atomicCellScale y)^7)^50 := by
  obtain ⟨K,hK,HK⟩ := logarithmic_tail_integral
  refine ⟨K,hK,?_⟩
  intro g₀ hg hm hrad n J Z hZ ψ g hd hn hmin E D hE hbase hD r hr j c r₀ s hc hr₀ hs hscale y hy ha1 hDa hwidth
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw J (rawLaw ψ)
  let μ := conditionalPacketDensity P Prod.fst (tailObservation r j) g₀ c r₀ s
  let f := fun z : ObservationSample n J => ‖y‖^4*((Z:ℝ)*coulombKernel y-potentialOf (μ (tailObservation r j z)) y)
  have hgs : HasCompactSupport (g₀ : Position → ℝ) :=
    HasCompactSupport.intro (isCompact_closedBall (0:Position) 1) (fun z hz =>
      hg z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  have hf : Measurable f := ((measurable_const.sub
    (measurable_conditionalPacketPotential_data P Prod.fst (tailObservation r j)
      g₀.continuous hgs hm hc hr₀ hs y)).comp (measurable_tailObservation r j)).const_mul _
  have hB (z : ObservationSample n J) : f z ≤ ‖y‖^4*((Z:ℝ)*coulombKernel y) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg y) 4)
    have hpot := potentialOf_nonneg (conditionalPacketDensity_nonneg P Prod.fst
      (tailObservation r j) g₀ hc hr₀ hs (tailObservation r j z)) y
    linarith
  apply HK P hf hB physicalFieldCapBase_ge_one
    (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) observationEventEnergyConstant_pos.le)
      (observationWidthSquareSum_nonneg _)) (pow_nonneg (Coulomb.atomicCellScale_pos hy).le 7))
  intro b hb hp
  have hC0 : 0 ≤ physicalFieldCapBase := zero_le_one.trans physicalFieldCapBase_ge_one
  have hb' : physicalFieldCapBase ≤ b := by linarith
  have H := physical_retained_field_tail g₀ hg hm hrad Z hZ hd hn hmin hE hbase hD
    r hr j hc hr₀ hs hscale y hy ha1 hDa hwidth
    (physicalFieldCapBase_ge_unit.trans hb') hp
  apply le_trans _ H
  apply pow_le_pow_left₀ (by linarith : 0 ≤ b-physicalFieldCapBase)
  linarith [physicalFieldCapBase_ge_unit]
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom
lemma cap_scale_power {r : ℝ} (hr : 0<r) :
    ((((r^(101/100:ℝ))⁻¹)^2)*r^7)^50=r^249 := by
  rw [←Real.rpow_neg hr.le,←Real.rpow_natCast _ 2,←Real.rpow_mul hr.le,
    ←Real.rpow_natCast r 7,←Real.rpow_add hr,←Real.rpow_natCast _ 50,←Real.rpow_mul hr.le]
  norm_num

lemma cap_moment_factor {r a A C S : ℝ} (hr : 0<r) (ha : 0≤a)
    (_ : 0≤A) (hC : 0≤C) (hS : 0≤S) (haA : a≤A*r)
    (hwidth : S≤(4/3:ℝ)*((r^(101/100:ℝ))⁻¹)^2) :
    (C*S*a^7)^50≤((4/3:ℝ)*C*A^7)^50*r^249 := by
  have hp : a^7≤A^7*r^7 := by simpa only [mul_pow] using pow_le_pow_left₀ ha haA 7
  have h1 := mul_le_mul (mul_le_mul_of_nonneg_left hwidth hC) hp
    (pow_nonneg ha 7) (by positivity : 0≤C*((4/3:ℝ)*((r^(101/100:ℝ))⁻¹)^2))
  have h2 : C*S*a^7≤((4/3:ℝ)*C*A^7)*(((r^(101/100:ℝ))⁻¹)^2*r^7) := by
    calc
      _ ≤ C*((4/3:ℝ)*((r^(101/100:ℝ))⁻¹)^2)*(A^7*r^7) := h1
      _ = _ := by ring
  have h3 := pow_le_pow_left₀ (by positivity : 0≤C*S*a^7) h2 50
  rw [mul_pow ((4/3:ℝ)*C*A^7),cap_scale_power hr] at h3
  exact h3

lemma cap_annulus_compact (r L : ℝ) :
    IsCompact {z : Position | r/2≤‖z‖ ∧ ‖z‖≤8*L*r} := by
  apply (isCompact_closedBall (0:Position) (8*L*r)).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro z hz
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2

lemma cap_annulus_volume_ratio {r L : ℝ} (hr : 0<r) (hL : 1≤L) :
    volume.real {z : Position | r/2≤‖z‖ ∧ ‖z‖≤8*L*r}/
      (4*Real.pi/3*(r/8)^3)≤(64*L)^3 := by
  have hR : 0≤8*L*r := by positivity
  have hV : 0<4*Real.pi/3*(r/8)^3 := by positivity
  have H : volume.real {z : Position | r/2≤‖z‖ ∧ ‖z‖≤8*L*r}≤
      volume.real (Metric.closedBall (0:Position) (8*L*r)) := by
    apply measureReal_mono ?_ (isCompact_closedBall (0:Position) (8*L*r)).measure_ne_top
    intro z hz
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2
  rw [Coulomb.volume_closedBall_three _ hR] at H
  apply (div_le_iff₀ hV).2
  have he : (64*L)^3*(4*Real.pi/3*(r/8)^3)=4*Real.pi/3*(8*L*r)^3 := by ring
  rw [he]
  exact H
end NeutralAtom
end

end

end OAI
