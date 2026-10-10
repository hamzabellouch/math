import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.PosteriorSpatialCap

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_retained_spatial_cap {L : ℝ} (hL : 1 ≤ L) :
    ∃ C : ℝ,0 < C ∧
    ∀ (g₀ : 𝓢(Position,ℝ)), (∀ z,1 < ‖z‖ → g₀ z=0) → (∫ z,g₀ z^2)=1 →
    (∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖)) →
    ∀ {n J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction n) (h : Gradient n),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E D : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → 0 ≤ D →
    ∀ {c r₀ s : ℝ},0 < c → 0 < r₀ → 0 < s →
    c*(1+packetExponent)*s^packetExponent ≤ 1/2 →
    100000*c*s^packetExponent ≤ 10 →
    (8*L/100000)*s ≤ 1 → D*((8*L/100000)*s)^7 ≤ 1 →
    ∀ (j : ℕ),r₀*2^j ≤ s →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let r := fun k : Fin J =>  r₀*2^k.val
    ∃ G : Set (ObservationSample n J),(MeasurableSet G ∧
      MeasurableSet[MeasurableSpace.comap (tailObservation r j) inferInstance] G) ∧
      P.real Gᶜ ≤ C*(r₀*2^j)^249 ∧
      ∀ z∈G,∀ y : Position,3*(r₀*2^j)/4 ≤ ‖y‖ → ‖y‖ ≤ 6*L*(r₀*2^j) →
        ‖y‖^4*((Z:ℝ)*coulombKernel y-potentialOf
          (conditionalPacketDensity P Prod.fst (tailObservation r j) g₀ c r₀ s
            (tailObservation r j z)) y) ≤ physicalSpatialCap := by
  obtain ⟨K,hK,HK⟩ := physical_retained_field_excess_moment
  let A := 8*L/100000
  let B := physicalFieldCapUnit^2*observationEventEnergyConstant
  let C₀ := K*((4/3:ℝ)*B*A^7)^50
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; exact mul_pos (sq_pos_of_pos physicalFieldCapUnit_pos) observationEventEnergyConstant_pos
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨16*(64*L)^3*C₀,by positivity,?_⟩
  intro g₀ hg hm hrad n J Z hZ ψ g hd hn hmin E D hE hb hD c r₀ s hc hr₀ hs hscale hw hsA hsD j hrj
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw J (rawLaw ψ)
  let r : Fin J → ℝ := fun k =>  r₀*2^k.val
  let R := r₀*2^j
  have hR : 0 < R := by dsimp [R]; positivity
  have hrR : r₀ ≤ R := le_mul_of_one_le_right hr₀.le (one_le_pow₀ (by norm_num))
  have hgs : HasCompactSupport (g₀ : Position → ℝ) :=
    HasCompactSupport.intro (isCompact_closedBall (0:Position) 1) (fun z hz =>
      hg z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  have hmoment (y : Position) (hy0 : R/2 ≤ ‖y‖) (hy1 : ‖y‖ ≤ 8*L*R) :
      (∫ z,max (‖y‖^4*((Z:ℝ)*coulombKernel y-potentialOf
        (conditionalPacketDensity P Prod.fst (tailObservation r j) g₀ c r₀ s
          (tailObservation r j z)) y)-2*physicalFieldCapBase) 0 ∂P)  ≤  C₀*R^249 := by
    have hyn : 0 < ‖y‖ := by linarith
    have hy : y≠0 := norm_pos_iff.mp hyn
    let a := Coulomb.atomicCellScale y
    have ha : 0 < a := Coulomb.atomicCellScale_pos hy
    have haR : a ≤ A*R := by dsimp [a,A,Coulomb.atomicCellScale]; linarith
    have haS : a ≤ A*s := haR.trans (mul_le_mul_of_nonneg_left hrj hA.le)
    have ha1 : a ≤ 1 := haS.trans hsA
    have hDa : D*a^7 ≤ 1 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le haS 7) hD).trans hsD
    have hmax : max ‖y‖ r₀ ≤ 2*‖y‖ := max_le (by linarith) (by linarith)
    have hp := (packetWidth_le c r₀ s hc.le hr₀ hs y).trans
      (mul_le_mul_of_nonneg_left hmax (by positivity))
    have hwidth : 2*packetWidth c r₀ s y ≤ 40*a := by
      have hmul := mul_le_mul_of_nonneg_right hw hyn.le
      dsimp [a,Coulomb.atomicCellScale]
      nlinarith
    have H := HK g₀ hg hm hrad Z hZ hd hn hmin hE hb hD r
      (fun _ =>  by dsimp [r]; positivity) j hc hr₀ hs hscale y hy ha1 hDa hwidth
    apply H.trans
    have Hfac := cap_moment_factor hR ha.le hA.le hB.le
      (observationWidthSquareSum_nonneg (fun k : RetainedScales J j =>  (r k.val)^(101/100:ℝ)))
      haR (observationWidthSquareSum_retained_dyadic hr₀ J j)
    have Hmul := mul_le_mul_of_nonneg_left Hfac hK.le
    change K*(B*observationWidthSquareSum (fun k : RetainedScales J j =>  (r k.val)^(101/100:ℝ))*a^7)^50 ≤ C₀*R^249
    calc
      _  ≤  K*(((4/3:ℝ)*B*A^7)^50*R^249) := Hmul
      _ = _ := by dsimp [C₀]; ring
  obtain ⟨G,hG,hprob,hcap⟩ := posterior_spatial_cap_of_moment P Prod.fst
    (tailObservation r j) (measurable_tailObservation r j) g₀.continuous hgs hm hc hr₀ hs
    (by positivity : (0:ℝ) ≤ Z) hR hL (by positivity : 0 ≤ C₀*R^249) hmoment
  refine ⟨G,hG,?_,hcap⟩
  calc
    _  ≤  16*(64*L)^3*(C₀*R^249) := hprob
    _ = _ := by ring
end NeutralAtom
end

end

end OAI
