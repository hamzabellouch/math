import OAI.MeasureTheory.Falconer.Fourier.NoncomparableOriginalIntegral
import OAI.MeasureTheory.Falconer.Fourier.JetStateFarSupport

namespace OAI

/-! # Radial replacement of the original two-sphere kernel

Both endpoint amplitudes are the original recursive symbols. The estimate
is pointwise in all four endpoints, so its norm can subsequently be
integrated without any spatial measurability assertion for stationary jets.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

private theorem state_pair_sphere_measurable {m K L : ℕ} {F : Finset PolicyDescriptor} {Dq : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F Dq)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (T : PolicyDescriptor → Finset (Sphere (m+3)))
    (A : ℝ) (x y : Space (m+3)) :
    Measurable (fun w : Sphere (m+3) => f.value Q ρ profile N σ J i T A x w *
      star (f.value Q ρ profile N σ J i T A y w)) := by
  have hm : Measurable (fun w : Sphere (m+3) =>
      f.pairAmbient Q ρ profile N σ J i T A x y (w : Space (m+3))) :=
    (f.pairAmbient_smooth Q ρ profile N σ J i T A x y).continuous.measurable.comp
      continuous_subtype_val.measurable
  simpa only [DescriptorJetSymbol.pairAmbient_sphere] using hm

private theorem state_pair_sphere_bound {m K L : ℕ} {F : Finset PolicyDescriptor} {Dq : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F Dq)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (T : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ T b, ∀ z ∈ T b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (x y : Space (m+3)) (r : ℝ) (e : Sphere (m+3)) :
    ‖sphereOscillation r e (fun w => f.value Q ρ profile N σ J i T A x w *
      star (f.value Q ρ profile N σ J i T A y w))‖ ≤
      ((descriptorJetBound (m+3) K)^K*A⁻¹)^2*(sphereMeasure (m+3)).real univ := by
  apply sphereOscillation_norm_le_of_bound
  intro w
  rw [norm_mul,norm_star,pow_two]
  exact mul_le_mul (f.value_norm_le Q ρ profile N σ J i T hF hA x w)
    (f.value_norm_le Q ρ profile N σ J i T hF hA y w) (norm_nonneg _)
    (mul_nonneg (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)
      (inv_nonneg.mpr hA.le))

theorem exists_jetState_original_stationary_replacement
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L J : ℕ) (hJ : 1 ≤ J) (hJL : 2*J+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧
      ∀ (F : Finset PolicyDescriptor) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
        (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J₀ i : ℕ)
        (T : PolicyDescriptor → Finset (Sphere (m+3))),
      (∀ b ∈ F, ∀ w ∈ T b, ∀ z ∈ T b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A →
      1 ≤ 2*(E+Dq) → (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f g : DescriptorJetSymbol (m+1) K L F Dq) (w₀ : Sphere (m+3))
        (v base κ : ℝ), 1 ≤ base → 2*(E+Dq) ≤ base^2 →
      ∀ z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3)),
      (∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 →
        (1 ≤ r*dist z.1.1 z.1.2 ∧ (2*(E+Dq))^2/(r*dist z.1.1 z.1.2) ≤ base^(-κ)) ∧
        (1 ≤ r*dist z.2.1 z.2.2 ∧ (2*(E+Dq))^2/(r*dist z.2.1 z.2.2) ≤ base^(-κ))) →
      let ε := C*(B^K*A⁻¹)^2*base^(-κ*(J:ℝ)+2*(m+3))
      let M := ((descriptorJetBound (m+3) K)^K*A⁻¹)^2*(sphereMeasure (m+3)).real univ
      ‖jetStateOriginalKernel f g w₀ Q ρ profile N σ J₀ i T A A v Ψ z -
        jetStateStationaryKernel f g w₀ Q ρ profile N σ J₀ i T A J ((2:ℝ)^v) Ψ z‖ ≤
        4*W*(ε*(2*M+ε)) := by
  obtain ⟨B,C,hB,hC,hpower⟩ := exists_jetState_far_sphere_power
    hgnomonic hquadratic m J K L hJ hJL
  refine ⟨B,C,hB,hC,?_⟩
  intro F Q ρ profile N σ J₀ i T hF Dq Dmask E A hDq hDm hA hD hscale hE
    f g w₀ v base κ hbase hupper z hregime
  let e := normalizeToSphere w₀ (z.1.1-z.1.2)
  let e' := normalizeToSphere w₀ (z.2.1-z.2.2)
  let Af : ℝ → ℂ := fun r => sphereOscillation (r*dist z.1.1 z.1.2) e
    (fun w => f.value Q ρ profile N σ J₀ i T A z.1.1 w *
      star (f.value Q ρ profile N σ J₀ i T A z.1.2 w))
  let Ag : ℝ → ℂ := fun r => sphereOscillation (r*dist z.2.1 z.2.2) e'
    (fun w => g.value Q ρ profile N σ J₀ i T A z.2.1 w *
      star (g.value Q ρ profile N σ J₀ i T A z.2.2 w))
  let Pf : ℝ → ℂ := fun r => stationarySphereApprox m J (r*dist z.1.1 z.1.2)
    (f.pairAmbient Q ρ profile N σ J₀ i T A z.1.1 z.1.2) e
  let Pg : ℝ → ℂ := fun r => stationarySphereApprox m J (r*dist z.2.1 z.2.2)
    (g.pairAmbient Q ρ profile N σ J₀ i T A z.2.1 z.2.2) e'
  let ε := C*(B^K*A⁻¹)^2*base^(-κ*(J:ℝ)+2*(m+3))
  let M := ((descriptorJetBound (m+3) K)^K*A⁻¹)^2*(sphereMeasure (m+3)).real univ
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hM : 0 ≤ M := mul_nonneg (sq_nonneg _) measureReal_nonneg
  have hfm := state_pair_sphere_measurable f Q ρ profile N σ J₀ i T A z.1.1 z.1.2
  have hgm := state_pair_sphere_measurable g Q ρ profile N σ J₀ i T A z.2.1 z.2.2
  have hAf : Measurable Af := (sphereOscillation_frequency_measurable e _
    hfm).comp (by fun_prop)
  have hAg : Measurable Ag := (sphereOscillation_frequency_measurable e' _
    hgm).comp (by fun_prop)
  have hPf : Measurable Pf := (stationarySphereApprox_frequency_measurable m J _ e).comp (by fun_prop)
  have hPg : Measurable Pg := (stationarySphereApprox_frequency_measurable m J _ e').comp (by fun_prop)
  have herrorf (r : ℝ) (hr : Ψ (r/(2:ℝ)^v) ≠ 0) :=
    hpower F Q ρ profile N σ J₀ i T hF Dq Dmask E A hDq hDm hA hD hscale hE
      f z.1.1 z.1.2 e base (r*dist z.1.1 z.1.2) κ hbase (hregime r hr).1.1
      hupper (hregime r hr).1.2
  have herrorg (r : ℝ) (hr : Ψ (r/(2:ℝ)^v) ≠ 0) :=
    hpower F Q ρ profile N σ J₀ i T hF Dq Dmask E A hDq hDm hA hD hscale hE
      g z.2.1 z.2.2 e' base (r*dist z.2.1 z.2.2) κ hbase (hregime r hr).2.1
      hupper (hregime r hr).2.2
  have h := PlanarFalconer.angular_radial_product_replacement v hΨ hpos hs hW hΨW
    Af Ag Pf Pg hAf hAg hPf hPg (C := M) (ε := ε) hM hε
    (fun r => state_pair_sphere_bound f Q ρ profile N σ J₀ i T hF hA _ _ _ _)
    (fun r => state_pair_sphere_bound g Q ρ profile N σ J₀ i T hF hA _ _ _ _)
    herrorf herrorg
  have hzero (s : ℝ) (hz : s ≤ 0) : Ψ s = 0 := by
    by_contra hn
    have hp := (hs s hn).1
    linarith
  rw [jetStateOriginalKernel_eq_volume f g w₀ Q ρ profile N σ J₀ i T A A v hΨ hpos hzero z]
  simpa only [Af,Ag,Pf,Pg,e,e',ε,M,jetStateStationaryKernel,Complex.real_smul,mul_assoc] using h

end Falconer

end OAI
