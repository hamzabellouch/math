import OAI.MeasureTheory.Falconer.Radial.FarRadialKernel
import OAI.MeasureTheory.Falconer.Fourier.FourStationaryPhases
import OAI.MeasureTheory.Falconer.Fourier.JetStateAntipodal

namespace OAI

/-! # The two actual stationary signs and their radial scaling

The incoming coefficient is the conjugate coefficient of the antipodal
amplitude. Both signs use the original amplitude derivative budget.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def signedStationaryCoefficient (m j : ℕ) (Λ : ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) (outgoing : Bool) : ℂ :=
  if outgoing then normalizedStationaryCoefficient m j Λ B e
  else star (normalizedStationaryCoefficient m j Λ (antipodalConjugate B) e)

theorem signedStationaryCoefficient_bound (m j : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B →
      ∀ C D Λ : ℝ, 0 ≤ C → 1 ≤ D → 0 < Λ → D^2 ≤ Λ →
      (∀ t ≤ 2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t B w‖ ≤ C*D^t) →
      ∀ (e : Sphere (m+3)) (outgoing : Bool),
        ‖signedStationaryCoefficient m j Λ B e outgoing‖ ≤ H*C := by
  obtain ⟨H,hH,hb⟩ := normalizedStationaryCoefficient_bound m j
  refine ⟨H,hH,?_⟩
  intro B hB C D Λ hC hD hΛ hscale hder e outgoing
  cases outgoing with
  | false =>
    simp only [signedStationaryCoefficient,Bool.false_eq_true,ite_false,norm_star]
    apply hb (antipodalConjugate B) (antipodalConjugate_contDiff hB)
      C D Λ hC hD hΛ hscale
    intro t ht w
    rw [antipodalConjugate_derivative_norm]
    exact hder t ht (oppositePole w)
  | true =>
    exact hb B hB C D Λ hC hD hΛ hscale hder e

theorem normalizedStationaryCoefficient_scale (m j : ℕ) (R d s : ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) :
    normalizedStationaryCoefficient m j (R*s*d) B e =
      ((s^j)⁻¹:ℝ)*normalizedStationaryCoefficient m j (R*d) B e := by
  have hp : (R*s*d)^j = s^j*(R*d)^j := by ring
  simp only [normalizedStationaryCoefficient,hp,mul_inv_rev,Complex.ofReal_mul]
  ring

theorem signedStationaryCoefficient_scale (m j : ℕ) (R d s : ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) (outgoing : Bool) :
    signedStationaryCoefficient m j (R*s*d) B e outgoing =
      ((s^j)⁻¹:ℝ)*signedStationaryCoefficient m j (R*d) B e outgoing := by
  cases outgoing <;>
    simp only [signedStationaryCoefficient,Bool.false_eq_true,ite_false,ite_true,
      normalizedStationaryCoefficient_scale,star_mul']
  rw [show star (((s^j)⁻¹:ℝ):ℂ) = (((s^j)⁻¹:ℝ):ℂ) from Complex.conj_ofReal _]

theorem directStationarySum_normalized (m J : ℕ) {Λ : ℝ} (hΛ : 0 < Λ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) :
    directStationarySum m J Λ B e =
      ∑ j ∈ Finset.range J, normalizedStationaryCoefficient m j Λ B e := by
  apply Finset.sum_congr rfl
  intro j _
  simp only [normalizedStationaryCoefficient,Real.rpow_neg hΛ.le,Real.rpow_natCast]

theorem stationarySphereApprox_signed (m J : ℕ) {Λ : ℝ} (hΛ : 0 < Λ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) :
    stationarySphereApprox m J Λ B e =
      ((Λ^(-((m+2:ℕ):ℝ)/2):ℝ):ℂ)*
        (stationaryPhase Λ*(∑ j ∈ Finset.range J, signedStationaryCoefficient m j Λ B e true)+
          stationaryPhase (-Λ)*(∑ j ∈ Finset.range J, signedStationaryCoefficient m j Λ B e false)) := by
  rw [stationarySphereApprox,directStationarySum_normalized m J hΛ,
    directStationarySum_normalized m J hΛ]
  simp only [signedStationaryCoefficient,ite_true,Bool.false_eq_true,ite_false,neg_div]
  change ((Λ^(-(((m+2:ℕ):ℝ)/2)):ℝ):ℂ)*
    (stationaryPhase Λ*_+star (stationaryPhase Λ*_)) = _
  rw [star_mul',stationaryPhase_star,star_sum]

theorem DescriptorJetSymbol.signed_stationary_support {m K L : ℕ}
    {F : Finset PlanarFalconer.PolicyDescriptor} {Dq : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F Dq)
    (Q : DyadicCube (m+3)) (ρ : MeasureTheory.Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere (m+3)))
    (A : ℝ) (x y : Space (m+3)) (w : Sphere (m+3)) (j : ℕ) (Λ : ℝ) (outgoing : Bool)
    (hne : signedStationaryCoefficient m j Λ
      (f.pairAmbient Q ρ profile N σ J i S A x y) w outgoing ≠ 0) :
    ∀ b ∈ F, (x,w) ∈ descriptorEndpointGood Q ρ profile N σ J (i+1) b ∧
      (y,w) ∈ descriptorEndpointGood Q ρ profile N σ J (i+1) b := by
  cases outgoing with
  | false =>
    apply f.pair_incoming_stationary_support Q ρ profile N σ J i S A x y w j
    intro hz
    exact hne (by simp only [signedStationaryCoefficient,Bool.false_eq_true,ite_false,
      normalizedStationaryCoefficient,hz,mul_zero,star_zero])
  | true =>
    apply f.pair_stationary_support Q ρ profile N σ J i S A x y w j
    intro hz
    exact hne (by simp only [signedStationaryCoefficient,ite_true,
      normalizedStationaryCoefficient,hz,mul_zero])

end Falconer

end OAI
