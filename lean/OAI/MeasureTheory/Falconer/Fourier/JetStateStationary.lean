import OAI.MeasureTheory.Falconer.Fourier.JetStateAmbient
import OAI.MeasureTheory.Falconer.Shells.DistanceInverse

namespace OAI

/-! # Actual stationary amplitudes retain every old descriptor

The far expansion uses these internal endpoint pairs before any reached
mask is removed. Locality of the stationary operator preserves the old
support tests, also for already differentiated masks.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {Dq : ℝ}

 theorem ambient_eventually_zero (f : DescriptorJetSymbol n K L F Dq)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x : Space (n+2)) (w : Sphere (n+2))
    {b : PolicyDescriptor} (hb : b ∈ F)
    (hbad : (x,w) ∉ descriptorEndpointGood Q ρ m N σ J (i+1) b) :
    f.ambient Q ρ m N σ J i S A x =ᶠ[𝓝 (w:Space (n+2))] 0 := by
  have hnot : (w:Space (n+2)) ∉ tsupport (descriptorAmbientMask Q ρ m N σ J i b (S b) x) :=
    fun h => hbad (descriptorAmbientMask_tsupport_good Q ρ m N σ J i b (S b) x w h)
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hnot).iteratedFDeriv (𝕜 := ℝ) (f.jet b).order
  filter_upwards [hz] with z hz
  have hj : normalizedAmbientDescriptorJet Q ρ m N σ J i b (S b)
      (f.jet b).order (f.jet b).vectors x z = 0 := by
    simp only [normalizedAmbientDescriptorJet,hz,iteratedFDeriv_zero,Pi.zero_apply,zero_apply,mul_zero]
  have hp : (∏ c ∈ F, normalizedAmbientDescriptorJet Q ρ m N σ J i c (S c)
      (f.jet c).order (f.jet c).vectors x z) = 0 := Finset.prod_eq_zero hb hj
  simp only [ambient,hp,Complex.ofReal_zero,zero_mul,mul_zero,Pi.zero_apply]

noncomputable def pairAmbient (f : DescriptorJetSymbol n K L F Dq)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x y z : Space (n+2)) : ℂ :=
  f.ambient Q ρ m N σ J i S A x z * star (f.ambient Q ρ m N σ J i S A y z)

 theorem pairAmbient_smooth (f : DescriptorJetSymbol n K L F Dq)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x y : Space (n+2)) :
    ContDiff ℝ ∞ (f.pairAmbient Q ρ m N σ J i S A x y) :=
  (f.ambient_smooth Q ρ m N σ J i S A x).mul
    (Complex.conjCLE.contDiff.comp (f.ambient_smooth Q ρ m N σ J i S A y))

 theorem pairAmbient_sphere (f : DescriptorJetSymbol n K L F Dq)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x y : Space (n+2)) (w : Sphere (n+2)) :
    f.pairAmbient Q ρ m N σ J i S A x y w =
      f.value Q ρ m N σ J i S A x w*star (f.value Q ρ m N σ J i S A y w) := by
  simp only [pairAmbient,ambient_sphere]

 theorem pair_stationary_support {m₀ : ℕ}
    (f : DescriptorJetSymbol (m₀+1) K L F Dq)
    (Q : DyadicCube (m₀+3)) (ρ : Measure (Space (m₀+3))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m₀+3)))
    (A : ℝ) (x y : Space (m₀+3)) (w : Sphere (m₀+3)) (j : ℕ)
    (hne : actualStationaryCoefficient m₀ j (f.pairAmbient Q ρ m N σ J i S A x y) w ≠ 0) :
    ∀ b ∈ F, (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b ∧
      (y,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  intro b hb
  constructor
  · by_contra hbad
    have hz := f.ambient_eventually_zero Q ρ m N σ J i S A x w hb hbad
    have he : f.pairAmbient Q ρ m N σ J i S A x y =ᶠ[𝓝 (w:Space (m₀+3))] 0 := by
      filter_upwards [hz] with z hz
      simp only [pairAmbient,hz,Pi.zero_apply,zero_mul]
    have hlocal := actualStationaryCoefficient_local m₀ j w he
    exact hne (hlocal.trans (actualStationaryCoefficient_zero_amplitude m₀ j w))
  · by_contra hbad
    have hz := f.ambient_eventually_zero Q ρ m N σ J i S A y w hb hbad
    have he : f.pairAmbient Q ρ m N σ J i S A x y =ᶠ[𝓝 (w:Space (m₀+3))] 0 := by
      filter_upwards [hz] with z hz
      simp only [pairAmbient,hz,Pi.zero_apply,star_zero,mul_zero]
    have hlocal := actualStationaryCoefficient_local m₀ j w he
    exact hne (hlocal.trans (actualStationaryCoefficient_zero_amplitude m₀ j w))

end DescriptorJetSymbol
end Falconer

end OAI
