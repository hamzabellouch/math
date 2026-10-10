import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.BoundedFormCross
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CorrectedStateCoordinates

namespace OAI

/-! The mixed form of an actual corrected-orbital state is the finite sum
of its orbital residual pairings against the complementary state. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem corrected_potential_pairing {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) (V : Configuration 1 → ℝ)
    (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (v : Coulomb.H1Vector 1) (s : SpinConfiguration 1) :
    inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
      (correctedLocalizedMode_memLp hfreq u i))
      (BoundedPotential.operator V hV B hB (h1Coordinates v (Sum.inl s))) =
      ∫ x, v.value s x*(V x*oneElectronCorrectedMode freq u i x : ℝ) := by
  have hm : MemLp (fun x : Configuration 1 => (oneElectronCorrectedMode freq u i x : ℂ)) 2 :=
    (oneElectronCorrectedMode_memLp hfreq u i).ofReal
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hm.coeFn_toLp,
    BoundedPotential.operator_ae V hV B hB (h1Coordinates v (Sum.inl s)),
    (h1Coordinate_memLp v (Sum.inl s)).coeFn_toLp] with x hp hA hv
  change oneElectronOrbitalLp (correctedLocalizedMode freq u i)
    (correctedLocalizedMode_memLp hfreq u i) x = (oneElectronCorrectedMode freq u i x : ℂ) at hp
  change h1Coordinates v (Sum.inl s) x = v.value s x at hv
  rw [hA,hp,hv,RCLike.inner_apply]
  simp only [Complex.conj_ofReal,Complex.ofReal_mul]
  ring

theorem corrected_complex_cross_expansion {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (c : SpinConfiguration 1 → Fin m → ℂ)
    (V : Configuration 1 → ℝ) (hV : Continuous V) (B E : ℝ) (hB : ∀ x, |V x| ≤ B)
    (v : Coulomb.H1Vector 1) :
    graphComplexCross (BoundedPotential.operator V hV B hB)
      (h1Coordinates (correctedOneElectronState hfreq u c)) (h1Coordinates v) =
      ∑ s, ∑ i, (starRingEnd ℂ) (c s i)*
        (realOrbitalPairing V E (oneElectronCorrectedMode freq u i) v s+
          (E:ℂ)*inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
            (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v (Sum.inl s))) := by
  have hd (s : SpinConfiguration 1) (i : Fin m) (a : Fin 1 × Fin 3) :
      inner ℂ (correctedPartialLp hfreq u i a) (h1Coordinates v (Sum.inr (s,a))) =
      ∫ x, v.gradient s a x*(configurationRealPartial (oneElectronCorrectedMode freq u i) a x : ℂ) :=
    h1_inner_real_coordinate v (Sum.inr (s,a)) _ (oneElectronCorrectedMode_partial_memLp hfreq u i a)
  have hv (s : SpinConfiguration 1) (i : Fin m) :
      inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
        (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v (Sum.inl s)) =
      ∫ x, v.value s x*(oneElectronCorrectedMode freq u i x : ℂ) :=
    oneElectron_inner_real_orbital v s _ (correctedLocalizedMode_memLp hfreq u i)
  have hp (s : SpinConfiguration 1) (i : Fin m) :
      realOrbitalPairing V E (oneElectronCorrectedMode freq u i) v s+
        (E:ℂ)*inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
          (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v (Sum.inl s)) =
      (1/2:ℂ)*(∑ a, inner ℂ (correctedPartialLp hfreq u i a) (h1Coordinates v (Sum.inr (s,a))))+
        inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
          (correctedLocalizedMode_memLp hfreq u i))
          (BoundedPotential.operator V hV B hB (h1Coordinates v (Sum.inl s))) := by
    simp only [realOrbitalPairing,hd,hv,corrected_potential_pairing hfreq u i V hV B hB]
    ring
  simp_rw [hp]
  unfold graphComplexCross
  simp_rw [correctedOneElectronState_gradient_coordinate,correctedOneElectronState_coordinate,
    sum_inner,inner_smul_left]
  have hk (s : SpinConfiguration 1) :
      (∑ a : Fin 1 × Fin 3, ∑ i, (starRingEnd ℂ) (c s i)*
        inner ℂ (correctedPartialLp hfreq u i a) (h1Coordinates v (Sum.inr (s,a)))) =
      ∑ i, (starRingEnd ℂ) (c s i)*
        ∑ a, inner ℂ (correctedPartialLp hfreq u i a) (h1Coordinates v (Sum.inr (s,a))) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  simp_rw [hk]
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem corrected_complex_cross_orthogonal {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (c : SpinConfiguration 1 → Fin m → ℂ)
    (V : Configuration 1 → ℝ) (hV : Continuous V) (B E : ℝ) (hB : ∀ x, |V x| ≤ B)
    (v : Coulomb.H1Vector 1)
    (ho : ∀ s i, inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
      (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v (Sum.inl s)) = 0) :
    graphComplexCross (BoundedPotential.operator V hV B hB)
      (h1Coordinates (correctedOneElectronState hfreq u c)) (h1Coordinates v) =
      ∑ s, ∑ i, (starRingEnd ℂ) (c s i)*realOrbitalPairing V E (oneElectronCorrectedMode freq u i) v s := by
  rw [corrected_complex_cross_expansion hfreq u c V hV B E hB v]
  simp only [ho,mul_zero,add_zero]

end ContinuumCoulomb

end

end OAI
