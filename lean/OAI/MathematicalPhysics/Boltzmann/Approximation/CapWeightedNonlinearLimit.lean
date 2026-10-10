import OAI.MathematicalPhysics.Boltzmann.Branching.ProductKineticCutoff
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetStability
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalMomentIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairPatchIdentity

namespace OAI

section

/-! # Identification of the actual cap-family weak pair limit -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum

/-- The velocity-averaging step identifies the genuine nonlinear pair product. -/
theorem TightCapFamily.exists_nonlinear_weak_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairProduct
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairProduct g) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ g z) := by
  obtain ⟨ψ,hψ,hψc,hdet⟩ := Compactness.exists_countable_smooth_determining_tests
  choose β hβ hβc _hβn hβtest using fun i => Compactness.exists_velocity_cutoff (hψc i)
  obtain ⟨χ,hχ,hχc,hχs,hcover⟩ := Compactness.exists_spacetime_cutoff_cover
    TorusKineticChart.interiorRegion_open TorusKineticChart.interiorRegion_nonempty
  let cuts : ℕ → Published.KineticPhase → ℝ := fun n =>
    Compactness.productCutoff (χ (Nat.unpair n).1) (β (Nat.unpair n).2)
  let tests : ℕ → Velocity → ℝ := fun n => ψ (Nat.unpair n).2
  have hcuts (n) : ContDiff ℝ (⊤ : ℕ∞) (cuts n) :=
    Compactness.productCutoff_smooth (hχ _) (hβ _)
  have hcutsc (n) : HasCompactSupport (cuts n) :=
    Compactness.productCutoff_compact (hχc _) (hβc _)
  have hcutss (n) : tsupport (cuts n) ⊆ {z | z.1.2 ∈ TorusChart.cube} :=
    Compactness.productCutoff_in_cell _ (hχs _)
  have hcuts0 (n) (p : Velocity × Velocity) : cuts n (TransportCutoff.characteristic p 0) = 0 :=
    Compactness.productCutoff_initial_zero _ (hχs _) p
  obtain ⟨φ,g,W,hφ,hg,hW,hmom,hgn,_hWn⟩ := F.exists_factorized_pair_moments
    hcarleman hGLPS hDP hq₁ hq₂ cuts hcuts hcutsc hcutss hcuts0 tests
    (fun n => hψ _) (fun n => hψc _)
  have hw (s i : ℕ) : averageWeight (cuts (Nat.pair s i)) (tests (Nat.pair s i)) =
      fun z => χ s z.1*ψ i z.2 := by
    dsimp only [cuts,tests]
    rw [Nat.unpair_pair]
    exact Compactness.productCutoff_preserves_test (χ s) (hβtest i)
  have hgw := TorusKineticChart.weak_density_transfer
    (fun n => (F.approximation (φ n)).solution.measurable_value) hg
  have hWw := TorusKineticChart.weak_pair_transfer
    (fun n => (F.approximation (φ n)).solution.measurable_value) hW
  have hscaled (s i j : ℕ) : ∀ᵐ x ∂TorusKineticChart.baseVolume F.time,
      (∫ y : Velocity × Velocity, ((χ s x*ψ i y.1)*(χ s x*ψ j y.2))*TorusKineticChart.liftPair W (x,y)) =
        (∫ v, (χ s x*ψ i v)*TorusKineticChart.liftDensity g (x,v))*
          (∫ w, (χ s x*ψ j w)*TorusKineticChart.liftDensity g (x,w)) := by
    apply Compactness.ae_of_all_compact_restrict
    intro S hS
    have ht := hmom (Nat.pair s i) (Nat.pair s j) S hS
    simp only [hw s i,hw s j] at ht
    filter_upwards [ht] with x hx
    exact hx
  have hpatch (s) : ∀ᵐ x ∂TorusKineticChart.baseVolume F.time, χ s x ≠ 0 →
      (fun y => TorusKineticChart.liftPair W (x,y)) =ᵐ[volume]
        (fun y : Velocity × Velocity => TorusKineticChart.liftDensity g (x,y.1)*
          TorusKineticChart.liftDensity g (x,y.2)) := by
    apply Compactness.pair_identity_on_patch hψ hψc hdet hWw.1 hgw.1 hWw.2.1 hgw.2.1 (χ s)
    exact fun i j => (hscaled s i j).mono (fun _ h _ => h)
  have hfib : ∀ᵐ x ∂TorusKineticChart.baseVolume F.time,
      (fun y => TorusKineticChart.liftPair W (x,y)) =ᵐ[volume]
        (fun y : Velocity × Velocity => TorusKineticChart.liftDensity g (x,y.1)*
          TorusKineticChart.liftDensity g (x,y.2)) := by
    filter_upwards [ae_all_iff.mpr hpatch,TorusKineticChart.interiorRegion_ae F.time] with x hx hxin
    obtain ⟨s,hs⟩ := hcover x hxin
    exact hx s hs
  have he : TorusKineticChart.liftPair W =ᵐ[TorusKineticChart.pairCellVolume F.time]
      CollisionCompactness.pairProduct (TorusKineticChart.liftDensity g) := by
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr hfib
    exact measurableSet_eq_fun hWw.1 (CollisionCompactness.pairProduct_measurable hgw.1)
  have hback := (TorusKineticChart.pair_measurePreserving F.time).quasiMeasurePreserving.ae he
  have hEq : W =ᵐ[(AnnularEnvelope.timePositionVolume F.time).prod volume]
      CollisionCompactness.pairProduct g := by
    filter_upwards [hback] with z hz
    simpa only [TorusKineticChart.liftPair,TorusKineticChart.pairChart,
      CollisionCompactness.pairProduct,TorusKineticChart.liftDensity,
      TorusChart.projection_representative] using hz
  refine ⟨φ,g,hφ,hg,?_,hgn⟩
  refine ⟨CollisionCompactness.pairProduct_measurable hg.1,hW.2.1.congr hEq,?_⟩
  intro θ hθ hθB
  have ht := hW.2.2 θ hθ hθB
  have hi : (∫ z, θ z*W z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume) =
      ∫ z, θ z*CollisionCompactness.pairProduct g z
        ∂(AnnularEnvelope.timePositionVolume F.time).prod volume :=
    integral_congr_ae (hEq.mono (fun z hz => congrArg (fun y => θ z*y) hz))
  rw [hi] at ht
  exact ht

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The physical pair weight also converges to the genuine nonlinear product -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.exists_weighted_nonlinear_weak_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairDensity g) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ g z) := by
  obtain ⟨a,g,ha,hg,hraw,hgn⟩ := F.exists_nonlinear_weak_limit hcarleman hGLPS hDP hq₁ hq₂
  have hm (n) := CollisionCompactness.pairDensity_measurable
    (torusPhysical_measurable (F.approximation (a n)).solution.measurable_value q)
  obtain ⟨b,G,hb,hG⟩ := (hDP F.time F.time_pos.le).2
    (fun n => CollisionCompactness.pairDensity (torusPhysical q (F.approximation (a n)).solution.value))
    hm (Compactness.uniformIntegrable_comp F.pairs_ui a) (F.pairs_tight.comp a)
  let w : (ℝ × Position) × (Velocity × Velocity) → ℝ := fun z => 1+‖z.2.1‖+‖z.2.2‖
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hw1 : ∀ z, 1 ≤ w z := by
    intro z
    dsimp [w]
    linarith [norm_nonneg z.2.1,norm_nonneg z.2.2]
  have hfun (u : (ℝ × Position) × Velocity → ℝ) :
      (fun z => w z*CollisionCompactness.pairProduct u z) = CollisionCompactness.pairDensity u := by
    funext z
    simp only [w,CollisionCompactness.pairProduct,CollisionCompactness.pairDensity,mul_assoc]
  have hraw' := hraw.comp hb.tendsto_atTop
  have hG' : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
      (fun n z => w z*CollisionCompactness.pairProduct
        (torusPhysical q (F.approximation (a (b n))).solution.value) z) G := by
    have hseq : (fun n z => w z*CollisionCompactness.pairProduct
        (torusPhysical q (F.approximation (a (b n))).solution.value) z) =
        (fun n => CollisionCompactness.pairDensity (torusPhysical q
          (F.approximation (a (b n))).solution.value)) := funext (fun n => hfun _)
    rw [hseq]
    exact hG
  have he := Published.identify_weighted_weak_limit hraw' hG' hw hw1
  have he' : G =ᵐ[(AnnularEnvelope.timePositionVolume F.time).prod volume]
      CollisionCompactness.pairDensity g := by
    rw [hfun] at he
    exact he
  exact ⟨a ∘ b,g,ha.comp hb,hg.comp hb.tendsto_atTop,
    hG.congr_limit (CollisionCompactness.pairDensity_measurable hg.1) he',hgn⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
