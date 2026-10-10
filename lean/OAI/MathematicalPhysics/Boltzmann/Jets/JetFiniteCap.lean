import OAI.MathematicalPhysics.Boltzmann.Approximation.CapMomentBound
import OAI.MathematicalPhysics.Boltzmann.Branching.HotSeedCoreLower
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicMildApproximation
import OAI.MathematicalPhysics.Boltzmann.Jets.JetCoreMomentBound
import OAI.MathematicalPhysics.Boltzmann.Jets.PeriodicJetFamilies
import OAI.MathematicalPhysics.Boltzmann.Jets.JetContinuation

namespace OAI

section

/-! # The escaped-barrier estimate is uniform over all periodic cells -/

noncomputable section

open Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetCopyDatum BoltzmannNonuniqueness.JetSpatialBox

namespace BoltzmannNonuniqueness.JetEscapedTotal

theorem shifted_cell {x y : Velocity} {m : Lattice}
    (h : JetPeriodicDatum.spatialMap y = JetPeriodicDatum.spatialMap x-displacement m) (n : Lattice) :
    shifted y n = shifted x (n+m) := by
  change JetPeriodicDatum.spatialMap y-displacement n =
    JetPeriodicDatum.spatialMap x-displacement (n+m)
  rw [h,displacement_add]
  abel

theorem annulus_cell {x y : Velocity} {m : Lattice}
    (h : JetPeriodicDatum.spatialMap y = JetPeriodicDatum.spatialMap x-displacement m)
    (η K α γ s d₀ t : ℝ) (v : Velocity) :
    annulus η K α γ s d₀ t y v = annulus η K α γ s d₀ t x v := by
  classical
  unfold annulus
  apply tsum_congr
  intro a
  calc
    _ = ∑' n : Lattice, {n | JetLatticeTail.outside η s t a x n}.indicator
        (fun n => ENNReal.ofReal (JetBarrier.barrier η K α γ s (d₀*s^10) t a (shifted x n,v))) (n+m) := by
      apply tsum_congr
      intro n
      simp only [indicator_apply,mem_ofPred_eq,JetLatticeTail.outside,shifted_cell h n]
    _ = _ := (Equiv.addRight m).tsum_eq _

theorem total_cell {x y : Velocity} {m : Lattice}
    (h : JetPeriodicDatum.spatialMap y = JetPeriodicDatum.spatialMap x-displacement m)
    (s₀ η K α γ d₀ t : ℝ) (v : Velocity) :
    total s₀ η K α γ d₀ t y v = total s₀ η K α γ d₀ t x v := by
  unfold total
  exact tsum_congr (fun j => annulus_cell h η K α γ _ d₀ t v)

theorem arbitrary_power_global {s₀ η K α d₀ t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (m : ℕ) (hm : 31 < 16*m) (γ : ℝ) (x v : Velocity) :
    total s₀ η K α γ d₀ t x v ≤
      ENNReal.ofReal (powerConstant s₀ η α K d₀ m*t^m*Real.exp (-4*‖v‖^2)) := by
  obtain ⟨n,y,hy,he⟩ := exists_shift_in_cell (JetPeriodicDatum.spatialMap x)
  rw [← total_cell he.symm s₀ η K α γ d₀ t v]
  exact arbitrary_power hs₀ hsmax hη hηmax hK hα hαmax hd₀ hdmax ht htmax m hm γ y v hy

end BoltzmannNonuniqueness.JetEscapedTotal

end

end

section

/-! # Uniform escaped-family estimates on the entire periodic covering space -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetSpatialBox
open BoltzmannNonuniqueness.JetLatticeTail

namespace BoltzmannNonuniqueness.JetEscapedEnvelope

theorem arbitrary_power_global {s₀ η K α γ d₀ t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1)
    (hγ : 0 ≤ γ) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1 / 32)
    (hsmall : JetComparisonCoefficient.coefficient K * d₀ * s₀ ^ 9 ≤ 1)
    (m : ℕ) (hm : 31 < 16 * m) (q : ℝ)
    (S : ℕ → Bool → Lattice → Prop) (F : ℕ → Bool → Lattice → ℝ)
    (x v : Velocity)
    (hF : ∀ j a n, S j a n → F j a n ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η j) (d₀ * jetScale s₀ η j ^ 10) t a (shifted x n, v)) :
    escapedSum s₀ η t x S F ≤ ENNReal.ofReal (constant s₀ η α K d₀ m * t ^ m * H q v) := by
  have hp := JetEscapedTotal.powerConstant_nonneg hs₀ hK hd₀ η α m
  have hg : Real.exp (-4 * ‖v‖ ^ 2) ≤ tiltConstant * H q v := by
    apply (Real.exp_le_exp.mpr (show -4 * ‖v‖ ^ 2 ≤ -2 * ‖v‖ ^ 2 by nlinarith [sq_nonneg ‖v‖])).trans
    exact JetGaussianEscape.gaussian_le_hot q v
  calc
    _ ≤ 2 * JetEscapedTotal.total s₀ η K α γ d₀ t x v :=
      sum_le_twice hs₀ hη hK hα hγ hd₀ ht (htmax.trans (by norm_num)) hsmall S F x v hF
    _ ≤ 2 * ENNReal.ofReal (JetEscapedTotal.powerConstant s₀ η α K d₀ m * t ^ m *
        Real.exp (-4 * ‖v‖ ^ 2)) := mul_le_mul' le_rfl (JetEscapedTotal.arbitrary_power_global
          hs₀ hsmax hη hηmax hK hα hαmax hd₀ hd₀max ht htmax m hm γ x v)
    _ = ENNReal.ofReal (2 * (JetEscapedTotal.powerConstant s₀ η α K d₀ m * t ^ m *
        Real.exp (-4 * ‖v‖ ^ 2))) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ 2 * (JetEscapedTotal.powerConstant s₀ η α K d₀ m * t ^ m * (tiltConstant * H q v)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (mul_nonneg hp (pow_nonneg ht.le _)))
            (by norm_num)
        _ = _ := by unfold constant; ring

theorem real_power_global {s₀ η K α γ d₀ t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1)
    (hγ : 0 ≤ γ) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1 / 32)
    (hsmall : JetComparisonCoefficient.coefficient K * d₀ * s₀ ^ 9 ≤ 1) (A q : ℝ)
    (S : ℕ → Bool → Lattice → Prop) (F : ℕ → Bool → Lattice → ℝ)
    (x v : Velocity)
    (hF : ∀ j a n, S j a n → F j a n ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η j) (d₀ * jetScale s₀ η j ^ 10) t a (shifted x n, v)) :
    escapedSum s₀ η t x S F ≤
      ENNReal.ofReal (constant s₀ η α K d₀ (exponent A) * t ^ A * H q v) := by
  apply (arbitrary_power_global hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max ht htmax hsmall
    (exponent A) (exponent_large A) q S F x v hF).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (H_nonneg q v)
  apply mul_le_mul_of_nonneg_left _ (constant_nonneg hs₀ hK hd₀ η α _)
  simpa only [Real.rpow_natCast] using
    Real.rpow_le_rpow_of_exponent_ge ht (htmax.trans (by norm_num)) (le_exponent A)

end BoltzmannNonuniqueness.JetEscapedEnvelope

end

end

section

/-! # Actual finite periodic approximations attaining the hot cap -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_uniform_cap_solution (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1/32 ∧ ∀ (N : ℕ) (b T : ℝ), 0 ≤ b → 0 ≤ T → T ≤ τ →
      ∃ (A ell : ℝ), 0 < A ∧ ell ∈ Icc 0 2 ∧
        (∀ p, initial s₀ η K α γ d₀ q N
          (fun p => ell*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p) p ≤ 2*A) ∧
        ∃ F : PeriodicMildState q b (damping q b A) T (2*A)
          (initial s₀ η K α γ d₀ q N
            (fun p => ell*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p)),
          F.hotPeak (DatumBounds.scale s₀ η (N+1)) (color s₀ η K α γ d₀ q N) = 1 := by
  obtain ⟨τ,hτ,hτmax,hzero⟩ := exists_uniform_zero_solution_large hcarleman hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hwidth hsmall hq₁ hq₂
  refine ⟨τ,hτ,hτmax,?_⟩
  intro N b T hb hT hTτ
  let δ := DatumBounds.scale s₀ η (N+1)
  have hδ : 0 < δ := DatumBounds.scale_pos hs₀ (N+1)
  have hδone : δ ≤ 1 := by
    have he : Real.exp (-((N+1:ℕ):ℝ)*η) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hη.le)
    have hs := mul_le_mul_of_nonneg_left he hs₀.le
    dsimp [δ,DatumBounds.scale]
    nlinarith
  let ψ := HotSeedProfile.normalized q δ
  obtain ⟨M,hM,hψb⟩ := HotSeedProfile.normalized_bounds hδ hδone q
  have hψm : Measurable ψ := HotSeedProfile.normalized_measurable q δ
  have hψnorm : PhaseEssSup.size ψ = δ := HotSeedProfile.normalized_norm hδ hδone q
  let f := seed s₀ η K α γ d₀ q N
  let c₀ := color s₀ η K α γ d₀ q N
  let B := WeightedFiniteSeed.amplitude s₀ η K d₀ N+coldNormBound s₀ η K α d₀ N+T+δ
  let A := B+2*M+1
  have hamp : 0 < WeightedFiniteSeed.amplitude s₀ η K d₀ N :=
    WeightedFiniteSeed.amplitude_pos hs₀ hK hd₀.le η N
  have hcold : 0 ≤ coldNormBound s₀ η K α d₀ N := coldNormBound_nonneg hs₀ hK hd₀ η α N
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hBA : B < A := by dsimp [A]; linarith
  have hA0 : continuationAmplitude s₀ η K α d₀ N ≤ A := by
    dsimp [continuationAmplitude,A,B]
    linarith [hM.le,hδ.le]
  have hR : 0 ≤ 2*A := by positivity
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  have hloss : (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A := le_rfl
  have hseedB (ell) (hell : ell ∈ Icc (0:ℝ) 2) (p) :
      0 ≤ affineSeed f ψ ell p ∧ affineSeed f ψ ell p ≤ A := by
    have hf := seed_bounds hs₀ hsmax hη hηmax hK hd₀ hwidth hα.le hαmax γ q N p
    have hm := mul_le_mul hell.2 (hψb p).2 (hψb p).1 (by norm_num : (0:ℝ) ≤ 2)
    change 0 ≤ f p+ell*ψ p ∧ f p+ell*ψ p ≤ A
    exact ⟨add_nonneg hf.1 (mul_nonneg hell.1 (hψb p).1),by dsimp [A,B,f]; nlinarith [hf.2]⟩
  have hseedR (ell) (hell : ell ∈ Icc (0:ℝ) 2) (p) : affineSeed f ψ ell p ≤ 2*A :=
    (hseedB ell hell p).2.trans (by linarith)
  have hdom (ell) (hell : ell ∈ Icc (0:ℝ) 2) (s : Finset JetLattice.Label) (p) :
      ∑ i ∈ s, c₀ i p ≤ affineSeed f ψ ell p :=
    (initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N
      (fun p => mul_nonneg hell.1 (hψb p).1)).2 s p
  have hc₀ (i) (p) : 0 ≤ c₀ i p ∧ c₀ i p ≤ 2*A := by
    refine ⟨color_nonneg hs₀ hK hd₀.le η α γ q N i p,?_⟩
    simpa only [Finset.sum_singleton] using (hdom 0 ⟨le_rfl,by norm_num⟩ {i} p).trans
      (hseedR 0 ⟨le_rfl,by norm_num⟩ p)
  have hper (ell) (_hell : ell ∈ Icc (0:ℝ) 2) (n) (p) :
      affineSeed f ψ ell (shift (displacement n) p) = affineSeed f ψ ell p := by
    simp only [affineSeed,f,seed_periodic,ψ,HotSeedProfile.normalized_periodic]
  have hzeroCap : ∃ F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ 0),
      hotPeak δ c₀ F < 1 := by
    have hz := hzero N b A T hb hA0 hT hTτ
    have he : (fun _ : JetPrototype.Phase => (0:ℝ)) = (fun p => (0:ℝ)*ψ p) := by funext p; simp
    rw [he] at hz
    obtain ⟨F,hF⟩ := hz
    have hreg := rebuilt_hot_continuous hq₂ hb hL hT hR hloss F.measurable_value
      ((measurable_seed s₀ η K α γ d₀ q N).add (hψm.const_mul 0))
      (measurable_color s₀ η K α γ d₀ q N) F.value_bounds
      (hseedR 0 ⟨le_rfl,by norm_num⟩) hc₀ (hdom 0 ⟨le_rfl,by norm_num⟩) (F.all_mild hT)
    have hp := Cap.peak_le_of_square hT hδ hreg hF
    refine ⟨F,hp.trans_lt ?_⟩
    exact (hTτ.trans hτmax).trans_lt (by norm_num)
  have hlarge (F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ 2)) :
      1 < hotPeak δ c₀ F := by
    have hi := hotPeak_ge_initial hq₂ hb hL hT hR hδ hloss
      ((measurable_seed s₀ η K α γ d₀ q N).add (hψm.const_mul 2))
      (hseedR 2 ⟨by norm_num,le_rfl⟩) (measurable_color s₀ η K α γ d₀ q N)
      hc₀ (hdom 2 ⟨by norm_num,le_rfl⟩) F
    have he : (fun p => affineSeed f ψ 2 p-∑' i, c₀ i p) = (fun p => 2*ψ p) := by
      funext p
      change (∑' i, c₀ i p)+2*ψ p-(∑' i, c₀ i p) = _
      ring
    change PhaseEssSup.size (fun p => affineSeed f ψ 2 p-∑' i, c₀ i p)/δ ≤ hotPeak δ c₀ F at hi
    rw [he,PhaseEssSup.size_const_mul,hψnorm,abs_of_pos (by norm_num : (0:ℝ) < 2)] at hi
    have htwo : (2*δ)/δ = 2 := mul_div_cancel_right₀ _ hδ.ne'
    rw [htwo] at hi
    linarith
  have hbound (ell) (hell : ell ∈ Icc (0:ℝ) 2)
      (F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ ell))
      (hcap : hotPeak δ c₀ F ≤ 1) :
      ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (t,p) ≤ B :=
    capped_total_bound hs₀ hsmax hη hηmax hK hα.le hαmax hγ.le hd₀ hd₀max hwidth hsmall
      hq₂ hb hL hT hR (hTτ.trans hτmax) hδ hloss N (hψm.const_mul ell)
      (fun p => mul_nonneg hell.1 (hψb p).1) (hseedR ell hell) F hcap
  obtain ⟨ell,hell,F,hF⟩ := select_seed_at_cap hq₂ hb hA hT hδ hM.le hBA (by norm_num : (0:ℝ) < 2)
    (measurable_seed s₀ η K α γ d₀ q N) hψm (fun p => by rw [abs_of_nonneg (hψb p).1]; exact (hψb p).2)
    (measurable_color s₀ η K α γ d₀ q N) hc₀ hseedB hdom hper hzeroCap hlarge hbound
  exact ⟨A,ell,hA,hell,hseedR ell hell,F,hF⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
