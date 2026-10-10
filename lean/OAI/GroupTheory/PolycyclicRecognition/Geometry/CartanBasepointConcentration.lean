import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBasepointAffineComparison
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordBallSamplingSequence
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactSamplingMean

namespace OAI

/-! # Basepoint comparison from the established concentration estimates -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module MeasureTheory Filter Set Metric
open scoped Manifold Topology ENNReal

variable {EG G W I L P : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [Fintype I] [DecidableEq I] [Finite L] [Nonempty L]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  [IsTopologicalGroup F.N.carrier] [IsTopologicalGroup F.D.carrier]
  [SecondCountableTopology F.N.carrier]

/-- The deterministic conclusion of the basepoint argument, keeping the
already proved sampling geometry and concentration estimates separate. -/
theorem nearby_labels_of_concentration
    (hD : Continuous F.ExpD)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ v, chartD v = F.ExpD v)
    (π : G →* Multiplicative W) (height : H →ₗ[ℝ] W)
    (hheight : Function.Surjective height)
    (hchartheight : ∀ v, (π (F.inclusionD (chartD (F.D.equiv v)))).toAdd = height v)
    (hkill : ∀ u v : H, height ⁅u, v⁆ = 0)
    (A : L → W →L[ℝ] W) (hA : Function.Injective A)
    (J : P → G → W) (hJ : ∀ p, Continuous (J p))
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    {ρ R η t : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hρR : ρ ≤ R) (ht : 0 < t)
    (μ : ℝ → ProbabilityMeasure F.N.carrier) (B : ℝ → Set F.N.carrier)
    (hne : ∀ r, (B r).Nonempty) {D : ℝ≥0∞} (hDfinite : D ≠ ∞)
    (C : ℝ → Set F.N.carrier) (hcompact : ∀ r, IsCompact (C r))
    (hfull : ∀ r, ∀ᵐ z ∂(μ r : Measure F.N.carrier), z ∈ C r)
    (hgeometry : ∀ scale : ℕ → ℝ, Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
      ∀ᶠ n in atTop, ∀ g : G, dist 1 g ≤ η * scale n →
      ∃ (u : F.N.carrier) (k : F.D.carrier) (ν : ProbabilityMeasure F.N.carrier),
        F.inclusionN u * F.inclusionD k = g ∧
        (π (F.inclusionD k)).toAdd = (π g).toAdd ∧
        (∀ᵐ a ∂(ν : Measure F.N.carrier), a ∈ B (t * scale n)) ∧
        (∀ U : Set F.N.carrier, MeasurableSet U →
          (μ (scale n) : Measure F.N.carrier) ((fun a => F.action k⁻¹ (u⁻¹ * a)) ⁻¹' U) ≤
            D * (μ (t * scale n) : Measure F.N.carrier).prod (ν : Measure F.N.carrier)
              {p | p.1 * p.2 ∈ U}) ∧
        ∀ z : Fin (finrank ℝ H) → ℝ, ‖z‖ ≤ ρ →
          ‖wordChartLeftShift F.D.equiv chartD
            (exponentialRescaleBasis (WordBasisSelections.basis X S β)
              (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log (scale n)))
            (exponentialRescaleBasis (WordBasisSelections.basis X S β)
              (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log (t * scale n)))
            k z‖ ≤ R) :
    let Z := closedBall (0 : Fin (finrank ℝ H) → ℝ) R
    let q := (height.comp (WordBasisSelections.basis X S β).equivFun.symm.toLinearMap).toContinuousLinearMap
    let raw := fun (p : P × G) r => F.realScaleProfile hD (J p.1) (hJ p.1) p.2 X S β r
    let b := fun p r => ∫ k, raw p r k 0 ∂(μ r : Measure F.N.carrier)
    let label := fun p r => canonicalAffineLabel (μ r : Measure F.N.carrier)
      (fun k => (raw p r k).restrict Z)
      (fun l => linearBallProfile q (A l) R + ContinuousMap.const Z (b p r))
    (∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
      (∀ n, 1 ≤ scale n) → ∀ (p : ℕ → P) (x : ℕ → G),
      ∃ a : ℕ → L, Tendsto (fun n => ∫ k, dist ((raw (p n, x n) (scale n) k).restrict Z)
        (linearBallProfile q (A (a n)) R + ContinuousMap.const Z (b (p n, x n) (scale n)))
          ∂(μ (scale n) : Measure F.N.carrier)) atTop (𝓝 0)) →
    (∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, ∀ p r, r₀ ≤ r → ‖b p r‖ ≤ ε) →
    (∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
      (∀ n, 1 ≤ scale n) → ∀ (p : ℕ → P) (x : ℕ → G) (k : ℕ → F.N.carrier),
      (∀ n, k n ∈ B (scale n)) → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (μ (scale n) : Measure F.N.carrier)
        {z | ε ≤ dist ((raw (p n, x n) (scale n) (z * k n)).restrict Z)
          ((raw (p n, x n) (scale n) z).restrict Z)}) atTop (𝓝 0)) →
    ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
      (∀ n, 1 ≤ scale n) → (∀ n, 1 ≤ t * scale n) →
      ∀ (p : ℕ → P) (x y : ℕ → G), (∀ n, dist (x n) (y n) ≤ η * scale n) →
      (∀ᶠ n in atTop, label (p n, x n) (scale n) = label (p n, y n) (t * scale n)) ∧
      Tendsto (fun n => (scale n)⁻¹ • (J (p n) (y n) - J (p n) (x n) -
        A (label (p n, y n) (t * scale n)) ((π ((x n)⁻¹ * y n)).toAdd))) atTop (𝓝 0) := by
  classical
  let : Fintype L := Fintype.ofFinite L
  dsimp only
  intro hmean huniform hsuffix scale hscale hstrict hscale1 hsmall1 pair x y hxy
  let Z := closedBall (0 : Fin (finrank ℝ H) → ℝ) R
  let bD := WordBasisSelections.basis X S β
  let q := (height.comp bD.equivFun.symm.toLinearMap).toContinuousLinearMap
  let raw := fun (p : P × G) r => F.realScaleProfile hD (J p.1) (hJ p.1) p.2 X S β r
  let b := fun p r => ∫ k, raw p r k 0 ∂(μ r : Measure F.N.carrier)
  let label := fun p r => canonicalAffineLabel (μ r : Measure F.N.carrier)
    (fun k => (raw p r k).restrict Z)
    (fun l => linearBallProfile q (A l) R + ContinuousMap.const Z (b p r))
  let small := fun n => t * scale n
  have hsmall : Tendsto small atTop atTop := hscale.const_mul_atTop ht
  have hsmallstrict : StrictMono small := fun i j hij => mul_lt_mul_of_pos_left (hstrict hij) ht
  let ξ := fun n => μ (scale n)
  let μ' := fun n => μ (small n)
  let suffixBox := fun n => B (small n)
  let test :=  fun n (u : F.N.carrier) (k : F.D.carrier) (ν : ProbabilityMeasure F.N.carrier) =>
    F.inclusionN u * F.inclusionD k = (x n)⁻¹ * y n ∧
    (π (F.inclusionD k)).toAdd = (π ((x n)⁻¹ * y n)).toAdd ∧
    (∀ᵐ z ∂(ν : Measure F.N.carrier), z ∈ suffixBox n) ∧
    (∀ U : Set F.N.carrier, MeasurableSet U →
      (ξ n : Measure F.N.carrier) ((fun a => F.action k⁻¹ (u⁻¹ * a)) ⁻¹' U) ≤
        (D) *
          (μ' n : Measure F.N.carrier).prod (ν : Measure F.N.carrier) {p | p.1 * p.2 ∈ U})
  let source := fun n => exponentialRescaleBasis bD
    (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log (scale n))
  let target := fun n => exponentialRescaleBasis bD
    (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log (small n))
  have hdata : ∀ᶠ n in atTop, ∃ (u : F.N.carrier) (k : F.D.carrier)
      (ν : ProbabilityMeasure F.N.carrier), test n u k ν ∧
      ∀ z : Fin (finrank ℝ H) → ℝ, ‖z‖ ≤ ρ →
        ‖wordChartLeftShift F.D.equiv chartD (source n) (target n) k z‖ ≤ R := by
    filter_upwards [hgeometry scale hscale hscale1] with n hn
    have hg : dist 1 ((x n)⁻¹ * y n) ≤ η * scale n := by
      have he := dist_mul_left ((x n)⁻¹) (x n) (y n)
      calc
        dist 1 ((x n)⁻¹ * y n) = dist (x n) (y n) := by
          simpa only [inv_mul_cancel] using he
        _ ≤ η * scale n := hxy n
    obtain ⟨u, k, ν, hf, hh, hν, hdom, hchart⟩ := hn ((x n)⁻¹ * y n) hg
    exact ⟨u, k, ν, ⟨hf, hh, hν, hdom⟩,
      fun z hz => hchart z hz⟩
  obtain ⟨u, k, ν, φ, hselected⟩ := exists_wordBall_sampling_sequence F.D.equiv chartD
    source target hR.le test hdata
  have hfactor : ∀ᶠ n in atTop, y n = x n * (F.inclusionN (u n) * F.inclusionD (k n)) := by
    filter_upwards [hselected] with n hn
    rw [hn.1.1, mul_inv_cancel_left]
  have hkheight : ∀ᶠ n in atTop,
      (π (F.inclusionD (k n))).toAdd = (π ((x n)⁻¹ * y n)).toAdd :=
    hselected.mono (fun _ hn => hn.1.2.1)
  have hdom : ∀ᶠ n in atTop, ∀ U : Set F.N.carrier, MeasurableSet U →
      (ξ n : Measure F.N.carrier) ((fun a => F.action (k n)⁻¹ ((u n)⁻¹ * a)) ⁻¹' U) ≤
        (D) *
          (μ' n : Measure F.N.carrier).prod (ν n : Measure F.N.carrier) {p | p.1 * p.2 ∈ U} :=
    hselected.mono (fun _ hn => hn.1.2.2.2)
  have hchart := hselected.mono (fun _ hn => hn.2)
  have hmean' (s : ℕ → ℝ) (hs : Tendsto s atTop atTop) (hsm : StrictMono s)
      (hs1 : ∀ n, 1 ≤ s n) (z : ℕ → G) :
      Tendsto (fun n => ∫ w, dist ((raw (pair n, z n) (s n) w).restrict Z)
        (linearBallProfile q (A (label (pair n, z n) (s n))) R +
          ContinuousMap.const Z (b (pair n, z n) (s n))) ∂(μ (s n) : Measure F.N.carrier))
        atTop (𝓝 0) := by
    exact canonicalAffineLabel_mean_tendsto_zero (fun n => (μ (s n) : Measure F.N.carrier))
      (fun n w => (raw (pair n, z n) (s n) w).restrict Z)
      (fun n l => linearBallProfile q (A l) R + ContinuousMap.const Z (b (pair n, z n) (s n)))
      (hmean s hs hsm hs1 pair z)

  have hprob (s : ℕ → ℝ) (hs : Tendsto s atTop atTop) (hsm : StrictMono s)
      (hs1 : ∀ n, 1 ≤ s n) (z : ℕ → G) (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n => (μ (s n) : Measure F.N.carrier)
        {w | ε ≤ dist ((raw (pair n, z n) (s n) w).restrict Z)
          (linearBallProfile q (A (label (pair n, z n) (s n))) R +
            ContinuousMap.const Z (b (pair n, z n) (s n)))}) atTop (𝓝 0) := by
    exact compact_profile_probability_of_mean (fun n => μ (s n)) _
      (fun n => hcompact (s n)) (fun n => hfull (s n)) _ (fun n => F.continuous_realScaleProfile_restrict
        hD (J (pair n)) (hJ _) (z n)
        X S β (s n) Z) _ (hmean' s hs hsm hs1 z) hε
  have hb (s : ℕ → ℝ) (hs : Tendsto s atTop atTop) (z : ℕ → G) :
      Tendsto (fun n => b (pair n, z n) (s n)) atTop (𝓝 0) := by
    have hv := huniform
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨S, hS⟩ := hv (ε / 2) (half_pos hε)
    filter_upwards [hs.eventually_ge_atTop S] with n hn
    exact lt_of_le_of_lt (by simpa only [dist_zero_right] using hS (pair n, z n) (s n) hn)
      (half_lt_self hε)
  have hsource : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (ξ n : Measure F.N.carrier)
      {z | ε ≤ dist (linearBallProfile q (A (label (pair n, x n) (scale n))) ρ +
        ContinuousMap.const _ (b (pair n, x n) (scale n)))
        ((raw (pair n, x n) (scale n) z).restrict (Metric.closedBall 0 ρ))}) atTop (𝓝 0) := by
    apply bad_probability_tendsto_zero_of_dist_le (fun n => (ξ n : Measure F.N.carrier))
      (fun n z => (raw (pair n, x n) (scale n) z).restrict Z)
      (fun n _ => linearBallProfile q (A (label (pair n, x n) (scale n))) R +
        ContinuousMap.const Z (b (pair n, x n) (scale n)))
      _ _ zero_lt_one
    · intro n z
      rw [one_mul, dist_comm]
      apply (ContinuousMap.dist_le dist_nonneg).mpr
      intro w
      let w' : Z := ⟨w, (Metric.closedBall_subset_closedBall hρR) w.property⟩
      exact ((raw (pair n, x n) (scale n) z).restrict Z).dist_apply_le_dist
        (g := linearBallProfile q (A (label (pair n, x n) (scale n))) R +
          ContinuousMap.const Z (b (pair n, x n) (scale n))) w'
    · exact hprob scale hscale hstrict hscale1 x
  have hsuffix' : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ' n : Measure F.N.carrier).prod (ν n : Measure F.N.carrier)
        {p | ε ≤ dist ((raw (pair n, y n) (small n) (p.1 * p.2)).restrict Z)
          ((raw (pair n, y n) (small n) p.1).restrict Z)}) atTop (𝓝 0) := by
    intro ε hε
    apply independent_eventually_supported_bad_probability_tendsto_zero μ' ν suffixBox
    · exact fun n => hne (small n)
    · exact hselected.mono (fun _ hn => hn.1.2.2.1)
    · intro n
      have hp := F.continuous_realScaleProfile_restrict hD
        (J (pair n)) (hJ _) (y n) X S β (small n) Z
      exact (isClosed_Ici.preimage ((hp.comp (continuous_fst.mul continuous_snd)).dist
        (hp.comp continuous_fst))).measurableSet
    · intro z hz
      exact hsuffix small hsmall hsmallstrict hsmall1 pair y z hz ε hε

  exact F.basepoint_affine_labels_of_sampling hD
    chartD hchartD π height hheight hchartheight hkill A hA X S β
    hρ hR ht scale hscale1 (Eventually.of_forall hsmall1) (fun n => J (pair n))
    (fun n => hJ _) x y u k hfactor hkheight φ hchart ξ μ' ν hDfinite hdom
    (fun n => label (pair n, x n) (scale n)) (fun n => label (pair n, y n) (small n))
    (fun n => b (pair n, x n) (scale n)) (fun n => b (pair n, y n) (small n))
    (hb scale hscale x) (hb small hsmall y) hsource
    (hprob small hsmall hsmallstrict hsmall1 y) hsuffix'

end PolycyclicRecognition.CartanFactorModel

end

end OAI
