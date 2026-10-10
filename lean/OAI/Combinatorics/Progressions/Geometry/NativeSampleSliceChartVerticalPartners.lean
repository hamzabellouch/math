import OAI.Combinatorics.Progressions.Probability.NativeSliceLawVerticalPartners

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators Classical

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

theorem exists_nativeSample_slice_chart_vertical_partners
    {Ω Pivot K σ X LG : Type*} [Fintype Ω] [Fintype Pivot] [Fintype K] [DecidableEq K]
    [LieRing LG] [LieAlgebra ℚ LG]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d : ℕ} (D : RationalFilteredNilmanifold LG s d)
    {w : σ → ℕ} {pNative : ℝ} (sample : X → σ → ℤ)
    (nativeValue : Pivot → X → ℂ)
    (native : ∀ j, NativeSampleModel w s pNative sample (nativeValue j))
    (P : Ω → Pivot → D.Niltest (fun _ : K => 1))
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    {N : K → ℕ} (stride : Ω → Pivot → ℕ)
    (S : ∀ a j, ResidueBoxSlice N (stride a j))
    (hstride : ∀ a ∈ H, ∀ j, 0 < stride a j)
    (hlen : ∀ a j i, 0 < (S a j).length i)
    (physical : Ω → integerBox N → X)
    (β : Ω → σ → MvPolynomial K ℤ)
    (hβ : ∀ a i, integerSampledRealChart (β a) i ∈
      weightedSupportLE (fun _ : K => 1) (w i))
    (hsample : ∀ a ∈ H, ∀ j (t : integerBox N), t.val ∈ (S a j).integerPoints →
      sample (physical a t) = fun i => MvPolynomial.eval t.val (β a i))
    (twist : Ω → Pivot → integerBox N → ℂ)
    {pLocal r q : ℝ} (hpLocal : 0 ≤ pLocal) (hr : 0 ≤ r) (hpq : pNative ≤ q)
    (hprecision : pLocal + r + 1 ≤ q)
    (hP : ∀ a ∈ H, ∀ j, (P a j).ComplexityLE pLocal)
    (htwist : ∀ a ∈ H, ∀ j t, ‖twist a j t‖ ≤ 1)
    (hcorr : ∀ a ∈ H, ∀ j, Real.exp (-r) ≤
      ‖((S a j).fullSliceLaw (hlen a j)).complexMean (fun t =>
        (star (twist a j t) * nativeValue j (physical a t)) * (P a j).eval t.val)‖) :
    ∃ (freq : ∀ j, (native j).L →ₗ[ℚ] ℚ)
      (V : ∀ j, (native j).model.Niltest w) (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      Real.exp (-verticalDecompositionBudget q * Fintype.card Pivot) * outer.mass H ≤
        outer.mass retained ∧
      (∀ j, (V j).orbit = (native j).test.orbit ∧
        (V j).ComplexityLE pNative ∧ (V j).normBound ≤ 1) ∧
      (∀ j i, rationalLogHeight (freq j ((native j).model.basis i)) ≤
        verticalDecompositionBudget q) ∧
      (∀ j z, z ∈ (native j).model.filtration.realification.subgroup s → ∀ x,
        (V j).observable (z • x) = character
          ((realifyFunctional (freq j) z.coord : ℝ) : CircleFourier.Circle) * (V j).observable x) ∧
      ∀ a ∈ retained, ∀ j,
        let W := (V j).integerChartPullback (fun _ : K => 1) (β a) (hβ a)
        W.orbit = ((native j).test.integerChartPullback
          (fun _ : K => 1) (β a) (hβ a)).orbit ∧
        W.ComplexityLE pNative ∧ W.normBound ≤ 1 ∧
        (Real.exp (-r) / (2 * Real.exp (verticalDecompositionBudget q)) ≤
          ‖((S a j).fullSliceLaw (hlen a j)).complexMean (fun t =>
            (star (twist a j t) * (V j).eval (sample (physical a t))) *
              (P a j).eval t.val)‖) ∧
        Real.exp (-r) / (2 * Real.exp (verticalDecompositionBudget q)) ≤
          ‖((S a j).fullSliceLaw (hlen a j)).complexMean (fun t =>
            star (twist a j t) * ((P a j).eval t.val * W.eval t.val))‖ := by
  have hnativeCorr (a : Ω) (ha : a ∈ H) (j : Pivot) :
      Real.exp (-r) ≤ ‖((S a j).fullSliceLaw (hlen a j)).complexMean (fun t =>
        ((P a j).eval t.val * star (twist a j t)) *
          (native j).test.eval (sample (physical a t)))‖ := by
    convert hcorr a ha j using 2
    congr 1
    funext t
    rw [(native j).eval]
    ring
  obtain ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, _hint,
      _hpres, hselected⟩ := exists_sliceLaw_localPivot_weighted_native_vertical_partners
    (fun j => (native j).model) (fun _ _ => D) (fun j => (native j).test) P
    outer H hH stride S hstride hlen (fun a t => sample (physical a t)) (fun _ _ t => t.val)
    (fun a j t => star (twist a j t)) hpLocal hr hpq hprecision
    (fun j => (native j).complexity) (fun j => by exact_mod_cast (native j).norm)
    hP (fun a ha j t => by simpa only [norm_star] using htwist a ha j t) hnativeCorr
  refine ⟨freq, V, retained, hsub, hpos, hmass, ?_, hheight, hvert, ?_⟩
  · intro j
    exact ⟨(hcert j).2.1, (hcert j).1, by exact_mod_cast (hcert j).2.2.2.2⟩
  · intro a ha j
    dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [RationalFilteredNilmanifold.Niltest.integerChartPullback,
        RationalFilteredNilmanifold.Niltest.withOrbit, (hcert j).2.1]
    · exact (V j).integerChartPullback_complexity_of (fun _ : K => 1) (β a) (hβ a) (hcert j).1
    · exact (show (V j).normBound ≤ 1 by exact_mod_cast (hcert j).2.2.2.2)
    · convert hselected a ha j using 2
      congr 1
      funext t
      ring
    · have hsel := hselected a ha j
      rw [(S a j).fullSliceLaw_complexMean (hlen a j)] at hsel ⊢
      convert hsel using 2
      apply Finset.expect_congr rfl
      intro t _ht
      rw [(V j).integerChartPullback_eval]
      rw [hsample a (hsub ha) j ((S a j).fullSlicePointInIntegerBox t)
        (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)]
      ring

end Erdos3

end

end OAI
