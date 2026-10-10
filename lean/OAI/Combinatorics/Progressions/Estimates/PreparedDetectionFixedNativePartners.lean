import OAI.Combinatorics.Progressions.Geometry.PreparedFullChartNativeDetection

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {X Ω T K : Type} [Fintype X] [DecidableEq X]
    [Fintype Ω] [Fintype T] [Nonempty T]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (outer : FiniteProbabilityWeights Ω) (physical : Ω → T → integerBox N)
    {Tests : Ω → Type} [∀ z, Nonempty (Tests z)]
    (slices : ∀ z, Tests z → Finset T) (weight : ∀ z, Tests z → T → ℂ)
    {degree : ℕ} {pNative α : ℝ}
    (hdetect : SampledSliceNativeDetection J N hbox poly outer
      (fun z t => (physical z t).val) slices weight degree pNative α)

include hdetect

omit [∀ z, Nonempty (Tests z)] in
theorem SampledSliceNativeDetection.restricted
    {sizeCap : ℝ}
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ sizeCap)
    (hweight : ∀ z j t, ‖weight z j t‖ ≤ 1)
    (g : integerBox N → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1)
    (hlarge : α ≤ sampledSliceSeminorm outer physical slices weight g) :
    ∃ (W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp pNative) (Real.exp pNative) ⟨Real.exp pNative, Real.exp_nonneg _⟩)
      (G : integerBox N → ℂ),
      Nonempty (NativeSampleModel (fun _ : X => 1) degree pNative
        (fun u : integerBox N => u.val) G) ∧
      Real.exp (-pNative) ≤
        ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
          g (fun u => star (W.eval N poly u.val) * G u)‖ := by
  let : Nonempty (integerBox N) := hbox.to_subtype
  let signal := (integerBox N : Set (X → ℤ)).indicator
    (finiteSiteExtension (Subtype.val : integerBox N → X → ℤ) g)
  have hsignal (u : X → ℤ) : ‖signal u‖ ≤ 1 := by
    by_cases hu : u ∈ integerBox N
    · rw [show signal u = g ⟨u, hu⟩ by
        simp only [signal, Set.indicator_of_mem hu]
        exact finiteSiteExtension_apply Subtype.val Subtype.val_injective g ⟨u, hu⟩]
      exact hg _
    · simp only [signal, Set.indicator_of_notMem hu, norm_zero, zero_le_one]
  have houtside (u : X → ℤ) (hu : u ∉ integerBox N) : signal u = 0 := by
    exact Set.indicator_of_notMem hu _
  have hin (u : integerBox N) : signal u.val = g u := by
    rw [show signal u.val = finiteSiteExtension Subtype.val g u.val from
      Set.indicator_of_mem u.property _]
    exact finiteSiteExtension_apply Subtype.val Subtype.val_injective g u
  have heq := sampledSliceSeminorm_congr_values outer
    (fun z t => (physical z t).val) physical slices weight hsize hweight
    signal g (fun z t => hin (physical z t))
  obtain ⟨W, G, hG, hc⟩ := hdetect signal hsignal houtside (by
    rw [heq]
    exact hlarge)
  refine ⟨W, G, hG, ?_⟩
  simpa only [hin] using hc

theorem SampledSliceNativeDetection.exists_native_approximation
    {sizeCap densityCap inputCap tau tail : ℝ}
    (hsizeCap : 0 ≤ sizeCap) (hdensityCap : 0 ≤ densityCap)
    (hinputCap : 0 < inputCap) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ sizeCap)
    (hweight : ∀ z j t, ‖weight z j t‖ ≤ 1)
    (hα : α ≤ (tau / inputCap ^ 2) / max 1 (sizeCap * (2 * densityCap) / tau))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
      (outer.siteLaw physical) densityCap ≤ tail)
    (input : integerBox N → ℂ) (hinput : ∀ x, ‖input x‖ ≤ inputCap) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → integerBox N → ℂ)
      (c : Fin n → ℝ) (e : integerBox N → ℂ),
      (∀ i, Q i ∈ twistedNativeSampleFunctions (fun _ : X => 1) degree pNative
        (fun u : integerBox N => u.val)
        (fun W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp pNative) (Real.exp pNative) ⟨Real.exp pNative, Real.exp_nonneg _⟩ =>
          fun u : integerBox N => W.eval N poly u.val)) ∧
      input = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2 / Real.exp (-pNative) ∧
      sampledSliceSeminorm outer physical slices weight e ≤
        2 * tau + 2 * sizeCap * (inputCap + 2 / Real.exp (-pNative)) * tail ∧
      (n : ℝ) ≤ 1 + 4 * (sizeCap * (2 * densityCap)) ^ 2 /
        (Real.exp (-pNative) ^ 2 * tau ^ 2) := by
  let : Nonempty (integerBox N) := hbox.to_subtype
  have hunit (g : integerBox N → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1)
      (hlarge : (tau / inputCap ^ 2) / max 1 (sizeCap * (2 * densityCap) / tau) ≤
        sampledSliceSeminorm outer physical slices weight g) :
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp pNative) (Real.exp pNative) ⟨Real.exp pNative, Real.exp_nonneg _⟩)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel (fun _ : X => 1) degree pNative
          (fun u : integerBox N => u.val) G) ∧
        Real.exp (-pNative) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
            g (fun u => star (W.eval N poly u.val) * G u)‖ := by
    exact hdetect.restricted J N hbox poly outer physical slices weight hsize hweight
      g hg (hα.trans hlarge)
  exact exists_sampled_native_model outer physical slices weight
    (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox)
    (fun u => by
      change 0 < (Fintype.card (integerBox N) : ℝ)⁻¹
      positivity)
    (fun _ : X => 1) degree pNative (fun u : integerBox N => u.val)
    (fun (W : NormalizedPolynomialTwist X (Σ j, J j) (Real.exp pNative) (Real.exp pNative) ⟨Real.exp pNative, Real.exp_nonneg _⟩) (u : integerBox N) => W.eval N poly u.val) (fun W u => W.norm_eval_le N poly u.val)
    hsizeCap hdensityCap hinputCap (Real.exp_pos _) htau hsize hweight hunit hexcess input hinput

theorem SampledSliceNativeDetection.exists_fixed_native_partners
    [Fintype K] (productive : Finset Ω) (selected : ∀ z, K → Tests z)
    (hS : ∀ z j, (slices z j).Nonempty)
    {sizeCap densityCap inputCap tau tail δ κ : ℝ}
    (hsizeCap : 0 ≤ sizeCap) (hdensityCap : 0 ≤ densityCap)
    (hinputCap : 0 < inputCap) (htau : 0 < tau) (hδ : 0 < δ) (hκ : 0 < κ)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ sizeCap)
    (hweight : ∀ z j t, ‖weight z j t‖ ≤ 1)
    (hα : α ≤ (tau / inputCap ^ 2) / max 1 (sizeCap * (2 * densityCap) / tau))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
      (outer.siteLaw physical) densityCap ≤ tail)
    (hproductive : κ ≤ outer.mass productive)
    (herror : (Fintype.card K : ℝ) *
      (2 * tau + 2 * sizeCap * (inputCap + 2 / Real.exp (-pNative)) * tail) ≤ κ * δ / 8)
    (input : K → integerBox N → ℂ) (hinput : ∀ k x, ‖input k x‖ ≤ inputCap)
    (hscore : ∀ z ∈ productive, ∀ k, δ ≤
      ‖𝔼 t ∈ slices z (selected z k), input k (physical z t) * weight z (selected z k) t‖) :
    ∃ (fixedTwist : K → NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp pNative) (Real.exp pNative) ⟨Real.exp pNative, Real.exp_nonneg _⟩)
      (nativeValue : K → integerBox N → ℂ)
      (_native : ∀ k, NativeSampleModel (fun _ : X => 1) degree pNative
        (fun u : integerBox N => u.val) (nativeValue k))
      (retained : Finset Ω),
      retained ⊆ productive ∧ 0 < outer.mass retained ∧
      (3 * κ / 4) / (1 + 4 * (sizeCap * (2 * densityCap)) ^ 2 /
        (Real.exp (-pNative) ^ 2 * tau ^ 2)) ^ Fintype.card K ≤ outer.mass retained ∧
      ∀ z ∈ retained, ∀ k, δ / (2 * (2 / Real.exp (-pNative))) ≤
        ‖𝔼 t ∈ slices z (selected z k),
          (star ((fixedTwist k).eval N poly (physical z t).val) * nativeValue k (physical z t)) *
            weight z (selected z k) t‖ := by
  choose n hn Q c e hQ hmodel hc herr hnBound using fun k =>
    hdetect.exists_native_approximation J N hbox poly outer physical slices weight
      hsizeCap hdensityCap hinputCap htau hsize hweight hα hexcess (input k) (hinput k)
  let : ∀ k, Nonempty (Fin (n k)) := fun k => ⟨⟨0, hn k⟩⟩
  have hmodelComplex (k : K) : input k = (∑ i, (c k i : ℂ) • Q k i) + e k :=
    hmodel k
  have hcComplex (k : K) : ∑ i, ‖(c k i : ℂ)‖ ≤ 2 / Real.exp (-pNative) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hc k
  have herrorSum : (∑ k, sampledSliceSeminorm outer physical slices weight (e k)) ≤ κ * δ / 8 := by
    apply le_trans (Finset.sum_le_sum (fun k _ => herr k))
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using herror
  obtain ⟨fixedTwist, nativeValue, native, retained, hsub, hpos, hmass, hcorr⟩ :=
    exists_fixed_sampled_slice_native_partners outer productive physical slices weight selected
      hS hsize hweight input e Q (fun k i => (c k i : ℂ)) hmodelComplex hδ
      (by positivity : 0 < 2 / Real.exp (-pNative)) hcComplex hproductive herrorSum hκ
      (fun _ : X => 1) degree pNative (fun u : integerBox N => u.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) (Real.exp pNative) (Real.exp pNative) ⟨Real.exp pNative, Real.exp_nonneg _⟩) (u : integerBox N) => W.eval N poly u.val) hQ hscore
  refine ⟨fixedTwist, nativeValue, native, retained, hsub, hpos, ?_, hcorr⟩
  apply le_trans _ hmass
  apply div_le_div_of_nonneg_left (by positivity)
    (Finset.prod_pos (fun k _ => by simpa only [Fintype.card_fin] using Nat.cast_pos.mpr (hn k)))
  calc
    (∏ k, (Fintype.card (Fin (n k)) : ℝ)) = ∏ k, (n k : ℝ) := by simp only [Fintype.card_fin]
    _ ≤ ∏ _k : K, (1 + 4 * (sizeCap * (2 * densityCap)) ^ 2 /
        (Real.exp (-pNative) ^ 2 * tau ^ 2)) :=
      Finset.prod_le_prod₀ (fun k _ => Nat.cast_nonneg _) (fun k _ => hnBound k)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

end Erdos3.VectorPolynomial

end

end OAI
