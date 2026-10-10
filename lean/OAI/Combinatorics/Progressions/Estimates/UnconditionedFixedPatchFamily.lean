import OAI.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical NNReal

theorem exists_productive_absolute_fixed_patch_function
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J] (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ E : ℕ, 2 ≤ E ∧ ∃ xi : ℝ, 0 < xi ∧
      ∀ {H X : Type*} [Fintype H] (outer : FiniteProbabilityWeights H) (productive : Finset H), 0 < outer.mass productive →
      ∀ {p a : ℝ}, 2 ≤ p → Real.exp (-p) ≤ a →
      ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)],
        (∀ j, (N j).Prime) → Function.Injective N →
        (∀ j, Real.exp ((p + 2) ^ C) ≤ N j) →
      ∀ (f : (X → ℤ) → ℝ) (z : H → (X → ℤ) × (Option J × X → ℤ)),
        (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
        IntegerVectorAPFree (Function.support f) k →
        (∀ h ∈ productive, Function.Injective
          (fun u => BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint N u) (z h))) →
        (∀ h ∈ productive, a ≤ 𝔼 u,
          f (BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint N u) (z h))) →
      let q := (p + 2) ^ C + (Fintype.card J : ℝ) + 2
      let D := ⌊(p + 2) ^ C⌋₊
      (1 + xi) * a < 1 ∧
      ∃ (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots J d w) (localForm : H → PolynomialSlots J d w)
        (retained : Finset H),
        d ≤ D ∧ (∀ i, 1 ≤ w i) ∧ (∀ i, w i ≤ k - 2) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((q + 2) ^ E) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ (q + 2) ^ E) ∧
        retained ⊆ productive ∧
        (outer.mass productive / ((D + 1) * (k - 2 + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ outer.mass retained ∧
        ∀ h ∈ retained, Real.exp (-((q + 2) ^ E)) ≤
          𝔼 u, (f (BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint N u) (z h)) -
            (1 + xi) * a) *
            (B.shearTransformedSlots hw
              ((localForm h).loweringAt (fun j => ((u j).val : ℝ)))).patchValue Ψ := by
  obtain ⟨C, hC, xi, hxi, habsolute⟩ := exists_productive_absolute_crt_patches (J := J) k hk
  obtain ⟨E, hE, hfixed⟩ := exists_varying_rank_fixed_patch_function (k - 2)
  refine ⟨C, hC, E, hE, xi, hxi, ?_⟩
  intro H X _ outer productive hmass p a hp ha N _ _ hprime hinj hsize f z hf hfree hzinj hmean
  let q := (p + 2) ^ C + (Fintype.card J : ℝ) + 2
  let D := ⌊(p + 2) ^ C⌋₊
  have hne : productive.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmass
    linarith)
  obtain ⟨h0, hh0⟩ := hne
  let : Nonempty H := ⟨h0⟩
  obtain ⟨hcap, d, patch, hcost, hscore⟩ :=
    habsolute productive ⟨h0,hh0⟩ hp ha N hprime hinj hsize f z hf hfree hzinj hmean
  have hpower : 0 ≤ (p + 2) ^ C := pow_nonneg (by linarith) _
  have hpq : (p + 2) ^ C ≤ q := by dsimp only [q]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card J)]
  have hq : 0 ≤ q := hpower.trans hpq
  have hD : (D : ℝ) ≤ q := (Nat.floor_le hpower).trans hpq
  have hJ : (Fintype.card J : ℝ) ≤ q := by dsimp only [q]; linarith
  have hd (h) : d h ≤ D := Nat.le_floor (hcost h).1
  have hLip (h) : ((patch h).kernel.lip : ℝ) ≤ Real.exp q :=
    (by linarith [(hcost h).2] : ((patch h).kernel.lip : ℝ) ≤ Real.exp ((p + 2) ^ C)).trans
      (Real.exp_le_exp.mpr hpq)
  let localLaw := fun _ : H => FiniteProbabilityWeights.uniform (∀ j, ZMod (N j))
  let point := fun (_ : H) (u : ∀ j, ZMod (N j)) => residueBoxIntegerPoint N u
  let score := fun h u => f (BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint N u) (z h)) -
    (1 + xi) * a
  have htarget : 0 ≤ (1 + xi) * a :=
    mul_nonneg (by linarith) ((Real.exp_pos (-p)).le.trans ha)
  have hscorebound (h) (u : ∀ j, ZMod (N j)) : |score h u| ≤ 1 := by
    dsimp only [score]
    exact abs_le.mpr ⟨by linarith [(hf (BooleanCubeKernel.jointIntegerPhysicalSite
      (residueBoxIntegerPoint N u) (z h))).1], by linarith [(hf (BooleanCubeKernel.jointIntegerPhysicalSite
      (residueBoxIntegerPoint N u) (z h))).2]⟩
  have hpositive (h) (hh : h ∈ productive) : Real.exp (-q) ≤ (localLaw h).mean
      (fun u => score h u * (patch h).value (fun j => (point h u j : ℝ))) := by
    simp only [localLaw, FiniteProbabilityWeights.uniform_mean, point, score, residueBoxIntegerPoint]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (hscore h hh)
  obtain ⟨d₀, w, hw, Ψ, B, localForm, retained, hd₀, hpos, hws, hΨ, hB, hsub, hretained, hlocal⟩ :=
    hfixed outer productive d patch D q hd hmass hq hD hJ hLip localLaw point score hscorebound hpositive
  refine ⟨hcap, d₀, w, hw, Ψ, B, localForm, retained, hd₀, hpos, hws, hΨ, hB, hsub, hretained, ?_⟩
  intro h hh
  simpa only [localLaw, FiniteProbabilityWeights.uniform_mean, point, score, residueBoxIntegerPoint, Int.cast_natCast, q] using hlocal h hh

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_concrete_unconditioned_fixed_patch_family (n₀ : ℕ) [NeZero n₀]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ E : ℕ, 2 ≤ E ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {X : Type*} [Fintype X] [DecidableEq X] (_i : X)
      {p a σ : ℝ}, 2 ≤ p → Real.exp (-p) ≤ a → 0 < σ → σ ≤ 1 →
    ∀ (P : Fin n₀ → ℕ) [∀ j, NeZero (P j)] [NeZero (∏ j, P j)],
      (∀ j, (P j).Prime) → Function.Injective P →
      (∀ j, Real.exp ((p + 2)^C) ≤ P j) →
    ∀ (N : X → ℕ),
      (∀ j, unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
        (unconditionedSpatialTrimFraction (Fintype.card X) σ)
        (unconditionedCollisionWidth P σ) ≤ (N j : ℝ)) →
    ∀ (f : (X → ℤ) → ℝ), (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree (Function.support f) k →
      a + σ ≤ (𝔼 x ∈ integerBox N, f x) →
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    let W := trimmedSpatialWidths (K := Fin n₀) (unconditionedResidueSiteBound P) τ N
    let R := spatialTrimMargin τ N
    ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (fun u =>
        BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
      (1 + xi) * a < 1 ∧
      let q := (p + 2) ^ C + (n₀ : ℝ) + 2
      let D := ⌊(p + 2) ^ C⌋₊
      ∃ (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots (Fin n₀) d w)
        (localForm : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          PolynomialSlots (Fin n₀) d w)
        (retained : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)),
        d ≤ D ∧ (∀ j, 1 ≤ w j) ∧ (∀ j, w j ≤ k - 2) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((q + 2) ^ E) ∧
        (∀ j, realPolynomialMass (B.center j) ≤ (q + 2) ^ E) ∧
        retained ⊆ productive ∧
        (law.mass productive / ((D + 1) * (k - 2 + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        ((σ / 4) / ((D + 1) * (k - 2 + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        (∀ z ∈ retained, Real.exp (-((q + 2) ^ E)) ≤
          𝔼 u, (f (BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint P u)
            (z.1.val,z.2.val)) - (1+xi)*a) *
            (B.shearTransformedSlots hw
              ((localForm z).loweringAt (fun j => ((u j).val : ℝ)))).patchValue Ψ) ∧
        ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1, ∀ u,
          BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint P u)
            (z.1.val,z.2.val) ∈ integerBox N := by
  obtain ⟨C, hC, E, hE, xi, hxi, hfixed⟩ :=
    exists_productive_absolute_fixed_patch_function (J := Fin n₀) k hk
  refine ⟨C, hC, E, hE, xi, hxi, ?_⟩
  intro X _ _ i p a σ hp ha hσ hσ1 P _ _ hprime hinj hsize N hN f hf hfree hmean
  let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
  let W := trimmedSpatialWidths (K := Fin n₀) (unconditionedResidueSiteBound P) τ N
  let R := spatialTrimMargin τ N
  obtain ⟨hW, hR, hZ, productive, hmass, hinjective, hlocal, hinside⟩ :=
    BooleanCubeKernel.exists_concrete_unconditioned_productive_family P i
      ((Real.exp_pos _).le.trans ha) hσ hσ1 N hN f hf hmean
  let law := selectedJointReference (trimmedIntegerBox N R)
    (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
  have hmasspos : 0 < law.mass productive := (by positivity : 0 < σ / 4).trans_le hmass
  obtain ⟨hcap, d, w, hw, Ψ, B, localForm, retained,
      hd, hwpos, hwmax, hΨ, hB, hsub, hretained, hscore⟩ :=
    hfixed law productive hmasspos hp ha P hprime hinj hsize f
      (fun z => (z.1.val,z.2.val)) hf hfree hinjective
      (fun z hz => (by linarith : a ≤ a + σ / 2).trans (hlocal z hz))
  refine ⟨hW, hR, hZ, productive, hmass, hinjective, hcap, d, w, hw, Ψ, B, localForm, retained,
    hd, hwpos, hwmax, ?_, ?_, hsub, ?_, ?_, ?_, hinside⟩
  · simpa only [Fintype.card_fin] using hΨ
  · simpa only [Fintype.card_fin] using hB
  · simpa only [Fintype.card_fin] using hretained
  · have hm := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hmass (Nat.cast_nonneg
        ((⌊(p + 2) ^ C⌋₊ + 1) * (k - 2 + 1) ^ ⌊(p + 2) ^ C⌋₊)))
      (Real.exp_pos (-(((p + 2) ^ C + (n₀ : ℝ) + 2 + 2) ^ E))).le
    exact hm.trans (by simpa only [Fintype.card_fin] using hretained)
  · simpa only [Fintype.card_fin] using hscore

theorem exists_concrete_unconditioned_fixed_patch_family_of_zero_score (n₀ : ℕ) [NeZero n₀]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ E : ℕ, 2 ≤ E ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {X : Type*} [Fintype X] [DecidableEq X] (_i : X)
      {p a σ : ℝ}, 2 ≤ p → Real.exp (-p) ≤ a → 0 < σ → σ ≤ 1 →
    ∀ (P : Fin n₀ → ℕ) [∀ j, NeZero (P j)] [NeZero (∏ j, P j)],
      (∀ j, (P j).Prime) → Function.Injective P →
      (∀ j, Real.exp ((p + 2)^C) ≤ P j) →
    ∀ (N : X → ℕ),
      (∀ j, unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
        (unconditionedSpatialTrimFraction (Fintype.card X) σ)
        (unconditionedCollisionWidth P σ) ≤ (N j : ℝ)) →
    ∀ (f : (X → ℤ) → ℝ), (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree (Function.support f) k →
      ∀ oldPatch : PolynomialPatch X (k - 2) 0,
      σ ≤ (𝔼 x ∈ integerBox N, (f x - a) * oldPatch.value (fun j => (x j : ℝ))) →
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    let W := trimmedSpatialWidths (K := Fin n₀) (unconditionedResidueSiteBound P) τ N
    let R := spatialTrimMargin τ N
    ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (fun u =>
        BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
      (1 + xi) * a < 1 ∧
      let q := (p + 2) ^ C + (n₀ : ℝ) + 2
      let D := ⌊(p + 2) ^ C⌋₊
      ∃ (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots (Fin n₀) d w)
        (localForm : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          PolynomialSlots (Fin n₀) d w)
        (retained : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)),
        d ≤ D ∧ (∀ j, 1 ≤ w j) ∧ (∀ j, w j ≤ k - 2) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((q + 2) ^ E) ∧
        (∀ j, realPolynomialMass (B.center j) ≤ (q + 2) ^ E) ∧
        retained ⊆ productive ∧
        (law.mass productive / ((D + 1) * (k - 2 + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        ((σ / 4) / ((D + 1) * (k - 2 + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        (∀ z ∈ retained, Real.exp (-((q + 2) ^ E)) ≤
          𝔼 u, (f (BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint P u)
            (z.1.val,z.2.val)) - (1+xi)*a) *
            (B.shearTransformedSlots hw
              ((localForm z).loweringAt (fun j => ((u j).val : ℝ)))).patchValue Ψ) ∧
        ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1, ∀ u,
          BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint P u)
            (z.1.val,z.2.val) ∈ integerBox N := by
  obtain ⟨C, hC, E, hE, xi, hxi, hmain⟩ :=
    exists_concrete_unconditioned_fixed_patch_family n₀ k hk
  refine ⟨C, hC, E, hE, xi, hxi, ?_⟩
  intro X _ _ i p a σ hp ha hσ hσ1 P _ _ hprime hinj hsize N hN f hf hfree oldPatch hscore
  have hbox : (integerBox N).Nonempty := by
    by_contra he
    have hempty : integerBox N = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [hempty, Finset.expect_empty] at hscore
    linarith
  have hmean := zero_slot_score_mean_lower_bound oldPatch N hbox f hσ hscore
  exact hmain i hp ha hσ hσ1 P hprime hinj hsize N hN f hf hfree hmean

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_unconditioned_fixed_patch_family (n₀ : ℕ) [NeZero n₀]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ E : ℕ, 2 ≤ E ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {X : Type*} [Fintype X] [DecidableEq X] (i : X)
      {p a σ L : ℝ}, 2 ≤ p → Real.exp (-p) ≤ a → 0 < σ → 0 < L →
    ∀ (P : Fin n₀ → ℕ) [∀ j, NeZero (P j)] [NeZero (∏ j, P j)],
      (∀ j, (P j).Prime) → Function.Injective P →
      (∀ j, Real.exp ((p + 2)^C) ≤ P j) →
    ∀ (N R : X → ℕ) (hR : ∀ i, 2 * R i < N i)
      (W : Option (Fin n₀) × X → ℝ) (hW : ∀ z, 0 < W z),
      (∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤
        residueProfileWidth (fun _ : X => 1) W z) →
      (∀ j, L ≤ W (some j,i)) →
      (∀ u j, BooleanCubeKernel.physicalSiteWidth (residueBoxIntegerPoint P u) W j ≤ (R j : ℝ)) →
      2 * (∑ j, 2 * (R j : ℝ) / N j) ≤ σ / 8 →
      (Fintype.card (∀ j, ZMod (P j)) : ℝ)^2 * (2 / L) ≤ σ / 16 →
    ∀ (f : (X → ℤ) → ℝ), (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree (Function.support f) k →
      a + σ ≤ (𝔼 x ∈ integerBox N, f x) →
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z,
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (fun u =>
        BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
      (1 + xi) * a < 1 ∧
      let q := (p + 2) ^ C + (n₀ : ℝ) + 2
      let D := ⌊(p + 2) ^ C⌋₊
      ∃ (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots (Fin n₀) d w)
        (localForm : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          PolynomialSlots (Fin n₀) d w)
        (retained : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)),
        d ≤ D ∧ (∀ j, 1 ≤ w j) ∧ (∀ j, w j ≤ k - 2) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((q + 2) ^ E) ∧
        (∀ j, realPolynomialMass (B.center j) ≤ (q + 2) ^ E) ∧
        retained ⊆ productive ∧
        (law.mass productive / ((D + 1) * (k - 2 + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        ((σ / 4) / ((D + 1) * (k - 2 + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        (∀ z ∈ retained, Real.exp (-((q + 2) ^ E)) ≤
          𝔼 u, (f (BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint P u)
            (z.1.val,z.2.val)) - (1+xi)*a) *
            (B.shearTransformedSlots hw
              ((localForm z).loweringAt (fun j => ((u j).val : ℝ)))).patchValue Ψ) ∧
        ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1, ∀ u,
          BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint P u)
            (z.1.val,z.2.val) ∈ integerBox N := by
  obtain ⟨C, hC, E, hE, xi, hxi, hfixed⟩ :=
    exists_productive_absolute_fixed_patch_function (J := Fin n₀) k hk
  refine ⟨C, hC, E, hE, xi, hxi, ?_⟩
  intro X _ _ i p a σ L hp ha hσ hL P _ _ hprime hinj hsize N R hR W hW
    hscale hwidth hfit hboundary hcollision f hf hfree hmean
  have hsite : Function.Injective (residueBoxIntegerPoint P) := by
    intro u v he
    funext j
    apply ZMod.val_injective
    have hj := congrFun he j
    change ((u j).val : ℤ) = ((v j).val : ℤ) at hj
    exact_mod_cast hj
  obtain ⟨hZ, productive, hmass, hinjective, hlocal, hinside⟩ :=
    BooleanCubeKernel.exists_unconditioned_productive_family N R hR
      (residueBoxIntegerPoint P) hsite i (fun _ : X => 1) (fun _ => by decide)
      {0} (Finset.singleton_nonempty _) W hW hscale hL hwidth hfit
      ((Real.exp_pos _).le.trans ha) hσ hboundary
      (by simpa only [Nat.cast_one, mul_one] using hcollision) f hf hmean
  let law := selectedJointReference (trimmedIntegerBox N R)
    (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
  have hmasspos : 0 < law.mass productive := (by positivity : 0 < σ / 4).trans_le hmass
  obtain ⟨hcap, d, w, hw, Ψ, B, localForm, retained,
      hd, hwpos, hwmax, hΨ, hB, hsub, hretained, hscore⟩ :=
    hfixed law productive hmasspos hp ha P hprime hinj hsize f
      (fun z => (z.1.val,z.2.val)) hf hfree hinjective
      (fun z hz => (by linarith : a ≤ a + σ / 2).trans (hlocal z hz))
  refine ⟨hZ, productive, hmass, hinjective, hcap, d, w, hw, Ψ, B, localForm, retained,
    hd, hwpos, hwmax, ?_, ?_, hsub, ?_, ?_, ?_, hinside⟩
  · simpa only [Fintype.card_fin] using hΨ
  · simpa only [Fintype.card_fin] using hB
  · simpa only [Fintype.card_fin] using hretained
  · have hm := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hmass (Nat.cast_nonneg
        ((⌊(p + 2) ^ C⌋₊ + 1) * (k - 2 + 1) ^ ⌊(p + 2) ^ C⌋₊)))
      (Real.exp_pos (-(((p + 2) ^ C + (n₀ : ℝ) + 2 + 2) ^ E))).le
    exact hm.trans (by simpa only [Fintype.card_fin] using hretained)
  · simpa only [Fintype.card_fin] using hscore

end Erdos3

end

end OAI
