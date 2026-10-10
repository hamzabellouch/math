import OAI.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_unconditioned_absolute_patch_family (n₀ : ℕ) [NeZero n₀]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
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
      ∃ (d : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) → ℕ)
        (patch : ∀ z, PolynomialPatch (Fin n₀) (k - 2) (d z)),
      (∀ z, (d z : ℝ) ≤ (p + 2)^C ∧ ((patch z).kernel.lip : ℝ) + 1 ≤ Real.exp ((p+2)^C)) ∧
      (∀ z ∈ productive, Real.exp (-((p+2)^C)) ≤
        𝔼 u, (f (BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint P u)
          (z.1.val,z.2.val)) - (1+xi)*a) *
          (patch z).value (fun j => ((u j).val : ℝ))) ∧
      ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1, ∀ u,
        BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint P u)
          (z.1.val,z.2.val) ∈ integerBox N := by
  obtain ⟨C, hC, xi, hxi, habsolute⟩ :=
    exists_productive_absolute_crt_patches (J := Fin n₀) k hk
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro X _ _ i p a σ L hp ha hσ hL P _ _ hprime hinj hsize N R hR W hW
    hscale hwidth hfit hboundary hcollision f hf hfree hmean
  have hsite : Function.Injective (residueBoxIntegerPoint P) := by
    intro u v he
    funext j
    apply ZMod.val_injective
    have hj := congrFun he j
    change ((u j).val : ℤ) = (v j).val at hj
    exact_mod_cast hj
  obtain ⟨hZ, productive, hmass, hinjective, hlocal, hinside⟩ :=
    BooleanCubeKernel.exists_unconditioned_productive_family N R hR
      (residueBoxIntegerPoint P) hsite i (fun _ : X => 1) (fun _ => by decide)
      {0} (Finset.singleton_nonempty _) W hW hscale hL hwidth hfit
      ((Real.exp_pos _).le.trans ha) hσ hboundary
      (by simpa only [Nat.cast_one, mul_one] using hcollision) f hf hmean
  have hne : productive.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmass
    linarith)
  obtain ⟨hcap, d, patch, hcost, hscore⟩ := habsolute productive hne hp ha P hprime hinj hsize f
    (fun z => (z.1.val,z.2.val)) hf hfree hinjective
    (fun z hz => (by linarith : a ≤ a + σ / 2).trans (hlocal z hz))
  exact ⟨hZ, productive, hmass, hinjective, hcap, d, patch, hcost, hscore, hinside⟩

end Erdos3

end

end OAI
