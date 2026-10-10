import OAI.Combinatorics.Progressions.Estimates.UnconditionedArbitraryFixedPatchFamily
import OAI.Combinatorics.Progressions.Lattices.UnconditionedLatePrimeBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

namespace BooleanCubeKernel

theorem exists_unconditioned_arbitrary_normalized_base (s n₀ : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ E : ℕ, 2 ≤ E ∧
      ∀ {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
        {p a Λ : ℝ}, 2 ≤ p → Real.exp (-p) ≤ a → a ≤ Λ → Λ ≤ 1 →
        ∀ (d₀ : ℕ), RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
        (Fintype.card X : ℝ) ≤ p → ∀ (N : X → ℕ),
        (∀ j, Real.exp ((p + 2) ^ C) ≤ (N j : ℝ)) →
        ∀ (f : (X → ℤ) → ℝ), (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
        IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
        ∀ (A : PolynomialPatch X s 0), Real.exp (-p) ≤ relativePatchBoxScore N f a A →
      ∃ (P : Fin n₀ → ℕ) (hprime : ∀ k, (P k).Prime),
        Function.Injective P ∧ (∀ k j, P k ≤ 2 ^ (n₀ + 1) * P j) ∧
        (∀ k, Real.exp p ≤ (P k : ℝ) ∧ (P k : ℝ) ≤ Real.exp (p + (n₀ : ℝ) + 2)) ∧
      let : ∀ k, NeZero (P k) := fun k => ⟨(hprime k).ne_zero⟩
      let σ := Real.exp (-p)
      let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
      let W := trimmedSpatialWidths (K := Fin n₀) (unconditionedResidueSiteBound P) τ N
      let R := spatialTrimMargin τ N
      let q := p + (n₀ : ℝ) + 2
      let D := min d₀ ⌊p⌋₊
      ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
        (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
      let law := selectedJointReference (trimmedIntegerBox N R)
        (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
      ∃ (productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)),
        σ / 4 ≤ law.mass productive ∧
        (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
          jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
        (∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1, ∀ u : ∀ k, ZMod (P k),
          jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val) ∈ integerBox N) ∧
      ∃ (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots (Fin n₀) d w)
        (localForm : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          PolynomialSlots (Fin n₀) d w)
        (localLaw : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          FiniteProbabilityWeights (integerBox P))
        (retained : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)),
        d ≤ d₀ ∧ d ≤ D ∧ (∀ j, 1 ≤ w j) ∧ (∀ j, w j ≤ s) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((q + 2) ^ E) ∧
        (∀ j, realPolynomialMass (B.center j) ≤ (q + 2) ^ E) ∧
        retained ⊆ productive ∧
        (law.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        ((σ / 4) / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        (∀ z ∈ retained, ∃ m, 0 < m ∧ ∃ (S : ResidueBoxSlice P m)
          (hlen : ∀ j, 0 < S.length j),
          (∀ j, Real.exp (-p) * (P j : ℝ) ≤ (S.length j : ℝ)) ∧
          localLaw z = S.fullSliceLaw hlen) ∧
        ∀ z ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw z).mean
          (fun x => (f (jointIntegerPhysicalSite x.val (z.1.val,z.2.val)) - Λ) *
            (B.shearTransformedSlots hw
              ((localForm z).loweringAt (fun j => (x.val j : ℝ)))).patchValue Ψ) := by
  obtain ⟨C, hC, hprimes⟩ := exists_unconditioned_prime_side_budget n₀
  obtain ⟨E, hE, hfamily⟩ := exists_unconditioned_arbitrary_fixed_patch_family s
  refine ⟨C, hC, E, hE, ?_⟩
  intro X _ _ _ p a Λ hp ha haΛ hΛ d₀ habsolute hX N hN f hf hfree A hscore
  obtain ⟨P, hprime, hinj, hcompare, hrange, hwidth⟩ := hprimes p hp
  let : ∀ k, NeZero (P k) := fun k => ⟨(hprime k).ne_zero⟩
  have hNpos (i : X) : 0 < N i := by
    exact_mod_cast (Real.exp_pos ((p + 2) ^ C)).trans_le (hN i)
  have hbox : (integerBox N).Nonempty := by
    refine ⟨fun _ => 0, (mem_integerBox N _).mpr ?_⟩
    intro i
    exact ⟨le_refl _, by exact_mod_cast hNpos i⟩
  have hmean : a + Real.exp (-p) ≤ 𝔼 x ∈ integerBox N, f x :=
    zero_slot_score_mean_lower_bound A N hbox f (Real.exp_pos _) hscore
  have ha0 : 0 ≤ a := (Real.exp_pos (-p)).le.trans ha
  have hΛ0 : 0 ≤ Λ := ha0.trans haΛ
  have hσ1 : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hspatial : ∀ j, unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
      (unconditionedSpatialTrimFraction (Fintype.card X) (Real.exp (-p)))
      (unconditionedCollisionWidth P (Real.exp (-p))) ≤ (N j : ℝ) :=
    fun j => (hwidth (Fintype.card X) hX).trans (hN j)
  refine ⟨P, hprime, hinj, hcompare, hrange, ?_⟩
  exact hfamily n₀ P (Classical.choice inferInstance) (by linarith) ha0 ⟨hΛ0, hΛ⟩
    (Real.exp_pos _) hσ1 d₀ habsolute hprime hinj hcompare (fun k => (hrange k).1)
    N hspatial f hf hfree hmean

end BooleanCubeKernel
end Erdos3

end

end OAI
