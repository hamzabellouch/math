import OAI.Combinatorics.Progressions.Estimates.UnconditionedArbitraryNormalizedBase

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical NNReal TensorProduct
namespace BooleanCubeKernel

theorem exists_unconditioned_arbitrary_niltest_base (s n₀ : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ E : ℕ, 2 ≤ E ∧ ∃ H : ℕ, 2 ≤ H ∧
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
        (retained : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1))
        (hpos : ∀ j, 1 ≤ w j) (hs : ∀ j, w j ≤ s),
        d ≤ d₀ ∧ d ≤ D ∧
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
        (∀ z ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw z).mean
          (fun x => (f (jointIntegerPhysicalSite x.val (z.1.val,z.2.val)) - Λ) *
            (B.shearTransformedSlots hw
              ((localForm z).loweringAt (fun j => (x.val j : ℝ)))).patchValue Ψ)) ∧
        (letI := polynomialShearIndexFintype w (fun i => hpos i)
         letI := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)
         letI := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)
         letI := realification_moduleTopology_t2 (polynomialShearOrderedBasis w)
         ∃ (F : (polynomialShearNilmanifold w s hs).Space → ℂ)
           (tests : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
             (polynomialShearNilmanifold w s hs).Niltest (fun _ : Fin n₀ => 1)),
           (∀ z, (tests z).observable = F ∧ (tests z).UnitIntervalValued ∧
             (tests z).ComplexityLE (((q + 2) ^ E + 2) ^ H)) ∧
           (∀ z t, (tests z).eval t =
             ((B.shearTransformedSlots hw
               ((localForm z).loweringAt (fun i => (t i : ℝ)))).patchValue Ψ : ℂ)) ∧
           ∀ z ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw z).mean
             (fun x => (f (jointIntegerPhysicalSite x.val (z.1.val,z.2.val)) - Λ) *
               ((tests z).eval x.val).re)) := by
  obtain ⟨C, hC, E, hE, hbase⟩ := exists_unconditioned_arbitrary_normalized_base s n₀
  obtain ⟨H, hH, hconvert⟩ := exists_fixed_local_patch_ordinary_niltest_family s
  refine ⟨C, hC, E, hE, H, hH, ?_⟩
  intro X _ _ _ p a Λ hp ha haΛ hΛ d₀ habsolute hX N hN f hf hfree A hscore
  obtain ⟨P, hprime, hinj, hcompare, hrange, hbase⟩ :=
    hbase hp ha haΛ hΛ d₀ habsolute hX N hN f hf hfree A hscore
  let : ∀ k, NeZero (P k) := fun k => ⟨(hprime k).ne_zero⟩
  obtain ⟨hW, hR, hZ, productive, hprod, hinjective, hinside,
    d, w, hw, Ψ, B, localForm, localLaw, retained, hd₀, hdD, hpos, hs,
    hΨ, hB, hretained, hmass, hmass', hslice, hcorrelation⟩ := hbase
  refine ⟨P, hprime, hinj, hcompare, hrange, hW, hR, hZ,
    productive, hprod, hinjective, hinside, d, w, hw, Ψ, B, localForm, localLaw,
    retained, hpos, hs, hd₀, hdD, hΨ, hB, hretained, hmass, hmass', hslice,
    hcorrelation, ?_⟩
  let := polynomialShearIndexFintype w (fun i => hpos i)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)
  let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)
  let := realification_moduleTopology_t2 (polynomialShearOrderedBasis w)
  let q := p + (n₀ : ℝ) + 2
  have hp0 : 0 ≤ p := by linarith
  have hd : (d : ℝ) ≤ p :=
    (Nat.cast_le.mpr (hdD.trans (Nat.min_le_right _ _))).trans (Nat.floor_le hp0)
  have hq : 1 ≤ q + 2 := by
    dsimp [q]
    linarith [Nat.cast_nonneg (α := ℝ) n₀]
  have hpq : p ≤ (q + 2) ^ E := by
    have hself : q + 2 ≤ (q + 2) ^ E := le_self_pow₀ hq (by omega)
    dsimp [q] at hself
    linarith [Nat.cast_nonneg (α := ℝ) n₀]
  obtain ⟨F, tests, htests, heval⟩ :=
    hconvert Ψ B localForm hw hpos hs ((q + 2) ^ E)
      (by positivity) (hd.trans hpq) hB hΨ
  refine ⟨F, tests, htests, heval, ?_⟩
  intro z hz
  simpa only [heval, Complex.ofReal_re] using hcorrelation z hz

end BooleanCubeKernel
end Erdos3

end

end OAI
