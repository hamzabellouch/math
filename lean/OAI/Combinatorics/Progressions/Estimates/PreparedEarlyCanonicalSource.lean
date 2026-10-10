import OAI.Combinatorics.Progressions.Dynamics.AllocatedSynchronizedBudgets

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

theorem exists_prepared_early_canonical_sources :
    ∃ A T : ℝ≥0, 1 ≤ A ∧ 1 ≤ T ∧ ∀ m : ℕ,
      ∃ Ksite Knorm Kgen Kideal A₀ T₀ Kproj : Fin (m + 1) → ℕ,
      ∃ C : ℕ, 2 ≤ C ∧
        (∀ s, 2 ≤ Ksite s ∧ 2 ≤ Knorm s ∧ 2 ≤ Kgen s ∧
          2 ≤ Kideal s ∧ 2 ≤ A₀ s ∧ 2 ≤ T₀ s ∧ 2 ≤ Kproj s) ∧
        (∀ s : Fin (m + 1),
          PhysicalAmbientRowsKernelSampling.{0,0,0} m (s.val + 1) (Kgen s)
            (fun j => (boundedBooleanJetRows (Fin (s.val + 1)) (j.val + 1) : Type))
            (fun _ => Subtype.val)) ∧
        ∀ (M : ℕ),
          let p : ℝ := preparedCommonSamplerDimension m M
          ∀ {P E : ℝ} (hP : 0 ≤ P), 0 ≤ E →
            ((m + 2 : ℕ) : ℝ) ≤ P → allocatedComparisonDimension m p ≤ P →
          let e := (p + A + T + P + E + C) ^ C
          0 ≤ e ∧ 0 < Real.exp (-e) ∧ Real.exp (-e) ≤ 1 ∧
          ∀ {X J : Type} (L : RankPreparationFamily X J m),
            (∀ j, Fintype.card (L j).Coord ≤ M) →
            ∃ δ : Fin (m + 1) → ℝ≥0, ∀ s : Fin (m + 1),
              0 < δ s ∧ δ s ≤ 1 ∧ (δ s : ℝ)⁻¹ ≤ Real.exp e ∧
              AllocatedUniversalCanonicalNativeSourceAt (G := PreparedCommonKernel m) (s := s.val)
                (PreparedCommonSamplerBlock L) p P E e (Real.exp (-e)) (Nat.cast_nonneg _) hP (δ s)
                (A₀ s) (T₀ s) (Kproj s) (Kideal s) (Ksite s) (Knorm s) (Kgen s) := by
  obtain ⟨A, T, hA, hT, hsource⟩ :=
    exists_uniform_flexible_canonical_sources.{0,0,0,0,0,0}
  refine ⟨A, T, hA, hT, ?_⟩
  intro m
  have hs (s : Fin (m + 1)) := hsource m (s.val + 1)
  choose Ksite Knorm Kgen Kideal A₀ T₀ Kproj
    hKsite hKnorm hKgen hKideal hA₀ hT₀ hKproj hgen hSources using hs
  obtain ⟨C, hC, hbudget⟩ := exists_allocatedSynchronizedRegularizationLog_bound m
  refine ⟨Ksite, Knorm, Kgen, Kideal, A₀, T₀, Kproj, C, hC,
    (fun s => ⟨hKsite s, hKnorm s, hKgen s, hKideal s, hA₀ s, hT₀ s, hKproj s⟩), hgen, ?_⟩
  intro M p P E hP hE hmP hDP e
  have hp : 0 ≤ p := Nat.cast_nonneg _
  have he : 0 ≤ e := by dsimp [e]; positivity
  refine ⟨he, Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr he), ?_⟩
  intro X J L hM
  obtain ⟨hvars, hI, hn⟩ := preparedCommonSampler_dimensions L hM
  have hvarsR : (Fintype.card (LayerSamplerVariables (PreparedCommonKernel m)
      (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (PreparedCommonSamplerBlock L)) : ℝ) ≤ p := by
    exact Nat.cast_le.mpr hvars
  have hIR : ∀ j, (Fintype.card (PreparedSamplerContinuous L j) : ℝ) ≤ p := by
    intro j; exact Nat.cast_le.mpr (hI j)
  have hnR : ∀ j, (preparedSamplerTransverse L j : ℝ) ≤ p := by
    intro j; exact Nat.cast_le.mpr (hn j)
  have hflex (s : Fin (m + 1)) :
      AllocatedFlexibleCanonicalSourceAt.{0,0,0,0,0,0}
        (G := PreparedCommonKernel m) (dim := s.val + 1) (PreparedCommonSamplerBlock L)
        p P E hp hP A T (Ksite s) (Knorm s) (Kgen s) (Kideal s) (A₀ s) (T₀ s) (Kproj s) := by
    apply hSources s (PreparedCommonSamplerBlock L) hp hP hE
      (Nat.succ_le_of_lt s.isLt) hmP hDP hvarsR hIR hnR
    intro j i
    simpa only [PreparedCommonSamplerBlock, Fintype.card_fin] using
      preparedCommonBlockCount_spectrum m j s
  have hcost := hbudget (G := PreparedCommonKernel m) (PreparedCommonSamplerBlock L)
    A T hp hP hE hvarsR hIR hnR
  have hsmooth (s : Fin (m + 1)) : 0 ≤
      allocatedCanonicalSmoothingLog (PreparedCommonSamplerBlock L) (s.val + 1) p P E A T :=
    (hflex s).1
  have htail (s : Fin (m + 1)) : 0 ≤
      allocatedCanonicalTailLog (G := PreparedCommonKernel m)
        (PreparedCommonSamplerBlock L) (s.val + 1) p P E A T :=
    (hflex s).2.1
  have hdata (s : Fin (m + 1)) := (hflex s).at_log_bounds (PreparedCommonSamplerBlock L)
    ((Finset.single_le_sum (fun i _ => hsmooth i) (Finset.mem_univ s)).trans hcost.1)
    ((Finset.single_le_sum (fun i _ => htail i) (Finset.mem_univ s)).trans hcost.2)
  choose δ hδ hδ1 hδe hnative using hdata
  exact ⟨δ, fun s => ⟨hδ s, hδ1 s, hδe s, hnative s⟩⟩

end Erdos3.VectorPolynomial

end

end OAI
