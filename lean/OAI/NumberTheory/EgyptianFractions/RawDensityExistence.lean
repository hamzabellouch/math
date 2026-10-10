import OAI.NumberTheory.EgyptianFractions.SampledDenominatorCertificate
import OAI.NumberTheory.EgyptianFractions.ResidueRegimeSplice
import OAI.NumberTheory.EgyptianFractions.RawDensityParameters
import OAI.NumberTheory.EgyptianFractions.FiniteResidueIndices
import OAI.NumberTheory.EgyptianFractions.DensityMomentBound
import OAI.NumberTheory.EgyptianFractions.DeterministicResidueSupply
import OAI.NumberTheory.EgyptianFractions.GeometricRandomResidues

namespace OAI
noncomputable section

open Filter
open scoped BigOperators

namespace Problem337

open RandomProducts

/-- The deterministic and sampled lists can use exactly the same Boolean
sample space. The deterministic list is chosen before the random realization,
and every realization is accommodated by a common bounded denominator.
This is an unconditional arithmetic statement, including the prime pool. -/
theorem eventually_common_residue_lists :
    ∀ᶠ S : ℝ in atTop,
      S ^ 99 ≤ ((widePrimePool (S ^ 100)).card : ℝ) ∧
      (∀ q ∈ widePrimePool (S ^ 100),
        Nat.Prime q ∧ S ^ 100 < (q : ℝ) ∧ (q : ℝ) ≤ S ^ 101) ∧
      ∃ t₀ : (Fin (ResidueLevels.scale S) → Bool) → ℕ,
        Function.Injective t₀ ∧
        ∀ f : Fin 1000 →
            ((Fin (ResidueLevels.scale S) × Bool) → widePrimePool (S ^ 100)),
          ∃ M : ℕ, Real.exp S < (M : ℝ) ∧
            (M : ℝ) ≤ Real.exp (RawDensityParameters.DM * S) ∧
            2 ^ TerminalDepth.binaryExponent RawDensityParameters.D₀ S ∣ M ∧
            (∀ I : Fin (ResidueLevels.scale S) → Bool,
              t₀ I ∣ M ∧ 0 < t₀ I ∧ (t₀ I : ℝ) ≤ Real.exp (101 * S)) ∧
            (∀ i (I : Fin (ResidueLevels.scale S) → Bool),
              sampledProduct (f i) I ∣ M ∧ 0 < sampledProduct (f i) I ∧
                (sampledProduct (f i) I : ℝ) ≤ Real.exp (101 * S)) := by
  filter_upwards [eventually_sampled_denominator_certificate] with S hS
  obtain ⟨hsize, hpool, p, hp, hprime, hsubset, hdenominator⟩ := hS
  let t₀ : (Fin (ResidueLevels.scale S) → Bool) → ℕ := fun I =>
    ResidueConstruction.subsetEntry p ((residueWordEquiv (ResidueLevels.scale S)).symm I)
  refine ⟨hsize, hpool, t₀, hsubset.comp (residueWordEquiv _).symm.injective, ?_⟩
  intro f
  obtain ⟨M, hMlo, hMhi, hbinary, hfixed, hsampled⟩ := hdenominator f
  refine ⟨M, hMlo, hMhi, hbinary, ?_, hsampled⟩
  intro I
  exact hfixed ((residueWordEquiv (ResidueLevels.scale S)).symm I)

open RawDensityParameters GeometricDensity in
/-- Actual deterministic residue supply simultaneously on the canonical high
levels, with the same Boolean sample type as the random construction. -/
theorem eventually_geometric_high_residue_lists :
    ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
      ∀ t : (Fin (ResidueLevels.scale S) → Bool) → ℕ,
        Function.Injective t →
        (∀ I, (t I : ℝ) ≤ Real.exp (101 * S)) →
        ∃ E : ℕ → Finset ℕ, ∀ j < depth DM η S,
          Real.exp S < cutoff DM η S j →
          ((E j).card : ℝ) ≤ cutoff DM η S j *
              Real.exp (-c * ResidueLevels.scale S) ∧
          ∀ u ∈ Finset.Icc 1 ⌊cutoff DM η S j⌋₊, u ∉ E j →
            cutoff DM η S (j + 1) < (u : ℝ) →
            contraction η S * (2 : ℝ) ^ ResidueLevels.scale S / 2 ≤
              ((Finset.univ.filter (fun I : Fin (ResidueLevels.scale S) → Bool =>
                Int.fract (-((C * t I : ℕ) : ℝ) / u) < contraction η S)).card : ℝ) := by
  classical
  filter_upwards [deterministic_high_residue_distribution (4 * (DM + 2))
      (by norm_num [DM]), ResidueLevels.eventually_scale_bounds,
    eventually_ge_atTop (1 : ℝ)] with S hhigh hscale hS
  intro C hClo hChi t ht hsize
  have hm : (0 : ℝ) < ResidueLevels.scale S := by
    exact_mod_cast (show 0 < ResidueLevels.scale S by omega)
  have hη : 0 < η := eta_pos
  have hrho : Real.exp (-(ResidueLevels.scale S : ℝ) / 10000) = contraction η S := by
    unfold contraction η
    congr 1
    ring
  have herr : Real.exp (-(ResidueLevels.scale S : ℝ) / 1000) =
      Real.exp (-c * ResidueLevels.scale S) := by
    unfold c
    congr 1
    ring
  have hcard : Real.exp (Real.log 2 * (ResidueLevels.scale S : ℝ)) ≤
      ((Finset.univ : Finset (Fin (ResidueLevels.scale S) → Bool)).card : ℝ) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp
  have hlocal : ∀ j : ℕ, ∃ E : Finset ℕ,
      j < depth DM η S → Real.exp S < cutoff DM η S j →
        (E.card : ℝ) ≤ cutoff DM η S j * Real.exp (-c * ResidueLevels.scale S) ∧
        ∀ u ∈ Finset.Icc 1 ⌊cutoff DM η S j⌋₊, u ∉ E →
          cutoff DM η S (j + 1) < (u : ℝ) →
          contraction η S * (2 : ℝ) ^ ResidueLevels.scale S / 2 ≤
            ((Finset.univ.filter (fun I : Fin (ResidueLevels.scale S) → Bool =>
              Int.fract (-((C * t I : ℕ) : ℝ) / u) < contraction η S)).card : ℝ) := by
    intro j
    by_cases hj : j < depth DM η S
    · by_cases hlarge : Real.exp S < cutoff DM η S j
      · have hX : cutoff DM η S j ≤ Real.exp ((4 * (DM + 2)) * S / 4) := by
          have hmono := (ResidueLevels.level_strictAnti
            (A := (DM + 2) * S) hm hη).antitone (Nat.zero_le j)
          simpa only [ResidueLevels.level_zero,
            show 4 * (DM + 2) * S / 4 = (DM + 2) * S by ring] using hmono
        obtain ⟨E, hsub, hEc, hcount⟩ := hhigh (ResidueLevels.scale S)
          (cutoff DM η S j) C hscale.2.2.1 hscale.2.2.2 hlarge.le hX hClo hChi
          Finset.univ t (fun _ _ _ _ heq => ht heq) hcard (fun I _ => hsize I)
        refine ⟨E, fun _ _ => ⟨by simpa only [herr] using hEc, ?_⟩⟩
        intro u hu hnot hunext
        have hstep : cutoff DM η S (j + 1) =
            Real.exp (-(ResidueLevels.scale S : ℝ) / 10000) * cutoff DM η S j := by
          rw [hrho]
          exact ResidueLevels.level_succ _ _ _ j
        have hfloor : ⌊Real.exp (-(ResidueLevels.scale S : ℝ) / 10000) *
            cutoff DM η S j⌋₊ < u := by
          apply (Nat.floor_lt' (by have := (Finset.mem_Icc.mp hu).1; omega : u ≠ 0)).2
          simpa only [hstep] using hunext
        have hu' := Finset.mem_Icc.mpr
          ⟨show ⌊Real.exp (-(ResidueLevels.scale S : ℝ) / 10000) *
              cutoff DM η S j⌋₊ + 1 ≤ u by omega, (Finset.mem_Icc.mp hu).2⟩
        simpa only [hrho, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using hcount u hu' hnot
      · exact ⟨∅, fun _ hh => (hlarge hh).elim⟩
    · exact ⟨∅, fun h _ => (hj h).elim⟩
  choose E hE using hlocal
  exact ⟨E, hE⟩

/-- Reindex the sampled count without losing repeated data. -/
theorem reindexed_boolean_residue_count {m : ℕ}
    (t : (Fin m → Bool) → ℕ) (ρ : ℝ) (u : ℕ)
    (h : ρ / 2 * (2 : ℝ) ^ m ≤
      ((Finset.univ.filter (fun a : Fin m → Bool =>
        Int.fract (-(t a : ℝ) / u) < ρ)).card : ℝ)) :
    ρ * ((residueIndices (Fin m → Bool)).card : ℝ) / 2 ≤
      (((residueIndices (Fin m → Bool)).filter (fun i =>
        Int.fract (-((residueEntry t i : ℕ) : ℝ) / u) < ρ)).card : ℝ) := by
  classical
  rw [card_filter_residueEntry t (fun n : ℕ => Int.fract (-(n : ℝ) / u) < ρ)]
  simp only [residueIndices_card, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  convert h using 1; ring

open RawDensityParameters GeometricDensity in
/-- Unconditional arithmetic construction of the raw density supply. The
prime-product and sampled lists share one bounded denominator, and the actual
high and middle residue estimates are joined before the density descent. -/
theorem eventually_raw_density_supply :
    ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
      RawDensitySupply DM L c K r S C := by
  classical
  filter_upwards [eventually_common_residue_lists,
    eventually_geometric_high_residue_lists,
    eventually_common_geometric_random_fractional_residues (DM + 2)
      (by norm_num [DM]),
    eventually_residue_level_moment DM η r DM_gt_one eta_pos eta_le_half
      (by linarith [r_ge_two]),
    eventually_raw_density_supply_of_residue_data,
    eventually_ge_atTop (1 : ℝ)] with S hlists hhigh hrandom hmoment hconstruct hS
  intro C hClo hChi
  have hSpos : 0 < S := by linarith
  obtain ⟨hpoolsize, hpool, t₀, ht₀, hdenom⟩ := hlists
  obtain ⟨f, E₁, hmiddle, hterminal⟩ := hrandom (widePrimePool (S ^ 100))
    (fun q hq => (hpool q hq).1)
    (fun q hq => ⟨(hpool q hq).2.1.le, (hpool q hq).2.2⟩) hpoolsize
  obtain ⟨M, hMlo, hMhi, hbinary, hfixed, hsampled⟩ := hdenom f
  obtain ⟨E₀, hhighE⟩ := hhigh C hClo hChi t₀ ht₀ (fun I => (hfixed I).2.2)
  let t₁ : (Fin (ResidueLevels.scale S) → Bool) → ℕ :=
    fun a => sampledProduct (f 0) a
  let I : Finset ℕ := residueIndices (Fin (ResidueLevels.scale S) → Bool)
  have hI : I.Nonempty := residueIndices_nonempty_iff _ |>.mpr inferInstance
  have hIcard : (I.card : ℝ) = (2 : ℝ) ^ ResidueLevels.scale S := by
    simp [I]
  have hpos₀ : ∀ i ∈ I, 0 < residueEntry t₀ i :=
    (forall_residueEntry_iff t₀ (fun t : ℕ => 0 < t)).mpr (fun a => (hfixed a).2.1)
  have hpos₁ : ∀ i ∈ I, 0 < residueEntry t₁ i :=
    (forall_residueEntry_iff _ (fun t : ℕ => 0 < t)).mpr
      (fun a => (hsampled 0 a).2.1)
  have hdvd₀ : ∀ i ∈ I, residueEntry t₀ i ∣ M :=
    (forall_residueEntry_iff t₀ (fun t : ℕ => t ∣ M)).mpr (fun a => (hfixed a).1)
  have hdvd₁ : ∀ i ∈ I, residueEntry t₁ i ∣ M :=
    (forall_residueEntry_iff _ (fun t : ℕ => t ∣ M)).mpr
      (fun a => (hsampled 0 a).1)
  have hrho : Real.exp (-(ResidueLevels.scale S : ℝ) / 10000) = contraction η S := by
    unfold contraction η
    congr 1
    ring
  have herr : Real.exp (-(ResidueLevels.scale S : ℝ) / 1000) =
      Real.exp (-c * ResidueLevels.scale S) := by
    unfold c
    congr 1
    ring
  have hjmiddle (j : ℕ) (hj : j < depth DM η S)
      (hsmall : cutoff DM η S j ≤ Real.exp S) :
      j ∈ GeometricRandomRanges.middleTests (DM + 2) S := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hsmall⟩
  have hdata : NormalizedResidueData DM D₀ η c r S 2 C M := by
    apply residueData_of_two_lists I hI (residueEntry t₀)
      (residueEntry t₁) hpos₀ hpos₁ hdvd₀ hdvd₁ E₀ E₁
    · intro j hj hlarge u hu hnot hunext
      have hx := (hhighE j hj hlarge).2 u hu hnot hunext
      rw [hIcard]
      dsimp only [I]
      rw [card_filter_residueEntry t₀ (fun t : ℕ =>
        Int.fract (-((C * t : ℕ) : ℝ) / u) < contraction η S)]
      exact hx
    · intro j hj hsmall u hu hnot hunext
      have hu' : u ∈ GeometricRandomRanges.middleLevel (DM + 2) S j :=
        Finset.mem_filter.mpr ⟨hu, hunext⟩
      have hx := (hmiddle j (hjmiddle j hj hsmall)).2.2 u hu' hnot
      have hrho' : Real.exp (-(blockLength S : ℝ) / 10000) = contraction η S := hrho
      rw [hrho'] at hx
      have hx' : contraction η S / 2 * (2 : ℝ) ^ ResidueLevels.scale S ≤
          ((Finset.univ.filter (fun a : Fin (ResidueLevels.scale S) → Bool =>
            Int.fract (-(t₁ a : ℝ) / u) < contraction η S)).card : ℝ) := by
        dsimp only [t₁, blockLength, ResidueLevels.scale] at hx ⊢
        exact hx
      exact reindexed_boolean_residue_count t₁ (contraction η S) u hx'
    · intro j hj hlarge
      exact (hhighE j hj hlarge).1
    · intro j hj hsmall
      have hx := (hmiddle j (hjmiddle j hj hsmall)).2.1
      change ((E₁ j).card : ℝ) ≤ cutoff DM η S j *
        Real.exp (-(ResidueLevels.scale S : ℝ) / 1000) at hx
      simpa only [herr] using hx
    · intro j hj t ht htdvd
      apply hmoment C M
      · exact_mod_cast (Real.exp_pos _).trans_le hClo
      · exact_mod_cast (Real.exp_pos _).trans hMlo
      · simpa only [show 2 * (4 * (DM + 2)) * S = 8 * (DM + 2) * S by ring]
          using hChi
      · exact hMhi
      · exact hj
      · exact htdvd
    · intro u huhi hulo
      have huR : (0 : ℝ) < u := (Real.rpow_pos_of_pos hSpos D₀).trans hulo
      have hu : 0 < u := by exact_mod_cast huR
      have hu' : u ∈ GeometricRandomRanges.terminalRange S := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨hu, Nat.le_floor huhi⟩, ?_⟩
        simpa only [D₀, show (100000 : ℝ) = (100000 : ℕ) by norm_num,
          Real.rpow_natCast] using hulo
      obtain ⟨i, a, ha⟩ := hterminal u hu'
      refine ⟨sampledProduct (f i) a, (hsampled i a).2.1, (hsampled i a).1, ?_⟩
      apply (sampledRemainder_lt_iff_fract (f i) u hu a ((u : ℝ) ^ (-η))).mp
      have hpower : (u : ℝ) ^ (-η) * u = (u : ℝ) ^ (9999 / 10000 : ℝ) := by
        calc
          (u : ℝ) ^ (-η) * u = (u : ℝ) ^ (-η) * (u : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = (u : ℝ) ^ (-η + 1) := (Real.rpow_add huR _ _).symm
          _ = (u : ℝ) ^ (9999 / 10000 : ℝ) := by congr 1; norm_num [η]
      simpa only [hpower] using ha
  exact hconstruct C M hClo hMlo hMhi hbinary (hdata.toResidueData hSpos)

/-- The complete quantitative raw-supply family, with no arithmetic or
analytic hypotheses left over. -/
theorem exists_raw_density_supply :
    ∃ DM L c K r : ℝ, 1 < DM ∧ 0 < L ∧ 0 < c ∧ 0 ≤ K ∧
      2 ≤ r ∧ 8 * K ≤ r ∧
      ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
        Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
        (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
        RawDensitySupply DM L c K r S C := by
  exact ⟨RawDensityParameters.DM, RawDensityParameters.L, RawDensityParameters.c,
    RawDensityParameters.K, RawDensityParameters.r, RawDensityParameters.DM_gt_one,
    RawDensityParameters.L_pos, RawDensityParameters.c_pos,
    RawDensityParameters.K_nonneg, RawDensityParameters.r_ge_two,
    RawDensityParameters.eight_K_le_r, eventually_raw_density_supply⟩

end Problem337

end

end OAI
