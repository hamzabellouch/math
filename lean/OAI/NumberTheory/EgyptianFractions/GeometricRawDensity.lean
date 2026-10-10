import OAI.NumberTheory.EgyptianFractions.RawDensityUpper
import OAI.NumberTheory.EgyptianFractions.ResidueLevels
import OAI.NumberTheory.EgyptianFractions.CeilResidue
import OAI.NumberTheory.EgyptianFractions.TerminalFiniteBudget

namespace OAI
noncomputable section

open Filter
open scoped BigOperators

namespace Problem337

/-- A positive integer shift has a positive natural ceiling quotient. -/
lemma positive_ceiling_quotient {N u : ℕ} (hN : 0 < N) (hu : 0 < u) :
    0 < ⌈(N : ℝ) / u⌉₊ := by
  have hNu : (0 : ℝ) < (N : ℝ) / u := div_pos (by exact_mod_cast hN)
    (by exact_mod_cast hu)
  exact Nat.ceil_pos.mpr hNu

/-- A normalized small negative residue gives the unnormalized ceiling bound
used by the backward construction. The cutoff need not be integral. -/
lemma ceiling_residue_le_of_fract_lt {N u : ℕ} {ρ X : ℝ}
    (hu : 0 < u) (hρ : 0 ≤ ρ) (huX : (u : ℝ) ≤ X)
    (hsmall : Int.fract (-(N : ℝ) / u) < ρ) :
    ((u * ⌈(N : ℝ) / u⌉₊ - N : ℕ) : ℝ) ≤ ρ * X := by
  rw [← natural_ceil_residue_div_eq_fract_neg u N hu] at hsmall
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  exact ((div_lt_iff₀ huR).mp hsmall).le.trans
    (mul_le_mul_of_nonneg_left huX hρ)

/-- The terminal normalized residue condition gives a genuine power-saving
integer residue step, including the case of residue zero. -/
lemma terminal_step_of_fract_lt {t u : ℕ} {η : ℝ}
    (ht : 0 < t) (hu : 0 < u)
    (hsmall : Int.fract (-(t : ℝ) / u) < (u : ℝ) ^ (-η)) :
    ∃ z h : ℕ, 0 < z ∧ (h : ℝ) ≤ (u : ℝ) ^ (1 - η) ∧
      t + h = u * z := by
  obtain ⟨_, heq, _⟩ := natural_ceil_residue_spec u t hu
  refine ⟨⌈(t : ℝ) / u⌉₊, u * ⌈(t : ℝ) / u⌉₊ - t,
    positive_ceiling_quotient ht hu, ?_, heq.symm⟩
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have h := ceiling_residue_le_of_fract_lt hu
    (Real.rpow_pos_of_pos huR (-η)).le (le_refl (u : ℝ)) hsmall
  have hp : (u : ℝ) ^ (-η) * u = (u : ℝ) ^ (1 - η) := by
    calc
      (u : ℝ) ^ (-η) * u = (u : ℝ) ^ (-η) * (u : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (u : ℝ) ^ (-η + 1) := (Real.rpow_add huR _ _).symm
      _ = (u : ℝ) ^ (1 - η) := by congr 1; ring
  simpa only [hp] using h

namespace GeometricDensity

abbrev depth (DM η S : ℝ) : ℕ :=
  ResidueLevels.depth ((DM + 2) * S) (ResidueLevels.scale S) η

abbrev cutoff (DM η S : ℝ) (j : ℕ) : ℝ :=
  ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η j

abbrev factor (DM η S : ℝ) (C j : ℕ) : ℕ :=
  ResidueLevels.factor ((DM + 2) * S) (ResidueLevels.scale S) η S C j

abbrev contraction (η S : ℝ) : ℝ := Real.exp (-η * ResidueLevels.scale S)

/-- Arithmetic residue information on the canonical geometric levels.
The normalized Fourier conclusion, exceptional count, shifted-divisor moment,
and terminal shrinking residue remain explicit hypotheses. All geometric
alignment, ceiling equations, and expansion construction are supplied below. -/
structure NormalizedResidueData (DM D₀ η c r S loss : ℝ) (C M : ℕ) where
  indices : ℕ → Finset ℕ
  divisor : ℕ → ℕ → ℕ
  exceptional : ℕ → Finset ℕ
  indices_nonempty : ∀ j < depth DM η S, (indices j).Nonempty
  divisor_pos : ∀ j < depth DM η S, ∀ i ∈ indices j, 0 < divisor j i
  divisor_dvd : ∀ j < depth DM η S, ∀ i ∈ indices j, divisor j i ∣ M
  many_residues : ∀ j < depth DM η S, ∀ u ∈ Finset.Icc 1 ⌊cutoff DM η S j⌋₊,
    u ∉ exceptional j → cutoff DM η S (j + 1) < (u : ℝ) →
    contraction η S * ((indices j).card : ℝ) / loss ≤
      (((indices j).filter (fun i =>
        Int.fract (-((factor DM η S C j * divisor j i : ℕ) : ℝ) / u) <
          contraction η S)).card : ℝ)
  exception_bound : ∀ j < depth DM η S,
    ((exceptional j).card : ℝ) ≤ cutoff DM η S j *
      Real.exp (-c * ResidueLevels.scale S)
  moment_bound : ∀ j < depth DM η S, ∀ i ∈ indices j,
    (∑ h ∈ Finset.Icc 1 ⌊cutoff DM η S (j + 1)⌋₊,
      densityDivisorCount (cutoff DM η S j)
        (factor DM η S C j * divisor j i + h) ^ r) ≤
      cutoff DM η S (j + 1) * Real.exp (S ^ (1 / 4 : ℝ))
  terminal_residue : ∀ u : ℕ, (u : ℝ) ≤ Real.exp (ResidueLevels.scale S) →
    S ^ D₀ < (u : ℝ) → ∃ t : ℕ, 0 < t ∧ t ∣ M ∧
      Int.fract (-(t : ℝ) / u) < (u : ℝ) ^ (-η)

/-- The weaker, directly consumable arithmetic data: only actual ceiling
residues are bounded. In particular a non-strict residue bound is sufficient. -/
structure ResidueData (DM D₀ η c r S loss : ℝ) (C M : ℕ) where
  indices : ℕ → Finset ℕ
  divisor : ℕ → ℕ → ℕ
  exceptional : ℕ → Finset ℕ
  indices_nonempty : ∀ j < depth DM η S, (indices j).Nonempty
  divisor_pos : ∀ j < depth DM η S, ∀ i ∈ indices j, 0 < divisor j i
  divisor_dvd : ∀ j < depth DM η S, ∀ i ∈ indices j, divisor j i ∣ M
  many_residues : ∀ j < depth DM η S, ∀ u ∈ Finset.Icc 1 ⌊cutoff DM η S j⌋₊,
    u ∉ exceptional j → cutoff DM η S (j + 1) < (u : ℝ) →
    contraction η S * ((indices j).card : ℝ) / loss ≤
      (((indices j).filter (fun i =>
        ((u * ⌈((factor DM η S C j * divisor j i : ℕ) : ℝ) / u⌉₊ -
          factor DM η S C j * divisor j i : ℕ) : ℝ) ≤ cutoff DM η S (j + 1))).card : ℝ)
  exception_bound : ∀ j < depth DM η S,
    ((exceptional j).card : ℝ) ≤ cutoff DM η S j *
      Real.exp (-c * ResidueLevels.scale S)
  moment_bound : ∀ j < depth DM η S, ∀ i ∈ indices j,
    (∑ h ∈ Finset.Icc 1 ⌊cutoff DM η S (j + 1)⌋₊,
      densityDivisorCount (cutoff DM η S j)
        (factor DM η S C j * divisor j i + h) ^ r) ≤
      cutoff DM η S (j + 1) * Real.exp (S ^ (1 / 4 : ℝ))
  terminal_residue : ∀ u : ℕ, (u : ℝ) ≤ Real.exp (ResidueLevels.scale S) →
    S ^ D₀ < (u : ℝ) → ∃ t : ℕ, 0 < t ∧ t ∣ M ∧
      ((u * ⌈(t : ℝ) / u⌉₊ - t : ℕ) : ℝ) ≤ (u : ℝ) ^ (1 - η)

/-- A normalized strict discrepancy conclusion implies the weaker ceiling
residue interface, without demanding a strict inequality from later consumers. -/
def NormalizedResidueData.toResidueData {DM D₀ η c r S loss : ℝ} {C M : ℕ}
    (H : NormalizedResidueData DM D₀ η c r S loss C M) (hS : 0 < S) :
    ResidueData DM D₀ η c r S loss C M := by
  refine {
    indices := H.indices
    divisor := H.divisor
    exceptional := H.exceptional
    indices_nonempty := H.indices_nonempty
    divisor_pos := H.divisor_pos
    divisor_dvd := H.divisor_dvd
    many_residues := ?_
    exception_bound := H.exception_bound
    moment_bound := H.moment_bound
    terminal_residue := ?_ }
  · intro j hj u hu huE hhigh
    apply (H.many_residues j hj u hu huE hhigh).trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hi, hsmall⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hi, ?_⟩
    have huX : (u : ℝ) ≤ cutoff DM η S j :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hu).2).trans
        (Nat.floor_le (ResidueLevels.level_pos _ _ _ j).le)
    have hsmall' := ceiling_residue_le_of_fract_lt (Finset.mem_Icc.mp hu).1
      (Real.exp_pos _).le huX hsmall
    simpa only [cutoff, contraction, ResidueLevels.level_succ] using hsmall'
  · intro u hu hSu
    obtain ⟨t, ht, htM, hsmall⟩ := H.terminal_residue u hu hSu
    have huR : (0 : ℝ) < u := (Real.rpow_pos_of_pos hS D₀).trans hSu
    have hu0 : 0 < u := by exact_mod_cast huR
    have hh := ceiling_residue_le_of_fract_lt hu0
      (Real.rpow_pos_of_pos huR (-η)).le (le_refl (u : ℝ)) hsmall
    have hp : (u : ℝ) ^ (-η) * u = (u : ℝ) ^ (1 - η) := by
      calc
        (u : ℝ) ^ (-η) * u = (u : ℝ) ^ (-η) * (u : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = (u : ℝ) ^ (-η + 1) := (Real.rpow_add huR _ _).symm
        _ = (u : ℝ) ^ (1 - η) := by congr 1; ring
    exact ⟨t, ht, htM, by simpa only [hp] using hh⟩

/-- Construct the exact raw family from ceiling residue information at the
canonical levels. This definition discharges every ceiling, divisibility,
terminal-expansion, and geometric-transition field. -/
def ResidueData.toFamily {DM D₀ η c r S loss : ℝ} {C M : ℕ}
    (H : ResidueData DM D₀ η c r S loss C M)
    (hDM : 1 < DM) (hD₀ : 1 ≤ D₀) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hS : 1 ≤ S) (hlog : 1 ≤ Real.log S) (hscale : 2 ≤ ResidueLevels.scale S)
    (hC : 0 < C) (hM : Real.exp S < (M : ℝ))
    (hbinary : 2 ^ TerminalDepth.binaryExponent D₀ S ∣ M)
    (hloss : 0 < loss)
    (hloss_bound : 1 + loss * Real.exp (S ^ (1 / 4 : ℝ) / r) ≤
      Real.exp (2 * S ^ (1 / 4 : ℝ))) :
    DensityResidueFamily S (ResidueLevels.scale S) (contraction η S) r c
      (depth DM η S) := by
  have hSpos : 0 < S := by linarith
  have hm : (0 : ℝ) < ResidueLevels.scale S := by exact_mod_cast (by omega :
    0 < ResidueLevels.scale S)
  have hmS : (ResidueLevels.scale S : ℝ) ≤ S :=
    ResidueLevels.scale_le_self hSpos.le hlog
  have hmA : (ResidueLevels.scale S : ℝ) ≤ (DM + 2) * S := by nlinarith
  have hα : 0 < 1 - η := by linarith
  have hα1 : 1 - η < 1 := by linarith
  have hMpos : 0 < M := by
    exact_mod_cast (Real.exp_pos S).trans hM
  have hfinal : cutoff DM η S (depth DM η S) ≤ Real.exp (ResidueLevels.scale S) :=
    (ResidueLevels.final_level_bounds hm hη hmA).2
  have hfinalS : cutoff DM η S (depth DM η S) ≤ Real.exp S :=
    hfinal.trans (Real.exp_le_exp.mpr hmS)
  have hfactor : factor DM η S C (depth DM η S) = 1 :=
    ResidueLevels.final_factor_one hm hη hmA hmS C
  have hterminal := TerminalAssembly.terminal_finite_expansions M
    (cutoff DM η S (depth DM η S)) D₀ (1 - η) S
    (ResidueLevels.level_pos _ _ _ _).le (hfinalS.trans_lt hM) hfinalS
    hD₀ hα hα1 hS hlog hbinary (by
      intro u hu hSu
      obtain ⟨t, ht, htM, hsmall⟩ := H.terminal_residue u (hu.trans hfinal) hSu
      have hu0 : 0 < u := by
        exact_mod_cast (Real.rpow_pos_of_pos hSpos D₀).trans hSu
      refine ⟨t, ⌈(t : ℝ) / u⌉₊, u * ⌈(t : ℝ) / u⌉₊ - t,
        ht, positive_ceiling_quotient ht hu0, htM, hsmall, ?_⟩
      exact (natural_ceil_residue_spec u t hu0).2.1.symm)
  refine {
    cutoff := cutoff DM η S
    exceptional := H.exceptional
    indices := H.indices
    residue := fun j i u =>
      u * ⌈((factor DM η S C j * H.divisor j i : ℕ) : ℝ) / u⌉₊ -
        factor DM η S C j * H.divisor j i
    denominator := M
    factor := factor DM η S C
    divisor := H.divisor
    quotient := fun j i u =>
      ⌈((factor DM η S C j * H.divisor j i : ℕ) : ℝ) / u⌉₊
    baseLength := ⌈TerminalAssembly.terminalCoefficient D₀ (1 - η) * Real.log S⌉₊
    loss := loss
    loss_pos := hloss
    loss_bound := hloss_bound
    cutoff_pos := fun j _ => ResidueLevels.level_pos _ _ _ j
    cutoff_step := fun j _ => ResidueLevels.level_succ _ _ _ j
    denominator_pos := hMpos
    factor_pos := fun j _ => ResidueLevels.factor_pos hC j
    factor_dvd := fun j _ => ResidueLevels.next_factor_dvd hm hη C j
    indices_nonempty := H.indices_nonempty
    divisor_pos := H.divisor_pos
    divisor_dvd := H.divisor_dvd
    quotient_pos := ?_
    residue_eq := ?_
    many_small_residues := H.many_residues
    exception_bound := H.exception_bound
    moment_bound := H.moment_bound
    terminal_expansions := ?_ }
  · intro j hj i hi u hu
    have hu0 : 0 < u := (Finset.mem_Icc.mp hu).1
    exact positive_ceiling_quotient
      (Nat.mul_pos (ResidueLevels.factor_pos hC j) (H.divisor_pos j hj i hi)) hu0
  · intro j hj i hi u hu
    exact (natural_ceil_residue_spec u
      (factor DM η S C j * H.divisor j i) (Finset.mem_Icc.mp hu).1).2.1.symm
  · intro u hu
    simpa only [hfactor, mul_one] using hterminal u hu

/-- The concrete geometric construction meets the raw upper-bound interface.
Only the arithmetic input data, denominator size, and the displayed loss
estimate are assumed; the depth and rounded terminal length are proved. -/
theorem raw_density_supply_of_geometric_residues
    {DM D₀ η c r S loss : ℝ} {C M : ℕ}
    (H : ResidueData DM D₀ η c r S loss C M)
    (hDM : 1 < DM) (hD₀ : 1 ≤ D₀) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hS : 1 ≤ S) (hlog : 1 ≤ Real.log S) (hscale : 2 ≤ ResidueLevels.scale S)
    (hscale_lower : S / (2 * Real.log S) ≤ (ResidueLevels.scale S : ℝ))
    (hC : 0 < C) (hM : Real.exp S < (M : ℝ))
    (hMupper : (M : ℝ) ≤ Real.exp (DM * S))
    (hbinary : 2 ^ TerminalDepth.binaryExponent D₀ S ∣ M)
    (hloss : 0 < loss)
    (hloss_bound : 1 + loss * Real.exp (S ^ (1 / 4 : ℝ) / r) ≤
      Real.exp (2 * S ^ (1 / 4 : ℝ))) :
    RawDensitySupply DM
      (TerminalAssembly.terminalCoefficient D₀ (1 - η) + 3 * (DM + 2) / η + 1)
      c (3 * (DM + 2) / η) r S C := by
  have hSpos : 0 < S := by linarith
  have hm : (0 : ℝ) < ResidueLevels.scale S := by exact_mod_cast (by omega :
    0 < ResidueLevels.scale S)
  have hmS := ResidueLevels.scale_le_self hSpos.le hlog
  have hmA : (ResidueLevels.scale S : ℝ) ≤ (DM + 2) * S := by nlinarith
  have hηone : η ≤ 1 := by linarith
  have hd : (depth DM η S : ℝ) ≤ (3 * (DM + 2) / η) * Real.log S :=
    ResidueLevels.depth_log_bound hSpos hlog (by linarith) hm hη hηone
      hscale_lower hmA
  let F := H.toFamily hDM hD₀ hη hηhalf hS hlog hscale hC hM hbinary
    hloss hloss_bound
  refine ⟨ResidueLevels.scale S, contraction η S, depth DM η S, F,
    hscale_lower, hd, Real.exp_pos _, ?_, ?_, ?_, ?_, hM, hMupper⟩
  · apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hη.le) hm.le
  · exact TerminalAssembly.terminal_finite_total_budget hD₀
      (by linarith) (by linarith) hlog hd
  · exact ResidueLevels.level_zero _ _ _
  · exact ResidueLevels.factor_zero (by linarith) hSpos C

end GeometricDensity

end Problem337

end

end OAI
