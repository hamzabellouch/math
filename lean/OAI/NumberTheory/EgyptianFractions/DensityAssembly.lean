import OAI.NumberTheory.EgyptianFractions.DescentDepth
import OAI.NumberTheory.EgyptianFractions.DescentDecay
import OAI.NumberTheory.EgyptianFractions.DescentHolder
import OAI.NumberTheory.EgyptianFractions.BadPredecessorCount
import OAI.NumberTheory.EgyptianFractions.BackwardExpansions
import OAI.NumberTheory.EgyptianFractions.GoodNumeratorSets
import OAI.NumberTheory.EgyptianFractions.DensityLoss

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- The truncated divisor count appearing in the shifted moment hypothesis. -/
def densityDivisorCount (X : ℝ) (N : ℕ) : ℝ :=
  ((N.divisors.filter (fun u : ℕ => (u : ℝ) ≤ X)).card : ℝ)

/-- Explicit finite arithmetic data consumed by the density descent.
No residue-distribution or divisor-moment estimate is asserted by this structure:
these are the `many_residues` and `moment_bound` fields that must be supplied. -/
structure DensityBadFamily (S m ρ r c : ℝ) (d : ℕ) where
  cutoff : ℕ → ℝ
  bad : ℕ → Finset ℕ
  exceptional : ℕ → Finset ℕ
  indices : ℕ → Finset ℕ
  residue : ℕ → ℕ → ℕ → ℕ
  shift : ℕ → ℕ → ℕ
  loss : ℝ
  loss_pos : 0 < loss
  loss_bound : 1 + loss * Real.exp (S ^ (1 / 4 : ℝ) / r) ≤ Real.exp (2 * S ^ (1 / 4 : ℝ))
  cutoff_pos : ∀ j ≤ d, 0 < cutoff j
  cutoff_step : ∀ j < d, cutoff (j + 1) = ρ * cutoff j
  bad_bounded : ∀ j ≤ d, bad j ⊆ Finset.Icc 1 ⌊cutoff j⌋₊
  terminal_empty : bad d = ∅
  indices_nonempty : ∀ j < d, (indices j).Nonempty
  shift_pos : ∀ j < d, ∀ i ∈ indices j, 0 < shift j i
  residue_dvd : ∀ j < d, ∀ i ∈ indices j, ∀ u ∈ bad j,
    u ∣ shift j i + residue j i u
  inherited : ∀ j < d, ∀ u ∈ bad j,
    (u : ℝ) ≤ cutoff (j + 1) → u ∈ bad (j + 1)
  many_residues : ∀ j < d, ∀ u ∈ bad j, u ∉ exceptional j →
    cutoff (j + 1) < (u : ℝ) →
    ρ * ((indices j).card : ℝ) / loss ≤
      (((indices j).filter (fun i => residue j i u ∈ bad (j + 1))).card : ℝ)
  exception_bound : ∀ j < d,
    ((exceptional j).card : ℝ) ≤ cutoff j * Real.exp (-c * m)
  moment_bound : ∀ j < d, ∀ i ∈ indices j,
    (∑ h ∈ Finset.Icc 1 ⌊cutoff (j + 1)⌋₊,
      densityDivisorCount (cutoff j) (shift j i + h) ^ r) ≤
        cutoff (j + 1) * Real.exp (S ^ (1 / 4 : ℝ))

private theorem card_le_cutoff {H : Finset ℕ} {X : ℝ}
    (hX : 0 ≤ X) (hH : H ⊆ Finset.Icc 1 ⌊X⌋₊) : (H.card : ℝ) ≤ X := by
  have hcard : H.card ≤ ⌊X⌋₊ := by
    simpa using Finset.card_le_card hH
  exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le hX)

/-- Pair counting and the actual shifted divisor moment give the normalized
nonlinear recurrence, including inherited bad numerators and list multiplicity. -/
theorem DensityBadFamily.recurrence
    {S m ρ r c : ℝ} {d : ℕ} (F : DensityBadFamily S m ρ r c d)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hr : 1 < r)
    (j : ℕ) (hj : j < d) :
    ((F.bad j).card : ℝ) / F.cutoff j ≤ Real.exp (-c * m) +
      Real.exp (2 * S ^ (1 / 4 : ℝ)) *
        (((F.bad (j + 1)).card : ℝ) / F.cutoff (j + 1)) ^ (1 - 1 / r) := by
  have hjle : j ≤ d := by omega
  have hjnext : j + 1 ≤ d := by omega
  have hX : 0 < F.cutoff j := F.cutoff_pos j hjle
  have hY : 0 < F.cutoff (j + 1) := F.cutoff_pos (j + 1) hjnext
  have hJ : (0 : ℝ) < (F.indices j).card := by
    exact_mod_cast Finset.card_pos.mpr (F.indices_nonempty j hj)
  have hbounded : ∀ u ∈ F.bad j, (u : ℝ) ≤ F.cutoff j := by
    intro u hu
    have huf : u ≤ ⌊F.cutoff j⌋₊ := (Finset.mem_Icc.mp (F.bad_bounded j hjle hu)).2
    exact (Nat.cast_le.mpr huf).trans (Nat.floor_le hX.le)
  have hpair := descent_bad_predecessor_divisor_count_loss (F.bad j) (F.bad (j + 1))
    (F.exceptional j) (F.indices j) (F.cutoff j) (F.cutoff (j + 1)) ρ F.loss
    (F.residue j) (F.shift j) hρ0 F.loss_pos (F.indices_nonempty j hj) hbounded
    (F.shift_pos j hj) (F.residue_dvd j hj) (F.inherited j hj) (F.many_residues j hj)
  change ((F.bad j).card : ℝ) ≤ ((F.exceptional j).card : ℝ) +
    ((F.bad (j + 1)).card : ℝ) + (F.loss / (ρ * (F.indices j).card)) *
      (∑ i ∈ F.indices j, ∑ h ∈ F.bad (j + 1),
        densityDivisorCount (F.cutoff j) (F.shift j i + h)) at hpair
  have hpair' : ((F.bad j).card : ℝ) ≤ F.cutoff j * Real.exp (-c * m) +
    ((F.bad (j + 1)).card : ℝ) + (F.loss / (ρ * (F.indices j).card)) *
      (∑ i ∈ F.indices j, ∑ h ∈ F.bad (j + 1),
        densityDivisorCount (F.cutoff j) (F.shift j i + h)) := by
    exact hpair.trans (add_le_add (add_le_add (F.exception_bound j hj) le_rfl) le_rfl)
  have hsum := indexed_descent_holder_bound (F.indices j)
    (Finset.Icc 1 ⌊F.cutoff (j + 1)⌋₊) (F.bad (j + 1))
    (fun i h => densityDivisorCount (F.cutoff j) (F.shift j i + h))
    (F.cutoff (j + 1)) (S ^ (1 / 4 : ℝ)) r (F.bad_bounded (j + 1) hjnext)
    hY hr (by intros; exact Nat.cast_nonneg _) (F.moment_bound j hj)
  exact descent_recurrence_of_pair_and_moment_loss _ _ _ _ _ _ _ _ _ _ _ hX hρ0 hρ1 hJ
    F.loss_pos.le (F.cutoff_step j hj) (Nat.cast_nonneg _)
    (card_le_cutoff hY.le (F.bad_bounded (j + 1) hjnext)) hr F.loss_bound hpair' hsum

/-- The full counting/analytic density conclusion, conditional on explicit
residue and shifted-divisor-moment data, uniformly in all finite families. -/
theorem eventually_density_bad_card_le_eighth
    (c K r : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (hr : 2 ≤ r) (hKr : 8 * K ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ (m ρ : ℝ) (d : ℕ) (F : DensityBadFamily S m ρ r c d),
      S / (2 * Real.log S) ≤ m → (d : ℝ) ≤ K * Real.log S →
      0 < ρ → ρ ≤ 1 → ((F.bad 0).card : ℝ) ≤ F.cutoff 0 / 8 := by
  filter_upwards [DescentDecay.eventually_descent_bound_le_eighth c K r hc hK
    (by linarith), eventually_gt_atTop (1 : ℝ)] with S hdecay hS
  intro m ρ d F hm hd hρ0 hρ1
  have hS0 : 0 < S := by linarith
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hm0 : 0 ≤ m := le_trans (by positivity) hm
  let δ : ℕ → ℝ := fun j => ((F.bad j).card : ℝ) / F.cutoff j
  have hδd : δ d = 0 := by simp [δ, F.terminal_empty]
  have hδ0 : ∀ j ≤ d, 0 ≤ δ j := by
    intro j hj
    exact div_nonneg (Nat.cast_nonneg _) (F.cutoff_pos j hj).le
  have hbound := descent_density_exp_bound δ d r K S c m hr hKr hS.le hc.le hm0 hd
    hδd hδ0 (fun j hj => F.recurrence hρ0 hρ1 (by linarith) j hj)
  have hsmall : δ 0 ≤ 1 / 8 := hbound.trans (by
    simpa only [neg_div] using hdecay m d hm (Nat.cast_nonneg d) hd)
  have hX : 0 < F.cutoff 0 := F.cutoff_pos 0 (Nat.zero_le d)
  have hcard := (div_le_iff₀ hX).mp hsmall
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hcard

/-- Raw residue data before the good sets are constructed. The terminal
expansions, small-residue supply and shifted divisor moments are explicit
inputs; all finite propagation is proved below. -/
structure DensityResidueFamily (S m ρ r c : ℝ) (d : ℕ) where
  cutoff : ℕ → ℝ
  exceptional : ℕ → Finset ℕ
  indices : ℕ → Finset ℕ
  residue : ℕ → ℕ → ℕ → ℕ
  denominator : ℕ
  factor : ℕ → ℕ
  divisor : ℕ → ℕ → ℕ
  quotient : ℕ → ℕ → ℕ → ℕ
  baseLength : ℕ
  loss : ℝ
  loss_pos : 0 < loss
  loss_bound : 1 + loss * Real.exp (S ^ (1 / 4 : ℝ) / r) ≤ Real.exp (2 * S ^ (1 / 4 : ℝ))
  cutoff_pos : ∀ j ≤ d, 0 < cutoff j
  cutoff_step : ∀ j < d, cutoff (j + 1) = ρ * cutoff j
  denominator_pos : 0 < denominator
  factor_pos : ∀ j ≤ d, 0 < factor j
  factor_dvd : ∀ j < d, factor (j + 1) ∣ factor j
  indices_nonempty : ∀ j < d, (indices j).Nonempty
  divisor_pos : ∀ j < d, ∀ i ∈ indices j, 0 < divisor j i
  divisor_dvd : ∀ j < d, ∀ i ∈ indices j, divisor j i ∣ denominator
  quotient_pos : ∀ j < d, ∀ i ∈ indices j, ∀ u ∈ Finset.Icc 1 ⌊cutoff j⌋₊,
    0 < quotient j i u
  residue_eq : ∀ j < d, ∀ i ∈ indices j, ∀ u ∈ Finset.Icc 1 ⌊cutoff j⌋₊,
    factor j * divisor j i + residue j i u = u * quotient j i u
  many_small_residues : ∀ j < d, ∀ u ∈ Finset.Icc 1 ⌊cutoff j⌋₊,
    u ∉ exceptional j → cutoff (j + 1) < (u : ℝ) →
    ρ * ((indices j).card : ℝ) / loss ≤
      (((indices j).filter (fun i => (residue j i u : ℝ) ≤ cutoff (j + 1))).card : ℝ)
  exception_bound : ∀ j < d,
    ((exceptional j).card : ℝ) ≤ cutoff j * Real.exp (-c * m)
  moment_bound : ∀ j < d, ∀ i ∈ indices j,
    (∑ h ∈ Finset.Icc 1 ⌊cutoff (j + 1)⌋₊,
      densityDivisorCount (cutoff j) (factor j * divisor j i + h) ^ r) ≤
        cutoff (j + 1) * Real.exp (S ^ (1 / 4 : ℝ))
  terminal_expansions : ∀ u ∈ Finset.Icc 1 ⌊cutoff d⌋₊,
    Descent.UnitListAtMost ((u : ℚ) / (denominator * factor d : ℕ)) baseLength

/-- The exact recursive good-set specification needed for both effects of the
construction: closure counts bad residues, and decomposition propagates lists. -/
def DensityResidueFamily.GoodSets
    {S m ρ r c : ℝ} {d : ℕ} (F : DensityResidueFamily S m ρ r c d)
    (G : ℕ → Finset ℕ) : Prop :=
  (∀ j ≤ d, G j ⊆ Finset.Icc 1 ⌊F.cutoff j⌋₊) ∧
  G d = Finset.Icc 1 ⌊F.cutoff d⌋₊ ∧
  (∀ j < d, ∀ u : ℕ, u ∈ G j ↔
    u ∈ Finset.Icc 1 ⌊F.cutoff j⌋₊ ∧
    (u ∈ G (j + 1) ∨ ∃ i ∈ F.indices j,
      F.residue j i u = 0 ∨ F.residue j i u ∈ G (j + 1)))

/-- Every small successful index for a bad numerator lands at a bad numerator
at the next level. In particular a zero residue cannot remain bad. -/
def DensityResidueFamily.toBadFamily
    {S m ρ r c : ℝ} {d : ℕ} (F : DensityResidueFamily S m ρ r c d)
    (G : ℕ → Finset ℕ) (hG : F.GoodSets G) : DensityBadFamily S m ρ r c d := by
  classical
  let H : ℕ → Finset ℕ := fun j => Finset.Icc 1 ⌊F.cutoff j⌋₊ \ G j
  refine {
    cutoff := F.cutoff
    bad := H
    exceptional := F.exceptional
    indices := F.indices
    residue := F.residue
    shift := fun j i => F.factor j * F.divisor j i
    loss := F.loss
    loss_pos := F.loss_pos
    loss_bound := F.loss_bound
    cutoff_pos := F.cutoff_pos
    cutoff_step := F.cutoff_step
    bad_bounded := fun j _ => Finset.sdiff_subset
    terminal_empty := ?_
    indices_nonempty := F.indices_nonempty
    shift_pos := ?_
    residue_dvd := ?_
    inherited := ?_
    many_residues := ?_
    exception_bound := F.exception_bound
    moment_bound := F.moment_bound }
  · simp [H, hG.2.1]
  · intro j hj i hi
    exact Nat.mul_pos (F.factor_pos j (by omega)) (F.divisor_pos j hj i hi)
  · intro j hj i hi u hu
    exact ⟨F.quotient j i u, F.residue_eq j hj i hi u (Finset.mem_sdiff.mp hu).1⟩
  · intro j hj u hu hlow
    obtain ⟨huI, hunG⟩ := Finset.mem_sdiff.mp hu
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp huI).1, Nat.le_floor hlow⟩
    · intro huG
      exact hunG ((hG.2.2 j hj u).mpr ⟨huI, Or.inl huG⟩)
  · intro j hj u hu huE hhigh
    obtain ⟨huI, hunG⟩ := Finset.mem_sdiff.mp hu
    apply (F.many_small_residues j hj u huI huE hhigh).trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hiI, hiSmall⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨hiI, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · have hne : F.residue j i u ≠ 0 := by
        intro hz
        exact hunG ((hG.2.2 j hj u).mpr ⟨huI, Or.inr ⟨i, hiI, Or.inl hz⟩⟩)
      exact Finset.mem_Icc.mpr ⟨by omega, Nat.le_floor hiSmall⟩
    · intro hiG
      exact hunG ((hG.2.2 j hj u).mpr ⟨huI, Or.inr ⟨i, hiI, Or.inr hiG⟩⟩)

/-- The same good-set specification supplies genuine unit-fraction lists;
this is not an additional expansion hypothesis at intermediate levels. -/
theorem DensityResidueFamily.good_expansions
    {S m ρ r c : ℝ} {d : ℕ} (F : DensityResidueFamily S m ρ r c d)
    (G : ℕ → Finset ℕ) (hG : F.GoodSets G) :
    ∀ j ≤ d, ∀ u ∈ G j,
      Descent.UnitListAtMost ((u : ℚ) / (F.denominator * F.factor j : ℕ))
        (F.baseLength + (d - j)) := by
  apply Descent.backward_good_set_expansions F.denominator d F.baseLength F.factor
    (fun j => (G j : Set ℕ)) F.denominator_pos F.factor_pos F.factor_dvd
  · intro u hu
    exact F.terminal_expansions u (hG.2.1 ▸ hu)
  · intro j hj u hu
    obtain ⟨huI, huStep⟩ := (hG.2.2 j hj u).mp hu
    rcases huStep with huNext | ⟨i, hi, hres⟩
    · exact Or.inl huNext
    · exact Or.inr ⟨F.divisor j i, F.quotient j i u, F.residue j i u,
        F.divisor_pos j hj i hi, F.divisor_dvd j hj i hi,
        F.quotient_pos j hj i hi u huI, F.residue_eq j hj i hi u huI, hres⟩

/-- Complete finite/analytic density construction from raw residue and moment
supply. The intermediate good sets and their expansions are constructed here. -/
theorem eventually_residue_family_dense
    (c K r : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (hr : 2 ≤ r) (hKr : 8 * K ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ (m ρ : ℝ) (d : ℕ) (F : DensityResidueFamily S m ρ r c d),
      S / (2 * Real.log S) ≤ m → (d : ℝ) ≤ K * Real.log S →
      0 < ρ → ρ ≤ 1 →
      ∃ G : Finset ℕ, G ⊆ Finset.Icc 1 ⌊F.cutoff 0⌋₊ ∧
        ((Finset.Icc 1 ⌊F.cutoff 0⌋₊ \ G).card : ℝ) ≤ F.cutoff 0 / 8 ∧
        ∀ u ∈ G, Descent.UnitListAtMost
          ((u : ℚ) / (F.denominator * F.factor 0 : ℕ)) (F.baseLength + d) := by
  filter_upwards [eventually_density_bad_card_le_eighth c K r hc hK hr hKr] with S hS
  intro m ρ d F hm hd hρ0 hρ1
  obtain ⟨G, hG⟩ := exists_good_numerator_sets d F.cutoff F.indices F.residue
  have hGood : F.GoodSets G := hG
  refine ⟨G 0, hG.1 0 (Nat.zero_le d), ?_, ?_⟩
  · exact hS m ρ d (F.toBadFamily G hGood) hm hd hρ0 hρ1
  · intro u hu
    simpa using F.good_expansions G hGood 0 (Nat.zero_le d) u hu

/-- Conversion to the list interface used by the elementary dense-family
reduction, retaining the same length bound. -/
theorem Descent.UnitListAtMost.to_density_list_two {x : ℚ} {B : ℕ}
    (H : Descent.UnitListAtMost x B) (hx : x < 1) :
    ∃ l : List ℕ, (∀ n ∈ l, 2 ≤ n) ∧ l.length ≤ B ∧
      (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum = x := by
  obtain ⟨k, hk, n, hn, hsum⟩ := H.denominators_two hx
  refine ⟨List.ofFn n, ?_, by simpa using hk, ?_⟩
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hn i
  · simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using hsum

/-- A directly consumable list version of the density proposition. The only
additional hypotheses are the supplied terminal-length budget and the fact
that all represented fractions lie below one. -/
theorem eventually_residue_family_dense_lists
    (c K r : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (hr : 2 ≤ r) (hKr : 8 * K ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ (m ρ L : ℝ) (d : ℕ) (F : DensityResidueFamily S m ρ r c d),
      S / (2 * Real.log S) ≤ m → (d : ℝ) ≤ K * Real.log S →
      0 < ρ → ρ ≤ 1 →
      ((F.baseLength + d : ℕ) : ℝ) ≤ L * Real.log S →
      F.cutoff 0 < ((F.denominator * F.factor 0 : ℕ) : ℝ) →
      ∃ G : Finset ℕ,
        ((Finset.Icc 1 ⌊F.cutoff 0⌋₊ \ G).card : ℝ) ≤ F.cutoff 0 / 8 ∧
        ∀ u ∈ G, ∃ ds : List ℕ,
          (∀ n ∈ ds, 2 ≤ n) ∧ (ds.length : ℝ) ≤ L * Real.log S ∧
          (ds.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum =
            (u : ℚ) / (F.denominator * F.factor 0 : ℕ) := by
  filter_upwards [eventually_residue_family_dense c K r hc hK hr hKr] with S hS
  intro m ρ L d F hm hd hρ0 hρ1 hlen hfrac
  obtain ⟨G, hGI, hholes, hG⟩ := hS m ρ d F hm hd hρ0 hρ1
  refine ⟨G, hholes, ?_⟩
  intro u hu
  have huX : (u : ℝ) ≤ F.cutoff 0 :=
    (Nat.cast_le.mpr (Finset.mem_Icc.mp (hGI hu)).2).trans
      (Nat.floor_le (F.cutoff_pos 0 (Nat.zero_le d)).le)
  have huD : u < F.denominator * F.factor 0 := by exact_mod_cast huX.trans_lt hfrac
  have hD : (0 : ℚ) < (F.denominator * F.factor 0 : ℕ) := by
    exact_mod_cast Nat.mul_pos F.denominator_pos (F.factor_pos 0 (Nat.zero_le d))
  have huq : (u : ℚ) / (F.denominator * F.factor 0 : ℕ) < 1 :=
    (div_lt_one hD).mpr (by exact_mod_cast huD)
  obtain ⟨ds, hds, hdslen, hdssum⟩ := (hG u hu).to_density_list_two huq
  exact ⟨ds, hds, (Nat.cast_le.mpr hdslen).trans hlen, hdssum⟩

end Problem337

end

end OAI
