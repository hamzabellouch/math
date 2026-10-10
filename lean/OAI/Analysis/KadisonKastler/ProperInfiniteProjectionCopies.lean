import OAI.Analysis.KadisonKastler.InfiniteFactorProperInfiniteness
import OAI.Analysis.KadisonKastler.ProjectionSchroederBernstein

namespace OAI

/-! # Countable copies of a full projection

A maximal orthogonal family with sources under a full projection gives a
countable partition of the identity.  Two orthogonal isometries provide
room for countably many copies of the full projection.  The partition
embeds into their sum, and concrete projection Schroeder--Bernstein moves
that sum onto the identity.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped BigOperators Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

private theorem exists_link_of_full (p q : AlgebraProjection M)
    (hp : (centralSupport p).val = 1) (hq : q.val ≠ 0) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧ v.support.val ≠ 0 := by
  have ha : ∃ a : Algebra M, q.val * a * p.val ≠ 0 := by
    by_contra h
    have hz : ∀ a : Algebra M, q.val * a * p.val = 0 := by
      simpa only [not_exists, not_not] using h
    have hh := mul_centralSupport_eq_zero_of_no_links p q hz
    rw [hp, mul_one] at hh
    exact hq hh
  obtain ⟨a, ha⟩ := ha
  apply exists_partialIsometry_of_link p q (q.val * a * p.val)
  · rw [mul_assoc, p.property.isIdempotentElem.eq]
  · rw [← mul_assoc, ← mul_assoc, q.property.isIdempotentElem.eq]
  · exact ha

private def fullSourceFamily (p : AlgebraProjection M)
    (s : Set (PartialIsometry M)) : Prop :=
  (∀ v ∈ s, v.support ≤ p ∧ v.support.val ≠ 0) ∧
    s.Pairwise (fun v w => v.target.val * w.target.val = 0)

private theorem exists_maximal_fullSourceFamily (p : AlgebraProjection M) :
    ∃ s : Set (PartialIsometry M), Maximal (fullSourceFamily p) s := by
  apply zorn_subset
  intro c hc hchain
  refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
  constructor
  · intro v hv
    obtain ⟨s, hs, hvs⟩ := Set.mem_sUnion.mp hv
    exact (hc hs).1 v hvs
  · intro v hv w hw hvw
    obtain ⟨s, hs, hvs⟩ := Set.mem_sUnion.mp hv
    obtain ⟨t, ht, hwt⟩ := Set.mem_sUnion.mp hw
    rcases hchain.total hs ht with hst | hts
    · exact (hc ht).2 (hst hvs) hwt hvw
    · exact (hc hs).2 hvs (hts hwt) hvw

private theorem nonzero_target (v : PartialIsometry M)
    (hv : v.support.val ≠ 0) : v.target.val ≠ 0 := by
  intro hz
  have he := v.target_mul
  rw [hz, zero_mul] at he
  have hi := v.initial
  rw [← he, star_zero, zero_mul] at hi
  exact hv hi.symm

/-- A full projection is the source bound for a countable orthogonal
partition of the identity, even when the algebra is not a factor. -/
theorem exists_countable_source_partition_of_full [TopologicalSpace.SeparableSpace H]
    (p : AlgebraProjection M) (hp : (centralSupport p).val = 1) :
    ∃ a : ℕ → PartialIsometry M,
      (∀ n, (a n).support ≤ p) ∧
      Pairwise (fun i j => (a i).target.val * (a j).target.val = 0) ∧
      (∀ q : AlgebraProjection M, (∀ n, (a n).target ≤ q) →
        (1 : Algebra M) = q.val) := by
  classical
  obtain ⟨s, hs, hmax⟩ := exists_maximal_fullSourceFamily p
  have hcount : Countable s := countable_of_orthogonal_nonzero_projections
    (fun v : s => v.val.target)
    (fun v => nonzero_target v.val ((hs.1 v.val v.property).2))
    (fun v w hvw => hs.2 v.property w.property (fun he => hvw (Subtype.ext he)))
  let : Encodable s := @Encodable.ofCountable s hcount
  let a (n : ℕ) : PartialIsometry M :=
    (Encodable.decode₂ s n).elim PartialIsometry.zero (fun v => v.val)
  have ha (v : s) : a (Encodable.encode v) = v.val := by
    simp only [a, Encodable.decode₂_encode, Option.elim_some]
  have has (n : ℕ) : a n = PartialIsometry.zero ∨ a n ∈ s := by
    unfold a
    cases h : Encodable.decode₂ s n with
    | none => exact Or.inl rfl
    | some v => exact Or.inr v.property
  have hap (n : ℕ) : (a n).support ≤ p := by
    rcases has n with h | h
    · rw [h]
      change p.val * 0 = 0
      exact mul_zero _
    · exact (hs.1 _ h).1
  have hao : Pairwise (fun i j => (a i).target.val * (a j).target.val = 0) := by
    intro i j hij
    unfold a
    cases hi : Encodable.decode₂ s i with
    | none => simp [PartialIsometry.zero, PartialIsometry.target]
    | some v =>
      cases hj : Encodable.decode₂ s j with
      | none => simp [PartialIsometry.zero, PartialIsometry.target]
      | some w =>
        apply hs.2 v.property w.property
        intro hvw
        have hvwe : v = w := Subtype.ext hvw
        have hvi := Encodable.decode₂_eq_some.mp hi
        have hwj := Encodable.decode₂_eq_some.mp hj
        exact hij (hvi.symm.trans (congrArg Encodable.encode hvwe |>.trans hwj))
  refine ⟨a, hap, hao, ?_⟩
  intro q hq
  by_contra hne
  let r : AlgebraProjection M := ⟨1 - q.val, q.property.one_sub⟩
  have hr : r.val ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨v, hvp, hvr, hv0⟩ := exists_link_of_full p r hp hr
  have hsq (w : PartialIsometry M) (hw : w ∈ s) : w.target ≤ q := by
    simpa only [ha ⟨w, hw⟩] using hq (Encodable.encode (⟨w, hw⟩ : s))
  have hov (w : PartialIsometry M) (hw : w ∈ s) :
      v.target.val * w.target.val = 0 := by
    have hrq : r.val * q.val = 0 := by
      change (1 - q.val) * q.val = 0
      rw [sub_mul, one_mul, q.property.isIdempotentElem.eq, sub_self]
    exact projection_orthogonal_of_le hrq hvr (hsq w hw)
  have hnew : fullSourceFamily p (insert v s) := by
    constructor
    · intro w hw
      rcases Set.mem_insert_iff.mp hw with rfl | hw
      · exact ⟨hvp, hv0⟩
      · exact hs.1 w hw
    · intro w hw z hz hwz
      rcases Set.mem_insert_iff.mp hw with hw | hw
      · subst w
        rcases Set.mem_insert_iff.mp hz with hz | hz
        · subst z
          exact (hwz rfl).elim
        · exact hov z hz
      · rcases Set.mem_insert_iff.mp hz with hz | hz
        · subst z
          exact PartialIsometry.orthogonal_reverse _ _ (hov w hw)
        · exact hs.2 hw hz hwz
  have hvs : v ∈ s := hmax hnew (Set.subset_insert v s) (Set.mem_insert v s)
  have hz : v.target.val * v.target.val = 0 := hov v hvs
  rw [v.target.property.isIdempotentElem.eq] at hz
  exact nonzero_target v hv0 hz

private def finiteProjectionSum (p : ℕ → AlgebraProjection M)
    (ho : Pairwise (fun i j => (p i).val * (p j).val = 0))
    (s : Finset ℕ) : AlgebraProjection M :=
  AlgebraProjection.finsetSum p s (fun _ _ _ _ hij => ho hij)

/-- Orthogonal projection sums are strong sums in the original representation. -/
theorem exists_orthogonal_projection_sum (p : ℕ → AlgebraProjection M)
    (ho : Pairwise (fun i j => (p i).val * (p j).val = 0)) :
    ∃ q : AlgebraProjection M, (∀ i, p i ≤ q) ∧
      (∀ r : AlgebraProjection M, (∀ i, p i ≤ r) → q ≤ r) ∧
      ∀ x : H, HasSum (fun i => ((p i).val : H →L[ℂ] H) x)
        ((q.val : H →L[ℂ] H) x) := by
  let a := finiteProjectionSum p ho
  have ha : Monotone a := by
    intro s t hst
    apply (AlgebraProjection.finsetSum_le_iff p s _ _).mpr
    intro i hi
    exact (AlgebraProjection.finsetSum_le_iff p t _ _).mp le_rfl i (hst hi)
  obtain ⟨q, hq⟩ := AlgebraProjection.exists_isLUB_monotone a ha
  refine ⟨q, ?_, ?_, ?_⟩
  · intro i
    have hi : p i ≤ a {i} :=
      (AlgebraProjection.finsetSum_le_iff p {i} _ _).mp le_rfl i (by simp)
    exact hi.trans (hq.1 ⟨{i}, rfl⟩)
  · intro r hr
    apply hq.2
    rintro _ ⟨s, rfl⟩
    exact (AlgebraProjection.finsetSum_le_iff p s _ r).mpr (fun i _ => hr i)
  · intro x
    have hv := AlgebraProjection.vectorValue_tendsto_monotone a ha q hq x
    have hs (s : Finset ℕ) :
        ‖(q.val : H →L[ℂ] H) x - ((a s).val : H →L[ℂ] H) x‖ ^ 2 =
          AlgebraProjection.vectorValue x q - AlgebraProjection.vectorValue x (a s) := by
      have hh := AlgebraProjection.vectorValue_remainder x (a s) q (hq.1 ⟨s, rfl⟩)
      rw [AlgebraProjection.vectorValue_eq_norm_sq] at hh
      exact hh
    have hc : Tendsto (fun _ : Finset ℕ => AlgebraProjection.vectorValue x q)
        atTop (𝓝 (AlgebraProjection.vectorValue x q)) := tendsto_const_nhds
    have hh := hc.sub hv
    rw [sub_self] at hh
    have hsquare := hh.congr (fun s => (hs s).symm)
    have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    have hnorm : Tendsto (fun s : Finset ℕ =>
        ‖((a s).val : H →L[ℂ] H) x - (q.val : H →L[ℂ] H) x‖) atTop (𝓝 0) := by
      simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
        Real.sqrt_zero, norm_sub_rev, Function.comp_def] using hn
    have ht := tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
    have ha_apply (s : Finset ℕ) :
        ((a s).val : H →L[ℂ] H) x = ∑ i ∈ s, ((p i).val : H →L[ℂ] H) x := by
      change (M.toStarSubalgebra.subtype (∑ i ∈ s, (p i).val)) x = _
      rw [map_sum]
      simp only [sum_apply]
      rfl
    simpa only [HasSum, SummationFilter.unconditional, ha_apply] using ht

private theorem isometry_power (u : Algebra M) (hu : star u * u = 1) (n : ℕ) :
    star (u ^ n) * u ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, star_mul]
    calc
      _ = star u * (star (u ^ n) * u ^ n) * u := by simp only [mul_assoc]
      _ = 1 := by rw [ih, mul_one, hu]

private def copySlot (u v : Algebra M) (hu : star u * u = 1)
    (hv : star v * v = 1) (p : AlgebraProjection M) (n : ℕ) : PartialIsometry M where
  support := p
  val := u ^ n * v * p.val
  initial := by
    rw [star_mul, star_mul, p.property.isSelfAdjoint.star_eq]
    calc
      _ = p.val * star v * (star (u ^ n) * u ^ n) * v * p.val := by
        simp only [mul_assoc]
      _ = p.val := by
        rw [isometry_power u hu, mul_one]
        calc
          _ = p.val * (star v * v) * p.val := by simp only [mul_assoc]
          _ = p.val := by rw [hv, mul_one, p.property.isIdempotentElem.eq]

private theorem copySlot_cross (u v : Algebra M) (hu : star u * u = 1)
    (hv : star v * v = 1) (huv : star u * v = 0) (p : AlgebraProjection M)
    {i j : ℕ} (hij : i < j) :
    star (copySlot u v hu hv p i).val * (copySlot u v hu hv p j).val = 0 := by
  have hvu : star v * u = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star huv
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hij)
  have hk : 0 < k := by omega
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  change star (u ^ i * v * p.val) * (u ^ (i + (l + 1)) * v * p.val) = 0
  rw [star_mul, star_mul, p.property.isSelfAdjoint.star_eq, pow_add]
  calc
    _ = p.val * star v * (star (u ^ i) * u ^ i) * u ^ (l + 1) * v * p.val := by
      simp only [mul_assoc]
    _ = 0 := by
      rw [isometry_power u hu, mul_one, pow_succ']
      calc
        _ = p.val * (star v * u) * u ^ l * v * p.val := by simp only [mul_assoc]
        _ = 0 := by rw [hvu, mul_zero, zero_mul, zero_mul, zero_mul]

private theorem copySlot_orthogonal (u v : Algebra M) (hu : star u * u = 1)
    (hv : star v * v = 1) (huv : star u * v = 0) (p : AlgebraProjection M) :
    Pairwise (fun i j => (copySlot u v hu hv p i).target.val *
      (copySlot u v hu hv p j).target.val = 0) := by
  have hh {i j : ℕ} (hij : i < j) :
      (copySlot u v hu hv p i).target.val * (copySlot u v hu hv p j).target.val = 0 := by
    change ((copySlot u v hu hv p i).val * star (copySlot u v hu hv p i).val) *
      ((copySlot u v hu hv p j).val * star (copySlot u v hu hv p j).val) = 0
    calc
      _ = (copySlot u v hu hv p i).val *
          (star (copySlot u v hu hv p i).val * (copySlot u v hu hv p j).val) *
          star (copySlot u v hu hv p j).val := by simp only [mul_assoc]
      _ = 0 := by rw [copySlot_cross u v hu hv huv p hij, mul_zero, zero_mul]
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hh h
  · exact PartialIsometry.orthogonal_reverse _ _ (hh h)

/-- Countably many copies of a full projection fill a properly infinite,
separably acting algebra. All the witnesses lie in the original algebra. -/
theorem exists_countable_projection_copies [TopologicalSpace.SeparableSpace H]
    (hM : ProperlyInfiniteIdentity M) (p : AlgebraProjection M)
    (hp : (centralSupport p).val = 1) : Nonempty (CountableProjectionCopies M p) := by
  obtain ⟨u, v, hu, hv, huv⟩ := hM.isometries
  let slot := copySlot u v hu hv p
  have ho : Pairwise (fun i j => (slot i).target.val * (slot j).target.val = 0) :=
    copySlot_orthogonal u v hu hv huv p
  obtain ⟨q, hq, _, hsum⟩ := exists_orthogonal_projection_sum (fun i => (slot i).target) ho
  obtain ⟨a, ha, hao, hatotal⟩ := exists_countable_source_partition_of_full p hp
  let b (n : ℕ) : PartialIsometry M := (slot n).compose (a n).adjoint (by
    rw [PartialIsometry.adjoint_target]
    exact ha n)
  have hbs (n : ℕ) : (b n).support = (a n).target := rfl
  have hbt (n : ℕ) : (b n).target ≤ (slot n).target :=
    PartialIsometry.compose_target_le _ _ _
  obtain ⟨B, _, hBs, hBt⟩ := PartialIsometry.traceFree_orthogonal_sum b
    (by intro i j hij; rw [hbs, hbs]; exact hao hij)
    (by intro i j hij; exact projection_orthogonal_of_le (ho hij) (hbt i) (hbt j))
  let oneP : AlgebraProjection M := ⟨1, IsStarProjection.one _⟩
  have hB1 : B.support = oneP := Subtype.ext (hatotal _ (fun n => by
    simpa only [hbs] using (hBs B.support).mp le_rfl n)).symm
  have hBq : B.target ≤ q := (hBt _).mpr (fun n => (hbt n).trans (hq n))
  have hq1 : q ≤ oneP := by change 1 * q.val = q.val; exact one_mul _
  obtain ⟨c, hcq, hc1⟩ := AlgebraProjection.equivalent_of_le_of_subequivalent hq1
    (show oneP.Subequivalent q from ⟨B, hB1, hBq⟩)
  let z (n : ℕ) := c.compose (slot n) (by rw [hcq]; exact hq n)
  have hzi (n : ℕ) : star (z n).val * (z n).val = p.val := (z n).initial
  have hzf (n : ℕ) : (z n).target.val = c.val * (slot n).target.val * star c.val :=
    PartialIsometry.compose_target c (slot n) _
  refine ⟨{ projection := fun n => (z n).target
            witness := fun n => (z n).val
            initial := hzi
            final := fun _ => rfl
            orthogonal := ?_
            total := ?_ }⟩
  · intro i j hij
    rw [hzf, hzf]
    calc
      _ = c.val * (slot i).target.val * (star c.val * c.val) *
          (slot j).target.val * star c.val := by simp only [mul_assoc]
      _ = 0 := by
        rw [c.initial, hcq]
        calc
          _ = c.val * ((slot i).target.val * q.val) * (slot j).target.val *
              star c.val := by simp only [mul_assoc]
          _ = c.val * ((slot i).target.val * (slot j).target.val) * star c.val := by
            rw [projection_mul_of_le (hq i)]
            simp only [mul_assoc]
          _ = 0 := by rw [ho hij, mul_zero, zero_mul]
  · intro x
    have hs := (c.val : H →L[ℂ] H).hasSum (hsum ((star c.val : H →L[ℂ] H) x))
    have hcx : (c.val : H →L[ℂ] H) ((q.val : H →L[ℂ] H)
        ((star c.val : H →L[ℂ] H) x)) = x := by
      have hmul : c.val * q.val = c.val := by rw [← hcq]; exact c.mul_support
      have hfinal : c.val * star c.val = 1 := congrArg Subtype.val hc1
      calc
        _ = (((c.val * q.val) * star c.val : Algebra M) : H →L[ℂ] H) x := rfl
        _ = x := by rw [hmul, hfinal]; rfl
    rw [hcx] at hs
    apply hs.congr_fun
    intro n
    rw [hzf]
    rfl

/-- Blackadar's countable full-projection copying assertion, proved from
partial-isometry sums and projection Schroeder--Bernstein. -/
theorem publishedProperInfiniteProjectionCopies :
    PublishedProperInfiniteProjectionCopies.{u} := by
  intro H _ _ _ _ M hM p hp
  exact exists_countable_projection_copies hM p hp

end

end KadisonKastler

end OAI
