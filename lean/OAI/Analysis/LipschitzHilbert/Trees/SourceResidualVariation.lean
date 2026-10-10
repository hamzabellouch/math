import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualPropagation
import OAI.Analysis.LipschitzHilbert.Estimates.StoppingScaleIntervals
import OAI.Analysis.LipschitzHilbert.Trees.UnaryRunVariation
import OAI.Analysis.LipschitzHilbert.Packets.VariationPacketL1
import OAI.Analysis.LipschitzHilbert.Estimates.VariationDisjointExact

namespace OAI

/-! The fixed residual collection is grouped by stopping level in the
unary recurrence and by packet length in the reference-line variation.
Antitone stopping transports every disjoint collection of level bands
to disjoint length bands. Empty bands contribute zero. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem packetPartialSum_sub_eq_band {N : ℕ} {E : Type*} [AddCommGroup E]
    (f : Fin N → E) {a b : ℕ} (hab : a ≤ b) :
    packetPartialSum f b-packetPartialSum f a =
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => a ≤ j.val ∧ j.val < b), f j := by
  simp only [packetPartialSum,Finset.sum_filter,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hja : j.val < a
  · have hjb : j.val < b := hja.trans_le hab
    simp [hja,hjb,not_le.mpr hja]
  · by_cases hjb : j.val < b
    · simp [hja,hjb,not_lt.mp hja]
    · simp [hja,hjb]

/-- Exact regrouping by stopping levels for any fixed packet subset. -/
theorem sum_packet_stopping_fibers {σ E : Type*} [AddCommMonoid E]
    (Q : Finset σ) (stop : σ → ℕ) (value : σ → E) (a b : ℕ) :
    (∑ k ∈ Finset.Ico a b, ∑ q ∈ Q.filter (fun q => stop q = k), value q) =
      ∑ q ∈ Q.filter (fun q => a ≤ stop q ∧ stop q < b), value q := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : stop q ∈ Finset.Ico a b
  · rw [Finset.sum_eq_single_of_mem (stop q) hq]
    · simp only [ite_true,ite_eq_left (Finset.mem_Ico.mp hq)]
    · intro k _ hk
      exact ite_eq_right (Ne.symm hk)
  · rw [Finset.sum_eq_zero]
    · exact (ite_eq_right (fun h => hq (Finset.mem_Ico.mpr h))).symm
    · intro k hk
      exact ite_eq_right (fun heq => hq (by simpa only [heq] using hk))

/-- Grouping by packet length preserves multiplicities and arbitrary
fixed packet selection. -/
theorem packet_stopping_band_eq_length_band {σ E : Type*} [AddCommMonoid E]
    {N : ℕ} (Q : Finset σ) (lengthIndex : σ → Fin N) (stop : Fin N → ℕ)
    (value : σ → E) (a b : ℕ) :
    (∑ q ∈ Q.filter (fun q => a ≤ stop (lengthIndex q) ∧ stop (lengthIndex q) < b), value q) =
      ∑ j ∈ Finset.univ.filter (fun j => a ≤ stop j ∧ stop j < b),
        ∑ q ∈ Q.filter (fun q => lengthIndex q = j), value q := by
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using
    (Finset.sum_fiberwise_eq_sum_filter Q
      (Finset.univ.filter (fun j => a ≤ stop j ∧ stop j < b)) lengthIndex value).symm

/-- Zero-length intervals may be discarded before applying the finite
disjoint-interval variation bound. -/
theorem disjoint_increment_cube_sum {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) (a b : ι → ℕ)
    (hab : ∀ i, a i ≤ b i) (hb : ∀ i, b i ≤ N)
    (hdisjoint : ∀ i j, i ≠ j → a i < b i → a j < b j → b i ≤ a j ∨ b j ≤ a i) :
    (∑ i, ‖F (b i)-F (a i)‖^3) ≤ finiteCubicVariation F N := by
  let active := Finset.univ.filter (fun i : ι => a i < b i)
  have hzero (i : ι) (hi : i ∈ Finset.univ) (hni : i ∉ active) :
      ‖F (b i)-F (a i)‖^3 = 0 := by
    have hn : ¬a i < b i := fun h => hni (Finset.mem_filter.mpr ⟨hi,h⟩)
    have heq : a i = b i := le_antisymm (hab i) (not_lt.mp hn)
    simp [heq]
  calc
    _ = ∑ i ∈ active, ‖F (b i)-F (a i)‖^3 :=
      (Finset.sum_subset (Finset.subset_univ active) hzero).symm
    _ = ∑ i : active, ‖F (b i.val)-F (a i.val)‖^3 := by
      exact (Finset.sum_subtype active (p := fun i => i ∈ active) (by simp)
        (fun i : ι => ‖F (b i)-F (a i)‖^3))
    _ ≤ _ := disjoint_increment_cube_sum_exact F N
      (fun i : active => a i.val) (fun i => b i.val)
      (fun i => (Finset.mem_filter.mp i.property).2) (fun i => hb i.val)
      (fun i j hij => hdisjoint i.val j.val (fun h => hij (Subtype.ext h))
        (Finset.mem_filter.mp i.property).2 (Finset.mem_filter.mp j.property).2)

/-- Disjoint stopping-level intervals become disjoint intervals of the
one fixed length sequence, including when some length fibers are empty. -/
theorem disjoint_stopping_band_cube_sum {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] {N : ℕ} (f : Fin N → E)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (a b : ι → ℕ)
    (hdisjoint : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i) :
    (∑ i, ‖∑ j ∈ Finset.univ.filter (fun j => a i ≤ stop j ∧ stop j < b i), f j‖^3) ≤
      finiteCubicVariation (packetPartialSum f) N := by
  choose lower upper hlu hu hband using fun i =>
    antitone_stopping_band_interval stop hstop (a i) (b i)
  have hdis (i j : ι) (hij : i ≠ j) (hi : lower i < upper i)
      (hj : lower j < upper j) : upper i ≤ lower j ∨ upper j ≤ lower i := by
    by_contra hn
    have h1 : lower j < upper i := by omega
    have h2 : lower i < upper j := by omega
    have hmaxi : max (lower i) (lower j) < upper i := max_lt_iff.mpr ⟨hi,h1⟩
    have hmaxj : max (lower i) (lower j) < upper j := max_lt_iff.mpr ⟨h2,hj⟩
    let k : Fin N := ⟨max (lower i) (lower j), hmaxi.trans_le (hu i)⟩
    have hki : a i ≤ stop k ∧ stop k < b i := (hband i k).mpr ⟨le_max_left _ _,hmaxi⟩
    have hkj : a j ≤ stop k ∧ stop k < b j := (hband j k).mpr ⟨le_max_right _ _,hmaxj⟩
    rcases hdisjoint i j hij with h | h <;> omega
  have heq (i : ι) :
      (∑ j ∈ Finset.univ.filter (fun j => a i ≤ stop j ∧ stop j < b i), f j) =
        packetPartialSum f (upper i)-packetPartialSum f (lower i) := by
    rw [packetPartialSum_sub_eq_band f (hlu i)]
    apply Finset.sum_congr
    · ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact hband i j
    · intro j _
      rfl
  simp_rw [heq]
  exact disjoint_increment_cube_sum (packetPartialSum f) N lower upper hlu hu hdis

/-- The cubic variation of the stop-grouped raw prefix is controlled by
the original length-grouped raw prefix, independently of angular depth. -/
theorem stopping_prefix_cubic_variation {σ E : Type*} [NormedAddCommGroup E]
    {N : ℕ} (Q : Finset σ) (lengthIndex : σ → Fin N)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (value : σ → E) (H : ℕ) :
    let raw := fun k => ∑ q ∈ Q.filter (fun q => stop (lengthIndex q) = k), value q
    let bands := fun j => ∑ q ∈ Q.filter (fun q => lengthIndex q = j), value q
    finiteCubicVariation (packetPrefix raw) H ≤
      finiteCubicVariation (packetPartialSum bands) N := by
  dsimp only
  apply Finset.sup'_le
  intro p _
  split_ifs with hp
  · have hband (i : Fin H) :
        packetPrefix (fun k => ∑ q ∈ Q.filter (fun q => stop (lengthIndex q) = k), value q)
          (p i.succ)-
        packetPrefix (fun k => ∑ q ∈ Q.filter (fun q => stop (lengthIndex q) = k), value q)
          (p i.castSucc) =
        ∑ j ∈ Finset.univ.filter (fun j => (p i.castSucc).val ≤ stop j ∧ stop j < (p i.succ).val),
          ∑ q ∈ Q.filter (fun q => lengthIndex q = j), value q := by
      rw [packetPrefix,packetPrefix,← Finset.sum_Ico_eq_sub _ (hp (Fin.castSucc_le_succ i)),
        sum_packet_stopping_fibers,packet_stopping_band_eq_length_band]
    simp_rw [hband]
    apply disjoint_stopping_band_cube_sum _ stop hstop
      (fun i : Fin H => (p i.castSucc).val) (fun i => (p i.succ).val)
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inl (hp (show i.succ ≤ j.castSucc by
        change i.val+1 ≤ j.val
        exact Nat.succ_le_of_lt h))
    · exact Or.inr (hp (show j.succ ≤ i.castSucc by
        change j.val+1 ≤ i.val
        exact Nat.succ_le_of_lt h))
  · exact finiteCubicVariation_nonneg _ _

/-- All unary runs and their point-dependent greedy segments use this
single length variation of the fixed packet collection. -/
theorem unary_runs_stopping_oscillation_cube_sum {σ E : Type*} [NormedAddCommGroup E]
    {unary : ℕ → Prop} {n : ℕ → ℝ} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish)
    (P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)
    {N : ℕ} (Q : Finset σ) (lengthIndex : σ → Fin N)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (value : σ → E)
    (level : ℕ → ℕ) (hlevel : StrictMono level) (H : ℕ) (hend : level finish ≤ H) :
    let raw := fun k => ∑ q ∈ Q.filter (fun q => stop (lengthIndex q) = k), value q
    let bands := fun j => ∑ q ∈ Q.filter (fun q => lengthIndex q = j), value q
    (∑ i : UnaryRunSegment R P,
      intervalOscillation (packetPrefix raw) H (level i.2.val.1) (level i.2.val.2)^3) ≤
        finiteCubicVariation (packetPartialSum bands) N := by
  dsimp only
  apply (unary_runs_oscillation_cube_sum R P _ level hlevel H hend).trans
  have h := stopping_prefix_cubic_variation Q lengthIndex stop hstop value (2*H)
  have heq :
      finiteCubicVariation (fun k => packetPrefix
        (fun j => ∑ q ∈ Q.filter (fun q => stop (lengthIndex q) = j), value q) (min k H)) (2*H) ≤
      finiteCubicVariation (packetPrefix
        (fun j => ∑ q ∈ Q.filter (fun q => stop (lengthIndex q) = j), value q)) (2*H) :=
    finiteCubicVariation_comp_le _ _ (fun k => min k H)
      (fun _ _ h => min_le_min h le_rfl) (min_le_left _ _)
  exact heq.trans h

end LipschitzHilbert

end

end OAI
