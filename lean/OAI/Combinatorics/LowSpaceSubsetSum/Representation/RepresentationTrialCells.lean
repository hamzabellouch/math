import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ExtraPreparationCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PreparedResidentCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationFamilyCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PreparedScheduleCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationPreparedTrial

namespace OAI

/-! # Memory of the complete stored representation trial

The prepared data and sampled families stay resident during the stopped
schedule. The schedule itself reuses storage across residue classes.
-/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationTrialCells

variable {n : ℕ}

def core {D F : Type} (prepared : (Option D × ℕ) × ℕ) (resident : ℕ)
    (middle : ∀ d, prepared.1.1 = some d → (Option F × ℕ) × ℕ)
    (last : ∀ d (hd : prepared.1.1 = some d) f,
      (middle d hd).1.1 = some f → BudgetedSeparatorCells.Execution Bool) :
    BudgetedSeparatorCells.Execution Bool :=
  match h : prepared.1.1 with
  | none => ((none, prepared.1.2+1), prepared.2+32)
  | some d =>
    let families := middle d h
    match hf : families.1.1 with
    | none => ((none, prepared.1.2+families.1.2+17), prepared.2+resident+families.2+32)
    | some f =>
      let out := last d h f hf
      ((out.1.1, prepared.1.2+families.1.2+out.1.2+17),
        prepared.2+resident+families.2+out.2+32)

abbrev bare := @RepresentationPreparedTrial.control

theorem core_value {D F : Type} (prepared : (Option D × ℕ) × ℕ) (resident : ℕ)
    (middle : ∀ d, prepared.1.1 = some d → (Option F × ℕ) × ℕ)
    (last : ∀ d (hd : prepared.1.1 = some d) f,
      (middle d hd).1.1 = some f → BudgetedSeparatorCells.Execution Bool) :
    (core prepared resident middle last).1 = bare prepared.1
      (fun d hd => (middle d hd).1) (fun d hd f hf => (last d hd f hf).1) := by
  rcases prepared with ⟨⟨p,work⟩,peak⟩
  cases p with
  | none => rfl
  | some d =>
    dsimp only [core, bare, RepresentationPreparedTrial.control]
    split <;> split <;> try simp_all
    rename_i f hf f' hf'
    have he : f = f' := Option.some.inj (hf.symm.trans hf')
    subst f'
    exact ⟨rfl,rfl⟩

theorem bare_congr {D F : Type} (p q : Option D × ℕ) (hp : p = q)
    (m : ∀ d, p.1 = some d → Option F × ℕ)
    (m' : ∀ d, q.1 = some d → Option F × ℕ)
    (hm : ∀ d hd, m d hd = m' d ((congrArg Prod.fst hp).symm.trans hd))
    (l : ∀ d (hd : p.1 = some d) f, (m d hd).1 = some f → BudgetedSeparatorCall.Outcome Bool)
    (l' : ∀ d (hd : q.1 = some d) f, (m' d hd).1 = some f → BudgetedSeparatorCall.Outcome Bool)
    (hl : ∀ d hd f hf, l d hd f hf =
      l' d ((congrArg Prod.fst hp).symm.trans hd) f ((congrArg Prod.fst (hm d hd)).symm.trans hf)) :
    bare p m l = bare q m' l' := by
  subst q
  have hm' : m = m' := funext (fun d => funext (fun hd => hm d hd))
  subst m'
  have hl' : l = l' := funext (fun d => funext (fun hd => funext (fun f => funext (fun hf => hl d hd f hf))))
  subst l'
  rfl

theorem core_cells {D F : Type} (prepared : (Option D × ℕ) × ℕ) (resident : ℕ)
    (middle : ∀ d, prepared.1.1 = some d → (Option F × ℕ) × ℕ)
    (last : ∀ d (hd : prepared.1.1 = some d) f,
      (middle d hd).1.1 = some f → BudgetedSeparatorCells.Execution Bool)
    (A B K : ℕ) (hp : prepared.2 ≤ A)
    (hm : ∀ d hd, (middle d hd).2 ≤ B)
    (hl : ∀ d hd f hf, (last d hd f hf).2 ≤ K) :
    (core prepared resident middle last).2 ≤ A+resident+B+K+32 := by
  unfold core
  split
  · dsimp only
    omega
  next d hd =>
    have hb := hm d hd
    dsimp only
    split
    · dsimp only
      omega
    next f hf =>
      have hk := hl d hd f hf
      dsimp only
      omega

def middle (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (hd : (ExtraPreparationCells.run I hn hlog s.1).1.1 = some d) :=
  RepresentationFamilyCells.run I hn hlog s.1 d
    ((congrArg Prod.fst (ExtraPreparationCells.value I hn hlog s.1)).symm.trans hd) s.2

def last (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed)
    (budget : ℕ) (d : RepresentationExtraPreparation.Data n)
    (hd : (ExtraPreparationCells.run I hn hlog s.1).1.1 = some d)
    (rows : Fin 4 → Array (Fin (2 ^ StoredTopCoordinates.width n)))
    (hf : (middle I hn hlog s d hd).1.1 = some rows) : BudgetedSeparatorCells.Execution Bool :=
  let hs := (congrArg Prod.fst (ExtraPreparationCells.value I hn hlog s.1)).symm.trans hd
  let hr := (congrArg Prod.fst (RepresentationFamilyCells.value I hn hlog s.1 d hs s.2)).symm.trans hf
  PreparedScheduleCells.run (RepresentationSchedulePreparation.fromSuccess I hn hlog s.1 d hs)
    d.residues.primes.stored.stored.layout.signs rfl (representationBufferCapacity n)
    d.residues.primes.stored.coordinates rows
    (RepresentationPreparedTrial.family_sizes I hn hlog s.1 d hs s.2 rows hr) budget

def run (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed)
    (budget : ℕ) : BudgetedSeparatorCells.Execution Bool :=
  core (ExtraPreparationCells.run I hn hlog s.1) (PreparedResidentCells.residentLimit n)
    (middle I hn hlog s) (last I hn hlog s budget)

theorem bare_run (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed)
    (budget : ℕ) :
    RepresentationPreparedTrial.run I hn hlog s budget =
      bare (RepresentationExtraPreparation.run I hn hlog s.1)
        (fun d hd => RepresentationFamilyPreparation.run I hn hlog s.1 d hd s.2)
        (fun d hd rows hf => BudgetedPreparedSchedule.run
          (RepresentationSchedulePreparation.fromSuccess I hn hlog s.1 d hd)
          d.residues.primes.stored.stored.layout.signs rfl (representationBufferCapacity n)
          d.residues.primes.stored.coordinates rows
          (RepresentationPreparedTrial.family_sizes I hn hlog s.1 d hd s.2 rows hf) budget) := by
  rfl

theorem value (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed)
    (budget : ℕ) :
    (run I hn hlog s budget).1 = RepresentationPreparedTrial.run I hn hlog s budget := by
  unfold run
  rw [core_value, bare_run]
  apply bare_congr _ _ (ExtraPreparationCells.value I hn hlog s.1)
    _ (fun d hd => RepresentationFamilyPreparation.run I hn hlog s.1 d hd s.2)
    (fun d hd => RepresentationFamilyCells.value I hn hlog s.1 d
      ((congrArg Prod.fst (ExtraPreparationCells.value I hn hlog s.1)).symm.trans hd) s.2)
    _ (fun d hd rows hf => BudgetedPreparedSchedule.run
      (RepresentationSchedulePreparation.fromSuccess I hn hlog s.1 d hd)
      d.residues.primes.stored.stored.layout.signs rfl (representationBufferCapacity n)
      d.residues.primes.stored.coordinates rows
      (RepresentationPreparedTrial.family_sizes I hn hlog s.1 d hd s.2 rows hf) budget)
  intro d hd rows hf
  exact PreparedScheduleCells.value _ _ _ _ _ _ _ _

theorem schedule_raw (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (hd : (RepresentationExtraPreparation.run I hn hlog s).1 = some d) :
    ∀ side i, ((RepresentationSchedulePreparation.fromSuccess I hn hlog s d hd).leaves side i).occurrences.card ≤
      (RepresentationSchedulePreparation.fromSuccess I hn hlog s d hd).capacity := by
  rw [RepresentationSchedulePreparation.fromSuccess_eq]
  intro side i
  have hz : Real.logb 2 (inputScale (canonicalRepresentationData I).zeroSetup.input : ℝ) ≤
      (n : ℝ)/1000000000 := by
    apply (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) ?_ ?_).trans hscale
    · exact_mod_cast (show 0 < inputScale (canonicalRepresentationData I).zeroSetup.input by
        unfold inputScale; omega)
    · exact_mod_cast (canonicalRepresentationData I).zeroSetup_inputScale_le
  exact (canonicalRepresentationData I).zeroSetup.rawLeaf_capacity _ _ _ hn hlog hz side i

theorem schedule_order (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (hd : (RepresentationExtraPreparation.run I hn hlog s).1 = some d) :
    (RepresentationSchedulePreparation.fromSuccess I hn hlog s d hd).topOrder.length ≤ n := by
  rw [RepresentationSchedulePreparation.fromSuccess_eq]
  change (((canonicalRepresentationData I).zeroSetup.orderedMixers _ 0).sort (· ≤ ·)).length ≤ n
  rw [Finset.length_sort]
  simpa only [Fintype.card_fin] using Finset.card_le_univ
    ((canonicalRepresentationData I).zeroSetup.orderedMixers _ 0)

theorem schedule_cells (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (hd : (RepresentationExtraPreparation.run I hn hlog s).1 = some d)
    (rows : Fin 4 → Array (Fin (2 ^ StoredTopCoordinates.width n)))
    (hrows : ∀ i, (rows i).size ≤ 11*2^StoredTopCoordinates.width n) (budget : ℕ) :
    (PreparedScheduleCells.run (RepresentationSchedulePreparation.fromSuccess I hn hlog s d hd)
      d.residues.primes.stored.stored.layout.signs rfl (representationBufferCapacity n)
      d.residues.primes.stored.coordinates rows hrows budget).2 ≤
        32*inputScale I^14*(compressionDictionaryCapacity n+1)+16 := by
  apply PreparedScheduleCells.cells _ _ _ _ _ _ _ _ hn
  · unfold RepresentationSchedulePreparation.width StoredTopCoordinates.width RepresentationSetup.blockHalf
    simp only [Matrix.cons_val_zero]
    omega
  · exact schedule_raw I hn hlog hscale s d hd
  · change compressionDictionaryCapacity n ≤ 2^n
    unfold compressionDictionaryCapacity
    apply Nat.pow_le_pow_right (by decide)
    omega
  · exact representationBufferCapacity_le n
  · exact schedule_order I hn hlog s d hd
  · exact RepresentationSetup.separator_table_rate_le_capacity

theorem middle_cells (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (hd : (ExtraPreparationCells.run I hn hlog s.1).1.1 = some d) :
    (middle I hn hlog s d hd).2 ≤ inputScale I^7*(compressionDictionaryCapacity n+1) :=
  RepresentationFamilyCells.cells I hn hlog s.1 d _ s.2

theorem last_cells (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed)
    (budget : ℕ) (d : RepresentationExtraPreparation.Data n)
    (hd : (ExtraPreparationCells.run I hn hlog s.1).1.1 = some d)
    (rows : Fin 4 → Array (Fin (2 ^ StoredTopCoordinates.width n)))
    (hf : (middle I hn hlog s d hd).1.1 = some rows) :
    (last I hn hlog s budget d hd rows hf).2 ≤
      32*inputScale I^14*(compressionDictionaryCapacity n+1)+16 :=
  schedule_cells I hn hlog hscale s.1 d _ rows _ budget

private theorem bound_sum (L r : ℕ) (hr : r ≤ L) (hb : 48 ≤ L) :
    L+r+L+(32*L+16)+32 ≤ 36*L := by omega

theorem cells (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed)
    (budget : ℕ) : (run I hn hlog s budget).2 ≤
      36*inputScale I^14*(compressionDictionaryCapacity n+1) := by
  let L := inputScale I^14*(compressionDictionaryCapacity n+1)
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hp (k : ℕ) (hk : k ≤ 14) : inputScale I^k*(compressionDictionaryCapacity n+1) ≤ L :=
    Nat.mul_le_mul_right _ (pow_le_pow_right' (by omega) hk)
  have he := (ExtraPreparationCells.cells I hn hlog s.1).trans (hp 13 (by decide))
  have hr := (PreparedResidentCells.residentLimit_scale I hn).trans (hp 4 (by decide))
  have hbase : 48 ≤ L := by
    have h1 := hp 1 (by decide)
    simp only [pow_one] at h1
    have h2 : inputScale I ≤ inputScale I*(compressionDictionaryCapacity n+1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  apply le_trans (b := L+PreparedResidentCells.residentLimit n+L+(32*L+16)+32)
  · unfold run
    apply core_cells _ _ _ _ L L (32*L+16) he
    · intro d hd
      exact (middle_cells I hn hlog s d hd).trans (hp 7 (by decide))
    · intro d hd rows hf
      simpa only [L, Nat.mul_assoc] using last_cells I hn hlog hscale s budget d hd rows hf
  · simpa only [Nat.mul_assoc] using bound_sum L _ hr hbase

end LowSpaceSubsetSum.RepresentationTrialCells

end

end OAI
