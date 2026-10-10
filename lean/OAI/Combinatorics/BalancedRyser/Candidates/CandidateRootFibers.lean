import OAI.Combinatorics.BalancedRyser.Candidates.CandidateRetentionBridge
import OAI.Combinatorics.BalancedRyser.Probability.RootSuccess

namespace OAI

namespace Balanced.TupleAlignment

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def RootPrescription.choice {g : Direction F} (M : MergedPairs F)
    (a : RootPrescription g) : SplitChoice F :=
  ⟨lineThrough g (tuplePoint M a.tuple 0), a.tuple⟩

omit [Fintype F] [DecidableEq F] in
@[simp] theorem RootPrescription.choice_tuple {g : Direction F}
    (M : MergedPairs F) (a : RootPrescription g) :
    (a.choice M).tuple = a.tuple := rfl

omit [Fintype F] [DecidableEq F] in
@[simp] theorem RootPrescription.choice_direction {g : Direction F}
    (M : MergedPairs F) (a : RootPrescription g) :
    (a.choice M).line.1 = g := rfl

omit [Field F] [Fintype F] [DecidableEq F] in
theorem RootPrescription.tuple_injective {g : Direction F} :
    Function.Injective (RootPrescription.tuple (F := F) (g := g)) := by
  intro a b h
  apply Prod.ext
  · apply DFunLike.ext
    intro i
    apply Subtype.ext
    exact congrArg (fun T : FourTuple F => T.generator i) h
  · exact congrArg FourTuple.side h

omit [Fintype F] [DecidableEq F] in
theorem RootPrescription.choice_injective {g : Direction F} (M : MergedPairs F) :
    Function.Injective (fun a : RootPrescription g => a.choice M) := by
  intro a b h
  exact RootPrescription.tuple_injective (congrArg SplitChoice.tuple h)

def RootPrescription.ofTuple (g : Direction F) (T : FourTuple F)
    (hinj : Function.Injective T.generator) (havoid : ∀ i, T.generator i ≠ g) :
    RootPrescription g :=
  (⟨fun i => ⟨T.generator i, havoid i⟩,
    fun _ _ h => hinj (congrArg Subtype.val h)⟩, T.side)

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem RootPrescription.ofTuple_tuple (g : Direction F) (T : FourTuple F)
    (hinj : Function.Injective T.generator) (havoid : ∀ i, T.generator i ≠ g) :
    (RootPrescription.ofTuple g T hinj havoid).tuple = T := rfl

def successfulPrescriptions (M : MergedPairs F) (g : Direction F) :
    Finset (RootPrescription g) :=
  Finset.univ.filter (fun a =>
    (∃ c, ∀ i, OnLine (tuplePoint M a.tuple i) (g, c)) ∧
    Function.Injective (tuplePoint M a.tuple))

@[simp] theorem successfulPrescriptions_card (M : MergedPairs F) (g : Direction F) :
    (successfulPrescriptions M g).card = rootSuccessCount g M := rfl

theorem choice_on_line_of_successful {M : MergedPairs F} {g : Direction F}
    {a : RootPrescription g} (ha : a ∈ successfulPrescriptions M g) :
    ∀ i, OnLine (tuplePoint M a.tuple i) (a.choice M).line := by
  obtain ⟨c, hc⟩ := (Finset.mem_filter.mp ha).2.1
  intro i
  change lineEval g (tuplePoint M a.tuple i) = lineEval g (tuplePoint M a.tuple 0)
  exact (hc i).trans (hc 0).symm

def successfulChoices (M : MergedPairs F) (g : Direction F) : Finset (SplitChoice F) :=
  (successfulPrescriptions M g).image (fun a => a.choice M)

@[simp] theorem successfulChoices_card (M : MergedPairs F) (g : Direction F) :
    (successfulChoices M g).card = rootSuccessCount g M := by
  rw [successfulChoices, Finset.card_image_of_injective _
    (RootPrescription.choice_injective M), successfulPrescriptions_card]

def validPrescriptions (M : MergedPairs F) (g : Direction F) :
    Finset (RootPrescription g) :=
  (successfulPrescriptions M g).filter (fun a => ValidChoice M g (a.choice M))

theorem exists_valid_prescription {M : MergedPairs F} {g : Direction F}
    {D : SplitChoice F} (hD : ValidChoice M g D) :
    ∃ a ∈ validPrescriptions M g, a.choice M = D := by
  rcases D with ⟨l, T⟩
  let a := RootPrescription.ofTuple g T hD.2.2.1 hD.2.2.2.1
  have htuple : a.tuple = T := rfl
  have hline : (a.choice M).line = l := by
    change lineThrough g (tuplePoint M T 0) = l
    rw [← hD.1]
    exact Prod.ext rfl (hD.2.2.2.2.2.1 0)
  have hchoice : a.choice M = (⟨l, T⟩ : SplitChoice F) := by
    change (⟨(a.choice M).line, T⟩ : SplitChoice F) = ⟨l, T⟩
    rw [hline]
  refine ⟨a, Finset.mem_filter.mpr ⟨?_, ?_⟩, hchoice⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ⟨l.2, ?_⟩, ?_⟩
    · intro i
      simpa only [htuple, ← hD.1] using hD.2.2.2.2.2.1 i
    · simpa only [htuple] using hD.2.2.2.2.1
  · simpa only [hchoice] using hD

theorem supportsValidTuple_iff_valid_prescription (M : MergedPairs F)
    (g : Direction F) (c : F) :
    SupportsValidTuple M (g, c) ↔
      ∃ a ∈ validPrescriptions M g, (a.choice M).line = (g, c) := by
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨a, ha, heq⟩ := exists_valid_prescription hT
    exact ⟨a, ha, congrArg SplitChoice.line heq⟩
  · rintro ⟨a, ha, hline⟩
    refine ⟨a.tuple, ?_⟩
    have hv := (Finset.mem_filter.mp ha).2
    change ValidChoice M g ⟨(a.choice M).line, a.tuple⟩ at hv
    rw [hline] at hv
    exact hv

def invalidSuccessCount (M : MergedPairs F) (g : Direction F) : ℕ :=
  ((successfulPrescriptions M g).filter (fun a => ¬ ValidChoice M g (a.choice M))).card

theorem valid_add_invalid_eq_success (M : MergedPairs F) (g : Direction F) :
    (validPrescriptions M g).card + invalidSuccessCount M g = rootSuccessCount g M := by
  exact Finset.card_filter_add_card_filter_not _

def rootFiberSquareCount (M : MergedPairs F) (g : Direction F) : ℕ :=
  ∑ l : Line F,
    ((successfulPrescriptions M g).filter (fun a => (a.choice M).line = l)).card ^ 2

def commonLineSuccessPairs (M : MergedPairs F) (g : Direction F) :
    Finset (RootPrescription g × RootPrescription g) :=
  ((successfulPrescriptions M g).product (successfulPrescriptions M g)).filter
    (fun ab => (ab.1.choice M).line = (ab.2.choice M).line)

theorem rootFiberSquareCount_eq_pair_card (M : MergedPairs F) (g : Direction F) :
    rootFiberSquareCount M g = (commonLineSuccessPairs M g).card := by
  have hfiber (l : Line F) :
      (commonLineSuccessPairs M g).filter (fun ab => (ab.1.choice M).line = l) =
        ((successfulPrescriptions M g).filter (fun a => (a.choice M).line = l)).product
          ((successfulPrescriptions M g).filter (fun a => (a.choice M).line = l)) := by
    ext ab
    simp only [commonLineSuccessPairs, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, hab⟩, hal⟩
      exact ⟨⟨ha, hal⟩, hb, hab.symm.trans hal⟩
    · rintro ⟨⟨ha, hal⟩, hb, hbl⟩
      exact ⟨⟨⟨ha, hb⟩, hal.trans hbl.symm⟩, hal⟩
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ab : RootPrescription g × RootPrescription g => (ab.1.choice M).line)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  simp only [rootFiberSquareCount, hfiber, Finset.product_eq_sprod, Finset.card_product, pow_two]

theorem rootFiberSquareCount_eq_sum_fibers (M : MergedPairs F) (g : Direction F) :
    rootFiberSquareCount M g =
      ∑ a ∈ successfulPrescriptions M g,
        ((successfulPrescriptions M g).filter
          (fun b => (b.choice M).line = (a.choice M).line)).card := by
  rw [rootFiberSquareCount_eq_pair_card]
  simp only [commonLineSuccessPairs, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [eq_comm]

theorem mem_successfulPrescriptions_fiber_iff (M : MergedPairs F)
    {g : Direction F} (a : RootPrescription g) (c : F) :
    a ∈ (successfulPrescriptions M g).filter
      (fun b => (b.choice M).line = (g, c)) ↔
      (∀ i, OnLine (tuplePoint M a.tuple i) (g, c)) ∧
      Function.Injective (tuplePoint M a.tuple) := by
  constructor
  · intro ha
    obtain ⟨hs, hl⟩ := Finset.mem_filter.mp ha
    exact ⟨fun i => hl ▸ choice_on_line_of_successful hs i,
      (Finset.mem_filter.mp hs).2.2⟩
  · rintro ⟨hc, hd⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨c, hc⟩, hd⟩, ?_⟩
    exact Prod.ext rfl (hc 0)

theorem mem_commonLineSuccessPairs_iff (M : MergedPairs F)
    {g : Direction F} (ab : RootPrescription g × RootPrescription g) :
    ab ∈ commonLineSuccessPairs M g ↔
      (∃ c, (∀ i, OnLine (tuplePoint M ab.1.tuple i) (g, c)) ∧
        (∀ i, OnLine (tuplePoint M ab.2.tuple i) (g, c))) ∧
      Function.Injective (tuplePoint M ab.1.tuple) ∧
      Function.Injective (tuplePoint M ab.2.tuple) := by
  simp only [commonLineSuccessPairs, Finset.mem_filter, Finset.product_eq_sprod,
    Finset.mem_product]
  constructor
  · rintro ⟨⟨ha, hb⟩, hab⟩
    refine ⟨⟨(ab.1.choice M).line.2, ?_, ?_⟩,
      (Finset.mem_filter.mp ha).2.2, (Finset.mem_filter.mp hb).2.2⟩
    · exact choice_on_line_of_successful ha
    · intro i
      exact hab ▸ choice_on_line_of_successful hb i
  · rintro ⟨⟨c, ha, hb⟩, hia, hib⟩
    have hfa := (mem_successfulPrescriptions_fiber_iff M ab.1 c).mpr ⟨ha, hia⟩
    have hfb := (mem_successfulPrescriptions_fiber_iff M ab.2 c).mpr ⟨hb, hib⟩
    obtain ⟨hsa, hla⟩ := Finset.mem_filter.mp hfa
    obtain ⟨hsb, hlb⟩ := Finset.mem_filter.mp hfb
    exact ⟨⟨hsa, hsb⟩, hla.trans hlb.symm⟩

theorem mean_rootFiberSquareCount (g : Direction F) :
    (∑ M : MergedPairs F, (rootFiberSquareCount M g : ℝ)) /
      Fintype.card (MergedPairs F) =
      ∑ ab : RootPrescription g × RootPrescription g,
        offsetEventProbability {M | ab ∈ commonLineSuccessPairs M g} := by
  let R (M : MergedPairs F) (ab : RootPrescription g × RootPrescription g) : Prop :=
    ab ∈ commonLineSuccessPairs M g
  have hcard (M : MergedPairs F) : rootFiberSquareCount M g =
      (Finset.univ.filter (R M)).card := by
    rw [rootFiberSquareCount_eq_pair_card]
    congr 1
    ext ab
    simp [R]
  have hswap : (∑ M : MergedPairs F, rootFiberSquareCount M g) =
      ∑ ab : RootPrescription g × RootPrescription g,
        (Finset.univ.filter (fun M => R M ab)).card := by
    simp only [hcard, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hprob (ab : RootPrescription g × RootPrescription g) :
      offsetEventProbability {M | R M ab} =
        ((Finset.univ.filter (fun M => R M ab)).card : ℝ) /
          Fintype.card (MergedPairs F) := by
    simp only [offsetEventProbability, offsetLaw,
      PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div,
      ENNReal.toReal_natCast, Fintype.card_subtype, Set.mem_ofPred_eq]
    congr 2
    simp only [Fintype.card_fun, Fintype.card_bool, Direction, Fintype.card_option]
  change _ = ∑ ab : RootPrescription g × RootPrescription g,
    offsetEventProbability {M | R M ab}
  simp_rw [hprob]
  rw [← Finset.sum_div]
  congr 1
  exact_mod_cast hswap

theorem successfulChoices_fiber_card (M : MergedPairs F) (g : Direction F) (l : Line F) :
    ((successfulChoices M g).filter (fun C => C.line = l)).card =
      ((successfulPrescriptions M g).filter (fun a => (a.choice M).line = l)).card := by
  rw [successfulChoices, Finset.filter_image]
  exact Finset.card_image_of_injective _ (RootPrescription.choice_injective M)

theorem successfulChoices_square_sum (M : MergedPairs F) (g : Direction F) :
    (∑ l : Line F,
      (((successfulChoices M g).filter (fun C => C.line = l)).card : ℝ) ^ 2) =
        (rootFiberSquareCount M g : ℝ) := by
  simp only [rootFiberSquareCount, Nat.cast_sum, Nat.cast_pow,
    successfulChoices_fiber_card]

theorem candidateSlot_lower_bound_of_root_counts (M : MergedPairs F) (s : Slot F)
    {a C : ℝ} (ha : 0 ≤ a) (hC : 0 < C)
    (hmass : a * Fintype.card F + invalidSuccessCount M s.1 ≤ rootSuccessCount s.1 M)
    (hsquare : (rootFiberSquareCount M s.1 : ℝ) ≤ C * Fintype.card F) :
    (a ^ 2 / C) * Fintype.card F ≤ ((candidateSlot M s).card : ℝ) := by
  let V := (validPrescriptions M s.1).image (fun a => a.choice M)
  have hsub : V ⊆ successfulChoices M s.1 :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hvalid : ∀ D ∈ V, ValidChoice M s.1 D := by
    intro D hD
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hD
    exact (Finset.mem_filter.mp ha).2
  have hcard : V.card = (validPrescriptions M s.1).card :=
    Finset.card_image_of_injective _ (RootPrescription.choice_injective M)
  have hsplit : ((validPrescriptions M s.1).card : ℝ) +
      invalidSuccessCount M s.1 = rootSuccessCount s.1 M := by
    exact_mod_cast valid_add_invalid_eq_success M s.1
  have hmassV : a * Fintype.card F ≤ (V.card : ℝ) := by
    rw [hcard]
    linarith
  apply CandidateRetention.candidateSlot_lower_bound M s hsub hvalid ha hC
    (by exact_mod_cast Fintype.card_pos (α := F)) hmassV
  simpa only [successfulChoices_square_sum] using hsquare

end
end Balanced.TupleAlignment

end OAI
