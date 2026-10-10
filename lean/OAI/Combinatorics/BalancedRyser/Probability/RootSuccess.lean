import OAI.Combinatorics.BalancedRyser.Probability.GlobalTupleLaw

namespace OAI

namespace Balanced.TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem successfulOffsets_probability (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool) (g : Direction F) :
    (Fintype.card {o : Fin 4 → Bool → F //
      (∃ c, ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)) ∧
      Function.Injective (tuplePositionEquiv d hd σ o)} : ℝ) /
      Fintype.card (Fin 4 → Bool → F) =
      ((Fintype.card F).descFactorial 4 : ℝ) / (Fintype.card F : ℝ)^7 := by
  rw [card_successfulOffsets]
  simp only [Nat.cast_mul, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem successfulOffsets_outer_probability (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool) (g : Direction F) :
    ((PMF.uniformOfFintype (Fin 4 → Bool → F)).toOuterMeasure
      {o | (∃ c, ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)) ∧
        Function.Injective (tuplePositionEquiv d hd σ o)}).toReal =
      ((Fintype.card F).descFactorial 4 : ℝ) / (Fintype.card F : ℝ)^7 := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  convert successfulOffsets_probability d hd σ g using 2
  congr 1

theorem tuplePoint_success_probability (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F) :
    offsetEventProbability {M |
      (∃ c, ∀ i, OnLine (tuplePoint M T i) (g,c)) ∧
      Function.Injective (tuplePoint M T)} =
      ((Fintype.card F).descFactorial 4 : ℝ) / (Fintype.card F : ℝ)^7 := by
  let hd := adjacent_ne_of_injective T hT
  let E : Set (Fin 4 → Point F) := {p |
    (∃ c, ∀ i, OnLine (p i) (g,c)) ∧ Function.Injective p}
  have hg := congrArg (fun p => (p.toOuterMeasure E).toReal) (tuplePoint_uniform T hT)
  have hr := congrArg (fun p => (p.toOuterMeasure E).toReal)
    (tuplePosition_uniform T.generator hd T.side)
  rw [PMF.toOuterMeasure_map_apply] at hg hr
  exact hg.trans (hr.symm.trans (successfulOffsets_outer_probability
    T.generator hd T.side g))

end Balanced.TupleAlignment

namespace Balanced.TupleAlignment

open scoped BigOperators
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev RootPrescription (g : Direction F) :=
  (Fin 4 ↪ {d : Direction F // d ≠ g}) × (Fin 4 → Bool)

noncomputable def RootPrescription.tuple {g : Direction F}
    (a : RootPrescription g) : FourTuple F :=
  ⟨fun i => (a.1 i).1, a.2⟩

omit [Field F] [Fintype F] [DecidableEq F] in
theorem RootPrescription.injective {g : Direction F} (a : RootPrescription g) :
    Function.Injective a.tuple.generator := by
  intro i j h
  exact a.1.injective (Subtype.ext h)

omit [Field F] in
theorem card_rootPrescription (g : Direction F) :
    Fintype.card (RootPrescription g) = 16 * (Fintype.card F).descFactorial 4 := by
  classical
  have hg : Fintype.card {d : Direction F // d ≠ g} = Fintype.card F := by
    rw [Fintype.card_subtype_compl]
    simp [Direction]
  simp only [RootPrescription, Fintype.card_prod, Fintype.card_embedding_eq,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, hg]
  omega

theorem sum_success_probabilities (g : Direction F) :
    ∑ a : RootPrescription g, offsetEventProbability {M |
      (∃ c, ∀ i, OnLine (tuplePoint M a.tuple i) (g,c)) ∧
      Function.Injective (tuplePoint M a.tuple)} =
      16 * ((Fintype.card F).descFactorial 4 : ℝ)^2 / (Fintype.card F : ℝ)^7 := by
  classical
  simp_rw [tuplePoint_success_probability _ (RootPrescription.injective _)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_rootPrescription, Nat.cast_mul, Nat.cast_ofNat]
  ring

noncomputable def rootSuccessCount (g : Direction F) (M : MergedPairs F) : ℕ := by
  classical
  exact (Finset.univ.filter (fun a : RootPrescription g =>
    (∃ c, ∀ i, OnLine (tuplePoint M a.tuple i) (g,c)) ∧
      Function.Injective (tuplePoint M a.tuple))).card

theorem mean_rootSuccessCount (g : Direction F) :
    (∑ M : MergedPairs F, (rootSuccessCount g M : ℝ)) /
      Fintype.card (MergedPairs F) =
      16 * ((Fintype.card F).descFactorial 4 : ℝ)^2 / (Fintype.card F : ℝ)^7 := by
  classical
  let R (M : MergedPairs F) (a : RootPrescription g) : Prop :=
    (∃ c, ∀ i, OnLine (tuplePoint M a.tuple i) (g,c)) ∧
      Function.Injective (tuplePoint M a.tuple)
  have hswap : (∑ M : MergedPairs F, rootSuccessCount g M) =
      ∑ a : RootPrescription g, (Finset.univ.filter (fun M => R M a)).card := by
    simp only [rootSuccessCount, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hprob (a : RootPrescription g) :
      offsetEventProbability {M | R M a} =
        ((Finset.univ.filter (fun M => R M a)).card : ℝ) /
          Fintype.card (MergedPairs F) := by
    simp only [offsetEventProbability, offsetLaw,
      PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div,
      ENNReal.toReal_natCast, Fintype.card_subtype, Set.mem_ofPred_eq]
    congr 2
    simp only [Fintype.card_fun, Fintype.card_bool, Direction, Fintype.card_option]
  rw [← sum_success_probabilities g]
  change _ = ∑ a : RootPrescription g, offsetEventProbability {M | R M a}
  simp_rw [hprob]
  rw [← Finset.sum_div]
  congr 1
  exact_mod_cast hswap

end Balanced.TupleAlignment

end OAI
