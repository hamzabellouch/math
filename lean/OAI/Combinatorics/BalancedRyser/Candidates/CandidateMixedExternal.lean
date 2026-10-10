import OAI.Combinatorics.BalancedRyser.Candidates.CandidateConditionalMean
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateExposedWitness
import OAI.Combinatorics.BalancedRyser.Probability.FreshRandomWitness
import OAI.Combinatorics.BalancedRyser.Probability.FreshTupleWitness
import OAI.Combinatorics.BalancedRyser.Probability.FreshWitnessProbability

namespace OAI

namespace Balanced.CandidateMixedExternal

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness CandidateExposedWitness
open FreshTupleWitness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def tupleTarget (g : Direction F) (T : FourTuple F) (M : MergedPairs F) : Line F :=
  (g, lineEval g (tuplePoint M T 0))

omit [Fintype F] [DecidableEq F] in
theorem successful_on_tupleTarget {g : Direction F} {T : FourTuple F}
    {M : MergedPairs F} (h : M ∈ successfulInDirection T g) :
    ∀ i, OnLine (tuplePoint M T i) (tupleTarget g T M) := by
  obtain ⟨⟨c, hc⟩, _⟩ := h
  intro i
  exact (hc i).trans (hc 0).symm

def mixedExternalEvent (g : Direction F) (T : FourTuple F)
    (d e : Direction F) (i j : Fin 4) : Set (MergedPairs F) :=
  {M | M ∈ successfulInDirection T g ∧ ∃ x : Point F,
    OnLine x (tupleTarget g T M) ∧
    x ∉ designated M ⟨tupleTarget g T M, T⟩ ∧ i ≠ j ∧
    PairWitness M d x (tuplePoint M T i) ∧
    PairWitness M e x (tuplePoint M T j)}

omit [Fintype F] in
theorem mixedExternalEvent_symm (g : Direction F) (T : FourTuple F)
    (d e : Direction F) (i j : Fin 4) :
    mixedExternalEvent g T d e i j = mixedExternalEvent g T e d j i := by
  ext M
  constructor <;> rintro ⟨hS, x, hx, hex, hij, hd, he⟩
  · exact ⟨hS, x, hx, hex, Ne.symm hij, he, hd⟩
  · exact ⟨hS, x, hx, hex, Ne.symm hij, he, hd⟩

def forcedFreshEvent (g : Direction F) (T : FourTuple F) (a : MergedPairs F)
    (d e : Direction F) (j : Fin 4) (σ τ : Bool) : Set (MergedPairs F) :=
  {M | M ∈ successfulInDirection T g ∧
    OnLine (forcedPoint a (tupleTarget g T M) d σ) (constituent M e τ) ∧
    OnLine (tuplePoint M T j) (constituent M e (!τ))}

omit [Fintype F] in
theorem mixedExternalEvent_forces {g : Direction F} {T : FourTuple F}
    {a M : MergedPairs F} {d e : Direction F} {i j : Fin 4}
    (hd : d ≠ g) (hDa : M d = a d)
    (h : M ∈ mixedExternalEvent g T d e i j) :
    ∃ s : Bool × Bool, M ∈ forcedFreshEvent g T a d e j s.1 s.2 := by
  obtain ⟨hS, x, hx, _, _, ⟨σ, hxd, _⟩, ⟨τ, hxe, hje⟩⟩ := h
  have hxa : OnLine x (constituent a d σ) := by
    simpa only [constituent, hDa] using hxd
  have hforced : x = forcedPoint a (tupleTarget g T M) d σ :=
    eq_forcedPoint hd hx hxa
  exact ⟨(σ, τ), hS, hforced ▸ hxe, hje⟩

theorem forcedFreshEvent_probability
    (g : Direction F) (T : FourTuple F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (d e : Direction F) (heD : e ∉ D)
    (heT : ∀ k, T.generator k ≠ e) (j : Fin 4) (σ τ : Bool) :
    conditionalProbability D a (forcedFreshEvent g T a d e j σ τ) =
      conditionalProbability D a (successfulInDirection T g) /
        (Fintype.card F : ℝ)^2 := by
  apply FreshRandomWitness.oriented_pair_probability D a e heD
    (fun M => M ∈ successfulInDirection T g)
    (fun M => forcedPoint a (tupleTarget g T M) d σ)
    (fun M => tuplePoint M T j) τ
  · intro M v
    simp only [successfulInDirection, alignedInDirection, Set.mem_ofPred_eq,
      tuplePoint_update_fresh T e heT]
  · intro M v
    simp only [tupleTarget, tuplePoint_update_fresh T e heT]
  · intro M v
    rw [tuplePoint_update_fresh T e heT]

theorem mixedExternalEvent_probability_le
    (g : Direction F) (T : FourTuple F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (d e : Direction F) (hdD : d ∈ D) (hdg : d ≠ g)
    (heD : e ∉ D) (heT : ∀ k, T.generator k ≠ e) (i j : Fin 4) :
    conditionalProbability D a (mixedExternalEvent g T d e i j) ≤
      4 * conditionalProbability D a (successfulInDirection T g) /
        (Fintype.card F : ℝ)^2 := by
  let E (s : Bool × Bool) := forcedFreshEvent g T a d e j s.1 s.2
  have hmono : conditionalProbability D a (mixedExternalEvent g T d e i j) ≤
      conditionalProbability D a {M | ∃ s, M ∈ E s} := by
    apply ENNReal.toReal_mono
    · rw [PMF.toOuterMeasure_apply]
      exact (exposedLaw D a).tsum_coe_indicator_ne_top _
    · apply PMF.toOuterMeasure_mono
      rintro M ⟨hM, hs⟩
      have hfixed : ∀ t, t ∈ D → M t = a t :=
        (PMF.mem_support_filter_iff
          (PartialAlignment.canonical_exposure_supported D a)).mp hs |>.1
      exact mixedExternalEvent_forces hdg (hfixed d hdD) hM
  calc
    _ ≤ conditionalProbability D a {M | ∃ s, M ∈ E s} := hmono
    _ ≤ ∑ s : Bool × Bool, conditionalProbability D a (E s) :=
      FreshWitnessProbability.probability_exists_le_sum (exposedLaw D a) E
    _ = ∑ _s : Bool × Bool,
        conditionalProbability D a (successfulInDirection T g) /
          (Fintype.card F : ℝ)^2 := by
      apply Finset.sum_congr rfl
      intro s _
      exact forcedFreshEvent_probability g T D a d e heD heT j s.1 s.2
    _ = _ := by simp; ring

def freshWitnessDirections (g : Direction F) (T : FourTuple F)
    (D : Finset (Direction F)) : Finset (Direction F) :=
  Finset.univ.filter (fun e => e ∉ D ∧ e ≠ g ∧ e ∉ generatorSet T)

def oldWitnessDirections (g : Direction F) (T : FourTuple F)
    (D : Finset (Direction F)) : Finset (Direction F) :=
  D.filter (fun d => d ≠ g ∧ d ∉ generatorSet T)

theorem sum_freshWitness_probability_le
    (g : Direction F) (T : FourTuple F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (d : Direction F) (hdD : d ∈ D) (hdg : d ≠ g) :
    (∑ e ∈ freshWitnessDirections g T D, ∑ i : Fin 4, ∑ j : Fin 4,
      conditionalProbability D a (mixedExternalEvent g T d e i j)) ≤
      128 * conditionalProbability D a (successfulInDirection T g) /
        (Fintype.card F : ℝ) := by
  let p := conditionalProbability D a (successfulInDirection T g)
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hcard : ((freshWitnessDirections g T D).card : ℝ) ≤
      (Fintype.card F : ℝ) + 1 := by
    exact_mod_cast (show (freshWitnessDirections g T D).card ≤ Fintype.card F + 1 by
      simpa only [Direction, Fintype.card_option] using
        Finset.card_le_univ (freshWitnessDirections g T D))
  calc
    _ ≤ ∑ _e ∈ freshWitnessDirections g T D, ∑ _i : Fin 4, ∑ _j : Fin 4,
        4 * p / (Fintype.card F : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro e he
      have he' := (Finset.mem_filter.mp he).2
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply mixedExternalEvent_probability_le g T D a d e hdD hdg he'.1
      intro k hk
      exact he'.2.2 (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)
    _ = ((freshWitnessDirections g T D).card : ℝ) *
        (64 * p / (Fintype.card F : ℝ)^2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ ((Fintype.card F : ℝ) + 1) *
        (64 * p / (Fintype.card F : ℝ)^2) := by gcongr
    _ ≤ 128 * p / (Fintype.card F : ℝ) := by
      apply (le_div_iff₀ hq).mpr
      have hq0 := ne_of_gt hq
      field_simp
      nlinarith [mul_nonneg hp (sub_nonneg.mpr hq1)]

def mixedExternalProbabilitySum (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) : ℝ :=
  ∑ T ∈ (eligibleTuples g).filter
      (fun T => 0 < (PartialAlignment.exposedTupleIndices T D).card),
    ∑ d ∈ oldWitnessDirections g T D,
      ∑ e ∈ freshWitnessDirections g T D, ∑ i : Fin 4, ∑ j : Fin 4,
        conditionalProbability D a (mixedExternalEvent g T d e i j)

theorem mixedExternalProbabilitySum_le_overlap
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F) :
    mixedExternalProbabilitySum g D a ≤
      (128 * (D.card : ℝ) / Fintype.card F) * overlapProbabilitySum g D a := by
  unfold mixedExternalProbabilitySum overlapProbabilitySum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T hT
  have hp : 0 ≤ conditionalProbability D a (successfulInDirection T g) :=
    ENNReal.toReal_nonneg
  calc
    _ ≤ ∑ _d ∈ oldWitnessDirections g T D,
        128 * conditionalProbability D a (successfulInDirection T g) /
          (Fintype.card F : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd' := Finset.mem_filter.mp hd
      exact sum_freshWitness_probability_le g T D a d hd'.1 hd'.2.1
    _ = ((oldWitnessDirections g T D).card : ℝ) *
        (128 * conditionalProbability D a (successfulInDirection T g) /
          (Fintype.card F : ℝ)) := by simp
    _ ≤ (D.card : ℝ) *
        (128 * conditionalProbability D a (successfulInDirection T g) /
          (Fintype.card F : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Finset.card_filter_le D (fun d => d ≠ g ∧ d ∉ generatorSet T)
      · positivity
    _ = _ := by ring

theorem mixedExternalProbabilitySum_le
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) :
    mixedExternalProbabilitySum g D a ≤
      2097152 * ((m : ℝ) + 1)^5 / (Fintype.card F : ℝ) := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcard : (D.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast (by omega : D.card ≤ m + 1)
  calc
    _ ≤ (128 * (D.card : ℝ) / Fintype.card F) * overlapProbabilitySum g D a :=
      mixedExternalProbabilitySum_le_overlap g D a
    _ ≤ (128 * (D.card : ℝ) / Fintype.card F) * (16384 * ((m : ℝ) + 1)^4) := by
      apply mul_le_mul_of_nonneg_left (overlapProbabilitySum_le g D a m hD)
      positivity
    _ ≤ (128 * ((m : ℝ) + 1) / Fintype.card F) *
        (16384 * ((m : ℝ) + 1)^4) := by gcongr
    _ = _ := by ring

end
end Balanced.CandidateMixedExternal

end OAI
