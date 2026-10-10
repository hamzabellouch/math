import Mathlib
import OAI.LinearAlgebra.MatrixFields.Histories.GroupOrbitTransport

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointAmbientDegree

open MatrixMultiplication.Foundation JointPopulation
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
  (counts : H → Shape → ℕ)

def localWord (t : JointCoarseHashing.Triple (Position counts)) (h : H) :
    Positions counts h → Shape :=
  fun i => (t.1 ⟨h, i⟩, t.2.1 ⟨h, i⟩, t.2.2 ⟨h, i⟩)

omit [Fintype H] [DecidableEq H] in
theorem localWord_injective : Function.Injective (localWord counts) := by
  intro t u he
  apply Prod.ext
  · funext p
    exact congrArg (fun w => (w p.1 p.2).1) he
  · apply Prod.ext
    · funext p
      exact congrArg (fun w => (w p.1 p.2).2.1) he
    · funext p
      exact congrArg (fun w => (w p.1 p.2).2.2) he

def localAllowed (sum : H → ℕ) (h : H) (w : Positions counts h → Shape) : Prop :=
  (∀ i, (w i).1.val + (w i).2.1.val + (w i).2.2.val = sum h) ∧
    ∀ s a, wordPopulation (shapeSide s ∘ w) a =
      wordPopulation (sideWord counts s (triple counts (canonicalTarget counts)) h) a

theorem localAllowed_of_mem_ambient (sum : H → ℕ)
    (t : JointCoarseHashing.Triple (Position counts))
    (ht : t ∈ ambientSet counts sum) (h : H) :
    localAllowed counts sum h (localWord counts t h) := by
  obtain ⟨hs, hm⟩ := (Finset.mem_filter.mp ht).2
  exact ⟨fun i => hs ⟨h, i⟩, fun s a => hm h s a⟩

def sameSide (s : Fin 3) (t e : JointCoarseHashing.Triple (Position counts)) : Prop :=
  ∀ h, sideWord counts s t h = sideWord counts s e h

def sharedAmbient (sum : H → ℕ) (s : Fin 3)
    (e : JointCoarseHashing.Triple (Position counts)) :
    Finset (JointCoarseHashing.Triple (Position counts)) :=
  (ambientSet counts sum).filter (sameSide counts s · e)

def classBound (s : Fin 3) (e : JointCoarseHashing.Triple (Position counts))
    (h : H) (entropyCap : ℝ) : ℝ :=
  ((Fintype.card (Positions counts h) : ℝ) + 1) ^ Fintype.card Shape *
    Real.exp ((Fintype.card (Positions counts h) : ℝ) *
      (entropyCap - finiteEntropy (fun a =>
        (wordPopulation (sideWord counts s e h) a : ℝ) /
          Fintype.card (Positions counts h))) +
      ((Fintype.card Shape : ℝ) + (Fintype.card (Fin 17) : ℝ) + 2) *
        (1 + Real.log (Fintype.card (Positions counts h) + 1 : ℕ)))

def classExponent (s : Fin 3) (e : JointCoarseHashing.Triple (Position counts))
    (h : H) (entropyCap : ℝ) : ℝ :=
  (Fintype.card (Positions counts h) : ℝ) *
      (entropyCap - finiteEntropy (fun a =>
        (wordPopulation (sideWord counts s e h) a : ℝ) /
          Fintype.card (Positions counts h))) +
    ((Fintype.card Shape : ℝ) + (Fintype.card (Fin 17) : ℝ) + 2) *
      (1 + Real.log (Fintype.card (Positions counts h) + 1 : ℕ)) +
    (Fintype.card Shape : ℝ) * Real.log (Fintype.card (Positions counts h) + 1 : ℕ)

omit [Fintype H] [DecidableEq H] in
theorem classBound_eq_exp (s : Fin 3)
    (e : JointCoarseHashing.Triple (Position counts)) (h : H) (entropyCap : ℝ) :
    classBound counts s e h entropyCap = Real.exp (classExponent counts s e h entropyCap) := by
  unfold classBound classExponent
  conv_rhs => rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity)]
  simp only [Nat.cast_add, Nat.cast_one]
  exact mul_comm _ _

omit [Fintype H] [DecidableEq H] in
theorem classExponent_target_eq (s : Fin 3) (e : Target counts) (h : H)
    (entropyCap : ℝ) :
    classExponent counts s (triple counts e) h entropyCap =
      classExponent counts s (triple counts (canonicalTarget counts)) h entropyCap := by
  simp_rw [classExponent, marginal_population_eq counts e (canonicalTarget counts)]

theorem sharedAmbient_card_le (sum : H → ℕ) (s : Fin 3)
    (e : JointCoarseHashing.Triple (Position counts)) (entropyCap : H → ℝ)
    (hentropy : ∀ h w, localAllowed counts sum h w →
      finiteEntropy (fun a => (wordPopulation w a : ℝ) /
        Fintype.card (Positions counts h)) ≤ entropyCap h) :
    ((sharedAmbient counts sum s e).card : ℝ) ≤
      ∏ h, classBound counts s e h (entropyCap h) := by
  classical
  let Allowed := fun h (w : Positions counts h → Shape) =>
    localAllowed counts sum h w ∧ ∀ i, shapeSide s (w i) = sideWord counts s e h i
  let Local := fun h => {w : Positions counts h → Shape // Allowed h w}
  let encode : {t // t ∈ sharedAmbient counts sum s e} → ∀ h, Local h := fun t h =>
    ⟨localWord counts t.val h, localAllowed_of_mem_ambient counts sum t.val
      (Finset.mem_filter.mp t.property).1 h,
      fun i => congrFun ((Finset.mem_filter.mp t.property).2 h) i⟩
  have hinj : Function.Injective encode := by
    intro t u he
    apply Subtype.ext
    apply localWord_injective counts
    funext h
    exact congrArg Subtype.val (congrFun he h)
  have hcard : (sharedAmbient counts sum s e).card ≤ ∏ h, Fintype.card (Local h) := by
    simpa only [Fintype.card_coe, Fintype.card_pi] using
      Fintype.card_le_of_injective encode hinj
  have hlocal (h : H) : (Fintype.card (Local h) : ℝ) ≤
      classBound counts s e h (entropyCap h) := by
    exact JointTypeCounts.card_allowed_over_coarse_le (shapeSide s)
      (sideWord counts s e h) (Allowed h) (entropyCap h)
      (fun w hw => hw.2) (fun w hw => hentropy h w hw.1)
  calc
    ((sharedAmbient counts sum s e).card : ℝ) ≤
        ∏ h, (Fintype.card (Local h) : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun history _ => hlocal history)

omit [Fintype H] [DecidableEq H] in
theorem sharesSide_iff (t e : JointCoarseHashing.Triple (Position counts)) :
    JointCoarseHashing.SharesSide t e ↔ ∃ s : Fin 3, sameSide counts s t e := by
  constructor
  · rintro (hx | hy | hz)
    · refine ⟨0, fun h => ?_⟩
      funext i
      change t.1 ⟨h, i⟩ = e.1 ⟨h, i⟩
      exact congrFun hx.symm ⟨h, i⟩
    · refine ⟨1, fun h => ?_⟩
      funext i
      change t.2.1 ⟨h, i⟩ = e.2.1 ⟨h, i⟩
      exact congrFun hy.symm ⟨h, i⟩
    · refine ⟨2, fun h => ?_⟩
      funext i
      change t.2.2 ⟨h, i⟩ = e.2.2 ⟨h, i⟩
      exact congrFun hz.symm ⟨h, i⟩
  · rintro ⟨s, hs⟩
    fin_cases s
    · apply Or.inl
      funext p
      simpa [sideWord, shapeSide] using (congrFun (hs p.1) p.2).symm
    · apply Or.inr ∘ Or.inl
      funext p
      simpa [sideWord, shapeSide] using (congrFun (hs p.1) p.2).symm
    · apply Or.inr ∘ Or.inr
      funext p
      simpa [sideWord, shapeSide] using (congrFun (hs p.1) p.2).symm

def neighbors (sum : H → ℕ) (e : JointCoarseHashing.Triple (Position counts)) :
    Finset (JointCoarseHashing.Triple (Position counts)) :=
  (ambientSet counts sum).filter (fun t => t ≠ e ∧ JointCoarseHashing.SharesSide t e)

theorem neighbors_card_le_sum (sum : H → ℕ)
    (e : JointCoarseHashing.Triple (Position counts)) :
    (neighbors counts sum e).card ≤ ∑ s : Fin 3, (sharedAmbient counts sum s e).card := by
  classical
  have hsub : neighbors counts sum e ⊆
      (ambientSet counts sum).filter (fun t => ∃ s ∈ (Finset.univ : Finset (Fin 3)),
        sameSide counts s t e) := by
    intro t ht
    obtain ⟨ha, _, hs⟩ := Finset.mem_filter.mp ht
    obtain ⟨s, hs⟩ := (sharesSide_iff counts t e).mp hs
    exact Finset.mem_filter.mpr ⟨ha, s, Finset.mem_univ _, hs⟩
  apply (Finset.card_le_card hsub).trans
  convert JointLossCounts.card_filter_exists_le (ambientSet counts sum) Finset.univ
    (fun side target => sameSide counts side target e) using 1 <;>
    simp [sharedAmbient]

theorem neighbors_card_le (sum : H → ℕ)
    (e : JointCoarseHashing.Triple (Position counts)) (entropyCap : H → ℝ)
    (hentropy : ∀ h w, localAllowed counts sum h w →
      finiteEntropy (fun a => (wordPopulation w a : ℝ) /
        Fintype.card (Positions counts h)) ≤ entropyCap h) :
    ((neighbors counts sum e).card : ℝ) ≤
      ∑ s : Fin 3, ∏ h, classBound counts s e h (entropyCap h) := by
  calc
    ((neighbors counts sum e).card : ℝ) ≤
        ∑ s : Fin 3, ((sharedAmbient counts sum s e).card : ℝ) := by
      exact_mod_cast neighbors_card_le_sum counts sum e
    _ ≤ _ := Finset.sum_le_sum fun s _ => sharedAmbient_card_le counts sum s e entropyCap hentropy

theorem neighbors_card_le_three_exp (sum : H → ℕ)
    (e : JointCoarseHashing.Triple (Position counts)) (entropyCap : H → ℝ)
    (hentropy : ∀ h w, localAllowed counts sum h w →
      finiteEntropy (fun a => (wordPopulation w a : ℝ) /
        Fintype.card (Positions counts h)) ≤ entropyCap h)
    (exponent : ℝ)
    (hupper : ∀ s : Fin 3, ∑ h, classExponent counts s e h (entropyCap h) ≤ exponent) :
    ((neighbors counts sum e).card : ℝ) ≤ 3 * Real.exp exponent := by
  have hprod (s : Fin 3) : (∏ h, classBound counts s e h (entropyCap h)) ≤
      Real.exp exponent := by
    simp_rw [classBound_eq_exp]
    rw [← Real.exp_sum]
    exact Real.exp_le_exp.mpr (hupper s)
  calc
    ((neighbors counts sum e).card : ℝ) ≤
        ∑ s : Fin 3, ∏ h, classBound counts s e h (entropyCap h) :=
      neighbors_card_le counts sum e entropyCap hentropy
    _ ≤ ∑ _s : Fin 3, Real.exp exponent := Finset.sum_le_sum fun s _ => hprod s
    _ = _ := by simp

theorem log_neighbors_card_le (sum : H → ℕ)
    (e : JointCoarseHashing.Triple (Position counts)) (entropyCap : H → ℝ)
    (hentropy : ∀ h w, localAllowed counts sum h w →
      finiteEntropy (fun a => (wordPopulation w a : ℝ) /
        Fintype.card (Positions counts h)) ≤ entropyCap h)
    (exponent : ℝ)
    (hupper : ∀ s : Fin 3, ∑ h, classExponent counts s e h (entropyCap h) ≤ exponent)
    (hne : 0 < (neighbors counts sum e).card) :
    Real.log ((neighbors counts sum e).card : ℝ) ≤ Real.log 3 + exponent := by
  have hb := Real.log_le_log (by exact_mod_cast hne :
      (0 : ℝ) < (neighbors counts sum e).card)
    (neighbors_card_le_three_exp counts sum e entropyCap hentropy exponent hupper)
  simpa only [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp] using hb

end MatrixMultiplication.JointAmbientDegree






namespace MatrixMultiplication.AllFieldGroupDegrees

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldGroupOrbitData JointPopulation JointCanonicalization
open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

abbrev Letter (sigma : Placement) (h : ActiveOrder K tick sigma) :=
  Fin (activeHalfLength h.val) → Fin 7

abbrev Class (sigma : Placement) := ActiveOrder K tick sigma × Fin 17

abbrev Symbol (sigma : Placement) (c : Class (K := K) (tick := tick) sigma) :=
  Statistic c.1.val

def projectedStatistic (sigma : Placement)
    (c : Class (K := K) (tick := tick) sigma) : Letter (K := K) (tick := tick) sigma c.1 → Symbol (K := K) (tick := tick) sigma c :=
  statistic c.1.val

def classDesignated (right : Bool) (side : Fin 3) (sigma : Placement)
    (c : Class (K := K) (tick := tick) sigma) (u : JointPopulation.Shape) : Prop :=
  designated right side sigma c.1 u

def classLaw (right : Bool) (side : Fin 3) (sigma : Placement)
    (c : Class (K := K) (tick := tick) sigma) (u : JointPopulation.Shape) :
    Symbol (K := K) (tick := tick) sigma c → ℝ := compatibilityLaw right side sigma c.1 u

theorem tripleSide_eq_sideWord (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (s : Fin 3) (t : JointCoarseHashing.Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (h : ActiveOrder K tick sigma) (i : JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) :
    tripleSide s t ⟨h, i⟩ = sideWord (Counts (K := K) (tick := tick) allocation m sigma) s t h i := by
  fin_cases s <;> rfl

theorem tripleSide_triple (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (s : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (h : ActiveOrder K tick sigma) (i : JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) :
    tripleSide s (triple (Counts (K := K) (tick := tick) allocation m sigma) e) ⟨h, i⟩ =
      shapeSide s ((e h).val i) := by
  fin_cases s <;> rfl

theorem childWidth_le {ε : ℝ} (hε : 0 ≤ ε) (h : Active K tick) :
    AllFieldHistoryMasks.childWidth ε h ≤ ε := by
  have hp : 0 ≤ AllFieldHistoryMasks.pairWidth ε h := by
    unfold AllFieldHistoryMasks.pairWidth
    positivity
  calc
    AllFieldHistoryMasks.childWidth ε h ≤ AllFieldHistoryMasks.pairWidth ε h :=
      div_le_self hp (by norm_num)
    _ ≤ ε := div_le_self hε (one_le_pow₀ (by norm_num))

theorem fineCompatible_uniform (allocation : Allocation) (m : ℕ)
    {ε χ : ℝ} (hε : 0 ≤ ε) (hχ : ε ≤ χ) (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : fineCompatible allocation m ε sigma side e w) :
    JointPopulationCompatibility.Compatible (Counts (K := K) (tick := tick) allocation m sigma)
      (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
      (projectedStatistic sigma) (projectedStatistic sigma)
      (classDesignated false side sigma) (classDesignated true side sigma)
      (classLaw false side sigma) (classLaw true side sigma) χ (sigma side) e w := by
  constructor
  · intro h u hd a
    exact (hw false h u hd a).trans
      (mul_le_mul_of_nonneg_left ((childWidth_le hε h.val).trans hχ) (Nat.cast_nonneg _))
  · intro h u hd a
    exact (hw true h u hd a).trans
      (mul_le_mul_of_nonneg_left ((childWidth_le hε h.val).trans hχ) (Nat.cast_nonneg _))

def uniformCompatible (allocation : Allocation) (m : ℕ) (χ : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) : Prop :=
  JointPopulationCompatibility.compatibleWithCoarse (Counts (K := K) (tick := tick) allocation m sigma)
    (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
    (projectedStatistic sigma) (projectedStatistic sigma)
    (classDesignated false side sigma) (classDesignated true side sigma)
    (classLaw false side sigma) (classLaw true side sigma) χ
    (ownWord allocation m sigma) (sigma side) (triple (Counts (K := K) (tick := tick) allocation m sigma) e) w

theorem Compatible_uniform (allocation : Allocation) (m : ℕ)
    {ε χ : ℝ} (hε : 0 ≤ ε) (hχ : ε ≤ χ) (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : Compatible allocation m ε sigma side e w) :
    uniformCompatible allocation m χ sigma side e w := by
  apply (JointPopulationCompatibility.compatibleWithCoarse_target
    (Counts (K := K) (tick := tick) allocation m sigma) (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma)
    (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (projectedStatistic sigma) (projectedStatistic sigma)
    (classDesignated false side sigma) (classDesignated true side sigma)
    (classLaw false side sigma) (classLaw true side sigma) χ
    (ownWord allocation m sigma) (sigma side) e w).2
  refine ⟨?_, fineCompatible_uniform allocation m hε hχ sigma side e w hw.2⟩
  intro h i
  have hh := congrFun hw.1 ⟨h, i⟩
  simpa only [coarse, tripleSide_reorder, tripleSide_triple] using hh

def conditionalCount (allocation : Allocation) (m : ℕ) (χ : ℝ)
    (sigma : Placement) (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) : ℕ :=
  JointPopulationCompatibility.compatibleTargetCount (Counts (K := K) (tick := tick) allocation m sigma)
    (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
    (projectedStatistic sigma) (projectedStatistic sigma)
    (classDesignated false side sigma) (classDesignated true side sigma)
    (classLaw false side sigma) (classLaw true side sigma) χ
    (sigma side) (ownWord allocation m sigma w) w

theorem uniformCompatible_count (allocation : Allocation) (m : ℕ) (χ : ℝ)
    (sigma : Placement) (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) :
    Fintype.card {e : Targets (K := K) (tick := tick) allocation m sigma //
      uniformCompatible allocation m χ sigma side e w} =
      conditionalCount allocation m χ sigma side w :=
  JointPopulationCompatibility.compatibleWithCoarse_target_count
    (Counts (K := K) (tick := tick) allocation m sigma) (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma)
    (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (projectedStatistic sigma) (projectedStatistic sigma)
    (classDesignated false side sigma) (classDesignated true side sigma)
    (classLaw false side sigma) (classLaw true side sigma) χ
    (ownWord allocation m sigma) (sigma side) w

theorem competitors_card_le_conditionalCount (allocation : Allocation) (m : ℕ)
    {ε χ : ℝ} (hε : 0 ≤ ε) (hχ : ε ≤ χ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (v : Variable (K := K) (tick := tick) allocation m sigma) :
    (competitors allocation m ε sigma e o v).card ≤
      conditionalCount allocation m χ sigma v.1 v.2 := by
  classical
  let candidates : Finset (Targets (K := K) (tick := tick) allocation m sigma) :=
    Finset.univ.filter fun f => uniformCompatible allocation m χ sigma v.1 f v.2
  have hsub : competitors allocation m ε sigma e o v ⊆
      candidates.image (coarse allocation m sigma) := by
    intro t ht
    obtain ⟨f, hf, hc⟩ := (Finset.mem_filter.mp ht).2.2.2
    exact Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Compatible_uniform allocation m hε hχ sigma v.1 f v.2 hc⟩, hf⟩
  calc
    (competitors allocation m ε sigma e o v).card ≤
        (candidates.image (coarse allocation m sigma)).card := Finset.card_le_card hsub
    _ ≤ candidates.card := Finset.card_image_le
    _ = Fintype.card {f : Targets (K := K) (tick := tick) allocation m sigma //
        uniformCompatible allocation m χ sigma v.1 f v.2} := by
      simp only [candidates, Fintype.card_subtype]
    _ = conditionalCount allocation m χ sigma v.1 v.2 :=
      uniformCompatible_count allocation m χ sigma v.1 v.2

theorem eligibility_card_le_sharedAmbient (allocation : Allocation) (m : ℕ)
    (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) :
    ((data allocation m ε sigma).eligibilityCompetitors e).card ≤
      (JointAmbientDegree.sharedAmbient (Counts (K := K) (tick := tick) allocation m sigma)
        (fun h => 2 * activeHalfLength h.val) (sigma 0)
        (triple (Counts (K := K) (tick := tick) allocation m sigma) e)).card := by
  let a := JointAmbientDegree.sharedAmbient (Counts (K := K) (tick := tick) allocation m sigma)
    (fun h => 2 * activeHalfLength h.val) (sigma 0)
    (triple (Counts (K := K) (tick := tick) allocation m sigma) e)
  have hs : (data allocation m ε sigma).eligibilityCompetitors e ⊆
      a.image (reorder sigma) := by
    intro f hf
    obtain ⟨ha, _, hx⟩ :=
      ((data allocation m ε sigma).mem_eligibilityCompetitors e f).1 hf
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
    apply Finset.mem_image.mpr
    refine ⟨t, Finset.mem_filter.mpr ⟨ht, ?_⟩, rfl⟩
    intro h
    funext i
    have hh := congrFun hx ⟨h, i⟩
    change tripleSide (sigma 0) t ⟨h, i⟩ =
      tripleSide (sigma 0) (triple (Counts (K := K) (tick := tick) allocation m sigma) e) ⟨h, i⟩ at hh
    simpa only [tripleSide_eq_sideWord] using hh
  exact (Finset.card_le_card hs).trans Finset.card_image_le

end MatrixMultiplication.AllFieldGroupDegrees






namespace MatrixMultiplication.JointMarginalSupport

open MatrixMultiplication.Foundation JointPopulation JointAmbientDegree
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → Shape → ℕ) (sum : H → ℕ)

omit [Fintype H] [DecidableEq H] in
theorem localAllowed_coordinate_witness (h : H) (w : Positions counts h → Shape)
    (hw : localAllowed counts sum h w) (s : Fin 3) (i : Positions counts h) :
    ∃ j : Positions counts h,
      shapeSide s ((canonicalTarget counts h).val j) = shapeSide s (w i) := by
  have hp : 0 < wordPopulation (shapeSide s ∘ w) (shapeSide s (w i)) := by
    unfold wordPopulation
    exact Fintype.card_pos_iff.mpr ⟨⟨i, rfl⟩⟩
  rw [hw.2 s (shapeSide s (w i))] at hp
  obtain ⟨⟨j, hj⟩⟩ := Fintype.card_pos_iff.mp hp
  exact ⟨j, hj⟩

omit [Fintype H] [DecidableEq H] in
theorem localAllowed_coordinate_support (h : H) (w : Positions counts h → Shape)
    (hw : localAllowed counts sum h w) (allowed : Fin 3 → Fin 17 → Prop)
    (hallowed : ∀ u, 0 < counts h u → ∀ s, allowed s (shapeSide s u)) :
    ∀ i s, allowed s (shapeSide s (w i)) := by
  intro i s
  obtain ⟨j, hj⟩ := localAllowed_coordinate_witness counts sum h w hw s i
  rw [← hj]
  exact hallowed ((canonicalTarget counts h).val j)
    (symbol_count_pos counts (canonicalTarget counts) h j) s

omit [Fintype H] [DecidableEq H] in
theorem localAllowed_parent_bounds (h : H) (w : Positions counts h → Shape)
    (hw : localAllowed counts sum h w) (parent : Fin 3 → ℕ)
    (hparent : ∀ u, 0 < counts h u → ∀ s, (shapeSide s u).val ≤ parent s) :
    ∀ i s, (shapeSide s (w i)).val ≤ parent s :=
  localAllowed_coordinate_support counts sum h w hw
    (fun s a => a.val ≤ parent s) hparent

omit [Fintype H] [DecidableEq H] in
theorem localAllowed_positive_reference (h : H) (w : Positions counts h → Shape)
    (hw : localAllowed counts sum h w) (parent : Fin 3 → ℕ) (p : Shape → ℝ)
    (hparent : ∀ u, 0 < counts h u → ∀ s, (shapeSide s u).val ≤ parent s)
    (hp : ∀ u : Shape, u.1.val + u.2.1.val + u.2.2.val = sum h →
      (∀ s, (shapeSide s u).val ≤ parent s) → 0 < p u) :
    ∀ i, 0 < p (w i) := by
  intro i
  exact hp (w i) (hw.1 i) (localAllowed_parent_bounds counts sum h w hw parent hparent i)

end MatrixMultiplication.JointMarginalSupport

end
end

end MatrixAllFields

end OAI
