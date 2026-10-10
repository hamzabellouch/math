import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.Population
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.TypeCounts

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

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
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun h _ => hlocal h)

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
      (Finset.univ : Finset (Fin 3)).biUnion (fun s => sharedAmbient counts sum s e) := by
    intro t ht
    obtain ⟨ha, _, hs⟩ := Finset.mem_filter.mp ht
    obtain ⟨s, hs⟩ := (sharesSide_iff counts t e).mp hs
    exact Finset.mem_biUnion.mpr
      ⟨s, Finset.mem_univ _, Finset.mem_filter.mpr ⟨ha, hs⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

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

end

end OAI
