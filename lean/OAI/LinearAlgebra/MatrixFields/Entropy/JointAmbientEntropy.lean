import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.JointGibbsApproximation
import OAI.LinearAlgebra.MatrixFields.Construction.JointMarginalSupport

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators Topology
open Filter MatrixMultiplication.Foundation
open MatrixMultiplication.JointPopulation MatrixMultiplication.JointAmbientDegree
open MatrixMultiplication.JointGibbsApproximation

namespace MatrixMultiplication.JointAmbientEntropy

section Empirical

variable {I A B : Type*} [Fintype I]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def empiricalFiniteLaw (w : I → A) (hpos : 0 < Fintype.card I) : FiniteLaw A where
  mass a := (wordPopulation w a : ℝ) / Fintype.card I
  nonneg a := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  total := by
    rw [← Finset.sum_div, ← Nat.cast_sum, wordPopulation_sum]
    exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos))

@[simp] theorem empiricalFiniteLaw_mass (w : I → A) (hpos : 0 < Fintype.card I) (a : A) :
    (empiricalFiniteLaw w hpos).mass a =
      (wordPopulation w a : ℝ) / Fintype.card I := rfl

theorem empiricalFiniteLaw_map_mass (w : I → A) (hpos : 0 < Fintype.card I)
    (f : A → B) (b : B) :
    ((empiricalFiniteLaw w hpos).map f).mass b =
      (wordPopulation (f ∘ w) b : ℝ) / Fintype.card I := by
  rw [FiniteLaw.map_mass, InheritedMasks.wordPopulation_statistic,
    Nat.cast_sum, Finset.sum_div, Finset.sum_filter]
  simp only [empiricalFiniteLaw_mass]

theorem empiricalFiniteLaw_supported (w : I → A) (hpos : 0 < Fintype.card I)
    (p : FiniteLaw A) (hsupport : ∀ i, 0 < p.mass (w i)) :
    ∀ a, p.mass a = 0 → (empiricalFiniteLaw w hpos).mass a = 0 := by
  intro a ha
  have : IsEmpty {i : I // w i = a} := ⟨fun i => by
    have hp := hsupport i.val
    rw [i.property, ha] at hp
    exact lt_irrefl 0 hp⟩
  simp only [empiricalFiniteLaw_mass, wordPopulation, Fintype.card_of_isEmpty,
    Nat.cast_zero, zero_div]

end Empirical

variable {H : Type*}

def canonicalLaw (counts : H → Shape → ℕ) (h : H) : FiniteLaw Shape :=
  if hpos : 0 < Fintype.card (Positions counts h) then
    empiricalFiniteLaw ((canonicalTarget counts) h).val hpos
  else FiniteLaw.pure (0, 0, 0)

theorem canonicalLaw_mass_of_pos (counts : H → Shape → ℕ) (h : H)
    (hpos : 0 < Fintype.card (Positions counts h)) (a : Shape) :
    (canonicalLaw counts h).mass a =
      (counts h a : ℝ) / Fintype.card (Positions counts h) := by
  rw [canonicalLaw, dite_eq_left hpos, empiricalFiniteLaw_mass,
    ((canonicalTarget counts) h).property]

theorem total_mul_canonicalLaw_mass (counts : H → Shape → ℕ) (h : H) (a : Shape) :
    (Fintype.card (Positions counts h) : ℝ) * (canonicalLaw counts h).mass a =
      counts h a := by
  by_cases hpos : 0 < Fintype.card (Positions counts h)
  · rw [canonicalLaw_mass_of_pos counts h hpos]
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos))
  · have hzero : Fintype.card (Positions counts h) = 0 := Nat.eq_zero_of_not_pos hpos
    have hsum : ∑ a, counts h a = 0 := by simpa only [Positions, Fintype.card_fin] using hzero
    have ha : counts h a = 0 := by
      have hle : counts h a ≤ ∑ b, counts h b :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      rw [hsum] at hle
      exact Nat.eq_zero_of_le_zero hle
    simp only [hzero, ha, Nat.cast_zero, zero_mul]

theorem localAllowed_marginal_eq (counts : H → Shape → ℕ) (sum : H → ℕ)
    (h : H) (w : Positions counts h → Shape)
    (hpos : 0 < Fintype.card (Positions counts h))
    (hw : localAllowed counts sum h w) (s : Fin 3) :
    ((empiricalFiniteLaw w hpos).map (shapeSide s)).mass =
      ((canonicalLaw counts h).map (shapeSide s)).mass := by
  rw [canonicalLaw, dite_eq_left hpos]
  funext a
  rw [empiricalFiniteLaw_map_mass, empiricalFiniteLaw_map_mass]
  exact congrArg (fun n : ℕ => (n : ℝ) / Fintype.card (Positions counts h)) (hw.2 s a)

def gibbsCap (counts : H → Shape → ℕ) (h : H) (p : FiniteLaw Shape)
    (u v w : Fin 17 → ℝ) : ℝ :=
  finiteEntropy p.mass + marginalError p (canonicalLaw counts h) (shapeSide 0) u +
    marginalError p (canonicalLaw counts h) (shapeSide 1) v +
    marginalError p (canonicalLaw counts h) (shapeSide 2) w

theorem gibbsCap_nonneg (counts : H → Shape → ℕ) (h : H) (p : FiniteLaw Shape)
    (u v w : Fin 17 → ℝ) : 0 ≤ gibbsCap counts h p u v w := by
  exact add_nonneg
    (add_nonneg (add_nonneg p.entropy_nonneg (marginalError_nonneg _ _ _ _))
      (marginalError_nonneg _ _ _ _)) (marginalError_nonneg _ _ _ _)

theorem localAllowed_entropy_le_of_word_support (counts : H → Shape → ℕ) (sum : H → ℕ)
    (h : H) (w : Positions counts h → Shape) (p : FiniteLaw Shape)
    (u v z : Fin 17 → ℝ) (c : ℝ)
    (hsupport : ∀ i, 0 < p.mass (w i))
    (hlog : ∀ a, 0 < p.mass a → Real.log (p.mass a) =
      u (shapeSide 0 a) + v (shapeSide 1 a) + z (shapeSide 2 a) - c)
    (hw : localAllowed counts sum h w) :
    finiteEntropy (fun a => (wordPopulation w a : ℝ) /
      Fintype.card (Positions counts h)) ≤ gibbsCap counts h p u v z := by
  by_cases hpos : 0 < Fintype.card (Positions counts h)
  · have hs := empiricalFiniteLaw_supported w hpos p hsupport
    have hg := entropy_le_of_marginal_errors_of_support p (empiricalFiniteLaw w hpos)
      (shapeSide 0) (shapeSide 1) (shapeSide 2) u v z c hs hlog
    have hx := localAllowed_marginal_eq counts sum h w hpos hw (0 : Fin 3)
    have hy := localAllowed_marginal_eq counts sum h w hpos hw (1 : Fin 3)
    have hz := localAllowed_marginal_eq counts sum h w hpos hw (2 : Fin 3)
    change finiteEntropy (fun a => (wordPopulation w a : ℝ) /
      Fintype.card (Positions counts h)) ≤ _ at hg
    simpa only [gibbsCap, marginalError, hx, hy, hz] using hg
  · have hzero : Fintype.card (Positions counts h) = 0 := Nat.eq_zero_of_not_pos hpos
    simpa only [hzero, Nat.cast_zero, div_zero, finiteEntropy, entropyTerm_zero,
      Finset.sum_const_zero] using gibbsCap_nonneg counts h p u v z

theorem localAllowed_entropy_le (counts : H → Shape → ℕ) (sum : H → ℕ)
    (h : H) (w : Positions counts h → Shape) (p : FiniteLaw Shape)
    (u v z : Fin 17 → ℝ) (c : ℝ)
    (hsupport : ∀ a : Shape, a.1.val + a.2.1.val + a.2.2.val = sum h → 0 < p.mass a)
    (hlog : ∀ a, 0 < p.mass a → Real.log (p.mass a) =
      u (shapeSide 0 a) + v (shapeSide 1 a) + z (shapeSide 2 a) - c)
    (hw : localAllowed counts sum h w) :
    finiteEntropy (fun a => (wordPopulation w a : ℝ) /
      Fintype.card (Positions counts h)) ≤ gibbsCap counts h p u v z :=
  localAllowed_entropy_le_of_word_support counts sum h w p u v z c
    (fun i => hsupport (w i) (hw.1 i)) hlog hw

section

variable [Fintype H] [DecidableEq H]

theorem sharedAmbient_card_le_of_supported_gibbs (counts : H → Shape → ℕ) (sum : H → ℕ)
    (s : Fin 3) (e : JointCoarseHashing.Triple (Position counts))
    (p : H → FiniteLaw Shape) (u v w : H → Fin 17 → ℝ) (c : H → ℝ)
    (hsupport : ∀ h word, localAllowed counts sum h word → ∀ i, 0 < (p h).mass (word i))
    (hlog : ∀ h a, 0 < (p h).mass a → Real.log ((p h).mass a) =
      u h (shapeSide 0 a) + v h (shapeSide 1 a) + w h (shapeSide 2 a) - c h) :
    ((sharedAmbient counts sum s e).card : ℝ) ≤
      ∏ h, classBound counts s e h (gibbsCap counts h (p h) (u h) (v h) (w h)) :=
  sharedAmbient_card_le counts sum s e _
    (fun h word hw => localAllowed_entropy_le_of_word_support counts sum h word (p h)
      (u h) (v h) (w h) (c h) (hsupport h word hw) (hlog h) hw)

theorem neighbors_card_le_of_supported_gibbs (counts : H → Shape → ℕ) (sum : H → ℕ)
    (e : JointCoarseHashing.Triple (Position counts))
    (p : H → FiniteLaw Shape) (u v w : H → Fin 17 → ℝ) (c : H → ℝ)
    (hsupport : ∀ h word, localAllowed counts sum h word → ∀ i, 0 < (p h).mass (word i))
    (hlog : ∀ h a, 0 < (p h).mass a → Real.log ((p h).mass a) =
      u h (shapeSide 0 a) + v h (shapeSide 1 a) + w h (shapeSide 2 a) - c h) :
    ((neighbors counts sum e).card : ℝ) ≤
      ∑ s : Fin 3, ∏ h, classBound counts s e h
        (gibbsCap counts h (p h) (u h) (v h) (w h)) :=
  neighbors_card_le counts sum e _
    (fun h word hw => localAllowed_entropy_le_of_word_support counts sum h word (p h)
      (u h) (v h) (w h) (c h) (hsupport h word hw) (hlog h) hw)

theorem sharedAmbient_card_le_of_gibbs (counts : H → Shape → ℕ) (sum : H → ℕ)
    (s : Fin 3) (e : JointCoarseHashing.Triple (Position counts))
    (p : H → FiniteLaw Shape) (u v w : H → Fin 17 → ℝ) (c : H → ℝ)
    (hsupport : ∀ h (a : Shape), a.1.val + a.2.1.val + a.2.2.val = sum h → 0 < (p h).mass a)
    (hlog : ∀ h a, 0 < (p h).mass a → Real.log ((p h).mass a) =
      u h (shapeSide 0 a) + v h (shapeSide 1 a) + w h (shapeSide 2 a) - c h) :
    ((sharedAmbient counts sum s e).card : ℝ) ≤
      ∏ h, classBound counts s e h (gibbsCap counts h (p h) (u h) (v h) (w h)) :=
  sharedAmbient_card_le counts sum s e _
    (fun h word hw => localAllowed_entropy_le counts sum h word (p h)
      (u h) (v h) (w h) (c h) (hsupport h) (hlog h) hw)

theorem neighbors_card_le_of_gibbs (counts : H → Shape → ℕ) (sum : H → ℕ)
    (e : JointCoarseHashing.Triple (Position counts))
    (p : H → FiniteLaw Shape) (u v w : H → Fin 17 → ℝ) (c : H → ℝ)
    (hsupport : ∀ h (a : Shape), a.1.val + a.2.1.val + a.2.2.val = sum h → 0 < (p h).mass a)
    (hlog : ∀ h a, 0 < (p h).mass a → Real.log ((p h).mass a) =
      u h (shapeSide 0 a) + v h (shapeSide 1 a) + w h (shapeSide 2 a) - c h) :
    ((neighbors counts sum e).card : ℝ) ≤
      ∑ s : Fin 3, ∏ h, classBound counts s e h
        (gibbsCap counts h (p h) (u h) (v h) (w h)) :=
  neighbors_card_le counts sum e _
    (fun h word hw => localAllowed_entropy_le counts sum h word (p h)
      (u h) (v h) (w h) (c h) (hsupport h) (hlog h) hw)

end

def classScale (counts : H → Shape → ℕ) (h : H) (N : ℕ) : ℝ :=
  (Fintype.card (Positions counts h) : ℝ) / N

theorem classScale_nonneg (counts : H → Shape → ℕ) (h : H) (N : ℕ) :
    0 ≤ classScale counts h N := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem classScale_mul_canonicalLaw_mass (counts : H → Shape → ℕ) (h : H)
    (N : ℕ) (a : Shape) :
    classScale counts h N * (canonicalLaw counts h).mass a = (counts h a : ℝ) / N := by
  unfold classScale
  calc
    _ = ((Fintype.card (Positions counts h) : ℝ) * (canonicalLaw counts h).mass a) / N := by ring
    _ = _ := by rw [total_mul_canonicalLaw_mass]

theorem classScale_mul_canonicalLaw_map_mass {B : Type*} [Fintype B] [DecidableEq B]
    (counts : H → Shape → ℕ) (h : H) (N : ℕ) (f : Shape → B) (b : B) :
    classScale counts h N * ((canonicalLaw counts h).map f).mass b =
      ∑ a, if f a = b then (counts h a : ℝ) / N else 0 := by
  rw [FiniteLaw.map_mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : f a = b
  · simp only [ha, ite_true]
    exact classScale_mul_canonicalLaw_mass counts h N a
  · simp only [ha, ite_false, mul_zero]

theorem classScale_mul_marginalError {B : Type*} [Fintype B] [DecidableEq B]
    (counts : H → Shape → ℕ) (h : H) (N : ℕ) (p : FiniteLaw Shape)
    (f : Shape → B) (v : B → ℝ) :
    classScale counts h N * marginalError p (canonicalLaw counts h) f v =
      ∑ b, |(∑ a, if f a = b then (counts h a : ℝ) / N else 0) -
        classScale counts h N * (p.map f).mass b| * |v b| := by
  unfold marginalError
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have habs : classScale counts h N *
      |((canonicalLaw counts h).map f).mass b - (p.map f).mass b| =
      |classScale counts h N * ((canonicalLaw counts h).map f).mass b -
        classScale counts h N * (p.map f).mass b| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (classScale_nonneg counts h N)]
  rw [← mul_assoc, habs, classScale_mul_canonicalLaw_map_mass]

theorem tendsto_classScale (counts : ℕ → H → Shape → ℕ) (h : H)
    (p : FiniteLaw Shape) (mass : ℝ)
    (hcounts : ∀ a, Tendsto (fun N => (counts N h a : ℝ) / N) atTop (𝓝 (mass * p.mass a))) :
    Tendsto (fun N => classScale (counts N) h N) atTop (𝓝 mass) := by
  have hsum := tendsto_finsetSum Finset.univ (fun a _ => hcounts a)
  simpa only [classScale, Positions, Fintype.card_fin, Nat.cast_sum,
    Finset.sum_div, ← Finset.mul_sum, p.total, mul_one] using hsum

theorem tendsto_classScale_mul_marginalError {B : Type*} [Fintype B] [DecidableEq B]
    (counts : ℕ → H → Shape → ℕ) (h : H) (p : FiniteLaw Shape)
    (mass : ℝ) (f : Shape → B) (v : B → ℝ)
    (hcounts : ∀ a, Tendsto (fun N => (counts N h a : ℝ) / N) atTop (𝓝 (mass * p.mass a))) :
    Tendsto (fun N => classScale (counts N) h N *
      marginalError p (canonicalLaw (counts N) h) f v) atTop (𝓝 0) := by
  have htotal := tendsto_classScale counts h p mass hcounts
  have hside (b : B) :
      Tendsto (fun N => ∑ a, if f a = b then (counts N h a : ℝ) / N else 0)
        atTop (𝓝 (mass * (p.map f).mass b)) := by
    have hterm (a : Shape) :
        Tendsto (fun N => if f a = b then (counts N h a : ℝ) / N else 0)
          atTop (𝓝 (if f a = b then mass * p.mass a else 0)) := by
      by_cases ha : f a = b
      · simpa only [ha, ite_true] using hcounts a
      · simp only [ha, ite_false]
        exact tendsto_const_nhds
    simpa only [FiniteLaw.map_mass, Finset.mul_sum, mul_ite, mul_zero] using
      tendsto_finsetSum Finset.univ (fun a _ => hterm a)
  have hterm (b : B) :
      Tendsto (fun N => |(∑ a, if f a = b then (counts N h a : ℝ) / N else 0) -
        classScale (counts N) h N * (p.map f).mass b| * |v b|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, zero_mul] using
      ((hside b).sub (htotal.mul_const ((p.map f).mass b))).abs.mul_const |v b|
  simpa only [classScale_mul_marginalError, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun b _ => hterm b)

theorem tendsto_classScale_mul_gibbsCap (counts : ℕ → H → Shape → ℕ) (h : H)
    (p : FiniteLaw Shape) (mass : ℝ) (u v w : Fin 17 → ℝ)
    (hcounts : ∀ a, Tendsto (fun N => (counts N h a : ℝ) / N) atTop (𝓝 (mass * p.mass a))) :
    Tendsto (fun N => classScale (counts N) h N *
      gibbsCap (counts N) h p u v w) atTop (𝓝 (mass * finiteEntropy p.mass)) := by
  have hm := (tendsto_classScale counts h p mass hcounts).mul_const (finiteEntropy p.mass)
  have hx := tendsto_classScale_mul_marginalError counts h p mass (shapeSide 0) u hcounts
  have hy := tendsto_classScale_mul_marginalError counts h p mass (shapeSide 1) v hcounts
  have hz := tendsto_classScale_mul_marginalError counts h p mass (shapeSide 2) w hcounts
  simpa only [gibbsCap, mul_add, add_zero] using ((hm.add hx).add hy).add hz

end MatrixMultiplication.JointAmbientEntropy

end

end MatrixAllFields

end OAI
