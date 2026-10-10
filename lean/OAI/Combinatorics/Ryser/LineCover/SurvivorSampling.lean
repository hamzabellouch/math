import OAI.Combinatorics.Ryser.LineCover.SamplingDefinitions
import OAI.Combinatorics.Ryser.LineCover.PairCounting
import OAI.Combinatorics.Ryser.LineCover.PairSampling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F]

theorem card_cross_survivors_le_hitCount (X : Finset (Point F))
    {t : ℕ} (a : LineTuple F t) :
    (X ∩ crossPoints a).card ≤ crossHitCount X a := by
  classical
  let S := X ∩ crossPoints a
  have hex (x : ↥S) : ∃ p : Fin t × Fin t,
      Incidence x.val (a (Sum.inl p.1)) ∧ Incidence x.val (a (Sum.inr p.2)) := by
    obtain ⟨i, j, hi, hj⟩ :=
      (mem_crossPoints a x.val).mp (Finset.mem_inter.mp x.property).2
    exact ⟨(i, j), hi, hj⟩
  let rep (x : ↥S) : Fin t × Fin t := Classical.choose (hex x)
  have hrep (x : ↥S) :
      Incidence x.val (a (Sum.inl (rep x).1)) ∧
        Incidence x.val (a (Sum.inr (rep x).2)) := Classical.choose_spec (hex x)
  let encode : ↥S → {p : Fin t × Fin t // CrossHit X a p} := fun x =>
    ⟨rep x, x.val, (Finset.mem_inter.mp x.property).1, (hrep x).1, (hrep x).2⟩
  have hinj : Function.Injective encode := by
    intro x y hxy
    have hp : rep x = rep y := congrArg Subtype.val hxy
    apply Subtype.ext
    exact eq_of_common_incidence_of_ne_lines (left_ne_right a (rep x).1 (rep x).2)
      (hrep x).1 (hrep x).2
      (by simpa only [hp] using (hrep y).1)
      (by simpa only [hp] using (hrep y).2)
  calc
    (X ∩ crossPoints a).card = Fintype.card ↥S := (Fintype.card_coe S).symm
    _ ≤ Fintype.card {p : Fin t × Fin t // CrossHit X a p} :=
      Fintype.card_le_of_injective encode hinj
    _ = crossHitCount X a := by
      rw [Fintype.card_subtype]
      unfold crossHitCount
      apply congrArg Finset.card
      ext p
      simp only [Finset.mem_filter]

theorem crossHitCount_eq_sum (X : Finset (Point F)) {t : ℕ}
    (a : LineTuple F t) :
    (crossHitCount X a : ℝ) =
      ∑ p : Fin t × Fin t, if CrossHit X a p then (1 : ℝ) else 0 := let _ := instFintypeF; let _ := instDecidableEqF; by
  exact Finset.natCast_card_filter (CrossHit X a) Finset.univ

theorem prob_crossHit_le (X : Finset (Point F)) (L : Finset (AffineLine F))
    {t : ℕ} [Nonempty (CoverSample L t)] (p : Fin t × Fin t) :
    (FiniteLaw.uniform (CoverSample L t)).prob
        (fun u => CrossHit X (liftSample L u) p) ≤
      (orderedPairMass Incidence X L : ℝ) / (L.card.descFactorial 2 : ℝ) := let _ := instFintypeF; let _ := instDecidableEqF; by
  classical
  let left : Fin 1 ↪ Fin t := ⟨fun _ => p.1, fun _ _ _ => Subsingleton.elim _ _⟩
  let right : Fin 1 ↪ Fin t := ⟨fun _ => p.2, fun _ _ _ => Subsingleton.elim _ _⟩
  have h := InjectionSampling.prob_disjoint_pairs_le
    (Function.Embedding.sumMap left right) (populationSurvivorPairs X L)
  have hevent :
      (fun u : CoverSample L t => ∀ k : Fin 1,
        (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ populationSurvivorPairs X L) =
        (fun u => CrossHit X (liftSample L u) p) := by
    funext u
    apply propext
    have hne : u (Sum.inl p.1) ≠ u (Sum.inr p.2) := by
      intro heq
      exact Sum.inl_ne_inr (u.injective heq)
    change (∀ _k : Fin 1,
      (u (Sum.inl p.1), u (Sum.inr p.2)) ∈ populationSurvivorPairs X L) ↔ _
    constructor
    · intro hu
      exact ((mem_populationSurvivorPairs X L _).mp (hu 0)).2
    · intro hu _k
      exact (mem_populationSurvivorPairs X L _).mpr ⟨hne, hu⟩
  change (FiniteLaw.uniform (CoverSample L t)).prob
      (fun u => ∀ k : Fin 1,
        (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ populationSurvivorPairs X L) ≤ _ at h
  rw [hevent] at h
  simpa only [pow_one, Nat.mul_one, Fintype.card_coe,
    card_populationSurvivorPairs_eq_orderedPairMass] using h

theorem expectation_crossHitCount_le
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    {t : ℕ} [Nonempty (CoverSample L t)] :
    (FiniteLaw.uniform (CoverSample L t)).expectation
        (fun u => (crossHitCount X (liftSample L u) : ℝ)) ≤
      (t : ℝ) ^ 2 * (orderedPairMass Incidence X L : ℝ) /
        (L.card.descFactorial 2 : ℝ) := by
  let μ := FiniteLaw.uniform (CoverSample L t)
  calc
    _ = μ.expectation (fun u => ∑ p : Fin t × Fin t,
        if CrossHit X (liftSample L u) p then (1 : ℝ) else 0) := by
      congr 1
      funext u
      exact crossHitCount_eq_sum X (liftSample L u)
    _ = ∑ p : Fin t × Fin t, μ.expectation
        (fun u => if CrossHit X (liftSample L u) p then (1 : ℝ) else 0) :=
      μ.expectation_sum _
    _ = ∑ p : Fin t × Fin t, μ.prob (fun u => CrossHit X (liftSample L u) p) := by
      apply Finset.sum_congr rfl
      intro p _
      exact (μ.prob_eq_expectation _).symm
    _ ≤ ∑ _p : Fin t × Fin t,
        (orderedPairMass Incidence X L : ℝ) / (L.card.descFactorial 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _
      exact prob_crossHit_le X L p
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      ring

theorem prob_many_cross_survivors_le
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    {t : ℕ} [Nonempty (CoverSample L t)] {δ : ℝ} (hδ : 0 < δ) (ht : 0 < t) :
    (FiniteLaw.uniform (CoverSample L t)).prob
        (fun u => δ * (t : ℝ) ^ 2 / 2 ≤
          ((X ∩ crossPoints (liftSample L u)).card : ℝ)) ≤
      2 * (orderedPairMass Incidence X L : ℝ) /
        (δ * (L.card.descFactorial 2 : ℝ)) := by
  let μ := FiniteLaw.uniform (CoverSample L t)
  have htR : 0 < (t : ℝ) := Nat.cast_pos.mpr ht
  have hthreshold : 0 < δ * (t : ℝ) ^ 2 / 2 := by positivity
  calc
    _ ≤ μ.prob (fun u => δ * (t : ℝ) ^ 2 / 2 ≤
        (crossHitCount X (liftSample L u) : ℝ)) := by
      apply μ.prob_mono
      intro u hu
      exact hu.trans (Nat.cast_le.mpr (card_cross_survivors_le_hitCount X _))
    _ ≤ μ.expectation (fun u => (crossHitCount X (liftSample L u) : ℝ)) /
        (δ * (t : ℝ) ^ 2 / 2) :=
      μ.prob_ge_le_expectation_div _ (fun _ => Nat.cast_nonneg _) hthreshold
    _ ≤ ((t : ℝ) ^ 2 * (orderedPairMass Incidence X L : ℝ) /
        (L.card.descFactorial 2 : ℝ)) / (δ * (t : ℝ) ^ 2 / 2) :=
      div_le_div_of_nonneg_right (expectation_crossHitCount_le X L) hthreshold.le
    _ = _ := by
      by_cases hden : (L.card.descFactorial 2 : ℝ) = 0
      · simp only [hden, div_zero, mul_zero, zero_div]
      · field_simp [hδ.ne', htR.ne', hden]

end RyserCoveringCounterexample.LineCover

end

end OAI
