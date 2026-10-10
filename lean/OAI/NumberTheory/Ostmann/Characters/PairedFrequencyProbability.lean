import OAI.NumberTheory.Ostmann.Characters.PairedSquareProbability
import OAI.NumberTheory.Ostmann.Characters.ReducedSquare

namespace OAI

noncomputable section
namespace Ostmann.Characters
open Arithmetic.FrequencyMultiplicity

theorem paired_raw_split_probability_le_rpow (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Q n n' : ℕ, ∀ [NeZero Q],
      ∀ hn : n∣Q, ∀ hn' : n'∣Q, ∀ v w v' w' : ℤ,
      ∀ A B : (ZMod n)ˣ, ∀ A' B' : (ZMod n')ˣ, ∀ P : (ZMod Q)ˣ,
      (Nat.card {M : (ZMod Q)ˣ //
        rawSplitConstraint n v w A B (ZMod.unitsMap hn P) (ZMod.unitsMap hn M) ∧
        rawSplitConstraint n' v' w' A' B' (ZMod.unitsMap hn' P) (ZMod.unitsMap hn' M)}:ℝ) /
        Nat.card (ZMod Q)ˣ ≤
      C*((reducedModulus v w (n:ℤ)).lcm (reducedModulus v' w' (n':ℤ)):ℝ)^(ε-1) := by
  classical
  obtain ⟨C,hC,hbound⟩ := paired_square_probability_le_rpow ε hε
  refine ⟨C,hC,fun Q n n' _ hn hn' v w v' w' A B A' B' P => ?_⟩
  have hn0 : NeZero n := ⟨fun hz => NeZero.ne Q (by rw [hz] at hn; exact Nat.zero_dvd.mp hn)⟩
  have hn'0 : NeZero n' := ⟨fun hz => NeZero.ne Q (by rw [hz] at hn'; exact Nat.zero_dvd.mp hn')⟩
  let R : (ZMod Q)ˣ → Prop := fun M =>
    rawSplitConstraint n v w A B (ZMod.unitsMap hn P) (ZMod.unitsMap hn M) ∧
    rawSplitConstraint n' v' w' A' B' (ZMod.unitsMap hn' P) (ZMod.unitsMap hn' M)
  by_cases hex : ∃ M,R M
  · obtain ⟨M₀,h₀⟩ := hex
    obtain ⟨a,ha⟩ := exists_reduced_square_target n v w A B (ZMod.unitsMap hn P)
      ⟨ZMod.unitsMap hn M₀,h₀.1⟩
    obtain ⟨a',ha'⟩ := exists_reduced_square_target n' v' w' A' B' (ZMod.unitsMap hn' P)
      ⟨ZMod.unitsMap hn' M₀,h₀.2⟩
    let d := n/(v.natAbs.gcd n)
    let d' := n'/(v'.natAbs.gcd n')
    have hdn : d∣n := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
    have hd'n' : d'∣n' := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
    have hdQ : d∣Q := dvd_trans hdn hn
    have hd'Q : d'∣Q := dvd_trans hd'n' hn'
    let S : (ZMod Q)ˣ → Prop := fun M =>
      (ZMod.unitsMap hdQ M)^2=a ∧ (ZMod.unitsMap hd'Q M)^2=a'
    have himp : ∀ M,R M→S M := by
      intro M hM
      constructor
      · simpa only [unitsMap_trans] using ha (ZMod.unitsMap hn M) hM.1
      · simpa only [unitsMap_trans] using ha' (ZMod.unitsMap hn' M) hM.2
    have hcard : Nat.card {M : (ZMod Q)ˣ // R M} ≤ Nat.card {M : (ZMod Q)ˣ // S M} := by
      apply Nat.card_le_card_of_injective (fun M => (⟨M.val,himp M.val M.property⟩ : {M // S M}))
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : {M : (ZMod Q)ˣ // S M} => z.val) hxy
    have hg : v.natAbs.gcd n=w.natAbs.gcd n :=
      gcd_eq_of_unit_congruence n v w
        (B*((ZMod.unitsMap hn P)/(ZMod.unitsMap hn M₀))) (A*ZMod.unitsMap hn M₀)
        (by simpa only [rawSplitConstraint, Units.val_mul, mul_assoc] using h₀.1)
    have hg' : v'.natAbs.gcd n'=w'.natAbs.gcd n' :=
      gcd_eq_of_unit_congruence n' v' w'
        (B'*((ZMod.unitsMap hn' P)/(ZMod.unitsMap hn' M₀))) (A'*ZMod.unitsMap hn' M₀)
        (by simpa only [rawSplitConstraint, Units.val_mul, mul_assoc] using h₀.2)
    have hd : reducedModulus v w (n:ℤ)=d := by
      simp only [reducedModulus, Int.natAbs_natCast, triple_gcd_eq v w n hg, d]
    have hd' : reducedModulus v' w' (n':ℤ)=d' := by
      simp only [reducedModulus, Int.natAbs_natCast, triple_gcd_eq v' w' n' hg', d']
    rw [hd,hd']
    calc
      _ ≤ (Nat.card {M : (ZMod Q)ˣ // S M}:ℝ)/Nat.card (ZMod Q)ˣ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
      _ ≤ C*(d.lcm d':ℝ)^(ε-1) := hbound Q d d' hdQ hd'Q a a'
  · have he : IsEmpty {M : (ZMod Q)ˣ // R M} := ⟨fun M => hex ⟨M.val,M.property⟩⟩
    change (Nat.card {M : (ZMod Q)ˣ // R M}:ℝ)/_≤_
    have hz : Nat.card {M : (ZMod Q)ˣ // R M}=0 := by simp
    rw [hz, Nat.cast_zero, zero_div]
    positivity

theorem paired_frequency_split_probability_le_rpow (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Q : ℕ, ∀ [NeZero Q], ∀ s s' v w v' w' : ℤ,
      ∀ hs : s.natAbs∣Q, ∀ hs' : s'.natAbs∣Q,
      ∀ A B : (ZMod s.natAbs)ˣ, ∀ A' B' : (ZMod s'.natAbs)ˣ, ∀ P : (ZMod Q)ˣ,
      (Nat.card {M : (ZMod Q)ˣ //
        rawSplitConstraint s.natAbs v w A B (ZMod.unitsMap hs P) (ZMod.unitsMap hs M) ∧
        rawSplitConstraint s'.natAbs v' w' A' B' (ZMod.unitsMap hs' P) (ZMod.unitsMap hs' M)}:ℝ) /
        Nat.card (ZMod Q)ˣ ≤
      C*((reducedModulus v w s).lcm (reducedModulus v' w' s'):ℝ)^(ε-1) := by
  obtain ⟨C,hC,hbound⟩ := paired_raw_split_probability_le_rpow ε hε
  refine ⟨C,hC,fun Q _ s s' v w v' w' hs hs' A B A' B' P => ?_⟩
  simpa only [reducedModulus, Int.natAbs_natCast] using
    hbound Q s.natAbs s'.natAbs hs hs' v w v' w' A B A' B' P

theorem frequency_split_probability_le_rpow (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Q : ℕ, ∀ [NeZero Q], ∀ s v w : ℤ,
      ∀ hs : s.natAbs∣Q, ∀ A B : (ZMod s.natAbs)ˣ, ∀ P : (ZMod Q)ˣ,
      (Nat.card {M : (ZMod Q)ˣ //
        rawSplitConstraint s.natAbs v w A B (ZMod.unitsMap hs P) (ZMod.unitsMap hs M)}:ℝ) /
        Nat.card (ZMod Q)ˣ ≤ C*(reducedModulus v w s:ℝ)^(ε-1) := by
  obtain ⟨C,hC,hbound⟩ := paired_frequency_split_probability_le_rpow ε hε
  refine ⟨C,hC,fun Q _ s v w hs A B P => ?_⟩
  simpa only [and_self, Nat.lcm_self] using hbound Q s s v w v w hs hs A B A B P

end Ostmann.Characters

end

end OAI
