import OAI.NumberTheory.EgyptianFractions.UniformSecondMoment
import OAI.NumberTheory.EgyptianFractions.RandomExposure
import OAI.NumberTheory.EgyptianFractions.ExposedCorrelation
import OAI.NumberTheory.EgyptianFractions.RandomProductParameters
import OAI.NumberTheory.EgyptianFractions.RandomCorrelation
import OAI.NumberTheory.EgyptianFractions.RandomGcdMarginal
import OAI.NumberTheory.EgyptianFractions.FiniteGoodExposure

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.RandomProducts

def sampledProduct {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (I : Fin m → Bool) : ℕ :=
  ∏ j, (p (j, I j) : ℕ)

def sampledPhase {m : ℕ} {P : Finset ℕ} (u l : ℕ) [NeZero u]
    (p : (Fin m × Bool) → P) (I : Fin m → Bool) : ℂ :=
  ZMod.stdAddChar ((l * sampledProduct p I : ℕ) : ZMod u)

@[simp] theorem norm_sampledPhase {m : ℕ} {P : Finset ℕ} (u l : ℕ) [NeZero u]
    (p : (Fin m × Bool) → P) (I : Fin m → Bool) : ‖sampledPhase u l p I‖ = 1 := by
  exact AddChar.norm_apply _ _

theorem sampledPhase_correlation {m : ℕ} {P : Finset ℕ} (u l : ℕ) [NeZero u]
    (p : (Fin m × Bool) → P) (I J : Fin m → Bool) :
    sampledPhase u l p I * star (sampledPhase u l p J) =
      ZMod.stdAddChar (((l * sampledProduct p I : ℕ) : ZMod u) -
        ((l * sampledProduct p J : ℕ) : ZMod u)) := by
  unfold sampledPhase
  rw [Complex.star_def, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  simp only [sub_eq_add_neg]

open RandomExposure

theorem sampledProduct_split_first {m : ℕ} {P : Finset ℕ}
    (I : Fin m → Bool) (A B : Finset (Fin m)) (hAB : Disjoint A B)
    (a : selectedLabels I A → P) (b : selectedLabels I B → P)
    (c : ExposedLabel I A B → P) :
    sampledProduct ((splitSampleExposedFirst (selectedLabels I A) (selectedLabels I B)
      (selectedLabels_disjoint I hAB)).symm (c, (a,b))) I =
      exposedFirstProduct (fun p : P => (p : ℕ)) I A B c *
        (∏ z, (a z : ℕ)) * (∏ z, (b z : ℕ)) := by
  unfold sampledProduct
  rw [splitSampleExposedFirst_symm]
  rw [selected_product_factorization I A B hAB
    (fun z => (((splitSample (selectedLabels I A) (selectedLabels I B)
      (selectedLabels_disjoint I hAB)).symm (a,b,c)) z : ℕ))]
  rw [exposed_first_factor_formula (fun p : P => (p : ℕ)) I A B hAB a b c]
  congr 1
  · congr 1
    rw [product_selectedLabels I A (fun z => (((splitSample (selectedLabels I A)
      (selectedLabels I B) (selectedLabels_disjoint I hAB)).symm (a,b,c)) z : ℕ))]
    apply Finset.prod_congr rfl
    intro z hz
    simp
  · rw [product_selectedLabels I B (fun z => (((splitSample (selectedLabels I A)
      (selectedLabels I B) (selectedLabels_disjoint I hAB)).symm (a,b,c)) z : ℕ))]
    apply Finset.prod_congr rfl
    intro z hz
    simp

theorem sampledProduct_split_other {m : ℕ} {P : Finset ℕ}
    (I J : Fin m → Bool) (A B : Finset (Fin m)) (hAB : Disjoint A B)
    (hA : ∀ i ∈ A, I i ≠ J i) (hB : ∀ i ∈ B, I i ≠ J i)
    (a : selectedLabels I A → P) (b : selectedLabels I B → P)
    (c : ExposedLabel I A B → P) :
    sampledProduct ((splitSampleExposedFirst (selectedLabels I A) (selectedLabels I B)
      (selectedLabels_disjoint I hAB)).symm (c, (a,b))) J =
      exposedOtherProduct (fun p : P => (p : ℕ)) I J A B hA hB c := by
  unfold sampledProduct
  rw [splitSampleExposedFirst_symm]
  exact exposed_other_factor_formula _ I J A B hAB hA hB a b c

/-- The exact sample-splitting interface for one pair of Boolean words. -/
theorem sampled_pair_bound_of_good_bad {m : ℕ} {P : Finset ℕ}
    (hne : P.Nonempty) (I J : Fin m → Bool) (A B : Finset (Fin m))
    (hAB : Disjoint A B) (hA : ∀ i ∈ A, I i ≠ J i) (hB : ∀ i ∈ B, I i ≠ J i)
    (u l : ℕ) [NeZero u] (bad : Finset (ExposedLabel I A B → P))
    (ε δ : ℝ) (hδ : 0 ≤ δ)
    (hbad : (bad.card : ℝ) / Fintype.card (ExposedLabel I A B → P) ≤ ε)
    (hgood : ∀ c, c ∉ bad →
      ‖𝔼 a : selectedLabels I A → P, 𝔼 b : selectedLabels I B → P,
        ZMod.stdAddChar
          (((l * exposedFirstProduct (fun p : P => (p : ℕ)) I A B c *
            (∏ z, (a z : ℕ)) * (∏ z, (b z : ℕ)) : ℕ) : ZMod u) -
            ((l * exposedOtherProduct (fun p : P => (p : ℕ)) I J A B hA hB c : ℕ) : ZMod u))‖ ≤ δ) :
    ‖𝔼 p : (Fin m × Bool) → P,
      ZMod.stdAddChar (((l * sampledProduct p I : ℕ) : ZMod u) -
        ((l * sampledProduct p J : ℕ) : ZMod u))‖ ≤ ε + δ := by
  let : Nonempty P := hne.to_subtype
  apply correlation_of_exposed_products
    (splitSampleExposedFirst (selectedLabels I A) (selectedLabels I B)
      (selectedLabels_disjoint I hAB))
    (fun p => sampledProduct p I) (fun p => sampledProduct p J)
    (exposedFirstProduct (fun p : P => (p : ℕ)) I A B)
    (exposedOtherProduct (fun p : P => (p : ℕ)) I J A B hA hB)
    (fun a => ∏ z, (a z : ℕ)) (fun b => ∏ z, (b z : ℕ))
    (fun c a b => sampledProduct_split_first I A B hAB a b c)
    (fun c a b => sampledProduct_split_other I J A B hAB hA hB a b c)
    u l bad ε δ hδ hbad hgood

/-- The actual labelled-prime-product random quantity, reduced to separated-pair
correlations. The remaining hypothesis is precisely the output of exposure. -/
theorem sampled_product_second_moment_of_correlations {P : Finset ℕ}
    (hne : P.Nonempty) (m u l : ℕ) [NeZero u] (V : ℝ)
    (hlarge : 50 ≤ min (m : ℝ) V)
    (hpair : ∀ I J : Fin m → Bool,
      (m : ℝ) / 4 ≤ (hammingDist I J : ℝ) →
      ‖𝔼 p : (Fin m × Bool) → P,
        ZMod.stdAddChar (((l * sampledProduct p I : ℕ) : ZMod u) -
          ((l * sampledProduct p J : ℕ) : ZMod u))‖ ≤
        Real.exp (-V / 20) + Real.exp (-V / 5)) :
    (𝔼 p : (Fin m × Bool) → P, ‖𝔼 I : Fin m → Bool, sampledPhase u l p I‖ ^ 2) ≤
      Real.exp (-min (m : ℝ) V / 100) := by
  let : Nonempty P := hne.to_subtype
  apply uniform_boolean_random_second_moment_bound m V (sampledPhase u l)
    (fun p I => (norm_sampledPhase u l p I).le) hlarge
  intro I J hIJ
  simpa only [sampledPhase_correlation] using hpair I J hIJ

/-- The actual Hamming condition supplies the two fresh blocks used by exposure. -/
theorem sampled_pair_fresh_blocks {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S)
    (I J : Fin (blockLength S) → Bool)
    (hIJ : (blockLength S : ℝ) / 4 ≤ (hammingDist I J : ℝ)) :
    ∃ A B : Finset (Fin (blockLength S)), Disjoint A B ∧
      A.card = freshLength S V ∧ B.card = freshLength S V ∧
      (∀ i ∈ A, I i ≠ J i) ∧ (∀ i ∈ B, I i ≠ J i) := by
  apply exists_differing_blocks
  apply fresh_coordinates_fit hS hV hVS
  have hreal : (blockLength S : ℝ) ≤ 4 * (hammingDist I J : ℝ) := by linarith
  exact_mod_cast hreal

/-- The exposed factor uses at most the full first word's number of coordinates. -/
theorem exposed_coordinate_card_le {S : ℝ} (hS : Real.exp 1 ≤ S)
    (A B : Finset (Fin (blockLength S))) :
    (Fintype.card ↥(Finset.univ \ (A ∪ B)) : ℝ) ≤ S := by
  have hcard : (Finset.univ \ (A ∪ B)).card ≤ blockLength S := by
    simpa using Finset.card_le_card (Finset.sdiff_subset :
      (Finset.univ \ (A ∪ B)) ⊆ Finset.univ)
  have hreal : ((Finset.univ \ (A ∪ B)).card : ℝ) ≤ blockLength S := by
    exact_mod_cast hcard
  simpa only [Fintype.card_coe] using hreal.trans (blockLength_le_self hS)

/-- The parameter range guarantees the fixed numeric threshold for error absorption. -/
theorem random_min_large {S V : ℝ} (hS : 2 ≤ S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S) :
    50 ≤ min (blockLength S : ℝ) V := by
  apply le_min
  · have h := blockLength_large (by linarith : 1 < S) hV hVS
    have : (100000 : ℝ) ≤ blockLength S := by exact_mod_cast h
    linarith
  · have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at htwo
    have hlog := htwo.trans (Real.log_le_log (by norm_num) hS)
    nlinarith

/-- The actual exposed first-word factor has an exponentially small bad-gcd event.
Unused exposed labels are eliminated by the exact uniform-coordinate marginal law. -/
theorem exposed_bad_gcd_fraction (S V : ℝ) (hS : 3 ≤ S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hinterval : ∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101)
    (hsize : S ^ 99 ≤ (P.card : ℝ)) (u l : ℕ)
    (huexp : (u : ℝ) = Real.exp V) (hl : 0 < l)
    (hlbound : (l : ℝ) ≤ Real.exp (V / 200))
    (I : Fin (blockLength S) → Bool) (A B : Finset (Fin (blockLength S))) :
    ((Finset.univ.filter (fun c : ExposedLabel I A B → P =>
      ((u / Nat.gcd (l * exposedFirstProduct (fun p : P => (p : ℕ)) I A B c) u : ℕ) : ℝ)
        < Real.exp (9 * V / 10))).card : ℝ) /
      Fintype.card (ExposedLabel I A B → P) ≤ Real.exp (-V / 20) := by
  classical
  let : Nonempty P := hP.to_subtype
  let e : ↥(Finset.univ \ (A ∪ B)) ↪ ExposedLabel I A B :=
    ⟨outsideSelectedLabel I A B, outsideSelectedLabel_injective I A B⟩
  let R : (↥(Finset.univ \ (A ∪ B)) → P) → Prop := fun a =>
    ((u / Nat.gcd (l * ∏ i, (a i : ℕ)) u : ℕ) : ℝ) < Real.exp (9 * V / 10)
  change ((Finset.univ.filter (fun c : ExposedLabel I A B → P =>
    R (fun k => c (e k)))).card : ℝ) / _ ≤ _
  rw [injective_coordinate_event_fraction e R]
  have hV0 : 0 ≤ V := by
    have := Real.log_pos (show 1 < S by linarith)
    nlinarith
  have hSexp : Real.exp 1 ≤ S := Real.exp_one_lt_three.le.trans hS
  have h := random_gcd_typed_bound (ι := ↥(Finset.univ \ (A ∪ B)))
    P u l S V hP (by linarith) hV0 hVS huexp hprime hinterval
    (exposed_coordinate_card_le hSexp A B) hsize hl hlbound
  simpa only [Fintype.card_subtype, R] using h

/-- The complete random-product second-moment estimate for labelled independent
prime samples, including Hamming exceptions, bad gcds, and bilinear cancellation. -/
theorem sampled_product_second_moment_bound
    (S V : ℝ) (hS : 3 ≤ S) (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hinterval : ∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101)
    (hsize : S ^ 99 ≤ (P.card : ℝ)) (u l : ℕ) [NeZero u]
    (huexp : (u : ℝ) = Real.exp V) (hl : 0 < l)
    (hlbound : (l : ℝ) ≤ Real.exp (V / 200)) :
    (𝔼 p : (Fin (blockLength S) × Bool) → P,
      ‖𝔼 I : Fin (blockLength S) → Bool, sampledPhase u l p I‖ ^ 2) ≤
        Real.exp (-min (blockLength S : ℝ) V / 100) := by
  classical
  have hS2 : 2 ≤ S := by linarith
  have hSpos : 0 < S := by linarith
  have hcardpos : 0 < (P.card : ℝ) := lt_of_lt_of_le (by positivity) hsize
  have hP : P.Nonempty := Finset.card_pos.mp (by exact_mod_cast hcardpos)
  have hu : 0 < u := Nat.pos_of_ne_zero (NeZero.ne u)
  apply sampled_product_second_moment_of_correlations hP _ u l V
    (random_min_large hS2 hV hVS)
  intro I J hIJ
  obtain ⟨A, B, hAB, hAs, hBs, hA, hB⟩ :=
    sampled_pair_fresh_blocks (by linarith : 1 < S) hV hVS I J hIJ
  let bad : Finset (ExposedLabel I A B → P) := Finset.univ.filter fun c =>
    ((u / Nat.gcd (l * exposedFirstProduct (fun p : P => (p : ℕ)) I A B c) u : ℕ) : ℝ)
      < Real.exp (9 * V / 10)
  apply sampled_pair_bound_of_good_bad hP I J A B hAB hA hB u l bad
    (Real.exp (-V / 20)) (Real.exp (-V / 5)) (Real.exp_pos _).le
  · exact exposed_bad_gcd_fraction S V hS hV hVS P hP hprime hinterval hsize
      u l huexp hl hlbound I A B
  · intro c hc
    have hq : Real.exp ((9 / 10 : ℝ) * V) ≤
        ((u / Nat.gcd (l * exposedFirstProduct (fun p : P => (p : ℕ)) I A B c) u : ℕ) : ℝ) := by
      have hn : ¬ ((u / Nat.gcd
          (l * exposedFirstProduct (fun p : P => (p : ℕ)) I A B c) u : ℕ) : ℝ) <
          Real.exp (9 * V / 10) := by simpa only [bad, Finset.mem_filter,
            Finset.mem_univ, true_and] using hc
      simpa only [show (9 / 10 : ℝ) * V = 9 * V / 10 by ring] using le_of_not_gt hn
    have hAc : Fintype.card (selectedLabels I A) = freshLength S V := by
      simpa only [Fintype.card_coe, selectedLabels_card] using hAs
    have hBc : Fintype.card (selectedLabels I B) = freshLength S V := by
      simpa only [Fintype.card_coe, selectedLabels_card] using hBs
    exact concrete_good_exposure_expect S V hAc hBc hS2 hV hVS P hprime hsize
      (fun p hp => (hinterval p hp).2)
      (l * exposedFirstProduct (fun p : P => (p : ℕ)) I A B c) u hu
      huexp.le hq ((l * exposedOtherProduct (fun p : P => (p : ℕ)) I J A B hA hB c : ℕ) : ZMod u)

/-- Logarithmic form with `V = log u` and the smaller common frequency range. -/
theorem sampled_product_second_moment_log_bound
    (S : ℝ) (hS : 3 ≤ S) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hinterval : ∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101)
    (hsize : S ^ 99 ≤ (P.card : ℝ)) (u l : ℕ) [NeZero u]
    (hV : 100000 * Real.log S ≤ Real.log (u : ℝ))
    (hVS : Real.log (u : ℝ) ≤ S) (hl : 0 < l)
    (hlbound : (l : ℝ) ≤ Real.exp (min (blockLength S : ℝ) (Real.log (u : ℝ)) / 200)) :
    (𝔼 p : (Fin (blockLength S) × Bool) → P,
      ‖𝔼 I : Fin (blockLength S) → Bool, sampledPhase u l p I‖ ^ 2) ≤
        Real.exp (-min (blockLength S : ℝ) (Real.log (u : ℝ)) / 100) := by
  apply sampled_product_second_moment_bound S (Real.log (u : ℝ)) hS hV hVS
    P hprime hinterval hsize u l
  · exact (Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne u))).symm
  · exact hl
  · exact hlbound.trans (Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)))

end Problem337.RandomProducts

end

end OAI
