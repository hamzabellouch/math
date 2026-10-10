import Mathlib
import OAI.NumberTheory.Jacobsthal.Analysis.ImplicitDerivatives

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosLatticeChain

def vectorLength (v : ℕ × ℕ) : ℕ := v.1+v.2

def totalLength (V : Finset (ℕ × ℕ)) : ℕ := ∑ v ∈ V, vectorLength v

def shortVectors (V : Finset (ℕ × ℕ)) (T : ℕ) : Finset (ℕ × ℕ) :=
  V.filter fun v => vectorLength v ≤ T

def longVectors (V : Finset (ℕ × ℕ)) (T : ℕ) : Finset (ℕ × ℕ) :=
  V.filter fun v => T < vectorLength v

def shortSquareEmbedding (V : Finset (ℕ × ℕ)) (T : ℕ) :
    ↥(shortVectors V T) ↪ (Fin (T+1) × Fin (T+1)) where
  toFun v :=
    (⟨v.1.1, by
      have h := (Finset.mem_filter.mp v.2).2
      dsimp [vectorLength] at h
      omega⟩,
     ⟨v.1.2, by
      have h := (Finset.mem_filter.mp v.2).2
      dsimp [vectorLength] at h
      omega⟩)
  inj' := by
    intro u v h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun w : Fin (T+1) × Fin (T+1) => w.1.val) h
    · exact congrArg (fun w : Fin (T+1) × Fin (T+1) => w.2.val) h

theorem short_card_le_square (V : Finset (ℕ × ℕ)) (T : ℕ) :
    (shortVectors V T).card ≤ (T+1)^2 := by
  have h := Fintype.card_le_of_embedding (shortSquareEmbedding V T)
  simpa [pow_two] using h

theorem short_long_card (V : Finset (ℕ × ℕ)) (T : ℕ) :
    (shortVectors V T).card+(longVectors V T).card = V.card := by
  simpa only [shortVectors, longVectors, not_le] using
    Finset.card_filter_add_card_filter_not (s := V) (fun v => vectorLength v ≤ T)

theorem long_card_mul_le_length (V : Finset (ℕ × ℕ)) (T : ℕ) :
    (T+1)*(longVectors V T).card ≤ totalLength V := by
  calc
    _ = ∑ _v ∈ longVectors V T, (T+1) := by simp [mul_comm]
    _ ≤ ∑ v ∈ longVectors V T, vectorLength v := by
      apply Finset.sum_le_sum
      intro v hv
      exact (Finset.mem_filter.mp hv).2
    _ ≤ ∑ v ∈ V, vectorLength v := Finset.sum_le_sum_of_subset
      (Finset.filter_subset _ _)
    _ = _ := rfl

theorem card_le_square_add_div (V : Finset (ℕ × ℕ)) (T : ℕ) {L : ℝ}
    (hL : (totalLength V : ℝ) ≤ L) :
    (V.card : ℝ) ≤ ((T : ℝ)+1)^2+L/((T : ℝ)+1) := by
  have hden : (0 : ℝ) < (T : ℝ)+1 := by positivity
  have hs : ((shortVectors V T).card : ℝ) ≤ ((T : ℝ)+1)^2 := by
    exact_mod_cast short_card_le_square V T
  have hl : ((T : ℝ)+1)*((longVectors V T).card : ℝ) ≤ L := by
    have h : ((T : ℝ)+1)*((longVectors V T).card : ℝ) ≤ (totalLength V : ℝ) := by
      exact_mod_cast long_card_mul_le_length V T
    exact h.trans hL
  have hld : ((longVectors V T).card : ℝ) ≤ L/((T : ℝ)+1) :=
    (le_div_iff₀ hden).mpr (by nlinarith only [hl])
  have he : ((shortVectors V T).card : ℝ)+((longVectors V T).card : ℝ) = (V.card : ℝ) := by
    exact_mod_cast short_long_card V T
  linarith

end ErdosLatticeChain

end

section

open scoped BigOperators
namespace ErdosLatticeChain

theorem consecutive_sum {n : ℕ} (f : Fin (n+1) → ℤ) :
    (∑ i : Fin n, (f i.succ-f i.castSucc)) = f (Fin.last n)-f 0 := by
  have hfirst := Fin.sum_univ_succ f
  have hlast := Fin.sum_univ_castSucc f
  rw [Finset.sum_sub_distrib]
  linarith

def coordinateVariation {n : ℕ} (f : Fin (n+1) → ℤ) : ℕ :=
  ∑ i : Fin n, (f i.succ-f i.castSucc).natAbs

theorem variation_of_monotone {n : ℕ} (f : Fin (n+1) → ℤ) (hf : Monotone f) :
    (coordinateVariation f : ℝ) = (f (Fin.last n) : ℝ)-(f 0 : ℝ) := by
  have he : (coordinateVariation f : ℤ) = f (Fin.last n)-f 0 := by
    unfold coordinateVariation
    push_cast
    rw [← consecutive_sum f]
    apply Finset.sum_congr rfl
    intro i _
    exact abs_of_nonneg (sub_nonneg.mpr (hf (by exact_mod_cast Nat.le_succ i.val)))
  exact_mod_cast he

theorem variation_of_antitone {n : ℕ} (f : Fin (n+1) → ℤ) (hf : Antitone f) :
    (coordinateVariation f : ℝ) = (f 0 : ℝ)-(f (Fin.last n) : ℝ) := by
  have he : (coordinateVariation f : ℤ) = f 0-f (Fin.last n) := by
    unfold coordinateVariation
    push_cast
    have h := consecutive_sum f
    have hneg : (∑ i : Fin n, -(f i.succ-f i.castSucc)) = f 0-f (Fin.last n) := by
      rw [Finset.sum_neg_distrib, h]
      ring
    rw [← hneg]
    apply Finset.sum_congr rfl
    intro i _
    exact abs_of_nonpos (sub_nonpos.mpr (hf (by exact_mod_cast Nat.le_succ i.val)))
  exact_mod_cast he

theorem variation_le_box {n : ℕ} (f : Fin (n+1) → ℤ) (S : ℝ)
    (hf : Monotone f ∨ Antitone f) (hbox : ∀ i, 0 ≤ (f i : ℝ) ∧ (f i : ℝ) ≤ S) :
    (coordinateVariation f : ℝ) ≤ S := by
  rcases hf with hf | hf
  · rw [variation_of_monotone f hf]
    linarith [(hbox 0).1, (hbox (Fin.last n)).2]
  · rw [variation_of_antitone f hf]
    linarith [(hbox (Fin.last n)).1, (hbox 0).2]

end ErdosLatticeChain

end


namespace ErdosLatticeChain

theorem vector_card_bound (V : Finset (ℕ × ℕ)) {L : ℝ} (hL : 0 ≤ L)
    (hlength : (totalLength V : ℝ) ≤ L) :
    (V.card : ℝ) ≤ 5*(1+L^((2 : ℝ)/3)) := by
  by_cases hL1 : 1 ≤ L
  · have hLp : 0 < L := by linarith
    let r := L^((1 : ℝ)/3)
    let T := ⌊r⌋₊
    have hr : 1 ≤ r := Real.one_le_rpow hL1 (by norm_num)
    have hrp : 0 < r := by linarith
    have hT : (T : ℝ) ≤ r := Nat.floor_le hrp.le
    have hTr : r ≤ (T : ℝ)+1 := (Nat.lt_floor_add_one r).le
    have hT2 : (T : ℝ)+1 ≤ 2*r := by linarith
    have hsquare : ((T : ℝ)+1)^2 ≤ 4*L^((2 : ℝ)/3) := by
      calc
        _ ≤ (2*r)^2 := by gcongr
        _ = _ := by
          dsimp [r]
          rw [mul_pow, ← Real.rpow_mul_natCast hL]
          norm_num
    have hlong : L/((T : ℝ)+1) ≤ L^((2 : ℝ)/3) := by
      calc
        _ ≤ L/r := div_le_div_of_nonneg_left hL hrp hTr
        _ = _ := by
          dsimp [r]
          rw [show (2 : ℝ)/3 = 1-1/3 by norm_num, Real.rpow_sub hLp, Real.rpow_one]
    have h := card_le_square_add_div V T hlength
    linarith
  · have h := card_le_square_add_div V 0 hlength
    have hp := Real.rpow_nonneg hL ((2 : ℝ)/3)
    norm_num at h
    linarith

theorem vector_card_bound_actual (V : Finset (ℕ × ℕ)) :
    (V.card : ℝ) ≤ 5*(1+(totalLength V : ℝ)^((2 : ℝ)/3)) :=
  vector_card_bound V (Nat.cast_nonneg _) le_rfl

end ErdosLatticeChain


section

open scoped BigOperators
namespace ErdosLatticeChain

def earlierIndex {n : ℕ} (i : Fin (n-1)) : Fin n := ⟨i.val, by have := i.isLt; omega⟩
def laterIndex {n : ℕ} (i : Fin (n-1)) : Fin n := ⟨i.val+1, by have := i.isLt; omega⟩

theorem earlier_lt_later {n : ℕ} (i : Fin (n-1)) : earlierIndex i < laterIndex i :=
  Nat.lt_succ_self i.val

def consecutiveDifference {n : ℕ} (P : Fin n → ℤ × ℤ) (i : Fin (n-1)) : ℤ × ℤ :=
  ((P (laterIndex i)).1-(P (earlierIndex i)).1,
   (P (laterIndex i)).2-(P (earlierIndex i)).2)

def natIncrement {n : ℕ} (P : Fin n → ℤ × ℤ) (i : Fin (n-1)) : ℕ × ℕ :=
  ((consecutiveDifference P i).1.natAbs, (consecutiveDifference P i).2.natAbs)

noncomputable def incrementVectors {n : ℕ} (P : Fin n → ℤ × ℤ) : Finset (ℕ × ℕ) :=
  Finset.univ.image (natIncrement P)

theorem int_eq_of_natAbs_eq_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a.natAbs = b.natAbs) : a = b := by
  have hc := congrArg (fun n : ℕ => (n : ℤ)) h
  simpa only [Int.natCast_natAbs, abs_of_nonneg ha, abs_of_nonneg hb] using hc

theorem int_eq_of_natAbs_eq_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0)
    (h : a.natAbs = b.natAbs) : a = b := by
  have hc := congrArg (fun n : ℕ => (n : ℤ)) h
  have hn : -a = -b := by
    simpa only [Int.natCast_natAbs, abs_of_nonpos ha, abs_of_nonpos hb] using hc
  exact neg_injective hn

theorem natIncrement_injective {n : ℕ} (P : Fin n → ℤ × ℤ)
    (hx : Monotone fun i => (P i).1)
    (hy : (Monotone fun i => (P i).2) ∨ (Antitone fun i => (P i).2))
    (hd : Function.Injective (consecutiveDifference P)) : Function.Injective (natIncrement P) := by
  intro i j h
  apply hd
  apply Prod.ext
  · apply int_eq_of_natAbs_eq_nonneg
      (sub_nonneg.mpr (hx (earlier_lt_later i).le))
      (sub_nonneg.mpr (hx (earlier_lt_later j).le))
    exact congrArg Prod.fst h
  · rcases hy with hy | hy
    · apply int_eq_of_natAbs_eq_nonneg
        (sub_nonneg.mpr (hy (earlier_lt_later i).le))
        (sub_nonneg.mpr (hy (earlier_lt_later j).le))
      exact congrArg Prod.snd h
    · apply int_eq_of_natAbs_eq_nonpos
        (sub_nonpos.mpr (hy (earlier_lt_later i).le))
        (sub_nonpos.mpr (hy (earlier_lt_later j).le))
      exact congrArg Prod.snd h

theorem incrementVectors_card {n : ℕ} (P : Fin n → ℤ × ℤ)
    (hi : Function.Injective (natIncrement P)) : (incrementVectors P).card = n-1 := by
  rw [incrementVectors, Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]

theorem incrementVectors_length {n : ℕ} (P : Fin (n+1) → ℤ × ℤ)
    (hi : Function.Injective (natIncrement P)) :
    totalLength (incrementVectors P) =
      coordinateVariation (fun i => (P i).1)+coordinateVariation (fun i => (P i).2) := by
  unfold totalLength incrementVectors
  rw [Finset.sum_image]
  · change (∑ i : Fin n, (((P i.succ).1-(P i.castSucc).1).natAbs +
        ((P i.succ).2-(P i.castSucc).2).natAbs)) = _
    rw [Finset.sum_add_distrib]
    rfl
  · exact fun i _ j _ h => hi h

theorem consecutive_first_pos {n : ℕ} (P : Fin n → ℤ × ℤ)
    (hx : StrictMono fun i => (P i).1) (i : Fin (n-1)) :
    0 < (consecutiveDifference P i).1 := sub_pos.mpr (hx (earlier_lt_later i))

end ErdosLatticeChain

end


namespace ErdosImplicitCurvature

noncomputable def inflectionPolynomial (Q : Bivariate) : Bivariate :=
  partialX (partialX Q)*(partialY Q)^2 -
    2*partialX (partialY Q)*partialX Q*partialY Q +
    partialY (partialY Q)*(partialX Q)^2

theorem peval_inflectionPolynomial (Q : Bivariate) (x y : ℝ) :
    peval (inflectionPolynomial Q) x y =
      peval (partialX (partialX Q)) x y*(peval (partialY Q) x y)^2 -
      2*peval (partialX (partialY Q)) x y*peval (partialX Q) x y*peval (partialY Q) x y +
      peval (partialY (partialY Q)) x y*(peval (partialX Q) x y)^2 := by
  simp [inflectionPolynomial, peval]

theorem curvature_scalar_identity {a b c d e u v : ℝ} (hb : b ≠ 0)
    (h1 : a+b*u = 0) (h2 : c+2*d*u+e*u^2+b*v = 0) :
    u = -a/b ∧ v = -(c*b^2-2*d*a*b+e*a^2)/b^3 := by
  have hu : u = -a/b := (eq_div_iff hb).mpr (by nlinarith only [h1])
  refine ⟨hu, ?_⟩
  apply (eq_div_iff (pow_ne_zero 3 hb)).mpr
  rw [hu] at h2
  field_simp at h2
  linear_combination h2

theorem implicit_derivatives (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ}
    (hI : IsOpen I) (hf : ContDiffOn ℝ 2 f I)
    (hcurve : ∀ t ∈ I, peval Q t (f t) = 0) {x : ℝ} (hx : x ∈ I)
    (hQy : peval (partialY Q) x (f x) ≠ 0) :
    deriv f x = -peval (partialX Q) x (f x)/peval (partialY Q) x (f x) ∧
      deriv (deriv f) x = -peval (inflectionPolynomial Q) x (f x)/(peval (partialY Q) x (f x))^3 := by
  rw [peval_inflectionPolynomial]
  exact curvature_scalar_identity hQy
    (implicit_first_equation Q f hI (hf.differentiableOn (by norm_num)) hcurve hx)
    (implicit_second_equation Q f hI hf hcurve hx)

theorem implicit_second_derivative (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ}
    (hI : IsOpen I) (hf : ContDiffOn ℝ 2 f I)
    (hcurve : ∀ t ∈ I, peval Q t (f t) = 0) {x : ℝ} (hx : x ∈ I)
    (hQy : peval (partialY Q) x (f x) ≠ 0) :
    deriv (deriv f) x = -peval (inflectionPolynomial Q) x (f x)/(peval (partialY Q) x (f x))^3 :=
  (implicit_derivatives Q f hI hf hcurve hx hQy).2

theorem curvature_zero_iff (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ}
    (hI : IsOpen I) (hf : ContDiffOn ℝ 2 f I)
    (hcurve : ∀ t ∈ I, peval Q t (f t) = 0) {x : ℝ} (hx : x ∈ I)
    (hQy : peval (partialY Q) x (f x) ≠ 0) :
    deriv (deriv f) x = 0 ↔ peval (inflectionPolynomial Q) x (f x) = 0 := by
  rw [implicit_second_derivative Q f hI hf hcurve hx hQy]
  simp [div_eq_zero_iff, hQy]

theorem curvature_ne_zero_iff (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ}
    (hI : IsOpen I) (hf : ContDiffOn ℝ 2 f I)
    (hcurve : ∀ t ∈ I, peval Q t (f t) = 0) {x : ℝ} (hx : x ∈ I)
    (hQy : peval (partialY Q) x (f x) ≠ 0) :
    deriv (deriv f) x ≠ 0 ↔ peval (inflectionPolynomial Q) x (f x) ≠ 0 :=
  not_congr (curvature_zero_iff Q f hI hf hcurve hx hQy)

end ErdosImplicitCurvature



namespace ErdosLatticeChain

theorem lattice_chain_bound {n : ℕ} (P : Fin n → ℤ × ℤ) (S : ℝ) (hS : 0 ≤ S)
    (hx : StrictMono fun i => (P i).1)
    (hy : (Monotone fun i => (P i).2) ∨ (Antitone fun i => (P i).2))
    (hbox : ∀ i, (0 ≤ ((P i).1 : ℝ) ∧ ((P i).1 : ℝ) ≤ S) ∧
      (0 ≤ ((P i).2 : ℝ) ∧ ((P i).2 : ℝ) ≤ S))
    (hd : Function.Injective (consecutiveDifference P)) :
    (n : ℝ) ≤ 12*(1+S^((2 : ℝ)/3)) := by
  have hp : 0 ≤ S^((2 : ℝ)/3) := Real.rpow_nonneg hS _
  cases n with
  | zero => simp only [Nat.cast_zero]; positivity
  | succ n =>
    have hi := natIncrement_injective P hx.monotone hy hd
    have hcard : (incrementVectors P).card = n := by
      simpa using incrementVectors_card P hi
    have hlength : (totalLength (incrementVectors P) : ℝ) ≤ 2*S := by
      rw [incrementVectors_length P hi, Nat.cast_add]
      have h1 := variation_le_box (fun i => (P i).1) S (Or.inl hx.monotone) (fun i => (hbox i).1)
      have h2 := variation_le_box (fun i => (P i).2) S hy (fun i => (hbox i).2)
      linarith
    have hv := vector_card_bound (incrementVectors P) (show 0 ≤ 2*S by positivity) hlength
    rw [hcard] at hv
    have htwo : (2*S)^((2 : ℝ)/3) ≤ 2*S^((2 : ℝ)/3) := by
      rw [Real.mul_rpow (by norm_num) hS]
      apply mul_le_mul_of_nonneg_right _ hp
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (2 : ℝ)/3 ≤ 1 by norm_num)
      simpa only [Real.rpow_one] using h
    simp only [Nat.cast_succ]
    linarith

noncomputable def chainPoints {n : ℕ} (P : Fin n → ℤ × ℤ) : Finset (ℤ × ℤ) :=
  Finset.univ.image P

theorem lattice_chain_card_bound {n : ℕ} (P : Fin n → ℤ × ℤ) (S : ℝ) (hS : 0 ≤ S)
    (hx : StrictMono fun i => (P i).1)
    (hy : (Monotone fun i => (P i).2) ∨ (Antitone fun i => (P i).2))
    (hbox : ∀ i, (0 ≤ ((P i).1 : ℝ) ∧ ((P i).1 : ℝ) ≤ S) ∧
      (0 ≤ ((P i).2 : ℝ) ∧ ((P i).2 : ℝ) ≤ S))
    (hd : Function.Injective (consecutiveDifference P)) :
    ((chainPoints P).card : ℝ) ≤ 12*(1+S^((2 : ℝ)/3)) := by
  have hi : Function.Injective P := by
    intro i j h
    exact hx.injective (congrArg Prod.fst h)
  rw [chainPoints, Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]
  exact lattice_chain_bound P S hS hx hy hbox hd

noncomputable def consecutiveSlope {n : ℕ} (P : Fin n → ℤ × ℤ) (i : Fin (n-1)) : ℝ :=
  ((consecutiveDifference P i).2 : ℝ)/((consecutiveDifference P i).1 : ℝ)

theorem difference_injective_of_slope {n : ℕ} (P : Fin n → ℤ × ℤ)
    (hs : Function.Injective (consecutiveSlope P)) :
    Function.Injective (consecutiveDifference P) := by
  intro i j h
  apply hs
  exact congrArg (fun v : ℤ × ℤ => (v.2 : ℝ)/(v.1 : ℝ)) h

theorem lattice_chain_strict_slopes {n : ℕ} (P : Fin n → ℤ × ℤ) (S : ℝ) (hS : 0 ≤ S)
    (hx : StrictMono fun i => (P i).1)
    (hy : (Monotone fun i => (P i).2) ∨ (Antitone fun i => (P i).2))
    (hbox : ∀ i, (0 ≤ ((P i).1 : ℝ) ∧ ((P i).1 : ℝ) ≤ S) ∧
      (0 ≤ ((P i).2 : ℝ) ∧ ((P i).2 : ℝ) ≤ S))
    (hs : StrictMono (consecutiveSlope P) ∨ StrictAnti (consecutiveSlope P)) :
    ((chainPoints P).card : ℝ) ≤ 12*(1+S^((2 : ℝ)/3)) := by
  apply lattice_chain_card_bound P S hS hx hy hbox
  apply difference_injective_of_slope P
  rcases hs with hs | hs
  · exact hs.injective
  · exact hs.injective

end ErdosLatticeChain



namespace ErdosConvexGraph

open ErdosLatticeChain

theorem convex_secants_lt {I : Set ℝ} {f : ℝ → ℝ} (hf : StrictConvexOn ℝ I f)
    {a b c d : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) (hd : d ∈ I)
    (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    (f b-f a)/(b-a) < (f d-f c)/(d-c) := by
  rcases eq_or_lt_of_le hbc with hbc | hbc
  · subst c
    exact hf.slope_strict_mono_adjacent ha hd hab hcd
  · exact (hf.slope_strict_mono_adjacent ha hc hab hbc).trans
      (hf.slope_strict_mono_adjacent hb hd hbc hcd)

theorem concave_secants_lt {I : Set ℝ} {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ I f)
    {a b c d : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) (hd : d ∈ I)
    (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    (f d-f c)/(d-c) < (f b-f a)/(b-a) := by
  rcases eq_or_lt_of_le hbc with hbc | hbc
  · subst c
    exact hf.slope_anti_adjacent ha hd hab hcd
  · exact (hf.slope_anti_adjacent hb hd hbc hcd).trans
      (hf.slope_anti_adjacent ha hc hab hbc)

noncomputable def secantSlopes {n : ℕ} (f : ℝ → ℝ) (x : Fin n → ℝ)
    (i : Fin (n-1)) : ℝ :=
  (f (x (laterIndex i))-f (x (earlierIndex i)))/(x (laterIndex i)-x (earlierIndex i))

theorem consecutive_intervals_ordered {n : ℕ} {i j : Fin (n-1)} (hij : i < j) :
    laterIndex i ≤ earlierIndex j := Nat.succ_le_of_lt hij

theorem convex_secantSlopes_strictMono {n : ℕ} {I : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConvexOn ℝ I f) (x : Fin n → ℝ) (hx : StrictMono x)
    (hdom : ∀ i, x i ∈ I) : StrictMono (secantSlopes f x) := by
  intro i j hij
  exact convex_secants_lt hf (hdom _) (hdom _) (hdom _) (hdom _)
    (hx (earlier_lt_later i)) (hx.monotone (consecutive_intervals_ordered hij))
    (hx (earlier_lt_later j))

theorem concave_secantSlopes_strictAnti {n : ℕ} {I : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConcaveOn ℝ I f) (x : Fin n → ℝ) (hx : StrictMono x)
    (hdom : ∀ i, x i ∈ I) : StrictAnti (secantSlopes f x) := by
  intro i j hij
  exact concave_secants_lt hf (hdom _) (hdom _) (hdom _) (hdom _)
    (hx (earlier_lt_later i)) (hx.monotone (consecutive_intervals_ordered hij))
    (hx (earlier_lt_later j))

theorem consecutiveSlope_eq_secantSlopes {n : ℕ} (P : Fin n → ℤ × ℤ) (f : ℝ → ℝ)
    (hgraph : ∀ i, ((P i).2 : ℝ) = f ((P i).1 : ℝ)) :
    consecutiveSlope P = secantSlopes f (fun i => ((P i).1 : ℝ)) := by
  funext i
  simp only [consecutiveSlope, consecutiveDifference, secantSlopes, Int.cast_sub, hgraph]

end ErdosConvexGraph



namespace ErdosConvexGraph

open ErdosLatticeChain

def OnGraph (I : Set ℝ) (f : ℝ → ℝ) (p : ℤ × ℤ) : Prop :=
  (p.1 : ℝ) ∈ I ∧ (p.2 : ℝ) = f (p.1 : ℝ)

def InSquare (S : ℝ) (p : ℤ × ℤ) : Prop :=
  (0 ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ S) ∧ (0 ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ S)

theorem graph_chain_y_monotone {n : ℕ} (P : Fin n → ℤ × ℤ) (I : Set ℝ) (f : ℝ → ℝ)
    (hx : Monotone fun i => (P i).1)
    (hf : MonotoneOn f I ∨ AntitoneOn f I) (hgraph : ∀ i, OnGraph I f (P i)) :
    (Monotone fun i => (P i).2) ∨ (Antitone fun i => (P i).2) := by
  rcases hf with hf | hf
  · left
    intro i j hij
    have h := hf (hgraph i).1 (hgraph j).1 (show ((P i).1 : ℝ) ≤ ((P j).1 : ℝ) by
      exact_mod_cast hx hij)
    rw [← (hgraph i).2, ← (hgraph j).2] at h
    exact_mod_cast h
  · right
    intro i j hij
    have h := hf (hgraph i).1 (hgraph j).1 (show ((P i).1 : ℝ) ≤ ((P j).1 : ℝ) by
      exact_mod_cast hx hij)
    rw [← (hgraph i).2, ← (hgraph j).2] at h
    exact_mod_cast h

theorem graph_chain_slopes {n : ℕ} (P : Fin n → ℤ × ℤ) (I : Set ℝ) (f : ℝ → ℝ)
    (hx : StrictMono fun i => (P i).1)
    (hf : StrictConvexOn ℝ I f ∨ StrictConcaveOn ℝ I f)
    (hgraph : ∀ i, OnGraph I f (P i)) :
    StrictMono (consecutiveSlope P) ∨ StrictAnti (consecutiveSlope P) := by
  have hxr : StrictMono fun i => ((P i).1 : ℝ) := by
    intro i j hij
    change ((P i).1 : ℝ) < ((P j).1 : ℝ)
    exact_mod_cast (show (P i).1 < (P j).1 from hx hij)
  rw [consecutiveSlope_eq_secantSlopes P f (fun i => (hgraph i).2)]
  rcases hf with hf | hf
  · exact Or.inl (convex_secantSlopes_strictMono hf _ hxr (fun i => (hgraph i).1))
  · exact Or.inr (concave_secantSlopes_strictAnti hf _ hxr (fun i => (hgraph i).1))

theorem graph_chain_bound {n : ℕ} (P : Fin n → ℤ × ℤ) (I : Set ℝ) (f : ℝ → ℝ)
    (S : ℝ) (hS : 0 ≤ S) (hx : StrictMono fun i => (P i).1)
    (hcurve : StrictConvexOn ℝ I f ∨ StrictConcaveOn ℝ I f)
    (hmono : MonotoneOn f I ∨ AntitoneOn f I)
    (hgraph : ∀ i, OnGraph I f (P i)) (hbox : ∀ i, InSquare S (P i)) :
    (n : ℝ) ≤ 12*(1+S^((2 : ℝ)/3)) := by
  apply lattice_chain_bound P S hS hx (graph_chain_y_monotone P I f hx.monotone hmono hgraph) hbox
  apply difference_injective_of_slope P
  rcases graph_chain_slopes P I f hx hcurve hgraph with hs | hs
  · exact hs.injective
  · exact hs.injective

theorem graph_chain_card_bound {n : ℕ} (P : Fin n → ℤ × ℤ) (I : Set ℝ) (f : ℝ → ℝ)
    (S : ℝ) (hS : 0 ≤ S) (hx : StrictMono fun i => (P i).1)
    (hcurve : StrictConvexOn ℝ I f ∨ StrictConcaveOn ℝ I f)
    (hmono : MonotoneOn f I ∨ AntitoneOn f I)
    (hgraph : ∀ i, OnGraph I f (P i)) (hbox : ∀ i, InSquare S (P i)) :
    ((chainPoints P).card : ℝ) ≤ 12*(1+S^((2 : ℝ)/3)) :=
  lattice_chain_strict_slopes P S hS hx (graph_chain_y_monotone P I f hx.monotone hmono hgraph)
    hbox (graph_chain_slopes P I f hx hcurve hgraph)

end ErdosConvexGraph



namespace ErdosConvexGraph

def graphAbscissae (G : Finset (ℤ × ℤ)) : Finset ℤ := G.image Prod.fst

noncomputable def graphEnumeration (G : Finset (ℤ × ℤ)) (f : ℝ → ℝ)
    (i : Fin (graphAbscissae G).card) : ℤ × ℤ :=
  ((graphAbscissae G).orderEmbOfFin rfl i,
    ⌊f (((graphAbscissae G).orderEmbOfFin rfl i : ℤ) : ℝ)⌋)

theorem onGraph_fst_injective {I : Set ℝ} {f : ℝ → ℝ} {p q : ℤ × ℤ}
    (hp : OnGraph I f p) (hq : OnGraph I f q) (h : p.1 = q.1) : p = q := by
  apply Prod.ext h
  have he : (p.2 : ℝ) = (q.2 : ℝ) := by rw [hp.2, hq.2, h]
  exact_mod_cast he

theorem graphAbscissae_card (G : Finset (ℤ × ℤ)) (I : Set ℝ) (f : ℝ → ℝ)
    (hG : ∀ p ∈ G, OnGraph I f p) : (graphAbscissae G).card = G.card := by
  apply Finset.card_image_of_injOn
  intro p hp q hq h
  exact onGraph_fst_injective (hG p hp) (hG q hq) h

theorem graphEnumeration_mem (G : Finset (ℤ × ℤ)) (I : Set ℝ) (f : ℝ → ℝ)
    (hG : ∀ p ∈ G, OnGraph I f p) (i : Fin (graphAbscissae G).card) :
    graphEnumeration G f i ∈ G := by
  have hm := (graphAbscissae G).orderEmbOfFin_mem rfl i
  obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hm
  have hpoint : graphEnumeration G f i = p := by
    apply Prod.ext
    · exact he.symm
    · change ⌊f (((graphAbscissae G).orderEmbOfFin rfl i : ℤ) : ℝ)⌋ = p.2
      rw [← he, ← (hG p hp).2]
      exact Int.floor_intCast _
  rw [hpoint]
  exact hp

theorem graphEnumeration_strictMono (G : Finset (ℤ × ℤ)) (f : ℝ → ℝ) :
    StrictMono fun i => (graphEnumeration G f i).1 :=
  ((graphAbscissae G).orderEmbOfFin rfl).strictMono

theorem finite_graph_set_bound (G : Finset (ℤ × ℤ)) (I : Set ℝ) (f : ℝ → ℝ)
    (S : ℝ) (hS : 0 ≤ S)
    (hcurve : StrictConvexOn ℝ I f ∨ StrictConcaveOn ℝ I f)
    (hmono : MonotoneOn f I ∨ AntitoneOn f I)
    (hgraph : ∀ p ∈ G, OnGraph I f p) (hbox : ∀ p ∈ G, InSquare S p) :
    (G.card : ℝ) ≤ 12*(1+S^((2 : ℝ)/3)) := by
  have h := graph_chain_bound (graphEnumeration G f) I f S hS
    (graphEnumeration_strictMono G f) hcurve hmono
    (fun i => hgraph _ (graphEnumeration_mem G I f hgraph i))
    (fun i => hbox _ (graphEnumeration_mem G I f hgraph i))
  rwa [graphAbscissae_card G I f hgraph] at h





attribute [local instance] Classical.propDecidable

noncomputable def graphLatticePoints (I : Set ℝ) (f : ℝ → ℝ) (S : ℝ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (0 : ℤ) ⌊S⌋).product (Finset.Icc (0 : ℤ) ⌊S⌋)).filter (OnGraph I f)

theorem mem_graphLatticePoints (I : Set ℝ) (f : ℝ → ℝ) (S : ℝ) (p : ℤ × ℤ) :
    p ∈ graphLatticePoints I f S ↔ InSquare S p ∧ OnGraph I f p := by
  simp only [graphLatticePoints, InSquare, Finset.mem_filter, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc, Int.le_floor, Int.cast_nonneg_iff]

theorem graph_arc_lattice_bound (I : Set ℝ) (f : ℝ → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hcurve : StrictConvexOn ℝ I f ∨ StrictConcaveOn ℝ I f)
    (hmono : MonotoneOn f I ∨ AntitoneOn f I) :
    ((graphLatticePoints I f S).card : ℝ) ≤ 12*(1+S^((2 : ℝ)/3)) :=
  finite_graph_set_bound _ I f S hS hcurve hmono
    (fun p hp => ((mem_graphLatticePoints I f S p).mp hp).2)
    (fun p hp => ((mem_graphLatticePoints I f S p).mp hp).1)

theorem closed_graph_arc_bound (a b : ℝ) (f : ℝ → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hcurve : StrictConvexOn ℝ (Set.Icc a b) f ∨ StrictConcaveOn ℝ (Set.Icc a b) f)
    (hmono : MonotoneOn f (Set.Icc a b) ∨ AntitoneOn f (Set.Icc a b)) :
    ((graphLatticePoints (Set.Icc a b) f S).card : ℝ) ≤ 12*(1+S^((2 : ℝ)/3)) :=
  graph_arc_lattice_bound _ f S hS hcurve hmono

theorem open_graph_arc_bound (a b : ℝ) (f : ℝ → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hcurve : StrictConvexOn ℝ (Set.Ioo a b) f ∨ StrictConcaveOn ℝ (Set.Ioo a b) f)
    (hmono : MonotoneOn f (Set.Ioo a b) ∨ AntitoneOn f (Set.Ioo a b)) :
    ((graphLatticePoints (Set.Ioo a b) f S).card : ℝ) ≤ 12*(1+S^((2 : ℝ)/3)) :=
  graph_arc_lattice_bound _ f S hS hcurve hmono

end ErdosConvexGraph



namespace ErdosImplicitCurvature

noncomputable def curvatureRatio (Q : Bivariate) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  peval (inflectionPolynomial Q) x (f x)/(peval (partialY Q) x (f x))^3

theorem strictConvexOn_of_curvatureRatio (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ}
    (hI : IsOpen I) (hconv : Convex ℝ I) (hf : ContDiffOn ℝ 2 f I)
    (hcurve : ∀ x ∈ I, peval Q x (f x) = 0)
    (hQy : ∀ x ∈ I, peval (partialY Q) x (f x) ≠ 0)
    (hsign : ∀ x ∈ I, curvatureRatio Q f x < 0) : StrictConvexOn ℝ I f := by
  apply strictConvexOn_of_deriv2_pos hconv hf.continuousOn
  intro x hx
  have hxI := interior_subset hx
  change 0 < deriv (deriv f) x
  rw [implicit_second_derivative Q f hI hf hcurve hxI (hQy x hxI), neg_div]
  exact neg_pos.mpr (hsign x hxI)

theorem strictConcaveOn_of_curvatureRatio (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ}
    (hI : IsOpen I) (hconv : Convex ℝ I) (hf : ContDiffOn ℝ 2 f I)
    (hcurve : ∀ x ∈ I, peval Q x (f x) = 0)
    (hQy : ∀ x ∈ I, peval (partialY Q) x (f x) ≠ 0)
    (hsign : ∀ x ∈ I, 0 < curvatureRatio Q f x) : StrictConcaveOn ℝ I f := by
  apply strictConcaveOn_of_deriv2_neg hconv hf.continuousOn
  intro x hx
  have hxI := interior_subset hx
  change deriv (deriv f) x < 0
  rw [implicit_second_derivative Q f hI hf hcurve hxI (hQy x hxI), neg_div]
  exact neg_neg_of_pos (hsign x hxI)

theorem implicit_graph_lattice_bound (Q : Bivariate) (f : ℝ → ℝ) (a b S : ℝ)
    (hS : 0 ≤ S) (hf : ContDiffOn ℝ 2 f (Set.Ioo a b))
    (hcurve : ∀ x ∈ Set.Ioo a b, peval Q x (f x) = 0)
    (hQy : ∀ x ∈ Set.Ioo a b, peval (partialY Q) x (f x) ≠ 0)
    (hsign : (∀ x ∈ Set.Ioo a b, curvatureRatio Q f x < 0) ∨
      (∀ x ∈ Set.Ioo a b, 0 < curvatureRatio Q f x))
    (hmono : MonotoneOn f (Set.Ioo a b) ∨ AntitoneOn f (Set.Ioo a b)) :
    ((ErdosConvexGraph.graphLatticePoints (Set.Ioo a b) f S).card : ℝ) ≤
      12*(1+S^((2 : ℝ)/3)) := by
  apply ErdosConvexGraph.open_graph_arc_bound a b f S hS _ hmono
  rcases hsign with hsign | hsign
  · exact Or.inl (strictConvexOn_of_curvatureRatio Q f isOpen_Ioo (convex_Ioo a b) hf hcurve hQy hsign)
  · exact Or.inr (strictConcaveOn_of_curvatureRatio Q f isOpen_Ioo (convex_Ioo a b) hf hcurve hQy hsign)





theorem continuous_nonzero_fixed_sign {I : Set ℝ} {g : ℝ → ℝ}
    (hI : IsPreconnected I) (hg : ContinuousOn g I) (hne : ∀ x ∈ I, g x ≠ 0) :
    (∀ x ∈ I, 0 < g x) ∨ (∀ x ∈ I, g x < 0) := by
  by_cases hp : ∀ x ∈ I, 0 < g x
  · exact Or.inl hp
  · right
    push Not at hp
    obtain ⟨a, ha, hga⟩ := hp
    have hneg : g a < 0 := by
      rcases lt_or_eq_of_le hga with h | h
      · exact h
      · exact (hne a ha h).elim
    intro y hy
    by_contra! hgy
    have hz : 0 ∈ g '' I := hI.intermediate_value ha hy hg ⟨hneg.le, hgy⟩
    obtain ⟨z, hz, he⟩ := hz
    exact hne z hz he

theorem regular_implicit_monotone (Q : Bivariate) (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo a b))
    (hcurve : ∀ x ∈ Set.Ioo a b, peval Q x (f x) = 0)
    (hQx : ∀ x ∈ Set.Ioo a b, peval (partialX Q) x (f x) ≠ 0)
    (hQy : ∀ x ∈ Set.Ioo a b, peval (partialY Q) x (f x) ≠ 0) :
    MonotoneOn f (Set.Ioo a b) ∨ AntitoneOn f (Set.Ioo a b) := by
  have hd : DifferentiableOn ℝ f (Set.Ioo a b) := hf.differentiableOn (by norm_num)
  have hc : ContDiffOn ℝ 1 (deriv f) (Set.Ioo a b) := hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hne : ∀ x ∈ Set.Ioo a b, deriv f x ≠ 0 := by
    intro x hx
    rw [implicit_first_derivative Q f isOpen_Ioo hd hcurve hx (hQy x hx)]
    exact div_ne_zero (neg_ne_zero.mpr (hQx x hx)) (hQy x hx)
  rcases continuous_nonzero_fixed_sign isPreconnected_Ioo hc.continuousOn hne with hp | hn
  · left
    exact monotoneOn_of_deriv_nonneg (convex_Ioo a b) hf.continuousOn
      (hd.mono interior_subset) (fun x hx => (hp x (interior_subset hx)).le)
  · right
    exact antitoneOn_of_deriv_nonpos (convex_Ioo a b) hf.continuousOn
      (hd.mono interior_subset) (fun x hx => (hn x (interior_subset hx)).le)

theorem regular_implicit_convex_or_concave (Q : Bivariate) (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo a b))
    (hcurve : ∀ x ∈ Set.Ioo a b, peval Q x (f x) = 0)
    (hQy : ∀ x ∈ Set.Ioo a b, peval (partialY Q) x (f x) ≠ 0)
    (hInf : ∀ x ∈ Set.Ioo a b, peval (inflectionPolynomial Q) x (f x) ≠ 0) :
    StrictConvexOn ℝ (Set.Ioo a b) f ∨ StrictConcaveOn ℝ (Set.Ioo a b) f := by
  have hc1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo a b) := hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hc2 : ContDiffOn ℝ 0 (deriv (deriv f)) (Set.Ioo a b) :=
    hc1.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hne : ∀ x ∈ Set.Ioo a b, deriv (deriv f) x ≠ 0 := by
    intro x hx
    exact (curvature_ne_zero_iff Q f isOpen_Ioo hf hcurve hx (hQy x hx)).mpr (hInf x hx)
  rcases continuous_nonzero_fixed_sign isPreconnected_Ioo hc2.continuousOn hne with hp | hn
  · left
    apply strictConvexOn_of_deriv2_pos (convex_Ioo a b) hf.continuousOn
    intro x hx
    exact hp x (interior_subset hx)
  · right
    apply strictConcaveOn_of_deriv2_neg (convex_Ioo a b) hf.continuousOn
    intro x hx
    exact hn x (interior_subset hx)

theorem regular_implicit_arc_lattice_bound (Q : Bivariate) (f : ℝ → ℝ) (a b S : ℝ)
    (hS : 0 ≤ S) (hf : ContDiffOn ℝ 2 f (Set.Ioo a b))
    (hcurve : ∀ x ∈ Set.Ioo a b, peval Q x (f x) = 0)
    (hQx : ∀ x ∈ Set.Ioo a b, peval (partialX Q) x (f x) ≠ 0)
    (hQy : ∀ x ∈ Set.Ioo a b, peval (partialY Q) x (f x) ≠ 0)
    (hInf : ∀ x ∈ Set.Ioo a b, peval (inflectionPolynomial Q) x (f x) ≠ 0) :
    ((ErdosConvexGraph.graphLatticePoints (Set.Ioo a b) f S).card : ℝ) ≤
      12*(1+S^((2 : ℝ)/3)) :=
  ErdosConvexGraph.open_graph_arc_bound a b f S hS
    (regular_implicit_convex_or_concave Q f a b hf hcurve hQy hInf)
    (regular_implicit_monotone Q f a b hf hcurve hQx hQy)

end ErdosImplicitCurvature


end Erdos970

end OAI
