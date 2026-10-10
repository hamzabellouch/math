import Mathlib
import OAI.Computability.MaxCut.Games.KMSMomentTheorem

namespace OAI

namespace OptimalMaxCut.Unweighted

open Finset
open scoped BigOperators ComplexConjugate

abbrev Vec (p : ℕ) := Fin 6 → ZMod p

def dot {p : ℕ} (x y : Vec p) : ZMod p := ∑ i, x i * y i

variable {p : ℕ} [Fact p.Prime]

@[simp] theorem card_vec : Fintype.card (Vec p) = p ^ 6 := by
  simp [Vec]

omit [Fact (Nat.Prime p)] in
theorem dot_comm (x y : Vec p) : dot x y = dot y x := by
  simp [dot, mul_comm]

@[simp] theorem dot_add_right (x y z : Vec p) :
    dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, sum_add_distrib]

@[simp] theorem dot_sub_left (x y z : Vec p) :
    dot (x - y) z = dot x z - dot y z := by
  simp [dot, sub_mul, sum_sub_distrib]

@[simp] theorem dot_zero_right (x : Vec p) : dot x 0 = 0 := by simp [dot]

noncomputable def dotChar (h : ZMod p) (x : Vec p) : AddChar (Vec p) ℂ where
  toFun y := ZMod.stdAddChar (h * dot x y)
  map_zero_eq_one' := by simp
  map_add_eq_mul' y z := by simp [mul_add, AddChar.map_add_eq_mul]

@[simp] theorem norm_stdChar (a : ZMod p) : ‖ZMod.stdAddChar a‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem dotChar_ne_one (h : ZMod p) (hh : h ≠ 0) (x : Vec p) (hx : x ≠ 0) :
    dotChar h x ≠ 1 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! hn
    exact hx (funext hn)
  apply AddChar.ne_one_iff.mpr
  refine ⟨Pi.single i 1, ?_⟩
  change ZMod.stdAddChar (h * dot x (Pi.single i 1)) ≠ 1
  have hd : dot x (Pi.single i 1) = x i := by simp [dot, Pi.single_apply]
  rw [hd, ← (ZMod.stdAddChar (N := p)).map_zero_eq_one]
  exact fun he => (mul_ne_zero hh hi) (ZMod.injective_stdAddChar he)

theorem sum_dotChar (h : ZMod p) (hh : h ≠ 0) (x : Vec p) :
    ∑ y : Vec p, ZMod.stdAddChar (h * dot x y) =
      if x = 0 then (p : ℂ) ^ 6 else 0 := by
  split_ifs with hx
  · subst x
    simp [dot]
  · exact AddChar.sum_eq_zero_of_ne_one (dotChar_ne_one h hh x hx)

@[simp] theorem conj_stdChar (a : ZMod p) :
    conj (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [← Complex.inv_eq_conj (norm_stdChar a), AddChar.map_neg_eq_inv]

theorem orthogonality (h : ZMod p) (hh : h ≠ 0) (x z : Vec p) :
    ∑ y : Vec p, ZMod.stdAddChar (h * dot x y) *
      conj (ZMod.stdAddChar (h * dot z y)) =
      if x = z then (p : ℂ) ^ 6 else 0 := by
  simp_rw [conj_stdChar, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg,
    ← mul_sub, ← dot_sub_left]
  rw [sum_dotChar h hh]
  simp only [sub_eq_zero]

theorem rectangle_energy (h : ZMod p) (hh : h ≠ 0) (T : Finset (Vec p)) :
    ∑ x : Vec p, ‖∑ y ∈ T, ZMod.stdAddChar (h * dot x y)‖ ^ 2 =
      (p : ℝ) ^ 6 * T.card := by
  have he : (∑ x : Vec p, (‖∑ y ∈ T, ZMod.stdAddChar (h * dot x y)‖ ^ 2 : ℝ) : ℂ) =
      (p : ℂ) ^ 6 * T.card := by
    push_cast
    simp_rw [← Complex.mul_conj', map_sum, sum_mul, mul_sum]
    rw [sum_comm]
    apply Eq.trans (sum_congr rfl (fun y hy => sum_comm ..))
    simp_rw [dot_comm (_ : Vec p), orthogonality h hh]
    simp [mul_comm]
  exact_mod_cast he

theorem rectangle_character_bound (h : ZMod p) (hh : h ≠ 0)
    (S T : Finset (Vec p)) :
    ‖∑ x ∈ S, ∑ y ∈ T, ZMod.stdAddChar (h * dot x y)‖ ≤ (p : ℝ) ^ 9 := by
  let f (x : Vec p) := ‖∑ y ∈ T, ZMod.stdAddChar (h * dot x y)‖
  have htriangle : ‖∑ x ∈ S, ∑ y ∈ T, ZMod.stdAddChar (h * dot x y)‖ ≤ ∑ x ∈ S, f x :=
    norm_sum_le _ _
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := f)
  have henergy : ∑ x ∈ S, f x ^ 2 ≤ (p : ℝ) ^ 6 * T.card := by
    rw [← rectangle_energy h hh T]
    exact sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
  have hS : (S.card : ℝ) ≤ (p : ℝ) ^ 6 := by
    exact_mod_cast (S.card_le_univ.trans_eq card_vec)
  have hT : (T.card : ℝ) ≤ (p : ℝ) ^ 6 := by
    exact_mod_cast (T.card_le_univ.trans_eq card_vec)
  have hbound : (∑ x ∈ S, f x) ^ 2 ≤ (p : ℝ) ^ 18 := by
    calc
      _ ≤ S.card * ∑ x ∈ S, f x ^ 2 := hcs
      _ ≤ S.card * ((p : ℝ) ^ 6 * T.card) :=
        mul_le_mul_of_nonneg_left henergy (by positivity)
      _ ≤ (p : ℝ) ^ 6 * ((p : ℝ) ^ 6 * (p : ℝ) ^ 6) :=
        mul_le_mul hS (mul_le_mul_of_nonneg_left hT (by positivity))
          (by positivity) (by positivity)
      _ = _ := by ring
  have hnonneg : 0 ≤ ∑ x ∈ S, f x := sum_nonneg (fun _ _ => norm_nonneg _)
  have hpower : (p : ℝ) ^ 18 = ((p : ℝ) ^ 9) ^ 2 := by ring
  rw [hpower] at hbound
  have happ : ∑ x ∈ S, f x ≤ (p : ℝ) ^ 9 :=
    (sq_le_sq₀ hnonneg (by positivity)).mp hbound
  exact htriangle.trans happ

/-- Fourier coefficient of the residue indicator, probability normalization. -/
noncomputable def beta (I : Finset (ZMod p)) (h : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ a ∈ I, ZMod.stdAddChar (-(h * a))

@[simp] theorem beta_zero (I : Finset (ZMod p)) :
    beta I 0 = (I.card : ℂ) / p := by simp [beta, div_eq_mul_inv, mul_comm]

theorem beta_norm_le_one (I : Finset (ZMod p)) (h : ZMod p) : ‖beta I h‖ ≤ 1 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hc : (I.card : ℝ) ≤ p := by
    exact_mod_cast (show I.card ≤ p by simpa using I.card_le_univ)
  calc
    _ = (p : ℝ)⁻¹ * ‖∑ a ∈ I, ZMod.stdAddChar (-(h * a))‖ := by
      simp [beta]
    _ ≤ (p : ℝ)⁻¹ * ∑ a ∈ I, ‖ZMod.stdAddChar (-(h * a))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = (p : ℝ)⁻¹ * I.card := by simp
    _ ≤ (p : ℝ)⁻¹ * p := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 1 := inv_mul_cancel₀ hp.ne'

theorem residue_fourier (I : Finset (ZMod p)) (a : ZMod p) :
    (if a ∈ I then (1 : ℂ) else 0) =
      ∑ h : ZMod p, beta I h * ZMod.stdAddChar (h * a) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  symm
  simp_rw [beta, mul_assoc, sum_mul, ← AddChar.map_add_eq_mul]
  rw [← mul_sum, sum_comm]
  have hin (b : ZMod p) :
      ∑ h : ZMod p, ZMod.stdAddChar (-(h * b) + h * a) =
        if a = b then (p : ℂ) else 0 := by
    simp_rw [show ∀ h : ZMod p, -(h * b) + h * a = h * (a - b) by intro; ring]
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p)]
    simp [sub_eq_zero]
  simp_rw [hin]
  by_cases ha : a ∈ I
  · simp [ha, inv_mul_cancel₀ hp]
  · simp [ha]

def rectangleCount (I : Finset (ZMod p)) (S T : Finset (Vec p)) : ℕ :=
  ∑ x ∈ S, ∑ y ∈ T, if dot x y ∈ I then 1 else 0

/-- Isolate the zero frequency in the rectangle count. -/
theorem rectangle_fourier (I : Finset (ZMod p)) (S T : Finset (Vec p)) :
    (rectangleCount I S T : ℂ) - (I.card : ℂ) / p * S.card * T.card =
      ∑ h ∈ (univ : Finset (ZMod p)).erase 0,
        beta I h * ∑ x ∈ S, ∑ y ∈ T, ZMod.stdAddChar (h * dot x y) := by
  have hfull : (rectangleCount I S T : ℂ) =
      ∑ h : ZMod p, beta I h * ∑ x ∈ S, ∑ y ∈ T, ZMod.stdAddChar (h * dot x y) := by
    simp only [rectangleCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    simp_rw [residue_fourier]
    calc
      _ = ∑ x ∈ S, ∑ h : ZMod p, ∑ y ∈ T,
          beta I h * ZMod.stdAddChar (h * dot x y) := by
        apply sum_congr rfl
        intro x hx
        rw [sum_comm]
      _ = ∑ h : ZMod p, ∑ x ∈ S, ∑ y ∈ T,
          beta I h * ZMod.stdAddChar (h * dot x y) := by rw [sum_comm]
      _ = _ := by simp_rw [mul_sum]
  rw [hfull, ← sum_erase_add _ _ (mem_univ (0 : ZMod p))]
  simp [mul_assoc]

/-- Absolute discrepancy in edge counts before dividing by Q=p^12. -/
theorem rectangle_discrepancy_count (I : Finset (ZMod p)) (S T : Finset (Vec p)) :
    |(rectangleCount I S T : ℝ) - (I.card : ℝ) / p * S.card * T.card| ≤ (p : ℝ) ^ 10 := by
  have hr : (rectangleCount I S T : ℂ) - (I.card : ℂ) / p * S.card * T.card =
      ((rectangleCount I S T : ℝ) - (I.card : ℝ) / p * S.card * T.card : ℝ) := by
    push_cast
    rfl
  have hbound : ‖(rectangleCount I S T : ℂ) - (I.card : ℂ) / p * S.card * T.card‖ ≤
      (p : ℝ) ^ 10 := by
    rw [rectangle_fourier]
    calc
      _ ≤ ∑ h ∈ (univ : Finset (ZMod p)).erase 0,
          ‖beta I h * ∑ x ∈ S, ∑ y ∈ T, ZMod.stdAddChar (h * dot x y)‖ := norm_sum_le _ _
      _ ≤ ∑ h ∈ (univ : Finset (ZMod p)).erase 0, (p : ℝ) ^ 9 := by
        apply sum_le_sum
        intro h hh
        rw [norm_mul]
        exact (mul_le_mul (beta_norm_le_one I h)
          (rectangle_character_bound h (mem_erase.mp hh).1 S T)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ ≤ ∑ _ : ZMod p, (p : ℝ) ^ 9 :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => by positivity)
      _ = (p : ℝ) ^ 10 := by simp [pow_succ, mul_comm]
  rw [hr, Complex.norm_real, Real.norm_eq_abs] at hbound
  exact hbound

def residueSet (w : ℚ) : Finset (ZMod p) :=
  (range ⌊(p : ℚ) * w⌋₊).image (fun j : ℕ => (j : ZMod p))

theorem card_residueSet (w : ℚ) (_hw : 0 ≤ w) (hw1 : w ≤ 1) :
    (residueSet (p := p) w).card = ⌊(p : ℚ) * w⌋₊ := by
  have hn : ⌊(p : ℚ) * w⌋₊ ≤ p :=
    Nat.floor_le_of_le (by nlinarith [show (0 : ℚ) ≤ p by positivity])
  rw [residueSet, card_image_of_injOn]
  · exact card_range _
  · intro a ha b hb hab
    have ha' : a < p := (mem_range.mp ha).trans_le hn
    have hb' : b < p := (mem_range.mp hb).trans_le hn
    have h := congrArg ZMod.val hab
    simpa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using h

/-- The exact rounding loss uses the original rational weight, not a renormalized one. -/
theorem residue_density_error (w : ℚ) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    |((residueSet (p := p) w).card : ℝ) / p - w| ≤ 1 / (p : ℝ) := by
  rw [card_residueSet w hw hw1]
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hfloor : ((⌊(p : ℚ) * w⌋₊ : ℕ) : ℝ) ≤ (p : ℝ) * (w : ℝ) := by
    exact_mod_cast (Nat.floor_le (show 0 ≤ (p : ℚ) * w by positivity))
  have hfloor' : (p : ℝ) * (w : ℝ) < (⌊(p : ℚ) * w⌋₊ : ℕ) + (1 : ℝ) := by
    exact_mod_cast (Nat.lt_floor_add_one ((p : ℚ) * w))
  have hlo : (⌊(p : ℚ) * w⌋₊ : ℝ) / p ≤ (w : ℝ) :=
    (div_le_iff₀ hp).mpr (by nlinarith)
  have hhi : (w : ℝ) < ((⌊(p : ℚ) * w⌋₊ : ℝ) + 1) / p :=
    (lt_div_iff₀ hp).mpr (by nlinarith)
  rw [add_div] at hhi
  exact abs_le.mpr ⟨by linarith, by linarith [show (0 : ℝ) ≤ 1 / p by positivity]⟩

theorem rectangle_discrepancy (w : ℚ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (S T : Finset (Vec p)) :
    |(rectangleCount (residueSet w) S T : ℝ) / (p : ℝ) ^ 12 -
      w * ((S.card : ℝ) / (p : ℝ) ^ 6) * ((T.card : ℝ) / (p : ℝ) ^ 6)| ≤
      1 / (p : ℝ) + 1 / (p : ℝ) ^ 2 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  let q : ℝ := (p : ℝ) ^ 6
  have hq : 0 < q := by dsimp [q]; positivity
  have hS : (S.card : ℝ) / q ≤ 1 := by
    apply (div_le_one hq).mpr
    dsimp [q]
    exact_mod_cast (S.card_le_univ.trans_eq card_vec)
  have hT : (T.card : ℝ) / q ≤ 1 := by
    apply (div_le_one hq).mpr
    dsimp [q]
    exact_mod_cast (T.card_le_univ.trans_eq card_vec)
  have hfrac : 0 ≤ (S.card : ℝ) / q * ((T.card : ℝ) / q) := by positivity
  have hfrac1 : (S.card : ℝ) / q * ((T.card : ℝ) / q) ≤ 1 := by
    nlinarith [show (0 : ℝ) ≤ S.card / q by positivity,
      show (0 : ℝ) ≤ T.card / q by positivity]
  have hfirst : |(rectangleCount (residueSet w) S T : ℝ) / (p : ℝ) ^ 12 -
      ((residueSet (p := p) w).card : ℝ) / p * (S.card / q) * (T.card / q)| ≤
      1 / (p : ℝ) ^ 2 := by
    have heq : (rectangleCount (residueSet w) S T : ℝ) / (p : ℝ) ^ 12 -
        ((residueSet (p := p) w).card : ℝ) / p * (S.card / q) * (T.card / q) =
        ((rectangleCount (residueSet w) S T : ℝ) -
          ((residueSet (p := p) w).card : ℝ) / p * S.card * T.card) / (p : ℝ) ^ 12 := by
      dsimp [q]
      field_simp

    rw [heq, abs_div, abs_of_pos (pow_pos hp _)]
    apply (div_le_iff₀ (pow_pos hp _)).mpr
    calc
      _ ≤ (p : ℝ) ^ 10 := rectangle_discrepancy_count _ S T
      _ = 1 / (p : ℝ) ^ 2 * (p : ℝ) ^ 12 := by field_simp
  have hsecond : |(((residueSet (p := p) w).card : ℝ) / p - w) *
      (S.card / q * (T.card / q))| ≤ 1 / (p : ℝ) := by
    rw [abs_mul, abs_of_nonneg hfrac]
    exact (mul_le_mul (residue_density_error w hw hw1) hfrac1 hfrac (by positivity)).trans_eq
      (mul_one _)
  have heq : (rectangleCount (residueSet w) S T : ℝ) / (p : ℝ) ^ 12 -
      w * ((S.card : ℝ) / (p : ℝ) ^ 6) * ((T.card : ℝ) / (p : ℝ) ^ 6) =
      ((rectangleCount (residueSet w) S T : ℝ) / (p : ℝ) ^ 12 -
        ((residueSet (p := p) w).card : ℝ) / p * (S.card / q) * (T.card / q)) +
        (((residueSet (p := p) w).card : ℝ) / p - w) * (S.card / q * (T.card / q)) := by
    dsimp [q]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (add_comm _ _))

section Rounding

variable {V : Type*} [Fintype V] [DecidableEq V]

def cutMass (a : V → ℝ) (σ : V → Bool) : ℝ :=
  ∏ i, if σ i then a i else 1 - a i

@[simp] theorem sum_cutMass (a : V → ℝ) : ∑ σ : V → Bool, cutMass a σ = 1 := by
  simp_rw [cutMass]
  rw [← Fintype.prod_sum (fun (i : V) (b : Bool) => if b then a i else 1 - a i)]
  simp []

omit [DecidableEq V] in
theorem cutMass_nonneg (a : V → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (σ : V → Bool) :
    0 ≤ cutMass a σ := by
  apply prod_nonneg
  intro i hi
  exact ite_nonneg (ha i).1 (sub_nonneg.mpr (ha i).2)

/-- Two distinct coordinates of a product law, proved by finite product expansion. -/
theorem independent_pair (f : V → Bool → ℝ) (hf : ∀ i, ∑ b : Bool, f i b = 1)
    (u v : V) (huv : u ≠ v) (g k : Bool → ℝ) :
    ∑ σ : V → Bool, (∏ i, f i (σ i)) * g (σ u) * k (σ v) =
      (∑ b : Bool, f u b * g b) * (∑ b : Bool, f v b * k b) := by
  let F (i : V) (b : Bool) := f i b * (if i = u then g b else 1) *
    (if i = v then k b else 1)
  have hmul (σ : V → Bool) : (∏ i, f i (σ i)) * g (σ u) * k (σ v) = ∏ i, F i (σ i) := by
    dsimp only [F]
    simp only [prod_mul_distrib]
    simp
  simp_rw [hmul]
  rw [← Fintype.prod_sum]
  have hF (i : V) : (∑ b : Bool, F i b) =
      (if i = u then (∑ b : Bool, f u b * g b) else 1) *
      (if i = v then (∑ b : Bool, f v b * k b) else 1) := by
    by_cases hiu : i = u
    · subst i
      simp [F, huv]
    · by_cases hiv : i = v
      · subst i
        simp [F, Ne.symm huv]
      · simpa [F, hiu, hiv] using hf i
  simp_rw [hF]
  rw [prod_mul_distrib]
  simp

/-- Probability that two distinct vertices receive different cut signs. -/
theorem cutMass_crossing (a : V → ℝ) (u v : V) (huv : u ≠ v) :
    ∑ σ : V → Bool, cutMass a σ * (if σ u ≠ σ v then 1 else 0) =
      a u * (1 - a v) + (1 - a u) * a v := by
  let f (i : V) (b : Bool) : ℝ := if b then a i else 1 - a i
  let g (b : Bool) : ℝ := if b then 1 else 0
  let k (b : Bool) : ℝ := if b then 0 else 1
  have hf (i : V) : ∑ b : Bool, f i b = 1 := by simp [f]
  have hcross (σ : V → Bool) : (if σ u ≠ σ v then (1 : ℝ) else 0) =
      g (σ u) * k (σ v) + k (σ u) * g (σ v) := by
    cases hu : σ u <;> cases hv : σ v <;> simp [g, k]
  simp_rw [hcross, mul_add, ← mul_assoc]
  rw [sum_add_distrib]
  change (∑ σ : V → Bool, (∏ i, f i (σ i)) * g (σ u) * k (σ v)) +
    (∑ σ : V → Bool, (∏ i, f i (σ i)) * k (σ u) * g (σ v)) = _
  rw [independent_pair f hf u v huv, independent_pair f hf u v huv]
  simp [f, g, k]

end Rounding

/-- Weighted cut on unordered distinct vertex pairs, on the original weight scale. -/
def weightedCut {N : ℕ} (w : Fin N → Fin N → ℝ) (σ : Fin N → Bool) : ℝ :=
  ∑ u, ∑ v, if u < v ∧ σ u ≠ σ v then w u v else 0

noncomputable def weightedMax {N : ℕ} (w : Fin N → Fin N → ℝ) : ℝ :=
  (univ.image (weightedCut w)).max' (univ_nonempty.image _)

theorem weightedCut_le_max {N : ℕ} (w : Fin N → Fin N → ℝ) (σ : Fin N → Bool) :
    weightedCut w σ ≤ weightedMax w := by
  exact (univ.image (weightedCut w)).le_max' _ (mem_image.mpr ⟨σ, mem_univ _, rfl⟩)

theorem weightedMax_attained {N : ℕ} (w : Fin N → Fin N → ℝ) :
    ∃ σ : Fin N → Bool, weightedCut w σ = weightedMax w := by
  have hm := (univ.image (weightedCut w)).max'_mem (univ_nonempty.image _)
  obtain ⟨σ, hσ, he⟩ := mem_image.mp hm
  exact ⟨σ, he⟩

/-- Expected cut weight under independent randomized rounding. -/
def fractionalCut {N : ℕ} (w : Fin N → Fin N → ℝ) (a : Fin N → ℝ) : ℝ :=
  ∑ u, ∑ v, if u < v then w u v * (a u * (1 - a v) + (1 - a u) * a v) else 0

theorem fractionalCut_expectation {N : ℕ} (w : Fin N → Fin N → ℝ) (a : Fin N → ℝ) :
    fractionalCut w a = ∑ σ : Fin N → Bool, cutMass a σ * weightedCut w σ := by
  unfold fractionalCut weightedCut
  symm
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  by_cases huv : u < v
  · simp only [huv, true_and, ite_true]
    have h (σ : Fin N → Bool) : cutMass a σ * (if σ u ≠ σ v then w u v else 0) =
        w u v * (cutMass a σ * (if σ u ≠ σ v then 1 else 0)) := by
      split_ifs <;> ring
    simp_rw [h]
    rw [← mul_sum, cutMass_crossing a u v (ne_of_lt huv)]
  · simp [huv]

/-- Rounding cannot exceed an actual integral maximum cut. -/
theorem fractionalCut_le_max {N : ℕ} (w : Fin N → Fin N → ℝ) (a : Fin N → ℝ)
    (ha : ∀ u, 0 ≤ a u ∧ a u ≤ 1) : fractionalCut w a ≤ weightedMax w := by
  rw [fractionalCut_expectation]
  calc
    _ ≤ ∑ σ : Fin N → Bool, cutMass a σ * weightedMax w :=
      sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left (weightedCut_le_max w σ)
        (cutMass_nonneg a ha σ))
    _ = weightedMax w := by rw [← sum_mul, sum_cutMass, one_mul]

def vecEquiv : Vec p ≃ Fin (p ^ 6) :=
  (Equiv.arrowCongr (Equiv.refl (Fin 6)) (ZMod.finEquiv p).symm.toEquiv).trans
    finFunctionFinEquiv

/-- Explicit lexicographic indexing of all Np^6 output vertices. -/
def vertexEquiv (N : ℕ) : (Fin N × Vec p) ≃ Fin (N * p ^ 6) :=
  (Equiv.prodCongr (Equiv.refl (Fin N)) vecEquiv).trans finProdFinEquiv

@[simp] theorem vertexEquiv_val {N : ℕ} (u : Fin N) (x : Vec p) :
    (vertexEquiv N (u, x) : ℕ) = (vecEquiv x : ℕ) + p ^ 6 * (u : ℕ) := rfl

theorem vertexEquiv_lt_of_lt {N : ℕ} (u v : Fin N) (x y : Vec p) (huv : u < v) :
    vertexEquiv N (u, x) < vertexEquiv N (v, y) := by
  change (vecEquiv x : ℕ) + p ^ 6 * (u : ℕ) < (vecEquiv y : ℕ) + p ^ 6 * (v : ℕ)
  have h := Nat.mul_le_mul_left (p ^ 6) (show (u : ℕ) + 1 ≤ (v : ℕ) from huv)
  have hx := (vecEquiv x).isLt
  nlinarith

theorem vertexEquiv_lt_iff_of_ne {N : ℕ} (u v : Fin N) (x y : Vec p) (huv : u ≠ v) :
    vertexEquiv N (u, x) < vertexEquiv N (v, y) ↔ u < v := by
  constructor
  · intro h
    rcases lt_or_gt_of_ne huv with huv' | hvu'
    · exact huv'
    · exact False.elim (lt_asymm h (vertexEquiv_lt_of_lt v u y x hvu'))
  · exact vertexEquiv_lt_of_lt u v x y

/-- The actual simple unweighted finite output graph, not an abstract promise. -/
def blowupGraph {N : ℕ} (w : Fin N → Fin N → ℚ) (hw : ∀ u v, w u v = w v u) : Graph where
  vertices := N * p ^ 6
  adj i j :=
    let a := (vertexEquiv N).symm i
    let b := (vertexEquiv N).symm j
    decide (a.1 ≠ b.1 ∧ dot a.2 b.2 ∈ residueSet (w a.1 b.1))
  symmetric i j := by
    dsimp only
    rw [dot_comm, hw]
    simp only [ne_comm]
  loopless i := by simp

/-- The scale is p^12, not the output number of edges. -/
def blowupOutput {N : ℕ} (w : Fin N → Fin N → ℚ) (hw : ∀ u v, w u v = w v u) : ScaledGraph where
  graph := blowupGraph (p := p) w hw
  scale := p ^ 12
  scale_pos := pow_pos (Fact.out : p.Prime).pos _

@[simp] theorem blowup_adj {N : ℕ} (w : Fin N → Fin N → ℚ)
    (hw : ∀ u v, w u v = w v u) (u v : Fin N) (x y : Vec p) :
    (blowupGraph w hw).adj (vertexEquiv N (u, x)) (vertexEquiv N (v, y)) =
      decide (u ≠ v ∧ dot x y ∈ residueSet (w u v)) := by
  simp [blowupGraph]

/-- A cut expressed in cluster coordinates. -/
def clusterCutCount {N : ℕ} (w : Fin N → Fin N → ℚ) (σ : Fin N → Vec p → Bool) : ℕ :=
  ∑ u, ∑ v, if u < v then
    ∑ x, ∑ y, if dot x y ∈ residueSet (w u v) ∧ σ u x ≠ σ v y then 1 else 0
    else 0

theorem blowup_cutSize {N : ℕ} (w : Fin N → Fin N → ℚ)
    (hw : ∀ u v, w u v = w v u) (cut : Fin (N * p ^ 6) → Bool) :
    (blowupGraph w hw).cutSize cut =
      clusterCutCount w (fun u x => cut (vertexEquiv N (u, x))) := by
  change (∑ u : Fin (N * p ^ 6), ∑ v : Fin (N * p ^ 6),
    if u < v ∧ (blowupGraph (p := p) w hw).adj u v = true ∧ cut u ≠ cut v
      then (1 : ℕ) else 0) = _
  rw [← Equiv.sum_comp (vertexEquiv N)]
  simp_rw [← Equiv.sum_comp (vertexEquiv N)]
  simp only [Fintype.sum_prod_type]
  unfold clusterCutCount
  apply sum_congr rfl
  intro u hu
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  by_cases huv : u < v
  · simp only [huv, ite_true]
    apply sum_congr rfl
    intro x hx
    apply sum_congr rfl
    intro y hy
    simp [blowup_adj, vertexEquiv_lt_of_lt u v x y huv, ne_of_lt huv]
  · simp only [huv, ite_false]
    apply sum_eq_zero
    intro x hx
    apply sum_eq_zero
    intro y hy
    by_cases heq : u = v
    · subst v
      simp
    · have hn : ¬ vertexEquiv N (u, x) < vertexEquiv N (v, y) :=
        fun h => huv ((vertexEquiv_lt_iff_of_ne u v x y heq).mp h)
      simp [hn]

/-- Either side of a cut inside one cluster. -/
def cutSet (σ : Vec p → Bool) (b : Bool) : Finset (Vec p) :=
  univ.filter (fun x => σ x = b)

@[simp] theorem mem_cutSet (σ : Vec p → Bool) (b : Bool) (x : Vec p) :
    x ∈ cutSet σ b ↔ σ x = b := by simp [cutSet]

theorem cutSet_card_partition (σ : Vec p → Bool) :
    (cutSet σ true).card + (cutSet σ false).card = p ^ 6 := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Vec p)))
    (fun x => σ x = true)
  simpa [cutSet] using h

/-- Fraction of a cluster on the positive side, on the exact p^6 scale. -/
noncomputable def cutFraction (σ : Vec p → Bool) : ℝ := (cutSet σ true).card / (p : ℝ) ^ 6

theorem cutFraction_mem (σ : Vec p → Bool) :
    0 ≤ cutFraction σ ∧ cutFraction σ ≤ 1 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  constructor
  · unfold cutFraction; positivity
  · unfold cutFraction
    apply (div_le_one (pow_pos hp _)).mpr
    exact_mod_cast ((cutSet σ true).card_le_univ.trans_eq card_vec)

theorem cutFraction_false (σ : Vec p → Bool) :
    ((cutSet σ false).card : ℝ) / (p : ℝ) ^ 6 = 1 - cutFraction σ := by
  have hp : (p : ℝ) ^ 6 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hc : ((cutSet σ true).card : ℝ) + (cutSet σ false).card = (p : ℝ) ^ 6 := by
    exact_mod_cast cutSet_card_partition σ
  have h : cutFraction σ + ((cutSet σ false).card : ℝ) / (p : ℝ) ^ 6 = 1 := by
    rw [cutFraction, ← add_div, hc, div_self hp]
  linarith

/-- The exact edge count crossing between two distinct clusters. -/
def pairCutCount (w : ℚ) (σ τ : Vec p → Bool) : ℕ :=
  ∑ x, ∑ y, if dot x y ∈ residueSet w ∧ σ x ≠ τ y then 1 else 0

theorem rectangle_cutSet (I : Finset (ZMod p)) (σ τ : Vec p → Bool) (b c : Bool) :
    rectangleCount I (cutSet σ b) (cutSet τ c) =
      ∑ x, ∑ y, if σ x = b ∧ τ y = c ∧ dot x y ∈ I then 1 else 0 := by
  simp only [rectangleCount, cutSet, sum_filter]
  apply sum_congr rfl
  intro x hx
  by_cases hb : σ x = b
  · simp only [hb, ite_true, true_and]
    apply sum_congr rfl
    intro y hy
    by_cases hc : τ y = c <;> simp [hc]
  · simp [hb]

theorem pairCutCount_rectangles (w : ℚ) (σ τ : Vec p → Bool) :
    pairCutCount w σ τ =
      rectangleCount (residueSet w) (cutSet σ true) (cutSet τ false) +
      rectangleCount (residueSet w) (cutSet σ false) (cutSet τ true) := by
  rw [rectangle_cutSet, rectangle_cutSet, ← sum_add_distrib]
  unfold pairCutCount
  apply sum_congr rfl
  intro x hx
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro y hy
  cases hσ : σ x <;> cases hτ : τ y <;> simp []

theorem pairCutCount_discrepancy (w : ℚ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (σ τ : Vec p → Bool) :
    |(pairCutCount w σ τ : ℝ) / (p : ℝ) ^ 12 -
      w * (cutFraction σ * (1 - cutFraction τ) + (1 - cutFraction σ) * cutFraction τ)| ≤
      2 * (1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) := by
  have h₁ := rectangle_discrepancy w hw hw1 (cutSet σ true) (cutSet τ false)
  have h₂ := rectangle_discrepancy w hw hw1 (cutSet σ false) (cutSet τ true)
  rw [cutFraction_false] at h₁ h₂
  change |(rectangleCount _ _ _ : ℝ) / (p : ℝ) ^ 12 -
    w * cutFraction σ * (1 - cutFraction τ)| ≤ _ at h₁
  change |(rectangleCount _ _ _ : ℝ) / (p : ℝ) ^ 12 -
    w * (1 - cutFraction σ) * cutFraction τ| ≤ _ at h₂
  rw [pairCutCount_rectangles, Nat.cast_add, add_div]
  calc
    _ = |((rectangleCount (residueSet w) (cutSet σ true) (cutSet τ false) : ℝ) /
          (p : ℝ) ^ 12 - w * cutFraction σ * (1 - cutFraction τ)) +
        ((rectangleCount (residueSet w) (cutSet σ false) (cutSet τ true) : ℝ) /
          (p : ℝ) ^ 12 - w * (1 - cutFraction σ) * cutFraction τ)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

/-- Twice the number of unordered distinct pairs, including N=0 and N=1. -/
theorem twice_pair_count (N : ℕ) :
    (∑ u : Fin N, ∑ v : Fin N, if u < v then (2 : ℝ) else 0) =
      (N : ℝ) * ((N : ℝ) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Fin.sum_univ_succ, Fin.not_lt_zero, ite_false, Fin.succ_pos,
      ite_true, sum_const, card_fin, nsmul_eq_mul, zero_add, Fin.succ_lt_succ_iff,
      ih, Nat.cast_add, Nat.cast_one]
    ring

/-- Summing the exact pair loss on the common unnormalized scale. -/
theorem clusterCutCount_discrepancy {N : ℕ} (w : Fin N → Fin N → ℚ)
    (hbound : ∀ u v, u < v → 0 ≤ w u v ∧ w u v ≤ 1)
    (σ : Fin N → Vec p → Bool) :
    |(clusterCutCount w σ : ℝ) / (p : ℝ) ^ 12 -
      fractionalCut (fun u v => (w u v : ℝ)) (fun u => cutFraction (σ u))| ≤
      (N : ℝ) * ((N : ℝ) - 1) * (1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) := by
  change |((∑ u, ∑ v, if u < v then pairCutCount (w u v) (σ u) (σ v) else 0 : ℕ) : ℝ) /
    (p : ℝ) ^ 12 - ∑ u, ∑ v, if u < v then
      (w u v : ℝ) * (cutFraction (σ u) * (1 - cutFraction (σ v)) +
        (1 - cutFraction (σ u)) * cutFraction (σ v)) else 0| ≤ _
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, sum_div]
  rw [← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ u, ∑ v,
        |(if u < v then (pairCutCount (w u v) (σ u) (σ v) : ℝ) else 0) /
          (p : ℝ) ^ 12 - (if u < v then
          (w u v : ℝ) * (cutFraction (σ u) * (1 - cutFraction (σ v)) +
            (1 - cutFraction (σ u)) * cutFraction (σ v)) else 0)| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun u _ => abs_sum_le_sum_abs _ _))
    _ ≤ ∑ u, ∑ v, if u < v then 2 * (1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) else 0 := by
      apply sum_le_sum
      intro u hu
      apply sum_le_sum
      intro v hv
      by_cases huv : u < v
      · simpa only [huv, ite_true] using
          pairCutCount_discrepancy (w u v) (hbound u v huv).1 (hbound u v huv).2 (σ u) (σ v)
      · simp [huv]
    _ = _ := by
      have he (u v : Fin N) :
          (if u < v then 2 * (1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) else 0) =
          (if u < v then (2 : ℝ) else 0) * (1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) := by
        split_ifs <;> ring
      simp_rw [he, ← sum_mul]
      rw [twice_pair_count]

/-- Every cut lies below the finite unweighted optimum. -/
theorem graph_cut_le_max (G : Graph) (σ : Fin G.vertices → Bool) :
    G.cutSize σ ≤ G.maxCut := by
  unfold Graph.maxCut
  exact le_sup (s := univ.image G.cutSize) (f := id) (mem_image.mpr ⟨σ, mem_univ _, rfl⟩)

/-- The finite unweighted optimum is attained by an actual cut. -/
theorem graph_max_attained (G : Graph) : ∃ σ, G.cutSize σ = G.maxCut := by
  have h := sup_mem_of_nonempty (s := (univ : Finset (Fin G.vertices → Bool)))
    (f := G.cutSize) univ_nonempty
  obtain ⟨σ, hσ, he⟩ := h
  refine ⟨σ, ?_⟩
  simpa [Graph.maxCut, sup_image, Function.comp_def] using he

@[simp] theorem cutFraction_const (b : Bool) :
    cutFraction (p := p) (fun _ => b) = if b then 1 else 0 := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  cases b <;> simp [cutFraction, cutSet, hp]

theorem fractionalCut_integral {N : ℕ} (w : Fin N → Fin N → ℝ) (σ : Fin N → Bool) :
    fractionalCut w (fun u => if σ u then 1 else 0) = weightedCut w σ := by
  unfold fractionalCut weightedCut
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  cases hσ : σ u <;> cases hτ : σ v <;> simp [hσ, hτ]

/-- Full optimum comparison for the actual simple finite graph.
No complexity certificate is asserted in this analytic/combinatorial theorem. -/
theorem blowup_maxCut_error {N : ℕ} (w : Fin N → Fin N → ℚ)
    (hw : ∀ u v, w u v = w v u)
    (hbound : ∀ u v, u < v → 0 ≤ w u v ∧ w u v ≤ 1) :
    |((blowupGraph (p := p) w hw).maxCut : ℝ) / (p : ℝ) ^ 12 -
      weightedMax (fun u v => (w u v : ℝ))| ≤
      (N : ℝ) * ((N : ℝ) - 1) * (1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  apply abs_le.mpr
  constructor
  · obtain ⟨σ, hσ⟩ := weightedMax_attained (fun u v => (w u v : ℝ))
    let cut : Fin (N * p ^ 6) → Bool := fun i => σ ((vertexEquiv N).symm i).1
    have he : (blowupGraph (p := p) w hw).cutSize cut =
        clusterCutCount w (fun u (_ : Vec p) => σ u) := by
      rw [blowup_cutSize]
      simp only [cut, Equiv.symm_apply_apply]
    have hc := clusterCutCount_discrepancy w hbound (fun u (_ : Vec p) => σ u)
    simp only [cutFraction_const, fractionalCut_integral, hσ] at hc
    have hmax := div_le_div_of_nonneg_right
      (show ((blowupGraph (p := p) w hw).cutSize cut : ℝ) ≤
        (blowupGraph (p := p) w hw).maxCut from by exact_mod_cast graph_cut_le_max (blowupGraph (p := p) w hw) cut)
      (le_of_lt (pow_pos hp 12))
    rw [he] at hmax
    linarith [(abs_le.mp hc).1]
  · obtain ⟨cut, hcut⟩ := graph_max_attained (blowupGraph (p := p) w hw)
    have hc := clusterCutCount_discrepancy w hbound
      (fun u x => cut (vertexEquiv N (u, x)))
    rw [← blowup_cutSize w hw cut, hcut] at hc
    have hf := fractionalCut_le_max (fun u v => (w u v : ℝ))
      (fun u => cutFraction (fun x => cut (vertexEquiv N (u, x))))
      (fun u => cutFraction_mem _)
    linarith [(abs_le.mp hc).2]

def totalWeight {N : ℕ} (w : Fin N → Fin N → ℚ) : ℚ :=
  ∑ u, ∑ v, if u < v then w u v else 0

theorem normalized_pair_bound {N : ℕ} (w : Fin N → Fin N → ℚ)
    (hnonneg : ∀ u v, u < v → 0 ≤ w u v) (hscale : totalWeight w ≤ 1) :
    ∀ u v, u < v → 0 ≤ w u v ∧ w u v ≤ 1 := by
  intro u v huv
  refine ⟨hnonneg u v huv, ?_⟩
  have hx (u v : Fin N) : 0 ≤ (if u < v then w u v else 0) := by
    split_ifs with h
    · exact hnonneg u v h
    · exact le_rfl
  have h₁ := single_le_sum (fun v (_ : v ∈ (univ : Finset (Fin N))) => hx u v) (mem_univ v)
  have h₂ : (∑ v, if u < v then w u v else 0) ≤ totalWeight w := by
    unfold totalWeight
    apply single_le_sum (s := univ) (a := u)
    · intro u hu
      exact sum_nonneg (fun v _ => hx u v)
    · exact mem_univ _
  have h₁' : w u v ≤ ∑ v, if u < v then w u v else 0 := by
    simpa only [huv, ite_true] using h₁
  exact h₁'.trans (h₂.trans hscale)

/-- Bounded deterministic prime search. Its bound follows from Bertrand,
not a prime oracle or an unbounded assumed operation. -/
def searchPrime (m : ℕ) : ℕ :=
  ((List.range (2 * (m + 1) + 1)).find? (fun q => decide (m + 1 < q ∧ q.Prime))).getD 2

theorem searchPrime_spec (m : ℕ) :
    (searchPrime m).Prime ∧ m < searchPrime m ∧ searchPrime m ≤ 2 * (m + 1) := by
  obtain ⟨q, hq, hmq, hqbound⟩ := Nat.exists_prime_lt_and_le_two_mul (m + 1) (by omega)
  have hs : ((List.range (2 * (m + 1) + 1)).find?
      (fun q => decide (m + 1 < q ∧ q.Prime))).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨q, List.mem_range.mpr (by omega), by simp [hmq, hq]⟩
  cases hf : ((List.range (2 * (m + 1) + 1)).find?
      (fun q => decide (m + 1 < q ∧ q.Prime))) with
  | none =>
    rw [hf] at hs
    contradiction
  | some q =>
    have hq' : m + 1 < q ∧ q.Prime := by simpa using List.find?_some hf
    have hq'' := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    simpa only [searchPrime, hf, Option.getD_some] using
      (show q.Prime ∧ m < q ∧ q ≤ 2 * (m + 1) from ⟨hq'.2, by omega, by omega⟩)

def deterministicOutput {N : ℕ} (K : ℕ) (w : Fin N → Fin N → ℚ)
    (hw : ∀ u v, w u v = w v u) : ScaledGraph :=
  let p := searchPrime (K * (N + 1) ^ 2)
  haveI : Fact p.Prime := ⟨(searchPrime_spec _).1⟩
  blowupOutput (p := p) w hw

theorem selected_prime_error (N K : ℕ) (hK : 0 < K) :
    let p := searchPrime (K * (N + 1) ^ 2)
    (N : ℝ) * ((N : ℝ) - 1) * (1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) ≤ 2 / (K : ℝ) := by
  dsimp only
  let p := searchPrime (K * (N + 1) ^ 2)
  have hp : 0 < (p : ℝ) := by exact_mod_cast (searchPrime_spec _).1.pos
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast (searchPrime_spec _).1.one_lt.le
  have hK' : 0 < (K : ℝ) := by exact_mod_cast hK
  have hN : 0 ≤ (N : ℝ) := by positivity
  have hlarge : (K : ℝ) * ((N : ℝ) + 1) ^ 2 ≤ (p : ℝ) := by
    exact_mod_cast (searchPrime_spec (K * (N + 1) ^ 2)).2.1.le
  have hpair : 0 ≤ (N : ℝ) * ((N : ℝ) - 1) := by
    rw [← twice_pair_count]
    apply sum_nonneg
    intro u hu
    apply sum_nonneg
    intro v hv
    split_ifs <;> norm_num
  have hr : 1 / (p : ℝ) + 1 / (p : ℝ) ^ 2 ≤ 2 / (p : ℝ) := by
    have hh := one_div_le_one_div_of_le hp (show (p : ℝ) ≤ (p : ℝ) ^ 2 by nlinarith)
    calc
      _ ≤ 1 / (p : ℝ) + 1 / (p : ℝ) := add_le_add (le_refl _) hh
      _ = 2 / (p : ℝ) := by ring
  calc
    _ ≤ (N : ℝ) * ((N : ℝ) - 1) * (2 / (p : ℝ)) := mul_le_mul_of_nonneg_left hr hpair
    _ ≤ ((N : ℝ) + 1) ^ 2 * (2 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ ≤ 2 / (K : ℝ) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hp hK').mpr
      nlinarith

theorem deterministicOutput_error {N : ℕ} (K : ℕ) (hK : 0 < K)
    (w : Fin N → Fin N → ℚ) (hw : ∀ u v, w u v = w v u)
    (hnonneg : ∀ u v, u < v → 0 ≤ w u v) (hscale : totalWeight w ≤ 1) :
    |((deterministicOutput K w hw).graph.maxCut : ℝ) / (deterministicOutput K w hw).scale -
      weightedMax (fun u v => (w u v : ℝ))| ≤ 2 / (K : ℝ) := by
  let p := searchPrime (K * (N + 1) ^ 2)
  have : Fact p.Prime := ⟨(searchPrime_spec _).1⟩
  have h := blowup_maxCut_error (p := p) w hw (normalized_pair_bound w hnonneg hscale)
  have he := h.trans (selected_prime_error N K hK)
  simpa only [deterministicOutput, blowupOutput, Nat.cast_pow] using he

/-- Explicit polynomial vertex bound for fixed K. It is a size bound, not
by itself a certificate of polynomial running time. -/
theorem deterministicOutput_vertex_bound {N : ℕ} (K : ℕ)
    (w : Fin N → Fin N → ℚ) (hw : ∀ u v, w u v = w v u) :
    (deterministicOutput K w hw).graph.vertices ≤ N * (2 * (K * (N + 1) ^ 2 + 1)) ^ 6 := by
  exact Nat.mul_le_mul_left N (Nat.pow_le_pow_left (searchPrime_spec _).2.2 6)

theorem deterministicOutput_scale_bound {N : ℕ} (K : ℕ)
    (w : Fin N → Fin N → ℚ) (hw : ∀ u v, w u v = w v u) :
    (deterministicOutput K w hw).scale ≤ (2 * (K * (N + 1) ^ 2 + 1)) ^ 12 := by
  exact Nat.pow_le_pow_left (searchPrime_spec _).2.2 12

theorem unweighted_finite_error (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ (N : ℕ) (w : Fin N → Fin N → ℚ)
      (hw : ∀ u v, w u v = w v u)
      (_hnonneg : ∀ u v, u < v → 0 ≤ w u v) (_hscale : totalWeight w ≤ 1),
      |((deterministicOutput K w hw).graph.maxCut : ℝ) / (deterministicOutput K w hw).scale -
        weightedMax (fun u v => (w u v : ℝ))| ≤ ε := by
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / ε)
  have hK' : 0 < (K : ℝ) := (div_pos (by norm_num) hε).trans hK
  have hKpos : 0 < K := by exact_mod_cast hK'
  have he : 2 / (K : ℝ) ≤ ε := by
    apply le_of_lt
    apply (div_lt_iff₀ hK').mpr
    have h := (div_lt_iff₀ hε).mp hK
    nlinarith
  refine ⟨K, hKpos, ?_⟩
  intro N w hw hnonneg hscale
  exact (deterministicOutput_error K hKpos w hw hnonneg hscale).trans he

end OptimalMaxCut.Unweighted

/-! Exact tree gate and slice symmetry. Sign values are encoded in ZMod 2:
b encodes (-1)^b. -/

end OAI
