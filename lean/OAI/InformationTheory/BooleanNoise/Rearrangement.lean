import OAI.InformationTheory.BooleanNoise.FiniteNoise
import OAI.InformationTheory.BooleanNoise.EntropyScalars
import Mathlib.Tactic

namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

def setBit (i : Fin n) (b : Bool) (x : Cube n) : Cube n := Function.update x i b

@[simp] theorem setBit_apply_same (i : Fin n) (b : Bool) (x : Cube n) :
    setBit i b x i = b := Function.update_self _ _ _

@[simp] theorem setBit_self (i : Fin n) (x : Cube n) : setBit i (x i) x = x :=
  Function.update_eq_self _ _

@[simp] theorem setBit_setBit (i : Fin n) (a b : Bool) (x : Cube n) :
    setBit i b (setBit i a x) = setBit i b x := Function.update_idem _ _ _

theorem setBit_comm {i j : Fin n} (hij : i ≠ j) (a b : Bool) (x : Cube n) :
    setBit j b (setBit i a x) = setBit i a (setBit j b x) :=
  by
    change Function.update (Function.update x i a) j b =
      Function.update (Function.update x j b) i a
    exact Function.update_comm hij a b x

def IsIncreasingIn (i : Fin n) (F : Cube n → ℝ) : Prop :=
  ∀ x, F (setBit i false x) ≤ F (setBit i true x)

def sortCoordinate (i : Fin n) (F : Cube n → ℝ) (x : Cube n) : ℝ :=
  if x i then max (F (setBit i false x)) (F (setBit i true x))
  else min (F (setBit i false x)) (F (setBit i true x))

@[simp] theorem sortCoordinate_false (i : Fin n) (F : Cube n → ℝ) (x : Cube n) :
    sortCoordinate i F (setBit i false x) =
      min (F (setBit i false x)) (F (setBit i true x)) := by
  simp [sortCoordinate]

@[simp] theorem sortCoordinate_true (i : Fin n) (F : Cube n → ℝ) (x : Cube n) :
    sortCoordinate i F (setBit i true x) =
      max (F (setBit i false x)) (F (setBit i true x)) := by
  simp [sortCoordinate]

theorem sortCoordinate_signValued (i : Fin n) {F : Cube n → ℝ}
    (hF : IsSignValued F) : IsSignValued (sortCoordinate i F) := by
  intro x
  rcases hF (setBit i false x) with h0 | h0 <;>
    rcases hF (setBit i true x) with h1 | h1 <;>
    cases hx : x i <;> simp [sortCoordinate, hx, h0, h1]

theorem sortCoordinate_increasingIn (i : Fin n) (F : Cube n → ℝ) :
    IsIncreasingIn i (sortCoordinate i F) := by
  intro x
  simp only [sortCoordinate_false, sortCoordinate_true]
  exact min_le_max

theorem sortCoordinate_preserves_increasingIn (i j : Fin n) {F : Cube n → ℝ}
    (hF : IsIncreasingIn j F) : IsIncreasingIn j (sortCoordinate i F) := by
  by_cases hij : i = j
  · subst j
    exact sortCoordinate_increasingIn i F
  · intro x
    have h0 := hF (setBit i false x)
    have h1 := hF (setBit i true x)
    simp only [sortCoordinate, setBit, Function.update_of_ne hij,
      Function.update_comm (Ne.symm hij)]
    cases hx : x i <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact min_le_min h0 h1
    · exact max_le_max h0 h1

theorem increasingIn_setBit_mono {F : Cube n → ℝ} {i : Fin n}
    (hF : IsIncreasingIn i F) (x : Cube n) (a b : Bool) (hab : a ≤ b) :
    F (setBit i a x) ≤ F (setBit i b x) := by
  cases a <;> cases b
  · exact le_rfl
  · exact hF x
  · exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) hab)
  · exact le_rfl

theorem isIncreasing_of_forall_increasingIn {F : Cube n → ℝ}
    (hF : ∀ i, IsIncreasingIn i F) : IsIncreasing F := by
  intro x y hxy
  let fill (s : Finset (Fin n)) : Cube n := fun i => if i ∈ s then y i else x i
  have hfill : ∀ s : Finset (Fin n), F x ≤ F (fill s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [fill]
    | @insert i s hi ih =>
      have hstep : F (fill s) ≤ F (setBit i (y i) (fill s)) := by
        have horder : fill s i ≤ y i := by simp [fill, hi, hxy i]
        simpa only [setBit_self] using
          increasingIn_setBit_mono (hF i) (fill s) (fill s i) (y i) horder
      have heq : setBit i (y i) (fill s) = fill (insert i s) := by
        funext j
        by_cases hji : j = i
        · subst j; simp [fill]
        · simp [setBit, fill, hji]
      exact ih.trans (heq ▸ hstep)
  simpa [fill] using hfill Finset.univ

theorem isIncreasing_increasingIn {F : Cube n → ℝ} (hF : IsIncreasing F)
    (i : Fin n) : IsIncreasingIn i F := by
  intro x
  apply hF
  intro j
  by_cases hji : j = i
  · subst j; simp
  · simp [setBit, Function.update_of_ne hji]

theorem pair_sum_setBit (i : Fin n) (F : Cube n → ℝ) (x : Cube n) :
    F (setBit i false x) + F (setBit i true x) = F x + F (flip i x) := by
  have hself := setBit_self i x
  cases hx : x i
  · simpa [setBit, flip, LeanBlast.GotsmanLinial.flip, hx] using
      congrArg (fun z => F z + F (setBit i true x)) hself
  · simpa [setBit, flip, LeanBlast.GotsmanLinial.flip, hx, add_comm] using
      congrArg (fun z => F (setBit i false x) + F z) hself

theorem sum_comp_flip (i : Fin n) (F : Cube n → ℝ) :
    (∑ x, F (flip i x)) = ∑ x, F x := by
  exact Fintype.sum_bijective (flip i) (LeanBlast.GotsmanLinial.flip_bijective i) _ _
    (fun _ => rfl)

theorem sum_setBit_pair (i : Fin n) (F : Cube n → ℝ) :
    (∑ x, (F (setBit i false x) + F (setBit i true x))) = 2 * ∑ x, F x := by
  simp_rw [pair_sum_setBit]
  rw [Finset.sum_add_distrib, sum_comp_flip]
  ring

theorem cubeAverage_sortCoordinate (i : Fin n) (F : Cube n → ℝ) :
    cubeAverage (sortCoordinate i F) = cubeAverage F := by
  have h : (∑ x, (sortCoordinate i F (setBit i false x) +
      sortCoordinate i F (setBit i true x))) =
      ∑ x, (F (setBit i false x) + F (setBit i true x)) := by
    simp only [sortCoordinate_false, sortCoordinate_true, min_add_max]
  rw [sum_setBit_pair, sum_setBit_pair] at h
  have hs : (∑ x, sortCoordinate i F x) = ∑ x, F x := by linarith
  exact congrArg (fun z : ℝ => z / (2 : ℝ) ^ n) hs

def coordinatePairMean (i : Fin n) (F : Cube n → ℝ) (x : Cube n) : ℝ :=
  (F (setBit i false x) + F (setBit i true x)) / 2

def coordinatePairDifference (i : Fin n) (F : Cube n → ℝ) (x : Cube n) : ℝ :=
  (F (setBit i true x) - F (setBit i false x)) / 2

def coordinateOffKernel (i : Fin n) (u : ℝ) (x y : Cube n) : ℝ :=
  ∏ j ∈ Finset.univ.erase i,
    if x j = y j then (1 + u) / 2 else (1 - u) / 2

def coordinateOffNoise (i : Fin n) (u : ℝ) (F : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ y, coordinateOffKernel i u x y / 2 * F y

theorem coordinateOffKernel_setBit_left (i : Fin n) (u : ℝ) (x y : Cube n) (b : Bool) :
    coordinateOffKernel i u (setBit i b x) y = coordinateOffKernel i u x y := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [setBit, Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem coordinateOffKernel_setBit_right (i : Fin n) (u : ℝ) (x y : Cube n) (b : Bool) :
    coordinateOffKernel i u x (setBit i b y) = coordinateOffKernel i u x y := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [setBit, Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem noiseKernel_setBit_pair (i : Fin n) (u : ℝ) (x y : Cube n) (a b : Bool) :
    noiseKernel u (setBit i a x) (setBit i b y) =
      (if a = b then (1 + u) / 2 else (1 - u) / 2) * coordinateOffKernel i u x y := by
  rw [noiseKernel_split_coord _ _ _ i]
  simp only [setBit_apply_same]
  change (if a = b then _ else _) *
    coordinateOffKernel i u (setBit i a x) (setBit i b y) = _
  rw [coordinateOffKernel_setBit_left, coordinateOffKernel_setBit_right]

theorem coordinateOffKernel_nonneg (i : Fin n) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (x y : Cube n) : 0 ≤ coordinateOffKernel i u x y := by
  apply Finset.prod_nonneg
  intro j _
  split_ifs <;> linarith [hu.1, hu.2]

theorem coordinateOffNoise_add (i : Fin n) (u : ℝ) (F G : Cube n → ℝ) (x : Cube n) :
    coordinateOffNoise i u (fun y => F y + G y) x =
      coordinateOffNoise i u F x + coordinateOffNoise i u G x := by
  simp only [coordinateOffNoise, mul_add, Finset.sum_add_distrib]

theorem coordinateOffNoise_smul (i : Fin n) (u c : ℝ) (F : Cube n → ℝ) (x : Cube n) :
    coordinateOffNoise i u (fun y => c * F y) x = c * coordinateOffNoise i u F x := by
  simp only [coordinateOffNoise, Finset.mul_sum, mul_left_comm]

theorem coordinateOffNoise_mono (i : Fin n) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    {F G : Cube n → ℝ} (hFG : ∀ y, F y ≤ G y) (x : Cube n) :
    coordinateOffNoise i u F x ≤ coordinateOffNoise i u G x := by
  exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hFG y)
    (div_nonneg (coordinateOffKernel_nonneg i hu x y) (by norm_num))

theorem coordinateOffNoise_nonneg (i : Fin n) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    {F : Cube n → ℝ} (hF : ∀ y, 0 ≤ F y) (x : Cube n) :
    0 ≤ coordinateOffNoise i u F x := by
  exact Finset.sum_nonneg fun y _ =>
    mul_nonneg (div_nonneg (coordinateOffKernel_nonneg i hu x y) (by norm_num)) (hF y)

theorem coordinateOffNoise_abs_bound (i : Fin n) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (F : Cube n → ℝ) (x : Cube n) :
    -coordinateOffNoise i u (fun y => |F y|) x ≤ coordinateOffNoise i u F x ∧
      coordinateOffNoise i u F x ≤ coordinateOffNoise i u (fun y => |F y|) x := by
  constructor
  · have h := coordinateOffNoise_mono i hu (fun y => neg_abs_le (F y)) x
    have heq : coordinateOffNoise i u (fun y => -|F y|) x =
        -coordinateOffNoise i u (fun y => |F y|) x := by
      simp [coordinateOffNoise]
    rw [heq] at h
    exact h
  · exact coordinateOffNoise_mono i hu (fun y => le_abs_self (F y)) x

theorem noiseOperator_setBit (i : Fin n) (u : ℝ) (F : Cube n → ℝ)
    (x : Cube n) (b : Bool) :
    noiseOperator u F (setBit i b x) =
      coordinateOffNoise i u (coordinatePairMean i F) x +
        (if b then u else -u) * coordinateOffNoise i u (coordinatePairDifference i F) x := by
  have h := sum_setBit_pair i (fun y => noiseKernel u (setBit i b x) y * F y)
  change _ = 2 * noiseOperator u F (setBit i b x) at h
  have heq : (∑ y, (noiseKernel u (setBit i b x) (setBit i false y) * F (setBit i false y) +
      noiseKernel u (setBit i b x) (setBit i true y) * F (setBit i true y))) =
      2 * coordinateOffNoise i u (fun y => coordinatePairMean i F y +
        (if b then u else -u) * coordinatePairDifference i F y) x := by
    rw [coordinateOffNoise, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [noiseKernel_setBit_pair, noiseKernel_setBit_pair]
    cases b <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
      coordinatePairMean, coordinatePairDifference] <;> ring
  rw [heq, coordinateOffNoise_add, coordinateOffNoise_smul] at h
  linarith

@[simp] theorem coordinatePairMean_sortCoordinate (i : Fin n) (F : Cube n → ℝ) :
    coordinatePairMean i (sortCoordinate i F) = coordinatePairMean i F := by
  funext x
  simp only [coordinatePairMean, sortCoordinate_false, sortCoordinate_true, min_add_max]

@[simp] theorem coordinatePairDifference_sortCoordinate (i : Fin n) (F : Cube n → ℝ) :
    coordinatePairDifference i (sortCoordinate i F) =
      fun x => |coordinatePairDifference i F x| := by
  funext x
  simp only [coordinatePairDifference, sortCoordinate_false, sortCoordinate_true]
  rcases le_total (F (setBit i false x)) (F (setBit i true x)) with h | h
  · rw [min_eq_left h, max_eq_right h, abs_of_nonneg (div_nonneg (sub_nonneg.mpr h) (by norm_num))]
  · rw [min_eq_right h, max_eq_left h, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr h) (by norm_num))]
    ring

theorem isIncreasing_noiseOperator {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    {F : Cube n → ℝ} (hF : IsIncreasing F) : IsIncreasing (noiseOperator u F) := by
  apply isIncreasing_of_forall_increasingIn
  intro i x
  rw [noiseOperator_setBit, noiseOperator_setBit]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hb : 0 ≤ coordinateOffNoise i u (coordinatePairDifference i F) x := by
    apply coordinateOffNoise_nonneg i hu
    intro y
    exact div_nonneg (sub_nonneg.mpr (isIncreasing_increasingIn hF i y)) (by norm_num)
  nlinarith [mul_nonneg hu.1 hb]

theorem psi_symmetric_pair_mono (a b c : ℝ) (hc : 0 ≤ c)
    (hb : -c ≤ b ∧ b ≤ c)
    (hminus : a - c ∈ Set.Icc (-1 : ℝ) 1)
    (hplus : a + c ∈ Set.Icc (-1 : ℝ) 1) :
    psi (a + b) + psi (a - b) ≤ psi (a + c) + psi (a - c) := by
  by_cases hcz : c = 0
  · have hbz : b = 0 := by rcases hb with ⟨hl, hu⟩; simp only [hcz, neg_zero] at hl hu; linarith
    simp [hcz, hbz]
  · have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hcz)
    let t : ℝ := (c + b) / (2 * c)
    let s : ℝ := (c - b) / (2 * c)
    have ht : 0 ≤ t := div_nonneg (by linarith [hb.1]) (by positivity)
    have hs : 0 ≤ s := div_nonneg (by linarith [hb.2]) (by positivity)
    have hts : t + s = 1 := by dsimp [t, s]; field_simp; ring
    have hst : s + t = 1 := by linarith
    have hr1 : t * (a + c) + s * (a - c) = a + b := by
      dsimp [t, s]; field_simp; ring
    have hr2 : s * (a + c) + t * (a - c) = a - b := by
      dsimp [t, s]; field_simp; ring
    have h1 := convexOn_psi.2 hplus hminus ht hs hts
    have h2 := convexOn_psi.2 hplus hminus hs ht hst
    simp only [smul_eq_mul, hr1] at h1
    simp only [smul_eq_mul, hr2] at h2
    calc
      psi (a + b) + psi (a - b) ≤
          (t * psi (a + c) + s * psi (a - c)) +
          (s * psi (a + c) + t * psi (a - c)) := add_le_add h1 h2
      _ = (t + s) * (psi (a + c) + psi (a - c)) := by ring
      _ = psi (a + c) + psi (a - c) := by rw [hts, one_mul]

private theorem rearrangement_sign_bounds {F : Cube n → ℝ} (hF : IsSignValued F) :
    ∀ y, -1 ≤ F y ∧ F y ≤ 1 := by
  intro y
  rcases hF y with h | h <;> rw [h] <;> norm_num

theorem psi_noise_sortCoordinate_pair (i : Fin n) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) {F : Cube n → ℝ} (hF : IsSignValued F) (x : Cube n) :
    psi (noiseOperator u F (setBit i false x)) +
        psi (noiseOperator u F (setBit i true x)) ≤
      psi (noiseOperator u (sortCoordinate i F) (setBit i false x)) +
        psi (noiseOperator u (sortCoordinate i F) (setBit i true x)) := by
  let A := coordinateOffNoise i u (coordinatePairMean i F) x
  let B := u * coordinateOffNoise i u (coordinatePairDifference i F) x
  let C := u * coordinateOffNoise i u (fun y => |coordinatePairDifference i F y|) x
  have hc : 0 ≤ C := mul_nonneg hu.1
    (coordinateOffNoise_nonneg i hu (fun y => abs_nonneg _) x)
  have hbound := coordinateOffNoise_abs_bound i hu (coordinatePairDifference i F) x
  have hb : -C ≤ B ∧ B ≤ C := by
    dsimp only [B, C]
    constructor
    · have h := mul_le_mul_of_nonneg_left hbound.1 hu.1
      nlinarith
    · exact mul_le_mul_of_nonneg_left hbound.2 hu.1
  have hfminus : noiseOperator u F (setBit i false x) = A - B := by
    rw [noiseOperator_setBit]
    dsimp [A, B]
    ring
  have hfplus : noiseOperator u F (setBit i true x) = A + B := by
    rw [noiseOperator_setBit]
    rfl
  have hsminus : noiseOperator u (sortCoordinate i F) (setBit i false x) = A - C := by
    rw [noiseOperator_setBit, coordinatePairMean_sortCoordinate, coordinatePairDifference_sortCoordinate]
    dsimp [A, C]
    ring
  have hsplus : noiseOperator u (sortCoordinate i F) (setBit i true x) = A + C := by
    rw [noiseOperator_setBit, coordinatePairMean_sortCoordinate, coordinatePairDifference_sortCoordinate]
    rfl
  have hsort := rearrangement_sign_bounds (sortCoordinate_signValued i hF)
  have hminus : A - C ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [← hsminus]
    exact noiseOperator_bounds hu.1 hu.2 hsort _
  have hplus : A + C ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [← hsplus]
    exact noiseOperator_bounds hu.1 hu.2 hsort _
  rw [hfminus, hfplus, hsminus, hsplus]
  simpa only [add_comm] using psi_symmetric_pair_mono A B C hc hb hminus hplus

theorem cubeAverage_psi_noise_sortCoordinate (i : Fin n) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) {F : Cube n → ℝ} (hF : IsSignValued F) :
    cubeAverage (fun x => psi (noiseOperator u F x)) ≤
      cubeAverage (fun x => psi (noiseOperator u (sortCoordinate i F) x)) := by
  have h := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Cube n))) =>
    psi_noise_sortCoordinate_pair i hu hF x)
  rw [sum_setBit_pair i (fun x => psi (noiseOperator u F x)),
    sum_setBit_pair i (fun x => psi (noiseOperator u (sortCoordinate i F) x))] at h
  have hs : (∑ x, psi (noiseOperator u F x)) ≤
      ∑ x, psi (noiseOperator u (sortCoordinate i F) x) := by linarith
  exact div_le_div_of_nonneg_right hs (cube_denominator_pos n).le

theorem informationDeficit_eq_psi_difference (F : Cube n → ℝ) :
    informationDeficit F = cubeAverage (fun x => psi (F x)) - psi (cubeAverage F) := by
  unfold informationDeficit entropyAverage entropy
  rw [cubeAverage_sub, cubeAverage_const]
  ring

theorem informationDeficit_noise_sortCoordinate (i : Fin n) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) {F : Cube n → ℝ} (hF : IsSignValued F) :
    informationDeficit (noiseOperator u F) ≤
      informationDeficit (noiseOperator u (sortCoordinate i F)) := by
  rw [informationDeficit_eq_psi_difference, informationDeficit_eq_psi_difference,
    cubeAverage_noiseOperator, cubeAverage_noiseOperator, cubeAverage_sortCoordinate]
  exact sub_le_sub_right (cubeAverage_psi_noise_sortCoordinate i hu hF) _

def sortCoordinates : List (Fin n) → (Cube n → ℝ) → Cube n → ℝ
  | [], F => F
  | i :: is, F => sortCoordinates is (sortCoordinate i F)

theorem sortCoordinates_signValued (is : List (Fin n)) {F : Cube n → ℝ}
    (hF : IsSignValued F) : IsSignValued (sortCoordinates is F) := by
  induction is generalizing F with
  | nil => exact hF
  | cons i is ih => exact ih (sortCoordinate_signValued i hF)

theorem cubeAverage_sortCoordinates (is : List (Fin n)) (F : Cube n → ℝ) :
    cubeAverage (sortCoordinates is F) = cubeAverage F := by
  induction is generalizing F with
  | nil => rfl
  | cons i is ih => rw [sortCoordinates, ih, cubeAverage_sortCoordinate]

theorem sortCoordinates_increasingIn (is : List (Fin n)) {F : Cube n → ℝ}
    (j : Fin n) (hj : j ∈ is ∨ IsIncreasingIn j F) :
    IsIncreasingIn j (sortCoordinates is F) := by
  induction is generalizing F with
  | nil => exact hj.resolve_left (by simp)
  | cons i is ih =>
      apply ih
      rcases hj with hmem | hinc
      · rcases List.mem_cons.mp hmem with hji | hmem
        · subst j
          exact Or.inr (sortCoordinate_increasingIn i F)
        · exact Or.inl hmem
      · exact Or.inr (sortCoordinate_preserves_increasingIn i j hinc)

theorem informationDeficit_noise_sortCoordinates (is : List (Fin n)) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) {F : Cube n → ℝ} (hF : IsSignValued F) :
    informationDeficit (noiseOperator u F) ≤
      informationDeficit (noiseOperator u (sortCoordinates is F)) := by
  induction is generalizing F with
  | nil => exact le_rfl
  | cons i is ih =>
      exact (informationDeficit_noise_sortCoordinate i hu hF).trans
        (ih (sortCoordinate_signValued i hF))

theorem exists_increasing_informationDeficit_ge (u : ℝ) (hu : u ∈ Set.Icc 0 1)
    (F : Cube n → ℝ) (hF : IsSignValued F) :
    ∃ G : Cube n → ℝ, IsSignValued G ∧ IsIncreasing G ∧
      cubeAverage G = cubeAverage F ∧
      informationDeficit (noiseOperator u F) ≤ informationDeficit (noiseOperator u G) := by
  classical
  let is : List (Fin n) := Finset.univ.toList
  refine ⟨sortCoordinates is F, sortCoordinates_signValued is hF, ?_,
    cubeAverage_sortCoordinates is F, informationDeficit_noise_sortCoordinates is hu hF⟩
  apply isIncreasing_of_forall_increasingIn
  intro j
  apply sortCoordinates_increasingIn is j
  exact Or.inl (by simp [is])

end LeanBlast.CourtadeKumar

end

end OAI
