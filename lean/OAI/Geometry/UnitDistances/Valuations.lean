import OAI.Geometry.UnitDistances.Radicals

namespace OAI

namespace PlanarUnitDistances.Radicals

universe u v

open WithZero Multiplicative

theorem exp_neg_one_ne_square (x : ℤᵐ⁰) : WithZero.exp (-1 : ℤ) ≠ x ^ 2 := by
  intro h
  have h' := congrArg WithZero.log h
  simp only [WithZero.log_exp, WithZero.log_pow, nsmul_eq_mul] at h'
  omega

theorem squareIndependent_of_private_valuations
    {K : Type u} [Field K] {ι : Type v} (is : List ι) (hi : is.Nodup)
    (d : ι → K)
    (hv : ∀ i ∈ is, ∃ v : Valuation K ℤᵐ⁰,
      v (d i) = WithZero.exp (-1 : ℤ) ∧ ∀ j ∈ is, j ≠ i → v (d j) = 1) :
    SquareIndependent (is.map d) := by
  intro s hs hsn c hc
  obtain ⟨js, hj, rfl⟩ := List.sublist_map_iff.mp hs
  cases js with
  | nil => exact hsn rfl
  | cons i js =>
    have hnd := List.nodup_cons.mp (hi.sublist hj)
    have him : i ∈ is := hj.subset (by simp)
    obtain ⟨v, hvi, hvj⟩ := hv i him
    have hone : (js.map (fun j => v (d j))).prod = 1 := by
      apply List.prod_eq_one
      intro a ha
      obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp ha
      exact hvj j (hj.subset (by simp [hjm])) (by
        intro he; exact hnd.1 (he ▸ hjm))
    apply exp_neg_one_ne_square (v c)
    have hh := congrArg v hc
    simpa [map_list_prod, List.map_map, Function.comp_def, hvi, hone] using hh

section RootValuation

open Polynomial IsDedekindDomain

variable {K : Type u} [Field K]

noncomputable def pointPrime (a : K) : HeightOneSpectrum K[X] where
  asIdeal := Ideal.span {X - C a}
  isPrime := by
    rw [Ideal.span_singleton_prime (X_sub_C_ne_zero a)]
    exact prime_X_sub_C a
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact X_sub_C_ne_zero a

noncomputable def pointValuation (a : K) : Valuation (RatFunc K) ℤᵐ⁰ :=
  (pointPrime a).valuation (RatFunc K)

theorem pointValuation_polynomial_of_eval_ne_zero {a : K} {p : K[X]}
    (hp : p.eval a ≠ 0) :
    pointValuation a (algebraMap K[X] (RatFunc K) p) = 1 := by
  apply (HeightOneSpectrum.valuation_eq_one_iff_notMem (pointPrime a)).mpr
  simpa [pointPrime, Ideal.mem_span_singleton, dvd_iff_isRoot, IsRoot] using hp

theorem pointValuation_X_sub_C (a : K) :
    pointValuation a (algebraMap K[X] (RatFunc K) (X - C a)) =
      WithZero.exp (-1 : ℤ) := by
  rw [pointValuation, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton (pointPrime a) (X_sub_C_ne_zero a) rfl

theorem pointValuation_of_simple_root {a : K} {p : K[X]}
    (hp : p.eval a = 0) (hp' : p.derivative.eval a ≠ 0) :
    pointValuation a (algebraMap K[X] (RatFunc K) p) =
      WithZero.exp (-1 : ℤ) := by
  obtain ⟨q, hq⟩ := (dvd_iff_isRoot.mpr hp : X - C a ∣ p)
  have hq' : q.eval a ≠ 0 := by
    simpa [hq, derivative_mul] using hp'
  rw [hq, map_mul, map_mul, pointValuation_X_sub_C,
    pointValuation_polynomial_of_eval_ne_zero hq', mul_one]

theorem squareIndependent_of_private_simple_roots {ι : Type v}
    (is : List ι) (hi : is.Nodup) (d : ι → K[X])
    (h : ∀ i ∈ is, ∃ a : K, (d i).eval a = 0 ∧
      (d i).derivative.eval a ≠ 0 ∧ ∀ j ∈ is, j ≠ i → (d j).eval a ≠ 0) :
    SquareIndependent (is.map (fun i => algebraMap K[X] (RatFunc K) (d i))) := by
  apply squareIndependent_of_private_valuations is hi
  intro i him
  obtain ⟨a, hai, hai', haj⟩ := h i him
  exact ⟨pointValuation a, pointValuation_of_simple_root hai hai',
    fun j hj hji => pointValuation_polynomial_of_eval_ne_zero (haj j hj hji)⟩

end RootValuation

section Plane

open Polynomial

variable {K : Type u} [Field K] [CharZero K]

omit [CharZero K] in
lemma ratFunc_X_sub_C_ne_zero (a : K) :
    (RatFunc.X : RatFunc K) - RatFunc.C a ≠ 0 := by
  simpa using RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a)

noncomputable def planePrivateRoot (a b : K) : RatFunc K :=
  (RatFunc.C b * (RatFunc.X - RatFunc.C a) + 4) /
    (RatFunc.X - RatFunc.C a)

lemma planePrivateRoot_ne_constant (a b c : K) :
    planePrivateRoot a b ≠ RatFunc.C c := by
  intro h
  have he := (div_eq_iff (ratFunc_X_sub_C_ne_zero a)).mp h
  have hp : C b * (X - C a) + 4 = C c * (X - C a) := by
    apply RatFunc.algebraMap_injective K
    simpa only [map_mul, map_sub, map_add, map_ofNat, RatFunc.algebraMap_C,
      RatFunc.algebraMap_X] using he
  have hp' := congrArg (Polynomial.eval a) hp
  norm_num at hp'

lemma planePrivateRoot_injective :
    Function.Injective (fun ab : K × K => planePrivateRoot ab.1 ab.2) := by
  intro ab cd he
  change planePrivateRoot ab.1 ab.2 = planePrivateRoot cd.1 cd.2 at he
  have hc := (div_eq_div_iff (ratFunc_X_sub_C_ne_zero ab.1)
    (ratFunc_X_sub_C_ne_zero cd.1)).mp he
  have hp : (C ab.2 * (X - C ab.1) + 4) * (X - C cd.1) =
      (C cd.2 * (X - C cd.1) + 4) * (X - C ab.1) := by
    apply RatFunc.algebraMap_injective K
    simpa only [map_mul, map_sub, map_add, map_ofNat, RatFunc.algebraMap_C,
      RatFunc.algebraMap_X] using hc
  have hp' := congrArg (Polynomial.eval ab.1) hp
  simp only [eval_mul, eval_add, eval_sub, eval_C, eval_X, eval_ofNat,
    sub_self, mul_zero, zero_add] at hp'
  have ha : ab.1 = cd.1 := by
    have h4 : (4 : K) ≠ 0 := by norm_num
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp').resolve_left h4)
  have hb : ab.2 = cd.2 := by
    unfold planePrivateRoot at he
    rw [ha] at he
    have hh := (div_left_inj' (ratFunc_X_sub_C_ne_zero cd.1)).mp he
    exact RatFunc.C_injective (mul_right_cancel₀ (ratFunc_X_sub_C_ne_zero cd.1)
      (add_right_cancel hh))
  exact Prod.ext ha hb

noncomputable def planeDistancePoly (a b : K) : (RatFunc K)[X] :=
  C (RatFunc.X - RatFunc.C a) * (X - C (RatFunc.C b))

noncomputable def planeRadicandPoly (a b : K) : (RatFunc K)[X] :=
  planeDistancePoly a b * (planeDistancePoly a b - 4)

omit [CharZero K] in
lemma planePrivateRoot_distance (a b : K) :
    (planeDistancePoly a b).eval (planePrivateRoot a b) = 4 := by
  simp only [planeDistancePoly, eval_mul, eval_C, eval_sub, eval_X, planePrivateRoot]
  field_simp [ratFunc_X_sub_C_ne_zero a]
  ring

lemma planePrivateRoot_simple (a b : K) :
    (planeRadicandPoly a b).eval (planePrivateRoot a b) = 0 ∧
    (planeRadicandPoly a b).derivative.eval (planePrivateRoot a b) ≠ 0 := by
  constructor
  · simp [planeRadicandPoly, planePrivateRoot_distance]
  · have h4 : (4 : RatFunc K) ≠ 0 := by norm_num
    have hd : (planeDistancePoly a b).derivative = C (RatFunc.X - RatFunc.C a) := by
      simp [planeDistancePoly]
    simpa [planeRadicandPoly, derivative_mul, derivative_sub,
      planePrivateRoot_distance, hd] using
      mul_ne_zero h4 (ratFunc_X_sub_C_ne_zero a)

lemma planePrivateRoot_other (ab cd : K × K) (h : cd ≠ ab) :
    (planeRadicandPoly cd.1 cd.2).eval (planePrivateRoot ab.1 ab.2) ≠ 0 := by
  simp only [planeRadicandPoly, eval_mul, eval_sub, eval_ofNat, mul_ne_zero_iff]
  constructor
  · simp only [planeDistancePoly, eval_mul, eval_C, eval_sub, eval_X, mul_ne_zero_iff]
    exact ⟨ratFunc_X_sub_C_ne_zero cd.1,
      sub_ne_zero.mpr (planePrivateRoot_ne_constant ab.1 ab.2 cd.2)⟩
  · intro he
    have hd := sub_eq_zero.mp he
    have hroot : planePrivateRoot ab.1 ab.2 = planePrivateRoot cd.1 cd.2 := by
      apply (eq_div_iff (ratFunc_X_sub_C_ne_zero cd.1)).mpr
      simp only [planeDistancePoly, eval_mul, eval_C, eval_sub, eval_X] at hd
      linear_combination hd
    exact h (planePrivateRoot_injective hroot).symm

theorem plane_radicands_squareIndependent (centers : List (K × K))
    (h : centers.Nodup) :
    SquareIndependent (centers.map (fun ab =>
      algebraMap (RatFunc K)[X] (RatFunc (RatFunc K))
        (planeRadicandPoly ab.1 ab.2))) := by
  apply squareIndependent_of_private_simple_roots centers h
  intro ab hab
  exact ⟨planePrivateRoot ab.1 ab.2, (planePrivateRoot_simple ab.1 ab.2).1,
    (planePrivateRoot_simple ab.1 ab.2).2,
    fun cd _ hcd => planePrivateRoot_other ab cd hcd⟩

end Plane

section GenericLine

open Polynomial

variable {B : Type u} {K : Type v} [Field B] [Field K] [Algebra B K]
variable {ι : Type*} {a : ι → K}

lemma independent_difference_ne (ha : AlgebraicIndependent B a)
    {i j : ι} (hij : i ≠ j) (c : B) :
    a i - a j ≠ algebraMap B K c := by
  classical
  intro he
  have hp : (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial ι B) =
      MvPolynomial.C c := ha (by simpa using he)
  have h0 := congrArg (MvPolynomial.eval (fun _ : ι => (0 : B))) hp
  have h1 := congrArg (MvPolynomial.eval (fun k : ι => if k = i then (1 : B) else 0)) hp
  simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_self] at h0
  simp [hij.symm] at h1
  exact one_ne_zero (h1.trans h0.symm)

noncomputable def lineDistancePoly (e a : K) : K[X] := C e * (X - C a) ^ 2

noncomputable def lineRadicandPoly (e a : K) : K[X] :=
  lineDistancePoly e a * (lineDistancePoly e a - 4)

variable [CharZero B] [CharZero K]

lemma line_root_simple (e c a : K) (h : e * c ^ 2 = 4) :
    (lineRadicandPoly e a).eval (a + c) = 0 ∧
    (lineRadicandPoly e a).derivative.eval (a + c) ≠ 0 := by
  have he : e ≠ 0 := by intro he; simp [he] at h
  have hc : c ≠ 0 := by intro hc; simp [hc] at h
  have hL : (lineDistancePoly e a).eval (a + c) = 4 := by
    simpa [lineDistancePoly] using h
  have hL' : (lineDistancePoly e a).derivative.eval (a + c) = 2 * e * c := by
    simp [lineDistancePoly, derivative_mul, derivative_pow]
    ring
  constructor
  · simp [lineRadicandPoly, hL]
  · simpa [lineRadicandPoly, derivative_mul, derivative_sub, hL, hL'] using
      mul_ne_zero (by norm_num : (8 : K) ≠ 0) (mul_ne_zero he hc)

lemma line_root_other (ha : AlgebraicIndependent B a) (e c : B)
    (hec : e * c ^ 2 = 4) {i j : ι} (hji : j ≠ i) :
    (lineRadicandPoly (algebraMap B K e) (a j)).eval
      (a i + algebraMap B K c) ≠ 0 := by
  have he : e ≠ 0 := by intro he; simp [he] at hec
  have he' : algebraMap B K e ≠ 0 := (map_ne_zero (algebraMap B K)).mpr he
  have hec' : algebraMap B K e * (algebraMap B K c) ^ 2 = (4 : K) := by
    simpa only [map_mul, map_pow, map_ofNat] using congrArg (algebraMap B K) hec
  have hdiff : a i + algebraMap B K c - a j ≠ 0 := by
    intro hzero
    apply independent_difference_ne ha hji.symm (-c)
    rw [map_neg]
    linear_combination hzero
  have hL : (lineDistancePoly (algebraMap B K e) (a j)).eval
      (a i + algebraMap B K c) ≠ 0 := by
    simpa [lineDistancePoly] using mul_ne_zero he' (pow_ne_zero 2 hdiff)
  have hL4 : (lineDistancePoly (algebraMap B K e) (a j)).eval
      (a i + algebraMap B K c) ≠ 4 := by
    intro hh
    simp only [lineDistancePoly, eval_mul, eval_C, eval_pow, eval_sub, eval_X] at hh
    have hs : (a i + algebraMap B K c - a j) ^ 2 = (algebraMap B K c) ^ 2 :=
      mul_left_cancel₀ he' (hh.trans hec'.symm)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs | hs
    · apply independent_difference_ne ha hji.symm 0
      simp only [map_zero]
      linear_combination hs
    · apply independent_difference_ne ha hji.symm (-2 * c)
      simp only [map_mul, map_neg, map_ofNat]
      linear_combination hs
  simpa only [lineRadicandPoly, eval_mul, eval_sub, eval_ofNat, mul_ne_zero_iff,
    sub_ne_zero] using And.intro hL hL4

theorem line_radicands_squareIndependent [IsAlgClosed B]
    (e : B) (he : e ≠ 0) (anchors : List ι) (hind : anchors.Nodup)
    (ha : AlgebraicIndependent B a) :
    SquareIndependent (anchors.map (fun i =>
      algebraMap K[X] (RatFunc K) (lineRadicandPoly (algebraMap B K e) (a i)))) := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (4 / e) (n := 2) (by decide)
  have hce : e * c ^ 2 = 4 := by rw [hc]; field_simp
  have hce' : algebraMap B K e * (algebraMap B K c) ^ 2 = (4 : K) := by
    simpa only [map_mul, map_pow, map_ofNat] using congrArg (algebraMap B K) hce
  apply squareIndependent_of_private_simple_roots anchors hind
  intro i hi
  refine ⟨a i + algebraMap B K c,
    (line_root_simple _ _ _ hce').1, (line_root_simple _ _ _ hce').2, ?_⟩
  intro j hj hji
  exact line_root_other ha e c hce hji

theorem line_radicands_squareIndependent_over_constants [IsAlgClosed K]
    (e : B) (he : e ≠ 0) (anchors : List ι) (hind : anchors.Nodup)
    (ha : AlgebraicIndependent B a) :
    SquareIndependent (anchors.map (fun i =>
      algebraMap K[X] (RatFunc K) (lineRadicandPoly (algebraMap B K e) (a i)))) := by
  let E := algebraicClosure B K
  let : IsAlgClosed E := IsAlgClosure.isAlgClosed B
  have he' : algebraMap B E e ≠ 0 := (_root_.map_ne_zero _).mpr he
  have hh := line_radicands_squareIndependent (K := K) (algebraMap B E e) he'
    anchors hind ha.algebraicClosure
  have heq : algebraMap E K (algebraMap B E e) = algebraMap B K e := by
    exact (IsScalarTower.algebraMap_apply B E K e).symm
  rw [heq] at hh
  exact hh

end GenericLine

section GenericCircle

open Polynomial

variable {B : Type u} {K : Type v} [Field B] [Field K] [Algebra B K]
variable [CharZero B] [CharZero K]
variable {ι : Type*} {a : ι → K}

omit [CharZero K] in
lemma independent_affine_ne (ha : AlgebraicIndependent B a)
    {i j : ι} (hij : i ≠ j) (e c : B) :
    a j ≠ algebraMap B K e * a i + algebraMap B K c := by
  classical
  intro he
  have hp : (MvPolynomial.X j : MvPolynomial ι B) =
      MvPolynomial.C e * MvPolynomial.X i + MvPolynomial.C c := ha (by simpa using he)
  have h0 := congrArg (MvPolynomial.eval (fun _ : ι => (0 : B))) hp
  have h1 := congrArg (MvPolynomial.eval (fun k : ι => if k = j then (1 : B) else 0)) hp
  simp at h0
  simp [hij] at h1
  exact one_ne_zero (h1.trans h0.symm)

lemma circle_aux_root [IsAlgClosed B] (b : B) (hb : b ≠ 0) (hb1 : b ≠ 1) :
    ∃ q : B, q ≠ 0 ∧ b * q ^ 2 + (4 - 2 * b) * q + b = 0 ∧
      2 * b * q + 4 - 2 * b ≠ 0 := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (1 - b) (n := 2) (by decide)
  have hc0 : c ≠ 0 := by
    intro he
    apply hb1
    simp only [he, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hc
    exact (sub_eq_zero.mp hc.symm).symm
  let q := (b - 2 + 2 * c) / b
  have hq : b * q ^ 2 + (4 - 2 * b) * q + b = 0 := by
    dsimp [q]
    field_simp
    linear_combination 4 * hc
  have hq0 : q ≠ 0 := by
    intro he
    exact hb (by simpa [he] using hq)
  refine ⟨q, hq0, hq, ?_⟩
  have hd : 2 * b * q + 4 - 2 * b = 4 * c := by
    dsimp [q]
    field_simp
    ring
  rw [hd]
  exact mul_ne_zero (by norm_num) hc0

noncomputable def circleNumerator (b a : K) : K[X] := -C b * (X - C a) ^ 2
noncomputable def circleDenominator (u a : K) : K[X] := (X - C u) * C (a - u)
noncomputable def circleDifference (b u a : K) : K[X] :=
  circleNumerator b a - 4 * circleDenominator u a
noncomputable def circleRadicandNumerator (b u a : K) : K[X] :=
  circleNumerator b a * circleDifference b u a

noncomputable def circleDistance (b u a : K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (circleNumerator b a) /
    algebraMap K[X] (RatFunc K) (circleDenominator u a)
noncomputable def circleRadicand (b u a : K) : RatFunc K :=
  circleDistance b u a * (circleDistance b u a - 4)

omit [CharZero K] in
lemma circleRadicand_eq_fraction (b u a : K) :
    circleRadicand b u a =
      algebraMap K[X] (RatFunc K) (circleRadicandNumerator b u a) /
        algebraMap K[X] (RatFunc K) (circleDenominator u a) ^ 2 := by
  simp only [circleRadicand, circleDistance, circleRadicandNumerator,
    circleDifference, map_mul, map_sub, map_ofNat]
  by_cases h : algebraMap K[X] (RatFunc K) (circleDenominator u a) = 0
  · simp [h]
  · field_simp

lemma circle_root_simple (b u a q : K) (ha : a ≠ u) (hq0 : q ≠ 0)
    (hq : b * q ^ 2 + (4 - 2 * b) * q + b = 0)
    (hd : 2 * b * q + 4 - 2 * b ≠ 0) :
    let s := u + q * (a - u)
    (circleRadicandNumerator b u a).eval s = 0 ∧
    (circleRadicandNumerator b u a).derivative.eval s ≠ 0 ∧
    (circleDenominator u a).eval s ≠ 0 := by
  dsimp only
  let s := u + q * (a - u)
  have hden : (circleDenominator u a).eval s = q * (a - u) ^ 2 := by
    simp [circleDenominator, s]
    ring
  have hden0 : (circleDenominator u a).eval s ≠ 0 := by
    rw [hden]
    exact mul_ne_zero hq0 (pow_ne_zero 2 (sub_ne_zero.mpr ha))
  have hdiff : (circleDifference b u a).eval s = 0 := by
    simp only [circleDifference, circleNumerator, circleDenominator,
      eval_sub, eval_mul, eval_neg, eval_C, eval_pow, eval_X, eval_ofNat]
    dsimp [s]
    linear_combination -(a - u) ^ 2 * hq
  have hnum : (circleNumerator b a).eval s = 4 * (circleDenominator u a).eval s := by
    simpa only [circleDifference, eval_sub, eval_mul, eval_ofNat, sub_eq_zero] using hdiff
  have hnum0 : (circleNumerator b a).eval s ≠ 0 := by
    rw [hnum]
    exact mul_ne_zero (by norm_num) hden0
  have hdif : (circleDifference b u a).derivative.eval s =
      -(2 * b * q + 4 - 2 * b) * (a - u) := by
    simp [circleDifference, circleNumerator, circleDenominator, s,
      derivative_sub, derivative_mul, derivative_pow]
    ring
  change (circleRadicandNumerator b u a).eval s = 0 ∧
    (circleRadicandNumerator b u a).derivative.eval s ≠ 0 ∧
    (circleDenominator u a).eval s ≠ 0
  refine ⟨?_, ?_, hden0⟩
  · simp [circleRadicandNumerator, hdiff]
  · simpa only [circleRadicandNumerator, derivative_mul, eval_add, eval_mul,
      hdiff, mul_zero, zero_add, hdif] using
      mul_ne_zero hnum0 (mul_ne_zero (neg_ne_zero.mpr hd) (sub_ne_zero.mpr ha))

lemma circle_root_other (ha : AlgebraicIndependent B a)
    (b u q : B) (hb : b ≠ 0) (hq0 : q ≠ 0) {i j : ι} (hji : j ≠ i) :
    let s := algebraMap B K u + algebraMap B K q * (a i - algebraMap B K u)
    (circleRadicandNumerator (algebraMap B K b) (algebraMap B K u) (a j)).eval s ≠ 0 ∧
    (circleDenominator (algebraMap B K u) (a j)).eval s ≠ 0 := by
  classical
  dsimp only
  let s := algebraMap B K u + algebraMap B K q * (a i - algebraMap B K u)
  have hai : a i ≠ algebraMap B K u := by
    intro he
    exact ha.transcendental i (he ▸ isAlgebraic_algebraMap (R := B) u)
  have haj : a j ≠ algebraMap B K u := by
    intro he
    exact ha.transcendental j (he ▸ isAlgebraic_algebraMap (R := B) u)
  have hsu : s ≠ algebraMap B K u := by
    dsimp [s]
    simpa using mul_ne_zero ((_root_.map_ne_zero (algebraMap B K)).mpr hq0) (sub_ne_zero.mpr hai)
  have hsaj : s ≠ a j := by
    intro he
    apply independent_affine_ne ha hji.symm q (u - q * u)
    rw [map_sub, map_mul]
    dsimp [s] at he
    linear_combination -he
  have hnum : (circleNumerator (algebraMap B K b) (a j)).eval s ≠ 0 := by
    simpa only [circleNumerator, eval_mul, eval_neg, eval_C, eval_pow, eval_sub, eval_X] using
      mul_ne_zero (neg_ne_zero.mpr ((_root_.map_ne_zero (algebraMap B K)).mpr hb)) (pow_ne_zero 2 (sub_ne_zero.mpr hsaj))
  have hdiff : (circleDifference (algebraMap B K b) (algebraMap B K u) (a j)).eval s ≠ 0 := by
    intro he
    let S : MvPolynomial ι B := MvPolynomial.C u + MvPolynomial.C q *
      (MvPolynomial.X i - MvPolynomial.C u)
    have hp : -MvPolynomial.C b * (S - MvPolynomial.X j) ^ 2 -
        4 * (S - MvPolynomial.C u) * (MvPolynomial.X j - MvPolynomial.C u) =
        (0 : MvPolynomial ι B) := by
      apply ha
      simpa [S, circleDifference, circleNumerator, circleDenominator, s, mul_assoc] using he
    have htest := congrArg
      (MvPolynomial.eval (fun k : ι => if k = j then u + 1 else u)) hp
    have : -b = 0 := by simpa [S, hji, hji.symm] using htest
    exact hb (neg_eq_zero.mp this)
  constructor
  · simpa [circleRadicandNumerator] using mul_ne_zero hnum hdiff
  · change (circleDenominator (algebraMap B K u) (a j)).eval s ≠ 0
    simpa only [circleDenominator, eval_mul, eval_sub, eval_X, eval_C] using
      mul_ne_zero (sub_ne_zero.mpr hsu) (sub_ne_zero.mpr haj)

theorem circle_radicands_squareIndependent [IsAlgClosed B]
    (b u : B) (hb : b ≠ 0) (hb1 : b ≠ 1)
    (anchors : List ι) (hind : anchors.Nodup) (ha : AlgebraicIndependent B a) :
    SquareIndependent (anchors.map (fun i =>
      circleRadicand (algebraMap B K b) (algebraMap B K u) (a i))) := by
  obtain ⟨q, hq0, hq, hd⟩ := circle_aux_root b hb hb1
  have hq0' : algebraMap B K q ≠ 0 := (_root_.map_ne_zero _).mpr hq0
  have hq' : algebraMap B K b * (algebraMap B K q) ^ 2 +
      (4 - 2 * algebraMap B K b) * algebraMap B K q + algebraMap B K b = 0 := by
    simpa only [map_add, map_mul, map_pow, map_sub, map_ofNat, map_zero] using
      congrArg (algebraMap B K) hq
  have hd' : 2 * algebraMap B K b * algebraMap B K q + 4 -
      2 * algebraMap B K b ≠ 0 := by
    simpa only [map_sub, map_add, map_mul, map_ofNat] using
      (_root_.map_ne_zero (algebraMap B K)).mpr hd
  apply squareIndependent_of_private_valuations anchors hind
  intro i hi
  have hai : a i ≠ algebraMap B K u := by
    intro he
    exact ha.transcendental i (he ▸ isAlgebraic_algebraMap (R := B) u)
  let s := algebraMap B K u + algebraMap B K q * (a i - algebraMap B K u)
  have hs := circle_root_simple (algebraMap B K b) (algebraMap B K u)
    (a i) (algebraMap B K q) hai hq0' hq' hd'
  refine ⟨pointValuation s, ?_, ?_⟩
  · rw [circleRadicand_eq_fraction, Valuation.map_div, map_pow,
      pointValuation_of_simple_root hs.1 hs.2.1,
      pointValuation_polynomial_of_eval_ne_zero hs.2.2]
    simp
  · intro j hj hji
    have hs' := circle_root_other ha b u q hb hq0 hji
    rw [circleRadicand_eq_fraction, Valuation.map_div, map_pow,
      pointValuation_polynomial_of_eval_ne_zero hs'.1,
      pointValuation_polynomial_of_eval_ne_zero hs'.2]
    simp

theorem circle_radicands_squareIndependent_over_constants [IsAlgClosed K]
    (b u : B) (hb : b ≠ 0) (hb1 : b ≠ 1)
    (anchors : List ι) (hind : anchors.Nodup) (ha : AlgebraicIndependent B a) :
    SquareIndependent (anchors.map (fun i =>
      circleRadicand (algebraMap B K b) (algebraMap B K u) (a i))) := by
  let E := algebraicClosure B K
  let : IsAlgClosed E := IsAlgClosure.isAlgClosed B
  have hb' : algebraMap B E b ≠ 0 := (_root_.map_ne_zero _).mpr hb
  have hb1' : algebraMap B E b ≠ 1 := by
    intro hh
    apply hb1
    apply (algebraMap B E).injective
    simpa using hh
  have hh := circle_radicands_squareIndependent (K := K)
    (algebraMap B E b) (algebraMap B E u) hb' hb1' anchors hind ha.algebraicClosure
  have hbe : algebraMap E K (algebraMap B E b) = algebraMap B K b :=
    (IsScalarTower.algebraMap_apply B E K b).symm
  have hue : algebraMap E K (algebraMap B E u) = algebraMap B K u :=
    (IsScalarTower.algebraMap_apply B E K u).symm
  rw [hbe, hue] at hh
  exact hh

end GenericCircle
end PlanarUnitDistances.Radicals

namespace PlanarUnitDistances.GenericCurve
open Polynomial
open scoped nonZeroDivisors
variable {K U : Type*} [Field K] [Field U] [Algebra K U]

noncomputable def ratEval (z : U) (hz : Transcendental K z) : RatFunc K →ₐ[K] U :=
  IsFractionRing.liftAlgHom (transcendental_iff_injective.mp hz)

lemma ratEval_polynomial (z : U) (hz : Transcendental K z) (p : K[X]) :
    ratEval z hz (algebraMap K[X] (RatFunc K) p) = aeval z p := by
  change IsFractionRing.lift (transcendental_iff_injective.mp hz)
    (algebraMap K[X] (RatFunc K) p) = _
  exact IsFractionRing.lift_algebraMap _ p

lemma ratEval_comp (z : U) (hz : Transcendental K z) :
    (ratEval z hz).toRingHom.comp (algebraMap K[X] (RatFunc K)) = (aeval z).toRingHom :=
  RingHom.ext (ratEval_polynomial z hz)

@[simp] lemma ratEval_X (z : U) (hz : Transcendental K z) :
    ratEval z hz RatFunc.X=z := by
  simpa only [RatFunc.algebraMap_X,aeval_X] using ratEval_polynomial z hz (X : K[X])

@[simp] lemma ratEval_C (z : U) (hz : Transcendental K z) (a : K) :
    ratEval z hz (RatFunc.C a)=algebraMap K U a := by
  simpa only [RatFunc.algebraMap_C,aeval_C] using ratEval_polynomial z hz (C a)

lemma irreducible_fraction_curve (f : K[X][X]) (hf : Irreducible f)
    (hdeg : f.natDegree ≠ 0) :
    Irreducible (f.map (algebraMap K[X] (RatFunc K))) :=
  (hf.isPrimitive hdeg).irreducible_iff_irreducible_map_fraction_map.mp hf

theorem exists_curve_embedding (f : K[X][X]) (hf : Irreducible f)
    (hdeg : f.natDegree ≠ 0) (z w : U) (hz : Transcendental K z)
    (hroot : f.eval₂ (aeval z).toRingHom w = 0) :
    ∃ φ : AdjoinRoot (f.map (algebraMap K[X] (RatFunc K))) →ₐ[K] U,
      Function.Injective φ ∧
      φ (AdjoinRoot.root _) = w ∧
      (∀ p : K[X], φ (AdjoinRoot.of _ (algebraMap K[X] (RatFunc K) p)) = aeval z p) := by
  let : Fact (Irreducible (f.map (algebraMap K[X] (RatFunc K)))) :=
    ⟨irreducible_fraction_curve f hf hdeg⟩
  have hr : (f.map (algebraMap K[X] (RatFunc K))).eval₂ (ratEval z hz).toRingHom w = 0 := by
    rw [eval₂_map, ratEval_comp]
    exact hroot
  let φ := AdjoinRoot.liftAlgHom (f.map (algebraMap K[X] (RatFunc K))) (ratEval z hz) w hr
  exact ⟨φ, φ.injective, AdjoinRoot.liftAlgHom_root _ _ _ _,
    fun p => (AdjoinRoot.liftAlgHom_of _ _ _ _ _).trans (ratEval_polynomial z hz p)⟩

lemma fiber_separable [CharZero K] (f : K[X][X]) (hf : Irreducible f)
    (hdeg : f.natDegree ≠ 0) (a : U) (ha : Transcendental K a) :
    (f.map (aeval a).toRingHom).Separable := by
  have hs := (irreducible_fraction_curve f hf hdeg).separable.map
    (f := (ratEval a ha).toRingHom)
  rwa [map_map, ratEval_comp] at hs

lemma fiber_degree (f : K[X][X]) (a : U) (ha : Transcendental K a) :
    (f.map (aeval a).toRingHom).natDegree = f.natDegree :=
  natDegree_map_eq_of_injective (transcendental_iff_injective.mp ha) f

lemma fiber_leadingCoeff_ne_zero (f : K[X][X]) (hf : f ≠ 0)
    (a : U) (ha : Transcendental K a) : aeval a f.leadingCoeff ≠ 0 := by
  intro he
  apply leadingCoeff_ne_zero.mpr hf
  exact transcendental_iff_injective.mp ha (he.trans (map_zero _).symm)

lemma separable_exists_root_ne [IsAlgClosed U] (p : U[X])
    (hs : p.Separable) (hd : 2 ≤ p.natDegree) (c : U) :
    ∃ b : U, p.eval b = 0 ∧ b ≠ c := by
  classical
  have hp : p ≠ 0 := by intro hp; simp [hp] at hd
  have hc : p.roots.toFinset.card = p.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hs), IsAlgClosed.card_roots_eq_natDegree]
  by_contra! hn
  have hsub : p.roots.toFinset ⊆ {c} := by
    intro b hb
    simp only [Finset.mem_singleton]
    apply hn b
    exact (mem_roots hp).mp (Multiset.mem_toFinset.mp hb)
  have hcard := Finset.card_le_card hsub
  rw [hc, Finset.card_singleton] at hcard
  omega

theorem exists_distinct_smooth_sheet [CharZero K] [IsAlgClosed U]
    (f : K[X][X]) (hf : Irreducible f) (hdeg : f.natDegree ≠ 0)
    (a c : U) (ha : Transcendental K a)
    (halt : f.eval₂ (aeval a).toRingHom c ≠ 0 ∨ 2 ≤ f.natDegree) :
    ∃ b : U, f.eval₂ (aeval a).toRingHom b = 0 ∧
      f.derivative.eval₂ (aeval a).toRingHom b ≠ 0 ∧ b ≠ c := by
  let p := f.map (aeval a).toRingHom
  have hs : p.Separable := fiber_separable f hf hdeg a ha
  have hd : p.natDegree = f.natDegree := fiber_degree f a ha
  obtain ⟨b, hb, hbc⟩ : ∃ b : U, p.eval b = 0 ∧ b ≠ c := by
    rcases halt with hnc | htwo
    · obtain ⟨b, hb⟩ := IsAlgClosed.exists_root p (fun h => (hd.trans_ne hdeg) (natDegree_eq_zero_iff_degree_le_zero.mpr h.le))
      change p.eval b = 0 at hb
      refine ⟨b, hb, ?_⟩
      intro he
      subst b
      exact hnc (by simpa only [p, eval_map] using hb)
    · exact separable_exists_root_ne p hs (hd ▸ htwo) c
  refine ⟨b, ?_, ?_, hbc⟩
  · simpa only [p, eval_map] using hb
  · have hh := hs.eval₂_derivative_ne_zero (RingHom.id U) (x := b) (by simpa using hb)
    simpa only [eval₂_id, p, derivative_map, eval_map] using hh

end PlanarUnitDistances.GenericCurve

namespace PlanarUnitDistances.GenericPlane
open Polynomial
variable {K U : Type*} [Field K] [Field U] [Algebra K U]

theorem exists_plane_embedding (x : Fin 2 → U) (hx : AlgebraicIndependent K x) :
    ∃ f : RatFunc (RatFunc K) →+* U,
      f (RatFunc.X : RatFunc (RatFunc K)) = x 1 ∧
      f (RatFunc.C (RatFunc.X : RatFunc K)) = x 0 ∧
      ∀ a : K, f (RatFunc.C (RatFunc.C a)) = algebraMap K U a := by
  let E := IntermediateField.adjoin K ({x 0} : Set U)
  let z : E := ⟨x 0, IntermediateField.subset_adjoin K _ (Set.mem_singleton _)⟩
  have hz : Transcendental K z := by
    intro h
    exact hx.transcendental 0 (h.algHom E.val)
  have hw : Transcendental E (x 1) := by
    apply IntermediateField.transcendental_adjoin_iff.mpr
    have hh := hx.transcendental_adjoin (s := {(0 : Fin 2)}) (i := 1) (by decide)
    rw [Set.image_singleton] at hh
    exact hh
  let g : RatFunc K →ₐ[K] E := GenericCurve.ratEval z hz
  let φ : (RatFunc K)[X] →+* U := (aeval (x 1) : E[X] →ₐ[E] U).toRingHom.comp
    (Polynomial.mapRingHom g.toRingHom)
  have hφ : Function.Injective φ :=
    (transcendental_iff_injective.mp hw).comp (Polynomial.map_injective g.toRingHom g.injective)
  let f : RatFunc (RatFunc K) →+* U := IsFractionRing.lift hφ
  have hf (p : (RatFunc K)[X]) : f (algebraMap (RatFunc K)[X] _ p)=φ p :=
    IsFractionRing.lift_algebraMap hφ p
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [← RatFunc.algebraMap_X, hf]
    simp [φ]
  · rw [← RatFunc.algebraMap_C, hf]
    change aeval (x 1) ((C RatFunc.X).map g.toRingHom) = x 0
    rw [Polynomial.map_C, aeval_C]
    change (g RatFunc.X : U) = x 0
    simp [g,z]
  · intro a
    rw [← RatFunc.algebraMap_C, hf]
    change aeval (x 1) ((C (RatFunc.C a)).map g.toRingHom) = algebraMap K U a
    rw [Polynomial.map_C, aeval_C]
    change (g (RatFunc.C a) : U) = algebraMap K U a
    simp [g]
end PlanarUnitDistances.GenericPlane

namespace PlanarUnitDistances.Radicals
universe u
variable {k K L : Type u} [Field k] [Field K] [CharZero K] [Field L]
  [Algebra k L] [Algebra K L]

theorem plane_differential_obstruction (D : Derivation k L L)
    (x : Fin 2 → L) (hx : AlgebraicIndependent K x)
    (a b da db t : Fin 4 → K) (hab : Function.Injective (fun i => (a i,b i)))
    (l : Fin 4 → L) (A : L) (hl : ∀ i, l i ≠ 0)
    (hdist : ∀ i, (x 0-algebraMap K L (a i))*(x 1-algebraMap K L (b i))=
      2-l i-(l i)⁻¹)
    (hda : ∀ i, D (algebraMap K L (a i))=algebraMap K L (da i))
    (hdb : ∀ i, D (algebraMap K L (b i))=algebraMap K L (db i))
    (hlog : ∀ i, D (l i)/l i=A-algebraMap K L (t i))
    (hD : ∀ i, D (l i) ≠ 0) : False := by
  obtain ⟨f,hw,hz,hc⟩ := GenericPlane.exists_plane_embedding x hx
  let C : K →+* RatFunc (RatFunc K) := RatFunc.C.comp RatFunc.C
  have hC (q : K) : f (C q)=algebraMap K L q := hc q
  have hind := plane_radicands_squareIndependent (List.ofFn (fun i => (a i,b i)))
    (List.nodup_ofFn.mpr hab)
  have hind' : SquareIndependent (List.ofFn (fun i : Fin 4 =>
      ((RatFunc.C (RatFunc.X : RatFunc K)-C (a i))*(RatFunc.X-C (b i)))*
      ((RatFunc.C (RatFunc.X : RatFunc K)-C (a i))*(RatFunc.X-C (b i))-4))) := by
    simpa only [List.map_ofFn, planeRadicandPoly, planeDistancePoly,
      map_mul, map_sub, map_ofNat, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
      Function.comp_def, C, RingHom.comp_apply] using hind
  apply differential_distance_obstruction D f (RatFunc.C RatFunc.X) RatFunc.X
    (C ∘ a) (C ∘ b) (C ∘ da) (C ∘ db) (C ∘ t) l A hind' hl
  · intro i; simpa only [hz,hw,Function.comp_apply,hC] using hdist i
  · intro i; simpa only [Function.comp_apply,hC] using hda i
  · intro i; simpa only [Function.comp_apply,hC] using hdb i
  · intro i; simpa only [Function.comp_apply,hC] using hlog i
  · exact hD
end PlanarUnitDistances.Radicals

namespace PlanarUnitDistances.Radicals
open Polynomial
universe u
variable {k B K L : Type u} [Field k] [Field B] [CharZero B] [Field K] [CharZero K]
  [Field L] [Algebra k L] [Algebra B K] [Algebra K L] [IsAlgClosed K]

theorem line_differential_obstruction (D : Derivation k L L)
    (e e' : B) (he : e ≠ 0)
    (z w : L) (hz : Transcendental K z)
    (hw : w=algebraMap K L (algebraMap B K e)*z+algebraMap K L (algebraMap B K e'))
    (a b da db t : Fin 4 → K) (ha : AlgebraicIndependent B a)
    (hb : ∀ i, b i=algebraMap B K e*a i+algebraMap B K e')
    (l : Fin 4 → L) (A : L) (hl : ∀ i, l i ≠ 0)
    (hdist : ∀ i, (z-algebraMap K L (a i))*(w-algebraMap K L (b i))=
      2-l i-(l i)⁻¹)
    (hda : ∀ i, D (algebraMap K L (a i))=algebraMap K L (da i))
    (hdb : ∀ i, D (algebraMap K L (b i))=algebraMap K L (db i))
    (hlog : ∀ i, D (l i)/l i=A-algebraMap K L (t i))
    (hD : ∀ i, D (l i) ≠ 0) : False := by
  let f : RatFunc K →+* L := (GenericCurve.ratEval z hz).toRingHom
  have hfX : f RatFunc.X=z := GenericCurve.ratEval_X z hz
  have hfC (q : K) : f (RatFunc.C q)=algebraMap K L q := GenericCurve.ratEval_C z hz q
  let w' : RatFunc K := RatFunc.C (algebraMap B K e)*RatFunc.X+RatFunc.C (algebraMap B K e')
  have hfw : f w'=w := by simpa only [w',map_add,map_mul,hfC,hfX] using hw.symm
  have hind := line_radicands_squareIndependent_over_constants e he
    (List.ofFn (id : Fin 4 → Fin 4)) (List.nodup_ofFn.mpr Function.injective_id) ha
  have hd (i : Fin 4) :
      (RatFunc.X-RatFunc.C (a i))*(w'-RatFunc.C (b i))=
        algebraMap K[X] (RatFunc K) (lineDistancePoly (algebraMap B K e) (a i)) := by
    simp only [hb,w',lineDistancePoly,map_mul,map_pow,map_sub,RatFunc.algebraMap_C,
      RatFunc.algebraMap_X,map_add]
    ring
  have hind' : SquareIndependent (List.ofFn (fun i : Fin 4 =>
      ((RatFunc.X-RatFunc.C (a i))*(w'-RatFunc.C (b i)))*
      ((RatFunc.X-RatFunc.C (a i))*(w'-RatFunc.C (b i))-4))) := by
    simpa only [hd,lineRadicandPoly,List.map_ofFn,Function.comp_def,id_eq,
      map_mul,map_sub,map_ofNat] using hind
  apply differential_distance_obstruction D f RatFunc.X w'
    (RatFunc.C ∘ a) (RatFunc.C ∘ b) (RatFunc.C ∘ da) (RatFunc.C ∘ db)
    (RatFunc.C ∘ t) l A hind' hl
  · intro i; simpa only [hfX,hfw,Function.comp_apply,hfC] using hdist i
  · intro i; simpa only [Function.comp_apply,hfC] using hda i
  · intro i; simpa only [Function.comp_apply,hfC] using hdb i
  · intro i; simpa only [Function.comp_apply,hfC] using hlog i
  · exact hD
end PlanarUnitDistances.Radicals

namespace PlanarUnitDistances.Radicals
open Polynomial
universe u
variable {K : Type u} [Field K]

lemma circleDistance_is_locus_distance (b u v a e : K) (ha : a ≠ u)
    (he : (a-u)*(e-v)=b) :
    (RatFunc.X-RatFunc.C a)*
      (RatFunc.C v+RatFunc.C b/(RatFunc.X-RatFunc.C u)-RatFunc.C e)=
      circleDistance b u a := by
  have he' : e=v+b/(a-u) := by
    apply (mul_left_cancel₀ (sub_ne_zero.mpr ha))
    field_simp
    linear_combination he
  have hX : (RatFunc.X : RatFunc K)-RatFunc.C u ≠ 0 := ratFunc_X_sub_C_ne_zero u
  have ha' : RatFunc.C a-RatFunc.C u ≠ 0 := by
    rw [← map_sub]
    exact (_root_.map_ne_zero _).mpr (sub_ne_zero.mpr ha)
  rw [he']
  simp only [circleDistance,circleNumerator,circleDenominator,
    map_mul,map_neg,map_pow,map_sub,map_add,map_div₀,
    RatFunc.algebraMap_C,RatFunc.algebraMap_X]
  field_simp
  ring

variable {k B L : Type u} [Field k] [Field B] [CharZero B] [CharZero K]
  [Field L] [Algebra k L] [Algebra B K] [Algebra K L] [IsAlgClosed K]

theorem circle_differential_obstruction (D : Derivation k L L)
    (u v b₀ : B) (hb₀ : b₀ ≠ 0) (hb₁ : b₀ ≠ 1)
    (z w : L) (hz : Transcendental K z)
    (hw : (z-algebraMap K L (algebraMap B K u))*
      (w-algebraMap K L (algebraMap B K v))=algebraMap K L (algebraMap B K b₀))
    (a b da db t : Fin 4 → K) (ha : AlgebraicIndependent B a)
    (hb : ∀ i, (a i-algebraMap B K u)*(b i-algebraMap B K v)=algebraMap B K b₀)
    (l : Fin 4 → L) (A : L) (hl : ∀ i, l i ≠ 0)
    (hdist : ∀ i, (z-algebraMap K L (a i))*(w-algebraMap K L (b i))=
      2-l i-(l i)⁻¹)
    (hda : ∀ i, D (algebraMap K L (a i))=algebraMap K L (da i))
    (hdb : ∀ i, D (algebraMap K L (b i))=algebraMap K L (db i))
    (hlog : ∀ i, D (l i)/l i=A-algebraMap K L (t i))
    (hD : ∀ i, D (l i) ≠ 0) : False := by
  let f : RatFunc K →+* L := (GenericCurve.ratEval z hz).toRingHom
  have hfX : f RatFunc.X=z := GenericCurve.ratEval_X z hz
  have hfC (q : K) : f (RatFunc.C q)=algebraMap K L q := GenericCurve.ratEval_C z hz q
  let w' : RatFunc K := RatFunc.C (algebraMap B K v)+
    RatFunc.C (algebraMap B K b₀)/(RatFunc.X-RatFunc.C (algebraMap B K u))
  have hz' : z-algebraMap K L (algebraMap B K u) ≠ 0 := by
    intro hh
    apply hz
    rw [sub_eq_zero.mp hh]
    exact isAlgebraic_algebraMap _
  have hfw : f w'=w := by
    simp only [w',map_add,map_div₀,map_sub,hfC,hfX]
    apply mul_left_cancel₀ hz'
    field_simp
    linear_combination -hw
  have hind := circle_radicands_squareIndependent_over_constants b₀ u hb₀ hb₁
    (List.ofFn (id : Fin 4 → Fin 4)) (List.nodup_ofFn.mpr Function.injective_id) ha
  have hd (i : Fin 4) :
      (RatFunc.X-RatFunc.C (a i))*(w'-RatFunc.C (b i))=
        circleDistance (algebraMap B K b₀) (algebraMap B K u) (a i) := by
    apply circleDistance_is_locus_distance _ _ _ _ _ _ (hb i)
    intro hh
    exact ha.transcendental i (hh ▸ isAlgebraic_algebraMap u)
  have hind' : SquareIndependent (List.ofFn (fun i : Fin 4 =>
      ((RatFunc.X-RatFunc.C (a i))*(w'-RatFunc.C (b i)))*
      ((RatFunc.X-RatFunc.C (a i))*(w'-RatFunc.C (b i))-4))) := by
    simpa only [hd,circleRadicand,List.map_ofFn,Function.comp_def,id_eq] using hind
  apply differential_distance_obstruction D f RatFunc.X w'
    (RatFunc.C ∘ a) (RatFunc.C ∘ b) (RatFunc.C ∘ da) (RatFunc.C ∘ db)
    (RatFunc.C ∘ t) l A hind' hl
  · intro i; simpa only [hfX,hfw,Function.comp_apply,hfC] using hdist i
  · intro i; simpa only [Function.comp_apply,hfC] using hda i
  · intro i; simpa only [Function.comp_apply,hfC] using hdb i
  · intro i; simpa only [Function.comp_apply,hfC] using hlog i
  · exact hD
end PlanarUnitDistances.Radicals

end OAI
