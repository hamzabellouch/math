import OAI.NumberTheory.DirichletL.Inversion.InitialFibers

namespace OAI

namespace SevenEighths.InverseSecondFibers

open ActualEisensteinCubic
open CompletedGauss (primaryGenerator primaryGenerator_mul)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open InverseInitialFibers (divisor_card_mul_le divisor_card_pos)
open scoped BigOperators Classical
noncomputable section

@[ext] structure OuterTriple where
  q0 : Ideal O
  quotient : Ideal O
  residual : Ideal O

@[ext] structure SecondTuple (Jo Jn : ℕ) where
  outer : OuterTriple
  core : Fin 8 → Ideal O
  commonResidual : Ideal O
  cubeResidual : Ideal O
  secondCube : Ideal O
  extractedCommon : Ideal O
  frequency : O
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal
  newAssigned : Fin Jn → SmoothMobiusCorrection.PrimeIdeal

structure Valid {Jo Jn : ℕ} (x : SecondTuple Jo Jn)
    (γ : OuterTriple) (f : Ideal O) (k : O) : Prop where
  outer_eq : x.outer = γ
  label : x.core 0 * x.core 1 * x.core 2 * x.commonResidual = f
  j_split : x.core 3 * x.cubeResidual = x.core 0
  b_split : x.core 4 * x.secondCube = γ.q0^2 * x.cubeResidual^2 * x.core 3
  a1 : x.core 5 ∣ (x.core 4 * x.secondCube).radical
  a2 : x.core 6 ∣ (x.core 4 * x.secondCube).radical
  d : x.core 7 ∣ x.core 1 * (x.core 4 * x.secondCube).radical
  extracted_eq : x.core 2 * γ.residual = x.extractedCommon
  generator_d : primaryGenerator (x.core 7) ≠ 0
  generator_d2 : primaryGenerator (x.core 2) ≠ 0
  row_eq : primaryGenerator (x.core 7) * primaryGenerator (x.core 2) * x.frequency = k
  old_dvd : ∀ i, (x.oldAssigned i).val ∣ γ.q0 * f * γ.quotient
  new_dvd : ∀ i, (x.newAssigned i).val ∣ f * γ.residual

lemma poisson_divisor_source (d C R rest B : Ideal O)
    (hR : R * rest = B.radical) (hd : d ∣ C * rest) : d ∣ C * B.radical := by
  apply hd.trans
  rw [← hR]
  exact mul_dvd_mul_left C (dvd_mul_left rest R)

lemma core_dvd_label {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) (i : Fin 4) :
    x.core ⟨i.val, by omega⟩ ∣ f := by
  have hJ : x.core 0 ∣ f := by
    rw [← hx.label]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  fin_cases i
  · exact hJ
  · rw [← hx.label]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
  · rw [← hx.label]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  · exact (show x.core 3 ∣ x.core 0 from ⟨x.cubeResidual, hx.j_split.symm⟩).trans hJ

lemma common_label_dvd {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) :
    x.core 1 * x.core 0 ∣ f := by
  refine ⟨x.core 2 * x.commonResidual, ?_⟩
  rw [← hx.label]
  ring

lemma cube_product_dvd_square {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) :
    x.core 4 * x.secondCube ∣ (γ.q0 * x.core 0)^2 := by
  refine ⟨x.core 3, ?_⟩
  rw [hx.b_split, ← hx.j_split]
  ring

lemma cube_radical_dvd {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) :
    (x.core 4 * x.secondCube).radical ∣ γ.q0 * x.core 0 := by
  apply Ideal.dvd_iff_le.mpr
  have hle := Ideal.radical_mono (Ideal.dvd_iff_le.mp (cube_product_dvd_square hx))
  rw [Ideal.radical_pow (γ.q0 * x.core 0) (by decide : (2 : ℕ) ≠ 0)] at hle
  exact Ideal.le_radical.trans hle

lemma cube_factor_dvd_target {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) :
    x.core 4 ∣ (γ.q0 * f)^2 :=
  (dvd_mul_right _ _).trans ((cube_product_dvd_square hx).trans
    (pow_dvd_pow_of_dvd (mul_dvd_mul_left _ (core_dvd_label hx 0)) 2))

lemma core_dvd_outer_label {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) (i : Fin 3) :
    x.core ⟨i.val+5, by omega⟩ ∣ γ.q0 * f := by
  have hrad : (x.core 4 * x.secondCube).radical ∣ γ.q0 * f :=
    (cube_radical_dvd hx).trans (mul_dvd_mul_left _ (core_dvd_label hx 0))
  fin_cases i
  · exact hx.a1.trans hrad
  · exact hx.a2.trans hrad
  · apply hx.d.trans
    apply (mul_dvd_mul_left (x.core 1) (cube_radical_dvd hx)).trans
    convert mul_dvd_mul_left γ.q0 (common_label_dvd hx) using 1
    ring

lemma core_ne_zero {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (i : Fin 8) : x.core i ≠ 0 := by
  have hd : x.core i ∣ (γ.q0*f)^2 := by
    by_cases hi : i.val < 4
    · exact (core_dvd_label hx ⟨i.val, hi⟩).trans
        ((dvd_mul_left _ _).trans (dvd_pow_self _ (by decide : 2 ≠ 0)))
    · by_cases hi4 : i.val = 4
      · have he : i = 4 := Fin.ext hi4
        simpa only [he] using cube_factor_dvd_target hx
      · have he : (⟨(i.val-5)+5, by omega⟩ : Fin 8) = i := by
          apply Fin.ext
          dsimp
          omega
        exact (he ▸ core_dvd_outer_label hx ⟨i.val-5, by omega⟩).trans
          (dvd_pow_self _ (by decide : 2 ≠ 0))
  intro hz
  rw [hz, zero_dvd_iff] at hd
  exact (pow_ne_zero 2 (mul_ne_zero hq hf)) hd

theorem valid_key_injective {Jo Jn : ℕ} (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) {x y : SecondTuple Jo Jn}
    (hx : Valid x γ f k) (hy : Valid y γ f k)
    (hc : x.core = y.core) (ho : x.oldAssigned = y.oldAssigned)
    (hn : x.newAssigned = y.newAssigned) : x = y := by
  have hcore (i : Fin 8) : x.core i = y.core i := congrFun hc i
  have hv : x.commonResidual = y.commonResidual := by
    apply mul_left_cancel₀ (mul_ne_zero
      (mul_ne_zero (core_ne_zero hx hf hq 0) (core_ne_zero hx hf hq 1))
      (core_ne_zero hx hf hq 2))
    exact hx.label.trans (by simpa only [hcore] using hy.label.symm)
  have hj : x.cubeResidual = y.cubeResidual := by
    apply mul_left_cancel₀ (core_ne_zero hx hf hq 3)
    exact hx.j_split.trans (by simpa only [hcore] using hy.j_split.symm)
  have hb : x.secondCube = y.secondCube := by
    apply mul_left_cancel₀ (core_ne_zero hx hf hq 4)
    exact hx.b_split.trans (by simpa only [hcore, hj] using hy.b_split.symm)
  have hg : x.extractedCommon = y.extractedCommon := by
    rw [← hx.extracted_eq, ← hy.extracted_eq, hcore]
  have hr : x.frequency = y.frequency := by
    apply mul_left_cancel₀ (mul_ne_zero hx.generator_d hx.generator_d2)
    exact hx.row_eq.trans (by simpa only [hcore] using hy.row_eq.symm)
  exact SecondTuple.ext (hx.outer_eq.trans hy.outer_eq.symm) hc hv hj hb hg hr ho hn

theorem valid_tuple_card_le {Jo Jn : ℕ} (T : Finset (SecondTuple Jo Jn))
    (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (hT : ∀ x ∈ T, Valid x γ f k) :
    T.card ≤ (idealDivisors f).card^4 * (idealDivisors ((γ.q0*f)^2)).card *
      (idealDivisors (γ.q0*f)).card^3 *
      (idealDivisors (γ.q0*f*γ.quotient)).card^Jo *
      (idealDivisors (f*γ.residual)).card^Jn := by
  let D := idealDivisors f
  let E := idealDivisors ((γ.q0*f)^2)
  let F := idealDivisors (γ.q0*f)
  let A := idealDivisors (γ.q0*f*γ.quotient)
  let B := idealDivisors (f*γ.residual)
  let Target := (Fin 4 → D) × E × (Fin 3 → F) × (Fin Jo → A) × (Fin Jn → B)
  let encode (x : T) : Target :=
    (fun i => ⟨x.val.core ⟨i.val, by omega⟩,
      (mem_idealDivisors hf).mpr (core_dvd_label (hT x.val x.property) i)⟩,
    ⟨x.val.core 4, (mem_idealDivisors (pow_ne_zero 2 (mul_ne_zero hq hf))).mpr
      (cube_factor_dvd_target (hT x.val x.property))⟩,
    (fun i => ⟨x.val.core ⟨i.val+5, by omega⟩,
      (mem_idealDivisors (mul_ne_zero hq hf)).mpr (core_dvd_outer_label (hT x.val x.property) i)⟩),
    (fun i => ⟨(x.val.oldAssigned i).val,
      (mem_idealDivisors (mul_ne_zero (mul_ne_zero hq hf) ht)).mpr
        ((hT x.val x.property).old_dvd i)⟩),
    (fun i => ⟨(x.val.newAssigned i).val,
      (mem_idealDivisors (mul_ne_zero hf hr)).mpr ((hT x.val x.property).new_dvd i)⟩))
  have hi : Function.Injective encode := by
    intro x y he
    apply Subtype.ext
    apply valid_key_injective γ f k hf hq (hT x.val x.property) (hT y.val y.property)
    · funext i
      fin_cases i
      · exact congrArg (fun z : Target => (z.1 0).val) he
      · exact congrArg (fun z : Target => (z.1 1).val) he
      · exact congrArg (fun z : Target => (z.1 2).val) he
      · exact congrArg (fun z : Target => (z.1 3).val) he
      · exact congrArg (fun z : Target => z.2.1.val) he
      · exact congrArg (fun z : Target => (z.2.2.1 0).val) he
      · exact congrArg (fun z : Target => (z.2.2.1 1).val) he
      · exact congrArg (fun z : Target => (z.2.2.1 2).val) he
    · funext i
      apply Subtype.ext
      exact congrArg (fun z : Target => (z.2.2.2.1 i).val) he
    · funext i
      apply Subtype.ext
      exact congrArg (fun z : Target => (z.2.2.2.2 i).val) he
  simpa only [Target, D, E, F, A, B, Fintype.card_coe, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, Nat.mul_assoc] using Fintype.card_le_of_injective encode hi

lemma divisor_card_sq_le (I : Ideal O) (hI : I ≠ 0) :
    (idealDivisors (I^2)).card ≤ (idealDivisors I).card^2 := by
  simpa only [pow_two] using divisor_card_mul_le I I hI hI

theorem valid_tuple_card_le_separated {Jo Jn : ℕ} (T : Finset (SecondTuple Jo Jn))
    (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (hT : ∀ x ∈ T, Valid x γ f k) :
    T.card ≤ (idealDivisors f).card^(9+Jo+Jn) * (idealDivisors γ.q0).card^(5+Jo) *
      (idealDivisors γ.quotient).card^Jo * (idealDivisors γ.residual).card^Jn := by
  let df := (idealDivisors f).card
  let dq := (idealDivisors γ.q0).card
  let dt := (idealDivisors γ.quotient).card
  let dr := (idealDivisors γ.residual).card
  have hqf : (idealDivisors (γ.q0*f)).card ≤ dq*df := divisor_card_mul_le _ _ hq hf
  have hsq : (idealDivisors ((γ.q0*f)^2)).card ≤ (dq*df)^2 :=
    (divisor_card_sq_le _ (mul_ne_zero hq hf)).trans (Nat.pow_le_pow_left hqf 2)
  have hold : (idealDivisors (γ.q0*f*γ.quotient)).card ≤ dq*df*dt :=
    (divisor_card_mul_le _ _ (mul_ne_zero hq hf) ht).trans (Nat.mul_le_mul_right _ hqf)
  have hnew : (idealDivisors (f*γ.residual)).card ≤ df*dr := divisor_card_mul_le _ _ hf hr
  apply (valid_tuple_card_le T γ f k hf hq ht hr hT).trans
  calc
    _ ≤ df^4 * (dq*df)^2 * (dq*df)^3 * (dq*df*dt)^Jo * (df*dr)^Jn := by
      gcongr
    _ = _ := by
      dsimp [df, dq, dt, dr]
      simp only [mul_pow, pow_add]
      ring

theorem valid_tuple_card_le_slot_cap {Jo Jn : ℕ} (T : Finset (SecondTuple Jo Jn))
    (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (hT : ∀ x ∈ T, Valid x γ f k) (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    T.card ≤ (idealDivisors f).card^(9+4*K) * (idealDivisors γ.q0).card^(5+2*K) *
      (idealDivisors γ.quotient).card^(2*K) * (idealDivisors γ.residual).card^(2*K) := by
  apply (valid_tuple_card_le_separated T γ f k hf hq ht hr hT).trans
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
    (pow_le_pow_right₀ (divisor_card_pos f hf) (by omega))
    (pow_le_pow_right₀ (divisor_card_pos γ.q0 hq) (by omega)))
    (pow_le_pow_right₀ (divisor_card_pos γ.quotient ht) ho))
    (pow_le_pow_right₀ (divisor_card_pos γ.residual hr) hn)

theorem valid_label_squarefree {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k)
    (hJ : Squarefree (x.core 0)) (hC : Squarefree (x.core 1))
    (hg : Squarefree x.extractedCommon) (hv : Squarefree x.commonResidual)
    (hJC : IsCoprime (x.core 0) (x.core 1))
    (hgmask : IsCoprime x.extractedCommon (x.core 1 * x.core 0))
    (hvmask : IsCoprime x.commonResidual (x.extractedCommon * x.core 1 * x.core 0)) :
    Squarefree f := by
  have hdg : x.core 2 ∣ x.extractedCommon := ⟨γ.residual, hx.extracted_eq.symm⟩
  have hdJC : IsCoprime (x.core 2) (x.core 0 * x.core 1) := by
    simpa only [mul_comm] using hgmask.of_isCoprime_of_dvd_left hdg
  have hdiv : (x.core 0 * x.core 1) * x.core 2 ∣
      x.extractedCommon * x.core 1 * x.core 0 := by
    convert mul_dvd_mul_left (x.core 0 * x.core 1) hdg using 1
    ring
  have hvJCd := hvmask.of_isCoprime_of_dvd_right hdiv
  rw [← hx.label]
  exact squarefree_mul_iff.mpr ⟨hvJCd.symm.isRelPrime,
    squarefree_mul_iff.mpr ⟨hdJC.symm.isRelPrime,
      squarefree_mul_iff.mpr ⟨hJC.isRelPrime, hJ, hC⟩,
      hg.squarefree_of_dvd hdg⟩, hv⟩

theorem cube_quotient_norm_sq_le {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) :
    Ideal.absNorm γ.q0 ^ 2 ≤ Ideal.absNorm (x.core 4) * Ideal.absNorm x.secondCube := by
  have hj0 : x.cubeResidual ≠ 0 := by
    intro hz
    have he := hx.j_split
    rw [hz, mul_zero] at he
    exact core_ne_zero hx hf hq 0 he.symm
  have hp0 : x.core 4 * x.secondCube ≠ 0 := by
    rw [hx.b_split]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hq) (pow_ne_zero 2 hj0))
      (core_ne_zero hx hf hq 3)
  have hdiv : γ.q0^2 ∣ x.core 4 * x.secondCube := by
    rw [hx.b_split]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hn := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun hz => hp0 (Ideal.absNorm_eq_zero_iff.mp hz)))
    (map_dvd Ideal.absNorm hdiv)
  simpa only [map_pow, map_mul] using hn

theorem cube_quotient_norm_le {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (N : ℕ)
    (hpair : Ideal.absNorm (x.core 4) * Ideal.absNorm x.secondCube ≤ N^2) :
    Ideal.absNorm γ.q0 ≤ N := by
  have hh := (cube_quotient_norm_sq_le hx hf hq).trans hpair
  nlinarith

def originalSource {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) : Finset (SecondTuple Jo Jn) :=
  source.filter fun x => (∀ i, x.oldAssigned i ∈ oldLists i) ∧
    (∀ i, x.newAssigned i ∈ newLists i) ∧ keep x

def sourceTriples {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) : Finset OuterTriple :=
  (originalSource source oldLists newLists keep).image SecondTuple.outer

theorem mem_sourceTriples {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) :
    γ ∈ sourceTriples source oldLists newLists keep ↔
      ∃ x ∈ source, (∀ i, x.oldAssigned i ∈ oldLists i) ∧
        (∀ i, x.newAssigned i ∈ newLists i) ∧ keep x ∧ x.outer = γ := by
  simp only [sourceTriples, originalSource, Finset.mem_image, Finset.mem_filter]
  aesop

theorem sourceTriples_property {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (P : OuterTriple → Prop)
    (hP : ∀ x ∈ originalSource source oldLists newLists keep, P x.outer)
    (γ : OuterTriple) (hγ : γ ∈ sourceTriples source oldLists newLists keep) : P γ := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hγ
  exact hP x hx

theorem sourceTriples_cube_norm_le {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (N : ℕ)
    (hsrc : ∀ x ∈ originalSource source oldLists newLists keep,
      ∃ f k, Valid x x.outer f k ∧ f ≠ 0 ∧ x.outer.q0 ≠ 0 ∧
        Ideal.absNorm (x.core 4) * Ideal.absNorm x.secondCube ≤ N^2)
    (γ : OuterTriple) (hγ : γ ∈ sourceTriples source oldLists newLists keep) :
    Ideal.absNorm γ.q0 ≤ N := by
  apply sourceTriples_property source oldLists newLists keep
    (fun γ => Ideal.absNorm γ.q0 ≤ N) ?_ γ hγ
  intro x hx
  obtain ⟨f, k, hv, hf, hq, hpair⟩ := hsrc x hx
  exact cube_quotient_norm_le hv hf hq N hpair

def secondFiber {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) (f : Ideal O) (k : O) :
    Finset (SecondTuple Jo Jn) :=
  (originalSource source oldLists newLists keep).filter (fun x => Valid x γ f k)

theorem secondFiber_outer_mem {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) (f : Ideal O) (k : O)
    (x : SecondTuple Jo Jn) (hx : x ∈ secondFiber source oldLists newLists keep γ f k) :
    γ ∈ sourceTriples source oldLists newLists keep := by
  obtain ⟨hsrc, hv⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_image.mpr ⟨x, hsrc, hv.outer_eq⟩

theorem secondFiber_empty_of_not_sourceTriple {Jo Jn : ℕ}
    (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) (f : Ideal O) (k : O)
    (hγ : γ ∉ sourceTriples source oldLists newLists keep) :
    secondFiber source oldLists newLists keep γ f k = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hγ (secondFiber_outer_mem source oldLists newLists keep γ f k x hx)

theorem secondFiber_card_le {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    (secondFiber source oldLists newLists keep γ f k).card ≤
      (idealDivisors f).card^(9+4*K) * (idealDivisors γ.q0).card^(5+2*K) *
      (idealDivisors γ.quotient).card^(2*K) * (idealDivisors γ.residual).card^(2*K) :=
  valid_tuple_card_le_slot_cap _ γ f k hf hq ht hr
    (fun _x hx => (Finset.mem_filter.mp hx).2) K ho hn

theorem secondFiber_weight_bound {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ x ∈ secondFiber source oldLists newLists keep γ f k, ‖w x‖ ≤ C) :
    (∑ x ∈ secondFiber source oldLists newLists keep γ f k, ‖w x‖) ≤
      C * ((idealDivisors f).card : ℝ)^(9+4*K) *
        ((idealDivisors γ.q0).card : ℝ)^(5+2*K) *
        ((idealDivisors γ.quotient).card : ℝ)^(2*K) *
        ((idealDivisors γ.residual).card : ℝ)^(2*K) := by
  calc
    _ ≤ ∑ _x ∈ secondFiber source oldLists newLists keep γ f k, C := Finset.sum_le_sum hw
    _ = ((secondFiber source oldLists newLists keep γ f k).card : ℝ) * C := by simp
    _ ≤ ((idealDivisors f).card^(9+4*K) * (idealDivisors γ.q0).card^(5+2*K) *
        (idealDivisors γ.quotient).card^(2*K) * (idealDivisors γ.residual).card^(2*K) : ℕ) * C :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast (secondFiber_card_le source oldLists newLists keep γ f k hf hq ht hr K ho hn)) hC
    _ = _ := by push_cast; ring

end
end SevenEighths.InverseSecondFibers

end OAI
