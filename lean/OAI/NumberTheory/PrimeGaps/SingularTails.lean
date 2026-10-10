import OAI.NumberTheory.PrimeGaps.SingularSeries

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

noncomputable def singularTailFactor (H : Finset ℤ) (y p : ℕ) : ℝ :=
  if p.Prime ∧ y<p then singularLocal H p else 1

noncomputable def singularTail (H : Finset ℤ) (y : ℕ) : ℝ :=
  ∏' p : ℕ, singularTailFactor H y p

theorem singularTailFactor_pos (H : Finset ℤ) {y : ℕ} (hys : 2*H.card ≤ y) (p : ℕ) :
    0 < singularTailFactor H y p := by
  unfold singularTailFactor
  split_ifs with h
  · have hh := singularLocal_ge_half H h.1.two_le (hys.trans h.2.le)
    linarith
  · norm_num

theorem singularTail_log_summable_bound (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) :
    Summable (fun p : ℕ => Real.log (singularTailFactor H y p)) ∧
    |∑' p : ℕ, Real.log (singularTailFactor H y p)| ≤ singularTailBound H y := by
  have hfin (S : Finset ℕ) :
      (∑ p ∈ S, |Real.log (singularTailFactor H y p)|) ≤ singularTailBound H y := by
    have hh := singularLocal_log_sum_bound H hy hys (S.filter (fun p => p.Prime ∧ y<p))
      (fun p hp => (Finset.mem_filter.mp hp).2)
    simpa only [Finset.sum_filter, singularTailFactor, apply_ite Real.log,
      Real.log_one, apply_ite abs, abs_zero] using hh
  have hs := summable_of_sum_le (fun p => abs_nonneg (Real.log (singularTailFactor H y p))) hfin
  refine ⟨summable_abs_iff.mp hs, ?_⟩
  calc
    _ ≤ ∑' p : ℕ, |Real.log (singularTailFactor H y p)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f:=fun p : ℕ => Real.log (singularTailFactor H y p)) (by
        simpa only [Real.norm_eq_abs] using hs)
    _ ≤ _ := hs.tsum_le_of_sum_le hfin

theorem singularTail_pos_and_log_bound (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) :
    0 < singularTail H y ∧ |Real.log (singularTail H y)| ≤ singularTailBound H y := by
  have hs := singularTail_log_summable_bound H hy hys
  have he : singularTail H y = Real.exp (∑' p : ℕ, Real.log (singularTailFactor H y p)) :=
    (Real.rexp_tsum_eq_tprod (singularTailFactor_pos H hys) hs.1).symm
  rw [he, Real.log_exp]
  exact ⟨Real.exp_pos _, hs.2⟩

theorem singularTail_error (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) (hsmall : singularTailBound H y ≤ 1) :
    |singularTail H y - 1| ≤ 2*singularTailBound H y := by
  obtain ⟨hpos, hlog⟩ := singularTail_pos_and_log_bound H hy hys
  have he := Real.abs_exp_sub_one_le (hlog.trans hsmall)
  rw [Real.exp_log hpos] at he
  exact he.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))

theorem singularSeries_eq_truncation_mul_tail (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) :
    singularSeries H = singularTruncation H y * singularTail H y := by
  classical
  let head : ℕ → ℝ := fun p => if p ∈ Nat.primesLE y then singularLocal H p else 1
  have hh : HasProd head (singularTruncation H y) := by
    have hh : HasProd head (∏ p ∈ Nat.primesLE y, head p) :=
      hasProd_prod_of_ne_finset_one (s:=Nat.primesLE y) (f:=head)
      (fun p hp => ite_eq_right hp)
    simpa only [head, singularTruncation, Finset.prod_ite_mem, Finset.inter_self] using hh
  have ht := Real.hasProd_of_hasSum_log (singularTailFactor_pos H hys)
    (singularTail_log_summable_bound H hy hys).1.hasSum
  have hp : (fun p => head p * singularTailFactor H y p) =
      (fun p : ℕ => if p.Prime then singularLocal H p else 1) := by
    funext p
    simp only [head, singularTailFactor, Nat.mem_primesLE]
    split_ifs <;> first | omega | simp_all
  have htt : HasProd (singularTailFactor H y) (singularTail H y) := by
    simpa only [singularTail, ← ht.tprod_eq] using ht
  have hfull := hh.mul htt
  rw [hp] at hfull
  simpa only [singularSeries, Nat.Primes.tprod_eq_tprod_ite] using hfull.tprod_eq

noncomputable def siftedCount {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) : ℝ :=
  ∑ x : ZMod q, ∏ i : Fin s, if IsUnit (x-a i) then (1:ℝ) else 0

noncomputable def normalizedSiftedCount {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) : ℝ :=
  ((q:ℝ)/q.totient)^s * siftedCount a / q

theorem unit_indicator_sum (q : ℕ) [NeZero q] :
    (∑ x : ZMod q, if IsUnit x then (1:ℝ) else 0) = (q.totient:ℝ) := by
  classical
  have he : (Finset.univ.filter fun x : ZMod q => IsUnit x) =
      Finset.univ.image (fun x : (ZMod q)ˣ => (x:ZMod q)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    change IsUnit x ↔ ∃ u : (ZMod q)ˣ, (u:ZMod q) = x
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨u, hu⟩
    · rintro ⟨u, rfl⟩
      exact u.isUnit
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, he]
  rw [Finset.card_image_of_injective _ Units.val_injective, Finset.card_univ,
    ZMod.card_units_eq_totient]

theorem shifted_unit_indicator_sum {q : ℕ} [NeZero q] (x : ZMod q) :
    (∑ a : ZMod q, if IsUnit (x-a) then (1:ℝ) else 0) = (q.totient:ℝ) := by
  classical
  have hh := (Equiv.subLeft x).sum_comp (fun a : ZMod q => if IsUnit a then (1:ℝ) else 0)
  exact hh.trans (unit_indicator_sum q)

theorem siftedCount_sum (s q : ℕ) [NeZero q] :
    (∑ a : Fin s → ZMod q, siftedCount a) = (q:ℝ)*(q.totient:ℝ)^s := by
  classical
  unfold siftedCount
  rw [Finset.sum_comm]
  have hf (x : ZMod q) :
      (∑ a : Fin s → ZMod q, ∏ i : Fin s, if IsUnit (x-a i) then (1:ℝ) else 0) =
      (q.totient:ℝ)^s := by
    calc
      _ = ∏ _i : Fin s, ∑ b : ZMod q, if IsUnit (x-b) then (1:ℝ) else 0 :=
        (Fintype.prod_sum (fun (_i : Fin s) (b : ZMod q) =>
          if IsUnit (x-b) then (1:ℝ) else 0)).symm
      _ = _ := by simp only [shifted_unit_indicator_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [hf]
  simp

theorem normalizedSiftedCount_sum (s q : ℕ) [NeZero q] :
    (∑ a : Fin s → ZMod q, normalizedSiftedCount a) = (q:ℝ)^s := by
  classical
  have hq : (q:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have ht : (q.totient:ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  unfold normalizedSiftedCount
  rw [← Finset.sum_div, ← Finset.mul_sum, siftedCount_sum]
  rw [div_pow]
  field_simp

theorem siftedCount_crt {s m n : ℕ} [NeZero m] [NeZero n]
    (hcop : m.Coprime n) (a : Fin s → ZMod (m*n)) :
    siftedCount a =
      siftedCount (fun i => (ZMod.chineseRemainder hcop (a i)).1) *
      siftedCount (fun i => (ZMod.chineseRemainder hcop (a i)).2) := by
  classical
  let e := ZMod.chineseRemainder hcop
  have hu (y : ZMod (m*n)) : IsUnit y ↔ IsUnit (e y) := by
    constructor
    · intro hy
      exact hy.map e.toMonoidHom
    · intro hy
      have hh := hy.map e.symm.toMonoidHom
      change IsUnit (e.symm (e y)) at hh
      simpa only [e.symm_apply_apply] using hh
  have hi (x : ZMod (m*n)) (i : Fin s) :
      (if IsUnit (x-a i) then (1:ℝ) else 0) =
      (if IsUnit ((e x).1-(e (a i)).1) then (1:ℝ) else 0) *
      (if IsUnit ((e x).2-(e (a i)).2) then (1:ℝ) else 0) := by
    simp only [hu, e.map_sub, Prod.isUnit_iff, Prod.fst_sub, Prod.snd_sub]
    split_ifs <;> first | omega | simp_all
  unfold siftedCount
  simp_rw [hi, Finset.prod_mul_distrib]
  have he := e.toEquiv.sum_comp (fun x : ZMod m × ZMod n =>
      (∏ i : Fin s, if IsUnit (x.1-(e (a i)).1) then (1:ℝ) else 0) *
      (∏ i : Fin s, if IsUnit (x.2-(e (a i)).2) then (1:ℝ) else 0))
  change _ = _ at he
  calc
    _ = ∑ x : ZMod m × ZMod n,
      (∏ i : Fin s, if IsUnit (x.1-(e (a i)).1) then (1:ℝ) else 0) *
      (∏ i : Fin s, if IsUnit (x.2-(e (a i)).2) then (1:ℝ) else 0) := he
    _ = _ := by
      rw [Fintype.sum_prod_type]
      exact (Fintype.sum_mul_sum
        (fun x : ZMod m => ∏ i : Fin s, if IsUnit (x-(e (a i)).1) then (1:ℝ) else 0)
        (fun x : ZMod n => ∏ i : Fin s, if IsUnit (x-(e (a i)).2) then (1:ℝ) else 0)).symm

theorem normalizedSiftedCount_crt {s m n : ℕ} [NeZero m] [NeZero n]
    (hcop : m.Coprime n) (a : Fin s → ZMod (m*n)) :
    normalizedSiftedCount a =
      normalizedSiftedCount (fun i => (ZMod.chineseRemainder hcop (a i)).1) *
      normalizedSiftedCount (fun i => (ZMod.chineseRemainder hcop (a i)).2) := by
  rw [normalizedSiftedCount, siftedCount_crt hcop, Nat.totient_mul hcop]
  simp only [normalizedSiftedCount, Nat.cast_mul, mul_div_mul_comm, mul_pow]
  ring

theorem product_indicator (s : ℕ) (P : Fin s → Prop) [DecidablePred P] :
    (∏ i : Fin s, if P i then (1:ℝ) else 0) = if ∀ i, P i then 1 else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem siftedCount_prime {s p : ℕ} [NeZero p] (hp : Nat.Prime p) (a : Fin s → ZMod p) :
    siftedCount a = (p:ℝ) - (Finset.univ.image a).card := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have he : (Finset.univ.filter fun x : ZMod p => ∀ i, x ≠ a i) =
      Finset.univ \ Finset.univ.image a := by
    ext x
    simp [eq_comm]
  unfold siftedCount
  simp_rw [isUnit_iff_ne_zero, sub_ne_zero, product_indicator]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, he]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Nat.cast_sub]
  · simp [ZMod.card]
  · exact Finset.card_le_card (Finset.subset_univ _)

theorem normalizedSiftedCount_prime {s p : ℕ} [NeZero p] (hp : Nat.Prime p) (a : Fin s → ZMod p) :
    normalizedSiftedCount a =
      (1 - ((Finset.univ.image a).card:ℝ)/(p:ℝ)) / (1-1/(p:ℝ))^s := by
  classical
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p:ℝ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [normalizedSiftedCount, siftedCount_prime hp, Nat.totient_prime hp]
  rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  have hd : (1:ℝ)-1/p = ((p:ℝ)-1)/p := by field_simp
  rw [hd]
  simp only [div_pow]
  field_simp

noncomputable def siftedTuple {s : ℕ} (a : Fin s → ℤ) (q : ℕ) : ℝ :=
  if h : q=0 then 0 else
    let _ : NeZero q := ⟨h⟩
    normalizedSiftedCount (fun i => (a i : ZMod q))

theorem siftedTuple_eq {s q : ℕ} [NeZero q] (a : Fin s → ℤ) :
    siftedTuple a q = normalizedSiftedCount (fun i => (a i : ZMod q)) := by
  simp only [siftedTuple, dite_eq_right (NeZero.ne q)]

theorem siftedTuple_crt {s m n : ℕ} [NeZero m] [NeZero n]
    (hcop : m.Coprime n) (a : Fin s → ℤ) :
    siftedTuple a (m*n) = siftedTuple a m * siftedTuple a n := by
  simp only [siftedTuple_eq]
  rw [normalizedSiftedCount_crt hcop]
  simp only [map_intCast, Prod.fst_intCast, Prod.snd_intCast]

theorem siftedTuple_one {s : ℕ} (a : Fin s → ℤ) : siftedTuple a 1 = 1 := by
  classical
  have hu (x : ZMod 1) : IsUnit x := by
    convert isUnit_one (M:=ZMod 1) using 1
    exact Subsingleton.elim _ _
  simp only [siftedTuple_eq, normalizedSiftedCount, siftedCount, hu, ite_true]
  simp

theorem siftedTuple_product {s : ℕ} (a : Fin s → ℤ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    siftedTuple a (∏ p ∈ P, p) = ∏ p ∈ P, siftedTuple a p := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [siftedTuple_one]
  | @insert p P hp ih =>
    have hpP := hP p (Finset.mem_insert_self p P)
    have hP' (q) (hq : q ∈ P) := hP q (Finset.mem_insert_of_mem hq)
    let hp0 : NeZero p := ⟨hpP.ne_zero⟩
    let hprod0 : NeZero (∏ q ∈ P, q) := ⟨Finset.prod_ne_zero_iff.mpr
      (fun q hq => (hP' q hq).ne_zero)⟩
    have hc : p.Coprime (∏ q ∈ P, q) := Nat.Coprime.prod_right fun q hq => by
      apply hpP.coprime_iff_not_dvd.mpr
      intro hd
      have he := ((hP' q hq).dvd_iff_eq hpP.ne_one).mp hd
      exact hp (he.symm ▸ hq)
    simp only [Finset.prod_insert hp]
    rw [siftedTuple_crt hc, ih hP']

theorem siftedCount_nonneg {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) :
    0 ≤ siftedCount a := by
  unfold siftedCount
  positivity

theorem siftedCount_le {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) :
    siftedCount a ≤ (q:ℝ) := by
  classical
  calc
    _ ≤ ∑ _x : ZMod q, (1:ℝ) := by
      unfold siftedCount
      apply Finset.sum_le_sum
      intro x _
      exact Finset.prod_le_one₀ (fun _ _ => by positivity) (fun _ _ => by split_ifs <;> norm_num)
    _ = _ := by simp

theorem normalizedSiftedCount_nonneg {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) :
    0 ≤ normalizedSiftedCount a :=
  div_nonneg (mul_nonneg (by positivity) (siftedCount_nonneg a)) (Nat.cast_nonneg _)

theorem normalizedSiftedCount_le {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) :
    normalizedSiftedCount a ≤ (q:ℝ)^s := by
  have hq : (0:ℝ)<q := by exact_mod_cast NeZero.pos q
  have ht : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hdiv : (q:ℝ)/q.totient ≤ q := (div_le_self hq.le ht)
  unfold normalizedSiftedCount
  calc
    _ ≤ (q:ℝ)^s * q / q := div_le_div_of_nonneg_right
      (mul_le_mul (pow_le_pow_left₀ (by positivity) hdiv s) (siftedCount_le a)
        (siftedCount_nonneg a) (by positivity)) hq.le
    _ = _ := mul_div_cancel_right₀ _ hq.ne'

theorem residueCount_eq_card_zmod (H : Finset ℤ) {q : ℕ} [NeZero q] :
    residueCount H q = (H.image fun a : ℤ => (a : ZMod q)).card := by
  classical
  have he : (H.image fun a => a % (q:ℤ)).image (fun a : ℤ => (a : ZMod q)) =
      H.image (fun a : ℤ => (a : ZMod q)) := by
    rw [Finset.image_image]
    congr 1
    funext a
    exact ZMod.intCast_mod a q
  rw [← he]
  symm
  apply Finset.card_image_of_injOn
  intro a ha b hb heq
  obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b', _, rfl⟩ := Finset.mem_image.mp hb
  have hh := (ZMod.intCast_eq_intCast_iff _ _ q).mp heq
  change (a' % (q:ℤ)) % (q:ℤ) = (b' % (q:ℤ)) % (q:ℤ) at hh
  simpa only [Int.emod_emod] using hh

theorem siftedTuple_prime_eq {s p : ℕ} (hp : Nat.Prime p) (a : Fin s → ℤ)
    (ha : Function.Injective a) :
    siftedTuple a p = singularLocal (Finset.univ.image a) p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [siftedTuple_eq, normalizedSiftedCount_prime hp, singularLocal,
    residueCount_eq_card_zmod, Finset.image_image,
    Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]
  rfl

theorem siftedTuple_primorial_eq {s y : ℕ} (a : Fin s → ℤ) (ha : Function.Injective a) :
    siftedTuple a (∏ p ∈ Nat.primesLE y, p) = singularTruncation (Finset.univ.image a) y := by
  rw [siftedTuple_product a _ (fun p hp => (Nat.mem_primesLE.mp hp).2)]
  exact Finset.prod_congr rfl fun p hp => siftedTuple_prime_eq (Nat.mem_primesLE.mp hp).2 a ha

def rangeResidue (h q c : ℕ) : Finset ℕ := (Finset.range h).filter fun n => n%q=c

theorem rangeResidue_card_bounds (h : ℕ) {q c : ℕ} (hq : 0<q) (hc : c<q) :
    h/q ≤ (rangeResidue h q c).card ∧ (rangeResidue h q c).card ≤ h/q+1 := by
  have hlo : (Finset.range (h/q)).card ≤ (rangeResidue h q c).card := by
    apply Finset.card_le_card_of_injOn (fun k => q*k+c)
    · intro k hk
      have hh := Nat.mul_le_mul_left q (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
      have hh' : q*k+q ≤ q*(h/q) := by simpa only [Nat.mul_succ] using hh
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
        change q*k+c<h
        have hd : q*(h/q) ≤ h := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self h q
        omega), ?_⟩
      simp only [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_eq_of_lt hc]
    · intro k _ l _ heq
      exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel heq)
  have hup : (rangeResidue h q c).card ≤ (Finset.range (h/q+1)).card := by
    apply Finset.card_le_card_of_injOn (fun n => n/q)
    · intro n hn
      have hh : n/q ≤ h/q := Nat.div_le_div_right (Finset.mem_range.mp (Finset.mem_filter.mp hn).1).le
      exact Finset.mem_range.mpr (by dsimp only; omega)
    · intro n hn m hm heq
      have hnmod := (Finset.mem_filter.mp hn).2
      have hmmod := (Finset.mem_filter.mp hm).2
      have hnform := Nat.div_add_mod n q
      have hmform := Nat.div_add_mod m q
      change n/q=m/q at heq
      rw [heq, hnmod] at hnform
      rw [hmmod] at hmform
      omega
  simpa only [Finset.card_range] using And.intro hlo hup

noncomputable def cyclicFiber (a : ℤ) (h q : ℕ) [NeZero q] (r : ZMod q) : Finset (Fin h) :=
  Finset.univ.filter fun n => (a:ZMod q)+(n:ℕ)=r

theorem cyclicFiber_card_bounds (a : ℤ) (h q : ℕ) [NeZero q] (r : ZMod q) :
    h/q ≤ (cyclicFiber a h q r).card ∧ (cyclicFiber a h q r).card ≤ h/q+1 := by
  classical
  have hpred (n : ℕ) : (a:ZMod q)+(n:ZMod q)=r ↔ n%q=(r-(a:ZMod q)).val := by
    rw [← eq_sub_iff_add_eq']
    constructor
    · intro he
      simpa only [ZMod.val_natCast] using congrArg ZMod.val he
    · intro he
      apply ZMod.val_injective q
      simpa only [ZMod.val_natCast] using he
  have hc : (cyclicFiber a h q r).card = (rangeResidue h q (r-(a:ZMod q)).val).card := by
    apply Finset.card_bij (fun (n : Fin h) _ => (n:ℕ))
    · intro n hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr n.isLt, ?_⟩
      exact (hpred n).mp (Finset.mem_filter.mp hn).2
    · intro n _ m _ he
      exact Fin.ext he
    · intro n hn
      obtain ⟨hn, hmod⟩ := Finset.mem_filter.mp hn
      refine ⟨⟨n, Finset.mem_range.mp hn⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hpred n).mpr hmod⟩
  rw [hc]
  exact rangeResidue_card_bounds h (NeZero.pos q) (ZMod.val_lt _)

noncomputable def residueTuple {s h q : ℕ} (a : Fin s → ℤ) (n : Fin s → Fin h) : Fin s → ZMod q :=
  fun i => (a i:ZMod q)+(n i:ℕ)

theorem residueTuple_fiber_card {s h q : ℕ} [NeZero q] (a : Fin s → ℤ) (r : Fin s → ZMod q) :
    (Finset.univ.filter fun n : Fin s → Fin h => residueTuple a n = r).card =
      ∏ i : Fin s, (cyclicFiber (a i) h q (r i)).card := by
  classical
  have he : (Finset.univ.filter fun n : Fin s → Fin h => residueTuple a n = r) =
      Fintype.piFinset (fun i => cyclicFiber (a i) h q (r i)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      cyclicFiber, funext_iff, residueTuple]
  rw [he, Fintype.card_piFinset]

theorem residueTuple_sum_bounds {s h q : ℕ} [NeZero q] (a : Fin s → ℤ)
    (f : (Fin s → ZMod q) → ℝ) (hf : ∀ r, 0≤f r) :
    ((h/q:ℕ):ℝ)^s * (∑ r, f r) ≤ (∑ n : Fin s → Fin h, f (residueTuple a n)) ∧
    (∑ n : Fin s → Fin h, f (residueTuple a n)) ≤ ((h/q+1:ℕ):ℝ)^s * (∑ r, f r) := by
  classical
  have he : (∑ n : Fin s → Fin h, f (residueTuple a n)) =
      ∑ r : Fin s → ZMod q,
        ((Finset.univ.filter fun n : Fin s → Fin h => residueTuple a n = r).card:ℝ) * f r := by
    rw [← Finset.sum_fiberwise Finset.univ (residueTuple (q:=q) a) (fun n => f (residueTuple a n))]
    apply Finset.sum_congr rfl
    intro r _
    calc
      _ = ∑ _n ∈ Finset.univ.filter (fun n : Fin s → Fin h => residueTuple a n = r), f r := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [(Finset.mem_filter.mp hn).2]
      _ = _ := by simp
  rw [he]
  have hcard (r : Fin s → ZMod q) : ((h/q:ℕ):ℝ)^s ≤
      ((Finset.univ.filter fun n : Fin s → Fin h => residueTuple a n = r).card:ℝ) ∧
      ((Finset.univ.filter fun n : Fin s → Fin h => residueTuple a n = r).card:ℝ) ≤
        ((h/q+1:ℕ):ℝ)^s := by
    rw [residueTuple_fiber_card, Nat.cast_prod]
    constructor
    · calc
        _ = ∏ _i : Fin s, ((h/q:ℕ):ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ => by
          exact_mod_cast (cyclicFiber_card_bounds (a i) h q (r i)).1
    · calc
        _ ≤ ∏ _i : Fin s, ((h/q+1:ℕ):ℝ) :=
          Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ => by
            exact_mod_cast (cyclicFiber_card_bounds (a i) h q (r i)).2
        _ = _ := by simp
  simp only [Finset.mul_sum]
  exact ⟨Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hcard r).1 (hf r),
    Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hcard r).2 (hf r)⟩

def boxTuple {s h : ℕ} (a : Fin s → ℤ) (n : Fin s → Fin h) : Fin s → ℤ :=
  fun i => a i + (n i:ℕ)

theorem boxTuple_collision_count {s h : ℕ} (a : Fin s → ℤ) {i j : Fin s} (hij : i≠j) :
    (Finset.univ.filter fun n : Fin s → Fin h => boxTuple a n i = boxTuple a n j).card ≤
      h^(s-1) := by
  classical
  have hc : Fintype.card {k : Fin s // k ≠ j} = s-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  calc
    _ ≤ (Finset.univ : Finset ({k : Fin s // k ≠ j} → Fin h)).card := by
      apply Finset.card_le_card_of_injOn (fun n k => n k.val)
      · intro n _
        exact Finset.mem_univ _
      · intro n hn m hm he
        have hi := congrFun he ⟨i, hij⟩
        have hn' := (Finset.mem_filter.mp hn).2
        have hm' := (Finset.mem_filter.mp hm).2
        funext k
        by_cases hk : k=j
        · subst k
          unfold boxTuple at hn' hm'
          have hci : (n i:ℕ)=(m i:ℕ) := congrArg Fin.val hi
          apply Fin.ext
          omega
        · exact congrFun he ⟨k, hk⟩
    _ = _ := by simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hc]

theorem boxTuple_nondistinct_count {s h : ℕ} (a : Fin s → ℤ) :
    (Finset.univ.filter fun n : Fin s → Fin h => ¬ Function.Injective (boxTuple a n)).card ≤
      s^2 * h^(s-1) := by
  classical
  let pairs : Finset (Fin s × Fin s) := Finset.univ.filter fun ij => ij.1 ≠ ij.2
  let bad (ij : Fin s × Fin s) := Finset.univ.filter fun n : Fin s → Fin h =>
    boxTuple a n ij.1 = boxTuple a n ij.2
  have hsub : (Finset.univ.filter fun n : Fin s → Fin h => ¬ Function.Injective (boxTuple a n)) ⊆
      pairs.biUnion bad := by
    intro n hn
    have hni := (Finset.mem_filter.mp hn).2
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨i, j, he, hne⟩ := hni
    exact Finset.mem_biUnion.mpr ⟨(i,j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
  calc
    _ ≤ (pairs.biUnion bad).card := Finset.card_le_card hsub
    _ ≤ pairs.card * h^(s-1) := Finset.card_biUnion_le_card_mul pairs bad _ fun ij hij =>
      boxTuple_collision_count a (Finset.mem_filter.mp hij).2
    _ ≤ s^2 * h^(s-1) := Nat.mul_le_mul_right _ (by
      calc
        pairs.card ≤ (Finset.univ : Finset (Fin s × Fin s)).card := Finset.card_filter_le _ _
        _ = _ := by simp [pow_two])

end LargePrimeGaps

end OAI
