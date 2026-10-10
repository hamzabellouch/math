import OAI.Combinatorics.SquareDifference.CompleteWeights

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

lemma periodic_nat_mod (a : ℕ → ℂ) (q : ℕ) (ha : Function.Periodic a q) (n : ℕ) :
    a (n % q) = a n := by
  have h := (ha.nsmul (n / q)) (n % q)
  simpa only [nsmul_eq_mul,Nat.cast_id,Nat.mul_comm (n / q) q,Nat.mod_add_div] using h.symm

lemma periodic_sum_multiple (a : ℕ → ℂ) (q k : ℕ) (ha : Function.Periodic a q) :
    ∑ m ∈ range (q*k), a m = (k : ℂ) * ∑ m ∈ range q, a m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ,sum_range_add,ih]
    have h (i : ℕ) : a (q*k+i)=a i := by
      simpa only [nsmul_eq_mul,Nat.cast_id,Nat.mul_comm k q,Nat.add_comm] using (ha.nsmul k) i
    simp_rw [h]
    push_cast
    ring

lemma periodicMean_multiple (a : ℕ → ℂ) (q k : ℕ) (hk : k ≠ 0)
    (ha : Function.Periodic a q) : periodicMean a (q*k)=periodicMean a q := by
  rw [periodicMean,periodic_sum_multiple a q k ha,periodicMean,Nat.cast_mul,mul_inv_rev]
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  field_simp

lemma periodicMean_of_dvd (a : ℕ → ℂ) (q t : ℕ) (ht : t ≠ 0)
    (hqt : q ∣ t) (ha : Function.Periodic a q) :
    periodicMean a t=periodicMean a q := by
  obtain ⟨k,rfl⟩ := hqt
  apply periodicMean_multiple a q k _ ha
  intro hz
  exact ht (by simp [hz])

lemma periodicMean_independent (a : ℕ → ℂ) (q t : ℕ) (hq : q ≠ 0) (ht : t ≠ 0)
    (haq : Function.Periodic a q) (hat : Function.Periodic a t) :
    periodicMean a q = periodicMean a t := by
  calc
    _ = periodicMean a (q*t) := (periodicMean_multiple a q t ht haq).symm
    _ = periodicMean a (t*q) := by rw [Nat.mul_comm]
    _ = _ := periodicMean_multiple a t q hq hat

lemma periodicMean_sum {I : Type*} (S : Finset I) (f : I → ℕ → ℂ) (t : ℕ) :
    periodicMean (fun n => ∑ i ∈ S, f i n) t = ∑ i ∈ S, periodicMean (f i) t := by
  simp only [periodicMean,mul_sum]
  rw [sum_comm]

lemma periodicMean_mul_left (a : ℕ → ℂ) (z : ℂ) (t : ℕ) :
    periodicMean (fun n => z*a n) t=z*periodicMean a t := by
  simp only [periodicMean,← mul_sum]
  ring

lemma prime_dvd_finset_prod_iff {I : Type*} (p : I → ℕ) (S : Finset I)
    (q : ℕ) (hq : q.Prime) : q ∣ ∏ i ∈ S, p i ↔ ∃ i ∈ S, q ∣ p i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [hq.not_dvd_one]
  | @insert i S hi ih =>
    simp only [prod_insert hi,hq.dvd_mul,ih,mem_insert]
    aesop

lemma mem_iff_dvd_prime_product {I : Type*} (p : I → ℕ)
    (hp : ∀i, (p i).Prime) (hinj : Function.Injective p) (S : Finset I) (i : I) :
    i ∈ S ↔ p i ∣ ∏ j ∈ S, p j := by
  rw [prime_dvd_finset_prod_iff p S (p i) (hp i)]
  constructor
  · intro hi; exact ⟨i,hi,dvd_rfl⟩
  · rintro ⟨j,hj,hij⟩
    have he : p i=p j := (Nat.dvd_prime (hp j)).mp hij |>.resolve_left (hp i).ne_one
    simpa only [hinj he] using hj

lemma prime_product_injective {I : Type*} (p : I → ℕ)
    (hp : ∀i, (p i).Prime) (hinj : Function.Injective p) :
    Function.Injective (fun S : Finset I => ∏ i ∈ S, p i) := by
  intro S T h
  change (∏ i ∈ S, p i) = (∏ i ∈ T, p i) at h
  ext i
  rw [mem_iff_dvd_prime_product p hp hinj,mem_iff_dvd_prime_product p hp hinj,h]

lemma bounded_prime_subsets_card {I : Type*} (p : I → ℕ)
    (hp : ∀i, (p i).Prime) (hinj : Function.Injective p)
    (S : Finset (Finset I)) (H : ℕ) (hS : ∀T∈S, ∏i∈T,p i≤H) : S.card≤H := by
  classical
  let f : S → Fin H := fun T => ⟨(∏i∈T.val,p i)-1, by
    have hpos : 0<∏i∈T.val,p i := prod_pos (fun i _ => (hp i).pos)
    have hle := hS T.val T.property
    omega⟩
  have hf : Function.Injective f := by
    intro T U h
    have hh := congrArg Fin.val h
    have hT : 0<∏i∈T.val,p i := prod_pos (fun i _ => (hp i).pos)
    have hU : 0<∏i∈U.val,p i := prod_pos (fun i _ => (hp i).pos)
    apply Subtype.ext
    apply prime_product_injective p hp hinj
    change (∏i∈T.val,p i)-1=(∏i∈U.val,p i)-1 at hh
    change (∏i∈T.val,p i)=(∏i∈U.val,p i)
    omega
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hf

lemma hasFourierBound_zero {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) : HasFourierBound ψ (fun _ => 0) 0 := by
  refine ⟨fun _ => 0, ?_, ?_⟩ <;> simp

lemma HasFourierBound.mono {R : Type*} [CommRing R] [Fintype R]
    {ψ : AddChar R ℂ} {w : R → ℂ} {C D : ℝ}
    (h : HasFourierBound ψ w C) (hCD : C≤D) : HasFourierBound ψ w D := by
  rcases h with ⟨a,ha,hb⟩
  exact ⟨a,ha,hb.trans hCD⟩

lemma HasFourierBound.mul_left {R : Type*} [CommRing R] [Fintype R]
    {ψ : AddChar R ℂ} {w : R → ℂ} {C : ℝ}
    (h : HasFourierBound ψ w C) (z : ℂ) : HasFourierBound ψ (fun x => z*w x) (‖z‖*C) := by
  rcases h with ⟨a,ha,hb⟩
  refine ⟨fun i => z*a i, ?_, ?_⟩
  · intro x
    dsimp only
    rw [ha,mul_sum]
    simp only [mul_assoc]
  · simpa only [norm_mul,← mul_sum] using mul_le_mul_of_nonneg_left hb (norm_nonneg z)

lemma hasFourierBound_sum {R I : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (S : Finset I) (w : I → R → ℂ) (C : I → ℝ)
    (h : ∀i∈S, HasFourierBound ψ (w i) (C i)) :
    HasFourierBound ψ (fun x => ∑i∈S,w i x) (∑i∈S,C i) := by
  classical
  choose a ha hb using h
  refine ⟨fun j => ∑i:S, a i i.property j, ?_, ?_⟩
  · intro x
    dsimp only
    calc
      _ = ∑i:S,w i x := (sum_coe_sort S _).symm
      _ = ∑i:S,∑j:R,a i i.property j*ψ (j*x) := by
        apply sum_congr rfl
        intro i _
        exact ha i i.property x
      _ = _ := by rw [sum_comm]; simp only [sum_mul]
  · calc
      _ ≤ ∑j:R, ∑i:S, ‖a i i.property j‖ := sum_le_sum fun _ _ => norm_sum_le _ _
      _ = ∑i:S, ∑j:R, ‖a i i.property j‖ := sum_comm
      _ ≤ ∑i:S,C i := sum_le_sum fun i _ => hb i i.property
      _ = _ := sum_coe_sort S _

lemma hasFourierBound_prod_budget {R I : Type*} [CommRing R] [Fintype R] [DecidableEq I]
    (ψ : AddChar R ℂ) (S : Finset I) (w : I → R → ℂ) (C : I → ℝ)
    (hw : ∀i∈S, HasFourierBound ψ (w i) (C i)) :
    HasFourierBound ψ (fun x => ∏i∈S,w i x) (∏i∈S,C i) := by
  induction S using Finset.induction_on with
  | empty => simpa only [prod_empty] using hasFourierBound_one ψ
  | @insert i S hi ih =>
    simpa only [prod_insert hi] using
      (hw i (mem_insert_self i S)).mul (ih (fun j hj => hw j (mem_insert_of_mem hj)))

section ActualWeight

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime]
  (R : Finset I) (c : ∀i, ZMod (p i))

omit [Fintype I] [DecidableEq I] in
lemma actualRootWeight_norm (n : ℕ) : ‖actualRootWeight p R c n‖≤(∏i∈R,p i : ℕ) := by
  unfold actualRootWeight
  rw [norm_prod,Nat.cast_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  split_ifs <;> simp

omit [Fintype I] in
lemma actualSieveWeight_norm (T : Finset I) (n : ℕ) : ‖actualSieveWeight p R T n‖≤1 := by
  unfold actualSieveWeight
  rw [norm_prod]
  apply prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro i _
  split_ifs
  · simp
  · simpa only [Complex.norm_real,Real.norm_eq_abs] using primeSieveWeight_abs_le (n : ZMod (p i))

omit [Fintype I] [DecidableEq I] in
lemma actualRootWeight_periodic (t : ℕ) (ht : ∀i∈R,p i∣t) :
    Function.Periodic (actualRootWeight p R c) t := by
  intro n
  unfold actualRootWeight
  apply prod_congr rfl
  intro i hi
  rw [Nat.cast_add,(ZMod.natCast_eq_zero_iff t (p i)).mpr (ht i hi),add_zero]

omit [Fintype I] in
lemma actualSieveWeight_periodic (T : Finset I) (t : ℕ) (ht : ∀i∈T,p i∣t) :
    Function.Periodic (actualSieveWeight p R T) t := by
  intro n
  unfold actualSieveWeight
  apply prod_congr rfl
  intro i hi
  rw [Nat.cast_add,(ZMod.natCast_eq_zero_iff t (p i)).mpr (ht i hi),add_zero]

omit [Fintype I] in
lemma actualTermWeight_periodic (T : Finset I) :
    Function.Periodic (fun n => actualRootWeight p R c n*actualSieveWeight p R T n)
      ((∏i∈R,p i)*(∏i∈T,p i)) := by
  apply Function.Periodic.mul
  · apply actualRootWeight_periodic
    intro i hi
    exact dvd_mul_of_dvd_left (dvd_prod_of_mem p hi) _
  · apply actualSieveWeight_periodic
    intro i hi
    exact dvd_mul_of_dvd_right (dvd_prod_of_mem p hi) _

variable (q : ℕ) [NeZero q] (hpq : ∀i,p i∣q)

noncomputable def ringRootWeight (x : ZMod q) : ℂ :=
  ∏i∈R,(residueDensity (hpq i) (c i) x : ℂ)

noncomputable def ringSieveWeight (T : Finset I) (x : ZMod q) : ℂ :=
  ∏i∈T, if i∈R then 0 else (primeSieveWeight (p i) (ZMod.castHom (hpq i) (ZMod (p i)) x) : ℂ)

noncomputable def ringDivisorWeight (H : ℝ) (x : ZMod q) : ℂ :=
  ringRootWeight p R c q hpq x * ∑T∈(univ:Finset I).powerset,
    if ((∏i∈T,p i : ℕ):ℝ)≤H then (-1)^T.card * ringSieveWeight p R q hpq T x else 0

omit [Fintype I] [DecidableEq I] [NeZero q] in
lemma ringRootWeight_natCast (n : ℕ) :
    ringRootWeight p R c q hpq (n : ZMod q)=actualRootWeight p R c n := by
  simp only [ringRootWeight,residueDensity,map_natCast,actualRootWeight]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)),Complex.ofReal_natCast,Complex.ofReal_zero]

omit [Fintype I] [NeZero q] in
lemma ringSieveWeight_natCast (T : Finset I) (n : ℕ) :
    ringSieveWeight p R q hpq T (n : ZMod q)=actualSieveWeight p R T n := by
  simp only [ringSieveWeight,map_natCast,actualSieveWeight]

omit [NeZero q] in
lemma ringDivisorWeight_natCast (H : ℝ) (n : ℕ) :
    ringDivisorWeight p R c q hpq H (n : ZMod q)=actualDivisorWeight p R c H n := by
  simp only [ringDivisorWeight,ringRootWeight_natCast,ringSieveWeight_natCast,actualDivisorWeight]

omit [Fintype I] in
lemma ringRootWeight_fourier :
    HasFourierBound (ZMod.stdAddChar (N:=q)) (ringRootWeight p R c q hpq) (∏i∈R,p i : ℕ) := by
  rw [Nat.cast_prod]
  exact hasFourierBound_prod_budget _ R _ _ (fun i _ =>
    residueDensity_fourier_dvd (hpq i) _ (ZMod.isPrimitive_stdAddChar q) (c i))

omit [Fintype I] in
lemma ringSieveWeight_fourier (T : Finset I) :
    HasFourierBound (ZMod.stdAddChar (N:=q)) (ringSieveWeight p R q hpq T) 1 := by
  apply hasFourierBound_prod
  intro i _
  by_cases hi : i∈R
  · simp only [ite_eq_left hi]
    exact (hasFourierBound_zero _).mono zero_le_one
  · simp only [ite_eq_right hi]
    exact primeSieveWeight_fourier_dvd (hpq i) _ (ZMod.isPrimitive_stdAddChar q)

lemma ringDivisorWeight_fourier (hinj : Function.Injective p) (H : ℝ) (hH : 0≤H) :
    HasFourierBound (ZMod.stdAddChar (N:=q)) (ringDivisorWeight p R c q hpq H)
      ((∏i∈R,p i : ℕ)*H) := by
  classical
  let S := (univ:Finset I).powerset.filter (fun T => ((∏i∈T,p i : ℕ):ℝ)≤H)
  have he (x : ZMod q) : ringDivisorWeight p R c q hpq H x=
      ringRootWeight p R c q hpq x*∑T∈S,(-1)^T.card*ringSieveWeight p R q hpq T x := by
    simp [ringDivisorWeight,S,sum_filter]
  have hf := hasFourierBound_sum (ZMod.stdAddChar (N:=q)) S
    (fun T x => (-1)^T.card*ringSieveWeight p R q hpq T x) (fun _ => 1) (by
      intro T _
      simpa only [norm_pow,norm_neg,norm_one,one_pow,one_mul] using
        (ringSieveWeight_fourier p R q hpq T).mul_left ((-1)^T.card))
  have hcard : (S.card:ℝ)≤H := by
    have h := bounded_prime_subsets_card p (fun i => Fact.out) hinj S ⌊H⌋₊ (by
      intro T hT
      exact Nat.le_floor (mem_filter.mp hT).2)
    have hnat : (S.card:ℝ)≤⌊H⌋₊ := by exact_mod_cast h
    exact hnat.trans (Nat.floor_le hH)
  have hmul := (ringRootWeight_fourier p R c q hpq).mul hf
  simp only [sum_const,nsmul_eq_mul,mul_one] at hmul
  simpa only [← he] using hmul.mono (mul_le_mul_of_nonneg_left hcard (by positivity))

end ActualWeight

section CompleteWeight

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (R : Finset I) (c : ∀i, ZMod (p i))

noncomputable def actualCompleteWeight (n : ℕ) : ℂ :=
  actualRootWeight p R c n * ∏i, (1 - if i∈R then 0 else
    (primeSieveWeight (p i) (n : ZMod (p i)) : ℂ))

omit [DecidableEq I] in
lemma prime_subset_product_le (T : Finset I) : (∏i∈T,p i) ≤ ∏i,p i := by
  exact prod_le_prod_of_subset_of_one_le (subset_univ T)
    (fun i _ _ => (Fact.out : (p i).Prime).one_le)

lemma actualDivisorWeight_complete (n : ℕ) :
    actualDivisorWeight p R c ((∏i,p i : ℕ) : ℝ) n=actualCompleteWeight p R c n := by
  unfold actualDivisorWeight actualCompleteWeight
  congr 1
  have h (T : Finset I) : ((∏i∈T,p i : ℕ) : ℝ)≤((∏i,p i : ℕ):ℝ) := by
    exact_mod_cast prime_subset_product_le p T
  simp only [ite_eq_left (h _),actualSieveWeight]
  exact finite_complete_sieve univ _

lemma actualCompleteWeight_periodic (t : ℕ) (ht : ∀i,p i∣t) :
    Function.Periodic (actualCompleteWeight p R c) t := by
  intro n
  unfold actualCompleteWeight
  rw [actualRootWeight_periodic p R c t (fun i _ => ht i) n]
  congr 1
  apply prod_congr rfl
  intro i _
  rw [Nat.cast_add,(ZMod.natCast_eq_zero_iff t (p i)).mpr (ht i),add_zero]

variable (hinj : Function.Injective p) (b : ℚ)
  (hb : b.den∣∏i,primaryModulus b.den (p i))

lemma primaryModelCoefficient_complete (H : ℝ) (htwo : ∀i,p i=2 → i∈R) :
    primaryModelCoefficient p hinj b hb R c H =
      if ((∏i∈primaryActive p b.den\R,p i : ℕ) : ℝ)≤H then
        periodicMean (fun n => actualCompleteWeight p R c (n+1)*
          expPhase ((b:ℝ)*(n+1)^2)) (∏i,primaryModulus b.den (p i)) else 0 := by
  have hfull : ((∏i∈primaryActive p b.den\R,p i : ℕ):ℝ)≤((∏i,p i : ℕ):ℝ) := by
    exact_mod_cast prime_subset_product_le p (primaryActive p b.den\R)
  have hmean := actualDivisorWeight_coefficient p hinj b hb R c ((∏i,p i : ℕ):ℝ)
  simp_rw [actualDivisorWeight_complete] at hmean
  rw [hmean,primary_coefficient_small p hinj b hb R c _ htwo hfull]
  unfold primaryModelCoefficient
  split_ifs <;> simp_all
  exfalso
  linarith

end CompleteWeight

noncomputable def smallQuadraticModulus (p : ℕ) : ℕ := if p=2 then 8 else p

lemma smallQuadraticModulus_pos {p : ℕ} (hp : p.Prime) : 0<smallQuadraticModulus p := by
  unfold smallQuadraticModulus
  split_ifs
  · norm_num
  · exact hp.pos

instance {p : ℕ} [Fact p.Prime] : NeZero (smallQuadraticModulus p) :=
  ⟨(smallQuadraticModulus_pos (Fact.out : p.Prime)).ne'⟩

lemma prime_dvd_smallQuadraticModulus (p : ℕ) : p∣smallQuadraticModulus p := by
  unfold smallQuadraticModulus
  split_ifs with h
  · subst p; norm_num
  · exact dvd_rfl

lemma smallQuadraticModuli_pairwise {I : Type*} (p : I → ℕ)
    (hp : ∀i,(p i).Prime) (hinj : Function.Injective p) :
    Pairwise (fun i j => (smallQuadraticModulus (p i)).Coprime (smallQuadraticModulus (p j))) := by
  intro i j hij
  have hc : (p i).Coprime (p j) := (Nat.coprime_primes (hp i) (hp j)).mpr (hinj.ne hij)
  unfold smallQuadraticModulus
  split_ifs with hi hj hj
  · exact False.elim (hij (hinj (hi.trans hj.symm)))
  · simpa only [hi,show 2^3=8 by norm_num] using hc.pow_left 3
  · simpa only [hj,show 2^3=8 by norm_num] using hc.pow_right 3
  · exact hc

noncomputable def smallRootSquare (p : ℕ) (c : ZMod p) : ZMod (smallQuadraticModulus p) :=
  if p=2 then 1 else (c.val : ZMod (smallQuadraticModulus p))^2

lemma small_root_quadratic {p : ℕ} [Fact p.Prime] (c : ZMod p)
    (hc : p=2 → c=1) (ψ : AddChar (ZMod (smallQuadraticModulus p)) ℂ) :
    (𝔼 x : ZMod (smallQuadraticModulus p),
      (residueDensity (prime_dvd_smallQuadraticModulus p) c x : ℂ)*ψ (x^2))=
        ψ (smallRootSquare p c) := by
  by_cases h2 : p=2
  · subst p
    rw [hc rfl]
    exact odd_root_quadratic_small (by norm_num [smallQuadraticModulus])
      (by simp [smallQuadraticModulus]) ψ
  · have hm : smallQuadraticModulus p=p := ite_eq_right h2
    have he (m : ℕ) [NeZero m] (hpm : p∣m) (hm : m=p) (φ : AddChar (ZMod m) ℂ) :
        (𝔼 x : ZMod m, (residueDensity hpm c x : ℂ)*φ (x^2))=φ ((c.val : ZMod m)^2) := by
      subst m
      simpa only [ZMod.natCast_zmod_val] using residueDensity_self_quadratic p c φ
    unfold smallRootSquare
    rw [ite_eq_right h2]
    exact he _ (prime_dvd_smallQuadraticModulus p) hm ψ

section CompleteCRT

variable {I : Type*} [Fintype I] [DecidableEq I]
    (p m : I → ℕ) [∀i, Fact (p i).Prime] [∀i, NeZero (m i)]
    (hm : ∀i, p i∣m i) (R : Finset I) (c : ∀i, ZMod (p i))

lemma crt_complete_coefficient {L : ℕ} [NeZero L]
    (e : ZMod L ≃+* ∀i, ZMod (m i)) (ψ : AddChar (ZMod L) ℂ) :
    (𝔼 x : ZMod L, (∏i,localRootWeight p m hm R c i (e x i))*
      (∏i,(1-localSieveWeight p m hm R i (e x i)))*ψ (x^2))=
      ∏i,(𝔼 x : ZMod (m i), localRootWeight p m hm R c i x*
        (1-localSieveWeight p m hm R i x)*
        coordinateChar (ψ.compAddMonoidHom e.symm.toAddMonoidHom) i (x^2)) := by
  rw [quadratic_mean_equiv e ψ (fun x => (∏i,localRootWeight p m hm R c i (x i))*
    (∏i,(1-localSieveWeight p m hm R i (x i))))]
  simp_rw [← prod_mul_distrib]
  exact product_quadratic_mean (I := I) (R := fun i => ZMod (m i))
    (ψ.compAddMonoidHom e.symm.toAddMonoidHom)
    (fun i x => localRootWeight p m hm R c i x*(1-localSieveWeight p m hm R i x))

lemma periodicMean_crt_complete {L : ℕ} [NeZero L]
    (e : ZMod L ≃+* ∀i, ZMod (m i)) (b : ℚ) (hbL : b.den∣L) :
    periodicMean (fun n => actualCompleteWeight p R c (n+1)*expPhase ((b:ℝ)*(n+1)^2)) L=
      ∏i,(𝔼 x : ZMod (m i), localRootWeight p m hm R c i x*
        (1-localSieveWeight p m hm R i x)*
        coordinateChar ((rationalChar b |>.compAddMonoidHom
          (ZMod.castHom hbL (ZMod b.den)).toAddMonoidHom).compAddMonoidHom e.symm.toAddMonoidHom) i (x^2)) := by
  let w : ZMod L → ℂ := fun x => (∏i,localRootWeight p m hm R c i (e x i))*
    ∏i,(1-localSieveWeight p m hm R i (e x i))
  have hw (n : ℕ) : w (n:ZMod L)=actualCompleteWeight p R c n := by
    simp only [w,map_natCast,Pi.natCast_apply,localRootWeight_natCast,localSieveWeight_natCast]
    unfold actualCompleteWeight actualRootWeight
    congr 1
    rw [← prod_filter]
    simp only [filter_mem_eq_inter,univ_inter]
  rw [show (fun n : ℕ => actualCompleteWeight p R c (n+1)*expPhase ((b:ℝ)*(n+1)^2))=
      (fun n : ℕ => w ((n+1:ℕ):ZMod L)*expPhase ((b:ℝ)*(n+1)^2)) by
    funext n; rw [hw]]
  rw [rational_periodic_coefficient b hbL w]
  exact crt_complete_coefficient p m hm R c e
    ((rationalChar b).compAddMonoidHom (ZMod.castHom hbL (ZMod b.den)).toAddMonoidHom)

end CompleteCRT

noncomputable def circleDistance (t : ℝ) : ℝ := |t - round t|

@[simp] lemma expPhase_zero : expPhase 0 = 1 := by simp [expPhase]
@[simp] lemma norm_expPhase (t : ℝ) : ‖expPhase t‖ = 1 := Circle.norm_coe _

lemma expPhase_add (s t : ℝ) : expPhase (s+t) = expPhase s * expPhase t := by
  simp [expPhase, AddChar.map_add_eq_mul]

lemma expPhase_neg (t : ℝ) : expPhase (-t) = conj (expPhase t) := by
  simp only [expPhase, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

lemma expPhase_sub (s t : ℝ) : expPhase (s-t) = expPhase s * conj (expPhase t) := by
  rw [sub_eq_add_neg, expPhase_add, expPhase_neg]

lemma expPhase_nat_mul (t : ℝ) (n : ℕ) : expPhase (n*t) = expPhase t^n := by
  simpa only [expPhase, nsmul_eq_mul, Circle.coe_pow] using congrArg (fun z : Circle => (z : ℂ))
    (AddChar.map_nsmul_eq_pow Real.fourierChar n t)

lemma expPhase_int (n : ℤ) : expPhase n = 1 := by
  change Complex.exp (↑(2 * Real.pi * (n : ℝ)) * Complex.I) = 1
  rw [show (↑(2 * Real.pi * (n : ℝ)) : ℂ) * Complex.I =
    (n : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

lemma expPhase_sub_int (t : ℝ) (n : ℤ) : expPhase (t-n) = expPhase t := by
  rw [expPhase_sub, expPhase_int, map_one, mul_one]

lemma circleDistance_nonneg (t : ℝ) : 0 ≤ circleDistance t := abs_nonneg _

lemma circleDistance_le_half (t : ℝ) : circleDistance t ≤ 1/2 := abs_sub_round t

lemma circleDistance_le_abs_sub_int (t : ℝ) (n : ℤ) : circleDistance t ≤ |t-n| :=
  round_le t n

lemma circleDistance_le_abs (t : ℝ) : circleDistance t ≤ |t| := by
  simpa using circleDistance_le_abs_sub_int t 0

lemma circleDistance_sub_le (s t : ℝ) : circleDistance (s-t) ≤
    |(s-round s)-(t-round t)| := by
  convert circleDistance_le_abs_sub_int (s-t) (round s-round t) using 1
  push_cast
  congr 1
  ring

lemma expPhase_sub_one_lower (t : ℝ) : 4*circleDistance t ≤ ‖expPhase t-1‖ := by
  let u := t-(round t : ℝ)
  have hu : |u| ≤ 1/2 := abs_sub_round t
  have hp := Real.pi_pos
  have hs := Real.mul_abs_le_abs_sin (x := Real.pi*u)
    (by rw [abs_mul, abs_of_pos hp]; nlinarith)
  rw [abs_mul, abs_of_pos hp] at hs
  have hmul : 2/Real.pi*(Real.pi*|u|)=2*|u| := by field_simp
  rw [hmul] at hs
  rw [← expPhase_sub_int t (round t)]
  change 4*|u| ≤ ‖Complex.exp (↑(2*Real.pi*u)*Complex.I)-1‖
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2*Real.pi*u/2=Real.pi*u by ring, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ)<2)]
  linarith

lemma linear_phase_sum_trivial (t : ℝ) (L : ℕ) :
    ‖∑ m ∈ range L, expPhase (m*t)‖ ≤ L := by
  calc
    _ ≤ ∑ m ∈ range L, ‖expPhase (m*t)‖ := norm_sum_le _ _
    _ = L := by simp

lemma linear_phase_sum_distance (t : ℝ) (L : ℕ) (ht : 0 < circleDistance t) :
    ‖∑ m ∈ range L, expPhase (m*t)‖ ≤ 1 / (2*circleDistance t) := by
  have hz : expPhase t ≠ 1 := by
    intro he
    have := expPhase_sub_one_lower t
    rw [he, sub_self, norm_zero] at this
    linarith
  simp_rw [expPhase_nat_mul]
  rw [geom_sum_eq hz, norm_div]
  have hn : ‖expPhase t ^ L - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖expPhase t^L‖+‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp; norm_num
  calc
    _ ≤ 2 / (4*circleDistance t) :=
      div_le_div₀ (by positivity) hn (by positivity) (expPhase_sub_one_lower t)
    _ = 1 / (2*circleDistance t) := by ring

noncomputable def phaseBound (M t : ℝ) : ℝ :=
  if circleDistance t = 0 then M else min M (circleDistance t)⁻¹

lemma phaseBound_nonneg {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : 0 ≤ phaseBound M t := by
  unfold phaseBound
  split_ifs
  · exact hM
  · exact le_min hM (inv_nonneg.mpr (circleDistance_nonneg t))

lemma phaseBound_le (M t : ℝ) : phaseBound M t ≤ M := by
  unfold phaseBound
  split_ifs
  · rfl
  · exact min_le_left _ _

end SquareDifference
end

end OAI
