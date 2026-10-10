import OAI.NumberTheory.PrimeGaps.DetectorMoments

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def primeCharacterPrefix (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)

noncomputable def primeCharacterError (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  primeCharacterPrefix x χ-if χ=1 then (x:ℂ) else 0

theorem character_prefix_orthogonality (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    ∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterPrefix x χ=
      (q.totient:ℂ)*(residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c:ℂ) := by
  classical
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hcop
  have he (n : ℕ) : (c:ZMod q)=(n:ZMod q) ↔ n%q=c := by
    rw [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt hc]
    exact eq_comm
  unfold primeCharacterPrefix
  simp_rw [Finset.mul_sum,←mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [←Finset.sum_mul,DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu,he]
  simp only [residuePrefix,residueSlice,Complex.ofReal_sum,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem character_error_orthogonality (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    ∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterError x χ=
      (q.totient:ℂ)*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient:ℝ):ℂ) := by
  classical
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hcop
  have huinv : IsUnit (c:ZMod q)⁻¹ := by
    obtain ⟨u,hu⟩ := hu
    rw [←hu,ZMod.inv_coe_unit]
    exact (u⁻¹).isUnit
  have ht : (q.totient:ℂ)≠0 := by exact_mod_cast ne_of_gt (Nat.totient_pos.mpr hq)
  simp only [primeCharacterError,mul_sub,Finset.sum_sub_distrib]
  rw [character_prefix_orthogonality x hq hc hcop]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,MulChar.one_apply huinv,one_mul]
  push_cast
  field_simp

theorem endpointClassError_le_character_sum (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient|≤
      (∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError x χ‖)/(q.totient:ℝ) := by
  have hphi : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (le_div_iff₀ hphi).mpr
  have hh := character_error_orthogonality x hq hc hcop
  calc
    _ = ‖(q.totient:ℂ)*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient:ℝ):ℂ)‖ := by
      rw [norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,mul_comm]
    _ = ‖∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterError x χ‖ := congrArg norm hh.symm
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ (c:ZMod q)⁻¹*primeCharacterError x χ‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro χ _
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

noncomputable def characterMeanError (x : ℝ) (q : ℕ) : ℝ :=
  (∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError x χ‖)/(q.totient:ℝ)

theorem characterMeanError_nonneg (x : ℝ) (q : ℕ) : 0≤characterMeanError x q := by
  unfold characterMeanError
  positivity

theorem endpointError_le_characterMeanError (x : ℝ) {q : ℕ} (hq : 0<q) :
    (endpointError x q:ℝ)≤characterMeanError x q := by
  change (endpointError x q:ℝ)≤(⟨characterMeanError x q,characterMeanError_nonneg x q⟩:NNReal)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro c hc
  split_ifs with hcop
  · exact NNReal.coe_le_coe.mp (endpointClassError_le_character_sum x hq (Finset.mem_range.mp hc) hcop)
  · exact bot_le

theorem endpointErrors_le_characterMeanErrors (x : ℝ) (Q : ℕ) :
    (∑ q∈Finset.Icc 1 Q,(endpointError x q:ℝ))≤
      ∑ q∈Finset.Icc 1 Q,characterMeanError x q := by
  apply Finset.sum_le_sum
  intro q hq
  exact endpointError_le_characterMeanError x (Finset.mem_Icc.mp hq).1

theorem vonMangoldt_noncoprime_sum_le (X : ℕ) {q : ℕ} (hq : 0<q) :
    (∑ n∈(Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n)≤(Nat.log 2 X:ℝ)*Real.log q := by
  classical
  let S := (Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q ∧ ArithmeticFunction.vonMangoldt n≠0)
  have he : (∑ n∈(Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n)=∑ n∈S,ArithmeticFunction.vonMangoldt n := by
    simp only [S,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hcop : Nat.Coprime n q <;> by_cases hn : ArithmeticFunction.vonMangoldt n=0 <;> simp [hcop,hn]
  rw [he]
  have hsub : S⊆(q^(Nat.log 2 X)).divisors := by
    intro n hn
    obtain ⟨hnI,hnq,hnv⟩ := Finset.mem_filter.mp hn
    obtain ⟨p,k,hp,_hk,hpkn⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hnv
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    have hdp : p∣q := by
      by_contra hd
      have hc := (hp'.coprime_iff_not_dvd).mpr hd
      exact hnq (hpkn ▸ hc.pow_left k)
    have hkX : k≤Nat.log 2 X := by
      apply Nat.le_log_of_pow_le (by norm_num : 1<2)
      calc
        2^k≤p^k := Nat.pow_le_pow_left hp'.two_le k
        _ = n := hpkn
        _ ≤ X := (Finset.mem_Ioc.mp hnI).2
    apply Nat.mem_divisors.mpr
    refine ⟨?_,pow_ne_zero _ (ne_of_gt hq)⟩
    rw [←hpkn]
    exact (pow_dvd_pow_of_dvd hdp k).trans (pow_dvd_pow q hkX)
  calc
    _ ≤ ∑ n∈(q^(Nat.log 2 X)).divisors,ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log ((q^(Nat.log 2 X):ℕ):ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ = _ := by rw [Nat.cast_pow,Real.log_pow]

theorem primitiveCharacter_eq_one_iff {q : ℕ} (hq : 0<q) (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter=1 ↔ χ=1 := by
  have : NeZero q := ⟨ne_of_gt hq⟩
  constructor
  · intro h
    rw [←DirichletCharacter.changeLevel_primitiveCharacter χ,h,DirichletCharacter.changeLevel_one]
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

theorem primeCharacterPrefix_primitive_difference (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterPrefix x χ-primeCharacterPrefix x χ.primitiveCharacter‖≤
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have hsame (n : ℕ) (hn : Nat.Coprime n q) :
      χ.primitiveCharacter (n:ZMod χ.conductor)=χ (n:ZMod q) := by
    simpa only [Int.cast_natCast] using χ.primitiveCharacter_apply_of_isCoprime hn.isCoprime
  have hzero (n : ℕ) (hn : ¬Nat.Coprime n q) : χ (n:ZMod q)=0 :=
    χ.map_nonunit (fun h => hn ((ZMod.isUnit_iff_coprime n q).mp h))
  calc
    _ = ‖∑ n∈Finset.Ioc 0 ⌊x⌋₊,(χ (n:ZMod q)-χ.primitiveCharacter (n:ZMod χ.conductor))*
        (ArithmeticFunction.vonMangoldt n:ℂ)‖ := by
      congr 1
      simp only [primeCharacterPrefix,sub_mul,Finset.sum_sub_distrib]
    _ ≤ ∑ n∈Finset.Ioc 0 ⌊x⌋₊,‖(χ (n:ZMod q)-χ.primitiveCharacter (n:ZMod χ.conductor))*
        (ArithmeticFunction.vonMangoldt n:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n∈(Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬Nat.Coprime n q),ArithmeticFunction.vonMangoldt n := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : Nat.Coprime n q
      · simp [hn,hsame n hn]
      · simp only [ite_eq_left hn,hzero n hn,zero_sub,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
          (χ.primitiveCharacter.norm_le_one _)
    _ ≤ _ := vonMangoldt_noncoprime_sum_le _ hq

theorem primeCharacterError_primitive_difference (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter‖≤
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have he : primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter=
      primeCharacterPrefix x χ-primeCharacterPrefix x χ.primitiveCharacter := by
    simp only [primeCharacterError,primitiveCharacter_eq_one_iff hq χ]
    ring
  rw [he]
  exact primeCharacterPrefix_primitive_difference x hq χ

theorem primeCharacterError_le_primitive (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterError x χ‖≤‖primeCharacterError x χ.primitiveCharacter‖+
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have hn := norm_add_le (primeCharacterError x χ.primitiveCharacter)
    (primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter)
  rw [add_sub_cancel] at hn
  exact hn.trans (add_le_add_right (primeCharacterError_primitive_difference x hq χ) _)

theorem characterMeanError_le_primitive_average (x : ℝ) {q : ℕ} (hq : 0<q) :
    characterMeanError x q≤
      (∑ χ : DirichletCharacter ℂ q,‖primeCharacterError x χ.primitiveCharacter‖)/(q.totient:ℝ)+
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hphi : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hcard : Fintype.card (DirichletCharacter ℂ q)=q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  unfold characterMeanError
  calc
    _ ≤ (∑ χ : DirichletCharacter ℂ q,(‖primeCharacterError x χ.primitiveCharacter‖+
        (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q))/(q.totient:ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun χ _ => primeCharacterError_le_primitive x hq χ)) hphi.le
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul,add_div]
      congr 1
      exact mul_div_cancel_left₀ _ hphi.ne'

noncomputable def primitiveErrorMass (x : ℝ) (d : ℕ) : ℝ :=
  ∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ d)).filter DirichletCharacter.IsPrimitive,
    ‖primeCharacterError x χ‖

theorem primitiveErrorMass_nonneg (x : ℝ) (d : ℕ) : 0≤primitiveErrorMass x d := by
  unfold primitiveErrorMass
  positivity

theorem induced_primitive_sum_le (x : ℝ) {q : ℕ} (hq : 0<q) :
    (∑ χ : DirichletCharacter ℂ q,‖primeCharacterError x χ.primitiveCharacter‖)≤
      ∑ d∈q.divisors,primitiveErrorMass x d := by
  classical
  let i : DirichletCharacter ℂ q → Sigma (DirichletCharacter ℂ) :=
    fun χ => ⟨χ.conductor,χ.primitiveCharacter⟩
  let lift : Sigma (DirichletCharacter ℂ) → DirichletCharacter ℂ q :=
    fun p => if h : p.1∣q then DirichletCharacter.changeLevel h p.2 else 1
  have hleft (χ : DirichletCharacter ℂ q) : lift (i χ)=χ := by
    dsimp [lift,i]
    rw [dite_eq_left χ.conductor_dvd_level,DirichletCharacter.changeLevel_primitiveCharacter]
  have hi : Function.Injective i := by
    intro χ ψ h
    simpa only [hleft] using congrArg lift h
  let S := q.divisors.sigma (fun d =>
    (Finset.univ : Finset (DirichletCharacter ℂ d)).filter DirichletCharacter.IsPrimitive)
  have hsub : Finset.univ.image i⊆S := by
    intro p hp
    obtain ⟨χ,_,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_sigma.mpr ⟨Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level,ne_of_gt hq⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,χ.primitiveCharacter_isPrimitive⟩⟩
  calc
    _ = ∑ p∈Finset.univ.image i,‖primeCharacterError x p.2‖ := by
      rw [Finset.sum_image (fun _ _ _ _ h => hi h)]
    _ ≤ ∑ p∈S,‖primeCharacterError x p.2‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
    _ = _ := by rw [Finset.sum_sigma]; rfl

theorem endpointError_le_primitive_conductors (x : ℝ) {q : ℕ} (hq : 0<q) :
    (endpointError x q:ℝ)≤(∑ d∈q.divisors,primitiveErrorMass x d)/(q.totient:ℝ)+
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  apply (endpointError_le_characterMeanError x hq).trans
  apply (characterMeanError_le_primitive_average x hq).trans
  exact add_le_add_left (div_le_div_of_nonneg_right (induced_primitive_sum_le x hq) (Nat.cast_nonneg _)) _

theorem nat_le_card_divisors_mul_totient (q : ℕ) : q≤q.divisors.card*q.totient := by
  calc
    q = ∑ d∈q.divisors,d.totient := (Nat.sum_totient q).symm
    _ ≤ ∑ _d∈q.divisors,q.totient := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2))
        (Nat.totient_dvd_of_dvd (Nat.mem_divisors.mp hd).1)
    _ = _ := by simp

theorem divisorMultiplicity_two (q : ℕ) : divisorMultiplicity 2 q=q.divisors.card := by
  rw [show 2=1+1 from rfl,divisorMultiplicity_succ]
  calc
    _ = ∑ _d∈q.divisors,1 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [divisorMultiplicity,ArithmeticFunction.zeta_apply_ne
        (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)).ne']
    _ = _ := by simp

theorem sum_totient_reciprocal_le (Q : ℕ) :
    (∑ q∈Finset.Icc 1 Q,(1:ℝ)/(q.totient:ℝ))≤(harmonic Q:ℝ)^2 := by
  apply le_trans (Finset.sum_le_sum (g:=fun q => (divisorMultiplicity 2 q:ℝ)/(q:ℝ)) ?_)
    (sum_divisorMultiplicity_reciprocal_le 2 Q)
  intro q hq
  have hq0 : (0:ℝ)<q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  have hp : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp hq).1
  rw [divisorMultiplicity_two,div_le_div_iff₀ hp hq0,one_mul]
  exact_mod_cast nat_le_card_divisors_mul_totient q

theorem reciprocal_totient_divisor_sum_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q.totient : ℝ)) ≤
      (∑ d ∈ Finset.Icc 1 Q, f d / (d.totient : ℝ)) * (harmonic Q : ℝ)^2 := by
  classical
  let s := (Finset.Icc 1 Q).sigma fun q => q.divisors
  let t := (Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)
  let e : (a : ℕ) × ℕ → ℕ × ℕ := fun x => (x.2, x.1/x.2)
  have he_mem : ∀ x ∈ s, e x ∈ t := by
    rintro ⟨q,d⟩ hx
    obtain ⟨hq, hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq1,hqQ⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hdq,hq0⟩ := Nat.mem_divisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq1
    have hdle : d ≤ q := Nat.le_of_dvd hq1 hdq
    have hdivpos : 0 < q/d := Nat.div_pos hdle hd0
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hd0, hdle.trans hqQ⟩,
      Finset.mem_Icc.mpr ⟨hdivpos, (Nat.div_le_self q d).trans hqQ⟩⟩
  have he_inj : Set.InjOn e s := by
    rintro ⟨q,d⟩ hx ⟨q',d'⟩ hy he
    obtain ⟨hq,hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq',hd'⟩ := Finset.mem_sigma.mp hy
    have hed : d = d' := congrArg Prod.fst he
    have heq : q/d = q'/d' := congrArg Prod.snd he
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdq' : d' ∣ q' := (Nat.mem_divisors.mp hd').1
    have hqq : q = q' := by
      rw [← Nat.div_mul_cancel hdq, ← Nat.div_mul_cancel hdq', heq, hed]
    subst d'
    subst q'
    rfl
  have hsum : (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q.totient : ℝ)) ≤
      ∑ x ∈ s, f (e x).1 / (e x).1.totient / (e x).2.totient := by
    dsimp only [s]
    rw [Finset.sum_sigma]
    apply Finset.sum_le_sum
    intro q hq
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro d hd
    have hdq := (Nat.mem_divisors.mp hd).1
    have hq0 : 0<q := (Finset.mem_Icc.mp hq).1
    have hd0 : 0<d := Nat.pos_of_dvd_of_pos hdq hq0
    have hk0 : 0<q/d := Nat.div_pos (Nat.le_of_dvd hq0 hdq) hd0
    have ht : (d.totient:ℝ)*(q/d).totient≤q.totient := by
      have hh := Nat.totient_super_multiplicative d (q/d)
      rw [Nat.mul_div_cancel' hdq] at hh
      exact_mod_cast hh
    dsimp only [e]
    rw [div_div]
    exact div_le_div_of_nonneg_left (hf d) (mul_pos
      (by exact_mod_cast Nat.totient_pos.mpr hd0) (by exact_mod_cast Nat.totient_pos.mpr hk0)) ht
  apply hsum.trans
  calc
    _ = ∑ x ∈ s.image e, f x.1 / (x.1.totient : ℝ) / (x.2.totient : ℝ) := by
      rw [Finset.sum_image he_inj]
    _ ≤ ∑ x ∈ t, f x.1 / (x.1.totient : ℝ) / (x.2.totient : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr he_mem)
        (fun x _ _ => div_nonneg (div_nonneg (hf _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    _ = (∑ d∈Finset.Icc 1 Q,f d/(d.totient:ℝ))*(∑ k∈Finset.Icc 1 Q,(1:ℝ)/k.totient) := by
      simp only [t,Finset.sum_product,div_eq_mul_inv,one_mul,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_totient_reciprocal_le Q)
      (Finset.sum_nonneg (fun _ _ => div_nonneg (hf _) (Nat.cast_nonneg _)))

theorem endpointErrors_le_primitive_weighted_sum (x : ℝ) (Q : ℕ) :
    (∑ q∈Finset.Icc 1 Q,(endpointError x q:ℝ))≤
      (∑ d∈Finset.Icc 1 Q,primitiveErrorMass x d/(d.totient:ℝ))*(harmonic Q:ℝ)^2+
      (Q:ℝ)*(Nat.log 2 ⌊x⌋₊:ℝ)*Real.log Q := by
  calc
    _ ≤ ∑ q∈Finset.Icc 1 Q,((∑ d∈q.divisors,primitiveErrorMass x d)/(q.totient:ℝ)+
        (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q) :=
      Finset.sum_le_sum (fun q hq => endpointError_le_primitive_conductors x (Finset.mem_Icc.mp hq).1)
    _ = (∑ q∈Finset.Icc 1 Q,(∑ d∈q.divisors,primitiveErrorMass x d)/(q.totient:ℝ))+
        ∑ q∈Finset.Icc 1 Q,(Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := Finset.sum_add_distrib
    _ ≤ _ := by
      apply add_le_add (reciprocal_totient_divisor_sum_le _ (primitiveErrorMass_nonneg x) Q)
      calc
        _ ≤ ∑ _q∈Finset.Icc 1 Q,(Nat.log 2 ⌊x⌋₊:ℝ)*Real.log Q := by
          apply Finset.sum_le_sum
          intro q hq
          exact mul_le_mul_of_nonneg_left (Real.log_le_log
            (by exact_mod_cast (Finset.mem_Icc.mp hq).1) (by exact_mod_cast (Finset.mem_Icc.mp hq).2))
            (Nat.cast_nonneg _)
        _ = _ := by simp [mul_assoc]

noncomputable def arithmeticCutoff (T : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n≤T then f n else 0,by simp⟩

@[simp] theorem arithmeticCutoff_apply (T n : ℕ) (f : ArithmeticFunction ℝ) :
    arithmeticCutoff T f n=if n≤T then f n else 0 := rfl

theorem vaughan_identity (U V : ℕ) :
    ArithmeticFunction.vonMangoldt =
      arithmeticCutoff U ArithmeticFunction.vonMangoldt+
      arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*ArithmeticFunction.log-
      arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*
        arithmeticCutoff U ArithmeticFunction.vonMangoldt*(ArithmeticFunction.zeta:ArithmeticFunction ℝ)+
      ((ArithmeticFunction.moebius:ArithmeticFunction ℝ)-arithmeticCutoff V ArithmeticFunction.moebius)*
        (ArithmeticFunction.vonMangoldt-arithmeticCutoff U ArithmeticFunction.vonMangoldt)*
        (ArithmeticFunction.zeta:ArithmeticFunction ℝ) := by
  rw [←ArithmeticFunction.vonMangoldt_mul_zeta]
  have hmu : (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*ArithmeticFunction.zeta=1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  linear_combination
    (arithmeticCutoff U ArithmeticFunction.vonMangoldt-ArithmeticFunction.vonMangoldt)*hmu

noncomputable def vaughanSecondCoefficient (U : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.vonMangoldt-arithmeticCutoff U ArithmeticFunction.vonMangoldt)*
    (ArithmeticFunction.zeta:ArithmeticFunction ℝ)

theorem vaughanSecondCoefficient_eq (U n : ℕ) :
    vaughanSecondCoefficient U n=
      ∑ d∈n.divisors,if U<d then ArithmeticFunction.vonMangoldt d else 0 := by
  rw [vaughanSecondCoefficient,ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_congr rfl
  intro d _
  change ArithmeticFunction.vonMangoldt d-(if d≤U then ArithmeticFunction.vonMangoldt d else 0)=_
  by_cases hd : d≤U
  · simp [hd,not_lt_of_ge hd]
  · simp [hd,lt_of_not_ge hd]

theorem vaughanSecondCoefficient_nonneg (U n : ℕ) :
    0≤vaughanSecondCoefficient U n := by
  rw [vaughanSecondCoefficient_eq]
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

theorem vaughanSecondCoefficient_le_log (U n : ℕ) :
    vaughanSecondCoefficient U n≤Real.log n := by
  rw [vaughanSecondCoefficient_eq,←ArithmeticFunction.vonMangoldt_sum]
  apply Finset.sum_le_sum
  intro d _
  split_ifs
  · rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

theorem vaughanSecondCoefficient_zero_of_le {U n : ℕ} (hn : n≤U) :
    vaughanSecondCoefficient U n=0 := by
  rw [vaughanSecondCoefficient_eq]
  apply Finset.sum_eq_zero
  intro d hd
  have hdle := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
    (Nat.mem_divisors.mp hd).1
  exact ite_eq_right (by omega)

end LargePrimeGaps

end OAI
