import OAI.NumberTheory.PrimeGaps.VaughanIdentity

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

open scoped ComplexConjugate

theorem sequenceSize_le_of_norm_le {N : ℕ} (a : Fin N→ℂ) {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀ n,‖a n‖ ≤ A) : sequenceSize a ≤ Real.sqrt N*A := by
  have hh : sequenceSize a^2 ≤ (N:ℝ)*A^2 := by
    rw [sequenceSize_sq]
    calc
      _ ≤ ∑ _n:Fin N,A^2 := Finset.sum_le_sum (fun n _=>pow_le_pow_left₀ (norm_nonneg _) (ha n) 2)
      _ = _ := by simp
  have hs : (Real.sqrt (N:ℝ))^2=(N:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  apply (sq_le_sq₀ (sequenceSize_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hA)).mp
  simpa only [mul_pow,hs] using hh

noncomputable def vaughanFirstSequence (V M : ℕ) : Fin M→ℂ :=
  fun m=>if V < m.val then (ArithmeticFunction.moebius m.val:ℂ) else 0

noncomputable def vaughanSecondSequence (U N : ℕ) : Fin N→ℂ :=
  fun n=>(vaughanSecondCoefficient U n.val:ℂ)

theorem vaughanFirstSequence_norm_le (V M : ℕ) (m : Fin M) :
    ‖vaughanFirstSequence V M m‖ ≤ 1 := by
  unfold vaughanFirstSequence
  split_ifs
  · rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=m.val))
  · simp

theorem vaughanFirstSequence_size_le (V M : ℕ) :
    sequenceSize (vaughanFirstSequence V M) ≤ Real.sqrt M := by
  simpa only [mul_one] using sequenceSize_le_of_norm_le (vaughanFirstSequence V M)
    zero_le_one (vaughanFirstSequence_norm_le V M)

theorem vaughanSecondSequence_norm_le (U N : ℕ) (n : Fin N) :
    ‖vaughanSecondSequence U N n‖ ≤ Real.log N := by
  rw [vaughanSecondSequence,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (vaughanSecondCoefficient_nonneg _ _)]
  exact (vaughanSecondCoefficient_le_log _ _).trans (log_nat_monotone n.isLt.le)

theorem vaughanSecondSequence_size_le (U N : ℕ) :
    sequenceSize (vaughanSecondSequence U N) ≤ Real.sqrt N*Real.log N := by
  apply sequenceSize_le_of_norm_le _ _ (vaughanSecondSequence_norm_le U N)
  simpa using log_nat_monotone (Nat.zero_le N)

theorem vaughan_typeII_block_mean (Q X U V M N k : ℕ) (hk : N ≤ 2^k)
    (p : Fin M→Prop) (r : Fin N→Prop) :
    primitiveCharacterMean Q (fun _ χ=>‖triangularCharacterSum
      (sequenceMask p (vaughanFirstSequence V M))
      (sequenceMask r (vaughanSecondSequence U N)) (fun m=>X/m.val+1) χ‖) ≤
      ((k:ℝ)+1)*sieveBilinearConstant Q M N*Real.sqrt M*(Real.sqrt N*Real.log N) := by
  have h:=triangular_primitive_mean_le Q M N k hk
    (sequenceMask p (vaughanFirstSequence V M))
    (sequenceMask r (vaughanSecondSequence U N)) (fun m=>X/m.val+1)
  apply h.trans
  have hC : 0 ≤ ((k:ℝ)+1)*sieveBilinearConstant Q M N :=
    mul_nonneg (by positivity) (sieveBilinearConstant_nonneg _ _ _)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left
      ((sequenceMask_size_le _ _).trans (vaughanFirstSequence_size_le _ _)) hC
  · exact (sequenceMask_size_le _ _).trans (vaughanSecondSequence_size_le _ _)
  · exact sequenceSize_nonneg _
  · exact mul_nonneg hC (Real.sqrt_nonneg _)

theorem sum_Icc_one_eq_range_of_zero {E : Type*} [AddCommMonoid E]
    (F : ℕ→E) (hF : F 0=0) (N : ℕ) :
    (∑ n∈Finset.Icc 1 N,F n)=∑ n∈Finset.range (N+1),F n := by
  apply Finset.sum_subset
  · intro n hn
    have h:=Finset.mem_Icc.mp hn
    exact Finset.mem_range.mpr (by omega)
  · intro n hn hn'
    have h:=Finset.mem_range.mp hn
    have hh:¬(1 ≤ n ∧ n ≤ N):=by simpa using hn'
    have he:n=0:=by omega
    simpa [he] using hF

theorem sum_range_filter_prefix {E : Type*} [AddCommMonoid E]
    (F : ℕ→E) {N K : ℕ} (hK : K ≤ N) :
    (∑ n∈Finset.range (N+1),if n<K+1 then F n else 0)=
      ∑ n∈Finset.range (K+1),F n := by
  rw [←Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter,Finset.mem_range]
  omega

theorem arithmeticCharacterSum_convolution_triangular {q : ℕ} (X : ℕ)
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X (f*g) χ=
      triangularCharacterSum (fun m:Fin (X+1)=>(f m.val:ℂ))
        (fun n:Fin (X+1)=>(g n.val:ℂ)) (fun m=>X/m.val+1) χ := by
  rw [arithmeticCharacterSum_convolution]
  rw [sum_Icc_one_eq_range_of_zero (fun d=>(f d:ℂ)*χ (d:ZMod q)*
    (∑ m∈Finset.Icc 1 (X/d),(g m:ℂ)*χ (m:ZMod q))) (by simp)]
  have he : triangularCharacterSum (fun m:Fin (X+1)=>(f m.val:ℂ))
      (fun n:Fin (X+1)=>(g n.val:ℂ)) (fun m=>X/m.val+1) χ=
      ∑ m∈Finset.range (X+1),∑ n∈Finset.range (X+1),
        if n<X/m+1 then (f m:ℂ)*(g n:ℂ)*χ (m:ZMod q)*χ (n:ZMod q) else 0 := by
    unfold triangularCharacterSum
    trans ∑ m:Fin (X+1),∑ n∈Finset.range (X+1),
      if n<X/m.val+1 then (f m.val:ℂ)*(g n:ℂ)*χ (m.val:ZMod q)*χ (n:ZMod q) else 0
    · apply Finset.sum_congr rfl
      intro m _
      exact Fin.sum_univ_eq_sum_range (fun n:ℕ=>
        if n<X/m.val+1 then (f m.val:ℂ)*(g n:ℂ)*χ (m.val:ZMod q)*χ (n:ZMod q) else 0) _
    · exact Fin.sum_univ_eq_sum_range (fun m:ℕ=>∑ n∈Finset.range (X+1),
        if n<X/m+1 then (f m:ℂ)*(g n:ℂ)*χ (m:ZMod q)*χ (n:ZMod q) else 0) _
  rw [he]
  apply Finset.sum_congr rfl
  intro m _
  rw [sum_Icc_one_eq_range_of_zero (fun n=>(g n:ℂ)*χ (n:ZMod q)) (by simp)]
  rw [←sum_range_filter_prefix (fun n=>(g n:ℂ)*χ (n:ZMod q)) (Nat.div_le_self X m)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> ring

theorem vaughan_typeII_exact {q : ℕ} (X U V : ℕ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ=
      triangularCharacterSum (vaughanFirstSequence V (X+1))
        (vaughanSecondSequence U (X+1)) (fun m=>X/m.val+1) χ := by
  rw [arithmeticCharacterSum_convolution_triangular]
  congr 1
  funext m
  change (((ArithmeticFunction.moebius m.val:ℝ)-
    (if m.val ≤ V then (ArithmeticFunction.moebius m.val:ℝ) else 0):ℝ):ℂ)=_
  by_cases hm:m.val ≤ V
  · simp [vaughanFirstSequence,hm,not_lt_of_ge hm]
  · simp [vaughanFirstSequence,hm,lt_of_not_ge hm]

noncomputable def arithmeticL1 (X : ℕ) (f : ArithmeticFunction ℝ) : ℝ :=
  ∑ n∈Finset.Icc 1 X,|f n|

theorem arithmeticCharacterSum_le_l1 {q : ℕ} (X : ℕ)
    (f : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    ‖arithmeticCharacterSum X f χ‖ ≤ arithmeticL1 X f := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _)

theorem arithmeticL1_nonneg (X : ℕ) (f : ArithmeticFunction ℝ) :
    0 ≤ arithmeticL1 X f := Finset.sum_nonneg (fun _ _=>abs_nonneg _)

theorem arithmeticL1_cutoff_le (X D : ℕ) (f : ArithmeticFunction ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hf : ∀ n∈Finset.Icc 1 D,|f n| ≤ A) :
    arithmeticL1 X (arithmeticCutoff D f) ≤ (D:ℝ)*A := by
  have he : arithmeticL1 X (arithmeticCutoff D f)=
      ∑ n∈(Finset.Icc 1 X).filter (fun n=>n ≤ D),|f n| := by
    simp only [arithmeticL1,arithmeticCutoff_apply,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> simp
  rw [he]
  have hs : (Finset.Icc 1 X).filter (fun n=>n ≤ D) ⊆ Finset.Icc 1 D := by
    intro n hn
    obtain ⟨hn,hnD⟩:=Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,hnD⟩
  calc
    _ ≤ ∑ _n∈(Finset.Icc 1 X).filter (fun n=>n ≤ D),A :=
      Finset.sum_le_sum (fun n hn=>hf n (hs hn))
    _ = (((Finset.Icc 1 X).filter (fun n=>n ≤ D)).card:ℝ)*A := by simp
    _ ≤ (D:ℝ)*A := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast (by simpa using Finset.card_le_card hs)

theorem arithmeticCharacterSum_log_convolution_bound {q : ℕ} (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (X : ℕ) (f : ArithmeticFunction ℝ) :
    ‖arithmeticCharacterSum X (f*ArithmeticFunction.log) χ‖ ≤
      arithmeticL1 X f*(2*Real.log (X+1:ℕ)*(Real.sqrt q*(harmonic q:ℝ))) := by
  rw [arithmeticCharacterSum_convolution]
  have he (d : ℕ) : (∑ n∈Finset.Icc 1 (X/d),
      (ArithmeticFunction.log n:ℂ)*χ (n:ZMod q))=
      ∑ n∈Finset.range (X/d+1),(Real.log n:ℂ)*χ (n:ZMod q) := by
    exact sum_Icc_one_eq_range_of_zero _ (by simp) _
  simp only [he]
  have h:=primitive_typeI_log_bound hq hχ X X (fun d=>(f d:ℂ))
  simpa only [arithmeticL1,Complex.norm_real,Real.norm_eq_abs] using h

theorem arithmeticCharacterSum_zeta_convolution_bound {q : ℕ} (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (X : ℕ) (f : ArithmeticFunction ℝ) :
    ‖arithmeticCharacterSum X (f*(ArithmeticFunction.zeta:ArithmeticFunction ℝ)) χ‖ ≤
      arithmeticL1 X f*(Real.sqrt q*(harmonic q:ℝ)) := by
  rw [arithmeticCharacterSum_convolution]
  have he (d : ℕ) : (∑ n∈Finset.Icc 1 (X/d),
      ((ArithmeticFunction.zeta:ArithmeticFunction ℝ) n:ℂ)*χ (n:ZMod q))=
      ∑ n∈Finset.range (X/d+1),χ (n:ZMod q) := by
    trans ∑ n∈Finset.Icc 1 (X/d),χ (n:ZMod q)
    · apply Finset.sum_congr rfl
      intro n hn
      have hn0:n≠0:=by have h:=(Finset.mem_Icc.mp hn).1; omega
      simp [ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply_ne hn0]
    · exact sum_Icc_one_eq_range_of_zero _ (by simpa using χ.map_zero' (by omega)) _
  simp only [he]
  have h:=primitive_typeI_bound hq hχ X X (fun d=>(f d:ℂ))
  simpa only [arithmeticL1,Complex.norm_real,Real.norm_eq_abs] using h

theorem arithmeticCutoff_mul_support (U V n : ℕ) (f g : ArithmeticFunction ℝ)
    (hn : U*V < n) : (arithmeticCutoff U f*arithmeticCutoff V g) n=0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have he:p.1*p.2=n:=(Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases h1:p.1 ≤ U
  · by_cases h2:p.2 ≤ V
    · have h:=Nat.mul_le_mul h1 h2
      omega
    · simp [arithmeticCutoff_apply,h2]
  · simp [arithmeticCutoff_apply,h1]

theorem vaughanShortCoefficient_abs_le (U V n : ℕ) :
    |(arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*
      arithmeticCutoff U ArithmeticFunction.vonMangoldt) n| ≤ Real.log n := by
  rw [ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ p∈n.divisorsAntidiagonal,
        |arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ) p.1*
          arithmeticCutoff U ArithmeticFunction.vonMangoldt p.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p∈n.divisorsAntidiagonal,ArithmeticFunction.vonMangoldt p.2 := by
      apply Finset.sum_le_sum
      intro p _
      rw [abs_mul]
      have hm: |arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ) p.1| ≤ 1 := by
        rw [arithmeticCutoff_apply]
        split_ifs
        · rw [ArithmeticFunction.intCoe_apply]
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=p.1))
        · simp
      have hl: |arithmeticCutoff U ArithmeticFunction.vonMangoldt p.2| ≤
          ArithmeticFunction.vonMangoldt p.2 := by
        rw [arithmeticCutoff_apply]
        split_ifs
        · exact (abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg).le
        · simp
      exact (mul_le_mul hm hl (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ d=>ArithmeticFunction.vonMangoldt d),
        ArithmeticFunction.vonMangoldt_sum]

theorem arithmeticCutoff_eq_of_support (D : ℕ) (f : ArithmeticFunction ℝ)
    (hf : ∀ n,D<n→f n=0) : arithmeticCutoff D f=f := by
  ext n
  by_cases hn:n ≤ D
  · simp [arithmeticCutoff_apply,hn]
  · simp [arithmeticCutoff_apply,hn,hf n (lt_of_not_ge hn)]

theorem vonMangoldt_cutoff_l1 (X U : ℕ) :
    arithmeticL1 X (arithmeticCutoff U ArithmeticFunction.vonMangoldt) ≤ (U:ℝ)*Real.log U := by
  apply arithmeticL1_cutoff_le
  · simpa using log_nat_monotone (Nat.zero_le U)
  · intro n hn
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact ArithmeticFunction.vonMangoldt_le_log.trans (log_nat_monotone (Finset.mem_Icc.mp hn).2)

theorem moebius_cutoff_l1 (X V : ℕ) :
    arithmeticL1 X (arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)) ≤ V := by
  have h:=arithmeticL1_cutoff_le X V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)
    zero_le_one (fun n _=>by
      rw [ArithmeticFunction.intCoe_apply]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=n)))
  simpa only [mul_one] using h

theorem vaughanShortCoefficient_l1 (X U V : ℕ) :
    arithmeticL1 X (arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*
      arithmeticCutoff U ArithmeticFunction.vonMangoldt) ≤ (V*U:ℕ)*Real.log (V*U:ℕ) := by
  let f:=arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*
    arithmeticCutoff U ArithmeticFunction.vonMangoldt
  have he : arithmeticCutoff (V*U) f=f :=
    arithmeticCutoff_eq_of_support _ _ (fun n hn=>arithmeticCutoff_mul_support V U n _ _ hn)
  change arithmeticL1 X f ≤ _
  rw [←he]
  apply arithmeticL1_cutoff_le
  · simpa using log_nat_monotone (Nat.zero_le (V*U))
  · intro n hn
    exact (vaughanShortCoefficient_abs_le U V n).trans (log_nat_monotone (Finset.mem_Icc.mp hn).2)

theorem primitive_vaughan_bound {q : ℕ} (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (X U V : ℕ) :
    ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ ≤
      (U:ℝ)*Real.log U+
      (V:ℝ)*(2*Real.log (X+1:ℕ)*(Real.sqrt q*(harmonic q:ℝ)))+
      ((V*U:ℕ)*Real.log (V*U:ℕ))*(Real.sqrt q*(harmonic q:ℝ))+
      ‖triangularCharacterSum (vaughanFirstSequence V (X+1))
        (vaughanSecondSequence U (X+1)) (fun m=>X/m.val+1) χ‖ := by
  have hH : 0 ≤ (harmonic q:ℝ) := by exact_mod_cast (harmonic_pos (by omega : q≠0)).le
  have hK : 0 ≤ Real.sqrt q*(harmonic q:ℝ) := mul_nonneg (Real.sqrt_nonneg _) hH
  have hL : 0 ≤ (2:ℝ)*Real.log (X+1:ℕ)*(Real.sqrt q*(harmonic q:ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X+1 by omega)))) hK
  have h0 := (arithmeticCharacterSum_le_l1 X (arithmeticCutoff U ArithmeticFunction.vonMangoldt) χ).trans
    (vonMangoldt_cutoff_l1 X U)
  have h1 := (arithmeticCharacterSum_log_convolution_bound hq hχ X
    (arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ))).trans
      (mul_le_mul_of_nonneg_right (moebius_cutoff_l1 X V) hL)
  have h2 := (arithmeticCharacterSum_zeta_convolution_bound hq hχ X
    (arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*
      arithmeticCutoff U ArithmeticFunction.vonMangoldt)).trans
      (mul_le_mul_of_nonneg_right (vaughanShortCoefficient_l1 X U V) hK)
  rw [vaughan_character_identity,vaughan_typeII_exact]
  apply le_trans (norm_add_le _ _)
  apply add_le_add _ le_rfl
  apply le_trans (norm_sub_le _ _)
  apply add_le_add _ h2
  exact (norm_add_le _ _).trans (add_le_add h0 h1)

noncomputable def hyperbolaBlock {q : ℕ} (X D E : ℕ)
    (a b : ℕ→ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ m∈Finset.Ico D E,a m*χ (m:ZMod q)*
    (∑ n∈Finset.range (X/m+1),b n*χ (n:ZMod q))

theorem hyperbolaBlock_eq_triangle {q : ℕ} (X D E : ℕ) (hD : 0 < D)
    (a b : ℕ→ℂ) (χ : DirichletCharacter ℂ q) :
    hyperbolaBlock X D E a b χ=
      triangularCharacterSum (sequenceMask (fun m:Fin E=>D ≤ m.val) (fun m=>a m.val))
        (fun n:Fin (X/D+1)=>b n.val) (fun m=>X/m.val+1) χ := by
  classical
  have hf : (Finset.range E).filter (fun m=>D ≤ m)=Finset.Ico D E := by
    ext m
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  have he : triangularCharacterSum
      (sequenceMask (fun m:Fin E=>D ≤ m.val) (fun m=>a m.val))
      (fun n:Fin (X/D+1)=>b n.val) (fun m=>X/m.val+1) χ=
      ∑ m∈Finset.range E,∑ n∈Finset.range (X/D+1),
        if n < X/m+1 then (if D ≤ m then a m else 0)*b n*χ (m:ZMod q)*χ (n:ZMod q) else 0 := by
    unfold triangularCharacterSum sequenceMask
    trans ∑ m:Fin E,∑ n∈Finset.range (X/D+1),
      if n < X/m.val+1 then (if D ≤ m.val then a m.val else 0)*b n*χ (m.val:ZMod q)*χ (n:ZMod q) else 0
    · apply Finset.sum_congr rfl
      intro m _
      by_cases hm:D ≤ m.val <;>
        simpa only [hm,ite_true,ite_false] using
          (Fin.sum_univ_eq_sum_range (fun n:ℕ=>
            if n < X/m.val+1 then (if D ≤ m.val then a m.val else 0)*b n*χ (m.val:ZMod q)*χ (n:ZMod q) else 0) (X/D+1))
    · exact Fin.sum_univ_eq_sum_range (fun m:ℕ=>∑ n∈Finset.range (X/D+1),
        if n < X/m+1 then (if D ≤ m then a m else 0)*b n*χ (m:ZMod q)*χ (n:ZMod q) else 0) _
  rw [he]
  unfold hyperbolaBlock
  rw [←hf,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm:D ≤ m
  · simp only [hm,ite_true]
    rw [←sum_range_filter_prefix (fun n=>b n*χ (n:ZMod q)) (Nat.div_le_div_left hm hD)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> ring
  · simp [hm]

theorem sum_Ico_one_pow_two {A : Type*} [AddCommMonoid A] (F : ℕ→A) (k : ℕ) :
    (∑ m∈Finset.Ico 1 (2^k),F m)=
      ∑ j∈Finset.range k,∑ m∈Finset.Ico (2^j) (2^(j+1)),F m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ,←ih,Finset.sum_Ico_consecutive]
    · exact one_le_pow₀ (by omega)
    · exact pow_le_pow_right₀ (by omega) (Nat.le_succ k)

theorem vaughan_hyperbolaBlock_mean (Q X U V D E k : ℕ) (hD : 0 < D)
    (hk : X/D+1 ≤ 2^k) :
    primitiveCharacterMean Q (fun _ χ=>‖hyperbolaBlock X D E
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
      (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ‖) ≤
      ((k:ℝ)+1)*sieveBilinearConstant Q E (X/D+1)*Real.sqrt E*
        (Real.sqrt ((X/D+1:ℕ):ℝ)*Real.log ((X/D+1:ℕ):ℝ)) := by
  have h:=vaughan_typeII_block_mean Q X U V E (X/D+1) k hk
    (fun m=>D ≤ m.val) (fun _=>True)
  have hr : sequenceMask (fun _ : Fin (X/D+1)=>True)
      (vaughanSecondSequence U (X/D+1))=vaughanSecondSequence U (X/D+1) := by
    funext n
    simp [sequenceMask]
  rw [hr] at h
  have he : (fun (_q : Fin Q) (χ : DirichletCharacter ℂ (_q.val+1))=>‖hyperbolaBlock X D E
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
      (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ‖)=
      (fun (_q : Fin Q) (χ : DirichletCharacter ℂ (_q.val+1))=>‖triangularCharacterSum
        (sequenceMask (fun m:Fin E=>D ≤ m.val) (vaughanFirstSequence V E))
        (vaughanSecondSequence U (X/D+1)) (fun m=>X/m.val+1) χ‖) := by
    funext q χ
    rw [hyperbolaBlock_eq_triangle X D E hD]
    rfl
  rw [he]
  exact h

theorem hyperbolaBlock_extend {q : ℕ} (X E : ℕ) (hE : X+1 ≤ E)
    (a b : ℕ→ℂ) (hb : b 0=0) (χ : DirichletCharacter ℂ q) :
    hyperbolaBlock X 1 (X+1) a b χ=hyperbolaBlock X 1 E a b χ := by
  unfold hyperbolaBlock
  apply Finset.sum_subset
  · intro m hm
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hm).1,
      ((Finset.mem_Ico.mp hm).2).trans_le hE⟩
  · intro m hm hm'
    have hx : X < m := by
      have h:=Finset.mem_Ico.mp hm
      have hh : ¬(1 ≤ m ∧ m < X+1) := by simpa only [Finset.mem_Ico] using hm'
      omega
    simp [Nat.div_eq_of_lt hx,hb]

theorem arithmeticCharacterSum_convolution_dyadic {q : ℕ} (X k : ℕ)
    (hk : X+1 ≤ 2^k) (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X (f*g) χ=
      ∑ j∈Finset.range k,hyperbolaBlock X (2^j) (2^(j+1))
        (fun m=>(f m:ℂ)) (fun n=>(g n:ℂ)) χ := by
  rw [arithmeticCharacterSum_convolution]
  have he : (∑ m∈Finset.Icc 1 X,(f m:ℂ)*χ (m:ZMod q)*
      ∑ n∈Finset.Icc 1 (X/m),(g n:ℂ)*χ (n:ZMod q))=
      hyperbolaBlock X 1 (X+1) (fun m=>(f m:ℂ)) (fun n=>(g n:ℂ)) χ := by
    unfold hyperbolaBlock
    rw [show Finset.Ico 1 (X+1)=Finset.Icc 1 X by ext m; simp]
    apply Finset.sum_congr rfl
    intro m _
    rw [sum_Icc_one_eq_range_of_zero (fun n=>(g n:ℂ)*χ (n:ZMod q)) (by simp)]
  rw [he,hyperbolaBlock_extend X (2^k) hk _ _ (by simp)]
  exact sum_Ico_one_pow_two _ k

theorem vaughan_typeII_dyadic {q : ℕ} (X U V k : ℕ) (hk : X+1 ≤ 2^k)
    (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ=
      ∑ j∈Finset.range k,hyperbolaBlock X (2^j) (2^(j+1))
        (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
        (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ := by
  rw [arithmeticCharacterSum_convolution_dyadic X k hk]
  have hf : (fun m=>(((ArithmeticFunction.moebius-
        arithmeticCutoff V ArithmeticFunction.moebius):ArithmeticFunction ℝ) m:ℂ))=
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0) := by
    funext m
    change (((ArithmeticFunction.moebius m:ℝ)-
      (if m ≤ V then (ArithmeticFunction.moebius m:ℝ) else 0):ℝ):ℂ)=_
    by_cases hm:m ≤ V
    · simp [hm,not_lt_of_ge hm]
    · simp [hm,lt_of_not_ge hm]
  rw [hf]

end LargePrimeGaps

end OAI
