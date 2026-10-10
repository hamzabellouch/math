import OAI.NumberTheory.DirichletL.GaussSum.MellinSupport
import OAI.NumberTheory.DirichletL.GaussSum.FiniteTranslations

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def lowRamifiedTransform (F:Eis→ℂ) (h:Eis) :ℂ :=
  3*F (9*h)+∑u:Eisˣ,∑k:Fin 5,ramifiedRawWeight h u k.val*
    F (h*(9*(u.val*lambda^(k.val+2))))

lemma principalArithmeticResidue_low (a r:Fin 3) (n:Eis) (hn:lambda^2∣n-1) :
    principalArithmeticResidue (lowRamifiedFrequency a r*n)=
      (∑u:Eisˣ,∑k:Fin 5,ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val*
        unramifiedGaussResidue ((lowRamifiedFrequency a r*n)*(9*(u.val*lambda^(k.val+2)))))/
          ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  let h:=lowRamifiedFrequency a r*n
  have hh:h≠0:=mul_ne_zero (lowRamifiedFrequency_ne_zero a r) (primary_ne_zero n hn)
  let N:=max (ramifiedFrequencyBound h+1) 5
  rw [principalArithmeticResidue_eq_sum h hh N (le_max_left _ _)]
  apply congrArg (fun z:ℂ=>z/((9*Real.sqrt 3/2:ℝ):ℂ))
  apply Finset.sum_congr rfl
  intro u hu
  change (∑k∈Finset.range N,principalResidueTerm h u k)=
    ∑k:Fin 5,principalResidueTerm h u k.val
  rw [Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
  intro k hk hk5
  have hz:=lowRamifiedFrequency_primary_vanish a r n hn u k
    (by simpa only [Finset.mem_range,not_lt] using hk5)
  simp only [principalResidueTerm,h,hz,mul_zero,zero_mul]

lemma sourceRayPhase_of_three_dvd (h:Eis) (hh:(3:Eis)∣h) :
    ShortDraftTrace.breveE (cuspFrequency h)=1 := by
  obtain ⟨z,rfl⟩:=hh
  have he:cuspFrequency ((3:Eis)*z)=eisEmbedding z/eisLam:=by
    simp only [cuspFrequency,map_mul,map_ofNat]
    ring
  rw [he]
  exact breveE_embedding_div_traceLambda z

lemma lowRamifiedFrequency_three_dvd (a r:Fin 3) : (3:Eis)∣lowRamifiedFrequency a r := by
  simpa only [lowRamifiedFrequency,←ramifiedOmegaUnit_val,←Units.val_pow_eq_pow_val] using
    ramifiedElement_level (ramifiedOmegaUnit^a.val) (r.val+2) (by omega)

theorem lowRamifiedTransform_actual (a r:Fin 3) (n:Eis) (hn:lambda^2∣n-1) :
    lowRamifiedTransform unramifiedGaussResidue (lowRamifiedFrequency a r*n)=
      (4*((9*Real.sqrt 3/2:ℝ):ℂ))*sourceArithmeticResidue (lowRamifiedFrequency a r*n) := by
  rw [sourceArithmeticResidue,ite_eq_left (sourceRayPhase_of_three_dvd _
    (dvd_mul_of_dvd_left (lowRamifiedFrequency_three_dvd a r) n)),
    principalArithmeticResidue_low a r n hn]
  unfold lowRamifiedTransform
  field_simp [show ((9*Real.sqrt 3/2:ℝ):ℂ)≠0 by exact_mod_cast (show (9*Real.sqrt 3/2:ℝ)≠0 by positivity)]
  ; ring

lemma lowRamifiedTransform_sub (F G:Eis→ℂ) (h:Eis) :
    lowRamifiedTransform (fun x=>F x-G x) h=
      lowRamifiedTransform F h-lowRamifiedTransform G h := by
  simp only [lowRamifiedTransform,mul_sub,Finset.sum_sub_distrib]
  ring

lemma ramifiedRawWeight_frequency_cube (h p:Eis) (hp:lambda^2∣p-1) (u:Eisˣ) (k:ℕ) :
    ramifiedRawWeight (h*p^3) u k=ramifiedRawWeight h u k := by
  rw [ramifiedRawWeight,ramifiedRawWeight,arithmeticResidueSum_frequency_cube h _ p
    (ramifiedElement_ne_zero u (k+2)) (ramifiedElement_level u (k+2) (by omega)) hp
    (ramified_primary_coprime u (k+2) p hp).of_mul_left_right]

lemma lowRamifiedTransform_cube_comp (F:Eis→ℂ) (h p:Eis) (hp:lambda^2∣p-1) :
    lowRamifiedTransform (fun x=>F (x*p^3)) h=lowRamifiedTransform F (h*p^3) := by
  simp only [lowRamifiedTransform,ramifiedRawWeight_frequency_cube h p hp]
  have he:9*h*p^3=9*(h*p^3):=by ring
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  ring_nf

theorem lowRamifiedTransform_cube_difference (p:Eis) (hp:Prime p) (hpp:lambda^2∣p-1)
    (a r:Fin 3) (n:Eis) (hn:lambda^2∣n-1) :
    lowRamifiedTransform (fun x=>unramifiedGaussResidue (x*p^3)-unramifiedGaussResidue x)
      (lowRamifiedFrequency a r*n)=0 := by
  rw [lowRamifiedTransform_sub,lowRamifiedTransform_cube_comp _ _ p hpp]
  have hnp:lambda^2∣n*p^3-1:=primary_mul n (p^3) hn (primary_pow_congruence p hpp 3)
  rw [mul_assoc,lowRamifiedTransform_actual a r (n*p^3) hnp,
    lowRamifiedTransform_actual a r n hn]
  rw [←mul_assoc,sourceArithmeticResidue_prime_cube p hp hpp _
    (mul_ne_zero (lowRamifiedFrequency_ne_zero a r) (primary_ne_zero n hn)),sub_self]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

lemma ramifiedFunction_reduce (F:Eis→ℂ) (hneg:∀x,F (-x)=F x)
    (hpow:∀x m,F (x*lambda^m)=F (x*lambda^(m%3))) (n:Eis) (u:Eisˣ) (m:ℕ) :
    ∃j k:Fin 3,F (n*((u:Eis)*lambda^m))=F (n*omega^j.val*lambda^k.val) := by
  obtain ⟨j,hj|hj⟩:=unit_eq_sign_omega u
  · refine ⟨j,⟨m%3,Nat.mod_lt _ (by decide)⟩,?_⟩
    rw [hj,←mul_assoc,hpow]
  · refine ⟨j,⟨m%3,Nat.mod_lt _ (by decide)⟩,?_⟩
    rw [hj,neg_mul,mul_neg,hneg,←mul_assoc,hpow]

lemma ramifiedFunction_family_bound (F:Eis→ℂ) (hneg:∀x,F (-x)=F x)
    (hpow:∀x m,F (x*lambda^m)=F (x*lambda^(m%3))) (n:Eis) (M:ℝ)
    (hM:∀j k:Fin 3,‖F (n*omega^j.val*lambda^k.val)‖≤M) (u:Eisˣ) (m:ℕ) :
    ‖F (n*((u:Eis)*lambda^m))‖≤M := by
  obtain ⟨j,k,hjk⟩:=ramifiedFunction_reduce F hneg hpow n u m
  rw [hjk]
  exact hM j k

lemma ramifiedNine_eq : (9:Eis)=omega*lambda^4 := by
  have hw:omega^2=-omega-1:=by linear_combination ramified_omega_relation
  have hl:lambda^2=-3*omega:=by
    change (omega-1)^2=-3*omega
    linear_combination hw
  calc
    (9:Eis)=9*omega^3:=by rw [omega_primitive.pow_eq_one]; ring
    _=omega*((-3*omega)^2):=by ring
    _=omega*((lambda^2)^2):=by rw [hl]
    _=omega*lambda^4:=by ring

lemma lowRamified_inner_family (a r:Fin 3) (n:Eis) (u:Eisˣ) (k:ℕ) :
    (lowRamifiedFrequency a r*n)*(9*(u.val*lambda^(k+2)))=
      n*((↑(ramifiedOmegaUnit^(a.val+1)*u):Eis)*lambda^(r.val+k+8)) := by
  simp only [lowRamifiedFrequency,ramifiedNine_eq,Units.val_mul,Units.val_pow_eq_pow_val,
    ramifiedOmegaUnit_val]
  rw [show r.val+k+8=(r.val+2)+(4+(k+2)) by omega]
  simp only [pow_add,pow_one]
  ring

lemma lowRamifiedLeading (F:Eis→ℂ)
    (hpow:∀x m,F (x*lambda^m)=F (x*lambda^(m%3))) (n:Eis) (j k:Fin 3) :
    F (9*(lowRamifiedFrequency ⟨(j.val+2)%3,Nat.mod_lt _ (by decide)⟩ k*n))=
      F (n*omega^j.val*lambda^k.val) := by
  have ho:omega^((j.val+2)%3+1)=omega^j.val:=by
    fin_cases j <;> norm_num [omega_primitive.pow_eq_one]
  have he:9*(lowRamifiedFrequency ⟨(j.val+2)%3,Nat.mod_lt _ (by decide)⟩ k*n)=
      (n*omega^j.val)*lambda^(k.val+6):=by
    simp only [lowRamifiedFrequency,ramifiedNine_eq]
    rw [show k.val+6=4+(k.val+2) by omega,pow_add,←ho,pow_succ]
    ring
  rw [he,hpow,show (k.val+6)%3=k.val by omega]

lemma lowRamified_remainder_bound (F:Eis→ℂ) (hneg:∀x,F (-x)=F x)
    (hpow:∀x m,F (x*lambda^m)=F (x*lambda^(m%3))) (n:Eis) (hn:lambda^2∣n-1)
    (M:ℝ) (hM0:0≤M) (hM:∀j k:Fin 3,‖F (n*omega^j.val*lambda^k.val)‖≤M)
    (a r:Fin 3) :
    ‖∑u:Eisˣ,∑k:Fin 5,ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val*
      F ((lowRamifiedFrequency a r*n)*(9*(u.val*lambda^(k.val+2))))‖≤(5/3)*M := by
  calc
    _≤∑u:Eisˣ,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val*
        F ((lowRamifiedFrequency a r*n)*(9*(u.val*lambda^(k.val+2))))‖:=by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun u hu=>norm_sum_le _ _))
    _≤∑u:Eisˣ,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val‖*M:=by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul,lowRamified_inner_family]
      exact mul_le_mul_of_nonneg_left (ramifiedFunction_family_bound F hneg hpow n M hM _ _) (norm_nonneg _)
    _=(∑u:Eisˣ,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val‖)*M:=by
      simp only [Finset.sum_mul]
    _≤(5/3)*M:=mul_le_mul_of_nonneg_right (lowRamifiedRawWeight_sum a r n hn) hM0

theorem lowRamifiedTransform_injective (F:Eis→ℂ) (hneg:∀x,F (-x)=F x)
    (hpow:∀x m,F (x*lambda^m)=F (x*lambda^(m%3))) (n:Eis) (hn:lambda^2∣n-1)
    (hz:∀a r:Fin 3,lowRamifiedTransform F (lowRamifiedFrequency a r*n)=0) :
    ∀j k:Fin 3,F (n*omega^j.val*lambda^k.val)=0 := by
  obtain ⟨i,hi,himax⟩:=Finset.exists_max_image (Finset.univ:Finset (Fin 3×Fin 3))
    (fun i=>‖F (n*omega^i.1.val*lambda^i.2.val)‖) Finset.univ_nonempty
  let M:=‖F (n*omega^i.1.val*lambda^i.2.val)‖
  have hM:∀j k:Fin 3,‖F (n*omega^j.val*lambda^k.val)‖≤M:=by
    intro j k
    exact himax (j,k) (Finset.mem_univ _)
  let a:Fin 3:=⟨(i.1.val+2)%3,Nat.mod_lt _ (by decide)⟩
  have hb:=lowRamified_remainder_bound F hneg hpow n hn M (norm_nonneg _) hM a i.2
  have he:=hz a i.2
  unfold lowRamifiedTransform at he
  have hlead:F (9*(lowRamifiedFrequency a i.2*n))=F (n*omega^i.1.val*lambda^i.2.val):=
    lowRamifiedLeading F hpow n i.1 i.2
  rw [hlead] at he
  have hnorm:3*M≤(5/3)*M:=by
    have heq:3*F (n*omega^i.1.val*lambda^i.2.val)=
        -(∑u:Eisˣ,∑k:Fin 5,ramifiedRawWeight (lowRamifiedFrequency a i.2*n) u k.val*
          F ((lowRamifiedFrequency a i.2*n)*(9*(u.val*lambda^(k.val+2))))):=by
      linear_combination he
    have hh:=congrArg norm heq
    rw [norm_mul,Complex.norm_ofNat,norm_neg] at hh
    exact hh.le.trans hb
  have hmzero:M=0:=by have hm0:0≤M:=norm_nonneg _; nlinarith
  intro j k
  exact norm_eq_zero.mp (le_antisymm (hmzero ▸ hM j k) (norm_nonneg _))

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma exists_primary_unit_lambda_factor (h:Eis) (hh:h≠0) :
    ∃n:Eis,∃u:Eisˣ,∃m:ℕ,lambda^2∣n-1 ∧ h=n*((u:Eis)*lambda^m) := by
  obtain ⟨⟨m,J⟩,hm⟩:=lambdaFactorMap_bijective.2
    ⟨Ideal.span {h},Ideal.span_singleton_eq_bot.not.mpr hh⟩
  have hi:ramifiedIdeal^m*J.val=Ideal.span {h}:=congrArg Subtype.val hm
  have hs:Ideal.span {lambda^m*primaryGenerator J.val}=Ideal.span {h}:=by
    rw [lambdaFactor_generator_span,hi]
  obtain ⟨u,hu⟩:=Ideal.span_singleton_eq_span_singleton.mp hs
  refine ⟨primaryGenerator J.val,u,m,(primaryGenerator_spec J.val J.property).2,?_⟩
  linear_combination -hu

theorem unramifiedGaussResidue_prime_cube (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) :
    unramifiedGaussResidue (h*p^3)=unramifiedGaussResidue h := by
  by_cases hh:h=0
  · simp only [hh,zero_mul]
  obtain ⟨n,u,m,hn,hfactor⟩:=exists_primary_unit_lambda_factor h hh
  let F:Eis→ℂ:=fun x=>unramifiedGaussResidue (x*p^3)-unramifiedGaussResidue x
  have hneg:∀x,F (-x)=F x:=by
    intro x
    dsimp only [F]
    rw [neg_mul,unramifiedGaussResidue_neg,unramifiedGaussResidue_neg]
  have hpow:∀x k,F (x*lambda^k)=F (x*lambda^(k%3)):=by
    intro x k
    dsimp only [F]
    have h1:unramifiedGaussResidue ((x*lambda^k)*p^3)=
        unramifiedGaussResidue ((x*lambda^(k%3))*p^3):=by
      rw [show (x*lambda^k)*p^3=(x*p^3)*lambda^k by ring,
        show (x*lambda^(k%3))*p^3=(x*p^3)*lambda^(k%3) by ring]
      exact unramifiedGaussResidue_lambda_pow (x*p^3) k
    exact congrArg₂ (fun a b:ℂ=>a-b) h1 (unramifiedGaussResidue_lambda_pow x k)
  have hz:∀j k:Fin 3,F (n*omega^j.val*lambda^k.val)=0:=
    lowRamifiedTransform_injective F hneg hpow n hn
      (fun a r=>lowRamifiedTransform_cube_difference p hp hpp a r n hn)
  obtain ⟨j,k,hjk⟩:=ramifiedFunction_reduce F hneg hpow n u m
  have hF:F h=0:=by rw [hfactor,hjk,hz]
  exact sub_eq_zero.mp hF

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma unramifiedGaussResidue_prime_pow_mod (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (_hh:h≠0) (n:ℕ) :
    unramifiedGaussResidue (h*p^n)=unramifiedGaussResidue (h*p^(n%3)) := by
  induction n using Nat.strong_induction_on with
  | h n ih=>
    by_cases hn:n<3
    · rw [Nat.mod_eq_of_lt hn]
    · have hn3:3≤n:=by omega
      have he:h*p^n=(h*p^(n-3))*p^3:=by rw [mul_assoc,←pow_add,Nat.sub_add_cancel hn3]
      rw [he,unramifiedGaussResidue_prime_cube p hp hprimary _,
        ih (n-3) (by omega)]
      have hm:(n-3)%3=n%3:=by omega
      rw [hm]

theorem unramifiedGaussResidue_prime_square (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    unramifiedGaussResidue (h*p^2)=0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have he:=unramifiedGaussResidue_square_cube p hp hprimary h hph
  rw [show h*p^5=(h*p^2)*p^3 by ring,
    unramifiedGaussResidue_prime_cube p hp hprimary _] at he
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hz:(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*unramifiedGaussResidue (h*p^2)=0:=by
    linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hq)

theorem unramifiedGaussResidue_prime_factor (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    unramifiedGaussResidue (h*p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
        primeCubicGauss p hp hprimary 2 h*unramifiedGaussResidue h := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have hrec:=unramifiedGaussResidue_prime_recurrence p hp hprimary h hph
  rw [unramifiedGaussResidue_prime_cube p hp hprimary h] at hrec
  have hrel:(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*
      primeCubicGauss p hp hprimary 1 h*unramifiedGaussResidue (h*p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*unramifiedGaussResidue h:=by
    linear_combination hrec
  have hG:=primeCubicGauss_one_mul_two p hp hprimary h hph
  let q:ℂ:=(Ideal.absNorm (Ideal.span {p}):ℂ)
  have hq:q≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hpower:q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q^2=1:=by
    rw [←Complex.cpow_add _ _ hq,←Complex.cpow_natCast q 2,
      ←Complex.cpow_add _ _ hq]
    norm_num
  calc
    unramifiedGaussResidue (h*p)=
        (q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q^2)*unramifiedGaussResidue (h*p):=by rw [hpower,one_mul]
    _=q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 h*
        (q^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 h*unramifiedGaussResidue (h*p)):=by
      calc
        _=q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q*
          (primeCubicGauss p hp hprimary 1 h*primeCubicGauss p hp hprimary 2 h)*
          unramifiedGaussResidue (h*p):=by rw [hG];ring
        _=_:=by ring
    _=q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 h*(q⁻¹*unramifiedGaussResidue h):=by rw [hrel]
    _=_:=by
      change q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 h*(q⁻¹*unramifiedGaussResidue h)=
        q^(-(2/3:ℂ))*primeCubicGauss p hp hprimary 2 h*unramifiedGaussResidue h
      field_simp [hq]

theorem unramifiedGaussResidue_prime_power_table (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (n:ℕ) :
    unramifiedGaussResidue (h*p^n)=
      if n%3=0 then unramifiedGaussResidue h
      else if n%3=1 then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
          primeCubicGauss p hp hprimary 2 h*unramifiedGaussResidue h
      else 0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  rw [unramifiedGaussResidue_prime_pow_mod p hp hprimary h hh n]
  split_ifs with h0 h1
  · simp only [h0,pow_zero,mul_one]
  · simp only [h1,pow_one]
    exact unramifiedGaussResidue_prime_factor p hp hprimary h hph
  · have hn:n%3=2:=by omega
    rw [hn,unramifiedGaussResidue_prime_square p hp hprimary h hph]

end

section
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def thetaFrequencyScale : ℂ := 1/((3:ℂ)*eisLam)
def thetaBesselScale : ℝ := ‖thetaFrequencyScale‖
def thetaDerivativeScalar : ℂ :=
  (-2*Real.pi*Complex.I)*star thetaFrequencyScale*infinityCoefficientScalar

lemma thetaFrequencyScale_ne_zero : thetaFrequencyScale≠0 := by
  exact one_div_ne_zero (mul_ne_zero (by norm_num) eisLam_ne_zero)

lemma thetaBesselScale_pos : 0<thetaBesselScale := norm_pos_iff.mpr thetaFrequencyScale_ne_zero

lemma thetaBesselScale_eq : thetaBesselScale=1/Real.sqrt 27 := by
  have hl : ‖eisLam‖^2=(3:ℝ) := by
    have h := congrArg norm TraceLambdaPhase.eisLam_sq
    norm_num only [norm_pow,norm_neg,Complex.norm_ofNat] at h
    exact h
  have hd : ‖(3:ℂ)*eisLam‖=Real.sqrt 27 := by
    rw [norm_mul,Complex.norm_ofNat]
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤27 by norm_num),
      Real.sqrt_nonneg (27:ℝ),norm_nonneg eisLam]
  rw [thetaBesselScale,thetaFrequencyScale,norm_div,norm_one,hd]

lemma thetaDerivativeScalar_ne_zero : thetaDerivativeScalar≠0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    (star_ne_zero.mpr thetaFrequencyScale_ne_zero)) infinityCoefficientScalar_ne_zero

lemma cuspFrequency_eq_thetaFrequencyScale (h : Eis) :
    cuspFrequency h=thetaFrequencyScale*eisEmbedding h := by
  unfold cuspFrequency thetaFrequencyScale
  ring

lemma completedCoefficient_mul_length (Ψ : Eis→*ℂ) (I J : NonzeroIdeal)
    (hI : primaryGenerator I.val≠0) (hJ : primaryGenerator J.val≠0)
    (hsq : Squarefree I.val) :
    completedMellinCoefficient Ψ (I,J)*(completedMellinLength (I,J):ℂ)=
      star (eisEmbedding (primaryGenerator I.val*(primaryGenerator J.val)^3))*
        (‖eisEmbedding (primaryGenerator J.val)‖:ℂ)*gaussTwo I.val hI*
        Ψ (primaryGenerator I.val)*(Ψ (primaryGenerator J.val))^3 := by
  have hni : (Ideal.absNorm I.val:ℂ)=(‖eisEmbedding (primaryGenerator I.val)‖:ℂ)^2 := by
    exact_mod_cast (primaryGenerator_norm_sq I.val hI).symm
  have hnj : (Ideal.absNorm J.val:ℂ)=(‖eisEmbedding (primaryGenerator J.val)‖:ℂ)^2 := by
    exact_mod_cast (primaryGenerator_norm_sq J.val hJ).symm
  have hi0 : (‖eisEmbedding (primaryGenerator I.val)‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hI))
  have hj0 : (‖eisEmbedding (primaryGenerator J.val)‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hJ))
  rw [completedMellinCoefficient,columnWeight_eq Ψ I.val hsq hI]
  rw [show cubeWeight Ψ J.val=star (FiniteGaussPhase.angularFactor (primaryGenerator J.val))^3*
    Ψ (primaryGenerator J.val)^3/(Ideal.absNorm J.val:ℂ) from rfl]
  simp only [FiniteGaussPhase.angularFactor,completedMellinLength,
    Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,
    ←primaryGenerator_norm I.val hI,hni,hnj,map_mul,map_pow,star_mul,star_pow,
    Complex.star_def,map_div₀,Complex.conj_ofReal]
  field_simp [hi0,hj0]

lemma thetaPair_frequency_norm (I J : NonzeroIdeal)
    (hI : primaryGenerator I.val≠0) (hJ : primaryGenerator J.val≠0) :
    ‖cuspFrequency (primaryGenerator I.val*(primaryGenerator J.val)^3)‖=
      thetaBesselScale*Real.sqrt (completedMellinLength (I,J)) := by
  rw [cuspFrequency_eq_thetaFrequencyScale,norm_mul,map_mul,map_pow,norm_mul,norm_pow]
  have he : completedMellinLength (I,J)=
      (‖eisEmbedding (primaryGenerator I.val)‖*‖eisEmbedding (primaryGenerator J.val)‖^3)^2 := by
    rw [completedMellinLength,←primaryGenerator_norm_sq I.val hI,←primaryGenerator_norm_sq J.val hJ]
    ring
  rw [he,Real.sqrt_sq (by positivity)]
  rfl

lemma thetaPair_derivative_coefficient (Ψ : Eis→*ℂ) (I J : NonzeroIdeal)
    (hI : primaryGenerator I.val≠0) (hJ : primaryGenerator J.val≠0)
    (hsq : Squarefree I.val) :
    (-2*Real.pi*Complex.I*star (cuspFrequency (primaryGenerator I.val*(primaryGenerator J.val)^3)))*
      fixedThetaTwist Ψ (primaryGenerator I.val*(primaryGenerator J.val)^3)*
        star (sourceResidualFourierCoefficient (primaryGenerator I.val*(primaryGenerator J.val)^3))=
      thetaDerivativeScalar*(completedMellinCoefficient Ψ (I,J)*(completedMellinLength (I,J):ℂ)) := by
  have he := fixedThetaTwist_infinity_coefficient Ψ I.val J.val hI hJ hsq
  have he' := congrArg (fun z:ℂ=>infinityCoefficientScalar*z) he
  simp only [←mul_assoc,mul_inv_cancel₀ infinityCoefficientScalar_ne_zero,one_mul] at he'
  rw [completedCoefficient_mul_length Ψ I J hI hJ hsq,cuspFrequency_eq_thetaFrequencyScale,star_mul]
  unfold thetaDerivativeScalar
  calc
    _ = (-2*Real.pi*Complex.I*star thetaFrequencyScale)*
        star (eisEmbedding (primaryGenerator I.val*(primaryGenerator J.val)^3))*
          (star (sourceResidualFourierCoefficient (primaryGenerator I.val*(primaryGenerator J.val)^3))*
            fixedThetaTwist Ψ (primaryGenerator I.val*(primaryGenerator J.val)^3)) := by ring
    _ = _ := by rw [he'];ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def thetaTwistedSource (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (v : ℝ) (hv : 0<v) (z : ℂ) : ℂ :=
  traceTwistedConjugateSource c hc (fixedThetaQuotient Ψ c) v hv z

theorem thetaTwistedSource_wirtingerBar_eq_completedBesselProfile
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) (v : ℝ) (hv : 0<v) :
    horizontalWirtingerBar (thetaTwistedSource Ψ c hc v hv) 0=
      thetaDerivativeScalar*completedBesselProfile Ψ thetaBesselScale v := by
  change horizontalWirtingerBar (traceTwistedConjugateSource c hc (fixedThetaQuotient Ψ c) v hv) 0 = _
  rw [traceTwistedConjugateSource_wirtingerBar_zero]
  simp only [fixedThetaQuotient_mk Ψ Q hΨ c hcQ]
  let w : Eis→ℂ := fun h=>(-2*Real.pi*Complex.I*star (cuspFrequency h))*
    fixedThetaTwist Ψ h*(v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)
  have hw : ∀h:Eis,w h≠0→lambda^2∣h-1 := by
    intro h hwh
    by_contra hh
    exact hwh (by simp only [w,fixedThetaTwist_not_primary Ψ h hh,mul_zero,zero_mul])
  calc
    _ = ∑'h:Eis,w h*star (sourceResidualFourierCoefficient h) := by
      apply tsum_congr
      intro h
      dsimp only [w]
      ring
    _ = ∑'p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
        {J:Ideal Eis // primaryGenerator J≠0}),
        w (primaryGenerator p.1.val*(primaryGenerator p.2.val)^3)*
          star (sourceResidualFourierCoefficient
            (primaryGenerator p.1.val*(primaryGenerator p.2.val)^3)) :=
      sourceFourier_tsum_primary_pairs w hw
    _ = thetaDerivativeScalar*completedBesselProfile Ψ thetaBesselScale v := by
      rw [completedBesselProfile_primary_pairs,←tsum_mul_left]
      apply tsum_congr
      intro p
      let ip := primaryCubePairToMellinIndex p
      have he := thetaPair_derivative_coefficient Ψ ip.1 ip.2 p.1.property.2 p.2.property p.1.property.1
      have hn := thetaPair_frequency_norm ip.1 ip.2 p.1.property.2 p.2.property
      change (-2*Real.pi*Complex.I*star (cuspFrequency (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)))*
          fixedThetaTwist Ψ (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)*(v:ℂ)*
          schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)‖*v)*
          star (sourceResidualFourierCoefficient (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)) =
        thetaDerivativeScalar*((completedMellinCoefficient Ψ ip*(completedMellinLength ip:ℂ))*(v:ℂ)*
          schlafliBesselK (1/3) (4*Real.pi*thetaBesselScale*Real.sqrt (completedMellinLength ip)*v))
      rw [hn,show 4*Real.pi*(thetaBesselScale*Real.sqrt (completedMellinLength ip))*v=
        4*Real.pi*thetaBesselScale*Real.sqrt (completedMellinLength ip)*v by ring]
      calc
        _ = ((-2*Real.pi*Complex.I*star (cuspFrequency (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)))*
            fixedThetaTwist Ψ (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)*
            star (sourceResidualFourierCoefficient (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)))*
            (v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*thetaBesselScale*Real.sqrt (completedMellinLength ip)*v) := by ring
        _ = _ := by rw [he];ring

end

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma horizontalWirtingerBar_finite_sum {ι : Type*} [Fintype ι]
    (f : ι→ℂ→ℂ) (weight : ι→ℂ) (z : ℂ)
    (h1 : ∀i,DifferentiableAt ℝ (fun t:ℝ=>f i (z+(t:ℂ))) 0)
    (hI : ∀i,DifferentiableAt ℝ (fun t:ℝ=>f i (z+(t:ℂ)*Complex.I)) 0) :
    horizontalWirtingerBar (fun w=>∑i,weight i*f i w) z=
      ∑i,weight i*horizontalWirtingerBar (f i) z := by
  unfold horizontalWirtingerBar
  rw [deriv_fun_sum (fun i hi=>(h1 i).const_mul (weight i)),
    deriv_fun_sum (fun i hi=>(hI i).const_mul (weight i))]
  simp only [deriv_const_mul_field,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma finiteConjugateSource_wirtingerBar_sum {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) :
    horizontalWirtingerBar (finiteConjugateSource shift weight v hv) 0=
      ∑i,weight i*cuspBarProfile cubicSourceConjugateFunction (shift i) v := by
  have hd (i : ι) (direction : ℂ) : DifferentiableAt ℝ
      (fun t:ℝ=>cubicSourceConjugateFunction (upperPoint (((t:ℂ)*direction)+shift i) v hv)) 0 := by
    have he : (fun t:ℝ=>cubicSourceConjugateFunction (upperPoint (((t:ℂ)*direction)+shift i) v hv))=
        fun t:ℝ=>star (sourceBesselCoefficients.fullFunction ((3*(Real.pi:ℂ))*constantArithmeticResidue)
          (upperPoint (shift i+(t:ℂ)*direction) v hv)) := by
      funext t
      simp only [cubicSourceConjugateFunction,cubicSourceResidualFunction_eq_bessel,sourceBesselFunction,add_comm]
    rw [he]
    exact (sourceBesselCoefficients.fullFunction_horizontal_hasDerivAt _ v hv (shift i) direction 0).differentiableAt.star
  rw [show finiteConjugateSource shift weight v hv=
    fun w=>∑i,weight i*cubicSourceConjugateFunction (upperPoint (w+shift i) v hv) from rfl]
  rw [horizontalWirtingerBar_finite_sum _ weight 0
    (fun i=>by simpa only [zero_add,mul_one] using hd i 1)
    (fun i=>by simpa only [zero_add] using hd i Complex.I)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [cuspBarProfile_positive _ _ _ hv]
  apply congrArg (fun z : ℂ => weight i * z)
  exact horizontalWirtingerBar_translate (fun z=>cubicSourceConjugateFunction (upperPoint z v hv)) (shift i)

def thetaTwistedCuspProfile (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (v : ℝ) : ℂ :=
  ∑h:Eis⧸Ideal.span {c},finiteAdditiveFourierCoeff (quotientTrace c hc)
    (fixedThetaQuotient Ψ c) h*cuspBarProfile cubicSourceConjugateFunction (thetaFourierTranslation c h) v

theorem thetaTwistedCuspProfile_eq_completedBesselProfile
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) (v : ℝ) (hv : 0<v) :
    thetaTwistedCuspProfile Ψ c hc v=thetaDerivativeScalar*completedBesselProfile Ψ thetaBesselScale v := by
  rw [←thetaTwistedSource_wirtingerBar_eq_completedBesselProfile Ψ Q hΨ c hc hcQ v hv]
  exact (finiteConjugateSource_wirtingerBar_sum (thetaFourierTranslation c)
    (finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c)) v hv).symm

end CubicEisenstein

end

end OAI
