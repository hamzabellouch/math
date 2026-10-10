import OAI.NumberTheory.DirichletL.Eisenstein.CuspAverage

namespace OAI

noncomputable section

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

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

lemma schlafliBesselK_cubic_scaled_mellin_integrable (s : ℂ) (c : ℝ)
    (hs : 1/3<s.re) (hc : 0<c) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^(s-1)*schlafliBesselK (1/3) (c*v))
      (Set.Ioi 0) volume := by
  have hb : MellinConvergent (fun v => schlafliBesselK (1/3) v) s := by
    simpa only [MellinConvergent,smul_eq_mul] using schlafliBesselK_cubic_mellin_integrable s hs
  have hh := (MellinConvergent.comp_mul_left
    (f := fun v => schlafliBesselK (1/3) v) (s := s) hc).mpr hb
  simpa only [MellinConvergent,smul_eq_mul] using hh

lemma schlafliBesselK_cubic_scaled_mellin (s : ℂ) (c : ℝ)
    (hs : 1/3<s.re) (hc : 0<c) :
    (∫v : ℝ in Set.Ioi 0,(v:ℂ)^(s-1)*schlafliBesselK (1/3) (c*v)) =
      (c:ℂ)^(-s)*((2:ℂ)^(s-2)*Complex.Gamma ((s-1/3)/2)*Complex.Gamma ((s+1/3)/2)) := by
  have hh := mellin_comp_mul_left (fun v => schlafliBesselK (1/3) v) s hc
  simp only [mellin,smul_eq_mul] at hh
  rw [schlafliBesselK_cubic_mellin s hs] at hh
  exact hh

lemma source_cubic_bessel_mellin_integrable (s freq : ℂ)
    (hs : -(1/3)<s.re) (hfreq : freq≠0) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^(2*s)*
      schlafliBesselK (1/3) (4*Real.pi*‖freq‖*v)) (Set.Ioi 0) volume := by
  have hc : 0<4*Real.pi*‖freq‖ := by positivity
  have ht : 1/3<(2*s+1).re := by norm_num; linarith
  simpa only [show (2*s+1:ℂ)-1=2*s by ring] using
    schlafliBesselK_cubic_scaled_mellin_integrable (2*s+1) (4*Real.pi*‖freq‖) ht hc

theorem source_cubic_bessel_mellin (s freq : ℂ)
    (hs : -(1/3)<s.re) (hfreq : freq≠0) :
    (∫v : ℝ in Set.Ioi 0,(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*‖freq‖*v)) =
      ((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
        ((4*Real.pi*‖freq‖:ℝ):ℂ)^(2*s+1) := by
  have hc : 0<4*Real.pi*‖freq‖ := by positivity
  have ht : 1/3<(2*s+1).re := by norm_num; linarith
  have hh := schlafliBesselK_cubic_scaled_mellin (2*s+1) (4*Real.pi*‖freq‖) ht hc
  rw [show (2*s+1:ℂ)-1=2*s by ring,
    show (2*s+1:ℂ)-2=2*s-1 by ring,
    show ((2*s+1:ℂ)-1/3)/2=s+1/3 by ring,
    show ((2*s+1:ℂ)+1/3)/2=s+2/3 by ring,Complex.cpow_neg] at hh
  rw [hh]
  ring

end CubicEisenstein

open scoped BigOperators Classical

namespace ShortDraftCRT

section
variable {R : Type*} [CommRing R]

theorem exists_fixed_completion (M c r a d0 : R)
    (hfixed : c∣a*d0-1) (hr : IsCoprime r (M*c)) (ha : IsCoprime a r) :
    ∃b d : R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 := by
  have hcr : IsCoprime c r := hr.of_mul_right_right.symm
  obtain ⟨u,v,huv⟩ := hr
  obtain ⟨x,y,hxy⟩ := ha
  let d : R := d0*u*r+x*v*(M*c)
  have hd : M*c∣d-d0 := by
    refine ⟨v*(x-d0),?_⟩
    dsimp [d]
    linear_combination d0*huv
  have hdr : r∣d-x := by
    refine ⟨u*(d0-x),?_⟩
    dsimp [d]
    linear_combination x*huv
  have hcd : c∣a*d-1 := by
    have hdiff : c∣a*(d-d0) := dvd_mul_of_dvd_right
      ((dvd_mul_left c M).trans hd) a
    convert dvd_add hdiff hfixed using 1 ; ring
  have hrd : r∣a*d-1 := by
    have hx : r∣a*x-1 := by
      refine ⟨-y,?_⟩
      linear_combination hxy
    have hdiff : r∣a*(d-x) := dvd_mul_of_dvd_right hdr a
    convert dvd_add hdiff hx using 1 ; ring
  obtain ⟨b,hb⟩ := hcr.mul_dvd hcd hrd
  refine ⟨b,d,?_,hd⟩
  linear_combination hb

variable [IsDomain R]

theorem fixed_completion_congr (M c r r0 a a0 b b0 d d0 : R)
    (hc : c≠0) (hr : IsCoprime M r)
    (hdet : a*d-b*(c*r)=1) (hdet0 : a0*d0-b0*(c*r0)=1)
    (ha : M*c∣a-a0) (hd : M*c∣d-d0) (hrr : M∣r-r0) : M∣b-b0 := by
  have hprod : M*c∣a*d-a0*d0 := by
    have h1 := dvd_mul_of_dvd_left ha d
    have h2 := dvd_mul_of_dvd_right hd a0
    convert dvd_add h1 h2 using 1 ; ring
  have hcancel : M*c∣c*(b*r-b0*r0) := by
    convert hprod using 1
    linear_combination -hdet+hdet0
  have hbr : M∣b*r-b0*r0 := by
    rw [mul_comm M c] at hcancel
    exact (mul_dvd_mul_iff_left hc).mp hcancel
  have hsub : M∣(b-b0)*r := by
    have hsmall := dvd_mul_of_dvd_right hrr b0
    convert dvd_sub hbr hsmall using 1 ; ring
  exact hr.dvd_of_dvd_mul_right hsub

end

open scoped BigOperators Classical Matrix

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
lemma quotient_eq_of_dvd_sub (M x y : R) (h : M ∣ x-y) :
    Ideal.Quotient.mk (Ideal.span {M}) x = Ideal.Quotient.mk (Ideal.span {M}) y := by
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)

theorem fixed_completion_matrix_congr (M c r r0 a a0 b b0 d d0 : R)
    (hc : c≠0) (hr : IsCoprime M r)
    (hdet : a*d-b*(c*r)=1) (hdet0 : a0*d0-b0*(c*r0)=1)
    (ha : M*c∣a-a0) (hd : M*c∣d-d0) (hrr : M∣r-r0) :
    (!![a,b;c*r,d] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M})) =
      (!![a0,b0;c*r0,d0] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M})) := by
  have hqa := quotient_eq_of_dvd_sub M a a0 ((dvd_mul_right M c).trans ha)
  have hqd := quotient_eq_of_dvd_sub M d d0 ((dvd_mul_right M c).trans hd)
  have hqb := quotient_eq_of_dvd_sub M b b0
    (fixed_completion_congr M c r r0 a a0 b b0 d d0 hc hr hdet hdet0 ha hd hrr)
  have hqc : Ideal.Quotient.mk (Ideal.span {M}) (c*r) =
      Ideal.Quotient.mk (Ideal.span {M}) (c*r0) := by
    apply quotient_eq_of_dvd_sub
    simpa only [mul_sub] using dvd_mul_of_dvd_right hrr c
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.map_apply,] <;>
    assumption

theorem exists_fixed_matrix_completion (M c a0 r0 d0 b0 : R)
    (hc : c≠0) (hdet0 : a0*d0-b0*(c*r0)=1) :
    ∀a r : R, M*c∣a-a0 → M∣r-r0 → IsCoprime r (M*c) → IsCoprime a r →
      ∃b d : R, a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧
        (!![a,b;c*r,d] : Matrix (Fin 2) (Fin 2) R).map
            (Ideal.Quotient.mk (Ideal.span {M})) =
          (!![a0,b0;c*r0,d0] : Matrix (Fin 2) (Fin 2) R).map
            (Ideal.Quotient.mk (Ideal.span {M})) := by
  intro a r ha hrr hr har
  have hbase : c ∣ a0*d0-1 := by
    refine ⟨b0*r0,?_⟩
    linear_combination hdet0
  have hfixed : c ∣ a*d0-1 := by
    have hdiff := dvd_mul_of_dvd_left ((dvd_mul_left c M).trans ha) d0
    convert dvd_add hdiff hbase using 1 ; ring
  obtain ⟨b,d,hdet,hd⟩ := exists_fixed_completion M c r a d0 hfixed hr har
  exact ⟨b,d,hdet,hd,fixed_completion_matrix_congr M c r r0 a a0 b b0 d d0 hc
    hr.of_mul_right_left.symm hdet hdet0 ha hd hrr⟩

end ShortDraftCRT

open scoped BigOperators Classical
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def conductorReduction (a b:Eis):
    (Eis⧸Ideal.span {a*b})→+*(Eis⧸Ideal.span {a}):=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right a b))

lemma conductorReduction_surjective (a b:Eis):Function.Surjective (conductorReduction a b):=
  Ideal.Quotient.factor_surjective _

def quotientTrace (c:Eis) (hc:c≠0):AddChar (Eis⧸Ideal.span {c}) ℂ:=
  eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc

lemma quotientTrace_mk (c:Eis) (hc:c≠0) (x:Eis):
    quotientTrace c hc (Ideal.Quotient.mk _ x)=residueAdditive (3*x) c 1:=by
  simp only [quotientTrace,eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  unfold residueAdditive cuspFrequency
  simp only [map_mul,map_one,map_ofNat]
  congr 1
  ring

def conductorFourier (a b:Eis) (ha:a≠0) (hb:b≠0)
    (F:(Eis⧸Ideal.span {a})→ℂ) (h:Eis):ℂ:=
  ∑'x:Eis⧸Ideal.span {a*b},F (conductorReduction a b x)*
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ h*x)

lemma conductorFourier_shift (a b:Eis) (ha:a≠0) (hb:b≠0)
    (F:(Eis⧸Ideal.span {a})→ℂ) (h t:Eis):
    conductorFourier a b ha hb F h=
      quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (h*a*t))*
        conductorFourier a b ha hb F h:=by
  let q:Eis⧸Ideal.span {a*b}:=Ideal.Quotient.mk _ (a*t)
  have hq:conductorReduction a b q=0:=by
    change Ideal.Quotient.mk (Ideal.span {a}) (a*t)=0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨t,rfl⟩)
  unfold conductorFourier
  conv_lhs => rw [←(Equiv.addRight q).tsum_eq]
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  change F (conductorReduction a b (x+q))*
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ h*(x+q))=_
  simp only [map_add,hq,add_zero,mul_add,AddChar.map_add_eq_mul]
  have he:Ideal.Quotient.mk (Ideal.span {a*b}) h*q=Ideal.Quotient.mk _ (h*a*t):=by
    dsimp [q]
    rw [←map_mul]
    congr 1
    ring
  rw [he]
  ring

theorem conductorFourier_support (a b:Eis) (ha:a≠0) (hb:b≠0)
    (F:(Eis⧸Ideal.span {a})→ℂ) (h:Eis)
    (hF:conductorFourier a b ha hb F h≠0):b∣h:=by
  have hphase (t:Eis):
      quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (h*a*t))=1:=by
    apply mul_right_cancel₀ hF
    rw [one_mul,←conductorFourier_shift]
  have hz:Ideal.Quotient.mk (Ideal.span {a*b}) (h*a)=0:=by
    by_contra hn
    apply GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (a*b) (mul_ne_zero ha hb) hn
    ext x
    obtain ⟨t,rfl⟩:=Ideal.Quotient.mk_surjective x
    simpa only [AddChar.mulShift_apply,←map_mul,AddChar.one_apply,quotientTrace] using hphase t
  have hd:a*b∣h*a:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hd':a*b∣a*h:=by simpa only [mul_comm h a] using hd
  exact (mul_dvd_mul_iff_left ha).mp hd'

lemma conductorReduction_kernel_card (a b:Eis) (ha:a≠0) (_hb:b≠0):
    Nat.card (conductorReduction a b).toAddMonoidHom.ker=Ideal.absNorm (Ideal.span {b}):=by
  have hc:=card_ring_eq_card_mul_kernel (conductorReduction a b)
    (conductorReduction_surjective a b)
  change Ideal.absNorm (Ideal.span {a*b})=
    Ideal.absNorm (Ideal.span {a})*Nat.card (conductorReduction a b).toAddMonoidHom.ker at hc
  conv_lhs at hc => rw [←Ideal.span_singleton_mul_span_singleton,map_mul]
  have hpos:0<Ideal.absNorm (Ideal.span {a}):=by
    apply Nat.pos_iff_ne_zero.mpr
    intro hz
    exact ha (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz))
  exact (Nat.eq_of_mul_eq_mul_left hpos hc).symm

private theorem finite_tsum_conductor_pullback {R S:Type*} [AddGroup R] [AddGroup S]
    [Finite R] [Finite S] (f:R→+S) (hf:Function.Surjective f) (F:S→ℂ):
    (∑'x:R,F (f x))=(Nat.card f.ker:ℂ)*∑'y:S,F y:=by
  let:Fintype R:=Fintype.ofFinite _
  let:Fintype S:=Fintype.ofFinite _
  let:Fintype f.ker:=Fintype.ofFinite _
  rw [tsum_fintype,tsum_fintype,←Fintype.sum_fiberwise' f F]
  have hc (y:S):Fintype.card {x:R//f x=y}=Fintype.card f.ker:=
    Fintype.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf y)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hc,Nat.card_eq_fintype_card]
  rw [Finset.mul_sum]

lemma quotientTrace_conductor_scale (a b k:Eis) (ha:a≠0) (hb:b≠0)
    (x:Eis⧸Ideal.span {a*b}):
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (b*k)*x)=
      quotientTrace a ha (Ideal.Quotient.mk _ k*conductorReduction a b x):=by
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  change quotientTrace (a*b) (mul_ne_zero ha hb)
    (Ideal.Quotient.mk _ (b*k)*Ideal.Quotient.mk _ d)=
    quotientTrace a ha (Ideal.Quotient.mk _ k*Ideal.Quotient.mk _ d)
  rw [←map_mul,←map_mul,quotientTrace_mk,quotientTrace_mk]
  simp only [residueAdditive,cuspFrequency,map_mul,map_one,map_ofNat]
  congr 1
  have hae:=eisEmbedding_ne_zero ha
  have hbe:=eisEmbedding_ne_zero hb
  field_simp

theorem conductorFourier_lift (a b:Eis) (ha:a≠0) (hb:b≠0)
    (F:(Eis⧸Ideal.span {a})→ℂ) (k:Eis):
    conductorFourier a b ha hb F (b*k)=
      (Ideal.absNorm (Ideal.span {b}):ℂ)*
        ∑'x:Eis⧸Ideal.span {a},F x*quotientTrace a ha (Ideal.Quotient.mk _ k*x):=by
  let:Finite (Eis⧸Ideal.span {a*b}):=finite_quotient_span (mul_ne_zero ha hb)
  let:Finite (Eis⧸Ideal.span {a}):=finite_quotient_span ha
  unfold conductorFourier
  calc
    _=∑'x:Eis⧸Ideal.span {a*b},F (conductorReduction a b x)*
        quotientTrace a ha (Ideal.Quotient.mk _ k*conductorReduction a b x):=by
      apply tsum_congr
      intro x
      rw [quotientTrace_conductor_scale a b k ha hb]
    _=_:=by
      have he:=finite_tsum_conductor_pullback (conductorReduction a b).toAddMonoidHom
        (conductorReduction_surjective a b)
        (fun y=>F y*quotientTrace a ha (Ideal.Quotient.mk _ k*y))
      rw [conductorReduction_kernel_card a b ha hb] at he
      exact he

end
section

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSymbol_pow_denominator (x p:Eis) (n:ℕ):
    symbol x (p^n)=(symbol x p)^n:=by
  induction n with
  | zero=>simp
  | succ n ih=>rw [pow_succ,symbol_mul_denominator,ih,pow_succ]

def primeCubicMulChar (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    MulChar (Eis⧸Ideal.span {p}) ℂ:=by
  letI:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg:lambda∉(Ideal.span {p}:Ideal Eis):=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  refine {toFun:=fun x=>eisEmbedding (symbol (GaussianShiftedPartition.representative p x) p)
          map_one':=?_,map_mul':=?_,map_nonunit':=?_}
  · have hd:p∣GaussianShiftedPartition.representative p 1-1:=by
      simpa only [map_one] using gaussRep_mk_congr p 1
    rw [symbol_congr hd,symbol_one_numerator p hprimary,map_one]
  · intro x y
    have hd:p∣GaussianShiftedPartition.representative p (x*y)-
        GaussianShiftedPartition.representative p x*GaussianShiftedPartition.representative p y:=by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      simp only [map_mul,GaussianShiftedPartition.representative_spec]
    rw [symbol_congr hd,symbol_mul_numerator _ _ p hprimary,map_mul]
  · intro x hx
    rw [symbol_prime p hp hprimary,primeValue_eq _ hg,
      GaussianShiftedPartition.representative_spec,MulChar.map_nonunit _ hx,map_zero]

lemma primeCubicMulChar_mk (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (x:Eis):
    primeCubicMulChar p hp hprimary (Ideal.Quotient.mk _ x)=eisEmbedding (symbol x p):=by
  change eisEmbedding (symbol (GaussianShiftedPartition.representative p
    (Ideal.Quotient.mk _ x)) p)=_
  rw [symbol_congr (gaussRep_mk_congr p x)]

lemma quotientTrace_mk_product (c:Eis) (hc:c≠0) (h d:Eis):
    quotientTrace c hc (Ideal.Quotient.mk _ h*Ideal.Quotient.mk _ d)=
      residueAdditive (3*h) c d:=by
  rw [←map_mul,quotientTrace_mk]
  unfold residueAdditive cuspFrequency
  simp only [map_mul,map_one,map_ofNat]
  congr 1
  ring

lemma conductorReduction_prime_power_unit (p:Eis) (n:ℕ)
    (x:Eis⧸Ideal.span {p*p^n}):
    IsUnit (conductorReduction p (p^n) x)↔IsUnit x:=by
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  change IsUnit (Ideal.Quotient.mk (Ideal.span {p}) d)↔
    IsUnit (Ideal.Quotient.mk (Ideal.span {p*p^n}) d)
  rw [isUnit_quotient_span_iff,isUnit_quotient_span_iff,←pow_succ',
    IsCoprime.pow_left_iff (Nat.succ_pos n)]

theorem cubicUnitGaussSum_prime_power_fourier (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis):
    cubicUnitGaussSum h (p^(n+1))=
      conductorFourier p (p^n) hp.ne_zero (pow_ne_zero _ hp.ne_zero)
        (fun x=>(primeCubicMulChar p hp hprimary^(n+1)) x) h:=by
  let χ:=primeCubicMulChar p hp hprimary
  let f:(Eis⧸Ideal.span {p*p^n})→ℂ:=fun x=>
    (χ^(n+1)) (conductorReduction p (p^n) x)*
      quotientTrace (p*p^n) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
        (Ideal.Quotient.mk _ h*x)
  have hsup:Function.support f⊆{x|IsUnit x}:=by
    intro x hx
    by_contra hn
    have hn':¬IsUnit (conductorReduction p (p^n) x):=
      fun hh=>hn ((conductorReduction_prime_power_unit p n x).mp hh)
    exact hx (by dsimp [f];rw [MulChar.map_nonunit _ hn',zero_mul])
  rw [pow_succ']
  change cubicUnitGaussSum h (p*p^n)=∑'x,f x
  rw [←tsum_subtype_eq_of_support_subset hsup]
  unfold cubicUnitGaussSum
  apply tsum_congr
  intro x
  let d:=GaussianShiftedPartition.representative (p*p^n) x.val
  have hd:Ideal.Quotient.mk (Ideal.span {p*p^n}) d=x.val:=
    GaussianShiftedPartition.representative_spec _ _
  change eisEmbedding (symbol d (p*p^n))*residueAdditive (3*h) (p*p^n) d=f x.val
  rw [←hd]
  dsimp [f]
  change _=(χ^(n+1)) (Ideal.Quotient.mk _ d)*_
  rw [MulChar.pow_apply' _ (Nat.succ_ne_zero n),primeCubicMulChar_mk,
    quotientTrace_mk_product,←pow_succ',cubicSymbol_pow_denominator,map_pow]

theorem cubicUnitGaussSum_prime_power_support (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis)
    (hne:cubicUnitGaussSum h (p^(n+1))≠0):p^n∣h:=by
  rw [cubicUnitGaussSum_prime_power_fourier p hp hprimary n h] at hne
  exact conductorFourier_support p (p^n) hp.ne_zero (pow_ne_zero _ hp.ne_zero) _ h hne

def primeCubicGauss (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis):ℂ:=
  ∑'x:Eis⧸Ideal.span {p},(primeCubicMulChar p hp hprimary^e) x*
    quotientTrace p hp.ne_zero (Ideal.Quotient.mk _ h*x)

theorem cubicUnitGaussSum_prime_power_lift (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis):
    cubicUnitGaussSum (p^n*h) (p^(n+1))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^n*primeCubicGauss p hp hprimary (n+1) h:=by
  rw [cubicUnitGaussSum_prime_power_fourier p hp hprimary n,
    conductorFourier_lift p (p^n) hp.ne_zero (pow_ne_zero _ hp.ne_zero)]
  have hn:Ideal.absNorm (Ideal.span {p^n})=Ideal.absNorm (Ideal.span {p})^n:=by
    rw [←Ideal.span_singleton_pow,map_pow]
  rw [hn,Nat.cast_pow]
  rfl

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma primeCubicMulChar_cube (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    primeCubicMulChar p hp hprimary^3=1:=by
  apply DFunLike.ext
  intro x
  by_cases hx:IsUnit x
  · obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
    rw [MulChar.pow_apply' _ (by decide),primeCubicMulChar_mk,←map_pow,
      symbol_cube_of_isCoprime d p hprimary ((isUnit_quotient_span_iff p d).mp hx).symm,map_one]
    exact (MulChar.one_apply_coe hx.unit).symm
  · rw [MulChar.map_nonunit _ hx,MulChar.map_nonunit _ hx]

lemma primeCubicMulChar_ne_one (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    primeCubicMulChar p hp hprimary≠1:=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg:lambda∉(Ideal.span {p}:Ideal Eis):=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  intro hchar
  apply cubicChar_ne_one (Ideal.span {p}) hg
  apply DFunLike.ext
  intro x
  by_cases hx:IsUnit x
  · obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
    have he:=congrArg (fun χ:MulChar (Eis⧸Ideal.span {p}) ℂ=>χ (Ideal.Quotient.mk _ d)) hchar
    rw [primeCubicMulChar_mk,symbol_prime p hp hprimary,primeValue_eq _ hg] at he
    have hoc:(1:MulChar (Eis⧸Ideal.span {p}) ℂ) (Ideal.Quotient.mk _ d)=1:=
      MulChar.one_apply_coe hx.unit
    have hoo:(1:MulChar (Eis⧸Ideal.span {p}) Eis) (Ideal.Quotient.mk _ d)=1:=
      MulChar.one_apply_coe hx.unit
    rw [hoo]
    apply eisEmbedding_injective
    simpa only [hoc,map_one] using he
  · rw [MulChar.map_nonunit _ hx,MulChar.map_nonunit _ hx]

lemma primeCubicMulChar_order (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    orderOf (primeCubicMulChar p hp hprimary)=3:=by
  have hd:=orderOf_dvd_of_pow_eq_one (primeCubicMulChar_cube p hp hprimary)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1|h3
  · exact False.elim (primeCubicMulChar_ne_one p hp hprimary (orderOf_eq_one_iff.mp h1))
  · exact h3

lemma primeCubicMulChar_pow_eq_one (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (e:ℕ):
    primeCubicMulChar p hp hprimary^e=1↔3∣e:=by
  rw [←orderOf_dvd_iff_pow_eq_one,primeCubicMulChar_order]

lemma primeCubicGauss_mod_three (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (e:ℕ) (h:Eis):
    primeCubicGauss p hp hprimary e h=primeCubicGauss p hp hprimary (e%3) h:=by
  unfold primeCubicGauss
  have he:=pow_mod_orderOf (primeCubicMulChar p hp hprimary) e
  rw [primeCubicMulChar_order] at he
  rw [he]

lemma primeCubicGauss_eq_gaussSum (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis) [Fintype (Eis⧸Ideal.span {p})]:
    primeCubicGauss p hp hprimary e h=
      gaussSum (primeCubicMulChar p hp hprimary^e)
        ((quotientTrace p hp.ne_zero).mulShift (Ideal.Quotient.mk _ h)):=by
  simp only [primeCubicGauss,tsum_fintype,gaussSum,AddChar.mulShift_apply]

theorem primeCubicGauss_of_dvd (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis) (hph:p∣h):
    primeCubicGauss p hp hprimary e h=
      if 3∣e then (Ideal.absNorm (Ideal.span {p}):ℂ)-1 else 0:=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  have hh:Ideal.Quotient.mk (Ideal.span {p}) h=0:=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hph)
  rw [primeCubicGauss_eq_gaussSum,hh,AddChar.mulShift_zero]
  split_ifs with he
  · rw [(primeCubicMulChar_pow_eq_one p hp hprimary e).mpr he,gaussSum_one_one,
      Nat.card_units,Nat.cast_sub (Nat.succ_le_of_lt Nat.card_pos),Nat.cast_one]
    rfl
  · exact gaussSum_one_right (fun hχ=>he ((primeCubicMulChar_pow_eq_one p hp hprimary e).mp hχ))

theorem primeCubicGauss_trivial_nonzero (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (he:3∣e) (h:Eis) (hph:¬p∣h):
    primeCubicGauss p hp hprimary e h=-1:=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  have hh:Ideal.Quotient.mk (Ideal.span {p}) h≠0:=by
    intro hh
    exact hph (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hh))
  rw [primeCubicGauss_eq_gaussSum,(primeCubicMulChar_pow_eq_one p hp hprimary e).mpr he]
  exact gaussSum_one_left (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero hh)

theorem primeCubicGauss_one_mul_two (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (h:Eis) (hph:¬p∣h):
    primeCubicGauss p hp hprimary 1 h*primeCubicGauss p hp hprimary 2 h=
      (Ideal.absNorm (Ideal.span {p}):ℂ):=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  have hh:Ideal.Quotient.mk (Ideal.span {p}) h≠0:=by
    intro hh
    exact hph (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hh))
  have hψ:((quotientTrace p hp.ne_zero).mulShift (Ideal.Quotient.mk _ h)).IsPrimitive:=
    AddChar.IsPrimitive.of_ne_one (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero hh)
  have he:=gaussSum_mul_gaussSum_pow_orderOf_sub_one
    (primeCubicMulChar_ne_one p hp hprimary) hψ
  rw [primeCubicMulChar_order] at he
  have hm:=MulChar.val_neg_one_eq_one_of_odd_order (by decide:Odd 3)
    (primeCubicMulChar_cube p hp hprimary)
  rw [hm,one_mul] at he
  change _=(Nat.card (Eis⧸Ideal.span {p}):ℂ)
  simpa only [primeCubicGauss_eq_gaussSum,pow_one,Nat.reduceSub,
    Nat.card_eq_fintype_card] using he

lemma primeCubicGauss_one_eq (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (h:Eis):
    primeCubicGauss p hp hprimary 1 h=cubicUnitGaussSum h p:=by
  have he:=cubicUnitGaussSum_prime_power_lift p hp hprimary 0 h
  simpa only [pow_zero,one_mul,pow_one,Nat.zero_add] using he.symm

end CubicEisenstein

end

end OAI
