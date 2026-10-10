import OAI.NumberTheory.DirichletL.Cusp.WeylRepresentatives

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

namespace ShortDraftCRT
open scoped BigOperators Classical Matrix MatrixGroups

section
open ActualEisensteinCubic CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma primary_coprime_nine (a:Eis) (ha:lambda^2∣a-1) : IsCoprime a (9:Eis) := by
  have h3:=primary_coprime_three a ha
  simpa only [show (3:Eis)*3=9 by norm_num] using h3.mul_right h3

lemma nine_coprime_of_not_lambda_dvd (c:Eis) (hc:¬lambda∣c) : IsCoprime (9:Eis) c := by
  have hL:IsCoprime lambda c:=
    PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr hc
  have h3:IsCoprime (3:Eis) c:=(hL.mul_left hL).of_isCoprime_of_dvd_left
    (by simpa only [pow_two] using three_dvd_lambda_sq)
  simpa only [show (3:Eis)*3=9 by norm_num] using h3.mul_left h3

lemma primary_numerator_controlled_inverse (c a:Eis)
    (ha:lambda^2∣a-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)*c∣a*d0-1 :=
  exists_controlled_inverse 9 c a ((primary_coprime_nine a ha).mul_right hac)

lemma completion_primary_lower_right (a b c d:Eis)
    (hdet:a*d-b*c=1) (ha:(3:Eis)∣a-1) (hb:(3:Eis)∣b) : (3:Eis)∣d-1 := by
  have had:(3:Eis)∣a*d-1:=by
    convert dvd_mul_of_dvd_left hb c using 1
    linear_combination hdet
  convert dvd_sub had (dvd_mul_of_dvd_left ha d) using 1 ; ring

lemma completion_negative_upper_right (a b c d:Eis)
    (hdet:a*d-b*c=1) (hc:(3:Eis)∣c-1) (hd:(3:Eis)∣d) : (3:Eis)∣b+1 := by
  have hbc:(3:Eis)∣b*c+1:=by
    convert dvd_mul_of_dvd_right hd a using 1
    linear_combination -hdet
  convert dvd_sub hbc (dvd_mul_of_dvd_right hc b) using 1 ; ring

theorem exists_primary_numerator_completion (M c a:Eis)
    (hc:c≠0) (h9M:(9:Eis)∣M) (ha:lambda^2∣a-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)*c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→lambda^2∣r-1→
      ∃b d:Eis,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ (9:Eis)∣b ∧
        (3:Eis)∣d-1 ∧ (3:Eis)∣c*r-c := by
  obtain ⟨d0,hd0⟩:=primary_numerator_controlled_inverse c a ha hac
  refine ⟨d0,hd0,?_⟩
  intro r hr har hprimary
  obtain ⟨b,d,hdet,hd,hb⟩:=exists_fixed_completion_upper_right 9 M c r a d0 hc h9M hr har hd0
  refine ⟨b,d,hdet,hd,hb,completion_primary_lower_right a b (c*r) d hdet
    (three_dvd_primary_sub_one a ha) ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hb),?_⟩
  convert dvd_mul_of_dvd_right (three_dvd_primary_sub_one r hprimary) c using 1 ; ring

theorem exists_unramified_denominator_completion (M c a:Eis)
    (h9M:(9:Eis)∣M) (hc:¬lambda∣c) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)∣d0 ∧ c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→
      ∃b d:Eis,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ (9:Eis)∣d ∧
        (9:Eis)∣a*d ∧ (9:Eis)∣b*(c*r)+1 := by
  obtain ⟨d0,hzero,hinv⟩:=exists_controlled_zero_inverse 9 c a
    (nine_coprime_of_not_lambda_dvd c hc) hac
  exact ⟨d0,hzero,hinv,fun r hr har=>exists_fixed_completion_lower_right 9 M c r a d0
    h9M hr har hzero hinv⟩

theorem exists_primary_denominator_completion (M c a:Eis)
    (h9M:(9:Eis)∣M) (hc:lambda^2∣c-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)∣d0 ∧ c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→lambda^2∣r-1→
      ∃b d:Eis,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ (9:Eis)∣d ∧
        (9:Eis)∣a*d ∧ (9:Eis)∣b*(c*r)+1 ∧ (3:Eis)∣b+1 ∧ (3:Eis)∣c*r-1 := by
  have hcl:¬lambda∣c:=by
    intro hd
    have hcL:IsCoprime lambda c:=
      (primary_coprime_three c hc).symm.of_isCoprime_of_dvd_left
        ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three)
    exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (hcL.isUnit_of_dvd hd)
  obtain ⟨d0,hzero,hinv,hcomp⟩:=exists_unramified_denominator_completion M c a h9M hcl hac
  refine ⟨d0,hzero,hinv,?_⟩
  intro r hr har hpr
  obtain ⟨b,d,hdet,hd,hBd,had,hbc⟩:=hcomp r hr har
  have hc3:(3:Eis)∣c*r-1:=three_dvd_primary_sub_one _ (primary_mul c r hc hpr)
  exact ⟨b,d,hdet,hd,hBd,had,hbc,completion_negative_upper_right a b (c*r) d hdet hc3
    ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hBd),hc3⟩

end

section
variable {R:Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
lemma controlled_inverse_sector (B M c a a0 d0:R)
    (hBM:B∣M) (ha:M*c∣a-a0) (hinv:B*c∣a0*d0-1) : B*c∣a*d0-1 := by
  have hdiff:=dvd_mul_of_dvd_left ((mul_dvd_mul_right hBM c).trans ha) d0
  convert dvd_add hdiff hinv using 1 ; ring

theorem exists_fixed_matrix_completion_controlled
    (B N M c a0 r0 b0 d0 bResidue dResidue:R)
    (hc:c≠0) (hBM:B∣M) (hNM:N∣M)
    (hdet0:a0*d0-b0*(c*r0)=1)
    (hb0:B∣b0-bResidue) (hd0:N∣d0-dResidue) :
    ∀a r:R,M*c∣a-a0→M∣r-r0→IsCoprime r (M*c)→IsCoprime a r→
      ∃b d:R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ B∣b-bResidue ∧ N∣d-dResidue ∧
        (!![a,b;c*r,d]:Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M}))=
        (!![a0,b0;c*r0,d0]:Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M})) := by
  intro a r ha hrr hr har
  obtain ⟨b,d,hdet,hd,hmat⟩:=exists_fixed_matrix_completion M c a0 r0 d0 b0 hc hdet0
    a r ha hrr hr har
  have hbd:B∣b-b0:=hBM.trans (fixed_completion_congr M c r r0 a a0 b b0 d d0 hc
    hr.of_mul_right_left.symm hdet hdet0 ha hd hrr)
  have hdd:N∣d-d0:=(hNM.trans (dvd_mul_right M c)).trans hd
  refine ⟨b,d,hdet,hd,?_,?_,hmat⟩
  · convert dvd_add hbd hb0 using 1 ; ring
  · convert dvd_add hdd hd0 using 1 ; ring

end

section
open ActualEisensteinCubic CubicEisenstein CubicJacobiGlobal CubicKubota ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O

def controlledCompletionMatrix (a b c d:Eis) (hdet:a*d-b*c=1) : SL(2,Eis) :=
  ⟨!![a,b;c,d],by simpa [Matrix.det_fin_two] using hdet⟩

theorem exists_primary_numerator_matrix (M c a:Eis)
    (hc:c≠0) (h9M:(9:Eis)∣M) (ha:lambda^2∣a-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)*c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→lambda^2∣r-1→
      ∃g:SL(2,Eis),g 0 0=a ∧ g 1 0=c*r ∧ M*c∣g 1 1-d0 ∧
        (9:Eis)∣g 0 1 ∧ (3:Eis)∣g 0 0-1 ∧ (3:Eis)∣g 1 1-1 ∧ (3:Eis)∣g 1 0-c := by
  obtain ⟨d0,hd0,hcomp⟩:=exists_primary_numerator_completion M c a hc h9M ha hac
  refine ⟨d0,hd0,?_⟩
  intro r hr har hpr
  obtain ⟨b,d,hdet,hd,hb,hd3,hc3⟩:=hcomp r hr har hpr
  exact ⟨controlledCompletionMatrix a b (c*r) d hdet,rfl,rfl,hd,hb,
    three_dvd_primary_sub_one a ha,hd3,hc3⟩

theorem exists_primary_denominator_matrix (M c a:Eis)
    (h9M:(9:Eis)∣M) (hc:lambda^2∣c-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)∣d0 ∧ c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→lambda^2∣r-1→
      ∃g:SL(2,Eis),g 0 0=a ∧ g 1 0=c*r ∧ M*c∣g 1 1-d0 ∧
        (9:Eis)∣g 1 1 ∧ (9:Eis)∣g 0 0*g 1 1 ∧
        (9:Eis)∣g 0 1*g 1 0+1 ∧ (3:Eis)∣g 0 1+1 ∧ (3:Eis)∣g 1 0-1 := by
  obtain ⟨d0,hzero,hinv,hcomp⟩:=exists_primary_denominator_completion M c a h9M hc hac
  refine ⟨d0,hzero,hinv,?_⟩
  intro r hr har hpr
  obtain ⟨b,d,hdet,hd,hBd,had,hbc,hb3,hc3⟩:=hcomp r hr har hpr
  exact ⟨controlledCompletionMatrix a b (c*r) d hdet,rfl,rfl,hd,hBd,had,hbc,hb3,hc3⟩

lemma controlled_primary_principal (g:SL(2,Eis)) (c:Eis)
    (ha:(3:Eis)∣g 0 0-1) (hb:(9:Eis)∣g 0 1)
    (hc:(3:Eis)∣g 1 0-c) (hc0:(3:Eis)∣c) (hd:(3:Eis)∣g 1 1-1) :
    g∈levelThree := by
  apply A3_principal_mem_levelThree g ha
    ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hb) _ hd
  convert dvd_add hc hc0 using 1 ; ring

lemma controlled_primary_ramified (g:SL(2,Eis)) (c u:Eis)
    (ha:(3:Eis)∣g 0 0-1) (hb:(9:Eis)∣g 0 1)
    (hc:(3:Eis)∣g 1 0-c) (hcu:(3:Eis)∣c-u) (hd:(3:Eis)∣g 1 1-1) :
    g*(lowerCuspMatrix u)⁻¹∈levelThree := by
  apply A3_ramified_mem_levelThree g u ha
    ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hb) _ hd
  convert dvd_add hc hcu using 1 ; ring

lemma controlled_denominator_unramified (g:SL(2,Eis)) (u:Eis)
    (ha:(3:Eis)∣g 0 0-u) (hb:(3:Eis)∣g 0 1+1)
    (hc:(3:Eis)∣g 1 0-1) (hd:(9:Eis)∣g 1 1) :
    g*(A3WeylCusp u)⁻¹∈levelThree :=
  A3_unramified_mem_levelThree g u ha hb hc ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hd)

end

open ActualEisensteinCubic CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem exists_primary_numerator_sector_completions {ι Q:Type*}
    (M c:Eis) (hc:c≠0) (h9M:(9:Eis)∣M)
    (sector:ι→Q) (a r:ι→Eis)
    (haPrimary:∀i,lambda^2∣a i-1) (hrPrimary:∀i,lambda^2∣r i-1)
    (hcop:∀i,IsCoprime (a i) (c*r i)) (hr:∀i,IsCoprime (r i) (M*c))
    (ha:∀i j,sector i=sector j→M*c∣a i-a j)
    (hrr:∀i j,sector i=sector j→M∣r i-r j) :
    ∃(b d:ι→Eis) (C:Q→Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {M})),
      (∀i,a i*d i-b i*(c*r i)=1) ∧ (∀i,(9:Eis)∣b i) ∧ (∀i,(3:Eis)∣d i-1) ∧
      ∀i,(!![a i,b i;c*r i,d i]:Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {M}))=C (sector i) := by
  have h3M:(3:Eis)∣M:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9M
  have hlocal (q:Q) :
      ∃C:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {M}),
      ∀i,sector i=q→∃b d:Eis,a i*d-b*(c*r i)=1 ∧ (9:Eis)∣b ∧ (3:Eis)∣d-1 ∧
        (!![a i,b;c*r i,d]:Matrix (Fin 2) (Fin 2) Eis).map
          (Ideal.Quotient.mk (Ideal.span {M}))=C := by
    by_cases hq:∃j,sector j=q
    · obtain ⟨j,hj⟩:=hq
      obtain ⟨inverse,_,hcompletion⟩:=exists_primary_numerator_completion M c (a j) hc h9M
        (haPrimary j) (hcop j).of_mul_right_left
      obtain ⟨b0,d0,hdet0,_,hb0,hd0,_⟩:=hcompletion (r j) (hr j)
        (hcop j).of_mul_right_right (hrPrimary j)
      refine ⟨(!![a j,b0;c*r j,d0]:Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {M})),?_⟩
      intro i hi
      have hs:sector i=sector j:=hi.trans hj.symm
      obtain ⟨b,d,hdet,_,hb,hd,hmat⟩:=exists_fixed_matrix_completion_controlled
        9 3 M c (a j) (r j) b0 d0 0 1 hc h9M h3M hdet0 (by simpa using hb0) hd0
        (a i) (r i) (ha i j hs) (hrr i j hs) (hr i) (hcop i).of_mul_right_right
      exact ⟨b,d,hdet,by simpa using hb,hd,hmat⟩
    · refine ⟨0,?_⟩
      intro i hi
      exact False.elim (hq ⟨i,hi⟩)
  choose C hC using hlocal
  have hi (i:ι):=hC (sector i) i rfl
  choose b d hdet hb hd hmat using hi
  exact ⟨b,d,C,hdet,hb,hd,hmat⟩

theorem exists_primary_denominator_sector_completions {ι Q:Type*}
    (M c:Eis) (h9M:(9:Eis)∣M) (hcPrimary:lambda^2∣c-1)
    (sector:ι→Q) (a r:ι→Eis) (hrPrimary:∀i,lambda^2∣r i-1)
    (hcop:∀i,IsCoprime (a i) (c*r i)) (hr:∀i,IsCoprime (r i) (M*c))
    (ha:∀i j,sector i=sector j→M*c∣a i-a j)
    (hrr:∀i j,sector i=sector j→M∣r i-r j) :
    ∃(b d:ι→Eis) (C:Q→Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {M})),
      (∀i,a i*d i-b i*(c*r i)=1) ∧ (∀i,(3:Eis)∣b i+1) ∧ (∀i,(9:Eis)∣d i) ∧
      ∀i,(!![a i,b i;c*r i,d i]:Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {M}))=C (sector i) := by
  have hc:c≠0:=primary_ne_zero c hcPrimary
  have h3M:(3:Eis)∣M:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9M
  have hlocal (q:Q) :
      ∃C:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {M}),
      ∀i,sector i=q→∃b d:Eis,a i*d-b*(c*r i)=1 ∧ (3:Eis)∣b+1 ∧ (9:Eis)∣d ∧
        (!![a i,b;c*r i,d]:Matrix (Fin 2) (Fin 2) Eis).map
          (Ideal.Quotient.mk (Ideal.span {M}))=C := by
    by_cases hq:∃j,sector j=q
    · obtain ⟨j,hj⟩:=hq
      obtain ⟨inverse,_,_,hcompletion⟩:=exists_primary_denominator_completion M c (a j)
        h9M hcPrimary (hcop j).of_mul_right_left
      obtain ⟨b0,d0,hdet0,_,hd0,_,_,hb0,_⟩:=hcompletion (r j) (hr j)
        (hcop j).of_mul_right_right (hrPrimary j)
      refine ⟨(!![a j,b0;c*r j,d0]:Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {M})),?_⟩
      intro i hi
      have hs:sector i=sector j:=hi.trans hj.symm
      obtain ⟨b,d,hdet,_,hb,hd,hmat⟩:=exists_fixed_matrix_completion_controlled
        3 9 M c (a j) (r j) b0 d0 (-1) 0 hc h3M h9M hdet0
        (by simpa using hb0) (by simpa using hd0)
        (a i) (r i) (ha i j hs) (hrr i j hs) (hr i) (hcop i).of_mul_right_right
      exact ⟨b,d,hdet,by simpa using hb,by simpa using hd,hmat⟩
    · refine ⟨0,?_⟩
      intro i hi
      exact False.elim (hq ⟨i,hi⟩)
  choose C hC using hlocal
  have hi (i:ι):=hC (sector i) i rfl
  choose b d hdet hb hd hmat using hi
  exact ⟨b,d,C,hdet,hb,hd,hmat⟩

end ShortDraftCRT

namespace CubicEisenstein
open scoped Classical BigOperators ContDiff MatrixGroups

open CompletedGauss CompletedDyadic

theorem sum_smoothedKernel_common_cusp {ι:Type*} [Fintype ι]
    (d:ι→SourceCuspDatum) (w:ι→ℂ) (j:Fin 3) (Q:ℝ)
    (hj:∀i,(d i).index=j) (hQ:∀i,(d i).heightScale=Q)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑i,w i*(d i).smoothedKernel W X)=fixedRadialCoefficientScalar*
      ∑'p:ThetaFullIndex,
        ((fixedConjugateCuspArray j p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
          sourceFrequencyAngle (thetaFullFrequency p))/
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        CubicReflectionKernel.paperKernel (Vstar W)
          (X*sourceCuspRadialLength (thetaFullFrequency p)/(27*(sourceCuspScale j)^2*Q^2))*
        (∑i,w i*((d i).multiplier*(Q:ℂ))*
          ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
            ((d i).dualPoint/(sourceCuspScale j:ℂ)))) := by
  let F:ι→ThetaFullIndex→ℂ:=fun i p=>w i*
    ((d i).multiplier*((d i).heightScale:ℂ)*(sourceCuspScale (d i).index:ℂ)^2)*
    (sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p)*
      CubicReflectionKernel.paperKernel (Vstar W)
        (X*sourceCuspRadialLength (thetaFullFrequency p)/
          (27*(sourceCuspScale (d i).index)^2*(d i).heightScale^2)))
  have hs (i:ι):Summable (F i):=by
    exact ((d i).smoothedKernel_full_index_norm_summable W a b ha hsupp hW X hX).of_norm.mul_left _
  have he (i:ι):w i*(d i).smoothedKernel W X=∑'p,F i p := by
    rw [(d i).smoothedKernel_full_index]
    simp only [F,tsum_mul_left]
    ring
  simp_rw [he]
  rw [←Summable.tsum_finsetSum (fun i _=>hs i),←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hn:=(d i).smoothedFullCoefficient_normalization p
  dsimp only [F]
  calc
    _=w i*(((d i).multiplier*((d i).heightScale:ℂ)*(sourceCuspScale (d i).index:ℂ)^2)*
      sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p))*
      CubicReflectionKernel.paperKernel (Vstar W)
        (X*sourceCuspRadialLength (thetaFullFrequency p)/
          (27*(sourceCuspScale (d i).index)^2*(d i).heightScale^2)):=by ring
    _=_:=by rw [hn,hj i,hQ i]; ring

end CubicEisenstein

open scoped Classical BigOperators

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def coprimalityMask (m:Eis) : Eis→*ℂ where
  toFun n:=if IsCoprime m n then 1 else 0
  map_one' := by simp only [isCoprime_one_right,ite_true]
  map_mul' x y := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hx:IsCoprime m x <;> by_cases hy:IsCoprime m y <;> simp [hx,hy]

lemma coprimalityMask_norm (m n:Eis) : ‖coprimalityMask m n‖≤1 := by
  change ‖if IsCoprime m n then (1:ℂ) else 0‖≤1
  split_ifs <;> norm_num

lemma isCoprime_congr_mod (m x y:Eis) (hxy:m∣x-y) : IsCoprime m x↔IsCoprime m y := by
  obtain ⟨z,hz⟩:=hxy
  constructor
  · rintro ⟨r,s,hrs⟩
    refine ⟨r+s*z,s,?_⟩
    linear_combination hrs-s*hz
  · rintro ⟨r,s,hrs⟩
    refine ⟨r-s*z,s,?_⟩
    linear_combination hrs+s*hz

lemma coprimalityMask_periodic (m:Eis) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {m}) (coprimalityMask m) := by
  intro x y hxy
  change (if IsCoprime m x then (1:ℂ) else 0)=(if IsCoprime m y then 1 else 0)
  rw [isCoprime_congr_mod m x y (Ideal.mem_span_singleton.mp hxy)]

lemma idealRowHom_prime_sixth_mask (m:Eis) (P:Ideal Eis) [P.IsMaximal] (hg:lambda∉P) :
    idealRowHom (m^6) P=if IsCoprime P (Ideal.span {m}) then 1 else 0 := by
  rw [idealRowHom_prime _ P hg]
  have hm:=canonicalSextic_sixth_power_mask P hg m
  rw [hm]
  rw [SixthPowerAverage.prime_coprime_span_iff]
  by_cases hm:m∈P <;> simp [hm]

theorem idealRowHom_sixth_mask (m:Eis) (I:Ideal Eis) (hI:Supported I) :
    idealRowHom (m^6) I=if IsCoprime I (Ideal.span {m}) then 1 else 0 := by
  have hprod (s:Multiset (Ideal Eis))
      (hs:∀P∈s,P.IsMaximal ∧ lambda∉P) :
      idealRowHom (m^6) s.prod=if IsCoprime s.prod (Ideal.span {m}) then 1 else 0 := by
    induction s using Multiset.induction_on with
    | empty =>
      change idealRowHom (m^6) 1=if IsCoprime (1:Ideal Eis) (Ideal.span {m}) then 1 else 0
      simp only [map_one,isCoprime_one_left,ite_true]
    | @cons P s ih =>
      have hp:=hs P (Multiset.mem_cons_self _ _)
      let:P.IsMaximal:=hp.1
      have ht:∀R∈s,R.IsMaximal ∧ lambda∉R:=fun R hR=>hs R (Multiset.mem_cons_of_mem hR)
      rw [Multiset.prod_cons,map_mul,idealRowHom_prime_sixth_mask m P hp.2,ih ht,
        IsCoprime.mul_left_iff]
      by_cases hP:IsCoprime P (Ideal.span {m}) <;>
        by_cases hS:IsCoprime s.prod (Ideal.span {m}) <;> simp [hP,hS]
  have h:=hprod (normalizedFactors I) (fun P hP=>
    ⟨(supported_factors_good I hI P hP).1,(supported_factors_good I hI P hP).2.1⟩)
  rwa [Ideal.prod_normalizedFactors_eq_self hI.1] at h

lemma idealRowHom_sixth_eq_mask (m n:Eis) (hn:Supported (Ideal.span {n})) :
    idealRowHom (m^6) (Ideal.span {n})=coprimalityMask m n := by
  rw [idealRowHom_sixth_mask m _ hn,Ideal.isCoprime_span_singleton_iff]
  change (if IsCoprime n m then (1:ℂ) else 0)=(if IsCoprime m n then 1 else 0)
  rw [isCoprime_comm]

lemma rowTwist_extract_sixth_mask (Ψ:Eis→*ℂ) (m f z n:Eis)
    (hn:Supported (Ideal.span {n})) :
    rowTwist Ψ m f z n=Ψ n*coprimalityMask m n*
      idealRowHom (f^4*z) (Ideal.span {n}) := by
  change Ψ n*idealRowHom (m^6*f^4*z) (Ideal.span {n})=_
  rw [show m^6*f^4*z=m^6*(f^4*z) by ring,idealRowHom_argument_mul,
    idealRowHom_sixth_eq_mask m n hn]
  ring

end CanonicalRowCompletion

open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp

section
open ActualEisensteinCubic CubicKubota CubicEisenstein ConcreteTraceCRT CubicJacobiGlobal
open CompletedGauss CanonicalRowCompletion
local notation "Eis" => ActualEisensteinCubic.O

theorem embedded_symbol_product {ι : Type*} [Fintype ι]
    (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i}) (a : Eis) :
    eisEmbedding (symbol a (∏i,p i))=
      ∏i,(actualSextic (Ideal.span {p i}) (hg i) (Ideal.Quotient.mk _ a))^2 := by
  change eisEmbedding (idealSymbol (Ideal.span {∏i,p i}) a)=_
  rw [←idealRowHom_square,idealRowHom_product p hg Finset.univ a]
  simp only [ActualEisensteinCubic.finiteSquarefreeRow,actualSextic,Finset.prod_pow]

theorem conjugate_symbol_product {ι : Type*} [Fintype ι]
    (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i}) (a : Eis) :
    star (eisEmbedding (symbol a (∏i,p i)))=
      ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        (Ideal.Quotient.mk _ a) := by
  rw [embedded_symbol_product p hg a,star_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [star_pow,MulChar.star_apply',MulChar.pow_apply' _ (by decide : (2:ℕ)≠0)]

theorem conjugate_symbol_product_frequency {ι : Type*} [Fintype ι]
    (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i}) (a : Eis)
    (σ : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i : Eis⧸Ideal.span {p i})*h i) :
    star (eisEmbedding (symbol a (∏i,p i)))=
      ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        ((σ i : Eis⧸Ideal.span {p i})*h i) := by
  rw [conjugate_symbol_product p hg a]
  simp only [ha]

end

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

lemma A4_field_inverse {F : Type*} [Field F] (a d B : F) (σ ε : Fˣ) (h x : F)
    (had : a*d=1) (ha : a=(σ:F)*h) (hε : B*(σ:F)*(ε:F)=-1) :
    h≠0 ∧ -d*B⁻¹*x=((ε:F)*x)*h⁻¹ := by
  have hh : h≠0 := by
    intro hz
    rw [ha,hz,mul_zero,zero_mul] at had
    exact zero_ne_one had
  have hB : B≠0 := by
    intro hz
    rw [hz,zero_mul,zero_mul] at hε
    exact neg_ne_zero.mpr (one_ne_zero : (1:F)≠0) hε.symm
  have hd : d=((σ:F)*h)⁻¹ := eq_inv_of_mul_eq_one_right (ha ▸ had)
  have he : (ε:F)=-(B*(σ:F))⁻¹ := by
    have heq : (B*(σ:F))*(-(ε:F))=1 := by linear_combination -hε
    exact neg_eq_iff_eq_neg.mp (eq_inv_of_mul_eq_one_right heq)
  refine ⟨hh,?_⟩
  rw [hd,he]
  field_simp

noncomputable local instance A4quotientField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance A4quotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

lemma A4_active_local {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (a b c0 d : Eis) (hdet : a*d-b*(c0*∏i,p i)=1)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i:Eis⧸Ideal.span {p i})*h i)
    (hε : ∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1)
    (x : Eis) (i : ι) :
    h i≠0 ∧
      -(Ideal.Quotient.mk (Ideal.span {p i}) d)*
        (Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i))⁻¹*
        Ideal.Quotient.mk (Ideal.span {p i}) x =
      ((ε i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk (Ideal.span {p i}) x)*(h i)⁻¹ := by
  have hz : Ideal.Quotient.mk (Ideal.span {p i}) (∏k,p k)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr
      (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))
  have had : Ideal.Quotient.mk (Ideal.span {p i}) a*
      Ideal.Quotient.mk (Ideal.span {p i}) d=1 := by
    have he := congrArg (Ideal.Quotient.mk (Ideal.span {p i})) hdet
    simpa only [map_sub,map_mul,map_one,hz,mul_zero,sub_zero] using he
  exact A4_field_inverse _ _ _ (σ i) (ε i) (h i) _ had (ha i) (hε i)

lemma A4_complement_inverse {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (c0 U w : Eis) (hbez : U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (i : ι) (v t : Eis) (hlocal : t*p i+v*cofactor p i=1) :
    (Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i))⁻¹=
      Ideal.Quotient.mk (Ideal.span {p i}) (w*v) := by
  have hz : Ideal.Quotient.mk (Ideal.span {p i}) (∏k,p k)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr
      (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))
  have hp0 : Ideal.Quotient.mk (Ideal.span {p i}) (p i)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hw := congrArg (Ideal.Quotient.mk (Ideal.span {p i})) hbez
  have hv := congrArg (Ideal.Quotient.mk (Ideal.span {p i})) hlocal
  simp only [map_add,map_mul,map_pow,map_one,hz,mul_zero,zero_add] at hw
  simp only [map_add,map_mul,map_one,hp0,mul_zero,zero_add] at hv
  symm
  apply eq_inv_of_mul_eq_one_right
  simp only [map_mul,map_pow]
  calc
    _ = ((Ideal.Quotient.mk _ ramifiedTraceLambda)^3*Ideal.Quotient.mk _ w*
        Ideal.Quotient.mk _ c0)*(Ideal.Quotient.mk _ v*Ideal.Quotient.mk _ (cofactor p i)) := by ring
    _ = 1 := by rw [hw,hv,mul_one]

end ShortDraftCusp

end

end OAI
