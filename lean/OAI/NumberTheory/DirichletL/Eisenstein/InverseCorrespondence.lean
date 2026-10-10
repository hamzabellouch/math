import OAI.NumberTheory.DirichletL.Eisenstein.CubeCuspAverage

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma integralCoverFiber_memLp {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hf : MemLp f 2 (integralQuotientVolume H)) (q : IntegralCoverCosets H K) :
    MemLp (fun w=>f (integralCoverFiberPoint H K q w)) 2
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet K)) := by
  have hD := hf.comp_measurePreserving (integralCoverDomain_projection_measurePreserving hHK hK)
  have hS := MemLp.mono_measure
    (Measure.restrict_mono_set hyperbolicVolume (Set.subset_iUnion (integralCoverSheet H K) q)) hD
  have hm := integralCoverSheet_measurePreserving H K q
  have hi := memLp_map_measure_iff (p:=2)
    (hmeas.comp (integralCoverFiberPoint_measurable H K q)).aestronglyMeasurable hm.aemeasurable
  rw [hm.map_eq] at hi
  apply hi.mpr
  simpa only [Function.comp_def,integralCoverFiberPoint_rep_smul] using hS

theorem integralCoverTraceFunction_memLp {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hf : MemLp f 2 (integralQuotientVolume H)) :
    MemLp (integralCoverTraceFunction H K f) 2 (integralQuotientVolume K) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  have hm := quotient_projection_measurePreserving K
  have hi := memLp_map_measure_iff (p:=2)
    (integralCoverTraceFunction_measurable H K f hmeas).aestronglyMeasurable hm.aemeasurable
  rw [hm.map_eq] at hi
  apply hi.mpr
  change MemLp (fun w=>∑q : IntegralCoverCosets H K,f (integralCoverFiberPoint H K q w)) 2 _
  exact memLp_finsetSum Finset.univ (fun q _=>integralCoverFiber_memLp hHK hK f hmeas hf q)

lemma integralCoverMap_fiberPoint {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K)
    (q : IntegralCoverCosets H K) (w : HyperbolicSpace) :
    integralCoverMap hHK (integralCoverFiberPoint H K q w)=integralOrbitProjection K w := by
  rw [integralCoverFiberPoint_rep,integralCoverMap_projection,integralSubgroup_smul,
    integralOrbitProjection_eq]

lemma integralCoverTraceFunction_pairing {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] (F : IntegralOrbitQuotient K→ℂ)
    (f : IntegralOrbitQuotient H→ℂ) (q : IntegralOrbitQuotient K) :
    integralCoverTraceFunction H K (fun r=>inner ℂ (F (integralCoverMap hHK r)) (f r)) q=
      inner ℂ (F q) (integralCoverTraceFunction H K f q) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  induction q using Quotient.inductionOn with
  | _ w =>
    change (∑r : IntegralCoverCosets H K,inner ℂ
      (F (integralCoverMap hHK (integralCoverFiberPoint H K r w)))
      (f (integralCoverFiberPoint H K r w)))=
      inner ℂ (F (integralOrbitProjection K w)) (∑r : IntegralCoverCosets H K,f (integralCoverFiberPoint H K r w))
    simp only [integralCoverMap_fiberPoint,inner_sum]

theorem integralCoverTrace_toLp_ae {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hf : MemLp f 2 (integralQuotientVolume H)) :
    integralCoverTrace hHK hK (hf.toLp f)=ᵐ[integralQuotientVolume K]
      integralCoverTraceFunction H K f := by
  let htr := integralCoverTraceFunction_memLp hHK hK f hmeas hf
  let Tf : IntegralQuotientL2 K := htr.toLp (integralCoverTraceFunction H K f)
  have he : Tf=integralCoverTrace hHK hK (hf.toLp f) := by
    apply ext_inner_left ℂ
    intro F
    let pair : IntegralOrbitQuotient H→ℂ := fun r=>inner ℂ (F (integralCoverMap hHK r)) (f r)
    have hpm : Measurable pair := by
      have hFm : Measurable (fun r=>F (integralCoverMap hHK r)) :=
        (Lp.stronglyMeasurable F).measurable.comp (integralCoverMap_measurable hHK)
      have hstar : Measurable (fun r=>star (F (integralCoverMap hHK r))) :=
        continuous_star.measurable.comp hFm
      have hm := hmeas.mul hstar
      change Measurable (fun r=>f r*star (F (integralCoverMap hHK r))) at hm
      simpa only [pair,RCLike.inner_apply,starRingEnd_apply] using hm
    have hae : (fun r=>inner ℂ (integralCoverPullback hHK hK F r) (hf.toLp f r))
        =ᵐ[integralQuotientVolume H]pair := by
      filter_upwards [integralCoverPullback_ae hHK hK F,hf.coeFn_toLp] with r hr hfR
      dsimp [pair]
      rw [hr,hfR]
    have hpi : Integrable pair (integralQuotientVolume H) :=
      (L2.integrable_inner (integralCoverPullback hHK hK F) (hf.toLp f)).congr hae
    calc
      inner ℂ F Tf = ∫q,inner ℂ (F q) (integralCoverTraceFunction H K f q)∂integralQuotientVolume K := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [htr.coeFn_toLp] with q hq
        change inner ℂ (F q) (htr.toLp (integralCoverTraceFunction H K f) q)=_
        rw [hq]
      _ = ∫q,integralCoverTraceFunction H K pair q∂integralQuotientVolume K := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun q=>(integralCoverTraceFunction_pairing hHK F f q).symm)
      _ = ∫r,pair r∂integralQuotientVolume H :=
        integralCoverTraceFunction_integral hHK hK pair hpm hpi
      _ = inner ℂ (integralCoverPullback hHK hK F) (hf.toLp f) :=
        (integral_congr_ae hae).symm
      _ = inner ℂ F (integralCoverTrace hHK hK (hf.toLp f)) :=
        (integralCoverTrace_pairing hHK hK F (hf.toLp f)).symm
  rw [←he]
  exact htr.coeFn_toLp

theorem integralCoverTrace_representative {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (G : IntegralQuotientL2 H) (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hrep : G=ᵐ[integralQuotientVolume H]f) :
    integralCoverTrace hHK hK G=ᵐ[integralQuotientVolume K]integralCoverTraceFunction H K f := by
  have hf : MemLp f 2 (integralQuotientVolume H) := (memLp_congr_ae hrep).mp (Lp.memLp G)
  have he : G=hf.toLp f := Lp.ext (hrep.trans hf.coeFn_toLp.symm)
  rw [he]
  exact integralCoverTrace_toLp_ae hHK hK f hmeas hf

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

theorem integralCoverTrace_cusp_representative {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (G : IntegralQuotientL2 H) (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hrep : G=ᵐ[integralQuotientVolume H]f) (C : ℝ)
    (hdec : ∀M : CubicKubota.levelThree,∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection H (complexMatrix M•upperPoint z v hv))‖≤C/v^3) :
    ∃g : IntegralOrbitQuotient K→ℂ,Measurable g ∧
      integralCoverTrace hHK hK G=ᵐ[integralQuotientVolume K]g ∧
      ∀M : CubicKubota.levelThree,∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
        ‖g (integralOrbitProjection K (complexMatrix M•upperPoint z v hv))‖≤
          (H.relIndex K:ℝ)*C/v^3 := by
  refine ⟨integralCoverTraceFunction H K f,
    integralCoverTraceFunction_measurable H K f hmeas,
    integralCoverTrace_representative hHK hK G f hmeas hrep,?_⟩
  exact integralCoverTraceFunction_cusp_decay H K hK f C hdec

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def primaryDenominatorShift (a:PrimaryLower) (m:Eis) : PrimaryCoprimeDenominator a≃PrimaryCoprimeDenominator a where
  toFun d:=⟨⟨d.val.val+3*a.val*m,by
    convert dvd_add d.val.2 (show (3:Eis)∣3*a.val*m from ⟨a.val*m,by ring⟩) using 1 ;ring⟩,by
      exact (isCoprime_right_congr_of_dvd a.val (d.val.val+3*a.val*m) d.val.val ⟨3*m,by ring⟩).mpr d.2⟩
  invFun d:=⟨⟨d.val.val-3*a.val*m,by
    convert dvd_sub d.val.2 (show (3:Eis)∣3*a.val*m from ⟨a.val*m,by ring⟩) using 1 ;ring⟩,by
      exact (isCoprime_right_congr_of_dvd a.val (d.val.val-3*a.val*m) d.val.val ⟨-(3*m),by ring⟩).mpr d.2⟩
  left_inv d:=by apply Subtype.ext;apply Subtype.ext;dsimp;ring
  right_inv d:=by apply Subtype.ext;apply Subtype.ext;dsimp;ring

def unitLowerDataShift (m:Eis) : UnitLowerData≃UnitLowerData :=
  Equiv.sigmaCongrRight (fun a=>primaryDenominatorShift a m)

lemma affineCusp_term_weighted_period (h q r:Eis) (j n:ℕ) (a d:PrimaryLower) (m:Eis)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j n*q) (z:ℂ) (v:ℝ) (s:ℂ) :
    affineLowerTerm q r z v s a.val (d.val+3*a.val*(q*m))*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
      affineLowerTerm q r (z+3*eisEmbedding m) v s a.val d.val*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m)) := by
  have hd:(3:Eis)∣d.val-a.val:=by simpa only [sub_sub_sub_cancel_right] using dvd_sub d.2 a.2
  obtain ⟨x,hx⟩:=hd
  have hdx:d.val=a.val+3*x:=by linear_combination hx
  have hb:(3:Eis)∣h+ramifiedAffineParameter j n*q*a.val:=by
    convert dvd_add hbase (a.2.mul_left (ramifiedAffineParameter j n*q)) using 1 ;ring
  obtain ⟨ell,hell⟩:=hb
  have he:=affineCusp_general_weighted_translate h q r a.val ell x (q*m) j n
    (primaryLower_primary a) hq hr hell.symm z v s
  have hqm:Ideal.Quotient.mk (Ideal.span {q}) (q*m)=0:=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right q m))
  rw [hqm,AddChar.map_zero_eq_one,one_mul] at he
  have hshift:3*eisEmbedding (q*m)/eisEmbedding q=3*eisEmbedding m:=by
    rw [map_mul]
    field_simp [eisEmbedding_ne_zero hq]
  rw [hshift] at he
  rw [hdx,show a.val+3*x+3*a.val*(q*m)=a.val+3*(x+a.val*(q*m)) by ring]
  exact he

def affineCuspBlock (q r:Eis) (z:ℂ) (v:ℝ) (s:ℂ) : ℂ :=
  ∑'p:UnitLowerData,affineLowerTerm q r z v s p.1.val p.2.val.val

lemma affineCuspBlock_weighted_periodic (h q r:Eis) (j n:ℕ)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j n*q) (v:ℝ) (s:ℂ) (m:Eis) (z:ℂ) :
    affineCuspBlock q r (z+3*eisEmbedding m) v s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m))=
      affineCuspBlock q r z v s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  rw [affineCuspBlock,affineCuspBlock,←tsum_mul_right,←tsum_mul_right]
  calc
    _ = ∑'p:UnitLowerData,affineLowerTerm q r z v s
      ((unitLowerDataShift (q*m) p).1.val) ((unitLowerDataShift (q*m) p).2.val.val)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
      apply tsum_congr
      intro p
      exact (affineCusp_term_weighted_period h q r j n p.1 p.2.val m hq hr hbase z v s).symm
    _ = _ := (unitLowerDataShift (q*m)).tsum_eq
      (fun p:UnitLowerData=>affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))

lemma period_integral_twisted_translation (f:ℂ→ℂ) (freq:ℂ)
    (hp:∀(n:Eis)(z:ℂ),f (z+3*eisEmbedding n)*ShortDraftTrace.breveE (-freq*(z+3*eisEmbedding n))=
      f z*ShortDraftTrace.breveE (-freq*z)) (b:ℂ) :
    (∫z in periodDomain,f (z+b)*ShortDraftTrace.breveE (-freq*z))=
      ShortDraftTrace.breveE (freq*b)*∫z in periodDomain,f z*ShortDraftTrace.breveE (-freq*z) := by
  let g:ℂ→ℂ:=fun z=>f z*ShortDraftTrace.breveE (-freq*z)
  have he (z:ℂ):f (z+b)*ShortDraftTrace.breveE (-freq*z)=ShortDraftTrace.breveE (freq*b)*g (b+z):=by
    dsimp only [g]
    rw [mul_left_comm,←AddChar.map_add_eq_mul]
    congr 1
    · rw [add_comm]
    · congr 1;ring
  simp_rw [he]
  rw [integral_const_mul,period_integral_translation g hp b]

lemma affineCuspBlock_integral_translation (h q r:Eis) (j n:ℕ)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j n*q) (v:ℝ) (s b:ℂ) :
    (∫z in periodDomain,affineCuspBlock q r (z+b) v s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ShortDraftTrace.breveE (ninthCuspFrequency h*b)*
        ∫z in periodDomain,affineCuspBlock q r z v s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) :=
  period_integral_twisted_translation (fun z=>affineCuspBlock q r z v s) (ninthCuspFrequency h)
    (affineCuspBlock_weighted_periodic h q r j n hq hr hbase v s) b

end
section

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma diagonal_unit_weighted_periodic (u t:Eisˣ) (j:ℕ) (h:Eis)
    (hr:(↑u⁻¹:Eis)^2*(t:Eis)=omega^j ∨ (↑u⁻¹:Eis)^2*(t:Eis)=-(omega^j))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j 0*(t:Eis))
    (v:ℝ) (hv:0<v) (s:ℂ) (m:Eis) (z:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis))*
      upperSection (z+3*eisEmbedding m) v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m))=
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis))*
      upperSection z v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  simpa only [diagonal_unit_eisenstein_rows,affineCuspBlock] using
    affineCuspBlock_weighted_periodic h (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis)) j 0 t.ne_zero
      (by simpa using hr) hbase v s m z

lemma diagonal_once_block_expansion (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
      upperSection z v hv) s=
    ∑l:Fin 3,affineCuspBlock (onceCuspScale t*omega^l.val)
      ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) z v s := by
  have hsum:=(diagonalOnceCuspIndex u t).summable_iff.mpr
    (summable_summand (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv)) s hs)
  have ht:Summable (fun p:OnceRamifiedData=>affineLowerTerm (onceCuspScale t*omega^p.1.val)
      ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val):=
    hsum.congr (fun p=>diagonal_once_summand u t z v hv s p)
  rw [mul_assoc,diagonal_once_eisenstein_rows,ht.tsum_prod,tsum_fintype]
  rfl

lemma diagonal_once_weighted_periodic (u t:Eisˣ) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (m:Eis) (z:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
      upperSection (z+3*eisEmbedding m) v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m))=
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
      upperSection z v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  rw [diagonal_once_block_expansion u t _ v hv s hs,diagonal_once_block_expansion u t _ v hv s hs,
    Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  exact affineCuspBlock_weighted_periodic h (onceCuspScale t*omega^l.val)
    ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) (onceCuspRayIndex u t l).val 1
      (mul_ne_zero (onceCusp_scale_ne_zero t) (pow_ne_zero _ (omega_primitive.isUnit (by decide)).ne_zero))
      (by simpa only [pow_one] using onceCuspRayIndex_spec u t l)
      (onceCusp_period_congruence t l h _ hfreq) v s m z

lemma diagonal_unit_fourier_shift (u t:Eisˣ) (j:ℕ) (h:Eis)
    (hr:(↑u⁻¹:Eis)^2*(t:Eis)=omega^j ∨ (↑u⁻¹:Eis)^2*(t:Eis)=-(omega^j))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j 0*(t:Eis))
    (v:ℝ) (hv:0<v) (s b:ℂ) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection (z+b) v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ShortDraftTrace.breveE (ninthCuspFrequency h*b)*
        ∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
          integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
            ShortDraftTrace.breveE (-ninthCuspFrequency h*z) :=
  period_integral_twisted_translation
    (fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s)
    (ninthCuspFrequency h) (diagonal_unit_weighted_periodic u t j h hr hbase v hv s) b

lemma diagonal_once_fourier_shift (u t:Eisˣ) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) (v:ℝ) (hv:0<v) (s b:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection (z+b) v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ShortDraftTrace.breveE (ninthCuspFrequency h*b)*
        ∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
          integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv) s*
            ShortDraftTrace.breveE (-ninthCuspFrequency h*z) :=
  period_integral_twisted_translation
    (fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv) s)
    (ninthCuspFrequency h) (diagonal_once_weighted_periodic u t h hfreq v hv s hs) b

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedCuspRoot (b:Bool) : Eisˣ := if b then ramifiedOmegaUnit^2 else ramifiedOmegaUnit

def ramifiedCuspScaleUnit (b:Bool) : Eisˣ := if b then ramifiedOmegaUnit^2 else -ramifiedOmegaUnit

def ramifiedCuspDirectIndex (b:Bool) : ℕ := if b then 2 else 1

def ramifiedCuspOppositeIndex (b:Bool) : ℕ := if b then 1 else 2

lemma ramified_omega_four : omega^4=omega := by
  rw [show (4:ℕ)=3+1 from rfl,pow_add,omega_primitive.pow_eq_one,pow_one,one_mul]

lemma ramifiedCuspRoot_val (b:Bool) : (ramifiedCuspRoot b:Eis)=omega^(ramifiedCuspDirectIndex b) := by
  cases b <;>simp [ramifiedCuspRoot,ramifiedCuspDirectIndex,ramifiedOmegaUnit_val]

lemma ramifiedCuspRoot_cube (b:Bool) : (ramifiedCuspRoot b:Eis)^3=1 := by
  rw [ramifiedCuspRoot_val,←pow_mul,Nat.mul_comm,pow_mul,omega_primitive.pow_eq_one,one_pow]

lemma ramifiedCuspRoot_primitive (b:Bool) :
    (ramifiedCuspRoot b:Eis)^2+(ramifiedCuspRoot b:Eis)+1=0 := by
  cases b
  · simpa [ramifiedCuspRoot,ramifiedOmegaUnit_val] using ramified_omega_relation
  · simp only [ramifiedCuspRoot,ite_true,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,←pow_mul]
    rw [show 2*2=4 from rfl,ramified_omega_four]
    linear_combination ramified_omega_relation

lemma ramifiedCuspScaleUnit_spec (b:Bool) :
    -(ramifiedCuspRoot b:Eis)*(1+2*(ramifiedCuspRoot b:Eis))=onceCuspScale (ramifiedCuspScaleUnit b) := by
  cases b
  · simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedTraceLambda,ramifiedOmegaUnit_val]
  · simp only [ramifiedCuspRoot,ramifiedCuspScaleUnit,ite_true,onceCuspScale,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,
      ramifiedTraceLambda]
    linear_combination -(2*omega^2)*ramified_omega_relation

lemma ramifiedCusp_neg_inv_square (b:Bool) :
    (↑(-(ramifiedCuspRoot b))⁻¹:Eis)^2=(ramifiedCuspRoot b:Eis) := by
  have hi:(↑(-(ramifiedCuspRoot b))⁻¹:Eis)=-(ramifiedCuspRoot b:Eis)^2:=by
    apply (-(ramifiedCuspRoot b)).inv_eq_of_mul_eq_one_right
    change -(ramifiedCuspRoot b:Eis)*(-(ramifiedCuspRoot b:Eis)^2)=1
    convert ramifiedCuspRoot_cube b using 1 ;ring
  rw [hi]
  linear_combination (ramifiedCuspRoot b:Eis)*ramifiedCuspRoot_cube b

lemma ramifiedCusp_opposite_character (b:Bool) :
    (↑(-(ramifiedCuspRoot b))⁻¹:Eis)^2*(-(ramifiedCuspRoot b:Eis))=
      -(omega^(ramifiedCuspOppositeIndex b)) := by
  rw [ramifiedCusp_neg_inv_square,ramifiedCuspRoot_val]
  cases b
  · simp [ramifiedCuspDirectIndex,ramifiedCuspOppositeIndex,pow_two]
  · simp only [ramifiedCuspDirectIndex,ramifiedCuspOppositeIndex,ite_true,pow_one]
    rw [mul_neg,←pow_add,show 2+2=4 from rfl,ramified_omega_four]

lemma ramifiedCusp_direct_period_constant (b:Bool) :
    (3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit b)+
      ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0*(ramifiedCuspRoot b:Eis) := by
  cases b
  · refine ⟨0,?_⟩
    simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedCuspDirectIndex,
      ramifiedAffineParameter,ramifiedOmegaUnit_val]
    ring
  · refine ⟨ramifiedTraceLambda*omega^2,?_⟩
    simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedCuspDirectIndex,
      ramifiedAffineParameter,ramifiedOmegaUnit_val]
    ring

lemma ramifiedCusp_opposite_period_constant (b:Bool) :
    (3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit b)+
      ramifiedAffineParameter (ramifiedCuspOppositeIndex b) 0*(-(ramifiedCuspRoot b:Eis)) := by
  cases b
  · refine ⟨-(omega*ramifiedTraceLambda),?_⟩
    simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedCuspOppositeIndex,
      ramifiedAffineParameter,ramifiedOmegaUnit_val]
    ring
  · refine ⟨0,?_⟩
    simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedCuspOppositeIndex,
      ramifiedAffineParameter,ramifiedOmegaUnit_val]
    ring

lemma ramifiedCusp_unit_period_constant (b:Bool) :
    (3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit b)+
      ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0 := by
  cases b
  · refine ⟨-omega^2,?_⟩
    simp [ramifiedCuspScaleUnit,ramifiedCuspDirectIndex,onceCuspScale,Units.val_neg,
      ramifiedOmegaUnit_val,ramifiedAffineParameter,Nat.cast_one,one_mul,sub_zero,
      ramifiedTraceLambda]
    linear_combination ramified_omega_relation
  · refine ⟨-omega^2,?_⟩
    simp only [ramifiedCuspScaleUnit,ramifiedCuspDirectIndex,ite_true,onceCuspScale,Units.val_pow_eq_pow_val,
      ramifiedOmegaUnit_val,ramifiedAffineParameter,Nat.cast_ofNat,Nat.cast_zero,sub_zero,
      ramifiedTraceLambda]
    linear_combination (2*omega+2)*ramified_omega_relation

lemma ramifiedCusp_support_standard (b:Bool) (h:Eis) :
    (3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b) ↔
      (3:Eis)∣h-(if b then -(omega-1) else omega-1) := by
  have hc:(3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit b)-(if b then -(omega-1) else omega-1):=by
    cases b
    · refine ⟨1,?_⟩
      simp [ramifiedCuspScaleUnit,onceCuspScale,Units.val_neg,ramifiedOmegaUnit_val,
        ramifiedTraceLambda]
      linear_combination -2*ramified_omega_relation
    · refine ⟨0,?_⟩
      simp only [ramifiedCuspScaleUnit,ite_true,onceCuspScale,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,
        ramifiedTraceLambda]
      linear_combination (2*omega-1)*ramified_omega_relation
  constructor
  · intro hh
    convert dvd_add hh hc using 1 ;ring
  · intro hh
    convert dvd_sub hh hc using 1 ;ring

end

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def unitCuspGaussSeries (u t:Eisˣ) (h:Eis) (s:ℂ) : ℂ :=
  ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (t:Eis))*
    unramifiedCubicGaussSeries s (3*((↑u⁻¹:Eis)^2*(t:Eis))^2*((↑t⁻¹:Eis)*h))

lemma unitCusp_eisenstein_fourier_base (u t:Eisˣ) (j:ℕ) (h:Eis)
    (hr:(↑u⁻¹:Eis)^2*(t:Eis)=omega^j ∨ (↑u⁻¹:Eis)^2*(t:Eis)=-(omega^j))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j 0*(t:Eis))
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*unitCuspGaussSeries u t h s := by
  have hh:h=(t:Eis)*((↑t⁻¹:Eis)*h):=by simp [←mul_assoc]
  have hf:(3:Eis)∣(↑t⁻¹:Eis)*h+ramifiedAffineParameter j 0:=by
    have he:(↑t⁻¹:Eis)*(h+ramifiedAffineParameter j 0*(t:Eis))=
        (↑t⁻¹:Eis)*h+ramifiedAffineParameter j 0:=by
      rw [mul_add]
      congr 1
      calc
        _ = ((↑t⁻¹:Eis)*(t:Eis))*ramifiedAffineParameter j 0 := by ring
        _ = _ := by simp
    rw [←he]
    exact hbase.mul_left _
  rw [diagonal_unit_eisenstein_fourier u t j h ((↑t⁻¹:Eis)*h) hr hh hf v hv s hs,
    unitCuspGaussSeries]
  ring

lemma unitCuspDiagonal_one : unitCuspDiagonal (1:Eisˣ)=1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;>fin_cases j <;>simp [unitCuspDiagonal]

lemma ramifiedCusp_direct_base (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) :
    (3:Eis)∣h+ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0*(ramifiedCuspRoot b:Eis) := by
  convert dvd_add hf (ramifiedCusp_direct_period_constant b) using 1 ;ring

lemma ramifiedCusp_opposite_base (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) :
    (3:Eis)∣h+ramifiedAffineParameter (ramifiedCuspOppositeIndex b) 0*(-(ramifiedCuspRoot b:Eis)) := by
  convert dvd_add hf (ramifiedCusp_opposite_period_constant b) using 1 ;ring

lemma ramifiedCusp_unit_base (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) :
    (3:Eis)∣h+ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0 := by
  convert dvd_add hf (ramifiedCusp_unit_period_constant b) using 1 ;ring

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicKubota
open CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma cubeKernelLeftGlobal_injective (p : ActualEisensteinCubic.O) (hp : p≠0) :
    Function.Injective (cubeKernelLeftGlobal p) := by
  intro x y hxy
  apply (cubeKernel_finite_covers p hp).1
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

lemma cubeKernelRightGlobal_injective (p : ActualEisensteinCubic.O) (hp : p≠0) :
    Function.Injective (cubeKernelRightGlobal p hp) := by
  intro x y hxy
  apply (cubeKernel_finite_covers p hp).2.1
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

def cubeKernelRangeEquiv (p : ActualEisensteinCubic.O) (hp : p≠0) :
    (cubeKernelLeftGlobal p).range≃*(cubeKernelRightGlobal p hp).range :=
  (MonoidHom.ofInjective (cubeKernelLeftGlobal_injective p hp)).symm.trans
    (MonoidHom.ofInjective (cubeKernelRightGlobal_injective p hp))

def cubeCoverMatrix (p : ActualEisensteinCubic.O) (hp : p≠0) : SL(2,ℂ) :=
  (cubeArchimedean_correspondence p hp).choose

lemma cubeCoverMatrix_spec (p : ActualEisensteinCubic.O) (hp : p≠0) :
    cubeCoverMatrix p hp 0 1=0 ∧ cubeCoverMatrix p hp 1 0=0 ∧
    cubeCoverMatrix p hp 0 0/cubeCoverMatrix p hp 1 1=ConcreteTraceCRT.eisEmbedding p^3 ∧
    ∀x : cubeKernelCorrespondence p,
      cubeCoverMatrix p hp*integralComplexMatrix (cubeKernelLeftGlobal p x)=
        integralComplexMatrix (cubeKernelRightGlobal p hp x)*cubeCoverMatrix p hp :=
  (cubeArchimedean_correspondence p hp).choose_spec

lemma cubeCoverMatrix_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) :
    IntegralCoverIntertwines (cubeKernelRangeEquiv p hp) (cubeCoverMatrix p hp) := by
  intro h
  let x := (MonoidHom.ofInjective (cubeKernelLeftGlobal_injective p hp)).symm h
  have hl : cubeKernelLeftGlobal p x=(h : SL(2,ActualEisensteinCubic.O)) :=
    MonoidHom.apply_ofInjective_symm (cubeKernelLeftGlobal_injective p hp) h
  change cubeCoverMatrix p hp*integralComplexMatrix (h : SL(2,ActualEisensteinCubic.O))=
    integralComplexMatrix (cubeKernelRightGlobal p hp x)*cubeCoverMatrix p hp
  rw [←hl]
  exact (cubeCoverMatrix_spec p hp).2.2.2 x

lemma cubeLeft_le_levelThree (p : ActualEisensteinCubic.O) :
    (cubeKernelLeftGlobal p).range≤levelThree :=
  (cubeKernelLeftGlobal_le p).trans globalKubotaKernel_le_levelThree

lemma cubeRight_le_levelThree (p : ActualEisensteinCubic.O) (hp : p≠0) :
    (cubeKernelRightGlobal p hp).range≤levelThree :=
  (cubeKernelRightGlobal_le p hp).trans globalKubotaKernel_le_levelThree

def cubeForwardL2Pullback (p : ActualEisensteinCubic.O) (hp : p≠0) :
    IntegralQuotientL2 (cubeKernelRightGlobal p hp).range→ₗᵢ[ℂ]
      IntegralQuotientL2 (cubeKernelLeftGlobal p).range :=
  integralConjugatePullback (cubeKernelRangeEquiv p hp) (cubeCoverMatrix p hp)
    (cubeCoverMatrix_intertwines p hp) (cubeLeft_le_levelThree p) (cubeRight_le_levelThree p hp)

def cubeInverseL2Pullback (p : ActualEisensteinCubic.O) (hp : p≠0) :
    IntegralQuotientL2 (cubeKernelLeftGlobal p).range→ₗᵢ[ℂ]
      IntegralQuotientL2 (cubeKernelRightGlobal p hp).range :=
  integralConjugatePullback (cubeKernelRangeEquiv p hp).symm (cubeCoverMatrix p hp)⁻¹
    (integralCoverIntertwines_inverse _ _ (cubeCoverMatrix_intertwines p hp))
    (cubeRight_le_levelThree p hp) (cubeLeft_le_levelThree p)

theorem cubeInverseL2Pullback_ae (p : ActualEisensteinCubic.O) (hp : p≠0)
    (F : IntegralQuotientL2 (cubeKernelLeftGlobal p).range) :
    cubeInverseL2Pullback p hp F=ᵐ[integralQuotientVolume (cubeKernelRightGlobal p hp).range]
      fun q=>F (integralConjugateMap (cubeKernelRangeEquiv p hp).symm (cubeCoverMatrix p hp)⁻¹
        (integralCoverIntertwines_inverse _ _ (cubeCoverMatrix_intertwines p hp)) q) :=
  integralConjugatePullback_ae _ _ _ _ _ F

def cubeInverseL2Correspondence (p : ActualEisensteinCubic.O) (hp : p≠0) : KernelQuotientL2→L[ℂ]KernelQuotientL2 := by
  letI := (cubeKernelGlobal_finite_covers p hp).1
  letI := (cubeKernelGlobal_finite_covers p hp).2
  letI : (cubeKernelLeftGlobal p).range.IsFiniteRelIndex globalKubotaKernel :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  letI : (cubeKernelRightGlobal p hp).range.IsFiniteRelIndex globalKubotaKernel :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  exact (integralCoverTrace (cubeKernelRightGlobal_le p hp) globalKubotaKernel_le_levelThree).comp
    ((cubeInverseL2Pullback p hp).toContinuousLinearMap.comp
      (integralCoverPullback (cubeKernelLeftGlobal_le p) globalKubotaKernel_le_levelThree))

end CubicKubota

end

end OAI
