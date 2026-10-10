import OAI.NumberTheory.DirichletL.Eisenstein.CubeResidueStrata

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

namespace CubicKubota

open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def actualCubeCuspPhaseSum (A:levelTwo) (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (w:Fin 4→ℂ) : ℂ :=
  ∑' r:Eis⧸Ideal.span {p^3},
    let d:=actualCubeCuspData (A:SL(2,Eis)) p (GaussianShiftedPartition.representative (p^3) r) hp hprimary
    w d.exponent * complexCharacter ⟨d.matrix*(A:SL(2,Eis))⁻¹,d.congruent⟩

theorem actualCubeCuspPhaseSum_coprime (A:levelTwo) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hC:IsCoprime ((A:SL(2,Eis)) 1 0) p) (w:Fin 4→ℂ) :
    actualCubeCuspPhaseSum A p hp hprimary w =
      w 0*(Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)+w 3 := by
  let e:=cubeResidueStrataEquiv p hp hprimary
  let a:=cubeCuspAffineEquiv p ((A:SL(2,Eis)) 0 0) ((A:SL(2,Eis)) 1 0) hprimary hC
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData (A:SL(2,Eis)) p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  let phi (s:CubeResidueStrata p):=w s.1*cubeStratumSymbol p ((A:SL(2,Eis)) 1 0) s.1 s.2
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      w (d r).exponent*complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩=
        phi (e.symm (a r)) := by
    rw [(d r).comparison_phase A hp hprimary hA hC]
    change phi ((d r).stratum hp.ne_zero)=phi (e.symm (a r))
    apply congrArg phi
    apply e.injective
    rw [e.apply_symm_apply]
    change cubeResidueStratumMap p ((d r).stratum hp.ne_zero)=a r
    rw [(d r).stratum_map hp.ne_zero]
    rw [←cubeCuspAffineEquiv_mk p ((A:SL(2,Eis)) 0 0) ((A:SL(2,Eis)) 1 0)
      (GaussianShiftedPartition.representative (p^3) r) hprimary hC,
      GaussianShiftedPartition.representative_spec]
  let (j:Fin 4):Finite (Eis⧸Ideal.span {p^(3-j.val)}) :=
    finite_quotient_span (pow_ne_zero _ hp.ne_zero)
  let (j:Fin 4):Finite (CubicUnitResidue (p^(3-j.val))) := inferInstance
  have hphi:Summable phi:=Summable.of_finite
  calc
    actualCubeCuspPhaseSum A p hp hprimary w = ∑' r,phi (e.symm (a r)) := by
      unfold actualCubeCuspPhaseSum
      exact tsum_congr hpoint
    _ = ∑' r,phi (e.symm r) := a.tsum_eq (fun r => phi (e.symm r))
    _ = ∑' s,phi s := e.symm.tsum_eq phi
    _ = ∑j:Fin 4,w j*∑' b:CubicUnitResidue (p^(3-j.val)),cubeStratumSymbol p ((A:SL(2,Eis)) 1 0) j b := by
      rw [hphi.tsum_sigma,tsum_fintype]
      apply Finset.sum_congr rfl
      intro j hj
      exact tsum_mul_left (f := fun b:CubicUnitResidue (p^(3-j.val)) =>
        cubeStratumSymbol p ((A:SL(2,Eis)) 1 0) j b) (a := w j)
    _ = _ := cubeStrata_weighted_sum p ((A:SL(2,Eis)) 1 0) hp hprimary hC w

theorem actualCubeCuspPhaseSum_dvd (A:levelTwo) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hC:p∣((A:SL(2,Eis)) 1 0)) (w:Fin 4→ℂ) :
    actualCubeCuspPhaseSum A p hp hprimary w =
      w 0*(Ideal.absNorm (Ideal.span {p}):ℂ)^3 := by
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData (A:SL(2,Eis)) p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      w (d r).exponent*complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩=w 0 := by
    have hj:((d r).exponent:ℕ)=0:=cube_exponent_zero_of_lower_divisible
      (A:SL(2,Eis)) (d r).matrix p _ _ hp hC (d r).first
    have hj':(d r).exponent=0:=Fin.ext hj
    let N:levelTwo:=⟨(d r).matrix,comparison_levelTwo A (d r).matrix (d r).congruent⟩
    have hphase:=levelTwo_cube_zero_phase A N p
      (GaussianShiftedPartition.representative (p^3) r) hprimary hA
      (comparison_primary _ _ (d r).congruent hA)
      (by simpa only [hj,pow_zero,one_mul] using (d r).first)
      (by simpa only [hj,Nat.sub_zero] using (d r).lower_eq hp.ne_zero)
      (d r).congruent
    change w (d r).exponent*complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,(d r).congruent⟩=w 0
    rw [hphase,hj',mul_one]
  calc
    actualCubeCuspPhaseSum A p hp hprimary w = ∑' r:Eis⧸Ideal.span {p^3},w 0 := by
      unfold actualCubeCuspPhaseSum
      exact tsum_congr hpoint
    _ = (Nat.card (Eis⧸Ideal.span {p^3}):ℂ)*w 0 := by
      rw [tsum_const,nsmul_eq_mul]
    _ = _ := by
      change (Ideal.absNorm (Ideal.span {p^3}):ℂ)*w 0 = _
      rw [←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]
      ring

end CubicKubota

namespace CubicEisenstein

section
open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local notation "ramLambda" => (omega-1:Eis)

lemma onceCusp_trace_lambda : ramifiedTraceLambda*ramLambda=3*omega^2 := by
  unfold ramifiedTraceLambda
  linear_combination -ramified_omega_relation

lemma onceCusp_lambda_dvd_trace : ramLambda∣ramifiedTraceLambda := by
  refine ⟨-omega,?_⟩
  unfold ramifiedTraceLambda
  linear_combination ramified_omega_relation

def onceCuspScale (u:Eisˣ) : Eis := (u:Eis)*ramifiedTraceLambda

def onceCuspComplement (u:Eisˣ) : Eis := -(↑u⁻¹:Eis)*ramifiedTraceLambda

lemma onceCusp_scale_complement (u:Eisˣ) : onceCuspScale u*onceCuspComplement u=3 := by
  calc
    _ = -((u:Eis)*(↑u⁻¹:Eis))*ramifiedTraceLambda^2 := by
      unfold onceCuspScale onceCuspComplement; ring
    _ = 3 := by simp [ramifiedTraceLambda_square]

lemma onceCusp_scale_ne_zero (u:Eisˣ) : onceCuspScale u≠0 := by
  intro h
  have hh:=onceCusp_scale_complement u
  rw [h,zero_mul] at hh
  exact (by norm_num : (0:Eis)≠3) hh

lemma onceCusp_scale_lambda (u:Eisˣ) : (3:Eis)∣onceCuspScale u*ramLambda := by
  refine ⟨(u:Eis)*omega^2,?_⟩
  simp only [onceCuspScale,mul_assoc,onceCusp_trace_lambda]
  ring

lemma onceCusp_complement_lambda (u:Eisˣ) : ramLambda∣onceCuspComplement u :=
  onceCusp_lambda_dvd_trace.mul_left _

lemma onceCusp_scale_coprime (u:Eisˣ) (d:PrimaryLower) : IsCoprime (onceCuspScale u) d.val := by
  apply (isCoprime_mul_unit_left_left u.isUnit _ _).mpr
  apply (primary_coprime_three d.val (primaryLower_primary d)).symm.of_isCoprime_of_dvd_left
  exact ⟨-ramifiedTraceLambda,by linear_combination ramifiedTraceLambda_square⟩

abbrev OnceRamifiedData := Fin 3×UnitLowerData

def onceRamifiedToPrimitive (u:Eisˣ) (p:OnceRamifiedData) : PrimitiveRow := by
  let b:=omega^p.1.val*p.2.1.val
  let d:=p.2.2.val.val
  refine ⟨![onceCuspScale u*(b-d),d],?_,?_,p.2.2.val.2⟩
  · change IsCoprime (onceCuspScale u*(b-d)) d
    apply (onceCusp_scale_coprime u p.2.2.val).mul_left
    apply IsCoprime.symm
    apply (isCoprime_right_congr_of_dvd d (b-d) b ⟨-1,by ring⟩).mpr
    exact ((isCoprime_mul_unit_left_left ((omega_primitive.isUnit (by decide)).pow _) _ _).mpr
      p.2.2.2).symm
  · change (3:Eis)∣onceCuspScale u*(b-d)
    have hb:ramLambda∣b-1:=(halfPrimaryFromAssociate (p.1,p.2.1)).2
    have hd:ramLambda∣d-1:=halfPrimary_lambda_dvd_three.trans p.2.2.val.2
    have hbd:ramLambda∣b-d:=by
      simpa only [sub_sub_sub_cancel_right] using dvd_sub hb hd
    obtain ⟨k,hk⟩:=hbd
    rw [hk,←mul_assoc]
    exact (onceCusp_scale_lambda u).mul_right k

lemma onceRamifiedToPrimitive_bijective (u:Eisˣ) :
    Function.Bijective (onceRamifiedToPrimitive u) := by
  constructor
  · rintro ⟨j,a,d,had⟩ ⟨k,b,e,hbe⟩ h
    have hrow:=congrArg Subtype.val h
    have hde:d=e:=Subtype.ext (congrFun hrow 1)
    subst e
    have he:=congrFun hrow 0
    change onceCuspScale u*(omega^j.val*a.val-d.val)=
      onceCuspScale u*(omega^k.val*b.val-d.val) at he
    have hsub:=mul_left_cancel₀ (onceCusp_scale_ne_zero u) he
    have hassoc:halfPrimaryFromAssociate (j,a)=halfPrimaryFromAssociate (k,b):=by
      apply Subtype.ext
      change omega^j.val*a.val=omega^k.val*b.val
      linear_combination hsub
    have hp:=halfPrimaryFromAssociate_injective hassoc
    have hj:j=k:=congrArg Prod.fst hp
    have hab:a=b:=congrArg Prod.snd hp
    subst k
    subst b
    rfl
  · intro r
    obtain ⟨k,hk⟩:=r.2.2.1
    let d:PrimaryLower:=⟨r.val 1,r.2.2.2⟩
    let b:HalfPrimary:=⟨onceCuspComplement u*k+d.val,by
      have hh:=dvd_add ((onceCusp_complement_lambda u).mul_right k)
        (halfPrimary_lambda_dvd_three.trans d.2)
      convert hh using 1 ;ring⟩
    let p:=halfPrimaryAssociateEquiv.symm b
    have hp:omega^p.1.val*p.2.val=b.val:=
      congrArg Subtype.val (halfPrimaryAssociateEquiv.apply_symm_apply b)
    have hr:onceCuspScale u*(b.val-d.val)=r.val 0:=by
      change onceCuspScale u*(onceCuspComplement u*k+d.val-d.val)=_
      rw [add_sub_cancel_right,←mul_assoc,onceCusp_scale_complement,hk]
    have hcop:IsCoprime p.2.val d.val:=by
      have h0:IsCoprime (b.val-d.val) d.val:=
        (hr ▸ r.2.1).of_isCoprime_of_dvd_left (dvd_mul_left _ _)
      have hb:IsCoprime b.val d.val:=by
        apply IsCoprime.symm
        exact (isCoprime_right_congr_of_dvd d.val (b.val-d.val) b.val ⟨-1,by ring⟩).mp h0.symm
      rw [←hp] at hb
      exact hb.of_isCoprime_of_dvd_left (dvd_mul_left _ _)
    refine ⟨(p.1,⟨p.2,d,hcop⟩),Subtype.ext ?_⟩
    funext i
    fin_cases i
    · change onceCuspScale u*(omega^p.1.val*p.2.val-d.val)=r.val 0
      rw [hp,hr]
    · rfl

def onceRamifiedEquiv (u:Eisˣ) : OnceRamifiedData≃PrimitiveRow :=
  Equiv.ofBijective _ (onceRamifiedToPrimitive_bijective u)

lemma onceRamified_row_phase (u:Eisˣ) (p:OnceRamifiedData) :
    (cosetCharacter (primitiveRowEquiv.symm (onceRamifiedEquiv u p)))⁻¹=
      eisEmbedding (symbol (onceCuspScale u*omega^p.1.val) p.2.2.val.val)*
        eisEmbedding (symbol p.2.2.val.val p.2.1.val) := by
  rw [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
  change eisEmbedding (symbol (onceCuspScale u*(omega^p.1.val*p.2.1.val-p.2.2.val.val))
    p.2.2.val.val)=_
  have hh : symbol (onceCuspScale u*(omega^p.1.val*p.2.1.val-p.2.2.val.val)) p.2.2.val.val=
      symbol ((onceCuspScale u*omega^p.1.val)*p.2.1.val) p.2.2.val.val :=
    symbol_congr ⟨-onceCuspScale u,by ring⟩
  rw [hh,symbol_mul_numerator _ _ _ (primaryLower_primary p.2.2.val),
    symbol_reciprocity p.2.1.val p.2.2.val.val (primaryLower_ne_zero p.2.1)
      (primaryLower_ne_zero p.2.2.val) (primaryLower_primary p.2.1)
        (primaryLower_primary p.2.2.val),map_mul]

end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def diagonalPrimitiveMap (u:Eisˣ) (v:PrimitiveRow) : PrimitiveRow :=
  ⟨![(u:Eis)^2*v.val 0,v.val 1],by
    refine ⟨?_,?_,v.2.2.2⟩
    · exact (isCoprime_mul_unit_left_left (u.isUnit.pow 2) _ _).mpr v.2.1
    · exact v.2.2.1.mul_left _⟩

def diagonalPrimitiveEquiv (u:Eisˣ) : PrimitiveRow≃PrimitiveRow where
  toFun:=diagonalPrimitiveMap u
  invFun:=diagonalPrimitiveMap u⁻¹
  left_inv v:=by
    apply Subtype.ext
    funext i
    fin_cases i
    · change (↑u⁻¹:Eis)^2*((u:Eis)^2*v.val 0)=v.val 0
      rw [←mul_assoc,←mul_pow]
      simp
    · rfl
  right_inv v:=by
    apply Subtype.ext
    funext i
    fin_cases i
    · change (u:Eis)^2*((↑u⁻¹:Eis)^2*v.val 0)=v.val 0
      rw [←mul_assoc,←mul_pow]
      simp
    · rfl

lemma rowOperator_unitCuspDiagonal (u:Eisˣ) (v:PrimitiveRow) :
    rowOperator (integralComplexMatrix (unitCuspDiagonal u))
      (embeddedRow (primitiveRowEquiv.symm v))=
      eisEmbedding (↑u⁻¹:Eis) •
        embeddedRow (primitiveRowEquiv.symm (diagonalPrimitiveEquiv u v)) := by
  simp only [embeddedRow, Function.comp_def, primitiveRowEquiv_symm_row]
  rw [rowOperator_apply]
  funext i
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    integralComplexMatrix_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases i
  · change eisEmbedding (v.val 0) * eisEmbedding (u : Eis) +
      eisEmbedding (v.val 1) * eisEmbedding (0 : Eis) =
      eisEmbedding (↑u⁻¹ : Eis) * eisEmbedding ((u : Eis) ^ 2 * v.val 0)
    simp only [map_zero, mul_zero, add_zero, map_mul, pow_two]
    have hu : eisEmbedding (↑u⁻¹ : Eis) * eisEmbedding (u : Eis) = 1 := by
      rw [← map_mul]
      simp
    calc
      _ = (eisEmbedding (↑u⁻¹ : Eis) * eisEmbedding (u : Eis)) *
          (eisEmbedding (v.val 0) * eisEmbedding (u : Eis)) := by rw [hu, one_mul]
      _ = _ := by ring
  · change eisEmbedding (v.val 0) * eisEmbedding (0 : Eis) +
      eisEmbedding (v.val 1) * eisEmbedding (↑u⁻¹ : Eis) =
      eisEmbedding (↑u⁻¹ : Eis) * eisEmbedding (v.val 1)
    simp [mul_comm]

lemma rowEnergy_unit_smul (u:Eisˣ) (v:Fin 2→ℂ) :
    rowEnergy (eisEmbedding (u:Eis) • v)=rowEnergy v := by
  simp only [rowEnergy,Pi.smul_apply,smul_eq_mul,norm_mul,
    GaussGeneratorTransport.norm_eisEmbedding_unit,one_mul]

lemma diagonal_ray_summand (u:Eisˣ) (g:SL(2,ℂ)) (s:ℂ) (v:PrimitiveRow) :
    summand (integralComplexMatrix (unitCuspDiagonal u)*g) s (primitiveRowEquiv.symm v)=
      eisEmbedding (symbol ((↑u⁻¹:Eis)^2) (v.val 1))*
        summand g s (primitiveRowEquiv.symm (diagonalPrimitiveEquiv u v)) := by
  have hphase : (cosetCharacter (primitiveRowEquiv.symm v))⁻¹=
      eisEmbedding (symbol ((↑u⁻¹:Eis)^2) (v.val 1))*
        (cosetCharacter (primitiveRowEquiv.symm (diagonalPrimitiveEquiv u v)))⁻¹ := by
    simp only [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
    change eisEmbedding (symbol (v.val 0) (v.val 1))=
      eisEmbedding (symbol ((↑u⁻¹:Eis)^2) (v.val 1))*
        eisEmbedding (symbol ((u:Eis)^2*v.val 0) (v.val 1))
    rw [←map_mul,←symbol_mul_numerator _ _ _ (lambda_sq_dvd_three.trans v.2.2.2)]
    congr 2
    rw [←mul_assoc,←mul_pow]
    simp
  rw [summand,←rowOperator_mul,rowOperator_unitCuspDiagonal,map_smul,rowEnergy_unit_smul,hphase,
    summand]
  ring

def rayEisenstein (r:Eis) (g:SL(2,ℂ)) (s:ℂ) : ℂ :=
  ∑'v:PrimitiveRow,eisEmbedding (symbol r (v.val 1))*summand g s (primitiveRowEquiv.symm v)

theorem eisenstein_unit_diagonal (u:Eisˣ) (g:SL(2,ℂ)) (s:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*g) s=
      rayEisenstein ((↑u⁻¹:Eis)^2) g s := by
  rw [eisenstein,←primitiveRowEquiv.symm.tsum_eq]
  simp_rw [diagonal_ray_summand]
  exact (diagonalPrimitiveEquiv u).tsum_eq
    (fun v:PrimitiveRow=>eisEmbedding (symbol ((↑u⁻¹:Eis)^2) (v.val 1))*
      summand g s (primitiveRowEquiv.symm v))

end

section
open MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def affineLowerTerm (q r:Eis) (z:ℂ) (v:ℝ) (s:ℂ) (a d:Eis) : ℂ :=
  (eisEmbedding (symbol r d)*eisEmbedding (symbol d a))*
    ((v/(‖eisEmbedding (q*a)*z+eisEmbedding d‖^2+
      ‖eisEmbedding (q*a)‖^2*v^2):ℝ):ℂ)^s

lemma affineLowerTerm_mul_ray (q r t:Eis) (z:ℂ) (v:ℝ) (s:ℂ) (a d:PrimaryLower) :
    eisEmbedding (symbol t d.val)*affineLowerTerm q r z v s a.val d.val=
      affineLowerTerm q (t*r) z v s a.val d.val := by
  rw [affineLowerTerm,affineLowerTerm,symbol_mul_numerator _ _ _ (primaryLower_primary d),
    map_mul eisEmbedding (symbol t d.val) (symbol r d.val)]
  ring

lemma onceRamified_summand (u:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (p:OnceRamifiedData) :
    summand (integralComplexMatrix (lowerCuspMatrix (onceCuspScale u))*upperSection z v hv) s
      (primitiveRowEquiv.symm (onceRamifiedEquiv u p))=
      affineLowerTerm (onceCuspScale u*omega^p.1.val) (onceCuspScale u*omega^p.1.val)
        z v s p.2.1.val p.2.2.val.val := by
  let r:Fin 2→ℂ:=![eisEmbedding ((onceCuspScale u*omega^p.1.val)*p.2.1.val),
    eisEmbedding p.2.2.val.val]
  have hr:rowOperator (integralComplexMatrix (lowerCuspMatrix (onceCuspScale u)))
      (embeddedRow (primitiveRowEquiv.symm (onceRamifiedEquiv u p)))=r:=by
    rw [embeddedRow, primitiveRowEquiv_symm_row, rowOperator_lowerCusp]
    funext i
    fin_cases i <;>
      simp [onceRamifiedEquiv, Equiv.ofBijective_apply, onceRamifiedToPrimitive,
        r, map_mul, map_sub, mul_sub, mul_assoc]
  have hr0:r≠0:=by
    intro hh
    have he:=congrFun hh 1
    exact eisEmbedding_ne_zero (primaryLower_ne_zero p.2.2.val) he
  have hp:=heightDenominator_pos z v hv r hr0
  rw [summand,←rowOperator_mul,hr,rowEnergy_upperSection,onceRamified_row_phase]
  change _= (eisEmbedding (symbol (onceCuspScale u*omega^p.1.val) p.2.2.val.val)*
    eisEmbedding (symbol p.2.2.val.val p.2.1.val))*((v/heightDenominator z v r:ℝ):ℂ)^s
  have hi:((v/heightDenominator z v r:ℝ):ℂ)=(((heightDenominator z v r/v:ℝ):ℂ))⁻¹:=by
    simp only [Complex.ofReal_div,inv_div]
  rw [hi,Complex.inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le),Complex.cpow_neg]

def diagonalOnceCuspIndex (u t:Eisˣ) : OnceRamifiedData≃CuspCosets :=
  (onceRamifiedEquiv t).trans ((diagonalPrimitiveEquiv u).symm.trans primitiveRowEquiv.symm)

def diagonalUnitCuspIndex (u t:Eisˣ) : UnitLowerData≃CuspCosets :=
  (unitLowerEquiv t).trans ((diagonalPrimitiveEquiv u).symm.trans primitiveRowEquiv.symm)

lemma diagonal_once_summand (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (p:OnceRamifiedData) :
    summand (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv)) s
      (diagonalOnceCuspIndex u t p)=
      affineLowerTerm (onceCuspScale t*omega^p.1.val)
        ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val := by
  change summand _ _ (primitiveRowEquiv.symm
    ((diagonalPrimitiveEquiv u).symm (onceRamifiedEquiv t p)))=_
  rw [diagonal_ray_summand,Equiv.apply_symm_apply,onceRamified_summand]
  change eisEmbedding (symbol ((↑u⁻¹:Eis)^2) p.2.2.val.val)*affineLowerTerm _ _ _ _ _ _ _=_
  exact affineLowerTerm_mul_ray _ _ _ _ _ _ p.2.1 p.2.2.val

lemma diagonal_unit_summand (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (p:UnitLowerData) :
    summand (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (t:Eis)))*upperSection z v hv) s
      (diagonalUnitCuspIndex u t p)=
      affineLowerTerm (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis)) z v s p.1.val p.2.val.val := by
  rw [mul_assoc]
  change summand _ _ (primitiveRowEquiv.symm
    ((diagonalPrimitiveEquiv u).symm (unitLowerEquiv t p)))=_
  rw [diagonal_ray_summand,Equiv.apply_symm_apply,unitLower_summand]
  change eisEmbedding (symbol ((↑u⁻¹:Eis)^2) p.2.val.val)*affineLowerTerm _ _ _ _ _ _ _=_
  exact affineLowerTerm_mul_ray _ _ _ _ _ _ p.1 p.2.val

theorem diagonal_once_eisenstein_rows (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv)) s=
      ∑'p:OnceRamifiedData,affineLowerTerm (onceCuspScale t*omega^p.1.val)
        ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val := by
  rw [eisenstein,←(diagonalOnceCuspIndex u t).tsum_eq]
  exact tsum_congr (diagonal_once_summand u t z v hv s)

theorem diagonal_unit_eisenstein_rows (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (t:Eis)))*upperSection z v hv) s=
      ∑'p:UnitLowerData,affineLowerTerm (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis))
        z v s p.1.val p.2.val.val := by
  rw [eisenstein,←(diagonalUnitCuspIndex u t).tsum_eq]
  exact tsum_congr (diagonal_unit_summand u t z v hv s)

theorem hasSum_diagonal_once_integrals (u t:Eisˣ) (v:ℝ) (hv:0<v) (s freq:ℂ) (hs:2<s.re) :
    HasSum (fun p:OnceRamifiedData=>∫z in periodDomain,
      affineLowerTerm (onceCuspScale t*omega^p.1.val)
        ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val*
          ShortDraftTrace.breveE (-freq*z))
      (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
        integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv) s*
          ShortDraftTrace.breveE (-freq*z)) := by
  have hh:=(diagonalOnceCuspIndex u t).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein
      (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)))
      v hv s freq hs)
  apply hh.congr_fun
  intro p
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z=>by dsimp only; rw [mul_assoc,diagonal_once_summand])

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

open ConcreteTraceCRT EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def eisensteinCoordinateMul (b : ActualEisensteinCubic.O) (x : Fin 2→ℝ) : Fin 2→ℝ :=
  ![(ActualEisensteinCoordinates.coords b).1 • x 0-(ActualEisensteinCoordinates.coords b).2 • x 1,
    (ActualEisensteinCoordinates.coords b).2 • x 0+
      ((ActualEisensteinCoordinates.coords b).1-(ActualEisensteinCoordinates.coords b).2) • x 1]

def eisensteinTorusMul (b : ActualEisensteinCubic.O) : UnitAddTorus (Fin 2)→+UnitAddTorus (Fin 2) where
  toFun t :=
    ![(ActualEisensteinCoordinates.coords b).1 • t 0-(ActualEisensteinCoordinates.coords b).2 • t 1,
      (ActualEisensteinCoordinates.coords b).2 • t 0+
        ((ActualEisensteinCoordinates.coords b).1-(ActualEisensteinCoordinates.coords b).2) • t 1]
  map_zero' := by ext i;fin_cases i <;> simp
  map_add' t s := by ext i;fin_cases i <;> simp [smul_add] <;> abel

lemma eisensteinTorusMul_continuous (b : ActualEisensteinCubic.O) : Continuous (eisensteinTorusMul b) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun t : UnitAddTorus (Fin 2) => (ActualEisensteinCoordinates.coords b).1 • t 0-(ActualEisensteinCoordinates.coords b).2 • t 1)
    fun_prop
  · change Continuous (fun t : UnitAddTorus (Fin 2) => (ActualEisensteinCoordinates.coords b).2 • t 0+((ActualEisensteinCoordinates.coords b).1-(ActualEisensteinCoordinates.coords b).2) • t 1)
    fun_prop

lemma periodVector_coordinateMul (b : ActualEisensteinCubic.O) (x : Fin 2→ℝ) :
    periodVector (eisensteinCoordinateMul b x)=eisEmbedding b*periodVector x := by
  have hb : eisEmbedding b=((ActualEisensteinCoordinates.coords b).1:ℂ)+
      ((ActualEisensteinCoordinates.coords b).2:ℂ)*omega3 := by
    simpa only [ActualEisensteinCubic.eisEmbedding_eval] using (congrArg eisEmbedding (ActualEisensteinCoordinates.eval_coords b)).symm
  rw [periodVector_apply,periodVector_apply,hb]
  simp only [eisensteinCoordinateMul,Matrix.cons_val_zero,Matrix.cons_val_one,
    zsmul_eq_mul]
  push_cast
  linear_combination -(3*((ActualEisensteinCoordinates.coords b).2:ℂ)*(x 1:ℂ))*EisensteinEmbedding.omega3_sq

lemma eisensteinTorusMul_periodTorus (b : ActualEisensteinCubic.O) (z : ℂ) :
    eisensteinTorusMul b (periodTorus z)=periodTorus (eisEmbedding b*z) := by
  obtain ⟨x,rfl⟩ := periodVector.surjective z
  rw [←periodVector_coordinateMul,periodTorus_periodVector,periodTorus_periodVector]
  ext i
  fin_cases i <;> rfl

lemma eisensteinTorusMul_surjective (b : ActualEisensteinCubic.O) (hb : b≠0) : Function.Surjective (eisensteinTorusMul b) := by
  intro t
  refine ⟨periodTorus ((eisEmbedding b)⁻¹*periodSection t),?_⟩
  rw [eisensteinTorusMul_periodTorus,←mul_assoc,mul_inv_cancel₀ (eisEmbedding_ne_zero hb),one_mul,
    periodTorus_section]

theorem eisensteinTorusMul_measurePreserving (b : ActualEisensteinCubic.O) (hb : b≠0) :
    MeasurePreserving (eisensteinTorusMul b) volume volume :=
  AddMonoidHom.measurePreserving (eisensteinTorusMul_continuous b) (eisensteinTorusMul_surjective b hb) rfl

lemma periodTorus_eq_implies_lattice_difference (z w : ℂ) (h : periodTorus z=periodTorus w) :
    ∃n : ActualEisensteinCubic.O,z=w+3*eisEmbedding n := by
  obtain ⟨x,rfl⟩ := periodVector.surjective z
  obtain ⟨y,rfl⟩ := periodVector.surjective w
  rw [periodTorus_periodVector,periodTorus_periodVector] at h
  have hz (i : Fin 2) : ((x i-y i:ℝ):UnitAddCircle)=0 := by
    rw [AddCircle.coe_sub,congrFun h i,sub_self]
  obtain ⟨n0,hn0⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp (hz 0)
  obtain ⟨n1,hn1⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp (hz 1)
  simp only [zsmul_eq_mul,mul_one] at hn0 hn1
  have hx0 : x 0=y 0+n0 := by linarith
  have hx1 : x 1=y 1+n1 := by linarith
  refine ⟨ActualEisensteinCoordinates.eval n0 n1,?_⟩
  rw [periodVector_apply,periodVector_apply,ActualEisensteinCubic.eisEmbedding_eval,hx0,hx1]
  push_cast
  ring

lemma periodic_function_periodSection (f : ℂ→ℂ)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (z : ℂ) :
    f (periodSection (periodTorus z))=f z := by
  obtain ⟨n,hn⟩ := periodTorus_eq_implies_lattice_difference (periodSection (periodTorus z)) z
    (periodTorus_section (periodTorus z))
  rw [hn,hp]

theorem period_integral_eisenstein_mul (f : ℂ→ℂ) (hf : Measurable f)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (b : ActualEisensteinCubic.O) (hb : b≠0) :
    (∫z in periodDomain,f (eisEmbedding b*z))=∫z in periodDomain,f z := by
  let F : UnitAddTorus (Fin 2)→ℂ := fun t=>f (periodSection t)
  have hF : Measurable F := hf.comp periodSection_measurableEmbedding.measurable
  have hm := eisensteinTorusMul_measurePreserving b hb
  have hi : (∫t,F (eisensteinTorusMul b t))=∫t,F t := by
    have hh := integral_map («μ» := (volume : Measure (UnitAddTorus (Fin 2)))) hm.measurable.aemeasurable hF.stronglyMeasurable.aestronglyMeasurable
    rw [hm.map_eq] at hh
    exact hh.symm
  rw [periodTorus_integral,periodTorus_integral] at hi
  simp only [eisensteinTorusMul_periodTorus,F,periodic_function_periodSection f hp] at hi
  simp only [Complex.real_smul] at hi
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (show (2/(9*Real.sqrt 3):ℝ)≠0 by positivity)) hi

end CubicEisenstein

open MeasureTheory Filter
open scoped BigOperators Classical ENNReal

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem finite_index_period_unfold_of_summable (q:Eis) (hq:q≠0) (f:ℂ→ℂ) (hf:Integrable f)
    (hsum:Summable (fun n:Eis=>∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))) :
    (∑'n:Eis,∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*(∫z:ℂ,f z) := by
  let : Finite (Eis⧸Ideal.span {q}):=finite_quotient_span hq
  let : Fintype (Eis⧸Ideal.span {q}):=Fintype.ofFinite _
  let I:Eis→ℂ:=fun n=>∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q)
  have hinner (r:Eis⧸Ideal.span {q}) :
      (∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),I n.val)=∫z:ℂ,f z := by
    rw [GaussianFiberEquiv.fiber_tsum q hq r (GaussianShiftedPartition.representative q r)
      (GaussianShiftedPartition.representative_spec q r)]
    let b:=3*eisEmbedding (GaussianShiftedPartition.representative q r)/eisEmbedding q
    have he (n:Eis) (z:ℂ) :
        z+3*eisEmbedding (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q=
          (z+3*eisEmbedding n)+b := by
      dsimp [b]
      simp only [map_add,map_mul]
      field_simp [eisEmbedding_ne_zero hq]
      ;ring
    change (∑'n:Eis,∫z in periodDomain,f (z+3*eisEmbedding
      (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q))=_
    simp_rw [he]
    rw [←integral_eq_period_integrals (fun z=>f (z+b)) (hf.comp_add_right b)]
    exact integral_add_right_eq_self f b
  have hsplit:=(hsum.hasSum.tsum_fiberwise (Ideal.Quotient.mk (Ideal.span {q}))).tsum_eq.symm
  change (∑'n:Eis,I n)=_ at hsplit ⊢
  rw [hsplit]
  change (∑'r:Eis⧸Ideal.span {q},∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),I n.val)=_
  simp only [hinner,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 1
  change (Fintype.card (Eis⧸Ideal.span {q}):ℂ)=(Nat.card (Eis⧸Ideal.span {q}):ℂ)
  rw [Nat.card_eq_fintype_card]

lemma finite_index_period_lintegral (q:Eis) (hq:q≠0) (f:ℂ→ℝ≥0∞) :
    (∑'n:Eis,∫⁻z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      (Ideal.absNorm (Ideal.span {q}):ℝ≥0∞)*(∫⁻z:ℂ,f z) := by
  let : Finite (Eis⧸Ideal.span {q}):=finite_quotient_span hq
  let : Fintype (Eis⧸Ideal.span {q}):=Fintype.ofFinite _
  let I:Eis→ℝ≥0∞:=fun n=>∫⁻z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q)
  have hinner (r:Eis⧸Ideal.span {q}) :
      (∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),I n.val)=∫⁻z:ℂ,f z := by
    rw [←(GaussianFiberEquiv.fiberEquiv q hq r (GaussianShiftedPartition.representative q r)
      (GaussianShiftedPartition.representative_spec q r)).tsum_eq]
    change (∑'n:Eis,∫⁻z in periodDomain,f (z+3*eisEmbedding
      (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q))=_
    let b:=3*eisEmbedding (GaussianShiftedPartition.representative q r)/eisEmbedding q
    have he (n:Eis) (z:ℂ) :
        z+3*eisEmbedding (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q=
          (z+3*eisEmbedding n)+b := by
      dsimp [b]
      simp only [map_add,map_mul]
      field_simp [eisEmbedding_ne_zero hq]
      ;ring
    simp_rw [he]
    rw [←lintegral_eq_period_lintegrals (fun z=>f (z+b))]
    exact lintegral_add_right_eq_self f b
  change (∑'n:Eis,I n)=_
  rw [←ENNReal.tsum_fiberwise I (Ideal.Quotient.mk (Ideal.span {q}))]
  simp only [hinner,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 1
  change (Fintype.card (Eis⧸Ideal.span {q}):ℝ≥0∞)=(Nat.card (Eis⧸Ideal.span {q}):ℝ≥0∞)
  rw [Nat.card_eq_fintype_card]

lemma finite_index_period_integrals_summable (q:Eis) (hq:q≠0) (f:ℂ→ℂ) (hf:Integrable f) :
    Summable (fun n:Eis=>∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q)) := by
  apply Summable.of_enorm
  apply ne_of_lt
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n=>enorm_integral_le_lintegral_enorm _))
  rw [finite_index_period_lintegral q hq (fun z=>‖f z‖ₑ)]
  exact ENNReal.mul_lt_top (by simp) hf.hasFiniteIntegral

theorem finite_index_period_unfold (q:Eis) (hq:q≠0) (f:ℂ→ℂ) (hf:Integrable f) :
    (∑'n:Eis,∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*(∫z:ℂ,f z) :=
  finite_index_period_unfold_of_summable q hq f hf
    (finite_index_period_integrals_summable q hq f hf)

end CubicEisenstein

end

end OAI
