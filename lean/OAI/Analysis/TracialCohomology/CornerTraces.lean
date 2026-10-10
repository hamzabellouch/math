import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.Partitions
import OAI.Analysis.TracialCohomology.RepresentationLimits
import OAI.Analysis.TracialCohomology.MatrixNorms

namespace OAI

/-! Corner traces for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {p : M} (hp : IsStarProjection p) (τ : M →ₚ[ℂ] ℂ)

def trace : algebra hp →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀
  ((((τ p).re⁻¹ : ℝ) : ℂ) • τ.toLinearMap.comp (algebra hp).toNonUnitalSubalgebra.toSubmodule.subtype) (by
    intro a ha
    change 0 ≤ (((τ p).re⁻¹ : ℝ) : ℂ)*τ (a:M)
    apply mul_nonneg
    · exact Complex.nonneg_iff.mpr ⟨inv_nonneg.mpr
        (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).1,rfl⟩
    · exact τ.map_nonneg ha)

@[simp] lemma trace_apply (a : algebra hp) :
    trace hp τ a=(((τ p).re⁻¹ : ℝ) : ℂ)*τ (a:M) := rfl

lemma trace_faithful (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) :
    ∀ a : algebra hp, trace hp τ (star a*a)=0 → a=0 := by
  intro a ha
  by_cases hp0 : p=0
  · apply Subtype.ext
    change (a:M)=0
    have hh := a.property.1
    simpa only [hp0,zero_mul] using hh.symm
  · have ht : 0 < (τ p).re := projection_trace_pos τ hfaith hp hp0
    apply Subtype.ext
    apply hfaith
    change (((τ p).re⁻¹ : ℝ) : ℂ)*τ (star (a:M)*(a:M))=0 at ha
    exact (mul_eq_zero.mp ha).resolve_left (by exact_mod_cast inv_ne_zero ht.ne')

lemma trace_tracial (htr : ∀ a b : M, τ (a*b)=τ (b*a)) :
    ∀ a b : algebra hp, trace hp τ (a*b)=trace hp τ (b*a) := by
  intro a b
  exact congrArg (fun z => (((τ p).re⁻¹ : ℝ) : ℂ)*z) (htr a.val b.val)

lemma trace_one (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hp0 : p ≠ 0) :
    trace hp τ 1=1 := by
  rw [trace_apply,coe_one]
  have ht : 0 < (τ p).re := projection_trace_pos τ hfaith hp hp0
  have hi := (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).2
  have he : τ p=((τ p).re : ℂ) := by apply Complex.ext <;> simp [hi]
  conv_lhs => rhs; rw [he]
  rw [←Complex.ofReal_mul,inv_mul_cancel₀ ht.ne',Complex.ofReal_one]

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
lemma trace_normal (hτ : TraceInPredual e τ) :
    TraceInPredual (predualEquiv e hp) (trace hp τ) := by
  obtain ⟨z,hz⟩ := hτ
  refine ⟨(((τ p).re⁻¹ : ℝ) : ℂ) • (Submodule.Quotient.mk z),fun a => ?_⟩
  rw [map_smul,predualEquiv_symm_apply_mk,trace_apply,hz a.val]
  simp [smul_eq_mul]

lemma corner_diffuse (hdiff : NoMinimalProjections M) : NoMinimalProjections (algebra hp) := by
  intro q hq hq0
  have hqM : IsStarProjection (q:M) := hq.map (incl hp)
  obtain ⟨r,hr,hrq,hr0,hrne⟩ := hdiff (q:M) hqM (fun he => hq0 (Subtype.ext he))
  have hqp : (q:M) ≤ p := (hqM.le_iff_mul_eq_left hp).mpr q.property.2
  have hrp : r ≤ p := hrq.trans hqp
  let r' : algebra hp := ⟨r,(hr.le_iff_mul_eq_right hp).mp hrp,(hr.le_iff_mul_eq_left hp).mp hrp⟩
  refine ⟨r',⟨Subtype.ext hr.isIdempotentElem.eq,Subtype.ext hr.isSelfAdjoint.star_eq⟩,
    hrq,fun he => hr0 (congrArg Subtype.val he),fun he => hrne (congrArg Subtype.val he)⟩
end PopaCorner

open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaMatrices
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {p : M} (hp : IsStarProjection p)

omit [PartialOrder M] [StarOrderedRing M] in
lemma full_center_lift {n : ℕ} (a b : Fin n → M)
    (ha : ∀ i, a i*p=a i) (hb : ∀ i, p*b i=b i) (hs : ∑ i, a i*b i=1)
    (x : algebra hp) (hx : ∀ z : algebra hp, Commute x z) :
    ∃ c : M, (∀ y : M, Commute c y) ∧ c*p=(x:M) := by
  let c : M := ∑ i, a i*(x:M)*b i
  have hz (z : M) (hz : z*p=z) : c*z=z*(x:M) := by
    have hm (i : Fin n) : b i*z ∈ algebra hp := by
      exact ⟨by rw [←mul_assoc,hb],by rw [mul_assoc,hz]⟩
    have hc (i : Fin n) : (x:M)*(b i*z)=(b i*z)*(x:M) :=
      congrArg Subtype.val (hx ⟨b i*z,hm i⟩).eq
    calc
      c*z = ∑ i, a i*((x:M)*(b i*z)) := by simp only [c,Finset.sum_mul,mul_assoc]
      _ = ∑ i, (a i*b i)*z*(x:M) := by simp only [hc,mul_assoc]
      _ = z*(x:M) := by rw [←Finset.sum_mul,←Finset.sum_mul,hs,one_mul]
  refine ⟨c,fun y => ?_,?_⟩
  · change c*y=y*c
    calc
      c*y = (c*y)*(∑ i, a i*b i) := by rw [hs,mul_one]
      _ = ∑ i, (c*(y*a i))*b i := by simp only [Finset.mul_sum,mul_assoc]
      _ = ∑ i, ((y*a i)*(x:M))*b i := by
        apply Finset.sum_congr rfl; intro i _
        rw [hz (y*a i) (by rw [mul_assoc,ha])]
      _ = y*c := by simp only [c,Finset.mul_sum,mul_assoc]
  · rw [hz p hp.isIdempotentElem.eq,x.property.1]

section Dual
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

include e hτ htr hfaith h1 hfactor in
lemma full_corner (hdiff : NoMinimalProjections M) {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ n : ℕ, ∃ a b : Fin n → M,
      (∀ i, a i*p=a i) ∧ (∀ i, p*b i=b i) ∧ ∑ i, a i*b i=1 := by
  have ht : 0 < (τ p).re := projection_trace_pos τ hfaith hp hp0
  obtain ⟨N,hN⟩ := exists_nat_gt (1/(τ p).re)
  have hNR : 0 < (N:ℝ) := (by positivity : 0 < 1/(τ p).re).trans hN
  have hNpos : 0<N := Nat.cast_pos.mp hNR
  have htp : 1/(N:ℝ) ≤ (τ p).re := by
    apply (div_le_iff₀ hNR).mpr
    have hh := (div_lt_iff₀ ht).mp hN
    nlinarith
  obtain ⟨s,hs⟩ := exists_system e τ hτ htr hfaith h1 hfactor hdiff N hNpos (IsStarProjection.one M)
  let i0 : Fin N := ⟨0,hNpos⟩
  obtain ⟨q,hq,hqp,hqt⟩ := exists_projection_of_trace τ e
    (HochschildSakai.abstract_multiplication_normal e).1 hτ htr hfaith hdiff hp
    (1/(N:ℝ)) (by positivity) htp
  have hsi : IsStarProjection (s.entry i0 i0) :=
    ⟨by simpa [IsIdempotentElem] using s.mul_entry i0 i0 i0 i0,s.star_entry i0 i0⟩
  obtain ⟨v,hvi,hvf,hvr,hqv⟩ := PopaCorners.CornerIso.equivalent_of_trace_eq e τ hτ htr hfaith h1 hfactor
    hsi hq (by rw [hs,h1,Complex.one_re,hqt])
  have hpv : p*v=v := by rw [←hqv,←mul_assoc,(hq.le_iff_mul_eq_right hp).mp hqp,hqv]
  have hvp : star v*p=star v := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpv
  refine ⟨N,fun i => s.entry i i0*star v,fun i => v*s.entry i0 i,?_,?_,?_⟩
  · intro i; rw [mul_assoc,hvp]
  · intro i; rw [←mul_assoc,hpv]
  · have he (i : Fin N) : (s.entry i i0*star v)*(v*s.entry i0 i)=s.entry i i := by
      rw [mul_assoc,←mul_assoc (star v),hvi,←mul_assoc,s.mul_entry,ite_eq_left rfl,s.mul_entry,ite_eq_left rfl]
    simp only [he,s.sum_diag]

include e hτ htr hfaith h1 hfactor in
lemma corner_factor (hdiff : NoMinimalProjections M) {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∀ b : algebra hp, (∀ x : algebra hp, Commute b x) → ∃ c : ℂ, b=c • (1:algebra hp) := by
  obtain ⟨n,a,b,ha,hb,hs⟩ := full_corner e τ hτ htr hfaith h1 hfactor hdiff hp hp0
  intro x hx
  obtain ⟨c,hc,hcp⟩ := full_center_lift hp a b ha hb hs x hx
  obtain ⟨z,hz⟩ := hfactor c hc
  refine ⟨z,Subtype.ext ?_⟩
  change (x:M)=z • p
  rw [←hcp,hz,smul_mul_assoc,one_mul]
end Dual
end PopaCorner

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaTypeII PopaMatrices PopaCorner
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma corner_typeII (hII : NoAbelianCorners M) {p : M} (hp : IsStarProjection p) :
    NoAbelianCorners (algebra hp) := by
  intro q hq hq0
  have hqM : IsStarProjection (q:M) := hq.map (incl hp)
  obtain ⟨x,y,hxy⟩ := hII (q:M) hqM (fun he => hq0 (Subtype.ext he))
  let L (z : algebra hqM) : algebra hp := ⟨z,by
    calc p*(z:M)=p*((q:M)*(z:M)) := by rw [z.property.1]
         _=(p*(q:M))*(z:M) := (mul_assoc _ _ _).symm
         _=(z:M) := by rw [q.property.1,z.property.1],by
    calc (z:M)*p=((z:M)*(q:M))*p := by rw [z.property.2]
         _=(z:M)*((q:M)*p) := mul_assoc _ _ _
         _=(z:M) := by rw [q.property.2,z.property.2]⟩
  let K (z : algebra hqM) : algebra hq := ⟨L z,Subtype.ext z.property.1,Subtype.ext z.property.2⟩
  refine ⟨K x,K y,fun hh => hxy ?_⟩
  apply Subtype.ext
  exact congrArg (fun z : algebra hq => ((z:algebra hp):M)) hh.eq

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
lemma full_corner_center (hII : NoAbelianCorners M) {p : M} (hp : IsStarProjection p)
    {t : ℝ} (ht : 0 < t) (hEp : average e τ hτ htr hfaith p=t • (1:M)) :
    ∃ n : ℕ, ∃ a b : Fin n → M,
      (∀ i, a i*p=a i) ∧ (∀ i, p*b i=b i) ∧ ∑ i, a i*b i=1 := by
  obtain ⟨k,hk⟩ := exists_nat_gt (1/t)
  have hpow : k < 2^(k+1) := lt_trans (Nat.lt_succ_self k) (Nat.lt_two_pow_self)
  have hn : 0 < 2^(k+1) := pow_pos (by omega) _
  have hnR : 0 < ((2^(k+1):ℕ):ℝ) := Nat.cast_pos.mpr hn
  have hle : ((2^(k+1):ℕ):ℝ)⁻¹ ≤ t := by
    have hh := hk.trans (Nat.cast_lt.mpr hpow)
    have hh' := (div_lt_iff₀ ht).mp hh
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hnR).mpr
    nlinarith
  obtain ⟨s⟩ := exists_dyadic_system e τ hτ htr hfaith h1 hII (k+1)
  let i0 : Fin (2^(k+1)) := ⟨0,hn⟩
  have hs := s.diagonal_projection i0
  have hEs : average e τ hτ htr hfaith (s.entry i0 i0)=((2^(k+1):ℕ):ℝ)⁻¹ • (1:M) := by
    have hh := congrArg (fun z : M => ((2^(k+1):ℕ):ℝ)⁻¹ • z)
      (average_diagonal_one e τ hτ htr hfaith h1 s i0)
    simpa only [smul_smul,inv_mul_cancel₀ hnR.ne',one_smul] using hh
  have he : average e τ hτ htr hfaith (s.entry i0 i0) ≤ average e τ hτ htr hfaith p := by
    rw [hEs,hEp]
    exact smul_le_smul_of_nonneg_right hle (zero_le_one)
  obtain ⟨v,hvi⟩ := exists_full_initial_of_average_le e τ hτ htr hfaith h1 hs hp he
  have hpv : p*(v:M)=(v:M) := by
    rw [←v.final_mul,←mul_assoc,(v.final_proj.le_iff_mul_eq_right hp).mp v.final_le,v.final_mul]
  have hvp : star (v:M)*p=star (v:M) := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpv
  refine ⟨2^(k+1),fun i => s.entry i i0*star (v:M),fun i => (v:M)*s.entry i0 i,?_,?_,?_⟩
  · intro i; rw [mul_assoc,hvp]
  · intro i; rw [←mul_assoc,hpv]
  · have he (i : Fin (2^(k+1))) :
        (s.entry i i0*star (v:M))*((v:M)*s.entry i0 i)=s.entry i i := by
      rw [mul_assoc,←mul_assoc (star _),show star (v:M)*(v:M)=s.entry i0 i0 from hvi,
        ←mul_assoc,s.mul_entry,ite_eq_left rfl,s.mul_entry,ite_eq_left rfl]
    simp only [he,s.sum_diag]
end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorner
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def centerAlgebra : StarSubalgebra ℂ M where
  carrier := {a | Central a}
  zero_mem' := fun x => Commute.zero_left x
  one_mem' := fun x => Commute.one_left x
  add_mem' ha hb := fun x => (ha x).add_left (hb x)
  mul_mem' ha hb := central_mul ha hb
  algebraMap_mem' r := fun x => Algebra.commutes r x
  star_mem' ha := central_star ha

instance centerAlgebra_closed : IsClosed (centerAlgebra (M:=M) : Set M) := by
  change IsClosed {a : M | ∀ x : M, a*x=x*a}
  simpa only [Set.ofPred_forall,id_eq,Pi.mul_apply] using isClosed_iInter (fun x : M => isClosed_eq
    ((continuous_id : Continuous (fun a : M => a)).mul_const x)
    ((continuous_const : Continuous (fun _ : M => x)).mul continuous_id))

def centerCompression {p : M} (hp : IsStarProjection p) :
    centerAlgebra (M:=M) →⋆ₐ[ℂ] algebra hp where
  toFun a := ⟨(a:M)*p,by
    constructor
    · rw [←mul_assoc,←(a.property p).eq,mul_assoc,hp.isIdempotentElem.eq]
    · rw [mul_assoc,hp.isIdempotentElem.eq]⟩
  map_one' := Subtype.ext (one_mul p)
  map_mul' a b := Subtype.ext (by
    change ((a:M)*(b:M))*p=((a:M)*p)*((b:M)*p)
    rw [mul_assoc (a:M) p,←mul_assoc p,←(b.property p).eq,mul_assoc (b:M),hp.isIdempotentElem.eq,mul_assoc])
  map_zero' := Subtype.ext (zero_mul p)
  map_add' a b := Subtype.ext (add_mul (a:M) (b:M) p)
  commutes' r := Subtype.ext (by change (algebraMap ℂ M r)*p=r • p; simp [Algebra.algebraMap_eq_smul_one])
  map_star' a := Subtype.ext (by
    change star (a:M)*p=star ((a:M)*p)
    rw [star_mul,hp.isSelfAdjoint.star_eq]
    exact (central_star a.property p).eq)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1
lemma centerCompression_injective {p : M} (hp : IsStarProjection p)
    {t : ℝ} (ht : 0<t) (hEp : average e τ hτ htr hfaith p=t • (1:M)) :
    Function.Injective (centerCompression hp) := by
  intro a b hab
  have hh := congrArg (average e τ hτ htr hfaith) (congrArg Subtype.val hab)
  change average e τ hτ htr hfaith ((a:M)*p)=average e τ hτ htr hfaith ((b:M)*p) at hh
  rw [average_bimodule e τ hτ htr hfaith h1 a.property,
    average_bimodule e τ hτ htr hfaith h1 b.property,hEp,mul_smul_comm,mul_smul_comm,mul_one,mul_one] at hh
  exact Subtype.ext ((smul_right_injective M ht.ne') hh)

lemma center_compression_norm {p : M} (hp : IsStarProjection p)
    {t : ℝ} (ht : 0<t) (hEp : average e τ hτ htr hfaith p=t • (1:M))
    {a : M} (ha : Central a) : ‖a*p‖=‖a‖ :=
  NonUnitalStarAlgHom.norm_map (centerCompression hp)
    (centerCompression_injective e τ hτ htr hfaith h1 hp ht hEp) ⟨a,ha⟩

lemma full_center_lift_norm (hII : PopaTypeII.NoAbelianCorners M) {p : M}
    (hp : IsStarProjection p) {t : ℝ} (ht : 0<t)
    (hEp : average e τ hτ htr hfaith p=t • (1:M))
    (x : algebra hp) (hx : Central x) :
    ∃ c : M, Central c ∧ c*p=(x:M) ∧ ‖c‖=‖x‖ := by
  obtain ⟨n,a,b,ha,hb,hs⟩ := full_corner_center e τ hτ htr hfaith h1 hII hp ht hEp
  obtain ⟨c,hc,hcp⟩ := full_center_lift hp a b ha hb hs x hx
  refine ⟨c,hc,hcp,?_⟩
  rw [←center_compression_norm e τ hτ htr hfaith h1 hp ht hEp hc,hcp]
  rfl
end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorner
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

def cornerAverage {p : M} (hp : IsStarProjection p) (a : algebra hp) : algebra hp :=
  average (predualEquiv e hp) (trace hp τ) (trace_normal hp τ e hτ)
    (trace_tracial hp τ htr) (trace_faithful hp τ hfaith) a

lemma cornerAverage_central {p : M} (hp : IsStarProjection p) (a : algebra hp) :
    Central (cornerAverage e τ hτ htr hfaith hp a) :=
  average_central _ _ _ _ _ _

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_corner {p : M} (hp : IsStarProjection p) {z : M} (hz : Central z) :
    Central (centerCompression hp ⟨z,hz⟩) := by
  intro x
  apply Subtype.ext
  change (z*p)*(x:M)=(x:M)*(z*p)
  calc
    (z*p)*(x:M)=z*(x:M) := by rw [mul_assoc,x.property.1]
    _=(x:M)*z := (hz (x:M)).eq
    _=(x:M)*(z*p) := by rw [(hz p).eq,←mul_assoc,x.property.2]

include h1 in
lemma average_cornerAverage {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (a : algebra hp) :
    average e τ hτ htr hfaith (cornerAverage e τ hτ htr hfaith hp a : M)=
      average e τ hτ htr hfaith (a:M) := by
  apply average_eq e τ hτ htr hfaith h1
  · exact average_central e τ hτ htr hfaith _
  · intro z hz
    rw [average_pair e τ hτ htr hfaith h1 hz]
    have hh := average_pair (predualEquiv e hp) (trace hp τ) (trace_normal hp τ e hτ)
      (trace_tracial hp τ htr) (trace_faithful hp τ hfaith) (trace_one hp τ hfaith hp0)
      (central_corner hp hz) a
    have hzmul (b : algebra hp) : ((centerCompression hp ⟨z,hz⟩*b : algebra hp):M)=z*(b:M) := by
      change (z*p)*(b:M)=z*(b:M)
      rw [mul_assoc,b.property.1]
    simp only [trace_apply,hzmul] at hh
    have ht : (((τ p).re⁻¹:ℝ):ℂ) ≠ 0 := by
      exact_mod_cast inv_ne_zero (HochschildDiffuse.projection_trace_pos τ hfaith hp hp0).ne'
    exact (mul_left_cancel₀ ht hh).symm

include h1 in
lemma cornerAverage_lift (hII : PopaTypeII.NoAbelianCorners M) {p : M}
    (hp : IsStarProjection p) (hp0 : p ≠ 0) {t : ℝ} (ht : 0<t)
    (hEp : average e τ hτ htr hfaith p=t • (1:M)) (a : algebra hp) :
    ∃ c : M, Central c ∧ c*p=(cornerAverage e τ hτ htr hfaith hp a:M) ∧
      ‖c‖≤‖a‖ ∧ average e τ hτ htr hfaith (a:M)=t • c := by
  obtain ⟨c,hc,hcp,hcn⟩ := full_center_lift_norm e τ hτ htr hfaith h1 hII hp ht hEp
    (cornerAverage e τ hτ htr hfaith hp a) (cornerAverage_central e τ hτ htr hfaith hp a)
  refine ⟨c,hc,hcp,?_,?_⟩
  · rw [hcn]
    exact average_norm _ _ _ _ _ a
  · rw [←average_cornerAverage e τ hτ htr hfaith h1 hp hp0 a,←hcp,
      average_bimodule e τ hτ htr hfaith h1 hc,hEp,mul_smul_comm,mul_one]

include h1 in
lemma average_corner_rank {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (q : algebra hp) {r : ℝ} (hq : cornerAverage e τ hτ htr hfaith hp q=r • (1:algebra hp)) :
    average e τ hτ htr hfaith (q:M)=r • average e τ hτ htr hfaith p := by
  rw [←average_cornerAverage e τ hτ htr hfaith h1 hp hp0 q,hq]
  change expectation e τ hτ htr hfaith h1 (r • p)=r • expectation e τ hτ htr hfaith h1 p
  exact (expectation e τ hτ htr hfaith h1).map_smul_of_tower r p

end PopaCenter

end

end OAI
