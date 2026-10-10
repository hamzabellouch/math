import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.CornerTraces
import OAI.Analysis.TracialCohomology.CenterQuantization

namespace OAI

/-! Local quantization for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

include e hτ htr hfaith h1 hfactor in

theorem exists_large_refinement (hdiff : NoMinimalProjections M)
    {n : ℕ} (s : System n (1:M)) (hn : 0 < n) (N : ℕ) :
    ∃ m : ℕ, N < m ∧ ∃ t : System m (1:M),
      ∀ x : M, ‖τ.toPreGNS (t.expect x)‖ ≤ ‖τ.toPreGNS (s.expect x)‖ := by
  obtain ⟨P,_hPn,hP⟩ := HochschildSakai.exists_abstract_star_preadjoint e
  let hL := (HochschildSakai.abstract_multiplication_normal e).1
  let hR := (HochschildSakai.abstract_multiplication_normal e).2
  let Q := closedCommutant e s P hP
  let eQ : StrongDual ℂ (X ⧸ WeakSubspace.preannihilator
      (WeakAlgebra.linearClosure e s.commutant)) ≃ₗᵢ⋆[ℂ] Q := WeakAlgebra.predualEquiv e s.commutant hL hR P hP
  let τQ : Q →ₚ[ℂ] ℂ := WeakAlgebra.inheritedTrace e τ s.commutant hL hR P hP
  obtain ⟨r⟩ := exists_system eQ τQ
    (WeakAlgebra.inheritedTrace_normal e τ s.commutant hL hR P hP hτ)
    (WeakAlgebra.inheritedTrace_tracial e τ s.commutant hL hR P hP htr)
    (WeakAlgebra.inheritedTrace_faithful e τ s.commutant hL hR P hP hfaith)
    (WeakAlgebra.inheritedTrace_one e τ s.commutant hL hR P hP h1)
    (closedCommutant_factor e s P hP hfactor)
    (closedCommutant_diffuse e s P hP hn hdiff) (N+1) (by omega) (p:=1) (IsStarProjection.one _)
  let rM := r.map Q.subtype
  have hc : ∀ i j a b, Commute (rM.entry i j) (s.entry a b) := by
    intro i j a b
    exact closedCommutant_subset e s P hP (r.entry i j).property a b
  let t := rM.tensor s hc
  refine ⟨(N+1)*n,by nlinarith,t,?_⟩
  intro x
  rw [show t.expect x=rM.expect (s.expect x) from rM.tensor_expect s hc x]
  exact rM.expect_norm_le τ htr (by omega) _

include e hτ htr hfaith h1 hfactor in
lemma exists_large_small_expectation (hdiff : NoMinimalProjections M)
    {r : ℕ} (F : Fin r → M) (hF : ∀ i, τ (F i)=0) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ ∃ s : System n (1:M), energy τ F s < ε := by
  obtain ⟨n,hn,s,hs⟩ := exists_small_expectation e τ hτ htr hfaith h1 hfactor hdiff F hF ε hε
  obtain ⟨m,hm,t,ht⟩ := exists_large_refinement e τ hτ htr hfaith h1 hfactor hdiff s hn N
  refine ⟨m,hm,t,(Finset.sum_le_sum (fun i _ => ?_)).trans_lt hs⟩
  exact pow_le_pow_left₀ (norm_nonneg _) (ht (F i)) 2
end PopaMatrices

open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

include e hτ htr hfaith h1 hfactor in

theorem local_quantization_centered (hdiff : NoMinimalProjections M)
    {r : ℕ} (F : Fin r → M) (hF : ∀ i, τ (F i)=0)
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ q : M, IsStarProjection q ∧ q ≠ 0 ∧ (τ q).re < δ ∧
      (∑ i, ‖τ.toPreGNS (q*F i*q)‖^2) < η*(τ q).re := by
  let C : ℝ := ∑ j, ‖τ.toPreGNS (F j)‖^2
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  obtain ⟨N,hN⟩ := exists_nat_gt (max (4*C/η) (1/δ))
  obtain ⟨n,hn,s,hs⟩ := exists_large_small_expectation e τ hτ htr hfaith h1 hfactor
    hdiff F hF (η/2) (by positivity) N
  have hnpos : 0<n := Nat.zero_lt_of_lt hn
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr hnpos
  have hb : 4*C/η < (n:ℝ) := (lt_of_le_of_lt (le_max_left _ _) hN).trans (Nat.cast_lt.mpr hn)
  have hd : 1/δ < (n:ℝ) := (lt_of_le_of_lt (le_max_right _ _) hN).trans (Nat.cast_lt.mpr hn)
  obtain ⟨a,ha⟩ := s.exists_flat_projection τ htr ⟨0,hnpos⟩ F
  let q := s.flatProjection ⟨0,hnpos⟩ a
  have hq : IsStarProjection q := s.flatProjection_projection _ _
  have ht : (τ q).re=(n:ℝ)⁻¹ := by
    rw [show τ q=(n:ℂ)⁻¹ from s.flatProjection_trace τ htr h1 _ _]
    rw [←Complex.ofReal_natCast,←Complex.ofReal_inv,Complex.ofReal_re]
  have htpos : 0 < (τ q).re := by rw [ht]; positivity
  refine ⟨q,hq,fun h => by simp only [h,map_zero,Complex.zero_re,lt_self_iff_false] at htpos,?_,?_⟩
  · rw [ht]
    rw [inv_eq_one_div]
    exact (div_lt_iff₀ hnR).mpr (by
      have hh := (div_lt_iff₀ hδ).mp hd
      nlinarith)
  · have hterm : (2/(n:ℝ))*C < η/2 := by
      have hh := (div_lt_iff₀ hη).mp hb
      apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
      have hn0 := hnR.ne'
      field_simp
      nlinarith
    have hh : (n:ℝ)*(∑ i, ‖τ.toPreGNS (q*F i*q)‖^2) < η := by
      rw [Finset.mul_sum]
      exact ha.trans_lt (by change energy τ F s+2/(n:ℝ)*C<η; linarith)
    rw [ht,←div_eq_mul_inv]
    exact (lt_div_iff₀ hnR).mpr (by nlinarith)
end PopaMatrices

open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

lemma norm_sq_trace_corner {p : M} (hp : IsStarProjection p) (a : algebra hp) :
    ‖(trace hp τ).toPreGNS a‖^2=(τ p).re⁻¹*‖τ.toPreGNS (a:M)‖^2 := by
  rw [PopaMatrices.System.norm_sq_eq_trace,PopaMatrices.System.norm_sq_eq_trace,trace_apply]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rfl

include e hτ htr hfaith h1 hfactor in

theorem local_quantization (hdiff : NoMinimalProjections M)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    {r : ℕ} (F : Fin r → M) (η δ : ℝ) (hη : 0<η) (hδ : 0<δ) :
    ∃ q : M, IsStarProjection q ∧ q ≠ 0 ∧ q ≤ p ∧ (τ q).re < δ*(τ p).re ∧
      (∑ i, ‖τ.toPreGNS (q*F i*q-(trace hp τ (compress hp (F i))) • q)‖^2) < η*(τ q).re := by
  let t := trace hp τ
  let G : Fin r → algebra hp := fun i => compress hp (F i)-t (compress hp (F i)) • 1
  have ht1 : t 1=1 := trace_one hp τ hfaith hp0
  have hG (i : Fin r) : t (G i)=0 := by simp [G,map_sub,map_smul,ht1]
  obtain ⟨q,hq,hq0,hqt,hqe⟩ := PopaMatrices.local_quantization_centered
    (predualEquiv e hp) t (trace_normal hp τ e hτ) (trace_tracial hp τ htr)
    (trace_faithful hp τ hfaith) ht1
    (corner_factor e τ hτ htr hfaith h1 hfactor hdiff hp hp0)
    (corner_diffuse hp hdiff) G hG η δ hη hδ
  have ht : 0 < (τ p).re := projection_trace_pos τ hfaith hp hp0
  have hqM : IsStarProjection (q:M) := hq.map (incl hp)
  have hqp : (q:M) ≤ p := (hqM.le_iff_mul_eq_left hp).mpr q.property.2
  have he (i : Fin r) : ((q*G i*q : algebra hp):M)=
      (q:M)*F i*(q:M)-t (compress hp (F i)) • (q:M) := by
    change (q:M)*(p*F i*p-t (compress hp (F i)) • p)*(q:M)=_
    rw [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,←mul_assoc (q:M),
      ←mul_assoc (q:M),q.property.2,mul_assoc _ p,q.property.1,hqM.isIdempotentElem.eq]
  refine ⟨q.val,hqM,fun hh => hq0 (Subtype.ext hh),hqp,?_,?_⟩
  · have hh : (τ p).re⁻¹*(τ (q:M)).re < δ := by
      simpa only [t,trace_apply,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero] using hqt
    calc
      (τ (q:M)).re = ((τ p).re⁻¹*(τ (q:M)).re)*(τ p).re := by field_simp
      _ < δ*(τ p).re := mul_lt_mul_of_pos_right hh ht
  · have hh : (τ p).re⁻¹*(∑ i, ‖τ.toPreGNS ((q:M)*F i*(q:M)-t (compress hp (F i)) • (q:M))‖^2)
        < η*((τ p).re⁻¹*(τ (q:M)).re) := by
      simpa only [t,norm_sq_trace_corner,he,trace_apply,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero,←Finset.mul_sum] using hqe
    have hm := mul_lt_mul_of_pos_left hh ht
    simpa only [←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul,mul_one,mul_left_comm (τ p).re η] using hm
end PopaCorner

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorner
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

def cornerCoefficient {p : M} (_hp : IsStarProjection p) (a : M) : M :=
  (τ p).re⁻¹ • average e τ hτ htr hfaith (p*a*p)

lemma cornerCoefficient_central {p : M} (hp : IsStarProjection p) (a : M) :
    Central (cornerCoefficient e τ hτ htr hfaith hp a) := fun x =>
  (average_central e τ hτ htr hfaith _ x).smul_left _

include h1 in
lemma cornerCoefficient_spec (hII : PopaTypeII.NoAbelianCorners M) {p : M}
    (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (hEp : average e τ hτ htr hfaith p=(τ p).re • (1:M)) (a : M) :
    cornerCoefficient e τ hτ htr hfaith hp a*p=
        (cornerAverage e τ hτ htr hfaith hp (compress hp a):M) ∧
      ‖cornerCoefficient e τ hτ htr hfaith hp a‖≤‖a‖ := by
  have ht := HochschildDiffuse.projection_trace_pos τ hfaith hp hp0
  obtain ⟨c,hc,hcp,hcn,hce⟩ := cornerAverage_lift e τ hτ htr hfaith h1 hII hp hp0 ht hEp (compress hp a)
  have he : cornerCoefficient e τ hτ htr hfaith hp a=c := by
    change (τ p).re⁻¹ • average e τ hτ htr hfaith ((compress hp a):M)=c
    rw [hce,smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
  rw [he]
  exact ⟨hcp,hcn.trans (compress_norm_le hp a)⟩

include h1 in
theorem local_quantization_corner (hII : PopaTypeII.NoAbelianCorners M)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (hEp : average e τ hτ htr hfaith p=(τ p).re • (1:M))
    {r : ℕ} (F : Fin r → M) (η δ : ℝ) (hη : 0<η) (hδ : 0<δ) :
    ∃ q : M, IsStarProjection q ∧ q ≠ 0 ∧ q ≤ p ∧ (τ q).re < δ*(τ p).re ∧
      average e τ hτ htr hfaith q=(τ q).re • (1:M) ∧
      (∑ i, ‖τ.toPreGNS (q*F i*q-cornerCoefficient e τ hτ htr hfaith hp (F i)*q)‖^2) < η*(τ q).re := by
  let t := trace hp τ
  let ec := predualEquiv e hp
  let htc := trace_normal hp τ e hτ
  let httr := trace_tracial hp τ htr
  let htf := trace_faithful hp τ hfaith
  have ht1 : t 1=1 := trace_one hp τ hfaith hp0
  let G : Fin r → algebra hp := fun i => compress hp (F i)-cornerAverage e τ hτ htr hfaith hp (compress hp (F i))
  have hG (i : Fin r) : average ec t htc httr htf (G i)=0 := by
    change expectation ec t htc httr htf ht1 (_-_)=0
    rw [map_sub]
    change average ec t htc httr htf (compress hp (F i))-
      average ec t htc httr htf (average ec t htc httr htf (compress hp (F i)))=0
    rw [average_id ec t htc httr htf ht1 (average_central ec t htc httr htf _),sub_self]
  obtain ⟨q,hq,hq0,hqt,hqE,hqe⟩ := local_quantization_center_valued ec t htc httr htf ht1
    (corner_typeII hII hp) G hG η δ hη hδ
  have ht : 0 < (τ p).re := HochschildDiffuse.projection_trace_pos τ hfaith hp hp0
  have hqM : IsStarProjection (q:M) := hq.map (incl hp)
  have hqp : (q:M) ≤ p := (hqM.le_iff_mul_eq_left hp).mpr q.property.2
  have hqtval : (t q).re=(τ p).re⁻¹*(τ (q:M)).re := by
    simp only [t,trace_apply,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have he (i : Fin r) : ((q*G i*q : algebra hp):M)=
      (q:M)*F i*(q:M)-cornerCoefficient e τ hτ htr hfaith hp (F i)*(q:M) := by
    let c := cornerCoefficient e τ hτ htr hfaith hp (F i)
    have hc : Central c := cornerCoefficient_central e τ hτ htr hfaith hp (F i)
    have hcp := (cornerCoefficient_spec e τ hτ htr hfaith h1 hII hp hp0 hEp (F i)).1
    change (q:M)*(p*F i*p-(cornerAverage e τ hτ htr hfaith hp (compress hp (F i)):M))*(q:M)=_
    rw [←hcp,mul_sub,sub_mul,←mul_assoc (q:M),←mul_assoc (q:M),q.property.2,
      mul_assoc _ p,q.property.1]
    change _-(q:M)*(c*p)*(q:M)=_
    have hec : (q:M)*(c*p)*(q:M)=c*(q:M) := by
      rw [mul_assoc (q:M) (c*p), mul_assoc c p, q.property.1,
        ←mul_assoc, ←(hc (q:M)).eq, mul_assoc, hqM.isIdempotentElem.eq]
    rw [hec]
  refine ⟨q.val,hqM,fun hh => hq0 (Subtype.ext hh),hqp,?_,?_,?_⟩
  · rw [hqtval] at hqt
    calc
      (τ (q:M)).re = ((τ p).re⁻¹*(τ (q:M)).re)*(τ p).re := by field_simp
      _ < δ*(τ p).re := mul_lt_mul_of_pos_right hqt ht
  · have hh := average_corner_rank e τ hτ htr hfaith h1 hp hp0 q hqE
    rw [hEp,hqtval,smul_smul] at hh
    have hmul : ((τ p).re⁻¹*(τ (q:M)).re)*(τ p).re=(τ (q:M)).re := by field_simp
    simpa only [hmul] using hh
  · have hh : (τ p).re⁻¹*(∑ i, ‖τ.toPreGNS ((q:M)*F i*(q:M)-cornerCoefficient e τ hτ htr hfaith hp (F i)*(q:M))‖^2)
        < η*((τ p).re⁻¹*(τ (q:M)).re) := by
      simpa only [t,norm_sq_trace_corner,he,trace_apply,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero,←Finset.mul_sum] using hqe
    have hm := mul_lt_mul_of_pos_left hh ht
    simpa only [←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul,mul_one,mul_left_comm (τ p).re η] using hm
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

include h1 in
lemma central_supported_norm_sq {q : M} (hq : IsStarProjection q)
    {t : ℝ} (hEq : average e τ hτ htr hfaith q=t • (1:M)) {z : M} (hz : Central z) :
    ‖τ.toPreGNS (q*z)‖^2=t*‖τ.toPreGNS z‖^2 := by
  have he : star (q*z)*(q*z)=(star z*z)*q := by
    rw [star_mul,hq.isSelfAdjoint.star_eq,mul_assoc,←mul_assoc q,hq.isIdempotentElem.eq,
      ←(hz q).eq,←mul_assoc]
  rw [PopaMatrices.System.norm_sq_eq_trace,he,
    ←average_pair e τ hτ htr hfaith h1 (central_mul (central_star hz) hz),hEq,
    mul_smul_comm,mul_one,τ.map_smul_of_tower]
  rw [PopaMatrices.System.norm_sq_eq_trace]
  simp only [Complex.smul_re,smul_eq_mul]

include h1 in
lemma average_supported_norm_sq {q : M} (hq : IsStarProjection q)
    {t : ℝ} (ht : 0≤t) (hEq : average e τ hτ htr hfaith q=t • (1:M))
    {a : M} (ha : q*a=a) :
    ‖τ.toPreGNS (average e τ hτ htr hfaith a)‖^2 ≤ t*‖τ.toPreGNS a‖^2 := by
  let z := average e τ hτ htr hfaith a
  have hz : Central z := average_central e τ hτ htr hfaith a
  have hsq := central_supported_norm_sq e τ hτ htr hfaith h1 hq hEq hz
  have hi : inner ℂ (τ.toPreGNS (q*z)) (τ.toPreGNS a)=
      inner ℂ (τ.toPreGNS z) (τ.toPreGNS z) := by
    simp only [PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,star_mul,hq.isSelfAdjoint.star_eq,mul_assoc,ha]
    exact (average_pair e τ hτ htr hfaith h1 (central_star hz) a).symm
  have hcs := norm_inner_le_norm (𝕜:=ℂ) (τ.toPreGNS (q*z)) (τ.toPreGNS a)
  rw [hi,inner_self_eq_norm_sq_to_K] at hcs
  simp only [norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)] at hcs
  have hcs2 := mul_self_le_mul_self (sq_nonneg _) hcs
  have hnon : 0≤t*‖τ.toPreGNS a‖^2 := mul_nonneg ht (sq_nonneg _)
  change ‖τ.toPreGNS z‖^2 ≤ _
  by_cases hz0 : ‖τ.toPreGNS z‖=0
  · simpa only [hz0,zero_pow (by omega : (2:ℕ) ≠ 0)] using hnon
  · have hzpos : 0<‖τ.toPreGNS z‖^2 := sq_pos_of_ne_zero hz0
    apply le_of_mul_le_mul_left (a:=‖τ.toPreGNS z‖^2) ?_ hzpos
    calc
      _ ≤ ‖τ.toPreGNS (q*z)‖^2*‖τ.toPreGNS a‖^2 := by nlinarith [hcs2]
      _ = _ := by rw [hsq]; ring

include h1 in
lemma average_corner_error {q : M} (hq : IsStarProjection q) (hq0 : q ≠ 0)
    (hEq : average e τ hτ htr hfaith q=(τ q).re • (1:M))
    (a : algebra hq) {θ : ℝ} (hθ : 0≤θ)
    (ha : ‖(trace hq τ).toPreGNS a‖≤θ) :
    ‖τ.toPreGNS (average e τ hτ htr hfaith (a:M))‖≤(τ q).re*θ := by
  have ht := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  have hsq := average_supported_norm_sq e τ hτ htr hfaith h1 hq ht.le hEq a.property.1
  have hnorm := norm_sq_trace_corner τ hq a
  have ha2 := mul_self_le_mul_self (norm_nonneg _) ha
  have ht0 := ht.ne'
  have he : ‖τ.toPreGNS (a:M)‖^2=(τ q).re*‖(trace hq τ).toPreGNS a‖^2 := by
    rw [hnorm,←mul_assoc,mul_inv_cancel₀ ht0,one_mul]
  rw [he] at hsq
  have hh := mul_le_mul_of_nonneg_left ha2 (sq_nonneg (τ q).re)
  nlinarith [norm_nonneg (τ.toPreGNS (average e τ hτ htr hfaith (a:M))),mul_nonneg ht.le hθ]
end PopaCenter

end

end OAI
