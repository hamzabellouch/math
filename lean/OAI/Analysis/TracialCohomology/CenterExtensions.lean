import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.MatrixExtensions

namespace OAI

/-! Center extensions for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
variable {n : ℕ} (s : PopaMatrices.System n (1:M))
variable (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

lemma closedCommutant_typeII (hn : 0 < n) (hII : NoAbelianCorners M) :
    NoAbelianCorners (closedCommutant e s P hP) := by
  intro p hp hp0
  let Q := closedCommutant e s P hP
  let i : Fin n := ⟨0,hn⟩
  have hpM : IsStarProjection (p:M) := hp.map Q.subtype
  have hpQ := closedCommutant_subset e s P hP p.property
  let a : M := s.entry i i*(p:M)
  have ha : IsStarProjection a := (s.diagonal_projection i).mul hpM (hpQ i i).symm
  have hac : s.coordinate a i i=(p:M) := s.coordinate_of_commutes (p:M) hpQ i
  have ha0 : a ≠ 0 := by
    intro h
    exact hp0 (Subtype.ext (by change (p:M)=0; simpa only [h,s.coordinate_zero] using hac.symm))
  obtain ⟨x,y,hxy⟩ := hII a ha ha0
  have hai : a ≤ s.entry i i := (ha.le_iff_mul_eq_right (s.diagonal_projection i)).mpr (by
    dsimp [a]; rw [←mul_assoc,(s.diagonal_projection i).isIdempotentElem.eq])
  have aL := (ha.le_iff_mul_eq_right (s.diagonal_projection i)).mp hai
  have aR := (ha.le_iff_mul_eq_left (s.diagonal_projection i)).mp hai
  have xiR (z : PopaCorner.algebra ha) : (z:M)*s.entry i i=(z:M) := by
    calc _=((z:M)*a)*s.entry i i := by rw [z.property.2]
         _=(z:M)*(a*s.entry i i) := mul_assoc _ _ _
         _=(z:M) := by rw [aR,z.property.2]
  have xiL (z : PopaCorner.algebra ha) : s.entry i i*(z:M)=(z:M) := by
    calc _=s.entry i i*(a*(z:M)) := by rw [z.property.1]
         _=(s.entry i i*a)*(z:M) := (mul_assoc _ _ _).symm
         _=(z:M) := by rw [aL,z.property.1]
  let lift (z : PopaCorner.algebra ha) : Q :=
    ⟨s.coordinate (z:M) i i,mem_closedCommutant e s P hP (s.coordinate_mem _ i i)⟩
  have hLp (z : PopaCorner.algebra ha) : p*lift z=lift z := by
    apply Subtype.ext
    change (p:M)*s.coordinate (z:M) i i=s.coordinate (z:M) i i
    rw [←hac,←s.coordinate_mul i aR,z.property.1]
  have hRp (z : PopaCorner.algebra ha) : lift z*p=lift z := by
    apply Subtype.ext
    change s.coordinate (z:M) i i*(p:M)=s.coordinate (z:M) i i
    rw [←hac,←s.coordinate_mul i (xiR z),z.property.2]
  let L (z : PopaCorner.algebra ha) : PopaCorner.algebra hp := ⟨lift z,hLp z,hRp z⟩
  refine ⟨L x,L y,?_⟩
  intro hcomm
  apply hxy
  apply Subtype.ext
  change (x:M)*(y:M)=(y:M)*(x:M)
  have hh := congrArg (fun z : PopaCorner.algebra hp => ((z:Q):M)) hcomm.eq
  change s.coordinate (x:M) i i*s.coordinate (y:M) i i=
    s.coordinate (y:M) i i*s.coordinate (x:M) i i at hh
  rw [←s.coordinate_mul i (xiR x),←s.coordinate_mul i (xiR y)] at hh
  have hxyL : s.entry i i*((x:M)*(y:M))=(x:M)*(y:M) := by rw [←mul_assoc,xiL x]
  have hxyR : ((x:M)*(y:M))*s.entry i i=(x:M)*(y:M) := by rw [mul_assoc,xiR y]
  have hyxL : s.entry i i*((y:M)*(x:M))=(y:M)*(x:M) := by rw [←mul_assoc,xiL y]
  have hyxR : ((y:M)*(x:M))*s.entry i i=(y:M)*(x:M) := by rw [mul_assoc,xiR x]
  simpa only [s.extract_coordinate i hxyL hxyR,s.extract_coordinate i hyxL hyxR]
    using congrArg (fun z => s.entry i i*z) hh

end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorners PopaCorners.CornerIso PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include e hτ htr hfaith h1 in
lemma conjugate_of_average_eq {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (he : average e τ hτ htr hfaith p=average e τ hτ htr hfaith q) :
    ∃ u : unitary M, (u:M)*p*star (u:M)=q := by
  obtain ⟨v,hvp,hvq,hvr,hvl⟩ := equivalent_of_average_eq e τ hτ htr hfaith h1 hp hq he
  have hec : average e τ hτ htr hfaith (1-p)=average e τ hτ htr hfaith (1-q) := by
    change expectation e τ hτ htr hfaith h1 (1-p)=expectation e τ hτ htr hfaith h1 (1-q)
    simp only [map_sub,expectation_apply,he]
  obtain ⟨b,hbp,hbq,hbr,hbl⟩ := equivalent_of_average_eq e τ hτ htr hfaith h1 hp.one_sub hq.one_sub hec
  let vi : CornerIso (1:M) 1 := ⟨v,by rw [hvp]; exact hp,by rw [hvp]; exact hvr,
    by rw [hvp]; exact hp.le_one,by rw [hvq]; exact hq.le_one⟩
  let bi : CornerIso (1-vi.initial) (1-vi.final) := ⟨b,by rw [hbp]; exact hp.one_sub,
    by rw [hbp]; exact hbr,by change star b*b ≤ 1-(star v*v); rw [hbp,hvp],
    by change b*star b ≤ 1-(v*star v); rw [hbq,hvq]⟩
  obtain ⟨w,hw,hvw⟩ := add_orthogonal (IsStarProjection.one M) (IsStarProjection.one M) vi bi
  have hcross : star v*b=0 := by
    have hsv : star v*q=star v := by
      simpa only [star_mul,hq.isSelfAdjoint.star_eq] using congrArg star hvl
    calc
      star v*b=(star v*q)*((1-q)*b) := by rw [hsv,hbl]
      _=star v*(q*(1-q))*b := by simp only [mul_assoc]
      _=0 := by rw [mul_sub,mul_one,hq.isIdempotentElem.eq,sub_self,mul_zero,zero_mul]
  have hcross' : star b*v=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hcross
  have hwi : w.initial=1 := by
    change star (w:M)*(w:M)=1
    rw [hw]
    change star (v+b)*(v+b)=1
    simp only [star_add,add_mul,mul_add,hcross,hcross',hvp,hbp,add_zero,zero_add]
    abel
  have hwf : w.final=1 := by
    apply le_antisymm w.final_le
    apply HochschildDiffuse.projection_le_of_comparable_trace_le τ hfaith
      (IsStarProjection.one M) w.final_proj (Or.inr w.final_le)
    have ht : τ w.final=τ w.initial := htr (w:M) (star (w:M))
    rw [hwi] at ht
    exact le_of_eq (congrArg Complex.re ht.symm)
  let u : unitary M := ⟨(w:M),⟨hwi,hwf⟩⟩
  have hu : (u:M)*p=v := by simpa only [vi,initial,hvp] using hvw.2
  refine ⟨u,?_⟩
  calc
    (u:M)*p*star (u:M)=((u:M)*p)*star ((u:M)*p) := by
      simp only [star_mul,hp.isSelfAdjoint.star_eq,mul_assoc,←mul_assoc p p,hp.isIdempotentElem.eq]
    _ = q := by rw [hu,hvq]

namespace System
variable {n : ℕ} (s : PopaMatrices.System n (1:M))

def conjugated (u : unitary M) : PopaMatrices.System n (1:M) where
  entry i j := Unitary.conjStarAlgAut ℂ M u (s.entry i j)
  star_entry i j := by rw [←map_star,s.star_entry]
  mul_entry i j k l := by
    rw [←map_mul,s.mul_entry]
    split_ifs <;> simp only [map_zero]
  sum_diag := by rw [←map_sum,s.sum_diag,map_one]
lemma conjugated_expect (u : unitary M) (x : M) :
    (conjugated s u).expect x=Unitary.conjStarAlgAut ℂ M u
      (s.expect ((Unitary.conjStarAlgAut ℂ M u).symm x)) := by
  have hs (r : ℝ) (a : M) : Unitary.conjStarAlgAut ℂ M u (r • a)=
      r • Unitary.conjStarAlgAut ℂ M u a := by
    simp only [Unitary.conjStarAlgAut_apply,mul_smul_comm,smul_mul_assoc]
  simp only [PopaMatrices.System.expect,PopaMatrices.System.sumExpect,hs,map_sum,map_mul,
    StarAlgEquiv.apply_symm_apply,conjugated]

lemma conjugated_commutes (u : unitary M) (q : M)
    (hq : ∀ x : M, Commute (s.expect x) q) (x : M) :
    Commute ((conjugated s u).expect x) (Unitary.conjStarAlgAut ℂ M u q) := by
  rw [conjugated_expect]
  exact (hq _).map (Unitary.conjStarAlgAut ℂ M u)
end System
end PopaCenter

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaMatrices PopaTypeII PopaCorners PopaCorners.CornerIso
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include e hτ htr hfaith h1 in

theorem exists_matrix_approximating_projection_center (hII : NoAbelianCorners M)
    {p : M} (hp : IsStarProjection p) (η : ℝ) (hη : 0 < η) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : PopaMatrices.System n (1:M), ∃ q : M,
      IsStarProjection q ∧ q ≤ p ∧ ‖τ.toPreGNS (p-q)‖^2 < η ∧
      ∀ x : M, Commute (s.expect x) q := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  obtain ⟨k,hk⟩ := ((tendsto_order.mp ht).2 η hη).exists
  have hkp : 0 < (2:ℝ)^k := pow_pos (by norm_num) _
  have hki : ((2:ℝ)^k)⁻¹ < η := by simpa only [one_div,inv_pow] using hk
  have hn : 0 < 2^k := pow_pos (by omega) _
  obtain ⟨s⟩ := exists_dyadic_system e τ hτ htr hfaith h1 hII k
  have hap := average_nonneg e τ hτ htr hfaith hp.nonneg
  have hap1 : average e τ hτ htr hfaith p ≤ 1 := by
    simpa only [average_id e τ hτ htr hfaith h1 (fun x => Commute.one_left x)] using
      average_mono e τ hτ htr hfaith h1 hp.le_one
  obtain ⟨z,hz,hzc,hz0,hz1⟩ := central_dyadic_digits e k (average e τ hτ htr hfaith p)
    hap hap1 (average_central e τ hτ htr hfaith p)
  let a := diagonal s z
  have ha := diagonal_projection s z hz hzc
  have hea : (2:ℝ)^k • average e τ hτ htr hfaith a=∑ i, z i := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using average_diagonal_sum e τ hτ htr hfaith h1 s z hzc
  have herr : (2:ℝ)^k • (average e τ hτ htr hfaith p-average e τ hτ htr hfaith a)=
      (2:ℝ)^k • average e τ hτ htr hfaith p-∑ i, z i := by rw [smul_sub,hea]
  have hao : average e τ hτ htr hfaith a ≤ average e τ hτ htr hfaith p := by
    apply sub_nonneg.mp
    have hh := smul_nonneg (inv_pos.mpr hkp).le hz0
    rwa [←herr,smul_smul,inv_mul_cancel₀ hkp.ne',one_smul] at hh
  have herror : average e τ hτ htr hfaith p-average e τ hτ htr hfaith a ≤
      ((2:ℝ)^k)⁻¹ • (1:M) := by
    have hh := smul_le_smul_of_nonneg_left hz1 (inv_pos.mpr hkp).le
    rwa [←herr,smul_smul,inv_mul_cancel₀ hkp.ne',one_smul] at hh
  obtain ⟨v,hva⟩ := exists_full_initial_of_average_le e τ hτ htr hfaith h1 ha hp hao
  have hev : average e τ hτ htr hfaith a=average e τ hτ htr hfaith v.final := by
    calc
      _=average e τ hτ htr hfaith v.initial := congrArg (average e τ hτ htr hfaith) hva.symm
      _=_ := average_trace e τ hτ htr hfaith h1 (star (v:M)) (v:M)
  obtain ⟨u,hu⟩ := conjugate_of_average_eq e τ hτ htr hfaith h1 ha v.final_proj hev
  refine ⟨2^k,hn,System.conjugated s u,v.final,v.final_proj,v.final_le,?_,?_⟩
  · rw [projection_norm_sq τ ((v.final_proj.le_iff_sub hp).mp v.final_le),map_sub,Complex.sub_re]
    have hh : (τ (average e τ hτ htr hfaith p-average e τ hτ htr hfaith a)).re ≤
        (τ (((2:ℝ)^k)⁻¹ • (1:M))).re := Complex.re_le_re (τ.monotone herror)
    rw [map_sub,trace_average e τ hτ htr hfaith h1,
      trace_average e τ hτ htr hfaith h1,τ.map_smul_of_tower,h1] at hh
    have heτ : τ a=τ v.final := by
      rw [←trace_average e τ hτ htr hfaith h1 a,hev,trace_average e τ hτ htr hfaith h1]
    simp only [Complex.sub_re,Complex.real_smul,Complex.ofReal_re,mul_one] at hh
    rw [heτ] at hh
    exact hh.trans_lt hki
  · intro x
    have hh := System.conjugated_commutes s u a
      (fun x => diagonal_commutes s z hzc (s.expect x) (s.expect_mem x)) x
    simpa only [Unitary.conjStarAlgAut_apply,a,hu] using hh
end PopaCenter

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDixmier PopaQuantization PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
include e in
lemma center_distance_le_projection_commutators (h1 : τ 1=1)
    (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (b : M) (δ : ℝ) (hδ : 0 ≤ δ)
    (hp : ∀ p : M, IsStarProjection p → ‖τ.toPreGNS (p*b-b*p)‖ ≤ δ) :
    ‖τ.toPreGNS (b-average e τ hτ htr hfaith b)‖ ≤ 4*δ := by
  have : Nontrivial M := nontrivial_of_ne (1:M) 0 (by
    intro hz
    have hh := congrArg τ hz
    exact one_ne_zero (by simpa only [h1,map_zero] using hh))
  have hu (u : unitary M) : ‖τ.toPreGNS (conjugate u b-b)‖ ≤ 4*δ := by
    have hh := bound_of_projection_bound e (commutatorMap τ h1 b) δ hδ
      (fun p hp0 => by simpa only [commutatorMap_apply] using hp p hp0) (u:M)
    have he : conjugate u b-b=((u:M)*b-b*(u:M))*star (u:M) := by
      rw [sub_mul,mul_assoc b,Unitary.mul_star_self_of_mem u.property,mul_one]
      rfl
    rw [he]
    change ‖τ.toPreGNS (((u:M)*b-b*(u:M))*(star u : unitary M))‖ ≤ _
    rw [preGNS_norm_unitary_right τ htr]
    simpa only [CStarRing.norm_coe_unitary,mul_one,commutatorMap_apply] using hh
  have hsub : gnsVector τ '' convexHull ℝ (Set.range (fun u : unitary M => conjugate u b)) ⊆
      Metric.closedBall (gnsVector τ b) (4*δ) := by
    rw [(gnsVector τ).image_convexHull]
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨c,⟨u,rfl⟩,rfl⟩
    simpa only [Metric.mem_closedBall,dist_eq_norm,← map_sub,gnsVector_norm] using hu u
  have hc := average_orbit e τ hτ htr hfaith b
  have hh := closure_minimal hsub Metric.isClosed_closedBall hc
  have hh' : ‖τ.toPreGNS (average e τ hτ htr hfaith b-b)‖ ≤ 4*δ := by
    simpa only [Metric.mem_closedBall,dist_eq_norm,← map_sub,gnsVector_norm] using hh
  simpa only [map_sub,norm_sub_rev] using hh'

include e in

theorem exists_large_projection_commutator_center (h1 : τ 1=1)
    (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (b : M) (hbτ : average e τ hτ htr hfaith b=0) (hb : 0 < ‖τ.toPreGNS b‖) :
    ∃ p : M, IsStarProjection p ∧ ‖τ.toPreGNS b‖/8 < ‖τ.toPreGNS (p*b-b*p)‖ := by
  by_contra h
  push Not at h
  have hh := center_distance_le_projection_commutators e τ h1 hτ htr hfaith b
    (‖τ.toPreGNS b‖/8) (by positivity) h
  simp only [hbτ,sub_zero] at hh
  linarith

variable (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
include e hτ htr hfaith h1 in

theorem exists_matrix_energy_decrease_center (hII : NoAbelianCorners M)
    (b : M) (hbτ : average e τ hτ htr hfaith b=0) (hb : 0 < ‖τ.toPreGNS b‖) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : System n (1:M),
      ‖τ.toPreGNS (s.expect b)‖^2 < (1-1/1024:ℝ)*‖τ.toPreGNS b‖^2 := by
  obtain ⟨p,hp,hcomm⟩ := exists_large_projection_commutator_center e τ h1 hτ htr hfaith b hbτ hb
  let ε : ℝ := ‖τ.toPreGNS b‖/(32*(‖b‖+1))
  have hε : 0 < ε := div_pos hb (by positivity)
  obtain ⟨n,hn,s,q,hq,_hqp,happrox,hcq⟩ := exists_matrix_approximating_projection_center
    e τ hτ htr hfaith h1 hII hp (ε^2) (sq_pos_of_pos hε)
  have hap : ‖τ.toPreGNS (p-q)‖ < ε := by nlinarith [norm_nonneg (τ.toPreGNS (p-q))]
  have hεeq : 32*(‖b‖+1)*ε=‖τ.toPreGNS b‖ := by
    dsimp [ε]; field_simp
  have hsmall : 2*‖b‖*‖τ.toPreGNS (p-q)‖ < ‖τ.toPreGNS b‖/16 := by
    nlinarith [mul_nonneg (norm_nonneg b) (le_of_lt (sub_pos.mpr hap))]
  have hcb := commutator_difference_bound τ htr b p q
  have hlarge : ‖τ.toPreGNS b‖/16 < ‖τ.toPreGNS (b*q-q*b)‖ := by
    rw [map_sub,norm_sub_rev,← map_sub]
    linarith
  have he := s.energy_drop τ htr hn b q hq (hcq b)
  refine ⟨n,hn,s,?_⟩
  nlinarith [sq_nonneg (‖τ.toPreGNS (b*q-q*b)‖-‖τ.toPreGNS b‖/16)]
end PopaCenter

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
lemma average_expect {n : ℕ} (s : PopaMatrices.System n (1:M)) (hn : 0 < n) (a : M) :
    average e τ hτ htr hfaith (s.expect a)=average e τ hτ htr hfaith a := by
  apply average_eq e τ hτ htr hfaith h1
  · exact average_central e τ hτ htr hfaith a
  · intro z hz
    rw [average_pair e τ hτ htr hfaith h1 hz]
    have he : s.expect (z*a)=z*s.expect a := by
      simpa only [mul_one] using s.expect_bimodule z 1 a
        (fun i j => hz (s.entry i j)) s.commutant.one_mem
    rw [←he,s.trace_expect hn τ htr]

include e hτ htr hfaith h1 in
lemma extend_energy_decrease_center (hII : NoAbelianCorners M)
    {n : ℕ} (s : PopaMatrices.System n (1:M)) (hn : 0 < n) (a : M)
    (haE : average e τ hτ htr hfaith a=0) (ha : 0<‖τ.toPreGNS (s.expect a)‖) :
    ∃ m : ℕ, 0 < m ∧ ∃ t : PopaMatrices.System m (1:M),
      (∀ x : M, ‖τ.toPreGNS (t.expect x)‖ ≤ ‖τ.toPreGNS (s.expect x)‖) ∧
      ‖τ.toPreGNS (t.expect a)‖^2 < (1-1/1024:ℝ)*‖τ.toPreGNS (s.expect a)‖^2 := by
  obtain ⟨P,_hPn,hP⟩ := HochschildSakai.exists_abstract_star_preadjoint e
  let hL := (HochschildSakai.abstract_multiplication_normal e).1
  let hR := (HochschildSakai.abstract_multiplication_normal e).2
  let Q := closedCommutant e s P hP
  let eQ : StrongDual ℂ (X ⧸ WeakSubspace.preannihilator
      (WeakAlgebra.linearClosure e s.commutant)) ≃ₗᵢ⋆[ℂ] Q := WeakAlgebra.predualEquiv e s.commutant hL hR P hP
  let τQ : Q →ₚ[ℂ] ℂ := WeakAlgebra.inheritedTrace e τ s.commutant hL hR P hP
  let b : Q := ⟨s.expect a,mem_closedCommutant e s P hP (s.expect_mem a)⟩
  let htQ := WeakAlgebra.inheritedTrace_normal e τ s.commutant hL hR P hP hτ
  let htrQ := WeakAlgebra.inheritedTrace_tracial e τ s.commutant hL hR P hP htr
  let hfQ := WeakAlgebra.inheritedTrace_faithful e τ s.commutant hL hR P hP hfaith
  let h1Q := WeakAlgebra.inheritedTrace_one e τ s.commutant hL hR P hP h1
  have hcen (z : Q) (hz : Central z) : Central (z:M) :=
    s.central_in_commutant_is_central (z:M) (closedCommutant_subset e s P hP z.property)
      (fun x hx => congrArg Subtype.val (hz ⟨x,mem_closedCommutant e s P hP hx⟩).eq)
  have hbE : average eQ τQ htQ htrQ hfQ b=0 := by
    apply average_eq eQ τQ htQ htrQ hfQ h1Q
    · exact fun x => Commute.zero_left x
    · intro z hz
      change τ ( (z:M)*0)=τ ((z:M)*s.expect a)
      rw [←average_pair e τ hτ htr hfaith h1 (hcen z hz) (s.expect a),
        average_expect e τ hτ htr hfaith h1 s hn,haE]
  have hnorm (x : Q) : ‖τQ.toPreGNS x‖=‖τ.toPreGNS (x:M)‖ :=
    preGNS_norm_eq_of_trace τ τQ Q.subtype (fun _ => rfl) x
  have hb : 0 < ‖τQ.toPreGNS b‖ := by rw [hnorm]; exact ha
  obtain ⟨k,hk,r,hr⟩ := exists_matrix_energy_decrease_center eQ τQ htQ htrQ hfQ h1Q
    (closedCommutant_typeII e s P hP hn hII) b hbE hb
  let rM := r.map Q.subtype
  have hc : ∀ i j a b, Commute (rM.entry i j) (s.entry a b) := by
    intro i j a b
    exact closedCommutant_subset e s P hP (r.entry i j).property a b
  let t := rM.tensor s hc
  refine ⟨k*n,Nat.mul_pos hk hn,t,?_,?_⟩
  · intro x
    rw [show t.expect x=rM.expect (s.expect x) from rM.tensor_expect s hc x]
    exact rM.expect_norm_le τ htr hk _
  · simp only [hnorm] at hr
    rw [show t.expect a=rM.expect (s.expect a) from rM.tensor_expect s hc a]
    change ‖τ.toPreGNS ((r.map Q.subtype).expect (Q.subtype b))‖^2 <
      (1-1/1024:ℝ)*‖τ.toPreGNS (Q.subtype b)‖^2
    rw [r.map_expect]
    exact hr
end PopaCenter

end

end OAI
