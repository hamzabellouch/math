import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.CenterCorners

namespace OAI

/-! Relative central quantization and residual center bounds. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildCentralQuantization
open BoundedHochschild HochschildCorners FinitePathMain
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

def residualCenter {p : M} (hp : IsStarProjection p) (hp0 : p≠0) (a : M) : M :=
  (cornerExpectation e τ hτ htr hfaith hp hp0 ⟨p*a*p,compress_mem_corner hp a⟩ : M)

include e hτ htr hfaith in

theorem exists_relative_center_order_corner
    (hII : TypeII1 M) {p : M} (hp : IsStarProjection p) (hp0 : p≠0)
    {I : Type v} [Fintype I] (x : I → M) {δ η : ℝ} (hδ : 0<δ) (hη : 0<η) :
    ∃ q : M, IsStarProjection q ∧ q≤p ∧ q≠0 ∧ (τ q).re<η ∧
      (∑ i, centerExpectation e τ hτ htr hfaith
        (star (q*(x i-residualCenter e τ hτ htr hfaith hp hp0 (x i))*q)*
          (q*(x i-residualCenter e τ hτ htr hfaith hp hp0 (x i))*q))) ≤
        δ • centerExpectation e τ hτ htr hfaith q := by
  classical
  let ec := cornerPredualEquiv p hp e
  let tc := cornerTrace p hp τ
  have hn : TraceInPredual ec tc := cornerTrace_normal p hp e τ hτ
  have ht : ∀ a b : Corner p hp, tc (a*b)=tc (b*a) := cornerTrace_tracial p hp τ htr
  have hf : ∀ a : Corner p hp, tc (star a*a)=0 → a=0 := cornerTrace_faithful p hp τ hfaith hp0
  let y : I → Corner p hp := fun i => ⟨p*x i*p,compress_mem_corner hp (x i)⟩
  let z : I → Corner p hp := fun i => y i-centerExpectation ec tc hn ht hf (y i)
  have hz : ∀ i, CentrallyCentered tc (z i) := fun i => centered_sub_expectation ec tc hn ht hf (y i)
  have htp : 0<(τ p).re := HochschildDiffuse.projection_trace_pos τ hfaith hp hp0
  obtain ⟨q,hq,hq0,hqt,hqb⟩ := exists_small_corner_center_order ec tc hn ht hf
    (cornerTrace_one p hp τ hfaith hp0) (corner_typeII1 e τ hτ htr hfaith hp hp0 hII)
    z hz hδ (div_pos hη htp)
  have hqM : IsStarProjection (q:M) := corner_projection_coe p hp hq
  refine ⟨q,hqM,corner_projection_le p hp hq,fun hh => hq0 (Subtype.ext hh),?_,?_⟩
  · have hh : (τ p).re⁻¹*(τ (q:M)).re<η/(τ p).re := by
      simpa only [tc,cornerTrace_apply,← Complex.ofReal_inv,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hqt
    have hh' := mul_lt_mul_of_pos_left hh htp
    simpa only [← mul_assoc,mul_inv_cancel₀ htp.ne',one_mul,mul_div_cancel₀ _ htp.ne'] using hh'
  · let inc : Corner p hp →ₗ[ℂ] M := (corner p hp).subtype
    have hinc : Monotone inc := fun a b h => h
    have hh := centerExpectation_monotone e τ hτ htr hfaith (hinc hqb)
    have hcoe (i : I) : ((q*z i*q : Corner p hp):M)=
        (q:M)*(x i-residualCenter e τ hτ htr hfaith hp hp0 (x i))*(q:M) := by
      change (q:M)*(p*x i*p-residualCenter e τ hτ htr hfaith hp hp0 (x i))*(q:M)=_
      rw [mul_sub,sub_mul,mul_sub,sub_mul]
      congr 1
      rw [← mul_assoc,← mul_assoc,q.property.2,mul_assoc,q.property.1]
    change (centerExpectation e τ hτ htr hfaith)
      (inc (∑ i,cornerExpectation e τ hτ htr hfaith hp hp0 (star (q*z i*q)*(q*z i*q)))) ≤
        (centerExpectation e τ hτ htr hfaith) (inc (δ • cornerExpectation e τ hτ htr hfaith hp hp0 q)) at hh
    rw [← Complex.coe_smul,map_sum,map_smul,map_sum,map_smul] at hh
    have htower (a : Corner p hp) :
        centerExpectation e τ hτ htr hfaith (inc (cornerExpectation e τ hτ htr hfaith hp hp0 a))=
          centerExpectation e τ hτ htr hfaith (a:M) := centerExpectation_corner_tower e τ hτ htr hfaith hp hp0 a
    simp only [htower,Complex.coe_smul,corner_coe_mul,corner_coe_star,hcoe] at hh
    exact hh

end HochschildCentralQuantization

open scoped ComplexOrder
namespace HochschildCentralQuantization
open BoundedHochschild HochschildCorners FinitePathMain
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma residualCenter_of_center_mass_unit {p : M} (hp : IsStarProjection p) (hp0 : p≠0)
    (u : Mˣ) (hu : (u:M)=centerExpectation e τ hτ htr hfaith p) (a : M) :
    residualCenter e τ hτ htr hfaith hp hp0 a =
      p*((u⁻¹:Mˣ):M)*centerExpectation e τ hτ htr hfaith (p*a*p)*p := by
  let y : Corner p hp := ⟨p*a*p,compress_mem_corner hp a⟩
  let b := cornerExpectation e τ hτ htr hfaith hp hp0 y
  let z : M := ((u⁻¹:Mˣ):M)*centerExpectation e τ hτ htr hfaith (p*a*p)
  have huC (x : M) : Commute (u:M) x := by rw [hu]; exact centerPart_central e τ hτ htr hfaith p x
  have hz (x : M) : Commute z x := (huC x).units_inv_left.mul_left
    (centerPart_central e τ hτ htr hfaith (p*a*p) x)
  let c : Corner p hp := ⟨p*z*p,compress_mem_corner hp z⟩
  have hbC (x : M) : Commute (b:M) (p*x*p) := by
    exact congrArg (fun v : Corner p hp => (v:M))
      (centerPart_central (cornerPredualEquiv p hp e) (cornerTrace p hp τ)
        (cornerTrace_normal p hp e τ hτ) (cornerTrace_tracial p hp τ htr)
        (cornerTrace_faithful p hp τ hfaith hp0) y ⟨p*x*p,compress_mem_corner hp x⟩).eq
  have hcC (x : M) : Commute (c:M) (p*x*p) := by
    exact congrArg (fun v : Corner p hp => (v:M))
      (central_corner_weight hp hz ⟨p*x*p,compress_mem_corner hp x⟩).eq
  have hcE : centerExpectation e τ hτ htr hfaith (c:M)=
      centerExpectation e τ hτ htr hfaith (p*a*p) := by
    have he : p*z*p=z*p := by rw [← (hz p).eq,mul_assoc,hp.isIdempotentElem.eq]
    change centerExpectation e τ hτ htr hfaith (p*z*p)=_
    rw [he,centerExpectation_bimodule e τ hτ htr hfaith hz,← hu]
    change (((u⁻¹:Mˣ):M)*centerExpectation e τ hτ htr hfaith (p*a*p))*(u:M)=_
    have hcomm : Commute (centerExpectation e τ hτ htr hfaith (p*a*p)) (u:M) :=
      centerPart_central e τ hτ htr hfaith (p*a*p) (u:M)
    rw [mul_assoc,hcomm.eq,← mul_assoc]
    simp only [Units.inv_mul,one_mul]
  have heq : (b:M)=(c:M) := by
    apply sub_eq_zero.mp
    apply corner_centered_zero e τ hτ htr hfaith hp ((corner p hp).sub_mem b.property c.property)
      (fun x => (hbC x).sub_left (hcC x))
    apply (centerExpectation_zero_iff e τ hτ htr hfaith _).mp
    rw [map_sub,centerExpectation_corner_tower,hcE,sub_self]
  change (b:M)=_
  rw [heq]
  change p*(((u⁻¹:Mˣ):M)*centerExpectation e τ hτ htr hfaith (p*a*p))*p=_
  simp only [mul_assoc]

lemma residualCenter_norm_of_unit {p : M} (hp : IsStarProjection p) (hp0 : p≠0)
    (u : Mˣ) (hu : (u:M)=centerExpectation e τ hτ htr hfaith p) (a : M) :
    ‖residualCenter e τ hτ htr hfaith hp hp0 a‖ ≤
      ‖((u⁻¹:Mˣ):M)‖*‖centerExpectation e τ hτ htr hfaith (p*a*p)‖ := by
  rw [residualCenter_of_center_mass_unit e τ hτ htr hfaith hp hp0 u hu a]
  have hn := hp.norm_le p
  calc
    _ ≤ (‖p‖*‖((u⁻¹:Mˣ):M)‖*‖centerExpectation e τ hτ htr hfaith (p*a*p)‖)*‖p‖ := by
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
        (norm_nonneg _))
    _ ≤ (1*‖((u⁻¹:Mˣ):M)‖*‖centerExpectation e τ hτ htr hfaith (p*a*p)‖)*1 := by gcongr
    _ = _ := by ring

lemma exists_center_mass_unit {p : M} (hp : IsStarProjection p)
    {ε : ℝ} (hε : 0<ε)
    (hmass : ε • (1:M) ≤ centerExpectation e τ hτ htr hfaith p) :
    ∃ u : Mˣ, (u:M)=centerExpectation e τ hτ htr hfaith p ∧
      ‖((u⁻¹:Mˣ):M)‖≤ε⁻¹ := by
  let s : Mˣ := Units.map (algebraMap ℝ M).toMonoidHom (Units.mk0 ε hε.ne')
  have hs : (s:M)=ε • (1:M) := by
    simp only [s,Units.coe_map,Units.val_mk0,RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe,Algebra.algebraMap_eq_smul_one]
  have hspos : 0≤(s:M) := by rw [hs]; exact smul_nonneg hε.le zero_le_one
  have hunit : IsUnit (centerExpectation e τ hτ htr hfaith p) :=
    CStarAlgebra.isUnit_of_le (s:M) (hs ▸ hmass) ⟨hspos,s.isUnit⟩
  obtain ⟨u,hu⟩ := hunit
  refine ⟨u,hu,?_⟩
  have hu0 : 0≤(u:M) := by rw [hu]; exact centerExpectation_nonneg e τ hτ htr hfaith hp.nonneg
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (inv_nonneg.mpr hε.le)
    (CFC.inv_nonneg_of_nonneg u hu0)).mpr
  have hh : ((u⁻¹:Mˣ):M)≤((s⁻¹:Mˣ):M) :=
    CStarAlgebra.inv_le_inv hspos (by rw [hs,hu]; exact hmass)
  convert hh using 1
  simp only [s,Units.coe_map_inv,Units.val_inv_eq_inv_val,Units.val_mk0,
    RingHom.toMonoidHom_eq_coe,MonoidHom.coe_coe]

lemma residualCenter_norm_of_mass_floor {p : M} (hp : IsStarProjection p) (hp0 : p≠0)
    {ε : ℝ} (hε : 0<ε)
    (hmass : ε • (1:M) ≤ centerExpectation e τ hτ htr hfaith p) (a : M) :
    ‖residualCenter e τ hτ htr hfaith hp hp0 a‖ ≤
      ‖centerExpectation e τ hτ htr hfaith (p*a*p)‖/ε := by
  obtain ⟨u,hu,hun⟩ := exists_center_mass_unit e τ hτ htr hfaith hp hε hmass
  exact (residualCenter_norm_of_unit e τ hτ htr hfaith hp hp0 u hu a).trans
    (by simpa only [div_eq_mul_inv,mul_comm] using (mul_le_mul_of_nonneg_right hun
      (norm_nonneg (centerExpectation e τ hτ htr hfaith (p*a*p)))))

lemma centerExpectation_cyclic (a b : M) :
    centerExpectation e τ hτ htr hfaith (a*b)=centerExpectation e τ hτ htr hfaith (b*a) := by
  apply central_trace_unique τ hfaith
    (centerPart_central e τ hτ htr hfaith (a*b))
    (centerPart_central e τ hτ htr hfaith (b*a))
  intro z hz
  rw [centerPart_trace e τ hτ htr hfaith _ z hz,centerPart_trace e τ hτ htr hfaith _ z hz]
  calc
    _ = τ ((z*a)*b) := by rw [mul_assoc]
    _ = τ (b*(z*a)) := htr _ _
    _ = _ := by rw [← mul_assoc,← (hz b).eq,mul_assoc]

lemma centerExpectation_compression {p : M} (hp : IsStarProjection p) (a : M) :
    centerExpectation e τ hτ htr hfaith (p*a*p)=centerExpectation e τ hτ htr hfaith (p*a) := by
  rw [centerExpectation_cyclic e τ hτ htr hfaith (p*a) p,← mul_assoc,hp.isIdempotentElem.eq]

lemma residualCenter_norm_complement {s : M} (hs : IsStarProjection s) (hp0 : 1-s≠0)
    {ε : ℝ} (hε : 0<ε)
    (hmass : ε • (1:M) ≤ centerExpectation e τ hτ htr hfaith (1-s)) (a : M) :
    ‖residualCenter e τ hτ htr hfaith hs.one_sub hp0 a‖ ≤
      (‖centerExpectation e τ hτ htr hfaith a‖+
        ‖centerExpectation e τ hτ htr hfaith (s*a)‖)/ε := by
  have hh := residualCenter_norm_of_mass_floor e τ hτ htr hfaith hs.one_sub hp0 hε hmass a
  rw [centerExpectation_compression e τ hτ htr hfaith hs.one_sub a,sub_mul,one_mul,map_sub] at hh
  exact hh.trans (div_le_div_of_nonneg_right (norm_sub_le _ _) hε.le)

include e hτ htr hfaith in

lemma exists_positive_central_mass_band (h1 : τ 1=1) {p : M}
    (hp : IsStarProjection p) (hp0 : p≠0) :
    ∃ (ε : ℝ) (c : M), 0<ε ∧ IsStarProjection c ∧ c≠0 ∧
      (∀ x : M, Commute c x) ∧ c*p≠0 ∧
      ε • c ≤ centerExpectation e τ hτ htr hfaith (c*p) ∧
      centerExpectation e τ hτ htr hfaith (c*p) ≤ c := by
  let ε : ℝ := (τ p).re/2
  have ht : 0<(τ p).re := HochschildDiffuse.projection_trace_pos τ hfaith hp hp0
  have hε : 0<ε := div_pos ht (by norm_num)
  let a : M := centerExpectation e τ hτ htr hfaith p-ε • (1:M)
  have ha : IsSelfAdjoint a := (IsSelfAdjoint.of_nonneg
    (centerExpectation_nonneg e τ hτ htr hfaith hp.nonneg)).sub
    ((IsSelfAdjoint.all ε).smul (IsSelfAdjoint.one M))
  have hac (x : M) : Commute a x :=
    (centerPart_central e τ hτ htr hfaith p x).sub_left ((Commute.one_left x).smul_left ε)
  have hat : 0<(τ a).re := by
    have he : τ (ε • (1:M))=(ε:ℂ) := by rw [← Complex.coe_smul,map_smul,h1,smul_eq_mul,mul_one]
    dsimp only [a]
    rw [map_sub,Complex.sub_re,centerExpectation_trace,he,Complex.ofReal_re]
    dsimp only [ε]; linarith
  obtain ⟨c,hc,hcz,hca,hca0⟩ := exists_central_positive_cut e τ hτ htr hfaith ha hac hat
  have hc0 : c≠0 := by intro h; apply hca0; rw [h,zero_mul]
  have hfloor : ε • c ≤ centerExpectation e τ hτ htr hfaith (c*p) := by
    rw [centerExpectation_bimodule e τ hτ htr hfaith hcz]
    apply sub_nonneg.mp
    simpa only [a,mul_sub,mul_smul_comm,mul_one] using hca
  have hcp0 : c*p≠0 := by
    intro hh
    have hcpos := HochschildDiffuse.projection_trace_pos τ hfaith hc hc0
    rw [hh,map_zero] at hfloor
    have hz := τ.map_nonneg (neg_nonneg.mpr hfloor)
    have he : τ (ε • c)=(ε:ℂ)*τ c := by rw [← Complex.coe_smul,map_smul,smul_eq_mul]
    rw [map_neg,he,Complex.nonneg_iff] at hz
    have hr : 0≤ -(ε*(τ c).re) := by
      simpa only [Complex.neg_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hz.1
    nlinarith [mul_pos hε hcpos]
  refine ⟨ε,c,hε,hc,hc0,hcz,hcp0,hfloor,?_⟩
  have hcp : IsStarProjection (c*p) := hc.mul hp (hcz p)
  have hle : c*p≤c := (hcp.le_iff_mul_eq_right hc).mpr (by rw [← mul_assoc,hc.isIdempotentElem.eq])
  simpa only [centerExpectation_fix e τ hτ htr hfaith hcz] using
    centerExpectation_monotone e τ hτ htr hfaith hle

end HochschildCentralQuantization

end

end OAI
