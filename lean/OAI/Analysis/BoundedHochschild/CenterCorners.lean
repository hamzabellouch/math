import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.CenterExpectations
import OAI.Analysis.BoundedHochschild.CenterEnergy

namespace OAI

/-! Local central quantization and center-valued traces on corners. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildCentralQuantization
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems
  FinitePathMain
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {I : Type v} [Fintype I]

include e in
lemma exists_large_small_expectations
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hII : TypeII1 M)
    (x : I → M) (hx : ∀ i, CentrallyCentered τ (x i)) {ε : ℝ} (hε : 0<ε) (N : ℕ) :
    ∃ (n : ℕ) (E : MatrixSystem M n), N<n ∧ ∀ i, ‖τ.toPreGNS (E.expectation (x i))‖<ε := by
  obtain ⟨n,E,hn,hE⟩ := exists_small_matrix_expectations e τ hτ h1 htr hfaith hII x hx hε
  obtain ⟨P,hPn,hP⟩ := exists_abstract_star_preadjoint e
  let hL := mul_hasPreadjoint e
  let hR := mul_right_hasPreadjoint e
  let eC := E.commutantPredualEquiv e hL hR P hP
  let ρ := E.commutantTrace τ
  obtain ⟨F⟩ := exists_matrixSystem_of_typeII1 eC ρ (E.commutantTrace_normal e hL hR P hP τ hτ)
    (E.commutantTrace_tracial τ htr) (E.commutantTrace_faithful τ hfaith)
    (E.commutant_typeII1 e τ hn hτ htr hfaith hII) (N+1) (by omega)
  refine ⟨n*(N+1),E.extend F,?_,?_⟩
  · have hh : N+1 ≤ n*(N+1) := Nat.le_mul_of_pos_left _ hn
    omega
  · intro i
    exact (E.extension_gns_contract F τ htr (Nat.ne_of_gt hn) (by omega) (x i)).trans_lt (hE i)

include e in

theorem exists_small_corner_of_trace_limit
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hII : TypeII1 M)
    (x : I → M) (hx : ∀ i, CentrallyCentered τ (x i)) {δ η₀ : ℝ} (hδ : 0<δ) (hη₀ : 0<η₀) :
    ∃ q : M, IsStarProjection q ∧ q ≠ 0 ∧ (τ q).re < η₀ ∧
      ∀ i, ‖τ.toPreGNS (q*x i*q)‖^2 < δ*(τ q).re := by
  classical
  let K : ℝ := Fintype.card I+1
  have hK : 0<K := by dsimp [K]; positivity
  let η : ℝ := Real.sqrt (δ/(4*K))
  have hη : 0<η := Real.sqrt_pos.mpr (by positivity)
  have hηsq : η^2=δ/(4*K) := Real.sq_sqrt (by positivity)
  let B : ℝ := ∑ i,‖τ.toPreGNS (x i)‖^2
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  obtain ⟨N,hNall⟩ := exists_nat_gt (max (4*B/δ) (1/η₀))
  have hN : 4*B/δ < (N:ℝ) := (le_max_left _ _).trans_lt hNall
  have hNη : 1/η₀ < (N:ℝ) := (le_max_right _ _).trans_lt hNall
  obtain ⟨n,E,hnN,hE⟩ := exists_large_small_expectations e τ hτ h1 htr hfaith hII x hx hη N
  have hn : 0<n := lt_of_le_of_lt (Nat.zero_le N) hnN
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hBlt : B/(n:ℝ)<δ/4 := by
    have hh : 4*B/δ<(n:ℝ) := hN.trans (by exact_mod_cast hnN)
    have hh' := (div_lt_iff₀ hδ).mp hh
    apply (div_lt_iff₀ hnR).mpr
    nlinarith
  have hsum : (∑ i,‖τ.toPreGNS (E.expectation (x i))‖^2) ≤ (Fintype.card I:ℝ)*η^2 := by
    calc
      _ ≤ ∑ _i : I,η^2 := Finset.sum_le_sum (fun i hi =>
        (sq_le_sq₀ (norm_nonneg _) hη.le).mpr (hE i).le)
      _ = _ := by simp
  have hcard : (Fintype.card I:ℝ)*η^2<δ/4 := by
    rw [hηsq]
    have hh : (Fintype.card I:ℝ)<K := by dsimp [K]; linarith
    have hrat : 0<δ/(4*K) := by positivity
    have hall : K*(δ/(4*K))=δ/4 := by field_simp
    nlinarith [mul_lt_mul_of_pos_right hh hrat]
  have htotal : (∑ i,(‖τ.toPreGNS (E.expectation (x i))‖^2+‖τ.toPreGNS (x i)‖^2/(n:ℝ)))<δ := by
    rw [Finset.sum_add_distrib,← Finset.sum_div]
    change _ + B/(n:ℝ)<δ
    linarith
  obtain ⟨g,hg⟩ := E.exists_phase_energy_bound τ htr (Nat.ne_of_gt hn) x
  have hend : ∀ i,‖τ.toPreGNS (E.phaseCoefficient g (x i))‖^2<δ := by
    intro i
    have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
      sq_nonneg ‖τ.toPreGNS (E.phaseCoefficient g (x j))‖) (Finset.mem_univ i)
    exact hi.trans_lt (hg.trans_lt htotal)
  refine ⟨E.rankOne g,E.rankOne_projection (Nat.ne_of_gt hn) g,?_,?_,?_⟩
  · intro hz
    have ht := E.trace_rankOne τ htr h1 (Nat.ne_of_gt hn) g
    rw [hz,map_zero] at ht
    exact (inv_ne_zero (by exact_mod_cast (Nat.ne_of_gt hn) : (n:ℂ) ≠ 0)) ht.symm
  · rw [E.trace_rankOne τ htr h1 (Nat.ne_of_gt hn) g]
    have he : (n:ℂ)⁻¹=Complex.ofReal ((n:ℝ)⁻¹) := by simp
    rw [he,Complex.ofReal_re]
    have hh : 1/η₀ < (n:ℝ) := hNη.trans (by exact_mod_cast hnN)
    exact (inv_lt_comm₀ hnR hη₀).mpr (by simpa only [one_div] using hh)
  · intro i
    rw [E.rankOne_compression_norm τ htr (Nat.ne_of_gt hn) g (x i),
      E.trace_rankOne τ htr h1 (Nat.ne_of_gt hn) g]
    have he : (n:ℂ)⁻¹=Complex.ofReal ((n:ℝ)⁻¹) := by simp
    rw [he,Complex.ofReal_re,mul_comm δ]
    exact mul_lt_mul_of_pos_left (hend i) (inv_pos.mpr hnR)

include e in
theorem exists_small_corner
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hII : TypeII1 M)
    (x : I → M) (hx : ∀ i, CentrallyCentered τ (x i)) {δ : ℝ} (hδ : 0<δ) :
    ∃ q : M, IsStarProjection q ∧ q ≠ 0 ∧
      ∀ i, ‖τ.toPreGNS (q*x i*q)‖^2 < δ*(τ q).re := by
  obtain ⟨q,hq,hq0,_,hxq⟩ := exists_small_corner_of_trace_limit e τ hτ h1 htr hfaith
    hII x hx hδ (by norm_num : (0:ℝ)<1)
  exact ⟨q,hq,hq0,hxq⟩

end HochschildCentralQuantization

open scoped ComplexOrder
namespace HochschildCentralQuantization
open BoundedHochschild HochschildSakai HochschildRigidity FinitePathMain
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hτ htr hfaith in
lemma exists_central_positive_cut {a : M} (ha : IsSelfAdjoint a)
    (hcentral : ∀ x : M, Commute a x) (ht : 0<(τ a).re) :
    ∃ c : M, IsStarProjection c ∧ (∀ x : M, Commute c x) ∧
      0≤c*a ∧ c*a ≠ 0 := by
  obtain ⟨c,hc⟩ := exists_support_projection e τ (mul_hasPreadjoint e) hτ htr hfaith
    a⁺ (CFC.posPart_nonneg a)
  have hca : c*a=a⁺ := by
    conv_lhs => rw [← CFC.posPart_sub_negPart a ha]
    rw [mul_sub,hc.left,hc.annihilate a⁻ (CFC.posPart_mul_negPart a),sub_zero]
  have hn : a⁺ ≠ 0 := by
    intro hz
    have he : a= -a⁻ := by
      calc a = a⁺-a⁻ := (CFC.posPart_sub_negPart a ha).symm
           _ = -a⁻ := by rw [hz,zero_sub]
    have hh := τ.map_nonneg (CFC.negPart_nonneg a)
    rw [he,map_neg,Complex.neg_re] at ht
    have hhr : (0:ℝ) ≤ (τ a⁻).re := hh.1
    linarith
  refine ⟨c,hc.proj,?_,by rw [hca]; exact CFC.posPart_nonneg a,by rwa [hca]⟩
  intro x
  apply hc.commute (IsSelfAdjoint.of_nonneg (CFC.posPart_nonneg a))
  rw [CFC.posPart_def,cfcₙ_eq_cfc]
  exact (hcentral x).cfc (by simpa only [ha.star_eq] using hcentral x) _

lemma centerExpectation_trace (a : M) :
    τ (centerExpectation e τ hτ htr hfaith a)=τ a := by
  simpa only [one_mul,centerExpectation_apply] using centerPart_trace e τ hτ htr hfaith a 1
    (fun x => Commute.one_left x)

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_cut_compression {c q x : M} (hc : IsStarProjection c)
    (hz : ∀ a : M, Commute c a) : (c*q)*x*(c*q)=c*(q*x*q) := by
  calc
    _ = c*((q*x)*c)*q := by simp only [mul_assoc]
    _ = c*(c*(q*x))*q := by rw [← (hz (q*x)).eq]
    _ = _ := by rw [← mul_assoc c c,hc.isIdempotentElem.eq]; simp only [mul_assoc]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_cut_energy {c q x : M} (hc : IsStarProjection c)
    (hz : ∀ a : M, Commute c a) :
    star ((c*q)*x*(c*q))*((c*q)*x*(c*q))=c*(star (q*x*q)*(q*x*q)) := by
  rw [central_cut_compression hc hz,star_mul,hc.isSelfAdjoint.star_eq]
  calc
    _ = star (q*x*q)*(c*c)*(q*x*q) := by simp only [mul_assoc]
    _ = c*(star (q*x*q)*(q*x*q)) := by
      rw [hc.isIdempotentElem.eq,← (hz (star (q*x*q))).eq,mul_assoc]

include e hτ htr hfaith in

lemma exists_center_order_cut {I : Type*} [Fintype I]
    (x : I → M) {q : M} (hq : IsStarProjection q) {δ : ℝ}
    (hsmall : (∑ i, ‖τ.toPreGNS (q*x i*q)‖^2) < δ*(τ q).re) :
    ∃ r : M, IsStarProjection r ∧ r ≠ 0 ∧ r ≤ q ∧
      (∑ i, centerExpectation e τ hτ htr hfaith (star (r*x i*r)*(r*x i*r))) ≤
        δ • centerExpectation e τ hτ htr hfaith r := by
  classical
  let E := centerExpectation e τ hτ htr hfaith
  let b : I → M := fun i => star (q*x i*q)*(q*x i*q)
  let a : M := δ • E q - ∑ i,E (b i)
  have hEz (x y : M) : Commute (E x) y := centerPart_central e τ hτ htr hfaith x y
  have hEp (x : M) (hx : 0≤x) : 0≤E x := centerExpectation_nonneg e τ hτ htr hfaith hx
  have ha : IsSelfAdjoint a := by
    apply IsSelfAdjoint.sub
    · exact (IsSelfAdjoint.all δ).smul (IsSelfAdjoint.of_nonneg (hEp q hq.nonneg))
    · exact IsSelfAdjoint.of_nonneg (Finset.sum_nonneg (fun i _ => hEp _ (star_mul_self_nonneg _)))
  have hac : ∀ y : M, Commute a y := by
    intro y
    apply Commute.sub_left
    · exact (hEz q y).smul_left δ
    · exact Commute.sum_left Finset.univ (fun i => E (b i)) y (fun i _ => hEz (b i) y)
  have hat : 0<(τ a).re := by
    have hreal : τ (δ • E q) = (δ:ℂ)*τ q := by
      rw [← Complex.coe_smul,map_smul,smul_eq_mul,centerExpectation_trace]
    have hb (i : I) : (τ (E (b i))).re=‖τ.toPreGNS (q*x i*q)‖^2 := by
      rw [centerExpectation_trace]
      exact trace_star_mul_self_re τ _
    dsimp only [a]
    rw [map_sub,Complex.sub_re,hreal,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,map_sum,Complex.re_sum]
    simp only [hb]
    linarith
  obtain ⟨c,hc,hcz,hca,hca0⟩ := exists_central_positive_cut e τ hτ htr hfaith ha hac hat
  have hr : IsStarProjection (c*q) := hc.mul hq (hcz q)
  have hcut : (∑ i,E (star ((c*q)*x i*(c*q))*((c*q)*x i*(c*q)))) ≤ δ • E (c*q) := by
    have hid : δ • E (c*q) - ∑ i,E (star ((c*q)*x i*(c*q))*((c*q)*x i*(c*q))) = c*a := by
      simp only [E,central_cut_energy hc hcz,centerExpectation_bimodule e τ hτ htr hfaith hcz,
        a,b,mul_sub,mul_smul_comm,Finset.mul_sum]
    exact sub_nonneg.mp (by rw [hid]; exact hca)
  refine ⟨c*q,hr,?_,?_,hcut⟩
  · intro he
    apply hca0
    have hEb : ∀ i, c*E (b i)=0 := by
      intro i
      rw [← centerExpectation_bimodule e τ hτ htr hfaith hcz]
      have hcb : c*b i=0 := by
        have hh := central_cut_energy (q := q) (x := x i) hc hcz
        rw [he,zero_mul,mul_zero,star_zero,mul_zero] at hh
        exact hh.symm
      rw [hcb,map_zero]
    change c*(δ • E q - ∑ i,E (b i))=0
    rw [mul_sub,mul_smul_comm,← centerExpectation_bimodule e τ hτ htr hfaith hcz,
      he,map_zero,smul_zero,Finset.mul_sum]
    simp only [hEb,Finset.sum_const_zero,sub_self]
  · apply (hr.le_iff_mul_eq_left hq).mpr
    rw [mul_assoc,hq.isIdempotentElem.eq]

include e hτ htr hfaith in

theorem exists_small_corner_center_order
    (h1 : τ 1=1) (hII : TypeII1 M)
    {I : Type*} [Fintype I] (x : I → M) (hx : ∀ i, CentrallyCentered τ (x i))
    {δ η : ℝ} (hδ : 0<δ) (hη : 0<η) :
    ∃ r : M, IsStarProjection r ∧ r ≠ 0 ∧ (τ r).re<η ∧
      (∑ i, centerExpectation e τ hτ htr hfaith (star (r*x i*r)*(r*x i*r))) ≤
        δ • centerExpectation e τ hτ htr hfaith r := by
  classical
  let K : ℝ := Fintype.card I+1
  have hK : 0<K := by dsimp [K]; positivity
  obtain ⟨q,hq,hq0,hqt,hqx⟩ := exists_small_corner_of_trace_limit e τ hτ h1 htr hfaith
    hII x hx (div_pos hδ hK) hη
  have ht : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  have hs : (∑ i,‖τ.toPreGNS (q*x i*q)‖^2)<δ*(τ q).re := by
    have hh : (∑ i,‖τ.toPreGNS (q*x i*q)‖^2) ≤ (Fintype.card I:ℝ)*(δ/K*(τ q).re) := by
      calc
        _ ≤ ∑ _i : I,δ/K*(τ q).re := Finset.sum_le_sum (fun i _ => (hqx i).le)
        _ = _ := by simp
    have hcard : (Fintype.card I:ℝ)<K := by dsimp [K]; linarith
    have hp : 0<δ/K*(τ q).re := mul_pos (div_pos hδ hK) ht
    have he : K*(δ/K*(τ q).re)=δ*(τ q).re := by field_simp
    exact hh.trans_lt (by nlinarith [mul_lt_mul_of_pos_right hcard hp])
  obtain ⟨r,hr,hr0,hrq,hrx⟩ := exists_center_order_cut e τ hτ htr hfaith x hq hs
  refine ⟨r,hr,hr0,?_,hrx⟩
  exact (Complex.re_le_re (τ.monotone hrq)).trans_lt hqt

end HochschildCentralQuantization

open scoped ComplexOrder
namespace HochschildCentralQuantization
open BoundedHochschild HochschildSakai HochschildCorners HochschildCentralComparison FinitePathMain
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hτ htr hfaith in
lemma central_corner_projection_lift {p r : M} (hp : IsStarProjection p)
    (hr : IsStarProjection r) (hrp : r≤p)
    (hcentral : ∀ a : M, Commute r (p*a*p)) :
    ∃ z : M, CentralProjection z ∧ z*p=r := by
  have hpr : p*r=r := (hr.le_iff_mul_eq_right hp).mp hrp
  have hrp' : r*p=r := (hr.le_iff_mul_eq_left hp).mp hrp
  have hcomp : IsStarProjection (p-r) := (hr.le_iff_sub hp).mp hrp
  have hoff : ∀ a : M, r*a*(p-r)=0 := by
    intro a
    have hc := (hcentral a).eq
    have h1 : r*(p*a*p)=r*a*p := by rw [← mul_assoc,← mul_assoc,hrp']
    have h2 : (p*a*p)*r=p*a*r := by rw [mul_assoc,hpr]
    rw [h1,h2] at hc
    have h3 := congrArg (fun b : M => r*b) hc
    simp only [← mul_assoc,hr.isIdempotentElem.eq,hrp'] at h3
    rw [mul_sub,h3,sub_self]
  obtain ⟨z,hz,hrz,hzcomp⟩ := central_separator e τ hτ htr hfaith hr hcomp hoff
  refine ⟨z,hz,?_⟩
  have hzr : z*r=r := (hr.le_iff_mul_eq_right hz.1).mp hrz
  rw [mul_sub,hzr,sub_eq_zero] at hzcomp
  exact hzcomp

include e hτ htr hfaith in
lemma corner_selfAdjoint_posPart_trace {p a : M} (hp : IsStarProjection p)
    (ha : a ∈ corner p hp) (has : IsSelfAdjoint a)
    (hac : ∀ b : M, Commute a (p*b*p)) (hat : CentrallyCentered τ a) :
    τ a⁺=0 := by
  obtain ⟨r,hr⟩ := BoundedHochschild.exists_support_projection e τ
    (mul_hasPreadjoint e) hτ htr hfaith a⁺ (CFC.posPart_nonneg a)
  have hrp : r≤p := support_le_corner hp (posPart_mem_corner hp ha) hr
  have hrc : ∀ b : M, Commute r (p*b*p) := by
    intro b
    apply hr.commute (IsSelfAdjoint.of_nonneg (CFC.posPart_nonneg a))
    rw [CFC.posPart_def,cfcₙ_eq_cfc]
    exact (hac b).cfc (by simpa only [has.star_eq] using hac b) _
  obtain ⟨z,hz,hzp⟩ := central_corner_projection_lift e τ hτ htr hfaith hp hr.proj hrp hrc
  have hra : r*a=a⁺ := by
    conv_lhs => rw [← CFC.posPart_sub_negPart a has]
    rw [mul_sub,hr.left,hr.annihilate a⁻ (CFC.posPart_mul_negPart a),sub_zero]
  have hza : z*a=a⁺ := by
    calc z*a = z*(p*a) := by rw [ha.1]
         _ = a⁺ := by rw [← mul_assoc,hzp,hra]
  rw [← hza]
  exact hat z hz.2

include e hτ htr hfaith in
lemma corner_selfAdjoint_centered_zero {p a : M} (hp : IsStarProjection p)
    (ha : a ∈ corner p hp) (has : IsSelfAdjoint a)
    (hac : ∀ b : M, Commute a (p*b*p)) (hat : CentrallyCentered τ a) : a=0 := by
  have hpz := corner_selfAdjoint_posPart_trace e τ hτ htr hfaith hp ha has hac hat
  have hnt : CentrallyCentered τ (-a) := by
    intro z hz
    rw [mul_neg,map_neg,hat z hz,neg_zero]
  have hnz := corner_selfAdjoint_posPart_trace e τ hτ htr hfaith hp
    ((corner p hp).neg_mem ha) has.neg (fun b => (hac b).neg_left) hnt
  have hposzero (b : M) (hb : 0≤b) (hbt : τ b=0) : b=0 := by
    have hs : CFC.sqrt b=0 := hfaith _ (by
      rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq,
        CFC.sqrt_mul_sqrt_self b hb,hbt])
    calc b = CFC.sqrt b*CFC.sqrt b := (CFC.sqrt_mul_sqrt_self b hb).symm
         _ = 0 := by rw [hs,mul_zero]
  have hp0 := hposzero a⁺ (CFC.posPart_nonneg a) hpz
  have hn0 := hposzero (-a)⁺ (CFC.posPart_nonneg (-a)) hnz
  have hn0' : a⁻=0 := by simpa only [CFC.posPart_neg] using hn0
  calc a = a⁺-a⁻ := (CFC.posPart_sub_negPart a has).symm
       _ = 0 := by rw [hp0,hn0',sub_self]

include e hτ htr hfaith in
lemma corner_centered_zero {p a : M} (hp : IsStarProjection p)
    (ha : a ∈ corner p hp) (hac : ∀ b : M, Commute a (p*b*p))
    (hat : CentrallyCentered τ a) : a=0 := by
  have hE : centerExpectation e τ hτ htr hfaith a=0 :=
    (centerExpectation_zero_iff e τ hτ htr hfaith a).mpr hat
  have hacs (b : M) : Commute (star a) (p*b*p) := by
    have hh := (hac (star b)).star_star
    simpa only [star_mul,hp.isSelfAdjoint.star_eq,star_star,mul_assoc] using hh
  have hplus : a+star a=0 := by
    apply corner_selfAdjoint_centered_zero e τ hτ htr hfaith hp
      ((corner p hp).add_mem ha (show star a ∈ corner p hp from star_mem ha)) (IsSelfAdjoint.add_star_self a)
      (fun b => (hac b).add_left (hacs b))
    apply (centerExpectation_zero_iff e τ hτ htr hfaith _).mp
    rw [map_add,centerExpectation_star,hE,star_zero,add_zero]
  have hstar : star a= -a := eq_neg_of_add_eq_zero_right hplus
  have hIplus : Complex.I • a+star (Complex.I • a)=0 := by
    have hIa : Complex.I • a ∈ corner p hp := (corner p hp).smul_mem _ ha
    apply corner_selfAdjoint_centered_zero e τ hτ htr hfaith hp
      ((corner p hp).add_mem hIa (show star (Complex.I • a) ∈ corner p hp from star_mem hIa))
      (IsSelfAdjoint.add_star_self (Complex.I • a))
    · intro b
      apply Commute.add_left ((hac b).smul_left _)
      rw [star_smul]
      exact (hacs b).smul_left _
    · apply (centerExpectation_zero_iff e τ hτ htr hfaith _).mp
      rw [map_add,centerExpectation_star,map_smul,hE,smul_zero,star_zero,add_zero]
  simp only [star_smul,Complex.star_def,Complex.conj_I,hstar,smul_neg,neg_smul,neg_neg] at hIplus
  have htwo : (2:ℂ) • (Complex.I • a)=0 := by rw [two_smul, hIplus]
  exact (smul_eq_zero.mp ((smul_eq_zero.mp htwo).resolve_left two_ne_zero)).resolve_left Complex.I_ne_zero

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_corner_weight_mul {p z : M} (hp : IsStarProjection p)
    (hz : ∀ b : M, Commute z b) (a : Corner p hp) : (p*z*p)*(a:M)=z*(a:M) := by
  calc (p*z*p)*(a:M) = (p*z)*(p*(a:M)) := by rw [mul_assoc]
       _ = (p*z)*(a:M) := by rw [a.property.1]
       _ = (z*p)*(a:M) := by rw [(hz p).eq]
       _ = z*(a:M) := by rw [mul_assoc,a.property.1]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_corner_weight {p z : M} (hp : IsStarProjection p)
    (hz : ∀ b : M, Commute z b) :
    ∀ a : Corner p hp, Commute (⟨p*z*p,compress_mem_corner hp z⟩ : Corner p hp) a := by
  intro a
  change (⟨p*z*p,compress_mem_corner hp z⟩ : Corner p hp)*a=
    a*(⟨p*z*p,compress_mem_corner hp z⟩ : Corner p hp)
  apply Subtype.ext
  change (p*z*p)*(a:M)=(a:M)*(p*z*p)
  rw [central_corner_weight_mul hp hz a,← mul_assoc,← mul_assoc,a.property.2,
    ← (hz (a:M)).eq,mul_assoc,a.property.2]

include e hτ htr hfaith in

lemma ambient_centered_corner {p : M} (hp : IsStarProjection p) (hp0 : p≠0)
    (a : Corner p hp) (ha : CentrallyCentered τ (a:M)) :
    CentrallyCentered (cornerTrace p hp τ) a := by
  let ec := cornerPredualEquiv p hp e
  let tc := cornerTrace p hp τ
  have hn : TraceInPredual ec tc := cornerTrace_normal p hp e τ hτ
  have ht : ∀ a b : Corner p hp, tc (a*b)=tc (b*a) := cornerTrace_tracial p hp τ htr
  have hf : ∀ a : Corner p hp, tc (star a*a)=0 → a=0 := cornerTrace_faithful p hp τ hfaith hp0
  let b : Corner p hp := centerPart ec tc hn ht hf a
  have hbc : ∀ x : M, Commute (b:M) (p*x*p) := by
    intro x
    have hh := centerPart_central ec tc hn ht hf a ⟨p*x*p,compress_mem_corner hp x⟩
    exact congrArg (fun v : Corner p hp => (v:M)) hh.eq
  have hbt : CentrallyCentered τ (b:M) := by
    intro z hz
    let zc : Corner p hp := ⟨p*z*p,compress_mem_corner hp z⟩
    have hh := centerPart_trace ec tc hn ht hf a zc (central_corner_weight hp hz)
    change ((τ p).re : ℂ)⁻¹ * τ ((p*z*p)*(b:M))=
      ((τ p).re : ℂ)⁻¹ * τ ((p*z*p)*(a:M)) at hh
    rw [central_corner_weight_mul hp hz b,central_corner_weight_mul hp hz a,ha z hz,mul_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (HochschildDiffuse.projection_trace_pos τ hfaith hp hp0).ne'))
  have hb0 : (b:M)=0 := corner_centered_zero e τ hτ htr hfaith hp b.property hbc hbt
  apply (centerExpectation_zero_iff ec tc hn ht hf a).mp
  exact Subtype.ext hb0

def cornerExpectation {p : M} (hp : IsStarProjection p) (hp0 : p≠0) :
    Corner p hp →L[ℂ] Corner p hp :=
  centerExpectation (cornerPredualEquiv p hp e) (cornerTrace p hp τ)
    (cornerTrace_normal p hp e τ hτ) (cornerTrace_tracial p hp τ htr)
    (cornerTrace_faithful p hp τ hfaith hp0)

lemma cornerExpectation_weighted_trace {p : M} (hp : IsStarProjection p) (hp0 : p≠0)
    (a : Corner p hp) {z : M} (hz : ∀ x : M, Commute z x) :
    τ (z*(cornerExpectation e τ hτ htr hfaith hp hp0 a : M))=τ (z*(a:M)) := by
  let zc : Corner p hp := ⟨p*z*p,compress_mem_corner hp z⟩
  have hh := centerPart_trace (cornerPredualEquiv p hp e) (cornerTrace p hp τ)
    (cornerTrace_normal p hp e τ hτ) (cornerTrace_tracial p hp τ htr)
    (cornerTrace_faithful p hp τ hfaith hp0) a zc (central_corner_weight hp hz)
  change ((τ p).re : ℂ)⁻¹ * τ ((p*z*p)*(cornerExpectation e τ hτ htr hfaith hp hp0 a : M))=
    ((τ p).re : ℂ)⁻¹ * τ ((p*z*p)*(a:M)) at hh
  rw [central_corner_weight_mul hp hz,central_corner_weight_mul hp hz] at hh
  exact mul_left_cancel₀ (inv_ne_zero (Complex.ofReal_ne_zero.mpr
    (HochschildDiffuse.projection_trace_pos τ hfaith hp hp0).ne')) hh

lemma centerExpectation_corner_tower {p : M} (hp : IsStarProjection p) (hp0 : p≠0)
    (a : Corner p hp) :
    centerExpectation e τ hτ htr hfaith (cornerExpectation e τ hτ htr hfaith hp hp0 a : M)=
      centerExpectation e τ hτ htr hfaith (a:M) := by
  apply central_trace_unique τ hfaith
    (centerPart_central e τ hτ htr hfaith _) (centerPart_central e τ hτ htr hfaith _)
  intro z hz
  exact (centerPart_trace e τ hτ htr hfaith _ z hz).trans
    ((cornerExpectation_weighted_trace e τ hτ htr hfaith hp hp0 a hz).trans
      (centerPart_trace e τ hτ htr hfaith _ z hz).symm)

lemma centerExpectation_monotone : Monotone (centerExpectation e τ hτ htr hfaith) := by
  intro a b hab
  apply sub_nonneg.mp
  rw [← map_sub]
  exact centerExpectation_nonneg e τ hτ htr hfaith (sub_nonneg.mpr hab)

include e hτ htr hfaith in
lemma corner_typeII1 {p : M} (hp : IsStarProjection p) (hp0 : p≠0)
    (hII : TypeII1 M) : TypeII1 (Corner p hp) := by
  constructor
  · exact HochschildMatrixSystems.finite_of_faithful_trace (cornerTrace p hp τ)
      (cornerTrace_tracial p hp τ htr) (cornerTrace_faithful p hp τ hfaith hp0)
  · intro z hz
    by_contra hz0
    obtain ⟨q,hq,_hqz,hq0⟩ := hz.2 z hz.1 le_rfl hz0
    have hqm : IsStarProjection (q:M) := corner_projection_coe p hp hq.1
    have hcompress (a : M) : (q:M)*(p*a*p)*(q:M)=(q:M)*a*(q:M) := by
      rw [← mul_assoc,← mul_assoc,q.property.2,mul_assoc,q.property.1]
    have hqa : AbelianProjection (q:M) := by
      refine ⟨hqm,fun a b => ?_⟩
      have hh := congrArg (fun v : Corner p hp => (v:M))
        (hq.2 ⟨p*a*p,compress_mem_corner hp a⟩ ⟨p*b*p,compress_mem_corner hp b⟩).eq
      change ((q:M)*(p*a*p)*(q:M))*((q:M)*(p*b*p)*(q:M))=
        ((q:M)*(p*b*p)*(q:M))*((q:M)*(p*a*p)*(q:M)) at hh
      change (q:M)*a*(q:M)*((q:M)*b*(q:M))=(q:M)*b*(q:M)*((q:M)*a*(q:M))
      simpa only [hcompress] using hh
    exact hq0 (Subtype.ext (HochschildTypeII.no_abelian_projection e τ hτ htr hfaith hII hqa))

end HochschildCentralQuantization

end

end OAI
