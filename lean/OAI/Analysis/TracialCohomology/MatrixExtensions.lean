import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.ProjectionEstimates

namespace OAI

/-! Matrix extensions for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaQuantization
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

include htr in
lemma commutator_difference_bound (b p q : M) :
    ‖τ.toPreGNS (p*b-b*p)‖ ≤ ‖τ.toPreGNS (q*b-b*q)‖ +
      2*‖b‖*‖τ.toPreGNS (p-q)‖ := by
  have he : p*b-b*p=(q*b-b*q)+((p-q)*b-b*(p-q)) := by
    simp only [sub_mul,mul_sub]; abel
  rw [he,map_add]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [map_sub]
  calc
    ‖τ.toPreGNS ((p-q)*b)-τ.toPreGNS (b*(p-q))‖ ≤
        ‖τ.toPreGNS ((p-q)*b)‖+‖τ.toPreGNS (b*(p-q))‖ := norm_sub_le _ _
    _ ≤ ‖b‖*‖τ.toPreGNS (p-q)‖+‖b‖*‖τ.toPreGNS (p-q)‖ :=
      add_le_add (preGNS_norm_mul_right_le τ htr _ _) (preGNS_norm_mul_le τ _ _)
    _ = _ := by ring

include e hτ htr hfaith h1 hfactor in

theorem exists_matrix_energy_decrease (hdiff : NoMinimalProjections M)
    (b : M) (hbτ : τ b=0) (hb : 0 < ‖τ.toPreGNS b‖) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : System n (1:M),
      ‖τ.toPreGNS (s.expect b)‖^2 < (1-1/1024:ℝ)*‖τ.toPreGNS b‖^2 := by
  obtain ⟨p,hp,hcomm⟩ := exists_large_projection_commutator e τ h1 hτ htr hfaith hfactor b hbτ hb
  let ε : ℝ := ‖τ.toPreGNS b‖/(32*(‖b‖+1))
  have hε : 0 < ε := div_pos hb (by positivity)
  obtain ⟨n,hn,s,q,hq,_hqp,happrox,hcq⟩ := exists_matrix_approximating_projection
    e τ hτ htr hfaith h1 hfactor hdiff hp (ε^2) (sq_pos_of_pos hε)
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
end PopaQuantization

open scoped ComplexOrder
namespace PopaMatrices.System
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n m : ℕ} (s : PopaMatrices.System n (1:M)) (t : PopaMatrices.System m (1:M))
variable (hc : ∀ i j a b, Commute (s.entry i j) (t.entry a b))

lemma sum_product_index {E : Type*} [AddCommMonoid E] (f : Fin (n*m) → E) :
    ∑ i, f i=∑ i : Fin n, ∑ a : Fin m, f (finProdFinEquiv (i,a)) := by
  exact (Fintype.sum_equiv finProdFinEquiv.symm f (fun z => f (finProdFinEquiv z))
    (fun i => (congrArg f (finProdFinEquiv.apply_symm_apply i)).symm)).trans (Fintype.sum_prod_type _)

def tensor : PopaMatrices.System (n*m) (1:M) where
  entry i j := s.entry (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
    t.entry (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2
  star_entry i j := by
    simp only [star_mul,s.star_entry,t.star_entry]
    exact (hc _ _ _ _).eq.symm
  mul_entry i j k l := by
    classical
    let a := finProdFinEquiv.symm j
    let b := finProdFinEquiv.symm k
    have he : (j=k) ↔ (a.1=b.1 ∧ a.2=b.2) := by
      rw [← Prod.ext_iff]
      exact finProdFinEquiv.symm.injective.eq_iff.symm
    have hh : (s.entry (finProdFinEquiv.symm i).1 a.1 *
        t.entry (finProdFinEquiv.symm i).2 a.2) *
        (s.entry b.1 (finProdFinEquiv.symm l).1 * t.entry b.2 (finProdFinEquiv.symm l).2) =
        (s.entry (finProdFinEquiv.symm i).1 a.1 * s.entry b.1 (finProdFinEquiv.symm l).1)*
        (t.entry (finProdFinEquiv.symm i).2 a.2 * t.entry b.2 (finProdFinEquiv.symm l).2) := by
      simp only [mul_assoc]
      rw [← mul_assoc (t.entry _ _),← (hc _ _ _ _).eq,mul_assoc]
    rw [hh,s.mul_entry,t.mul_entry]
    by_cases ha : a.1=b.1 <;> by_cases hb : a.2=b.2 <;> simp [ha,hb,he]
  sum_diag := by
    rw [sum_product_index]
    simp only [Equiv.symm_apply_apply]
    simp_rw [← Finset.mul_sum,t.sum_diag,mul_one]
    exact s.sum_diag

omit [PartialOrder M] [StarOrderedRing M] in
lemma tensor_entry (i j : Fin n) (a b : Fin m) :
    (s.tensor t hc).entry (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b)) =
      s.entry i j*t.entry a b := by
  change s.entry (finProdFinEquiv.symm (finProdFinEquiv (i,a))).1
    (finProdFinEquiv.symm (finProdFinEquiv (j,b))).1 *
    t.entry (finProdFinEquiv.symm (finProdFinEquiv (i,a))).2
    (finProdFinEquiv.symm (finProdFinEquiv (j,b))).2 = _
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

omit [PartialOrder M] [StarOrderedRing M] in
lemma tensor_sumExpect (x : M) : (s.tensor t hc).sumExpect x=s.sumExpect (t.sumExpect x) := by
  rw [sumExpect,sum_product_index]
  simp_rw [sum_product_index,(s.tensor_entry t hc)]
  simp only [sumExpect,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [mul_assoc]
  rw [(hc j i b a).eq]

omit [PartialOrder M] [StarOrderedRing M] in
lemma tensor_expect (x : M) : (s.tensor t hc).expect x=s.expect (t.expect x) := by
  unfold expect
  rw [tensor_sumExpect]
  simp only [sumExpect,mul_smul_comm,smul_mul_assoc,
    ← Finset.smul_sum,smul_smul,Nat.cast_mul,mul_inv_rev]
  rw [mul_comm]
end PopaMatrices.System

open scoped ComplexOrder
namespace PopaMatrices
open HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ}
namespace System
variable (s : System n (1:M))

omit [PartialOrder M] [StarOrderedRing M] in
lemma left_mul_coordinate (x : M) (i j a b : Fin n) :
    s.entry a b*s.coordinate x i j = s.entry a i*x*s.entry j b := by
  classical
  simp [coordinate,Finset.mul_sum,← mul_assoc,s.mul_entry,ite_mul,zero_mul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma coordinate_zero (i : Fin n) : s.coordinate 0 i i=0 := by
  simp only [coordinate,mul_zero,zero_mul,Finset.sum_const_zero]

omit [PartialOrder M] [StarOrderedRing M] in
lemma coordinate_sub (x y : M) (i : Fin n) :
    s.coordinate (x-y) i i=s.coordinate x i i-s.coordinate y i i := by
  simp only [coordinate,mul_sub,sub_mul,Finset.sum_sub_distrib]

omit [PartialOrder M] [StarOrderedRing M] in
lemma coordinate_star (x : M) (i : Fin n) :
    s.coordinate (star x) i i=star (s.coordinate x i i) := by
  simp only [coordinate,star_sum,star_mul,s.star_entry,mul_assoc]

omit [PartialOrder M] [StarOrderedRing M] in
lemma coordinate_mul {x y : M} (i : Fin n) (hxi : x*s.entry i i=x) :
    s.coordinate (x*y) i i=s.coordinate x i i*s.coordinate y i i := by
  classical
  have hterm (k l : Fin n) : (s.entry k i*x*s.entry i k)*(s.entry l i*y*s.entry i l)=
      if k=l then s.entry k i*(x*y)*s.entry i k else 0 := by
    calc
      _ = s.entry k i*(x*(s.entry i k*s.entry l i))*y*s.entry i l := by
        simp only [mul_assoc]
      _ = _ := by
        by_cases h : k=l
        · subst l
          simp only [s.mul_entry,↓reduceIte,hxi,mul_assoc]
        · simp only [s.mul_entry,ite_eq_right h,mul_zero,zero_mul]
  simp only [coordinate,Finset.sum_mul,Finset.mul_sum,hterm]
  simp

omit [PartialOrder M] [StarOrderedRing M] in
lemma extract_coordinate {x : M} (i : Fin n)
    (hix : s.entry i i*x=x) (hxi : x*s.entry i i=x) :
    s.entry i i*s.coordinate x i i=x := by
  rw [s.left_mul_coordinate,hix,hxi]

omit [PartialOrder M] [StarOrderedRing M] in
lemma coordinate_of_commutes (x : M) (hx : x ∈ s.commutant) (i : Fin n) :
    s.coordinate (s.entry i i*x) i i=x := by
  have hterm (k : Fin n) : s.entry k i*(s.entry i i*x)*s.entry i k=s.entry k k*x := by
    calc
      _ = (s.entry k i*s.entry i i)*(x*s.entry i k) := by simp only [mul_assoc]
      _ = s.entry k k*x := by
        rw [s.entry_absorb_right,(hx i k).eq]
        rw [← mul_assoc,s.mul_entry,ite_eq_left rfl]
  simp only [coordinate,hterm,← Finset.sum_mul,s.sum_diag,one_mul]

lemma coordinate_projection {x : M} (i : Fin n) (hx : IsStarProjection x)
    (hxi : x ≤ s.entry i i) : IsStarProjection (s.coordinate x i i) := by
  have habs := (hx.le_iff_mul_eq_left (s.diagonal_projection i)).mp hxi
  refine ⟨?_,?_⟩
  · change s.coordinate x i i*s.coordinate x i i=s.coordinate x i i
    rw [← s.coordinate_mul i habs,hx.isIdempotentElem.eq]
  · change star (s.coordinate x i i)=s.coordinate x i i
    rw [← s.coordinate_star,hx.isSelfAdjoint.star_eq]

theorem commutant_subprojection (hdiff : NoMinimalProjections M)
    (i : Fin n) {p : M} (hp : IsStarProjection p) (hpQ : p ∈ s.commutant) (hp0 : p ≠ 0) :
    ∃ q : M, q ∈ s.commutant ∧ IsStarProjection q ∧ q ≤ p ∧ q ≠ 0 ∧ q ≠ p := by
  let a : M := s.entry i i*p
  have ha : IsStarProjection a := (s.diagonal_projection i).mul hp (hpQ i i).symm
  have hai : a ≤ s.entry i i := (ha.le_iff_mul_eq_right (s.diagonal_projection i)).mpr (by
    dsimp [a]; rw [← mul_assoc,(s.diagonal_projection i).isIdempotentElem.eq])
  have hac : s.coordinate a i i=p := s.coordinate_of_commutes p hpQ i
  have ha0 : a ≠ 0 := by
    intro h
    exact hp0 (by simpa only [h,s.coordinate_zero] using hac.symm)
  obtain ⟨t,ht,hta,ht0,htne⟩ := hdiff a ha ha0
  have hti := hta.trans hai
  let q := s.coordinate t i i
  have htq : s.entry i i*q=t := s.extract_coordinate i
    ((ht.le_iff_mul_eq_right (s.diagonal_projection i)).mp hti)
    ((ht.le_iff_mul_eq_left (s.diagonal_projection i)).mp hti)
  have hq : IsStarProjection q := s.coordinate_projection i ht hti
  have hsub : IsStarProjection (p-q) := by
    rw [← hac,← s.coordinate_sub]
    apply s.coordinate_projection i ((ht.le_iff_sub ha).mp hta)
    exact (sub_le_self _ ht.nonneg).trans hai
  refine ⟨q,s.coordinate_mem t i i,hq,(hq.le_iff_sub hp).mpr hsub,?_,?_⟩
  · intro h
    exact ht0 (by simpa only [h,mul_zero] using htq.symm)
  · intro h
    exact htne (by simpa only [h] using htq.symm)

end System
end PopaMatrices

open Filter Topology
open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
variable {n : ℕ} (s : System n (1:M))

section Closed
variable (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

def closedCommutant : StarSubalgebra ℂ M := WeakAlgebra.closure e s.commutant
  (HochschildSakai.abstract_multiplication_normal e).1
  (HochschildSakai.abstract_multiplication_normal e).2 P hP

instance closedCommutant_closed : IsClosed (closedCommutant e s P hP : Set M) :=
  WeakAlgebra.closure_closed e s.commutant
    (HochschildSakai.abstract_multiplication_normal e).1
    (HochschildSakai.abstract_multiplication_normal e).2 P hP

omit [PartialOrder M] [StarOrderedRing M] in
lemma mem_closedCommutant {a : M} (ha : a ∈ s.commutant) : a ∈ closedCommutant e s P hP :=
  WeakAlgebra.mem_linearClosure e s.commutant ha

omit [PartialOrder M] [StarOrderedRing M] in
lemma closedCommutant_subset : closedCommutant e s P hP ≤ s.commutant := by
  intro a ha i j
  let R := ((ContinuousLinearMap.mul ℂ M).flip (s.entry i j))
  let L := ContinuousLinearMap.mul ℂ M (s.entry i j)
  have hR := WeakAlgebra.normal_continuous e R
    ((HochschildSakai.abstract_multiplication_normal e).2 (s.entry i j))
  have hL := WeakAlgebra.normal_continuous e L
    ((HochschildSakai.abstract_multiplication_normal e).1 (s.entry i j))
  have hclosed := isClosed_eq hR hL
  have hm : (WeakAlgebra.weakEquiv e).symm a ∈
      closure ((s.commutant.toSubalgebra.toSubmodule.map
        (WeakAlgebra.weakEquiv e).symm.toLinearMap : Submodule ℂ (WeakDual ℂ X)) :
          Set (WeakDual ℂ X)) := ha
  have he : (WeakAlgebra.weakEquiv e).symm (R a)=
      (WeakAlgebra.weakEquiv e).symm (L a) := by
    have hz := closure_minimal (s := ((s.commutant.toSubalgebra.toSubmodule.map
        (WeakAlgebra.weakEquiv e).symm.toLinearMap : Submodule ℂ (WeakDual ℂ X)) :
          Set (WeakDual ℂ X))) (t := {f : WeakDual ℂ X |
        (WeakAlgebra.weakEquiv e).symm (R (WeakAlgebra.weakEquiv e f)) =
        (WeakAlgebra.weakEquiv e).symm (L (WeakAlgebra.weakEquiv e f))})
      (by
        rintro f ⟨b,hb,rfl⟩
        change (WeakAlgebra.weakEquiv e).symm (R ((WeakAlgebra.weakEquiv e)
          ((WeakAlgebra.weakEquiv e).symm b))) =
          (WeakAlgebra.weakEquiv e).symm (L ((WeakAlgebra.weakEquiv e)
          ((WeakAlgebra.weakEquiv e).symm b)))
        simpa [R,L] using congrArg (WeakAlgebra.weakEquiv e).symm (hb i j).eq) hclosed hm
    change (WeakAlgebra.weakEquiv e).symm (R ((WeakAlgebra.weakEquiv e)
      ((WeakAlgebra.weakEquiv e).symm a))) =
      (WeakAlgebra.weakEquiv e).symm (L ((WeakAlgebra.weakEquiv e)
      ((WeakAlgebra.weakEquiv e).symm a))) at hz
    simpa using hz
  exact (WeakAlgebra.weakEquiv e).symm.injective he

omit [PartialOrder M] [StarOrderedRing M] in
lemma closedCommutant_factor
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))
    (b : closedCommutant e s P hP)
    (hb : ∀ x : closedCommutant e s P hP, Commute b x) :
    ∃ c : ℂ, b=c • (1 : closedCommutant e s P hP) := by
  have hbc : (b:M) ∈ s.commutant := closedCommutant_subset e s P hP b.property
  have hc (a : M) (ha : a ∈ s.commutant) : Commute (b:M) a := by
    exact congrArg Subtype.val (hb ⟨a,mem_closedCommutant e s P hP ha⟩).eq
  obtain ⟨c,hc⟩ := hfactor (b:M) (s.central_in_commutant_is_central (b:M) hbc hc)
  exact ⟨c,Subtype.ext hc⟩

lemma closedCommutant_diffuse (hn : 0 < n) (hdiff : NoMinimalProjections M) :
    NoMinimalProjections (closedCommutant e s P hP) := by
  intro p hp hp0
  have hpM : IsStarProjection (p:M) := hp.map (closedCommutant e s P hP).subtype
  obtain ⟨q,hqQ,hq,hqp,hq0,hqne⟩ := s.commutant_subprojection hdiff ⟨0,hn⟩ hpM
    (closedCommutant_subset e s P hP p.property) (fun h => hp0 (Subtype.ext h))
  let q' : closedCommutant e s P hP := ⟨q,mem_closedCommutant e s P hP hqQ⟩
  refine ⟨q',⟨Subtype.ext hq.isIdempotentElem.eq,Subtype.ext hq.isSelfAdjoint.star_eq⟩,
    hqp,?_,?_⟩
  · intro h; exact hq0 (congrArg Subtype.val h)
  · intro h; exact hqne (congrArg Subtype.val h)

end Closed
end PopaMatrices

open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u v
namespace System
variable {M : Type u} {N : Type v} [CStarAlgebra M] [CStarAlgebra N]
variable {n : ℕ} (s : System n (1:M))

def map (f : M →⋆ₐ[ℂ] N) : System n (1:N) where
  entry i j := f (s.entry i j)
  star_entry i j := by rw [← map_star,s.star_entry]
  mul_entry i j k l := by
    rw [← map_mul,s.mul_entry]
    split_ifs <;> simp only [map_zero]
  sum_diag := by rw [← map_sum,s.sum_diag,map_one]

@[simp] lemma map_entry (f : M →⋆ₐ[ℂ] N) (i j : Fin n) :
    (s.map f).entry i j=f (s.entry i j) := rfl

lemma map_expect (f : M →⋆ₐ[ℂ] N) (x : M) :
    (s.map f).expect (f x)=f (s.expect x) := by
  simp only [expect,sumExpect,map_entry,← map_mul,← map_sum,← Complex.coe_smul,map_smul]

end System

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

lemma preGNS_norm_eq_of_trace {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (σ : A →ₚ[ℂ] ℂ) (f : A →⋆ₐ[ℂ] M) (hf : ∀ a, σ a=τ (f a)) (a : A) :
    ‖σ.toPreGNS a‖=‖τ.toPreGNS (f a)‖ := by
  have ha := congrArg Complex.re (σ.preGNS_norm_sq (σ.toPreGNS a))
  have hb := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS (f a)))
  simp only [← Complex.ofReal_pow,Complex.ofReal_re,PositiveLinearMap.ofPreGNS_toPreGNS] at ha hb
  rw [hf,map_mul,map_star] at ha
  nlinarith [norm_nonneg (σ.toPreGNS a),norm_nonneg (τ.toPreGNS (f a))]

include e hτ htr hfaith h1 hfactor in

theorem extend_energy_decrease (hdiff : NoMinimalProjections M)
    {n : ℕ} (s : System n (1:M)) (hn : 0 < n) (a : M)
    (haτ : τ a=0) (ha : 0 < ‖τ.toPreGNS (s.expect a)‖) :
    ∃ m : ℕ, 0 < m ∧ ∃ t : System m (1:M),
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
  have hnorm (x : Q) : ‖τQ.toPreGNS x‖=‖τ.toPreGNS (x:M)‖ :=
    preGNS_norm_eq_of_trace τ τQ Q.subtype (fun _ => rfl) x
  have hbτ : τQ b=0 := (s.trace_expect hn τ htr a).trans haτ
  have hb : 0 < ‖τQ.toPreGNS b‖ := by rw [hnorm]; exact ha
  obtain ⟨k,hk,r,hr⟩ := PopaQuantization.exists_matrix_energy_decrease eQ τQ
    (WeakAlgebra.inheritedTrace_normal e τ s.commutant hL hR P hP hτ)
    (WeakAlgebra.inheritedTrace_tracial e τ s.commutant hL hR P hP htr)
    (WeakAlgebra.inheritedTrace_faithful e τ s.commutant hL hR P hP hfaith)
    (WeakAlgebra.inheritedTrace_one e τ s.commutant hL hR P hP h1)
    (closedCommutant_factor e s P hP hfactor)
    (closedCommutant_diffuse e s P hP hn hdiff) b hbτ hb
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
end PopaMatrices

end

end OAI
