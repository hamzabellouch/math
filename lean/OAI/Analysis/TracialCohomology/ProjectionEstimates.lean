import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.Partitions
import OAI.Analysis.TracialCohomology.MatrixNorms
import OAI.Analysis.TracialCohomology.RandomSigns

namespace OAI

/-! Projection estimates for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaMatrices.System
open HochschildRigidity PopaQuantization
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (s : PopaMatrices.System n (1:M))

def flatColumn (i0 : Fin n) (a : Fin n → Bool) : M :=
  (Real.sqrt (n:ℝ))⁻¹ • ∑ i, sign (a i) • s.entry i i0

def flatProjection (i0 : Fin n) (a : Fin n → Bool) : M :=
  s.flatColumn i0 a*star (s.flatColumn i0 a)

omit [PartialOrder M] [StarOrderedRing M] in
lemma flatColumn_source (i0 : Fin n) (a : Fin n → Bool) :
    s.flatColumn i0 a*s.entry i0 i0=s.flatColumn i0 a := by
  simp only [flatColumn,smul_mul_assoc,Finset.sum_mul,s.mul_entry,↓reduceIte]

omit [PartialOrder M] [StarOrderedRing M] in
lemma flatColumn_star_mul (i0 : Fin n) (a : Fin n → Bool) :
    star (s.flatColumn i0 a)*s.flatColumn i0 a=s.entry i0 i0 := by
  classical
  have hn : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Fin.pos i0))
  have hs : (Real.sqrt (n:ℝ))⁻¹*(Real.sqrt (n:ℝ))⁻¹*(n:ℝ)=1 := by
    rw [← mul_inv,Real.mul_self_sqrt (Nat.cast_nonneg n),inv_mul_cancel₀ hn]
  have hw : star (∑ i, sign (a i) • s.entry i i0)*(∑ i, sign (a i) • s.entry i i0)=
      (n:ℝ) • s.entry i0 i0 := by
    simp only [star_sum,star_smul,star_trivial,s.star_entry,Finset.sum_mul,
      Finset.mul_sum,smul_mul_assoc,mul_smul_comm,s.mul_entry]
    simp only [smul_ite,smul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,smul_smul,sign_sq,one_smul]
    rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.cast_smul_eq_nsmul]
  rw [flatColumn,star_smul,star_trivial,smul_mul_assoc,mul_smul_comm,hw,
    smul_smul,smul_smul,hs,one_smul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma flatProjection_projection (i0 : Fin n) (a : Fin n → Bool) :
    IsStarProjection (s.flatProjection i0 a) := by
  refine ⟨?_,?_⟩
  · change (s.flatColumn i0 a*star (s.flatColumn i0 a))*(s.flatColumn i0 a*star (s.flatColumn i0 a))=_
    rw [mul_assoc,← mul_assoc (star _),s.flatColumn_star_mul,← mul_assoc,s.flatColumn_source]
    rfl
  · change star (s.flatColumn i0 a*star (s.flatColumn i0 a))=_
    simp only [star_mul,star_star]
    rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma flatColumn_compression (i0 : Fin n) (a : Fin n → Bool) (x : M) :
    star (s.flatColumn i0 a)*x*s.flatColumn i0 a=
      (n:ℝ)⁻¹ • ∑ i, ∑ j, (sign (a i)*sign (a j)) • (s.entry i0 i*x*s.entry j i0) := by
  have hw : star (∑ i, sign (a i) • s.entry i i0)*x*(∑ i, sign (a i) • s.entry i i0)=
      ∑ i, ∑ j, (sign (a i)*sign (a j)) • (s.entry i0 i*x*s.entry j i0) := by
    simp only [star_sum,star_smul,star_trivial,s.star_entry]
    rw [Finset.sum_mul,Finset.sum_mul]
    simp only [Finset.mul_sum,smul_mul_assoc,mul_smul_comm,smul_smul]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [mul_comm]
  rw [flatColumn,star_smul,star_trivial,smul_mul_assoc,smul_mul_assoc,
    mul_smul_comm,hw,smul_smul,← mul_inv,Real.mul_self_sqrt (Nat.cast_nonneg n)]

variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
include htr
omit [StarOrderedRing M] in
lemma flatProjection_trace (h1 : τ 1=1) (i0 : Fin n) (a : Fin n → Bool) :
    τ (s.flatProjection i0 a)=(n:ℂ)⁻¹ := by
  rw [flatProjection,htr,s.flatColumn_star_mul]
  have hh := s.trace_diagonal τ htr i0 1 s.commutant.one_mem
  simp only [mul_one,h1] at hh
  have hn : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Fin.pos i0))
  apply mul_left_cancel₀ hn
  rw [hh,mul_inv_cancel₀ hn]

lemma flatProjection_compression_norm (i0 : Fin n) (a : Fin n → Bool) (x : M) :
    ‖τ.toPreGNS (s.flatProjection i0 a*x*s.flatProjection i0 a)‖=
      ‖τ.toPreGNS (star (s.flatColumn i0 a)*x*s.flatColumn i0 a)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_trace,norm_sq_eq_trace]
  congr 1
  let v := s.flatColumn i0 a
  let p := s.entry i0 i0
  have hv : star v*v=p := s.flatColumn_star_mul i0 a
  have hvp : v*p=v := s.flatColumn_source i0 a
  have hpv : p*star v=star v := by
    have hh := congrArg star hvp
    have hp : star p=p := s.star_entry i0 i0
    simpa only [star_mul,hp] using hh
  change τ (star ((v*star v)*x*(v*star v))*((v*star v)*x*(v*star v)))=
    τ (star (star v*x*v)*(star v*x*v))
  simp only [star_mul,star_star,mul_assoc]
  calc
    _ = τ (v*(star v*(star x*(v*(star v*(v*(star v*(x*(v*star v))))))))) := rfl
    _ = τ (v*(star v*(star x*(v*(p*(star v*(x*(v*star v)))))))) := by rw [← mul_assoc (star v) v,hv]
    _ = τ (v*(star v*(star x*(v*(star v*(x*(v*star v))))))) := by rw [← mul_assoc p (star v),hpv]
    _ = τ (star v*(v*(star v*(star x*(v*(star v*(x*v))))))) := by
      simpa only [mul_assoc] using htr (v*(star v*(star x*(v*(star v*(x*v)))))) (star v)
    _ = τ (star v*(star x*(v*(star v*(x*v))))) := by rw [← mul_assoc (star v) v,hv,← mul_assoc p (star v),hpv]
    _ = _ := rfl
end PopaMatrices.System

open Filter Topology
open scoped ComplexOrder
namespace PopaQuantization
open BoundedHochschild HochschildDiffuse HochschildSakai
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℂ E]

include e
lemma contraction_bound_of_projection_bound (T : M →L[ℂ] E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hp : ∀ p : M, IsStarProjection p → ‖T p‖ ≤ δ)
    (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : ‖T a‖ ≤ δ := by
  have hbound : ∀ n : ℕ, ∀ b : M, 0 ≤ b → b ≤ 1 →
      ‖T b‖ ≤ δ + (1/2:ℝ)^n * ‖T‖ := by
    intro n
    induction n with
    | zero =>
      intro b hb0 hb1
      have h := (T.le_opNorm b).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hb0).mpr hb1))
      simpa only [pow_zero,one_mul] using h.trans (le_add_of_nonneg_left hδ)
    | succ n ih =>
      intro b hb0 hb1
      obtain ⟨p,hp0,h0,h1⟩ := exists_dyadic_projection e b hb0 hb1
      have hh := ih ((2:ℝ) • b-p) h0 h1
      have he : (2:ℝ) • T b=T ((2:ℝ) • b-p)+T p := by
        simp only [map_sub, ← Complex.coe_smul,map_smul]; module
      have hh' := norm_add_le (T ((2:ℝ) • b-p)) (T p)
      rw [← he,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)] at hh'
      have hpp := hp p hp0
      rw [pow_succ]
      nlinarith
  have ht : Tendsto (fun n : ℕ => δ + (1/2:ℝ)^n * ‖T‖) atTop (𝓝 δ) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).mul_const ‖T‖).const_add δ
  exact ge_of_tendsto ht (Eventually.of_forall fun n => hbound n a ha0 ha1)

lemma positive_bound_of_projection_bound (T : M →L[ℂ] E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hp : ∀ p : M, IsStarProjection p → ‖T p‖ ≤ δ)
    (a : M) (ha : 0 ≤ a) : ‖T a‖ ≤ δ*‖a‖ := by
  by_cases ha0 : a=0
  · simp [ha0]
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  let b : M := ‖a‖⁻¹ • a
  have hb0 : 0 ≤ b := smul_nonneg (inv_nonneg.mpr hn.le) ha
  have hbn : ‖b‖=1 := by simp [b,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),hn.ne']
  have hb1 : b ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hb0).mp hbn.le
  have h := contraction_bound_of_projection_bound e T δ hδ hp b hb0 hb1
  have hab : a=‖a‖ • b := by simp [b,smul_smul,hn.ne']
  calc
    ‖T a‖ = ‖a‖*‖T b‖ := by
      conv_lhs => rw [hab]
      rw [← Complex.coe_smul,map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg a)]
    _ ≤ ‖a‖*δ := mul_le_mul_of_nonneg_left h hn.le
    _ = δ*‖a‖ := mul_comm _ _

lemma bound_of_projection_bound (T : M →L[ℂ] E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hp : ∀ p : M, IsStarProjection p → ‖T p‖ ≤ δ) (a : M) :
    ‖T a‖ ≤ 4*δ*‖a‖ := by
  obtain ⟨x,hx0,hxn,hx⟩ := CStarAlgebra.exists_sum_four_nonneg a
  calc
    ‖T a‖ = ‖∑ i : Fin 4, Complex.I^i.val • T (x i)‖ := by rw [hx,map_sum]; simp
    _ ≤ ∑ i : Fin 4, ‖Complex.I^i.val • T (x i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 4, ‖T (x i)‖ := by simp only [norm_smul,norm_pow,Complex.norm_I,one_pow,one_mul]
    _ ≤ ∑ _i : Fin 4, δ*‖a‖ := Finset.sum_le_sum fun i _ =>
      (positive_bound_of_projection_bound e T δ hδ hp (x i) (hx0 i)).trans
        (mul_le_mul_of_nonneg_left (hxn i) hδ)
    _ = 4*δ*‖a‖ := by simp; ring
end PopaQuantization

open Filter Topology
open scoped ComplexOrder
namespace PopaQuantization
open HochschildRigidity BoundedHochschild HochschildDixmier
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

def commutatorMap (h1 : τ 1=1) (b : M) : M →L[ℂ] τ.PreGNS :=
  (TracialUltrapower.traceHilbertMap τ h1).comp
    (((ContinuousLinearMap.mul ℂ M).flip b)-(ContinuousLinearMap.mul ℂ M b))

@[simp] lemma commutatorMap_apply (h1 : τ 1=1) (b a : M) :
    commutatorMap τ h1 b a=τ.toPreGNS (a*b-b*a) := rfl

include e in
lemma scalar_distance_le_projection_commutators (h1 : τ 1=1)
    (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))
    (b : M) (δ : ℝ) (hδ : 0 ≤ δ)
    (hp : ∀ p : M, IsStarProjection p → ‖τ.toPreGNS (p*b-b*p)‖ ≤ δ) :
    ‖τ.toPreGNS (b-(τ b) • (1:M))‖ ≤ 4*δ := by
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
  have hc := scalar_mem_orbit_closure e τ (HochschildSakai.abstract_multiplication_normal e).1
    hτ h1 htr hfaith hfactor b
  have hh := closure_minimal hsub Metric.isClosed_closedBall hc
  have hh' : ‖τ.toPreGNS ((τ b) • (1:M)-b)‖ ≤ 4*δ := by
    simpa only [Metric.mem_closedBall,dist_eq_norm,← map_sub,gnsVector_norm] using hh
  simpa only [map_sub,norm_sub_rev] using hh'

include e in

theorem exists_large_projection_commutator (h1 : τ 1=1)
    (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))
    (b : M) (hbτ : τ b=0) (hb : 0 < ‖τ.toPreGNS b‖) :
    ∃ p : M, IsStarProjection p ∧ ‖τ.toPreGNS b‖/8 < ‖τ.toPreGNS (p*b-b*p)‖ := by
  by_contra h
  push Not at h
  have hh := scalar_distance_le_projection_commutators e τ h1 hτ htr hfaith hfactor b
    (‖τ.toPreGNS b‖/8) (by positivity) h
  simp only [hbτ,zero_smul,sub_zero] at hh
  linarith
end PopaQuantization

open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

lemma projection_norm_sq {p : M} (hp : IsStarProjection p) :
    ‖τ.toPreGNS p‖^2=(τ p).re := by
  have h := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS p))
  simpa only [← Complex.ofReal_pow,Complex.ofReal_re,PositiveLinearMap.ofPreGNS_toPreGNS,
    hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] using h

include e hτ htr hfaith h1 hfactor in

lemma exists_matrix_approximating_projection (hdiff : NoMinimalProjections M)
    {p : M} (hp : IsStarProjection p) (η : ℝ) (hη : 0 < η) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : System n (1:M), ∃ q : M,
      IsStarProjection q ∧ q ≤ p ∧ ‖τ.toPreGNS (p-q)‖^2 < η ∧
      ∀ x : M, Commute (s.expect x) q := by
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt hη
  let n := m+1
  have hn : 0 < n := Nat.succ_pos m
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  let r : ℝ := (τ p).re
  have hr0 : 0 ≤ r := (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).1
  have hr1 : r ≤ 1 := by
    have h := (Complex.nonneg_iff.mp (τ.map_nonneg (sub_nonneg.mpr hp.le_one))).1
    simp only [map_sub,h1,Complex.sub_re,Complex.one_re] at h
    exact sub_nonneg.mp h
  let k := Nat.floor ((n:ℝ)*r)
  have hkR : (k:ℝ) ≤ (n:ℝ)*r := Nat.floor_le (mul_nonneg hnR.le hr0)
  have hk : k ≤ n := Nat.floor_le_of_le (mul_le_of_le_one_right hnR.le hr1)
  have hk1 : (n:ℝ)*r < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have ht : 0 ≤ (k:ℝ)/(n:ℝ) := div_nonneg (Nat.cast_nonneg _) hnR.le
  have htp : (k:ℝ)/(n:ℝ) ≤ (τ p).re := (div_le_iff₀ hnR).mpr (by simpa only [mul_comm] using hkR)
  obtain ⟨q,hq,hqp,hqt⟩ := exists_projection_of_trace τ e
    (HochschildSakai.abstract_multiplication_normal e).1 hτ htr hfaith hdiff hp
    ((k:ℝ)/(n:ℝ)) ht htp
  have hsum : k+(n-k)=n := Nat.add_sub_of_le hk
  have hsumpos : 0 < k+(n-k) := by omega
  obtain ⟨s,hs⟩ := system_containing_rational_projection e τ hτ htr hfaith h1 hfactor
    hdiff k (n-k) hsumpos hq (by simpa only [hsum] using hqt)
  refine ⟨k+(n-k),hsumpos,s,q,hq,hqp,?_,hs⟩
  rw [projection_norm_sq τ ((hq.le_iff_sub hp).mp hqp),map_sub,Complex.sub_re,hqt]
  have hlt : r-(k:ℝ)/(n:ℝ) < 1/(n:ℝ) := by
    apply (lt_div_iff₀ hnR).mpr
    field_simp
    nlinarith
  exact hlt.trans (by simpa only [n,Nat.cast_add,Nat.cast_one] using hm)
end PopaMatrices

end

end OAI
