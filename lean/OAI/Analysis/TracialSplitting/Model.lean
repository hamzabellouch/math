import OAI.Analysis.TracialSplitting.ChallengeDefinitions

namespace OAI

noncomputable section

universe uA uD uE uI uR uX

section

namespace Pureness

open scoped TensorProduct ComplexOrder

universe u v

def IsNuclear (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (B : Type v) [CStarAlgebra B], Subsingleton (CStarAlgebraNorm (A ⊗[ℂ] B))

end Pureness

namespace CurrentMain

section

open Pureness

open scoped ComplexOrder

def RealRankZero (D : Type uD) [CStarAlgebra D] : Prop :=
  ∀ a : D, IsSelfAdjoint a → ∀ ε : ℝ, 0 < ε →
    ∃ b : D, IsSelfAdjoint b ∧ (spectrum ℂ b).Finite ∧ ‖a - b‖ < ε

def traceTwoNorm {D : Type uD} [CStarAlgebra D] [PartialOrder D]
    (τ : TracialState D) (a : D) : ℝ :=
  Real.sqrt (τ.functional (star a * a)).re

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceTwoNorm_eq_gns (τ : TracialState D) (a : D) :
    traceTwoNorm τ a = ‖τ.functional.toPreGNS a‖ := rfl

omit [StarOrderedRing D] in

lemma traceTwoNorm_nonneg (τ : TracialState D) (a : D) :
    0 ≤ traceTwoNorm τ a := Real.sqrt_nonneg _

omit [StarOrderedRing D] in

@[simp] lemma traceTwoNorm_zero (τ : TracialState D) : traceTwoNorm τ 0 = 0 := by
  simp [traceTwoNorm]

omit [StarOrderedRing D] in

@[simp] lemma traceTwoNorm_one (τ : TracialState D) : traceTwoNorm τ 1 = 1 := by
  simp [traceTwoNorm, τ.normalized]

lemma traceTwoNorm_add_le (τ : TracialState D) (a b : D) :
    traceTwoNorm τ (a + b) ≤ traceTwoNorm τ a + traceTwoNorm τ b := by
  simpa only [traceTwoNorm_eq_gns, map_add] using
    norm_add_le (τ.functional.toPreGNS a) (τ.functional.toPreGNS b)

omit [StarOrderedRing D] in

@[simp] lemma traceTwoNorm_star (τ : TracialState D) (a : D) :
    traceTwoNorm τ (star a) = traceTwoNorm τ a := by
  simp only [traceTwoNorm, star_star, τ.tracial a (star a)]

lemma traceTwoNorm_mul_left (τ : TracialState D) (a b : D) :
    traceTwoNorm τ (a * b) ≤ ‖a‖ * traceTwoNorm τ b := by
  let f := τ.functional
  have hop : ‖f.leftMulMapPreGNS a‖ ≤ ‖a‖ := by
    unfold PositiveLinearMap.leftMulMapPreGNS
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  calc
    traceTwoNorm τ (a * b) = ‖f.leftMulMapPreGNS a (f.toPreGNS b)‖ := rfl
    _ ≤ ‖f.leftMulMapPreGNS a‖ * ‖f.toPreGNS b‖ := (f.leftMulMapPreGNS a).le_opNorm _
    _ ≤ ‖a‖ * traceTwoNorm τ b := mul_le_mul_of_nonneg_right hop (norm_nonneg _)

lemma traceTwoNorm_mul_right (τ : TracialState D) (a b : D) :
    traceTwoNorm τ (b * a) ≤ ‖a‖ * traceTwoNorm τ b := by
  calc
    traceTwoNorm τ (b * a) = traceTwoNorm τ (star a * star b) := by
      rw [← star_mul, traceTwoNorm_star]
    _ ≤ ‖star a‖ * traceTwoNorm τ (star b) := traceTwoNorm_mul_left τ _ _
    _ = ‖a‖ * traceTwoNorm τ b := by rw [norm_star, traceTwoNorm_star]

lemma traceTwoNorm_le_norm (τ : TracialState D) (a : D) :
    traceTwoNorm τ a ≤ ‖a‖ := by
  simpa only [mul_one, traceTwoNorm_one] using traceTwoNorm_mul_left τ a 1

lemma trace_norm_le_twoNorm (τ : TracialState D) (a : D) :
    ‖τ.functional a‖ ≤ traceTwoNorm τ a := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (τ.functional.toPreGNS 1)
    (τ.functional.toPreGNS a)
  have hone : ‖τ.functional.toPreGNS 1‖ = 1 := traceTwoNorm_one τ
  simpa only [PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, hone,
    ← traceTwoNorm_eq_gns] using h

lemma trace_norm_le_norm (τ : TracialState D) (a : D) :
    ‖τ.functional a‖ ≤ ‖a‖ :=
  (trace_norm_le_twoNorm τ a).trans (traceTwoNorm_le_norm τ a)

end

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceTwoNorm_neg (τ : Pureness.TracialState D) (a : D) :
    traceTwoNorm τ (-a) = traceTwoNorm τ a := by
  simp only [traceTwoNorm_eq_gns, map_neg, norm_neg]

end CurrentMain

namespace Pureness

open Filter

open scoped Topology NNReal ENNReal

namespace ClosedStarIdeal

variable {D : Type uD} [CStarAlgebra D] (J : ClosedStarIdeal D)

abbrev Quotient := J.ideal.ringCon.Quotient

def quotientMap : D →ₐ[ℂ] J.Quotient := J.ideal.ringCon.mkₐ ℂ

lemma quotientMap_surjective : Function.Surjective J.quotientMap :=
  J.ideal.ringCon.mkₐ_surjective (α := ℂ)

lemma rel_star (u v : D) (h : J.ideal.ringCon u v) :
    J.ideal.ringCon (star u) (star v) := by
  rw [TwoSidedIdeal.rel_iff] at h ⊢
  simpa only [star_sub] using J.star_mem h

instance quotientStar : Star (J.Quotient) where
  star := Quotient.map' star (J.rel_star)

lemma quotientMap_star (u : D) :
    J.quotientMap (star u) = star (J.quotientMap u) := rfl

instance quotientStarRing : StarRing (J.Quotient) where
  star_involutive x := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    rw [← J.quotientMap_star,← J.quotientMap_star,star_star]
  star_mul x y := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    obtain ⟨v,rfl⟩ := J.quotientMap_surjective y
    rw [← map_mul,← J.quotientMap_star,star_mul,map_mul,
      J.quotientMap_star,J.quotientMap_star]
  star_add x y := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    obtain ⟨v,rfl⟩ := J.quotientMap_surjective y
    rw [← map_add,← J.quotientMap_star,star_add,map_add,
      J.quotientMap_star,J.quotientMap_star]

instance quotientStarModule : StarModule ℂ (J.Quotient) where
  star_smul c x := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    rw [← _root_.map_smul,← J.quotientMap_star,star_smul,_root_.map_smul,J.quotientMap_star]

abbrev idealSubmodule : Submodule ℂ (D) :=
  (J.quotientMap).toLinearMap.ker

lemma idealSubmodule_coe :
    (J.idealSubmodule : Set (D)) =
      (J.ideal : Set (D)) := by
  ext u
  change J.quotientMap u = 0 ↔ u ∈ J.ideal
  change (J.ideal).ringCon.mk' u = (J.ideal).ringCon.mk' 0 ↔ _
  exact Quotient.eq

instance idealSubmodule_closed : IsClosed (J.idealSubmodule : Set (D)) := by
  rw [J.idealSubmodule_coe]
  exact J.isClosed

def quotientLinearEquiv :
    (D ⧸ J.idealSubmodule) ≃ₗ[ℂ] J.Quotient :=
  (J.quotientMap).toLinearMap.quotKerEquivOfSurjective (J.quotientMap_surjective)

lemma quotientLinearEquiv_mk (u : D) :
    J.quotientLinearEquiv (Submodule.Quotient.mk u) = J.quotientMap u := rfl

instance quotientNormedAddCommGroup : NormedAddCommGroup (J.Quotient) :=
  NormedAddCommGroup.induced _ _ (J.quotientLinearEquiv).symm
    (J.quotientLinearEquiv).symm.injective

instance quotientNormedSpace : NormedSpace ℂ (J.Quotient) :=
  NormedSpace.induced ℂ _ _ (J.quotientLinearEquiv).symm

def quotientNormEquiv : J.Quotient ≃ₗᵢ[ℂ]
    (D ⧸ J.idealSubmodule) where
  __ := (J.quotientLinearEquiv).symm
  norm_map' _ := rfl

lemma quotientMap_norm_le (u : D) :
    ‖J.quotientMap u‖ ≤ ‖u‖ := by
  change ‖(J.quotientLinearEquiv).symm (J.quotientMap u)‖ ≤ ‖u‖
  rw [← J.quotientLinearEquiv_mk, LinearEquiv.symm_apply_apply]
  exact Submodule.Quotient.norm_mk_le _ u

lemma quotient_norm_lt_rep (x : J.Quotient) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : D, J.quotientMap u = x ∧ ‖u‖ < ‖x‖+ε := by
  obtain ⟨u,hu,hun⟩ := Submodule.Quotient.norm_mk_lt ((J.quotientLinearEquiv).symm x) hε
  refine ⟨u,?_,hun⟩
  apply (J.quotientLinearEquiv).symm.injective
  rw [← J.quotientLinearEquiv_mk,LinearEquiv.symm_apply_apply,hu]

instance quotientCompleteSpace : CompleteSpace (J.Quotient) :=
  (J.quotientNormEquiv).toIsometryEquiv.completeSpace_iff.mpr inferInstance

lemma quotient_norm_mul_le (x y : J.Quotient) : ‖x*y‖ ≤ ‖x‖*‖y‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc := ((Metric.nhds_basis_ball.prod_nhds Metric.nhds_basis_ball).tendsto_iff
    Metric.nhds_basis_ball).mp (continuous_mul.tendsto (‖x‖,‖y‖)) ε hε
  simp only [Set.mem_prod,Metric.mem_ball,and_imp,Prod.forall,Prod.exists] at hc
  obtain ⟨δ,η,⟨hδ,hη⟩,h⟩ := hc
  obtain ⟨u,rfl,hu⟩ := J.quotient_norm_lt_rep x hδ
  obtain ⟨v,rfl,hv⟩ := J.quotient_norm_lt_rep y hη
  simp only [Real.dist_eq,abs_sub_lt_iff] at h
  specialize h ‖u‖ ‖v‖ ⟨by linarith,by linarith [J.quotientMap_norm_le u]⟩
    ⟨by linarith,by linarith [J.quotientMap_norm_le v]⟩
  calc
    _ = ‖J.quotientMap (u*v)‖ := by rw [map_mul]
    _ ≤ ‖u*v‖ := J.quotientMap_norm_le _
    _ ≤ ‖u‖*‖v‖ := norm_mul_le _ _
    _ ≤ _ := by linarith [h.2]

instance quotientNormedRing : NormedRing (J.Quotient) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := J.quotient_norm_mul_le

instance quotientNormedAlgebra : NormedAlgebra ℂ (J.Quotient) where
  norm_smul_le := norm_smul_le

lemma quotient_norm_star (x : J.Quotient) : ‖star x‖ = ‖x‖ := by
  have hle (y : J.Quotient) : ‖star y‖ ≤ ‖y‖ := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨u,rfl,hu⟩ := J.quotient_norm_lt_rep y hε
    rw [← J.quotientMap_star]
    exact (J.quotientMap_norm_le (star u)).trans (by simpa only [norm_star] using hu.le)
  exact le_antisymm (hle x) (by simpa only [star_star] using hle (star x))

instance quotientNormedStarGroup : NormedStarGroup (J.Quotient) where
  norm_star_le x := (J.quotient_norm_star x).le

end ClosedStarIdeal

end Pureness

namespace Pureness.ClosedStarIdeal

open Filter

open scoped Topology NNReal ENNReal

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (J : ClosedStarIdeal D)

def idealStarAlgebra : NonUnitalStarSubalgebra ℂ (D) where
  carrier := J.ideal
  zero_mem' := (J.ideal).zero_mem
  add_mem' := (J.ideal).add_mem
  mul_mem' {u v} _ hv := (J.ideal).mul_mem_left u v hv
  smul_mem' c u hu := by
    change c • u ∈ J.ideal
    rw [Algebra.smul_def]
    exact (J.ideal).mul_mem_left (algebraMap ℂ _ c) u hu
  star_mem' := J.star_mem

instance idealStarAlgebraCompleteSpace : CompleteSpace (J.idealStarAlgebra) :=
  (J.isClosed).completeSpace_coe

instance idealStarAlgebraCStar : NonUnitalCStarAlgebra (J.idealStarAlgebra) where
  norm_mul_self_le u := CStarRing.norm_mul_self_le u.1

instance idealPartialOrder : PartialOrder (J.idealStarAlgebra) :=
  CStarAlgebra.spectralOrder _

instance idealStarOrderedRing : StarOrderedRing (J.idealStarAlgebra) :=
  CStarAlgebra.spectralOrderedRing _

local instance : LE (J.idealStarAlgebra) := (J.idealPartialOrder).toLE

local instance : Preorder (J.idealStarAlgebra) := (J.idealPartialOrder).toPreorder

def idealInclusion : J.idealStarAlgebra →⋆ₙₐ[ℂ] D where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

lemma idealInclusion_nonneg {e : J.idealStarAlgebra} (he : 0 ≤ e) :
    0 ≤ (e : D) :=
  by
    have hs : star (CFC.sqrt e)*CFC.sqrt e = e := by
      rw [(CFC.sqrt_nonneg e).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self e he]
    have hs' := congrArg Subtype.val hs
    rw [← hs']
    exact star_mul_self_nonneg _

lemma norm_one_sub {e : D} (he : 0 ≤ e) (hn : ‖e‖ ≤ 1) :
    ‖1-e‖ ≤ 1 := by
  have he1 : e ≤ 1 := by
    simpa using (CStarAlgebra.norm_le_iff_le_algebraMap e (by norm_num : (0:ℝ) ≤ 1) he).mp hn
  rw [CStarAlgebra.norm_le_iff_le_algebraMap (1-e) (by norm_num : (0:ℝ) ≤ 1) (sub_nonneg.mpr he1)]
  simpa using sub_le_self (1 : D) he

lemma exists_ideal_contraction {w : D} (hw : w ∈ J.ideal)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : D, e ∈ J.ideal ∧ IsSelfAdjoint e ∧
      ‖1-e‖ ≤ 1 ∧ ‖w*(1-e)‖ < ε := by
  let W : J.idealStarAlgebra := ⟨w,hw⟩
  have hl := CStarAlgebra.increasingApproximateUnit (J.idealStarAlgebra)
  have ht := hl.tendsto_mul_left W
  have heps := (Metric.tendsto_nhds.mp ht) ε hε
  obtain ⟨e,hp,hn,hm⟩ := (hl.eventually_nonneg.and (hl.eventually_norm.and heps)).exists
  refine ⟨e.1,e.2,?_,norm_one_sub (J.idealInclusion_nonneg hp) hn,?_⟩
  · exact congrArg Subtype.val hp.isSelfAdjoint
  · change dist (W*e) W < ε at hm
    rw [dist_eq_norm] at hm
    change ‖w*e.1-w‖ < ε at hm
    simpa only [mul_sub,mul_one,← neg_sub (w*e.1) w,norm_neg] using hm

lemma quotient_norm_square_le (x : J.Quotient) :
    ‖x‖*‖x‖ ≤ ‖star x*x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
  obtain ⟨v,hv,hvn⟩ := J.quotient_norm_lt_rep
    (star (J.quotientMap u)*J.quotientMap u) (half_pos hε)
  let w := star u*u-v
  have hw : w ∈ J.ideal := by
    change (J.ideal).ringCon w 0
    apply Quotient.exact
    change J.quotientMap w = J.quotientMap 0
    simp only [w,map_sub,map_mul,J.quotientMap_star,hv,sub_self]
    exact (_root_.map_zero (J.quotientMap)).symm
  obtain ⟨e,he,hestar,hen,hwe⟩ := J.exists_ideal_contraction hw (half_pos hε)
  have heq : J.quotientMap e = 0 := Quotient.sound he
  have hmap : J.quotientMap (u*(1-e)) = J.quotientMap u := by
    simp [map_mul,map_sub,heq]
  have hun := J.quotientMap_norm_le (u*(1-e))
  rw [hmap] at hun
  have hidentity : star (u*(1-e))*(u*(1-e)) =
      (1-e)*v*(1-e)+(1-e)*(w*(1-e)) := by
    simp only [star_mul,star_sub,star_one,hestar.star_eq,w]
    noncomm_ring
  have hterm1 : ‖(1-e)*v*(1-e)‖ ≤ ‖v‖ := by
    calc
      _ ≤ ‖1-e‖*‖v‖*‖1-e‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1*‖v‖*1 := by gcongr
      _ = ‖v‖ := by ring
  have hterm2 : ‖(1-e)*(w*(1-e))‖ < ε/2 := by
    calc
      _ ≤ ‖1-e‖*‖w*(1-e)‖ := norm_mul_le _ _
      _ ≤ 1*‖w*(1-e)‖ := by gcongr
      _ < ε/2 := by simpa using hwe
  calc
    _ ≤ ‖u*(1-e)‖*‖u*(1-e)‖ := mul_self_le_mul_self (norm_nonneg _) hun
    _ = ‖star (u*(1-e))*(u*(1-e))‖ := (CStarRing.norm_star_mul_self (x := u*(1-e))).symm
    _ ≤ ‖(1-e)*v*(1-e)‖+‖(1-e)*(w*(1-e))‖ := by rw [hidentity]; exact norm_add_le _ _
    _ ≤ ‖star (J.quotientMap u)*J.quotientMap u‖+ε := by linarith

instance quotientCStarAlgebra : CStarAlgebra (J.Quotient) where
  norm_mul_self_le := J.quotient_norm_square_le

end Pureness.ClosedStarIdeal

namespace CurrentMain

section

open Pureness

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (τ : I → TracialState D) [Nonempty I]

def familyTwoNorm (a : D) : ℝ := ⨆ i, traceTwoNorm (τ i) a

omit [Nonempty I] in

lemma familyTwoNorm_bdd (a : D) : BddAbove (Set.range (fun i => traceTwoNorm (τ i) a)) :=
  ⟨‖a‖, by rintro _ ⟨i, rfl⟩; exact traceTwoNorm_le_norm (τ i) a⟩

omit [Nonempty I] in

lemma traceTwoNorm_le_family (i : I) (a : D) :
    traceTwoNorm (τ i) a ≤ familyTwoNorm τ a :=
  le_ciSup (familyTwoNorm_bdd τ a) i

lemma familyTwoNorm_nonneg (a : D) : 0 ≤ familyTwoNorm τ a := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact (traceTwoNorm_nonneg (τ i) a).trans (traceTwoNorm_le_family τ i a)

lemma familyTwoNorm_le_norm (a : D) : familyTwoNorm τ a ≤ ‖a‖ :=
  ciSup_le (fun i => traceTwoNorm_le_norm (τ i) a)

@[simp] lemma familyTwoNorm_zero : familyTwoNorm τ 0 = 0 := by
  apply le_antisymm _ (familyTwoNorm_nonneg τ 0)
  simpa only [norm_zero] using familyTwoNorm_le_norm τ 0

lemma familyTwoNorm_add_le (a b : D) :
    familyTwoNorm τ (a + b) ≤ familyTwoNorm τ a + familyTwoNorm τ b := by
  apply ciSup_le
  intro i
  exact (traceTwoNorm_add_le (τ i) a b).trans
    (add_le_add (traceTwoNorm_le_family τ i a) (traceTwoNorm_le_family τ i b))

omit [Nonempty I] in

@[simp] lemma familyTwoNorm_neg (a : D) : familyTwoNorm τ (-a) = familyTwoNorm τ a := by
  simp only [familyTwoNorm, traceTwoNorm_neg]

omit [Nonempty I] in

lemma familyTwoNorm_sub_swap (a b : D) : familyTwoNorm τ (a - b) = familyTwoNorm τ (b - a) := by
  rw [← neg_sub b a, familyTwoNorm_neg]

lemma familyTwoNorm_sub_triangle (a b c : D) :
    familyTwoNorm τ (a - c) ≤ familyTwoNorm τ (a - b) + familyTwoNorm τ (b - c) := by
  convert familyTwoNorm_add_le τ (a - b) (b - c) using 1
  abel_nf

omit [StarOrderedRing D] [Nonempty I] in

@[simp] lemma familyTwoNorm_star (a : D) : familyTwoNorm τ (star a) = familyTwoNorm τ a := by
  simp only [familyTwoNorm, traceTwoNorm_star]

lemma familyTwoNorm_mul_left (a b : D) :
    familyTwoNorm τ (a * b) ≤ ‖a‖ * familyTwoNorm τ b := by
  apply ciSup_le
  intro i
  exact (traceTwoNorm_mul_left (τ i) a b).trans
    (mul_le_mul_of_nonneg_left (traceTwoNorm_le_family τ i b) (norm_nonneg _))

lemma familyTwoNorm_mul_right (a b : D) :
    familyTwoNorm τ (a * b) ≤ familyTwoNorm τ a * ‖b‖ := by
  apply ciSup_le
  intro i
  simpa only [mul_comm] using (traceTwoNorm_mul_right (τ i) b a).trans
    (mul_le_mul_of_nonneg_left (traceTwoNorm_le_family τ i a) (norm_nonneg _))

end

open Pureness Filter

open scoped Topology NNReal ENNReal

instance boundedFamilyProductCStar {X : Type uX} {D : Type uD} [CStarAlgebra D] [Nontrivial D] :
    CStarAlgebra (lp (fun _ : X => D) ∞) where

section UniformNull

variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (τ : I → TracialState D) [Nonempty I]

def IsFamilyNull (F : Filter X) (u : X → D) : Prop :=
  Tendsto (fun n => familyTwoNorm τ (u n)) F (𝓝 0)

lemma isFamilyNull_iff (F : Filter X) (u : X → D) :
    IsFamilyNull τ F u ↔ ∀ ε > 0, ∀ᶠ n in F, familyTwoNorm τ (u n) < ε := by
  simp only [IsFamilyNull, Metric.tendsto_nhds, Real.dist_eq, sub_zero,
    abs_of_nonneg (familyTwoNorm_nonneg τ _)]

lemma isFamilyNull_zero (F : Filter X) : IsFamilyNull τ F (fun _ => 0) := by
  simp only [IsFamilyNull, familyTwoNorm_zero]
  exact tendsto_const_nhds

lemma isFamilyNull_add {F : Filter X} {u v : X → D}
    (hu : IsFamilyNull τ F u) (hv : IsFamilyNull τ F v) :
    IsFamilyNull τ F (fun n => u n + v n) := by
  apply squeeze_zero (fun n => familyTwoNorm_nonneg τ _)
    (fun n => familyTwoNorm_add_le τ _ _)
  simpa only [add_zero] using hu.add hv

omit [Nonempty I] in

lemma isFamilyNull_neg {F : Filter X} {u : X → D}
    (hu : IsFamilyNull τ F u) : IsFamilyNull τ F (fun n => -u n) := by
  simpa only [IsFamilyNull, familyTwoNorm_neg] using hu

omit [StarOrderedRing D] [Nonempty I] in

lemma isFamilyNull_star {F : Filter X} {u : X → D}
    (hu : IsFamilyNull τ F u) : IsFamilyNull τ F (fun n => star (u n)) := by
  simpa only [IsFamilyNull, familyTwoNorm_star] using hu

lemma isFamilyNull_mul_left {F : Filter X} {u v : X → D}
    (hv : IsFamilyNull τ F v) {M : ℝ} (hu : ∀ n, ‖u n‖ ≤ M) :
    IsFamilyNull τ F (fun n => u n * v n) := by
  apply squeeze_zero (fun n => familyTwoNorm_nonneg τ _) (fun n =>
    (familyTwoNorm_mul_left τ _ _).trans
      (mul_le_mul_of_nonneg_right (hu n) (familyTwoNorm_nonneg τ _)))
  simpa only [mul_zero] using hv.const_mul M

lemma isFamilyNull_mul_right {F : Filter X} {u v : X → D}
    (hu : IsFamilyNull τ F u) {M : ℝ} (hv : ∀ n, ‖v n‖ ≤ M) :
    IsFamilyNull τ F (fun n => u n * v n) := by
  apply squeeze_zero (fun n => familyTwoNorm_nonneg τ _) (fun n =>
    (familyTwoNorm_mul_right τ _ _).trans
      (mul_le_mul_of_nonneg_left (hv n) (familyTwoNorm_nonneg τ _)))
  simpa only [zero_mul] using hu.mul_const M

lemma familyNull_isClosed (F : Filter X) :
    IsClosed {u : lp (fun _ : X => D) ∞ | IsFamilyNull τ F (fun n => u n)} := by
  apply isClosed_of_closure_subset
  intro u hu
  change IsFamilyNull τ F (fun n => u n)
  rw [isFamilyNull_iff]
  intro ε hε
  obtain ⟨v,hv,huv⟩ := Metric.mem_closure_iff.mp hu (ε/2) (by linarith)
  have hnear (n : X) : familyTwoNorm τ (u n-v n) < ε/2 :=
    (familyTwoNorm_le_norm τ _).trans_lt
      ((lp.norm_apply_le_norm ENNReal.top_ne_zero (u-v) n).trans_lt
        (by simpa only [dist_eq_norm] using huv))
  have he := (isFamilyNull_iff τ F _).mp hv (ε/2) (by linarith)
  filter_upwards [he] with n hn
  have ht := familyTwoNorm_add_le τ (u n-v n) (v n)
  rw [sub_add_cancel] at ht
  linarith [hnear n]

variable [Nontrivial D]

def familyNullTwoSided (F : Filter X) : TwoSidedIdeal (lp (fun _ : X => D) ∞) :=
  TwoSidedIdeal.mk' {u | IsFamilyNull τ F (fun n => u n)}
    (isFamilyNull_zero τ F)
    (fun hu hv => isFamilyNull_add τ hu hv)
    (fun hu => isFamilyNull_neg τ hu)
    (fun {u _} hv => isFamilyNull_mul_left τ hv
      (lp.norm_apply_le_norm ENNReal.top_ne_zero u))
    (fun {_ v} hu => isFamilyNull_mul_right τ hu
      (lp.norm_apply_le_norm ENNReal.top_ne_zero v))

lemma familyNull_mem (F : Filter X) (u : lp (fun _ : X => D) ∞) :
    u ∈ familyNullTwoSided τ F ↔ IsFamilyNull τ F (fun n => u n) := by
  unfold familyNullTwoSided
  exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ u

lemma familyNull_star (F : Filter X) {u : lp (fun _ : X => D) ∞}
    (hu : u ∈ familyNullTwoSided τ F) : star u ∈ familyNullTwoSided τ F := by
  apply (familyNull_mem τ F (star u)).mpr
  exact isFamilyNull_star τ ((familyNull_mem τ F u).mp hu)

def familyNullIdeal (F : Filter X) : ClosedStarIdeal (lp (fun _ : X => D) ∞) where
  ideal := familyNullTwoSided τ F
  star_mem := familyNull_star τ F
  isClosed := by
    have he : (familyNullTwoSided τ F : Set (lp (fun _ : X => D) ∞)) = {u | IsFamilyNull τ F (fun n => u n)} :=
      Set.ext (familyNull_mem τ F)
    rw [he]
    exact familyNull_isClosed τ F

end UniformNull

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (τ : I → TracialState D) [Nonempty I]

def IsFamilyCauchy (u : ℕ → D) : Prop :=
  IsFamilyNull τ (atTop : Filter (ℕ × ℕ)) (fun p => u p.1 - u p.2)

lemma isFamilyCauchy_const (a : D) : IsFamilyCauchy τ (fun _ => a) := by
  simpa only [IsFamilyCauchy, sub_self] using
    isFamilyNull_zero τ (atTop : Filter (ℕ × ℕ))

lemma isFamilyCauchy_add {u v : ℕ → D} (hu : IsFamilyCauchy τ u)
    (hv : IsFamilyCauchy τ v) : IsFamilyCauchy τ (fun n => u n+v n) := by
  simpa only [IsFamilyCauchy, add_sub_add_comm] using isFamilyNull_add τ hu hv

omit [StarOrderedRing D] [Nonempty I] in

lemma isFamilyCauchy_star {u : ℕ → D} (hu : IsFamilyCauchy τ u) :
    IsFamilyCauchy τ (fun n => star (u n)) := by
  simpa only [IsFamilyCauchy, star_sub] using isFamilyNull_star τ hu

lemma isFamilyCauchy_mul {u v : ℕ → D} (hu : IsFamilyCauchy τ u)
    (hv : IsFamilyCauchy τ v) {M N : ℝ} (hM : ∀ n, ‖u n‖ ≤ M)
    (hN : ∀ n, ‖v n‖ ≤ N) : IsFamilyCauchy τ (fun n => u n*v n) := by
  have h₁ := isFamilyNull_mul_left τ hv (fun p : ℕ × ℕ => hM p.1)
  have h₂ := isFamilyNull_mul_right τ hu (fun p : ℕ × ℕ => hN p.2)
  have he (p : ℕ × ℕ) : u p.1 * (v p.1-v p.2) + (u p.1-u p.2)*v p.2 =
      u p.1*v p.1-u p.2*v p.2 := by noncomm_ring
  simpa only [IsFamilyCauchy, he] using isFamilyNull_add τ h₁ h₂

variable [Nontrivial D]

def familyCauchyAlgebra : StarSubalgebra ℂ (lp (fun _ : ℕ => D) ∞) where
  carrier := {u | IsFamilyCauchy τ (fun n => u n)}
  zero_mem' := isFamilyCauchy_const τ 0
  one_mem' := isFamilyCauchy_const τ 1
  add_mem' hu hv := isFamilyCauchy_add τ hu hv
  mul_mem' {u v} hu hv := isFamilyCauchy_mul τ hu hv
    (lp.norm_apply_le_norm ENNReal.top_ne_zero u)
    (lp.norm_apply_le_norm ENNReal.top_ne_zero v)
  algebraMap_mem' z := isFamilyCauchy_const τ (algebraMap ℂ D z)
  star_mem' hu := isFamilyCauchy_star τ hu

lemma familyCauchyAlgebra_isClosed : IsClosed
    (familyCauchyAlgebra τ : Set (lp (fun _ : ℕ => D) ∞)) := by
  apply isClosed_of_closure_subset
  intro u hu
  change IsFamilyCauchy τ (fun n => u n)
  rw [IsFamilyCauchy, isFamilyNull_iff]
  intro ε hε
  obtain ⟨v,hv,huv⟩ := Metric.mem_closure_iff.mp hu (ε/3) (by linarith)
  have hnear (n : ℕ) : familyTwoNorm τ (u n-v n) < ε/3 :=
    (familyTwoNorm_le_norm τ _).trans_lt
      ((lp.norm_apply_le_norm ENNReal.top_ne_zero (u-v) n).trans_lt
        (by simpa only [dist_eq_norm] using huv))
  have he := (isFamilyNull_iff τ _ _).mp hv (ε/3) (by linarith)
  filter_upwards [he] with p hp
  have h₁ := familyTwoNorm_sub_triangle τ (u p.1) (v p.1) (u p.2)
  have h₂ := familyTwoNorm_sub_triangle τ (v p.1) (v p.2) (u p.2)
  rw [familyTwoNorm_sub_swap τ (v p.2) (u p.2)] at h₂
  linarith [hnear p.1, hnear p.2]

instance familyCauchy_complete : CompleteSpace (familyCauchyAlgebra τ) :=
  (familyCauchyAlgebra_isClosed τ).completeSpace_coe

instance familyCauchy_cstar : CStarAlgebra (familyCauchyAlgebra τ) where

def familyCauchyNullIdeal : ClosedStarIdeal (familyCauchyAlgebra τ) where
  ideal := TwoSidedIdeal.comap (familyCauchyAlgebra τ).val.toRingHom
    (familyNullIdeal τ atTop).ideal
  star_mem := by
    intro u hu
    apply (familyNullIdeal τ atTop).star_mem hu
  isClosed := by
    exact (familyNullIdeal τ atTop).isClosed.preimage
      (continuous_subtype_val : Continuous (fun u : familyCauchyAlgebra τ => u.1))

abbrev UniformTracialCompletion := (familyCauchyNullIdeal τ).Quotient

end CurrentMain

namespace Pureness.ClosedStarIdeal

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

instance quotientOrder (J : ClosedStarIdeal D) : PartialOrder J.Quotient :=
  CStarAlgebra.spectralOrder _

instance quotientStarOrdered (J : ClosedStarIdeal D) : StarOrderedRing J.Quotient :=
  CStarAlgebra.spectralOrderedRing _

variable (J : ClosedStarIdeal D)

variable (τ : TracialState D) (hτ : ∀ a ∈ J.ideal, τ.functional a = 0)

omit [StarOrderedRing D] in

include hτ in

lemma trace_congr (u v : D) (huv : J.ideal.ringCon u v) :
    τ.functional u = τ.functional v := by
  rw [TwoSidedIdeal.rel_iff] at huv
  have h := hτ (u-v) huv
  rw [map_sub, sub_eq_zero] at h
  exact h

def descendedValue : J.Quotient → ℂ := Quotient.lift τ.functional (J.trace_congr τ hτ)

omit [StarOrderedRing D] in

lemma descendedValue_map (u : D) : J.descendedValue τ hτ (J.quotientMap u) = τ.functional u := rfl

def descendedLinear : J.Quotient →ₗ[ℂ] ℂ where
  toFun := J.descendedValue τ hτ
  map_add' x y := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    obtain ⟨v,rfl⟩ := J.quotientMap_surjective y
    rw [← map_add, J.descendedValue_map, J.descendedValue_map, J.descendedValue_map, map_add]
  map_smul' c x := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    rw [← map_smul, J.descendedValue_map, J.descendedValue_map, map_smul]
    rfl

lemma descendedLinear_square_nonneg (x : J.Quotient) :
    0 ≤ J.descendedLinear τ hτ (star x*x) := by
  obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
  change 0 ≤ J.descendedValue τ hτ (star (J.quotientMap u) * J.quotientMap u)
  rw [← J.quotientMap_star, ← map_mul, J.descendedValue_map]
  exact τ.functional.map_nonneg (star_mul_self_nonneg u)

def descendedTrace : TracialState J.Quotient where
  functional := { J.descendedLinear τ hτ with
    monotone' := by
      intro x y hxy
      apply sub_nonneg.mp
      change 0 ≤ J.descendedLinear τ hτ y - J.descendedLinear τ hτ x
      rw [← map_sub]
      obtain ⟨z,hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hxy)
      rw [hz]
      exact J.descendedLinear_square_nonneg τ hτ z }
  normalized := by
    change J.descendedValue τ hτ 1 = 1
    rw [← map_one J.quotientMap, J.descendedValue_map]
    exact τ.normalized
  tracial x y := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    obtain ⟨v,rfl⟩ := J.quotientMap_surjective y
    change J.descendedValue τ hτ (J.quotientMap u * J.quotientMap v) =
      J.descendedValue τ hτ (J.quotientMap v * J.quotientMap u)
    rw [← map_mul, ← map_mul, J.descendedValue_map, J.descendedValue_map]
    exact τ.tracial u v

end Pureness.ClosedStarIdeal

namespace CurrentMain

section

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

lemma bounded_ultrafilter_tendsto {X : Type uX} {E : Type uE} [NormedAddCommGroup E] [ProperSpace E]
    (U : Ultrafilter X) (f : X → E) (M : ℝ) (hM : ∀ n, ‖f n‖ ≤ M) :
    Tendsto f (U : Filter X) (𝓝 (limUnder (U : Filter X) f)) := by
  apply tendsto_nhds_limUnder
  obtain ⟨r,_,hr⟩ := (isCompact_closedBall (0 : E) M).ultrafilter_le_nhds' (U.map f)
    (show Metric.closedBall (0 : E) M ∈ U.map f from by
      change {n | f n ∈ Metric.closedBall (0 : E) M} ∈ U
      exact Filter.Eventually.of_forall (fun n => by simpa using hM n))
  exact ⟨r,hr⟩

section UltraTrace

variable {D : Type uD} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]

variable (θ : X → TracialState D) (U : Ultrafilter X)

instance boundedFamilyProductOrder : PartialOrder (lp (fun _ : X => D) ∞) :=
  CStarAlgebra.spectralOrder _

instance boundedFamilyProductStarOrdered : StarOrderedRing (lp (fun _ : X => D) ∞) :=
  CStarAlgebra.spectralOrderedRing _

def ultraTraceValue (u : lp (fun _ : X => D) ∞) : ℂ :=
  limUnder (U : Filter X) (fun n => (θ n).functional (u n))

omit [Nontrivial D] in

lemma ultraTraceValue_tendsto (u : lp (fun _ : X => D) ∞) :
    Tendsto (fun n => (θ n).functional (u n)) (U : Filter X) (𝓝 (ultraTraceValue θ U u)) :=
  bounded_ultrafilter_tendsto U _ ‖u‖ (fun n =>
    (trace_norm_le_norm (θ n) _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u n))

omit [Nontrivial D] in

lemma ultraTraceValue_add (u v : lp (fun _ : X => D) ∞) :
    ultraTraceValue θ U (u+v) = ultraTraceValue θ U u+ultraTraceValue θ U v := by
  apply tendsto_nhds_unique (ultraTraceValue_tendsto θ U (u+v))
  simpa only [lp.coeFn_add, Pi.add_apply, map_add] using
    (ultraTraceValue_tendsto θ U u).add (ultraTraceValue_tendsto θ U v)

lemma ultraTraceValue_smul (z : ℂ) (u : lp (fun _ : X => D) ∞) :
    ultraTraceValue θ U (z • u) = z • ultraTraceValue θ U u := by
  apply tendsto_nhds_unique (ultraTraceValue_tendsto θ U (z • u))
  simpa only [lp.coeFn_smul, Pi.smul_apply, map_smul, smul_eq_mul] using
    (ultraTraceValue_tendsto θ U u).const_mul z

def ultraTraceLinear : lp (fun _ : X => D) ∞ →ₗ[ℂ] ℂ where
  toFun := ultraTraceValue θ U
  map_add' := ultraTraceValue_add θ U
  map_smul' := ultraTraceValue_smul θ U

def boundedFamilyEval (n : X) : lp (fun _ : X => D) ∞ →⋆ₐ[ℂ] D where
  toFun u := u n
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def ultraTrace : TracialState (lp (fun _ : X => D) ∞) where
  functional := { ultraTraceLinear θ U with
    monotone' := by
      intro u v huv
      exact le_of_tendsto_of_tendsto (ultraTraceValue_tendsto θ U u)
        (ultraTraceValue_tendsto θ U v) (Eventually.of_forall (fun n =>
          (θ n).functional.monotone (map_rel (boundedFamilyEval n) huv))) }
  normalized := by
    apply tendsto_nhds_unique (ultraTraceValue_tendsto θ U 1)
    have he (n : X) : (θ n).functional ((1 : lp (fun _ : X => D) ∞) n) = 1 :=
      (θ n).normalized
    simp only [he]
    exact tendsto_const_nhds
  tracial u v := by
    change ultraTraceValue θ U (u*v) = ultraTraceValue θ U (v*u)
    apply tendsto_nhds_unique (ultraTraceValue_tendsto θ U (u*v))
    have he (n : X) : (θ n).functional ((u*v) n) = (θ n).functional ((v*u) n) :=
      (θ n).tracial (u n) (v n)
    simpa only [he] using ultraTraceValue_tendsto θ U (v*u)

end UltraTrace

variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]

variable (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)

abbrev FamilyUltrapower := (familyNullIdeal τ (U : Filter X)).Quotient

lemma ultraTrace_null (s : X → I) (u : lp (fun _ : X => D) ∞)
    (hu : u ∈ (familyNullIdeal τ (U : Filter X)).ideal) :
    (ultraTrace (fun n => τ (s n)) U).functional u = 0 := by
  have hn : IsFamilyNull τ (U : Filter X) (fun n => u n) :=
    (familyNull_mem τ _ u).mp hu
  have ht : Tendsto (fun n => (τ (s n)).functional (u n)) (U : Filter X) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n =>
      (trace_norm_le_twoNorm (τ (s n)) _).trans (traceTwoNorm_le_family τ (s n) _)) hn
  exact tendsto_nhds_unique (ultraTraceValue_tendsto (fun n => τ (s n)) U u) ht

def familyLimitTrace (s : X → I) : TracialState (FamilyUltrapower τ U) :=
  (familyNullIdeal τ (U : Filter X)).descendedTrace
    (ultraTrace (fun n => τ (s n)) U) (ultraTrace_null τ U s)

end

section

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

section PullbackTrace

variable {D : Type uD} {E : Type uE} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]

def pullbackTrace (τ : TracialState E) (ι : D →⋆ₐ[ℂ] E) : TracialState D where
  functional := { τ.functional.toLinearMap.comp ι.toLinearMap with
    monotone' := fun _ _ h => τ.functional.monotone (map_rel ι h) }
  normalized := by change τ.functional (ι 1) = 1; rw [map_one, τ.normalized]
  tracial x y := by
    change τ.functional (ι (x*y)) = τ.functional (ι (y*x))
    rw [map_mul ι x y, map_mul ι y x]
    exact τ.tracial _ _

end PullbackTrace

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I]

omit [Nontrivial D] in

lemma isFamilyCauchy_iff (u : ℕ → D) : IsFamilyCauchy τ u ↔
    ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, familyTwoNorm τ (u m-u n) < ε := by
  simp only [IsFamilyCauchy, isFamilyNull_iff, eventually_atTop_prod_self]
  constructor <;> intro h ε hε
  · obtain ⟨N,hN⟩ := h ε hε
    exact ⟨N,fun m hm n hn => hN m n hm hn⟩
  · obtain ⟨N,hN⟩ := h ε hε
    exact ⟨N,fun m n hm hn => hN m hm n hn⟩

lemma cauchy_trace_values (i : I) (u : familyCauchyAlgebra τ) :
    CauchySeq (fun n : ℕ => (τ i).functional (u.1 n)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := (isFamilyCauchy_iff τ _).mp u.2 ε hε
  refine ⟨N,fun m hm n hn => ?_⟩
  rw [dist_eq_norm, ← map_sub]
  exact (trace_norm_le_twoNorm (τ i) _).trans_lt
    ((traceTwoNorm_le_family τ i _).trans_lt (hN m hm n hn))

instance familyCauchyOrder : PartialOrder (familyCauchyAlgebra τ) :=
  CStarAlgebra.spectralOrder _

instance familyCauchyStarOrdered : StarOrderedRing (familyCauchyAlgebra τ) :=
  CStarAlgebra.spectralOrderedRing _

def cauchyTrace (i : I) : TracialState (familyCauchyAlgebra τ) :=
  pullbackTrace (ultraTrace (fun _ : ℕ => τ i) (Ultrafilter.of atTop))
    (familyCauchyAlgebra τ).subtype

lemma cauchyTrace_tendsto (i : I) (u : familyCauchyAlgebra τ) :
    Tendsto (fun n : ℕ => (τ i).functional (u.1 n)) atTop
      (𝓝 ((cauchyTrace τ i).functional u)) := by
  obtain ⟨z,hz⟩ := cauchySeq_tendsto_of_complete (cauchy_trace_values τ i u)
  have he : z = (cauchyTrace τ i).functional u := tendsto_nhds_unique
    (hz.mono_left (Ultrafilter.of_le atTop))
    (ultraTraceValue_tendsto (fun _ : ℕ => τ i) (Ultrafilter.of atTop) u.1)
  exact he ▸ hz

lemma cauchyTrace_null (i : I) (u : familyCauchyAlgebra τ)
    (hu : u ∈ (familyCauchyNullIdeal τ).ideal) :
    (cauchyTrace τ i).functional u = 0 := by
  have hmem : u.1 ∈ (familyNullIdeal τ atTop).ideal := hu
  have hn := (familyNull_mem τ atTop u.1).mp hmem
  have ht : Tendsto (fun n : ℕ => (τ i).functional (u.1 n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n =>
      (trace_norm_le_twoNorm (τ i) _).trans (traceTwoNorm_le_family τ i _)) hn
  exact tendsto_nhds_unique (cauchyTrace_tendsto τ i u) ht

def completionTrace (i : I) : TracialState (UniformTracialCompletion τ) :=
  (familyCauchyNullIdeal τ).descendedTrace (cauchyTrace τ i) (cauchyTrace_null τ i)

def boundedFamilyConstant {X : Type uX} (a : D) : lp (fun _ : X => D) ∞ :=
  ⟨fun _ => a, memℓp_infty_iff.mpr ⟨‖a‖,by rintro _ ⟨n,rfl⟩; exact le_rfl⟩⟩

def cauchyConstant (a : D) : familyCauchyAlgebra τ :=
  ⟨boundedFamilyConstant a, isFamilyCauchy_const τ a⟩

def completionMap : D →⋆ₐ[ℂ] UniformTracialCompletion τ where
  toFun a := (familyCauchyNullIdeal τ).quotientMap (cauchyConstant τ a)
  map_zero' := (familyCauchyNullIdeal τ).quotientMap.map_zero
  map_one' := (familyCauchyNullIdeal τ).quotientMap.map_one
  map_add' a b := (familyCauchyNullIdeal τ).quotientMap.map_add (cauchyConstant τ a) (cauchyConstant τ b)
  map_mul' a b := (familyCauchyNullIdeal τ).quotientMap.map_mul (cauchyConstant τ a) (cauchyConstant τ b)
  commutes' z := (familyCauchyNullIdeal τ).quotientMap.commutes z
  map_star' a := (familyCauchyNullIdeal τ).quotientMap_star (cauchyConstant τ a)

end

section

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I]

instance completionNontrivial : Nontrivial (UniformTracialCompletion τ) := by
  obtain ⟨i⟩ := ‹Nonempty I›
  refine ⟨⟨1,0,?_⟩⟩
  intro h
  have he := congrArg (completionTrace τ i).functional h
  rw [(completionTrace τ i).normalized, map_zero] at he
  exact one_ne_zero he

end

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)

def familyUltrapowerMap : D →⋆ₐ[ℂ] FamilyUltrapower τ U where
  toFun a := (familyNullIdeal τ (U : Filter X)).quotientMap (boundedFamilyConstant a)
  map_zero' := (familyNullIdeal τ (U : Filter X)).quotientMap.map_zero
  map_one' := (familyNullIdeal τ (U : Filter X)).quotientMap.map_one
  map_add' a b := (familyNullIdeal τ (U : Filter X)).quotientMap.map_add
    (boundedFamilyConstant a) (boundedFamilyConstant b)
  map_mul' a b := (familyNullIdeal τ (U : Filter X)).quotientMap.map_mul
    (boundedFamilyConstant a) (boundedFamilyConstant b)
  commutes' z := (familyNullIdeal τ (U : Filter X)).quotientMap.commutes z
  map_star' a := (familyNullIdeal τ (U : Filter X)).quotientMap_star (boundedFamilyConstant a)

end CurrentMain

namespace Pureness

open Filter Topology

variable {A : Type uA} [NormedRing A]

def TopologicallySimple (A : Type uA) [NormedRing A] : Prop :=
  ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤

end Pureness

end

namespace CurrentMain

open Pureness Filter

def StablyFinite (A : Type uA) [CStarAlgebra A] : Prop :=
  ∀ n : ℕ, ∀ v : CStarMatrix (Fin n) (Fin n) A,
    star v*v = 1 → v*star v = 1

def UniformPropertyGammaAt (A : Type) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
    [Nonempty (TracialState A)] (U : Ultrafilter ℕ) : Prop :=
  ∃ p : FamilyUltrapower (completionTrace (fun τ : TracialState A => τ)) U,
    IsStarProjection p ∧ ∀ x : UniformTracialCompletion (fun τ : TracialState A => τ),
      p * familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x =
        familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x * p ∧
      ∀ s : ℕ → TracialState A,
        (familyLimitTrace (completionTrace (fun τ : TracialState A => τ)) U s).functional
          (p * familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x) =
        (1/2 : ℂ) *
        (familyLimitTrace (completionTrace (fun τ : TracialState A => τ)) U s).functional
          (familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x)

end CurrentMain

end

end OAI
