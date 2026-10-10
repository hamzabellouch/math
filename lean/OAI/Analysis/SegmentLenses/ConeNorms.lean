import OAI.Analysis.SegmentLenses.ConeBlocks

namespace OAI

/-!
# Cone norms, separated families, and level forests
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex

namespace SegmentEmbedding
variable {V W : Type*} [DecidableEq V] [DecidableEq W] [SegmentSystem V] [SegmentSystem W]

theorem primalEquivOfSurjective_eq_map (e : SegmentEmbedding (V := V) (W := W))
    (he : Function.Surjective e.toEmbedding) (x : Primal V) :
    e.primalEquivOfSurjective he x = e.primalMap x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (e.primalEquivOfSurjective he).continuous e.primalMap.continuous) ?_
  intro u
  rw [e.primalEquivOfSurjective_test,e.primalMap_test]

end SegmentEmbedding

section ConeNorms
open scoped Classical ENNReal
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]


def coneDual (g : V) (z : FullDual V) : FullDual (ConeVertex g) :=
  z.comp (coneEmbedding g).primalMap



theorem cone_inclusion_composition (H : Finset V) (hH : Ancestral (· ≤ ·) H)
    (g : {g // Gate H g}) (u : Primal (ConeVertex g.val)) :
    (exteriorEmbedding H hH).primalMap
      ((ComponentPartition.regionEmbedding (exteriorPartition H) g).primalMap
        (coneBlockEquiv H hH g u)) = (coneEmbedding g.val).primalMap u := by
  have he : coneBlockEquiv H hH g u = (coneBlockEmbedding H hH g).primalMap u :=
    SegmentEmbedding.primalEquivOfSurjective_eq_map _ _ _
  rw [he]
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq ((exteriorEmbedding H hH).primalMap.continuous.comp
      ((ComponentPartition.regionEmbedding (exteriorPartition H) g).primalMap.continuous.comp
        (coneBlockEmbedding H hH g).primalMap.continuous)) (coneEmbedding g.val).primalMap.continuous) ?_
  intro v
  rw [test_as_sum v]
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w hw
  rw [SegmentEmbedding.primalMap_unitVector, SegmentEmbedding.primalMap_unitVector,
    SegmentEmbedding.primalMap_unitVector,SegmentEmbedding.primalMap_unitVector]
  rfl

@[simp] theorem exteriorConeDual_apply (H : Finset V) (hH : Ancestral (· ≤ ·) H)
    (z : FullDual V) (g : {g // Gate H g}) :
    exteriorConeDualL2Equiv H hH (exteriorDual H hH z) g = coneDual g.val z := by
  apply ContinuousLinearMap.ext
  intro u
  change ComponentPartition.regionDualL2Equiv (exteriorPartition H)
    (exteriorDual H hH z) g (coneBlockEquiv H hH g u) = _
  rw [ComponentPartition.regionDualL2Equiv_apply]
  change z ((exteriorEmbedding H hH).primalMap
    ((ComponentPartition.regionEmbedding (exteriorPartition H) g).primalMap
      (coneBlockEquiv H hH g u))) = z ((coneEmbedding g.val).primalMap u)
  rw [cone_inclusion_composition]




theorem complementary_cone_norm (H : Finset V) (hH : Ancestral (· ≤ ·) H) (z : FullDual V) :
    ‖tail H z‖^2 = ∑' g : {g // Gate H g}, ‖coneDual g.val z‖^2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (exteriorConeDualL2Equiv H hH (exteriorDual H hH z))
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
    norm_exteriorDual, exteriorConeDual_apply] using h



theorem exterior_range_eq_tail (H : Finset V) (hH : Ancestral (· ≤ ·) H) :
    (exteriorEmbedding H hH).primalIsometry.range = (primalTail H).range := by
  ext x
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨(exteriorEmbedding H hH).primalMap u,primalTail_exterior H hH u⟩
  · rintro ⟨u,rfl⟩
    exact ⟨(exteriorEmbedding H hH).primalRestriction u,exterior_primalTail H hH u⟩

def exteriorToTailEquiv (H : Finset V) (hH : Ancestral (· ≤ ·) H) :
    Primal (ExteriorVertex H) ≃ₗᵢ[ℝ] (primalTail H).range :=
  (exteriorEmbedding H hH).primalIsometry.equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (exterior_range_eq_tail H hH))



def complementary_cone_isometry (H : Finset V) (hH : Ancestral (· ≤ ·) H) :
    (primalTail H).range ≃ₗᵢ[ℝ] L2Sum (fun g : {g // Gate H g} => Primal (ConeVertex g.val)) :=
  (exteriorToTailEquiv H hH).symm.trans (exteriorConeL2Equiv H hH)

end ConeNorms





theorem infinite_separated_family {D : ℝ} (hD : 1 ≤ D) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : BInfinite) (z : ℕ → BInfinite),
      1 ≤ ‖x‖ → ‖x‖ ≤ D → (∀ i, ‖z i‖ ≤ 2*D) →
      (∀ i j, i ≠ j → 1 ≤ ‖z i-z j‖) →
      ∃ i, ‖x‖+c < max ‖x+z i‖ ‖x-z i‖ := by
  classical
  exact separated_predual_family (V := InfiniteVertex) hD



theorem forest_separated_family {D : ℝ} (hD : 1 ≤ D) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : X) (z : ℕ → X),
      1 ≤ ‖x‖ → ‖x‖ ≤ D → (∀ i, ‖z i‖ ≤ 2*D) →
      (∀ i j, i ≠ j → 1 ≤ ‖z i-z j‖) →
      ∃ i, ‖x‖+c < max ‖x+z i‖ ‖x-z i‖ := by
  classical
  obtain ⟨c,hc,h⟩ := separated_predual_family (V := ForestVertex) hD
  refine ⟨c,hc,?_⟩
  intro x z hx hxD hz hsep
  have hmem : ∀ w : X, w ∈ coordinateSpan ForestVertex := by
    intro w
    rw [forest_coordinateSpan_eq_top]
    trivial
  exact h ⟨x,hmem x⟩ (fun i => ⟨z i,hmem (z i)⟩) hx hxD hz hsep



section SingletonPrimal
variable {V : Type*} [Unique V] [SegmentSystem V]


def singletonTestEquiv : Test V ≃ₗᵢ[ℝ] ℝ where
  toFun u := u.coeff default
  invFun c := Test.ofFinsupp (Finsupp.single default c)
  left_inv u := by
    apply Finsupp.ext
    intro v
    have hv : v = default := Subsingleton.elim _ _
    subst v
    simp [Test.coeff,Test.ofFinsupp]
  right_inv c := by simp [Test.coeff,Test.ofFinsupp]
  map_add' u v := rfl
  map_smul' c u := rfl
  norm_map' u := by
    change ‖u.coeff default‖ = ‖u‖
    have he : u = u.coeff default • Test.ofFinsupp (Finsupp.single default 1) := by
      apply Finsupp.ext
      intro v
      change u.coeff v = (u.coeff default • Finsupp.single default 1 : V →₀ ℝ) v
      have hv : v = default := Subsingleton.elim _ _
      subst v
      change u.coeff default = u.coeff default * (Finsupp.single default (1:ℝ)) default
      simp
    conv_rhs => rw [he,norm_smul,norm_test_unit,mul_one]

def singletonPrimalEquiv : Primal V ≃ₗᵢ[ℝ] ℝ :=
  (singletonTestEquiv (V := V)).toLinearEquiv.extendOfIsometry
    (UniformSpace.Completion.toComplL : Test V →L[ℝ] Primal V).toLinearMap
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
    UniformSpace.Completion.denseRange_coe (by exact denseRange_id)
    (fun u => by
      change ‖singletonTestEquiv u‖ = ‖(u : Primal V)‖
      rw [UniformSpace.Completion.norm_coe,LinearIsometryEquiv.norm_map])

@[simp] theorem singletonPrimalEquiv_test (u : Test V) :
    singletonPrimalEquiv (u : Primal V) = u.coeff default := by
  change singletonPrimalEquiv ((UniformSpace.Completion.toComplL : Test V →L[ℝ] Primal V) u) = _
  unfold singletonPrimalEquiv
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ u

end SingletonPrimal


def realDualEquiv : StrongDual ℝ ℝ ≃ₗᵢ[ℝ] ℝ where
  toFun f := f 1
  invFun c := c • ContinuousLinearMap.id ℝ ℝ
  left_inv f := by
    apply ContinuousLinearMap.ext
    intro x
    have h := f.map_smul x (1:ℝ)
    simpa [mul_comm] using h.symm
  right_inv c := by simp
  map_add' f g := rfl
  map_smul' c f := rfl
  norm_map' f := by
    change ‖f 1‖ = ‖f‖
    apply le_antisymm
    · simpa using f.le_opNorm (1:ℝ)
    · apply f.opNorm_le_bound (norm_nonneg _)
      intro x
      have h := f.map_smul x (1:ℝ)
      simp only [smul_eq_mul,mul_one] at h
      rw [h,norm_mul,mul_comm]


def RealSum2Fiber (E : Type) : Bool → Type
  | false => ℝ
  | true => E

instance realSum2FiberGroup (E : Type) [NormedAddCommGroup E] :
    (b : Bool) → NormedAddCommGroup (RealSum2Fiber E b)
  | false => inferInstanceAs (NormedAddCommGroup ℝ)
  | true => inferInstanceAs (NormedAddCommGroup E)

instance realSum2FiberSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (b : Bool) → NormedSpace ℝ (RealSum2Fiber E b)
  | false => inferInstanceAs (NormedSpace ℝ ℝ)
  | true => inferInstanceAs (NormedSpace ℝ E)

instance realSum2FiberComplete (E : Type) [NormedAddCommGroup E] [CompleteSpace E] :
    (b : Bool) → CompleteSpace (RealSum2Fiber E b)
  | false => inferInstanceAs (CompleteSpace ℝ)
  | true => inferInstanceAs (CompleteSpace E)



abbrev RealSum2 (E : Type) [NormedAddCommGroup E] := L2Sum (RealSum2Fiber E)

theorem realSum2_norm_sq {E : Type} [NormedAddCommGroup E] (u : RealSum2 E) :
    ‖u‖^2 = ‖u false‖^2 + ‖u true‖^2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num : 0 < (2 : ℝ≥0∞).toReal) u
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,tsum_fintype,Fintype.sum_bool,add_comm] using h

namespace Levels
open scoped Classical



abbrev Vertex := IndexedForest.Vertex (fun h : ℕ => h)
abbrev J := Primal Vertex
abbrev X := FullDual Vertex

def partition : ComponentPartition (V := Vertex) (I := Bool) where
  index v := decide (v.val.1 ≠ 0)
  comparable := by intro v w hvw; simp only [hvw.1]

abbrev RootBlock := ComponentPartition.BlockVertex partition false
abbrev ForestBlock := ComponentPartition.BlockVertex partition true

def root : RootBlock := ⟨⟨(0,[]),by simp⟩,by simp [partition]⟩

instance : Unique RootBlock where
  default := root
  uniq v := by
    have hi : v.val.val.1 = 0 := by
      have h : decide (v.val.val.1 ≠ 0) = false := v.property
      exact not_not.mp (of_decide_eq_false h)
    have hw : v.val.val.2 = [] := by
      have h := v.val.property
      change v.val.val.2.length ≤ v.val.val.1 at h
      rw [hi] at h
      exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hi hw



def forestOrderEmbedding : ForestVertex ↪o ForestBlock where
  toFun v := ⟨⟨v.val,v.property.2⟩,by
    change decide (v.val.1 ≠ 0) = true
    have hh := v.property.1
    exact decide_eq_true (by omega : v.val.1 ≠ 0)⟩
  inj' := by intro v w h; exact Subtype.ext (congrArg (fun q : ForestBlock => q.val.val) h)
  map_rel_iff' := Iff.rfl

theorem forestOrderEmbedding_surjective : Function.Surjective forestOrderEmbedding := by
  intro v
  have hi : v.val.val.1 ≠ 0 := by
    have h : decide (v.val.val.1 ≠ 0) = true := v.property
    exact of_decide_eq_true h
  refine ⟨⟨v.val.val,⟨by omega,v.val.property⟩⟩,?_⟩
  rfl

def forestEmbedding : SegmentEmbedding (V := ForestVertex) (W := ForestBlock) :=
  convexSegmentEmbedding forestOrderEmbedding (fun {_ _ v} _ _ _ _ => forestOrderEmbedding_surjective v)

def forestBlockEquiv : SegmentLenses.J ≃ₗᵢ[ℝ] Primal ForestBlock :=
  forestEmbedding.primalEquivOfSurjective forestOrderEmbedding_surjective


def primalSplit : J ≃ₗᵢ[ℝ] RealSum2 SegmentLenses.J :=
  (ComponentPartition.regionL2Equiv partition).trans
    (l2Congr (fun b => by
      cases b
      · exact singletonPrimalEquiv (V := RootBlock)
      · exact forestBlockEquiv.symm))


def dualSplit : X ≃ₗᵢ[ℝ] RealSum2 SegmentLenses.X :=
  (ComponentPartition.regionDualL2Equiv partition).trans
    (l2Congr (fun b => by
      cases b
      · exact (dualTransport (singletonPrimalEquiv (V := RootBlock))).trans realDualEquiv
      · exact dualTransport forestBlockEquiv.symm))

end Levels




end SegmentLenses


end

end OAI
