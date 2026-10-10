import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalSmooth
import OAI.Geometry.TamingCompatibility.Hodge.HodgeClosedSmooth
import OAI.Geometry.TamingCompatibility.Hodge.HodgeHarmonicRegular

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include D hD in

theorem hodge_harmonic_smooth (u : hodgeEnergy A J α hs ht)
    (hu : hodgeWeakDerivative A J α hs ht u = 0) :
    ∃ b : PreL2 A J α hs ht true, hodgeSmooth A J α hs ht b = u := by
  classical
  choose V hV hxV w hw using hodge_harmonic_weak_patch A J α hs ht D hD u hu
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun x _ => mem_iUnion_of_mem x (hxV x))
  have hc : (univ : Set X) ⊆ ⋃ p : s, V p.val := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hscover hx)
    exact mem_iUnion_of_mem ⟨p,hp⟩ hxp
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun p : s => V p.val) (fun p => hV p.val) hc
  apply hodge_glue_weak_patches A J α hs ht (fun p : s => ρ p) (fun p => (ρ p).contMDiff)
    (fun x => ?_) _ (fun p : s => w p.val) (fun p => hw p.val (ρ p) (ρ p).contMDiff (hρ p))
  simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include D hD in
lemma hodgeSmoothShift_dense (r : ℝ) (hr : 0 < r) :
    DenseRange (fun a : PreL2 A J α hs ht true =>
      smoothL2 A J α hs ht true (hodgeSmoothShift A J α hs ht r a)) := by
  apply (hodgeSmoothShift_cube_dense A J α hs ht D hD r hr).mono
  rintro _ ⟨a,rfl⟩
  refine ⟨(hodgeSmoothShift A J α hs ht r ^ 2) a,?_⟩
  have he (K : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true) :
      (K ^ 3) a = K ((K ^ 2) a) := by rw [show 3 = 2+1 from rfl,pow_succ']; rfl
  dsimp only
  rw [he]

include D hD in
lemma hodgeResolvent_fixed_of_weak_harmonic (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true)
    (hf : ∀ a : PreL2 A J α hs ht true,
      ⟪f,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫ = 0) :
    hodgeResolvent A J α hs ht r f = f := by
  apply ext_inner_right ℝ
  have hsym (u v : L2 A J α hs ht true) :
      ⟪hodgeResolvent A J α hs ht r u,v⟫ = ⟪u,hodgeResolvent A J α hs ht r v⟫ :=
    hodgeResolvent_symmetric A J α hs ht r u v
  have he : (fun y => ⟪hodgeResolvent A J α hs ht r f,y⟫) =
      (fun y : L2 A J α hs ht true => ⟪f,y⟫) :=
    (hodgeSmoothShift_dense A J α hs ht D hD r hr).equalizer
      (continuous_const.inner continuous_id) (continuous_const.inner continuous_id) (by
      funext a
      dsimp only [Function.comp_apply]
      rw [hsym,
        hodgeResolvent_smoothShift A J α hs ht r hr,hodgeSmoothShift_apply,
        map_add,map_smul,inner_add_right,real_inner_smul_right,hf,mul_zero,add_zero])
  exact congrFun he

include D hD in
lemma hodge_weak_harmonic_graph (f : L2 A J α hs ht true)
    (hf : ∀ a : PreL2 A J α hs ht true,
      ⟪f,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫ = 0) :
    ∃ u : hodgeEnergy A J α hs ht,
      hodgeInclusion A J α hs ht u = f ∧ hodgeWeakDerivative A J α hs ht u = 0 := by
  let u := hodgeWeakSolution A J α hs ht 1 zero_lt_one f
  have hfix := hodgeResolvent_fixed_of_weak_harmonic A J α hs ht D hD 1 zero_lt_one f hf
  refine ⟨u,?_,?_⟩
  · rw [hodgeResolvent_eq A J α hs ht 1 zero_lt_one] at hfix
    exact hfix
  · have h := hodgeWeakSolution_identity A J α hs ht 1 zero_lt_one f u
    rw [hfix,one_pow,one_mul,add_eq_left] at h
    exact inner_self_eq_zero.mp h

omit [T2Space X] in
lemma hodgeSmooth_closed_of_weakDerivative_zero (b : PreL2 A J α hs ht true)
    (hb : hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht b) = 0) : IsClosed b.val := by
  apply (hodgeDelta_star_eq_zero_iff A J α hs ht b).mp
  apply (smoothL2 A J α hs ht false).injective
  have h := congrArg (fun z : HodgeDerivativePair A J α hs ht => z.snd) hb
  exact h

include D hD in

theorem hodge_weak_harmonic_smooth (f : L2 A J α hs ht true)
    (hf : ∀ a : PreL2 A J α hs ht true,
      ⟪f,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫ = 0) :
    ∃ b : PreL2 A J α hs ht true, smoothL2 A J α hs ht true b = f ∧ IsClosed b.val := by
  obtain ⟨u,hu,hDu⟩ := hodge_weak_harmonic_graph A J α hs ht D hD f hf
  obtain ⟨b,hb⟩ := hodge_harmonic_smooth A J α hs ht D hD u hDu
  refine ⟨b,?_,?_⟩
  · rw [← hodgeInclusion_smooth,hb,hu]
  · apply hodgeSmooth_closed_of_weakDerivative_zero A J α hs ht b
    rw [hb,hDu]
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def hodgePreClosed : Submodule ℝ (PreL2 A J α hs ht true) where
  carrier := {a | IsClosed a.val}
  zero_mem' := IsClosed.zero
  add_mem' {a b} ha hb := IsClosed.add ha hb a.property b.property
  smul_mem' c _ ha := ha.smul c

def hodgeClosedL2 : Submodule ℝ (L2 A J α hs ht true) :=
  ((hodgePreClosed A J α hs ht).map (smoothL2 A J α hs ht true).toLinearMap).topologicalClosure

def hodgeWeakClosedL2 : Submodule ℝ (L2 A J α hs ht true) where
  carrier := {v | ∀ ξ : PreL2 A J α hs ht false, ⟪v,l2Star A J α hs ht (testDerivative A J α hs ht ξ)⟫ = 0}
  zero_mem' := by intro ξ; exact inner_zero_left _
  add_mem' hv hw := by intro ξ; rw [inner_add_left,hv ξ,hw ξ,add_zero]
  smul_mem' c _ hv := by intro ξ; rw [real_inner_smul_left,hv ξ,mul_zero]

omit [T2Space X] in
lemma hodgeWeakClosedL2_isClosed : _root_.IsClosed (hodgeWeakClosedL2 A J α hs ht : Set (L2 A J α hs ht true)) := by
  change _root_.IsClosed {v : L2 A J α hs ht true | ∀ ξ : PreL2 A J α hs ht false,
    ⟪v,l2Star A J α hs ht (testDerivative A J α hs ht ξ)⟫ = 0}
  simp only [ofPred_forall]
  exact isClosed_iInter (fun _ => isClosed_eq (continuous_id.inner continuous_const) continuous_const)

omit [T2Space X] in
lemma hodgeSmooth_mem_weakClosed (a : PreL2 A J α hs ht true) (ha : IsClosed a.val) :
    smoothL2 A J α hs ht true a ∈ hodgeWeakClosedL2 A J α hs ht := by
  intro ξ
  rw [← smoothL2_preD,l2Star_smooth,(smoothL2 A J α hs ht true).inner_map_map,
    real_inner_comm,preStar_self_adjoint,hodgePreD_adjoint,
    (hodgeDelta_star_eq_zero_iff A J α hs ht a).mpr ha,inner_zero_right]

omit [T2Space X] in
lemma hodgeSmooth_mem_closedL2 (a : PreL2 A J α hs ht true) (ha : IsClosed a.val) :
    smoothL2 A J α hs ht true a ∈ hodgeClosedL2 A J α hs ht :=
  subset_closure ⟨a,ha,rfl⟩

omit [T2Space X] in
lemma hodgeClosedL2_le_weakClosed : hodgeClosedL2 A J α hs ht ≤ hodgeWeakClosedL2 A J α hs ht := by
  apply Submodule.topologicalClosure_minimal _ ?_ (hodgeWeakClosedL2_isClosed A J α hs ht)
  rintro _ ⟨a,ha,rfl⟩
  exact hodgeSmooth_mem_weakClosed A J α hs ht a ha

include D hD in
lemma hodge_closed_orthogonal_zero (v : L2 A J α hs ht true)
    (hv : v ∈ hodgeWeakClosedL2 A J α hs ht)
    (ho : v ∈ (hodgeClosedL2 A J α hs ht)ᗮ) : v = 0 := by
  have hh : ∀ a : PreL2 A J α hs ht true,
      ⟪v,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫ = 0 := by
    intro a
    have he := ho (smoothL2 A J α hs ht true (hodgePreD A J α hs ht (hodgeDelta A J α hs ht a)))
      (hodgeSmooth_mem_closedL2 A J α hs ht _ (hodgePreD_closed A J α hs ht _))
    rw [real_inner_comm] at he
    rw [hodgeLaplacian_apply,map_add,inner_add_right,he,zero_add,← l2Star_smooth,smoothL2_preD]
    exact hv _
  obtain ⟨b,hb,hbc⟩ := hodge_weak_harmonic_smooth A J α hs ht D hD v hh
  have h := ho (smoothL2 A J α hs ht true b) (hodgeSmooth_mem_closedL2 A J α hs ht b hbc)
  rw [hb] at h
  exact inner_self_eq_zero.mp h

include D hD in

theorem hodgeClosedL2_eq_weakClosed : hodgeClosedL2 A J α hs ht = hodgeWeakClosedL2 A J α hs ht := by
  let C := hodgeClosedL2 A J α hs ht
  let W := hodgeWeakClosedL2 A J α hs ht
  have hC : _root_.IsClosed (C : Set (L2 A J α hs ht true)) :=
    Submodule.isClosed_topologicalClosure _
  let : CompleteSpace C := hC.completeSpace_coe
  have hb : Cᗮ ⊓ W = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    exact (Submodule.mem_bot ℝ).mpr (hodge_closed_orthogonal_zero A J α hs ht D hD v hv.2 hv.1)
  have h := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (hodgeClosedL2_le_weakClosed A J α hs ht)
  change C ⊔ Cᗮ ⊓ W = W at h
  rwa [hb,sup_bot_eq] at h

include D hD in

theorem hodge_pair_weakClosed_eq_zero (U V : L2 A J α hs ht true)
    (hU : ∀ a : PreL2 A J α hs ht true, IsClosed a.val → ⟪U,smoothL2 A J α hs ht true a⟫ = 0)
    (hV : V ∈ hodgeWeakClosedL2 A J α hs ht) : ⟪U,V⟫ = 0 := by
  have ho : U ∈ (hodgeClosedL2 A J α hs ht)ᗮ := by
    rw [hodgeClosedL2,Submodule.orthogonal_closure]
    rintro _ ⟨a,ha,rfl⟩
    rw [real_inner_comm]
    exact hU a ha
  rw [← hodgeClosedL2_eq_weakClosed A J α hs ht D hD] at hV
  rw [real_inner_comm]
  exact ho V hV
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
