import Mathlib
import OAI.Analysis.BoundedHochschild.WeakSubspaces

namespace OAI

/-! Weak-star continuity of the involution and its predual action. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open Filter Topology
open scoped ComplexOrder
namespace HochschildSakai
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma imag_square (a : M) (t : ℝ) :
    star (1+Complex.I • (t • a))*(1+Complex.I • (t • a))=
      1+t • (Complex.I • (a-star a))+(t^2) • (star a*a) := by
  have ht : star t=t := rfl
  have hi : star Complex.I = -Complex.I := by simp
  simp only [star_add,star_one,star_smul,ht,hi]
  simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm]
  simp only [smul_add,smul_sub,neg_smul]
  match_scalars <;> ring_nf
  all_goals simp

omit [PartialOrder M] [StarOrderedRing M] in
lemma norm_one_bound : ‖(1:M)‖ ≤ 1 := by
  nontriviality M
  simp

omit [PartialOrder M] [StarOrderedRing M] in
lemma norm_imag_add_sq (a : M) (ha : IsSelfAdjoint a) (t : ℝ) :
    ‖(1:M)+Complex.I • (t • a)‖^2 ≤ 1+t^2*‖a‖^2 := by
  rw [pow_two,← CStarRing.norm_star_mul_self,imag_square,ha.star_eq,sub_self,
    smul_zero,smul_zero,add_zero]
  calc
    ‖(1:M)+t^2 • (a*a)‖ ≤ ‖(1:M)‖+‖t^2 • (a*a)‖ := norm_add_le _ _
    _ ≤ 1+t^2*‖a‖^2 := by
      rw [norm_smul,Real.norm_of_nonneg (sq_nonneg _),ha.norm_mul_self]
      exact add_le_add (norm_one_bound (M := M)) le_rfl

lemma imag_linear_bound (a : M) (C : ℝ)
    (h : ∀ t : ℝ, ‖(1:M)+Complex.I • (t • a)‖^2 ≤ 1+t^2*C) (t : ℝ) :
    t • (Complex.I • (a-star a)) ≤ algebraMap ℝ M (t^2*C) := by
  have hn := CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := (1:M)+Complex.I • (t • a))
  have hh := hn.trans (algebraMap_mono M (h t))
  rw [imag_square] at hh
  have hp : 0 ≤ t^2 • (star a*a) := smul_nonneg (sq_nonneg _) (star_mul_self_nonneg a)
  have h := (le_add_of_nonneg_right hp).trans hh
  simpa only [map_add,map_one,add_le_add_iff_left] using h

 

theorem isSelfAdjoint_of_norm_imag_add (a : M) (C : ℝ)
    (h : ∀ t : ℝ, ‖(1:M)+Complex.I • (t • a)‖^2 ≤ 1+t^2*C) :
    IsSelfAdjoint a := by
  let b := Complex.I • (a-star a)
  have hb (t : ℝ) (ht : 0 < t) : b ≤ algebraMap ℝ M (t*C) := by
    have hh := imag_linear_bound a C h t
    have heq : algebraMap ℝ M (t^2*C)=t • algebraMap ℝ M (t*C) := by
      rw [Algebra.smul_def,← map_mul]
      congr 1
      ring
    rw [heq] at hh
    exact (smul_le_smul_iff_of_pos_left ht).mp hh
  have hnb (t : ℝ) (ht : 0 < t) : -b ≤ algebraMap ℝ M (t*C) := by
    have hh := imag_linear_bound a C h (-t)
    have heq : algebraMap ℝ M ((-t)^2*C)=t • algebraMap ℝ M (t*C) := by
      rw [Algebra.smul_def,← map_mul]
      congr 1
      ring
    rw [heq,neg_smul,← smul_neg] at hh
    exact (smul_le_smul_iff_of_pos_left ht).mp hh
  have hb0 : b ≤ 0 := by
    have ht : Tendsto (fun t : ℝ => algebraMap ℝ M (t*C)) (𝓝[>] 0) (𝓝 0) := by
      have ht : Tendsto (fun t : ℝ => t*C) (𝓝[>] 0) (𝓝 (0*C)) :=
        ((continuousAt_id (x := (0:ℝ))).mul_const C).tendsto.mono_left inf_le_left
      simpa only [zero_mul,map_zero,Function.comp_def] using
        (continuous_algebraMap ℝ M).continuousAt.tendsto.comp ht
    exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with t ht using hb t ht)
  have hn0 : -b ≤ 0 := by
    have ht : Tendsto (fun t : ℝ => algebraMap ℝ M (t*C)) (𝓝[>] 0) (𝓝 0) := by
      have ht : Tendsto (fun t : ℝ => t*C) (𝓝[>] 0) (𝓝 (0*C)) :=
        ((continuousAt_id (x := (0:ℝ))).mul_const C).tendsto.mono_left inf_le_left
      simpa only [zero_mul,map_zero,Function.comp_def] using
        (continuous_algebraMap ℝ M).continuousAt.tendsto.comp ht
    exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with t ht using hnb t ht)
  have hz : b=0 := le_antisymm hb0 (neg_nonpos.mp hn0)
  have ha : a-star a=0 := (smul_eq_zero.mp hz).resolve_left Complex.I_ne_zero
  exact (sub_eq_zero.mp ha).symm

end HochschildSakai

 

open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

 

theorem isSelfAdjoint_of_predual_tendsto {a : I → M} {l : Filter I} [l.NeBot]
    {b : M} (C : ℝ) (_hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (hsa : ∀ i, IsSelfAdjoint (a i)) (ht : PredualTendsto e a l b) :
    IsSelfAdjoint b := by
  let := CStarAlgebra.spectralOrder M
  let := CStarAlgebra.spectralOrderedRing M
  apply isSelfAdjoint_of_norm_imag_add b (C^2)
  intro t
  have htC : 0 ≤ 1+t^2*C^2 := by positivity
  have hnorm (i : I) : ‖(1:M)+Complex.I • (t • a i)‖ ≤ Real.sqrt (1+t^2*C^2) := by
    apply (Real.le_sqrt (norm_nonneg _) htC).mpr
    exact (norm_imag_add_sq (a i) (hsa i) t).trans (by
      gcongr
      exact ha i)
  have htw : PredualTendsto e (fun i => (1:M)+Complex.I • (t • a i)) l
      ((1:M)+Complex.I • (t • b)) := by
    simp only [← Complex.coe_smul]
    exact predual_tendsto_add e (predual_tendsto_const e 1 l)
      (predual_tendsto_smul e (predual_tendsto_smul e ht (t:ℂ)) Complex.I)
  exact (Real.le_sqrt (norm_nonneg _) htC).mp
    (predual_norm_le e _ (Real.sqrt_nonneg _) (Eventually.of_forall hnorm) htw)

lemma star_eq_of_sum_sub_selfAdjoint (a b : M)
    (hadd : IsSelfAdjoint (a+b)) (hsub : IsSelfAdjoint (Complex.I • (a-b))) :
    b=star a := by
  have h1 := hadd.star_eq
  have h2 := hsub.star_eq
  simp only [star_add] at h1
  have h3 : -(star a-star b)=a-b := by
    apply (smul_right_injective M Complex.I_ne_zero)
    simpa only [star_smul,star_sub,Complex.star_def,map_sub,map_id,Complex.conj_I,
      neg_smul,smul_neg] using h2
  have h4 : (2:ℂ) • (b-star a)=0 := by
    have h3' : star b-star a=a-b := by simpa only [neg_sub] using h3
    calc
      (2:ℂ) • (b-star a) = (a+b-(star a+star b)) - (a-b-(star b-star a)) := by module
      _ = 0 := by rw [h1,h3']; simp
  exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_left (by norm_num))

 

theorem predual_tendsto_star_bounded {a : I → M} {l : Filter I}
    {b : M} (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (ht : PredualTendsto e a l b) :
    PredualTendsto e (fun i => star (a i)) l (star b) := by
  intro z
  rw [Filter.tendsto_iff_ultrafilter]
  intro u hu
  have htu : PredualTendsto e a (u : Filter I) b := fun x => (ht x).mono_left hu
  obtain ⟨c,_,hc⟩ := exists_predual_ultralimit e u (fun i => star (a i)) C
    (fun i => by simpa only [norm_star] using ha i)
  have hadd : IsSelfAdjoint (b+c) :=
    isSelfAdjoint_of_predual_tendsto e (2*C) (by positivity)
      (fun i => (norm_add_le (a i) (star (a i))).trans (by
        simpa only [norm_star,two_mul] using add_le_add (ha i) (ha i)))
      (fun i => by simp only [IsSelfAdjoint,star_add,star_star,add_comm])
      (predual_tendsto_add e htu hc)
  have hsub : IsSelfAdjoint (Complex.I • (b-c)) :=
    isSelfAdjoint_of_predual_tendsto e (2*C) (by positivity)
      (fun i => by
        rw [norm_smul,Complex.norm_I,one_mul]
        exact (norm_sub_le (a i) (star (a i))).trans (by
          simpa only [norm_star,two_mul] using add_le_add (ha i) (ha i)))
      (fun i => by simp [IsSelfAdjoint,star_smul,Complex.conj_I,sub_eq_add_neg,add_comm])
      (predual_tendsto_smul e (predual_tendsto_sub e htu hc) Complex.I)
  have hc' := star_eq_of_sum_sub_selfAdjoint b c hadd hsub
  exact hc' ▸ hc z

end HochschildSakai

 

open Filter Topology
namespace HochschildSakai
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

 

theorem mem_predual_of_bounded_weak_continuity [CompleteSpace X]
    (F : StrongDual ℂ (StrongDual ℂ X))
    (hF : ∀ (a : Finset X → StrongDual ℂ X),
      (∀ s, ‖a s‖ ≤ 1) →
      (∀ x, Tendsto (fun s => a s x) atTop (𝓝 0)) →
      Tendsto (fun s => F (a s)) atTop (𝓝 0)) :
    ∃ x : X, ∀ f : StrongDual ℂ X, F f=f x := by
  classical
  let : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
  let : NormedAddCommGroup (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
  let j := NormedSpace.inclusionInDoubleDual ℂ X
  let j₀ : X →ₗ[ℂ] Module.Dual ℂ (StrongDual ℂ X) :=
    (ContinuousLinearMap.coeLM ℂ).comp j.toLinearMap
  have hsmall (ε : ℝ) (hε : 0 < ε) : ∃ s : Finset X,
      ∀ f : StrongDual ℂ X, ‖f‖ ≤ 1 → (∀ x ∈ s, f x=0) → ‖F f‖ ≤ ε := by
    by_contra h
    push Not at h
    choose a ha haz hFa using h
    have ha0 (x : X) : Tendsto (fun s => a s x) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      apply Filter.eventually_atTop.mpr
      refine ⟨{x},fun s hs => ?_⟩
      exact (haz s x (hs (Finset.mem_singleton_self x))).symm
    have hh := (hF a ha ha0).norm.eventually (gt_mem_nhds (show ‖(0:ℂ)‖ < ε by simpa only [norm_zero] using hε))
    obtain ⟨s,hs⟩ := hh.exists
    exact (not_lt_of_ge (le_of_lt hs)) (hFa s)
  have happ (ε : ℝ) (hε : 0 < ε) : ∃ x : X, ‖F-j x‖ ≤ ε := by
    obtain ⟨s,hs⟩ := hsmall ε hε
    let W : Submodule ℂ (Module.Dual ℂ (StrongDual ℂ X)) :=
      Submodule.span ℂ (j₀ '' (s : Set X))
    have hfin : (j₀ '' (s : Set X)).Finite := s.finite_toSet.image j₀
    let : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ hfin
    let K : Submodule ℂ (StrongDual ℂ X) := W.dualCoannihilator
    let : NormedAddCommGroup K := inferInstance
    let : NormedSpace ℂ K := inferInstance
    let FK : StrongDual ℂ K := F.comp K.subtypeL
    have hFK : ‖FK‖ ≤ ε := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
      intro f hf
      apply hs f hf.le
      intro x hx
      have hmem : j₀ x ∈ W := Submodule.subset_span ⟨x,hx,rfl⟩
      exact ((Submodule.mem_dualCoannihilator (Φ := W) f.val).mp f.property) (j₀ x) hmem
    obtain ⟨G,hG,hGn⟩ := _root_.exists_extension_norm_eq K FK
    have hmem : (F-G).toLinearMap ∈ W := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)]
      apply (Submodule.mem_dualAnnihilator _).mpr
      intro f hf
      change F f-G f=0
      exact sub_eq_zero.mpr (hG ⟨f,hf⟩).symm
    have hle : W ≤ LinearMap.range j₀ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x,_,rfl⟩
      exact ⟨x,rfl⟩
    obtain ⟨x,hx⟩ := hle hmem
    have hx' : j x=F-G := by
      ext f
      exact LinearMap.congr_fun hx f
    refine ⟨x,?_⟩
    rw [hx']
    calc
      ‖F-(F-G)‖ = ‖G‖ := congrArg norm (sub_sub_cancel F G)
      _ = ‖FK‖ := hGn
      _ ≤ ε := hFK

  have hclosed : IsClosed (Set.range j) :=
    (NormedSpace.inclusionInDoubleDualLi ℂ (E := X)).isometry.isClosedEmbedding.isClosed_range
  have hmem : F ∈ closure (Set.range j) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨x,hx⟩ := happ (ε/2) (half_pos hε)
    refine ⟨j x,⟨x,rfl⟩,?_⟩
    rw [dist_eq_norm]
    exact hx.trans_lt (half_lt_self hε)
  obtain ⟨x,hx⟩ := hclosed.closure_eq ▸ hmem
  exact ⟨x,fun f => by rw [← hx]; rfl⟩

end HochschildSakai

 

open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

 

theorem exists_star_predual_vector (z : X) :
    ∃ w : X, ∀ a : M, e.symm (star a) z = star (e.symm a w) := by
  let : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
  let L : StrongDual ℂ X →ₗ[ℂ] ℂ :=
    { toFun := fun f => star (e.symm (star (e f)) z)
      map_add' := by intro f g; simp
      map_smul' := by intro r f; simp [map_smulₛₗ] }
  have hb (f : StrongDual ℂ X) : ‖L f‖ ≤ ‖z‖ * ‖f‖ := by
    change ‖star (e.symm (star (e f)) z)‖ ≤ _
    rw [norm_star,mul_comm]
    simpa only [e.symm.norm_map,norm_star,e.norm_map] using
      (e.symm (star (e f))).le_opNorm z
  let F := L.mkContinuous ‖z‖ hb
  have hF (a : Finset X → StrongDual ℂ X) (ha : ∀ s, ‖a s‖ ≤ 1)
      (hta : ∀ x, Tendsto (fun s => a s x) atTop (𝓝 0)) :
      Tendsto (fun s => F (a s)) atTop (𝓝 0) := by
    have ht : PredualTendsto e (fun s => e (a s)) atTop 0 := by
      intro x
      simpa using hta x
    have hs := predual_tendsto_star_bounded e 1 zero_le_one
      (fun s => by simpa only [e.norm_map] using ha s) ht
    simpa [F,L] using (hs z).star
  obtain ⟨w,hw⟩ := mem_predual_of_bounded_weak_continuity F hF
  refine ⟨w,fun a => ?_⟩
  have hh := congrArg star (hw (e.symm a))
  simpa [F,L] using hh

 

theorem predual_tendsto_star {a : I → M} {l : Filter I} {b : M}
    (ha : PredualTendsto e a l b) :
    PredualTendsto e (fun i => star (a i)) l (star b) := by
  intro z
  obtain ⟨w,hw⟩ := exists_star_predual_vector e z
  simpa only [hw] using (ha w).star

end HochschildSakai
end

end OAI
