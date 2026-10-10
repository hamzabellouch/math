import Mathlib
import OAI.Probability.SKGap.Localization.EqualityCurve
import OAI.Probability.SKGap.Entropy.EntropyTestBoundQPos

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace SKGap
end SKGap

namespace SKGap
open Filter
open scoped Topology

end SKGap

namespace SKGap
open Filter
open scoped Topology

end SKGap

namespace SKGap
open Filter
open scoped Topology

end SKGap

namespace SKGap

end SKGap

open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace SKGap

end SKGap

namespace SKGap

end SKGap

namespace SKGap

lemma scalar_consistency {j : ℝ} {p : ScalarPoint} (ht : 0 ≤ p.2.1) :
    j*scalarQMoment p.1 ≤ scalarS j p := by
  unfold scalarS
  nlinarith [sq_nonneg p.2.2]

lemma scalarPsi_eq_entropy {R j : ℝ} {p : ScalarPoint}
    (hp : p ∈ scalarMomentDomain R) (hs : 0 ≤ scalarS j p) :
    scalarPsi j p = scalarEntropyTarget (p.1 : Measure ℝ) j (scalarD j p) (scalarS j p).toNNReal := by
  simp only [scalarPsi, scalarEntropyTarget, Real.coe_toNNReal _ hs, scalarA_eq hp, scalarQMoment]

lemma scalar_weak_test {R j : ℝ} {p : ScalarPoint}
    (hp : p ∈ scalarMomentDomain R) (hj : 0 < j) (hj1 : j < 1)
    (ht : 0 ≤ p.2.1) (hs : 0 < scalarS j p) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ →ᵇ ℝ, scalarPsi j p-(∫ y, f y ∂p.1)+
      log (∫ y, exp (f y) ∂gaussianReal (scalarD j p) (scalarS j p).toNNReal) < ε := by
  by_contra hh
  push Not at hh
  have hD : EntropyTestBound (p.1 : Measure ℝ)
      (gaussianReal (scalarD j p) (scalarS j p).toNNReal) (scalarPsi j p-ε) := by
    intro f
    linarith [hh f]
  have hcons : j * (∫ y, tanh y^2 ∂p.1) ≤ ((scalarS j p).toNNReal : ℝ) := by
    rw [Real.coe_toNNReal _ hs.le]
    exact scalar_consistency ht
  have h := (test_scalar_inequality (momentBall_integrable hp.1) hj hj1
    (ne_of_gt (Real.toNNReal_pos.mpr hs)) hcons hD).1
  change scalarEntropyTarget (p.1 : Measure ℝ) j (scalarD j p) (scalarS j p).toNNReal ≤ _ at h
  rw [← scalarPsi_eq_entropy hp hs.le] at h
  linarith

lemma scalar_strict_test {R j : ℝ} {p : ScalarPoint}
    (hp : p ∈ scalarMomentDomain R) (hj : 0 < j) (hj1 : j < 1)
    (ht : 0 ≤ p.2.1) (hs : 0 < scalarS j p)
    (hne : (p.1 : Measure ℝ) ≠ gaussianReal (scalarD j p) (scalarS j p).toNNReal) :
    ∃ f : ℝ →ᵇ ℝ, scalarPsi j p-(∫ y, f y ∂p.1)+
      log (∫ y, exp (f y) ∂gaussianReal (scalarD j p) (scalarS j p).toNNReal) < 0 := by
  have hcons : j * (∫ y, tanh y^2 ∂p.1) ≤ ((scalarS j p).toNNReal : ℝ) := by
    rw [Real.coe_toNNReal _ hs.le]
    exact scalar_consistency ht
  obtain ⟨f,hf⟩ := scalar_strict_witness (momentBall_integrable hp.1) hj hj1
    (ne_of_gt (Real.toNNReal_pos.mpr hs)) hcons hne
  rw [← scalarPsi_eq_entropy hp hs.le] at hf
  exact ⟨f, by linarith⟩

lemma scalar_gaussian_curve {j : ℝ} {p : ScalarPoint}
    (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ p.2.1)
    (hσ : p.2.2 = 0) (hs : 0 ≤ scalarS j p)
    (hP : (p.1 : Measure ℝ) = gaussianReal (scalarD j p) (scalarS j p).toNNReal) :
    p.1 = scalarCurve j p.2.1 := by
  have hd : scalarD j p = p.2.1+j*(∫ y, tanh y ∂gaussianReal (scalarD j p) (scalarS j p).toNNReal) := by
    rw [← hP]
    rfl
  have hv : ((scalarS j p).toNNReal : ℝ) =
      p.2.1+j*(∫ y, tanh y^2 ∂gaussianReal (scalarD j p) (scalarS j p).toNNReal) := by
    rw [Real.coe_toNNReal _ hs, ← hP]
    simp [scalarS, scalarQMoment, hσ]
  obtain ⟨hd',hs'⟩ := consistent_gaussian_unique hj hj1 ht hd hv
  rw [Real.coe_toNNReal _ hs] at hs'
  apply ProbabilityMeasure.toMeasure_injective
  change (p.1 : Measure ℝ) = gaussianReal (scalarFixedPoint j p.2.1) (scalarFixedPoint j p.2.1).toNNReal
  rw [hP, hd', hs']

lemma continuousOn_scalar_test {R j : ℝ} (hR : 0 ≤ R) (hj : 0 ≤ j)
    (f : ℝ →ᵇ ℝ) : ContinuousOn (fun p : ScalarPoint =>
      scalarPsi j p-(∫ y, f y ∂p.1)+scalarLogMoment f (scalarD j p) (scalarS j p))
      (scalarMomentDomain R ∩ {p | 0 < scalarS j p}) := by
  have hψ : ContinuousOn (scalarPsi j)
      (scalarMomentDomain R ∩ {p | 0 < scalarS j p}) := (continuousOn_scalarPsi hR j).mono (by
        intro p hp
        refine ⟨hp.1,hp.2.ne',ne_of_gt ?_⟩
        exact add_pos_of_pos_of_nonneg hp.2 (mul_nonneg hj (scalarQMoment_bounds p.1).1))
  exact (hψ.sub ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp
    continuous_fst).continuousOn).add
    ((continuous_scalarLogMoment f).comp ((continuous_scalarD j).prodMk (continuous_scalarS j))).continuousOn

end SKGap

noncomputable section
open Set Filter Topology
namespace SKGap

lemma finite_pos_lower_bound {X : Type*} (C : Finset X) (a : X → ℝ)
    (ha : ∀ x ∈ C, 0 < a x) : ∃ ε > 0, ∀ x ∈ C, ε ≤ a x := by
  classical
  induction C using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | insert x C hx ih =>
    obtain ⟨ε,hε,he⟩ := ih (fun y hy => ha y (Finset.mem_insert_of_mem hy))
    refine ⟨min (a x) ε, lt_min (ha x (Finset.mem_insert_self _ _)) hε, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (he y hy)

theorem compact_strict_witness {X F : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (w : F → X → ℝ) (hw : ∀ f, ContinuousOn (w f) K)
    (hW : ∀ x ∈ K, ∃ f, w f x < 0) :
    ∃ a > 0, ∀ x ∈ K, ∃ f, w f x < -a := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  choose f hf using fun x : K => hW x.1 x.2
  let a (x : K) := -(w (f x) x)/2
  have ha (x : K) : 0 < a x := by dsimp [a]; linarith [hf x]
  let U (x : K) : Set K := {z | w (f x) z < -a x}
  have hU (x : K) : IsOpen (U x) := isOpen_lt (hw (f x)).domRestrict continuous_const
  have hcov : (univ : Set K) ⊆ ⋃ x, U x := by
    intro x _
    apply mem_iUnion.mpr
    refine ⟨x,?_⟩
    change w (f x) x < -a x
    dsimp [a]
    linarith [hf x]
  obtain ⟨C,hC⟩ := isCompact_univ.elim_finite_subcover U hU hcov
  obtain ⟨ε,hε,he⟩ := finite_pos_lower_bound C a (fun x _ => ha x)
  refine ⟨ε,hε,?_⟩
  intro z hz
  obtain ⟨x,hx⟩ := mem_iUnion.mp (hC (mem_univ (⟨z,hz⟩ : K)))
  obtain ⟨hxC,hxz⟩ := mem_iUnion.mp hx
  refine ⟨f x,?_⟩
  change w (f x) z < -a x at hxz
  linarith [he x hxC]

lemma compact_zero_fiber_neighborhood {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {σ : X → ℝ} (hσ : Continuous σ) (hnn : ∀ x, 0 ≤ σ x)
    {U : Set X} (hU : IsOpen U) (hzero : ∀ x, σ x = 0 → x ∈ U) :
    ∃ δ > 0, ∀ x, σ x ≤ δ → x ∈ U := by
  by_cases he : Uᶜ = ∅
  · refine ⟨1,by norm_num,?_⟩
    intro x _
    by_contra hx
    have hx' : x ∈ Uᶜ := hx
    simp only [he, mem_empty_iff_false] at hx'
  obtain ⟨x,hx,hmin⟩ := hU.isClosed_compl.isCompact.exists_isMinOn (nonempty_iff_ne_empty.mpr he) hσ.continuousOn
  have hxpos : 0 < σ x := lt_of_le_of_ne (hnn x) (by
    intro hh
    exact hx (hzero x hh.symm))
  refine ⟨σ x/2,by positivity,?_⟩
  intro y hy
  by_contra hny
  have h : σ x ≤ σ y := hmin hny
  linarith

theorem compact_small_noise_witness {X F : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (w : F → X → ℝ) (hw : ∀ f, ContinuousOn (w f) K)
    {σ : X → ℝ} (hσ : ContinuousOn σ K) (hnn : ∀ x ∈ K, 0 ≤ σ x)
    (hW : ∀ x ∈ K, σ x = 0 → ∃ f, w f x < 0) :
    ∃ a > 0, ∃ δ > 0, ∀ x ∈ K, σ x ≤ δ → ∃ f, w f x < -a := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Z : Set K := {x | σ x = 0}
  have hZ : IsCompact Z := (isClosed_eq hσ.domRestrict continuous_const).isCompact
  obtain ⟨a,ha,hA⟩ := compact_strict_witness hZ (fun f (x : K) => w f x)
    (fun f => (hw f).domRestrict.continuousOn) (fun x hx => hW x.1 x.2 hx)
  let U : Set K := {x | ∃ f, w f x < -(a/2)}
  have hU : IsOpen U := by
    have hu : U = ⋃ f : F, {x : K | w f x < -(a/2)} := by ext x; simp [U]
    rw [hu]
    exact isOpen_iUnion (fun f => isOpen_lt (hw f).domRestrict continuous_const)
  have hzU (x : K) (hx : σ x = 0) : x ∈ U := by
    obtain ⟨f,hf⟩ := hA x hx
    exact ⟨f,by linarith⟩
  obtain ⟨δ,hδ,hd⟩ := compact_zero_fiber_neighborhood hσ.domRestrict
    (fun x : K => hnn x.1 x.2) hU hzU
  exact ⟨a/2,by positivity,δ,hδ,fun x hx hσx => hd ⟨x,hx⟩ hσx⟩

end SKGap

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction

end
end
end
end
end
end

end OAI
