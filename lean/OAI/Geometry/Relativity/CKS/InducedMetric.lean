import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.BoundaryCharts
import OAI.Geometry.Relativity.CKS.SurfaceVolume

namespace OAI

noncomputable section
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
namespace CKSInducedArea
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass
  real_id_isometric

section Trivializations
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] tangent_manifold_one

attribute [local instance] tangent_vectorBundle

omit [IsManifold I ∞ M] in
attribute [local instance] scalar_smulCommClass

attribute [local instance] scalar_vectorBundle

attribute [local instance] scalar_continuousSMul

attribute [local instance] covector_vectorBundle

omit [IsManifold I ∞ M] in
attribute [local instance] covector_topologicalAddGroup

omit [IsManifold I ∞ M] in
attribute [local instance] covector_continuousSMul

attribute [local instance] OAI.CKSInducedArea.scalarAtlas

attribute [local instance] covector_atlas

@[simp] lemma bilinearTriv_baseSet (e : Trivialization E (π E (fun x : M => TangentSpace I x)))
    [MemTrivializationAtlas e] : (bilinearTriv I e).baseSet = e.baseSet := by
  simp [bilinearTriv]
lemma bilinearTriv_pair (e : Trivialization E (π E (fun x : M => TangentSpace I x)))
    [MemTrivializationAtlas e] {x : M} (hx : x ∈ e.baseSet)
    (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (v w : E) :
    ((bilinearTriv I e) ⟨x,B⟩).2 v w = B (e.symmL ℝ x v) (e.symmL ℝ x w) := by
  unfold bilinearTriv
  rw [Trivialization.continuousLinearMap_apply]
  dsimp only [ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
    (e.continuousLinearMap (RingHom.id ℝ) (Trivial.trivialization M ℝ))
    (show x ∈ (e.continuousLinearMap (RingHom.id ℝ) (Trivial.trivialization M ℝ)).baseSet by simpa using hx)]
  rw [Trivialization.continuousLinearMap_apply]
  dsimp only [ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
    (Trivial.trivialization M ℝ) (show x ∈ (Trivial.trivialization M ℝ).baseSet from mem_univ x)]
  rfl
end Trivializations

attribute [local instance] OAI.CKSInducedArea.bilNorm2

attribute [local instance] OAI.CKSInducedArea.bilSpace2

attribute [local instance] OAI.CKSInducedArea.bilNorm3

attribute [local instance] OAI.CKSInducedArea.bilSpace3

attribute [local instance] OAI.CKSInducedArea.mixNorm23

attribute [local instance] OAI.CKSInducedArea.mixSpace23

attribute [local instance] OAI.CKSInducedArea.mixNorm32

attribute [local instance] OAI.CKSInducedArea.mixSpace32

omit [IsManifold I2 ∞ S] in
lemma bilinearComp_smoothAt [IsManifold I2 ∞ S]
    {B : S → Bil3} {A : S → E2 →L[ℝ] E3} {x : S}
    (hB : ContMDiffAt I2 𝓘(ℝ,Bil3) ∞ B x)
    (hA : ContMDiffAt I2 𝓘(ℝ,E2 →L[ℝ] E3) ∞ A x) :
    ContMDiffAt I2 𝓘(ℝ,Bil2) ∞ (fun y => (B y).bilinearComp (A y) (A y)) x := by
  have flip1 : ContDiff ℝ ∞ (fun B : E2 →L[ℝ] E3 →L[ℝ] ℝ => B.flip) :=
    by
      let L : (E2 →L[ℝ] E3 →L[ℝ] ℝ) →L[ℝ] (E3 →L[ℝ] E2 →L[ℝ] ℝ) :=
        (ContinuousLinearMap.flipₗᵢ ℝ E2 E3 ℝ).toContinuousLinearEquiv.toContinuousLinearMap
      exact L.contDiff
  have flip2 : ContDiff ℝ ∞ (fun B : Bil2 => B.flip) :=
    by
      let L : Bil2 →L[ℝ] Bil2 :=
        (ContinuousLinearMap.flipₗᵢ ℝ E2 E2 ℝ).toContinuousLinearEquiv.toContinuousLinearMap
      exact L.contDiff
  exact flip2.comp_contMDiffAt ((flip1.comp_contMDiffAt (hB.clm_comp hA)).clm_comp hA)

lemma inducedInner_smooth (g : Smooth3 (I3 := I3) (N := N)) {φ : S → N}
    (hφ : ContMDiff I2 I3 ∞ φ) :
    ContMDiff I2 (I2.prod 𝓘(ℝ,Bil2)) ∞
      (fun x => TotalSpace.mk' Bil2 x (inducedInner g φ x)) := by
  let := real_id_isometric
  let := real_smulCommClass
  intro x
  let e := trivializationAt E2 (TangentSpace I2) x
  let e' := trivializationAt E3 (TangentSpace I3) (φ x)
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E2 (TangentSpace I2) x
  have hx' : φ x ∈ e'.baseSet := mem_baseSet_trivializationAt E3 (TangentSpace I3) (φ x)
  apply ((bilinearTriv I2 e).contMDiffAt_section_iff (IB := I2) (n := ∞)
    (F := Bil2) (s := inducedInner g φ) (by simpa using hx)).mpr
  have hB := ((bilinearTriv I3 e').contMDiffAt_section_iff (IB := I3) (n := ∞)
    (F := Bil3) (s := g.inner) (by simpa using hx')).mp (g.contMDiff (φ x))
  have hD := (hφ x).mfderiv_const (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  apply (bilinearComp_smoothAt (hB.comp x (hφ x)) hD).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx,
    hφ.continuous.continuousAt.preimage_mem_nhds (e'.open_baseSet.mem_nhds hx')] with y hy hy'
  ext v w
  rw [bilinearTriv_pair I2 e hy]
  rw [ContinuousLinearMap.bilinearComp_apply]
  dsimp only [Function.comp_apply]
  rw [bilinearTriv_pair I3 e' hy']
  dsimp [inducedInner,inTangentCoordinates,ContinuousLinearMap.inCoordinates]
  rw [e'.symmL_continuousLinearMapAt hy', e'.symmL_continuousLinearMapAt hy']
  rfl

lemma positive_bilinear_bounded (B : Bil2) (hB : ∀ v : E2, v ≠ 0 → 0 < B v v) :
    IsVonNBounded ℝ {v : E2 | B v v < 1} := by
  have hc : Continuous (fun v : E2 => B v v) := B.continuous.clm_apply continuous_id
  obtain ⟨a,ha,hm⟩ := (isCompact_sphere (0 : E2) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)) hc.continuousOn
  have haNorm : ‖a‖ = 1 := by simpa [Metric.mem_sphere] using ha
  have ha0 : a ≠ 0 := by intro h; simp [h] at haNorm
  have hp : 0 < B a a := hB a ha0
  have hlow : ∀ v : E2, B a a * ‖v‖ ^ 2 ≤ B v v := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hy : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have h := hm (show (‖v‖⁻¹ : ℝ) • v ∈ Metric.sphere (0 : E2) 1 by
      simpa [Metric.mem_sphere] using hy)
    have he : B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) = B v v / ‖v‖^2 := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      field_simp
    change B a a ≤ B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) at h
    rw [he] at h
    exact (le_div_iff₀ (sq_pos_of_pos hn)).mp h
  apply (NormedSpace.isVonNBounded_iff ℝ).mpr
  apply (Metric.isBounded_iff_subset_ball (0 : E2)).mpr
  refine ⟨1 + (B a a)⁻¹, ?_⟩
  intro v hv
  change dist v 0 < 1 + (B a a)⁻¹
  rw [dist_zero_right]
  have hbv : B v v < 1 := hv
  have hl := hlow v
  have hinv : 0 < (B a a)⁻¹ := inv_pos.mpr hp
  have he : B a a * (B a a)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  by_contra hh
  have hn : 1 + (B a a)⁻¹ ≤ ‖v‖ := le_of_not_gt hh
  have hn1 : 1 ≤ ‖v‖ := by linarith
  have hn2 : ‖v‖ ≤ ‖v‖^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hn hp.le
  have hmul2 := mul_le_mul_of_nonneg_left hn2 hp.le
  nlinarith

omit [IsManifold I2 ∞ S] in
lemma inducedInner_symm (metric : Smooth3 (I3 := I3) (N := N)) (immersion : S → N)
    (point : S) (left right : TangentSpace I2 point) :
    inducedInner metric immersion point left right = inducedInner metric immersion point right left :=
  metric.symm (immersion point) _ _

omit [IsManifold I2 ∞ S] in
lemma inducedInner_pos (metric : Smooth3 (I3 := I3) (N := N)) (immersion : S → N)
    (injective : ∀ point, Function.Injective (mfderiv I2 I3 immersion point))
    (point : S) (vector : TangentSpace I2 point) (nonzero : vector ≠ 0) :
    0 < inducedInner metric immersion point vector vector :=
  metric.pos (immersion point) _
    (fun zero => nonzero (injective point (zero.trans (map_zero _).symm)))

omit [IsManifold I2 ∞ S] in
lemma inducedInner_bounded (metric : Smooth3 (I3 := I3) (N := N)) (immersion : S → N)
    (injective : ∀ point, Function.Injective (mfderiv I2 I3 immersion point)) (point : S) :
    IsVonNBounded ℝ {vector : TangentSpace I2 point |
      inducedInner metric immersion point vector vector < 1} :=
  positive_bilinear_bounded (inducedInner metric immersion point)
    (inducedInner_pos metric immersion injective point)

lemma inducedMetric_lower (g G : Smooth3 (I3 := I3) (N := N)) (φ : S → N)
    (hφ : ContMDiff I2 I3 ∞ φ)
    (hinj : ∀ x, Function.Injective (mfderiv I2 I3 φ x)) {c : ℝ}
    (hlow : ∀ x v, c * g.inner x v v ≤ G.inner x v v) :
    ∀ x v, c * (inducedMetric g φ hφ hinj).inner x v v ≤
      (inducedMetric G φ hφ hinj).inner x v v := by
  intro x v
  exact hlow (φ x) _

end CKSInducedArea

end

end OAI
