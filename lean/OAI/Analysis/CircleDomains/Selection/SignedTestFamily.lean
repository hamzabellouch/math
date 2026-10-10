import OAI.Analysis.CircleDomains.Selection.SignedScalarTests
import OAI.Analysis.CircleDomains.Topology.CompactScalarCircleModel

namespace OAI

/-! One common cutoff encodes a finite signed list by unit-interval tests.
The cutoff is constant on the source dust, so all new trace pairs are null. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem constant_left_trace_pair_null {X : Type*} (B : Set X) (v : X → ℝ) (c : ℝ) :
    volume ((fun x => (c, v x)) '' B) = 0 := by
  apply measure_mono_null (t := ({c} : Set ℝ) ×ˢ univ)
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨rfl, trivial⟩
  · rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp

 theorem constant_right_trace_pair_null {X : Type*} (B : Set X) (v : X → ℝ) (c : ℝ) :
    volume ((fun x => (v x, c)) '' B) = 0 := by
  apply measure_mono_null (t := univ ×ˢ ({c} : Set ℝ))
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨trivial, rfl⟩
  · rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp

 theorem exists_common_signed_cutoff {G : Set Sphere} (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G) {m : ℕ} (u : Fin m → EuclideanPlane → ℝ)
    (hs : ∀ i, HasCompactSupport (u i)) :
    ∃ η : EuclideanPlane → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      (∀ x, η x ∈ Icc 0 1) ∧ (∀ x ∉ physicalPlaneDomain G, η x = 1) ∧
      (∀ i x, u i x ≠ 0 → η x = 1) := by
  let K : Set EuclideanPlane := (physicalPlaneDomain G)ᶜ ∪ ⋃ i, tsupport (u i)
  have hB : IsCompact (physicalPlaneDomain G)ᶜ := by
    have hh := (isCompact_finite_preimage hG.isClosed_compl (not_not.mpr hinf)).image
      complexPlaneCoordinates.symm.continuous
    convert hh using 1
    ext x
    simp only [mem_compl_iff, physicalPlaneDomain, mem_preimage, mem_image]
    constructor
    · intro hx
      exact ⟨complexPlaneCoordinates x, hx, complexPlaneCoordinates.symm_apply_apply x⟩
    · rintro ⟨z, hz, rfl⟩
      simpa only [planeSphere, ContinuousLinearEquiv.apply_symm_apply] using hz
  have hK : IsCompact K := hB.union (isCompact_iUnion fun i => hs i)
  obtain ⟨f, hf, hfs, _, hfr, hfo⟩ := exists_smooth_planar_cutoff
    (hK.image complexPlaneCoordinates.continuous) isOpen_univ (subset_univ _)
  refine ⟨f ∘ complexPlaneCoordinates, hf.comp complexPlaneCoordinates.contDiff,
    hfs.comp_homeomorph complexPlaneCoordinates.toHomeomorph, fun x => hfr _, ?_, ?_⟩
  · intro x hx
    exact hfo.self_of_nhdsSet _ (mem_image_of_mem _ (Or.inl hx))
  · intro i x hx
    exact hfo.self_of_nhdsSet _ (mem_image_of_mem _
      (Or.inr (mem_iUnion.mpr ⟨i, subset_tsupport _ hx⟩)))

structure SignedTestFamily (G : Set Sphere) {m : ℕ} (u : Fin m → EuclideanPlane → ℝ) where
  test : Fin (m + 1) → EuclideanPlane → ℝ
  continuous : ∀ i, Continuous (test i)
  compact : ∀ i, HasCompactSupport (test i)
  unit : ∀ i x, test i x ∈ Icc 0 1
  witness : ∀ i, DeGiorgi.MemW1pWitness 2 (test i) (physicalPlaneDomain G)
  pair_null : ∀ i j, i ≠ j → volume
    ((fun p => (sphereFromPlaneFunction (test i) p, sphereFromPlaneFunction (test j) p)) '' Gᶜ) = 0
  scale : Fin m → ℝ
  recovery : ∀ i x, (2 * scale i) * test i.succ x - scale i * test 0 x = u i x

 theorem exists_signed_test_family {G : Set Sphere} (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G) {m : ℕ} (u : Fin m → EuclideanPlane → ℝ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (H : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    (hpair : ∀ i j, i ≠ j → volume
      ((fun p => (sphereFromPlaneFunction (u i) p, sphereFromPlaneFunction (u j) p)) '' Gᶜ) = 0) :
    Nonempty (SignedTestFamily G u) := by
  classical
  obtain ⟨η, hη, hηs, hηr, hηB, hηu⟩ := exists_common_signed_cutoff hG hinf u hs
  choose C hC using fun i => (hu i).bounded_above_of_compact_support (hs i)
  let D : Fin m → ℝ := fun i => |C i| + 1
  have hD : ∀ i, 0 < D i := fun i => by dsimp [D]; positivity
  have huD : ∀ i x, ‖u i x‖ ≤ D i := fun i x => (hC i x).trans
    (by dsimp [D]; linarith [le_abs_self (C i)])
  let v : Fin (m + 1) → EuclideanPlane → ℝ :=
    Fin.cases η (fun i => signedScalarEncoding η (u i) (D i))
  let Hη := (smoothCompactPlaneWitness hη hηs).restrict
    (hG.preimage continuous_planeSphere) (subset_univ _)
  have hvpair : ∀ i j, i ≠ j → volume
      ((fun p => (sphereFromPlaneFunction (v i) p, sphereFromPlaneFunction (v j) p)) '' Gᶜ) = 0 := by
    have he (i : Fin m) (p : Sphere) (hp : p ∈ Gᶜ) :
        sphereFromPlaneFunction (v i.succ) p =
          (D i)⁻¹ / 2 * sphereFromPlaneFunction (u i) p + 1 / 2 := by
      have hpn : p ≠ OnePoint.infty := fun h => hp (h ▸ hinf)
      obtain ⟨x, rfl⟩ := exists_planeSphere_eq hpn
      change sphereFromPlaneFunction (signedScalarEncoding η (u i) (D i)) (planeSphere x) = _
      simp only [planeSphere, sphereFromPlaneFunction_coe, ContinuousLinearEquiv.symm_apply_apply]
      rw [signedScalarEncoding, hηB x hp]
      ring
    have he0 (p : Sphere) (hp : p ∈ Gᶜ) : sphereFromPlaneFunction (v 0) p = 1 := by
      have hpn : p ≠ OnePoint.infty := fun h => hp (h ▸ hinf)
      obtain ⟨x, rfl⟩ := exists_planeSphere_eq hpn
      change sphereFromPlaneFunction η (planeSphere x) = 1
      simpa only [planeSphere, sphereFromPlaneFunction_coe,
        ContinuousLinearEquiv.symm_apply_apply] using hηB x hp
    intro i j hij
    refine Fin.cases ?_ (fun a => ?_) i hij
    · refine Fin.cases ?_ (fun b _ => ?_) j
      · exact fun h => (h rfl).elim
      · convert constant_left_trace_pair_null Gᶜ (fun p => sphereFromPlaneFunction (v b.succ) p) 1
          using 1
        congr 1
        apply image_congr
        intro p hp
        rw [he0 p hp]
    · refine Fin.cases (fun _ => ?_) (fun b hab => ?_) j
      · convert constant_right_trace_pair_null Gᶜ (fun p => sphereFromPlaneFunction (v a.succ) p) 1
          using 1
        congr 1
        apply image_congr
        intro p hp
        rw [he0 p hp]
      · have hab' : a ≠ b := fun h => hab (congrArg Fin.succ h)
        have hh := affine_trace_pair_null Gᶜ
          (sphereFromPlaneFunction (u a)) (sphereFromPlaneFunction (u b)) (hpair a b hab')
          ((D a)⁻¹ / 2) (1 / 2) ((D b)⁻¹ / 2) (1 / 2)
        convert hh using 1
        congr 1
        apply image_congr
        intro p hp
        rw [he a p hp, he b p hp]
  refine ⟨{
    test := v
    continuous := Fin.cases hη.continuous (fun i => signedScalarEncoding_continuous hη.continuous (hu i) _)
    compact := Fin.cases hηs (fun i => signedScalarEncoding_compact hηs (hs i) _)
    unit := Fin.cases hηr (fun i => signedScalarEncoding_unit (hD i) hηr (huD i) (hηu i))
    witness := Fin.cases Hη (fun i => signedScalarEncoding_witness Hη (H i) (D i))
    pair_null := hvpair
    scale := D
    recovery := fun i x => signedScalarEncoding_recovery η (u i) (hD i).ne' x }⟩

end CircleDomainRigidity

end

end OAI
