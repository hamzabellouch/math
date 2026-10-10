import OAI.Analysis.KadisonKastler.PureStateExtension

namespace OAI

/-! # The compact annihilator ball for Sakai's separation argument -/

namespace KadisonKastler

noncomputable section

open scoped Topology

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def hermitianAnnihilatorBall (φ : A →⋆ₐ[ℂ] B) : Set (WeakDual ℂ B) :=
  {f | ‖f.toStrongDual‖ ≤ 1 ∧ (∀ b, f (star b) = star (f b)) ∧ ∀ a, f (φ a) = 0}

theorem hermitianAnnihilatorBall_isCompact (φ : A →⋆ₐ[ℂ] B) :
    IsCompact (hermitianAnnihilatorBall φ) := by
  have hstar : IsClosed {f : WeakDual ℂ B | ∀ b : B, f (star b) = star (f b)} := by
    simpa only [Set.ofPred_forall] using isClosed_iInter (fun b : B =>
      (isClosed_eq (WeakDual.eval_continuous (star b))
        (continuous_star.comp (WeakDual.eval_continuous b)) :
          IsClosed {f : WeakDual ℂ B | f (star b) = star (f b)}))
  have hann : IsClosed {f : WeakDual ℂ B | ∀ a : A, f (φ a) = 0} := by
    simpa only [Set.ofPred_forall] using isClosed_iInter (fun a : A =>
      (isClosed_eq (WeakDual.eval_continuous (φ a)) continuous_const :
        IsClosed {f : WeakDual ℂ B | f (φ a) = (0 : ℂ)}))
  have he : hermitianAnnihilatorBall φ =
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : B →L[ℂ] ℂ) 1 ∩
        {f | ∀ b, f (star b) = star (f b)} ∩ {f | ∀ a, f (φ a) = 0} := by
    ext f
    simp only [hermitianAnnihilatorBall, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, and_assoc]
  rw [he]
  exact ((WeakDual.isCompact_closedBall (0 : B →L[ℂ] ℂ) 1).inter_right hstar).inter_right hann

theorem hermitianAnnihilatorBall_convex (φ : A →⋆ₐ[ℂ] B) :
    Convex ℝ (hermitianAnnihilatorBall φ) := by
  intro f hf g hg a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · change ‖a • f.toStrongDual + b • g.toStrongDual‖ ≤ 1
    calc
      _ ≤ ‖a • f.toStrongDual‖ + ‖b • g.toStrongDual‖ := norm_add_le _ _
      _ = a * ‖f.toStrongDual‖ + b * ‖g.toStrongDual‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hf.1 ha)
        (mul_le_mul_of_nonneg_left hg.1 hb)
      _ = 1 := by simpa using hab
  · intro x
    change a • f (star x) + b • g (star x) = star (a • f x + b • g x)
    rw [hf.2.1, hg.2.1]
    simp only [star_add, star_smul, star_trivial]
  · intro x
    change a • f (φ x) + b • g (φ x) = 0
    rw [hf.2.2, hg.2.2]
    simp

theorem hermitianAnnihilatorBall_zero (φ : A →⋆ₐ[ℂ] B) :
    (0 : WeakDual ℂ B) ∈ hermitianAnnihilatorBall φ := by
  refine ⟨?_, ?_, ?_⟩
  · change ‖(0 : B →L[ℂ] ℂ)‖ ≤ 1
    norm_num
  · intro x
    change (0 : ℂ) = star 0
    rw [star_zero]
  · intro x
    rfl

theorem hermitianAnnihilatorBall_extreme_norm
    (φ : A →⋆ₐ[ℂ] B) (f : WeakDual ℂ B)
    (hf : f ∈ (hermitianAnnihilatorBall φ).extremePoints ℝ) (hne : f ≠ 0) :
    ‖f.toStrongDual‖ = 1 := by
  have hmem := (mem_extremePoints.mp hf).1
  have hn0 : f.toStrongDual ≠ 0 := by
    intro h
    apply hne
    exact WeakDual.toStrongDual.injective h
  have hn : 0 < ‖f.toStrongDual‖ := norm_pos_iff.mpr hn0
  apply le_antisymm hmem.1
  by_contra h
  have hlt : ‖f.toStrongDual‖ < 1 := lt_of_not_ge h
  let g : WeakDual ℂ B := ‖f.toStrongDual‖⁻¹ • f
  have hg : g ∈ hermitianAnnihilatorBall φ := by
    refine ⟨?_, ?_, ?_⟩
    · change ‖‖f.toStrongDual‖⁻¹ • f.toStrongDual‖ ≤ 1
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
    · intro x
      change ‖f.toStrongDual‖⁻¹ • f (star x) = star (‖f.toStrongDual‖⁻¹ • f x)
      rw [hmem.2.1]
      simp only [star_smul, star_trivial]
    · intro x
      change ‖f.toStrongDual‖⁻¹ • f (φ x) = 0
      rw [hmem.2.2, smul_zero]
  have hseg : f ∈ openSegment ℝ (0 : WeakDual ℂ B) g := by
    refine ⟨1 - ‖f.toStrongDual‖, ‖f.toStrongDual‖, sub_pos.mpr hlt, hn, by ring, ?_⟩
    rw [smul_zero, zero_add]
    apply DFunLike.ext
    intro x
    change ‖f.toStrongDual‖ • (‖f.toStrongDual‖⁻¹ • f x) = f x
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  exact hne ((mem_extremePoints.mp hf).2 0 (hermitianAnnihilatorBall_zero φ) g hg hseg).1.symm

theorem exists_extreme_hermitian_annihilator
    (φ : A →⋆ₐ[ℂ] B) (b : B)
    (hsep : ∃ f ∈ hermitianAnnihilatorBall φ, f b ≠ 0) :
    ∃ g ∈ (hermitianAnnihilatorBall φ).extremePoints ℝ,
      ‖g.toStrongDual‖ = 1 ∧ g b ≠ 0 := by
  let : IsScalarTower ℝ ℂ (WeakDual ℂ B) :=
    inferInstanceAs (IsScalarTower ℝ ℂ (B →L[ℂ] ℂ))
  let : ContinuousSMul ℝ (WeakDual ℂ B) := IsScalarTower.continuousSMul ℂ
  let : LocallyConvexSpace ℝ (WeakDual ℂ B) :=
    (WeakDual.withSeminorms ℂ B).toLocallyConvexSpace
  have hex : ∃ g ∈ (hermitianAnnihilatorBall φ).extremePoints ℝ, g b ≠ 0 := by
    by_contra h
    push Not at h
    let L : WeakDual ℂ B →ₗ[ℝ] ℂ :=
      { toFun := fun f => f b
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    have hclosed : IsClosed (L.ker : Set (WeakDual ℂ B)) :=
      isClosed_eq (WeakDual.eval_continuous b) continuous_const
    have hsub : convexHull ℝ ((hermitianAnnihilatorBall φ).extremePoints ℝ) ⊆ L.ker :=
      convexHull_min h L.ker.convex
    have hc := closure_minimal hsub hclosed
    have hKM : closure (convexHull ℝ ((hermitianAnnihilatorBall φ).extremePoints ℝ)) =
        hermitianAnnihilatorBall φ :=
      closure_convexHull_extremePoints (E := WeakDual ℂ B)
        (hermitianAnnihilatorBall_isCompact φ) (hermitianAnnihilatorBall_convex φ)
    rw [hKM] at hc
    obtain ⟨f, hf, hb⟩ := hsep
    exact hb (hc hf)
  obtain ⟨g, hg, hgb⟩ := hex
  refine ⟨g, hg, hermitianAnnihilatorBall_extreme_norm φ g hg ?_, hgb⟩
  intro hz
  apply hgb
  rw [hz]
  rfl

end

end KadisonKastler

end OAI
