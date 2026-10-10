import OAI.Geometry.SurfaceImmersion.Geometry.LinearProjectionImmersion

namespace OAI

/-! Dimension reduction of the ordinary Whitney embedding to a smooth
immersion of a compact surface in four-dimensional Euclidean space. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

def euclideanPad (n m : ℕ) : ProjectionTarget n →L[ℝ] ProjectionTarget m :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin m =>
      if hi : i.val < n then
        (ContinuousLinearMap.proj (⟨i.val,hi⟩ : Fin n)).comp
          (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap
      else 0)

lemma euclideanPad_injective {n m : ℕ} (hn : n ≤ m) :
    Function.Injective (euclideanPad n m) := by
  intro v w he
  ext i
  have h := congrArg (fun z : ProjectionTarget m => z ⟨i.val,lt_of_lt_of_le i.isLt hn⟩) he
  simpa [euclideanPad,i.isLt] using h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma smooth_immersion_postcompose (L : V →L[ℝ] W) (hL : Function.Injective L)
    {F : M → V} (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F)
    (hI : ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,V) F p)) :
    ContMDiff planeModel 𝓘(ℝ,W) ∞ (L ∘ F) ∧
      ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,W) (L ∘ F) p) := by
  have hLc : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,W) ∞ L := L.contDiff.contMDiff
  refine ⟨hLc.comp hF,?_⟩
  intro p
  rw [mfderiv_comp p (hLc.mdifferentiable (by simp)).mdifferentiableAt
    (hF.mdifferentiable (by simp)).mdifferentiableAt,mfderiv_eq_fderiv,L.fderiv]
  exact hL.comp (hI p)

variable [IsManifold planeModel ∞ M] [CompactSpace M]

theorem SmoothingAtlas.reduce_immersion_dimension (A : SmoothingAtlas M) (n : ℕ) :
    (∃ F : M → ProjectionTarget n, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget n) ∞ F ∧
      ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget n) F p)) →
    ∃ G : M → ProjectionTarget 4, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 4) ∞ G ∧
      ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 4) G p) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rintro ⟨F,hF,hI⟩
    by_cases hn : n ≤ 4
    · exact ⟨euclideanPad n 4 ∘ F,
        smooth_immersion_postcompose (euclideanPad n 4) (euclideanPad_injective hn) hF hI⟩
    · have hn0 : n ≠ 0 := by omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      let e : ProjectionTarget (k+1) ≃L[ℝ] ProjectionTarget k × ℝ :=
        ContinuousLinearEquiv.ofFinrankEq (by simp)
      obtain ⟨he,heI⟩ := smooth_immersion_postcompose e.toContinuousLinearMap e.injective hF hI
      obtain ⟨a,hg,hgI⟩ := A.exists_projected_immersion (show 4 ≤ k by omega) he heI
      exact ih k (Nat.lt_succ_self k) ⟨graphProjection a ∘ (e ∘ F),hg,hgI⟩

variable [T2Space M]

/-- The ordinary four-dimensional immersion is proved without the
three-dimensional Whitney input used in the conditional isometric theorem. -/
theorem exists_smooth_euclidean_four_immersion :
    ∃ F : M → ProjectionTarget 4, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 4) ∞ F ∧
      ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 4) F p) := by
  obtain ⟨A⟩ := exists_smoothingAtlas (M := M)
  obtain ⟨n,F,hF,_hclosed,hI⟩ := exists_embedding_euclidean_of_compact (I := planeModel) (M := M)
  exact A.reduce_immersion_dimension n ⟨F,hF,hI⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
