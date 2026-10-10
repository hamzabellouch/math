import OAI.Analysis.BoundedHochschild.MinimalRepresentedAverages

namespace OAI

/-! Compressions by operators in the two commutants have constant norm on a
minimal represented averaging family. -/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M H K : Type*} [CStarAlgebra M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def weakCompression (P : K →L[ℂ] K) (Q : H →L[ℂ] H) (W : H →WOT[ℂ] K) :
    H →WOT[ℂ] K :=
  (ContinuousLinearMapWOT.ofCLM P).comp (W.comp (ContinuousLinearMapWOT.ofCLM Q))

omit [CompleteSpace H] [CompleteSpace K] in
lemma weakCompression_continuous (P : K →L[ℂ] K) (Q : H →L[ℂ] H) :
    Continuous (weakCompression P Q) :=
  (ContinuousLinearMapWOT.continuous_postcomp _).comp
    (ContinuousLinearMapWOT.continuous_precomp _)

omit [CompleteSpace H] [CompleteSpace K] in
lemma weakCompression_sublevel_convex (P : K →L[ℂ] K) (Q : H →L[ℂ] H) (c : ℝ) :
    Convex ℝ {W : H →WOT[ℂ] K | ‖(weakCompression P Q W).toCLM‖ ≤ c} := by
  let f : (H →WOT[ℂ] K) →ₗ[ℝ] (H →L[ℂ] K) :=
    { toFun := fun W => (weakCompression P Q W).toCLM
      map_add' := by intros; ext; simp [weakCompression]
      map_smul' := by intros; ext; simp [weakCompression] }
  have hs : f ⁻¹' Metric.closedBall 0 c =
      {W : H →WOT[ℂ] K | ‖(weakCompression P Q W).toCLM‖ ≤ c} := by
    ext W
    change dist ((weakCompression P Q W).toCLM) 0 ≤ c ↔ _
    rw [dist_zero_right]
    rfl
  rw [← hs]
  exact (convex_closedBall (0 : H →L[ℂ] K) c).linear_preimage f

lemma representedRightAverage_compress (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (P : K →L[ℂ] K) (Q : H →L[ℂ] H)
    (hP : ∀ a, P.comp (π a) = (π a).comp P)
    (hQ : ∀ a, Q.comp (σ a) = (σ a).comp Q)
    {I : Type*} [Fintype I] (m : I → M) (W : H →L[ℂ] K) :
    P.comp ((representedRightAverage π σ m W).comp Q) =
      representedRightAverage π σ m (P.comp (W.comp Q)) := by
  have hp (a : M) (ξ : K) : P (π a ξ) = π a (P ξ) :=
    congrArg (fun A : K →L[ℂ] K => A ξ) (hP a)
  have hq (a : M) (ξ : H) : (σ a).adjoint (Q ξ) = Q ((σ a).adjoint ξ) := by
    have hh := congrArg (fun A : H →L[ℂ] H => A ξ) (hQ (star a)).symm
    simpa only [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.comp_apply] using hh
  ext ξ
  simp only [ContinuousLinearMap.comp_apply, representedRightAverage,
    operatorRowAverage_apply, map_sum, hp, hq]

theorem compressed_norm_eq_on_minimal_family (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (F : Set (H →WOT[ℂ] K))
    (hclosed : IsClosed F) (hconv : Convex ℝ F)
    (hinv : RepresentedRightAverageInvariant π σ F)
    (hmin : ∀ G : Set (H →WOT[ℂ] K), G ⊆ F → G.Nonempty → IsClosed G →
      Convex ℝ G → RepresentedRightAverageInvariant π σ G → F ⊆ G)
    (P : K →L[ℂ] K) (Q : H →L[ℂ] H)
    (hP : ∀ a, P.comp (π a) = (π a).comp P)
    (hQ : ∀ a, Q.comp (σ a) = (σ a).comp Q)
    {U V : H →WOT[ℂ] K} (hU : U ∈ F) (hV : V ∈ F) :
    ‖(weakCompression P Q U).toCLM‖ = ‖(weakCompression P Q V).toCLM‖ := by
  have hle (A B : H →WOT[ℂ] K) (hA : A ∈ F) (hB : B ∈ F) :
      ‖(weakCompression P Q A).toCLM‖ ≤ ‖(weakCompression P Q B).toCLM‖ := by
    let c := ‖(weakCompression P Q B).toCLM‖
    let G := F ∩ (weakCompression P Q ⁻¹' rectangularWeakBall c)
    have hGc : IsClosed G := hclosed.inter
      ((rectangularWeakBall_isClosed c).preimage (weakCompression_continuous P Q))
    have hGv : Convex ℝ G := hconv.inter (weakCompression_sublevel_convex P Q c)
    have hGi : RepresentedRightAverageInvariant π σ G := by
      intro n m hm W hW
      refine ⟨hinv n m hm hW.1, ?_⟩
      change ‖P.comp ((representedRightAverage π σ m W.toCLM).comp Q)‖ ≤ c
      rw [representedRightAverage_compress π σ P Q hP hQ]
      exact (representedRightAverage_norm_le π σ m hm _).trans hW.2
    exact (hmin G (fun _ h => h.1) ⟨B, hB, show ‖(weakCompression P Q B).toCLM‖ ≤ c from le_rfl⟩ hGc hGv hGi hA).2
  exact le_antisymm (hle U V hU hV) (hle V U hV hU)

end BoundedHochschild.KadisonRingrose

end

end OAI
