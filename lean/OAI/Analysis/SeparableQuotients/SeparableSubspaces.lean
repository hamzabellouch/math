import OAI.Analysis.SeparableQuotients.PerturbationOperator

namespace OAI

noncomputable section

namespace SeparableQuotient
open Set Metric TopologicalSpace Module
open scoped Classical Topology

lemma exists_separable_closed_ID {𝕜 Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (hY : ¬ FiniteDimensional 𝕜 Y) :
    ∃ F : Submodule 𝕜 Y, IsClosed (F : Set Y) ∧ ¬ FiniteDimensional 𝕜 F ∧
      IsSeparable (F : Set Y) := by
  let b := Basis.ofVectorSpace 𝕜 Y
  have hi : Infinite (Basis.ofVectorSpaceIndex 𝕜 Y) := by
    by_contra h
    let : Finite (Basis.ofVectorSpaceIndex 𝕜 Y) := not_infinite_iff_finite.mp h
    exact hY (Module.Finite.of_basis b)
  let := hi
  let f : ℕ → Y := b ∘ (Infinite.natEmbedding (Basis.ofVectorSpaceIndex 𝕜 Y))
  have hf : LinearIndependent 𝕜 f := b.linearIndependent.comp _ (Infinite.natEmbedding _).injective
  let F := (Submodule.span 𝕜 (range f)).topologicalClosure
  have hm (n : ℕ) : f n ∈ F := Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self n))
  have hfi : LinearIndependent 𝕜 (fun n => (⟨f n,hm n⟩ : F)) := by
    exact LinearIndependent.of_comp F.subtype hf
  refine ⟨F, Submodule.isClosed_topologicalClosure _, ?_, (countable_range f).isSeparable.span.closure⟩
  intro h
  let := h
  exact Module.Finite.not_linearIndependent_of_infinite _ hfi

lemma countable_of_separated_range {ι Y : Type*} [MetricSpace Y]
    (f : ι → Y) (hsep : IsSeparable (range f)) (r : ℝ) (hr : 0 < r)
    (hd : ∀ i j, i ≠ j → r ≤ dist (f i) (f j)) : Countable ι := by
  obtain ⟨t,ht,hcl⟩ := hsep
  have he (i : ι) : ∃ y : t, dist (f i) y < r/3 := by
    obtain ⟨y,hy,hyi⟩ := Metric.mem_closure_iff.mp (hcl (mem_range_self i)) (r/3) (by positivity)
    exact ⟨⟨y,hy⟩,hyi⟩
  choose g hg using he
  have hgI : Function.Injective g := by
    intro i j hij
    by_contra hn
    have h := hd i j hn
    have ht := dist_triangle (f i) (g i) (f j)
    have hi := hg i
    have hj := hg j
    rw [← hij,dist_comm (f j)] at hj
    linarith
  let := ht.to_subtype
  exact hgI.countable

end SeparableQuotient

namespace SeparableQuotient
lemma boolSeq_uncountable : ¬ Countable (ℕ → Bool) := by
  intro h
  have hm := Cardinal.mk_le_aleph0_iff.mpr h
  have he : Cardinal.mk (ℕ → Bool) = Cardinal.continuum := by
    simp only [Cardinal.mk_arrow,Cardinal.mk_bool,Cardinal.mk_nat,Cardinal.lift_ofNat,
      Cardinal.lift_aleph0,Cardinal.two_power_aleph0]
  rw [he] at hm
  exact (not_le_of_gt Cardinal.aleph0_lt_continuum) hm
end SeparableQuotient

namespace SeparableQuotient
open Set TopologicalSpace
lemma quotient_closure_lift {𝕜 D : Type*} [RCLike 𝕜]
    [NormedAddCommGroup D] [NormedSpace 𝕜 D]
    (Y X : Submodule 𝕜 D) [IsClosed (Y : Set D)] (z : D)
    (hz : Y.mkQL z ∈ (X.map Y.mkQ).topologicalClosure) :
    z ∈ (X ⊔ Y).topologicalClosure := by
  have he := Y.isOpenMap_mkQ.preimage_closure_eq_closure_preimage Y.mkQL.continuous
    (X.map Y.mkQ : Set (D ⧸ Y))
  have hp : Y.mkQ ⁻¹' (X.map Y.mkQ : Set (D ⧸ Y)) = (X ⊔ Y : Submodule 𝕜 D) := by
    change (Submodule.comap Y.mkQ (X.map Y.mkQ) : Set D) = _
    rw [Submodule.comap_map_eq,Submodule.ker_mkQ]
  rw [hp] at he
  change z ∈ closure ((X ⊔ Y : Submodule 𝕜 D) : Set D)
  rw [← he]
  exact hz
end SeparableQuotient

namespace SeparableQuotient
open Set TopologicalSpace
open scoped Classical
universe u v
variable {X : Type u} {E : Type v}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Transfer the necessary evaluation criterion through the actual predual
isomorphism, retaining a separable closed infinite-dimensional subspace. -/
lemma separable_restriction_of_quotient
    (R : E ≃L[ℝ] StrongDual ℝ X) (J : X →L[ℝ] StrongDual ℝ E)
    (hR : ∀ e x, R e x = J x e) (hSQ : HasSeparableQuotient ℝ X) :
    ∃ F : Submodule ℝ E, IsClosed (F : Set E) ∧ ¬ FiniteDimensional ℝ F ∧
      IsSeparable (F : Set E) ∧
      IsSeparable (range (fun x : X => (J x).comp F.subtypeL)) := by
  obtain ⟨H,hH,hHi,hHe⟩ := separable_evaluation_of_hasSeparableQuotient hSQ
  let hNg : NormedAddCommGroup H := inferInstance
  let hNs : NormedSpace ℝ H := inferInstance
  let : CompleteSpace H := hH.completeSpace_coe
  obtain ⟨G,hG,hGi,hGs⟩ := exists_separable_closed_ID (𝕜 := ℝ) (Y := H) hHi
  let gNg : NormedAddCommGroup G := inferInstance
  let gNs : NormedSpace ℝ G := inferInstance
  let : CompleteSpace G := hG.completeSpace_coe
  let : SeparableSpace G := hGs.separableSpace
  let T : G →L[ℝ] E := R.symm.toContinuousLinearMap.comp (H.subtypeL.comp G.subtypeL)
  have hi : Isometry (H.subtypeL.comp G.subtypeL) := fun _ _ => rfl
  have hT : ∃ K, AntilipschitzWith K T := by
    refine ⟨_,R.symm.antilipschitz.comp hi.antilipschitzWith⟩
  obtain ⟨K,hK⟩ := hT
  let F := T.range
  let fNg : NormedAddCommGroup F := inferInstance
  let fNs : NormedSpace ℝ F := inferInstance
  have hFc : IsClosed (F : Set E) := hK.isClosed_range T.uniformContinuous
  let e : G ≃L[ℝ] F := T.equivRange hK.injective hFc
  have hFi : ¬ FiniteDimensional ℝ F := by
    intro hh
    let := hh
    exact hGi (FiniteDimensional.of_injective e.toLinearMap e.injective)
  have hFs : IsSeparable (F : Set E) := isSeparable_range T.continuous
  let U : F →L[ℝ] H := G.subtypeL.comp e.symm.toContinuousLinearMap
  let A : StrongDual ℝ H →L[ℝ] StrongDual ℝ F := ContinuousLinearMap.precomp ℝ U
  have he (x : X) : (J x).comp F.subtypeL = A (subspaceEvaluation H x) := by
    ext z
    obtain ⟨g,rfl⟩ := e.surjective z
    change J x (T g) = ((U (e g) : H) : StrongDual ℝ X) x
    have hu : U (e g) = (g : H) := by
      change G.subtypeL (e.symm (e g)) = _
      rw [e.symm_apply_apply]
      rfl
    rw [hu]
    change J x (R.symm ((g : H) : StrongDual ℝ X)) = ((g : H) : StrongDual ℝ X) x
    rw [← hR,R.apply_symm_apply]
  refine ⟨F,hFc,hFi,hFs,(hHe.image A.continuous).mono ?_⟩
  rintro _ ⟨x,rfl⟩
  exact ⟨subspaceEvaluation H x,mem_range_self x,(he x).symm⟩

end SeparableQuotient

end

end OAI
