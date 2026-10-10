import Mathlib
import OAI.Geometry.Borsuk.Simplicial.OddSphereDimensionBoundFintype

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section Restrict
variable {V W ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι]

lemma Admissible.comp_isometry {f : V → ι → ℝ} (hf : Admissible f) (e : W →ₗᵢ[ℝ] V) :
    Admissible (fun x => f (e x)) := by
  refine ⟨fun i => (hf.smooth i).comp e.contDiff,?_,?_,?_,?_⟩
  · intro x i
    rw [map_neg,hf.antipodal]
  · intro x hx i
    exact hf.nonneg _ ((e.norm_map x).trans hx) i
  · intro x hx
    exact hf.sum_one _ ((e.norm_map x).trans hx)
  · intro x y hx hy hxy i
    exact hf.orthogonal _ _ ((e.norm_map x).trans hx) ((e.norm_map y).trans hy)
      ((e.inner_map_map x y).trans hxy) i

lemma Admissible.restrict_labels {f : V → ι → ℝ} (hf : Admissible f)
    (s : Finset ι) (hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ s, f x i = 0) :
    Admissible (fun x (i : s) => f x i.val) := by
  classical
  refine ⟨fun i => hf.smooth i.val,fun x i => hf.antipodal x i.val,
    fun x hx i => hf.nonneg x hx i.val,?_,fun x y hx hy hxy i => hf.orthogonal x y hx hy hxy i.val⟩
  intro x hx
  rw [← hf.sum_one x hx]
  rw [Finset.sum_coe_sort]
  exact Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => hzero x hx i hi)

end Restrict

lemma orthogonal_isometry (k : ℕ) {u : EuclideanSpace ℝ (Fin (k+1))} (hu : ‖u‖ = 1) :
    ∃ e : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k+1)),
      ∀ x, ⟪u,e x⟫ = 0 := by
  let W := (Submodule.span ℝ {u})ᗮ
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hdim : Module.finrank ℝ W = k := by
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (k+1))) = k+1) := ⟨by simp⟩
    exact Submodule.finrank_orthogonal_span_singleton hu0
  let b := (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
  refine ⟨W.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry,?_⟩
  intro x
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b.repr.symm x).property)

lemma Admissible.support_card_four_le {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f)
    {u : Vector4} (hu : ‖u‖ = 1) : (positiveSupport f u).card ≤ 4 := by
  classical
  obtain ⟨e,he⟩ := orthogonal_isometry 3 hu
  let s := (positiveSupport f u)ᶜ
  have hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ s, f (e x) i = 0 := by
    intro x hx i hi
    have hip : 0 < f u i := (mem_positiveSupport _ _ _).mp (by simpa [s] using hi)
    have hn := hf.nonneg (e x) (by simpa using hx) i
    exact le_antisymm (le_of_not_gt (fun hp => hf.orthogonal u (e x) hu
      (by simpa using hx) (he x) i ⟨hip,hp⟩)) hn
  have hb := ((hf.comp_isometry e).restrict_labels s hzero).label_bound
  have hc : Fintype.card (UpperTriangle (Fin 3)) = 6 := by decide
  rw [hc,Fintype.card_coe,Finset.card_compl] at hb
  rw [Fintype.card_fin] at hb
  omega

lemma Admissible.support_card_three_le {f : EuclideanSpace ℝ (Fin 3) → Fin 6 → ℝ}
    (hf : Admissible f) {u : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = 1) :
    (positiveSupport f u).card ≤ 3 := by
  classical
  obtain ⟨e,he⟩ := orthogonal_isometry 2 hu
  let s := (positiveSupport f u)ᶜ
  have hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ s, f (e x) i = 0 := by
    intro x hx i hi
    have hip : 0 < f u i := (mem_positiveSupport _ _ _).mp (by simpa [s] using hi)
    have hn := hf.nonneg (e x) (by simpa using hx) i
    exact le_antisymm (le_of_not_gt (fun hp => hf.orthogonal u (e x) hu
      (by simpa using hx) (he x) i ⟨hip,hp⟩)) hn
  have hb := ((hf.comp_isometry e).restrict_labels s hzero).label_bound
  have hc : Fintype.card (UpperTriangle (Fin 2)) = 3 := by decide
  rw [hc,Fintype.card_coe,Finset.card_compl] at hb
  rw [Fintype.card_fin] at hb
  omega

end BorsukNine

end OAI
