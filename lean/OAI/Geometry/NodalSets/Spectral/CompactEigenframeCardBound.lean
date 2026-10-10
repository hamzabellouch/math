import OAI.Geometry.NodalSets.Spectral.FiniteEigenframeMinMax

namespace OAI

namespace Yau.Analysis
open Set Metric
noncomputable section

theorem compact_eigenframe_card_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (c : ℝ) (hc : 0 < c) :
    ∃ K : ℕ, ∀ (N : ℕ) (e : Fin N → E) (mu : Fin N → ℝ),
      Orthonormal ℝ e → (∀ i, T (e i)=mu i • e i) →
      (∀ i, c ≤ mu i) → N ≤ K := by
  classical
  have hcomp := hT.isCompact_closure_image_closedBall (f := T.toLinearMap) 1
  obtain ⟨t,ht,hcover⟩ := Metric.totallyBounded_iff.mp hcomp.totallyBounded (c/2) (half_pos hc)
  let := ht.fintype
  refine ⟨Fintype.card t,?_⟩
  intro N e mu ho he hmu
  have hnear (i : Fin N) : ∃ a : t, dist (T (e i)) a < c/2 := by
    have hx : T (e i) ∈ closure (T '' closedBall 0 1) :=
      subset_closure ⟨e i,by simpa using (ho.norm_eq_one i).le,rfl⟩
    have hxcover := hcover hx
    simp only [mem_iUnion,mem_ball] at hxcover
    obtain ⟨a,ha,hai⟩ := hxcover
    exact ⟨⟨a,ha⟩,hai⟩
  choose f hf using hnear
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hinner : inner ℝ (e i) (T (e i)-T (e j)) = mu i := by
      rw [he i,he j,inner_sub_right,inner_smul_right,inner_smul_right,
        real_inner_self_eq_norm_sq,ho.norm_eq_one i,ho.inner_eq_zero hne]
      simp
    have hdist := real_inner_le_norm (e i) (T (e i)-T (e j))
    rw [ho.norm_eq_one i,one_mul,hinner,← dist_eq_norm] at hdist
    have hd : dist (T (e i)) (T (e j)) < c := by
      have h1 := hf i
      have h2 := hf j
      rw [← hij] at h2
      have hh := dist_triangle (T (e i)) (f i : E) (T (e j))
      rw [dist_comm (f i : E) (T (e j))] at hh
      linarith
    exact (not_lt_of_ge ((hmu i).trans hdist)) hd
  simpa using Fintype.card_le_of_injective f hinj

end
end Yau.Analysis

end OAI
