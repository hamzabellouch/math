import Mathlib
import OAI.Analysis.Commutator.DeMarrCenter
import OAI.Analysis.Commutator.MinimalNormCompact

namespace OAI

noncomputable section

section

noncomputable section

open Set TopologicalSpace

namespace Kadison.CompactInvariant

variable {G X E : Type*} [Group G] [TopologicalSpace X] [T2Space X]
  [AddCommGroup X] [Module ℝ X] [MulAction G X] [ContinuousConstSMul G X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_fixed_point (j : X ≃ₗ[ℝ] E) (hj : Continuous j.symm)
    (hball : ∀ y : E,∀ r : ℝ,IsClosed {x : X | dist (j x) y≤r})
    (hiso : ∀ g : G,∀ x y : X,dist (j (g • x)) (j (g • y))=dist (j x) (j y))
    {C : Set X} (hcomp : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (hinv : Invariant (G:=G) C) (hsep : IsSeparable (j '' C)) :
    ∃ x∈C,∀ g : G,g • x=x := by
  classical
  obtain ⟨C₀,hC₀⟩ := exists_minimal_convex hcomp hne hinv hconv
  have hCcomp : IsCompact C₀ := hcomp.of_isClosed_subset hC₀.prop.2.2.1 hC₀.prop.1
  obtain ⟨K,hK⟩ := exists_minimal_compact hCcomp hC₀.prop.2.1 hC₀.prop.2.2.2.1
  have hKcomp : IsCompact K := hCcomp.of_isClosed_subset hK.prop.2.2.1 hK.prop.1
  have hnormcomp : IsCompact (j '' K) := minimal_norm_compact j.toEquiv hj hball hiso
    hKcomp hK (hsep.mono (image_mono (hK.prop.1.trans hC₀.prop.1)))
  have hsubsingleton : (j '' K).Subsingleton := by
    by_contra hnot
    have hnontriv : (j '' K).Nontrivial := Set.not_subsingleton_iff.mp hnot
    let D := Metric.diam (j '' K)
    have hD : 0<D := Metric.diam_pos hnontriv hnormcomp.isBounded
    have hdiam : ∀ x∈j '' K,∀ y∈j '' K,dist x y≤D :=
      fun _ hx _ hy => Metric.dist_le_diam_of_mem hnormcomp.isBounded hx hy
    obtain ⟨c,hc,r,hr,hrD,hcr⟩ := DeMarrCenter.exists_center hnormcomp
      (hK.prop.2.1.image j) D hD hdiam
    have hcin : j.symm c∈C₀ := by
      change c∈convexHull ℝ (j.toLinearMap '' K) at hc
      rw [←j.toLinearMap.image_convexHull] at hc
      obtain ⟨z,hz,rfl⟩ := hc
      change j.symm (j z)∈C₀
      rw [j.symm_apply_apply]
      exact convexHull_min hK.prop.1 hC₀.prop.2.2.2.2 hz
    let L : Set X := C₀∩⋂ x∈K,j ⁻¹' Metric.closedBall (j x) r
    have hLc : IsClosed L := hC₀.prop.2.2.1.inter (isClosed_iInter fun x =>
      isClosed_iInter fun _ => hball (j x) r)
    have hLconv : Convex ℝ L := hC₀.prop.2.2.2.2.inter (convex_iInter fun x =>
      convex_iInter fun _ => (convex_closedBall (j x) r).linear_preimage j.toLinearMap)
    have hLne : L.Nonempty := by
      refine ⟨j.symm c,hcin,?_⟩
      apply mem_iInter₂.mpr
      intro x hx
      change dist (j (j.symm c)) (j x)≤r
      rw [j.apply_symm_apply]
      exact hcr _ ⟨x,hx,rfl⟩
    have hLinv : Invariant (G:=G) L := by
      intro g z hz
      refine ⟨hC₀.prop.2.2.2.1 g z hz.1,mem_iInter₂.mpr ?_⟩
      intro x hx
      have hgi : g⁻¹ • x∈K := hK.prop.2.2.2 g⁻¹ x hx
      have hb : dist (j z) (j (g⁻¹ • x))≤r := mem_iInter₂.mp hz.2 _ hgi
      change dist (j (g • z)) (j x)≤r
      rw [←hiso g z (g⁻¹ • x),smul_inv_smul] at hb
      exact hb
    have hCL : C₀⊆L := hC₀.le_of_le
      ⟨(inter_subset_left.trans hC₀.prop.1),hLne,hLc,hLinv,hLconv⟩ inter_subset_left
    have hDle : D≤r := by
      apply Metric.diam_le_of_forall_dist_le hr
      rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
      exact mem_iInter₂.mp (hCL (hK.prop.1 hx)).2 y hy
    linarith
  obtain ⟨x,hx⟩ := hK.prop.2.1
  refine ⟨x,hC₀.prop.1 (hK.prop.1 hx),?_⟩
  intro g
  apply j.injective
  exact hsubsingleton ⟨g • x,hK.prop.2.2.2 g x hx,rfl⟩ ⟨x,hx,rfl⟩

end Kadison.CompactInvariant

end

end
end

end OAI
