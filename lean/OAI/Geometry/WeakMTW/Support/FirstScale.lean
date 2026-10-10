import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.MinimizerCompactness
import OAI.Geometry.WeakMTW.Coordinates.TangentScaling
import OAI.Geometry.WeakMTW.Support.TotalInterior

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem compact_first_scale {K : Set (TangentBundle (model n) M)} (hK : IsCompact K)
    {t₀ : ℝ} (ht₀ : 0 < t₀) {p₀ : TangentBundle (model n) M} (hp₀ : p₀ ∈ K)
    (hfail : t₀•p₀.2 ∉ injectivityDomain p₀.1) :
    ∃ s : ℝ, 0 < s ∧ s ≤ t₀ ∧
      (∀ r : ℝ, 0 ≤ r → r < s → ∀ p ∈ K, r•p.2 ∈ injectivityDomain p.1) ∧
      (∀ p ∈ K, s•p.2 ∈ minimizingDomain p.1) ∧
      ∃ p ∈ K, s•p.2 ∉ injectivityDomain p.1 := by
  let E : Set (ℝ × TangentBundle (model n) M) :=
    (Icc 0 t₀ ×ˢ K) ∩ (fun q => mulState q.1 q.2) ⁻¹' (totalInterior (n := n) (M := M))ᶜ
  have hE : IsCompact E := (isCompact_Icc.prod hK).inter_right
    (totalInterior_open.isClosed_compl.preimage tangentScale_continuous)
  have hmem : (t₀,p₀) ∈ E := ⟨⟨⟨ht₀.le,le_refl _⟩,hp₀⟩,hfail⟩
  obtain ⟨s,hs⟩ := (hE.image continuous_fst).exists_isLeast ⟨t₀,⟨(t₀,p₀),hmem,rfl⟩⟩
  obtain ⟨⟨r,p⟩,hrp,hrs⟩ := hs.1
  change r = s at hrs
  subst r
  have hspos : 0 < s := lt_of_le_of_ne hrp.1.1.1 (by
    intro heq
    have hbad := hrp.2
    change s•p.2 ∉ injectivityDomain p.1 at hbad
    rw [← heq,zero_smul] at hbad
    exact hbad (zero_mem_injectivity p.1))
  have hb : ∀ r : ℝ, 0 ≤ r → r < s → ∀ p ∈ K, r•p.2 ∈ injectivityDomain p.1 := by
    intro r hr hrs q hq
    by_contra hn
    have hqE : (r,q) ∈ E := ⟨⟨⟨hr,hrs.le.trans hrp.1.1.2⟩,hq⟩,hn⟩
    exact (not_le.mpr hrs) (hs.2 ⟨(r,q),hqE,rfl⟩)
  refine ⟨s,hspos,hrp.1.1.2,hb,?_,p,hrp.1.2,hrp.2⟩
  intro q hq
  have hcont : Continuous (fun r : ℝ => mulState r q) :=
    tangentScale_continuous.comp (continuous_id.prodMk continuous_const)
  have htend : Tendsto (fun r : ℝ => mulState r q) (𝓝[<] s) (𝓝 (mulState s q)) :=
    hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply totalMinimizingSet_closed.mem_of_tendsto htend
  have hrnonneg : ∀ᶠ r : ℝ in 𝓝[<] s, 0 ≤ r :=
    ((eventually_gt_nhds hspos).mono (fun _ hr => hr.le)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hrnonneg,self_mem_nhdsWithin] with r hr hrs
  exact injectivity_subset_minimizing q.1 (hb r hr hrs q hq)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
