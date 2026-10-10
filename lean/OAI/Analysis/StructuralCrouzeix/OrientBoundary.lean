import OAI.Analysis.StructuralCrouzeix.Model

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
namespace StructuralCrouzeix
open CompleteCrouzeix Set Filter Metric Complex
open scoped Topology

private lemma preconnected_avoiding_frontier {U S : Set ℂ}
    (hU : IsOpen U) (hS : IsPreconnected S)
    (havoid : ∀ z ∈ S, z ∉ frontier U) :
    S ⊆ U ∨ S ⊆ (closure U)ᶜ := by
  apply hS.subset_or_subset hU isClosed_closure.isOpen_compl
  · exact Set.disjoint_left.mpr (fun z hz hn => hn (subset_closure hz))
  · intro z hz
    by_cases hi : z ∈ U
    · exact Or.inl hi
    · right
      intro hc
      apply havoid z hz
      rw [hU.frontier_eq]
      exact ⟨hc,hi⟩

theorem RegularAnalyticBoundaryAt.orient {U : Set ℂ} {p : ℂ}
    (hU : IsOpen U) (hcv : Convex ℝ U) (hne : U.Nonempty)
    (hp : p ∈ frontier U) (hchart : RegularAnalyticBoundaryAt U p) :
    LocalAnalyticBoundary U p := by
  obtain ⟨χ,hχ0,hχa,hχd,hboundary⟩ := hchart
  obtain ⟨r,hr,hrall⟩ := Metric.mem_nhds_iff.mp
    (hχa.eventually_analyticAt.and hboundary)
  let B : Set ℂ := ball 0 r
  let P : Set ℂ := B ∩ {z : ℂ | 0 < z.im}
  let N : Set ℂ := B ∩ {z : ℂ | z.im < 0}
  have hca : AnalyticOnNhd ℂ χ B := fun z hz => (hrall hz).1
  have hPc : Convex ℝ P :=
    (convex_ball (0 : ℂ) r).inter ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hNc : Convex ℝ N :=
    (convex_ball (0 : ℂ) r).inter ((convex_Iio (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hPi := hPc.isPreconnected.image χ (hca.continuousOn.mono inter_subset_left)
  have hNi := hNc.isPreconnected.image χ (hca.continuousOn.mono inter_subset_left)
  have hPa : ∀ y ∈ χ '' P, y ∉ frontier U := by
    rintro y ⟨z,hz,rfl⟩ hf
    have hi := (hrall hz.1).2.mp hf
    exact (ne_of_gt hz.2) hi
  have hNa : ∀ y ∈ χ '' N, y ∉ frontier U := by
    rintro y ⟨z,hz,rfl⟩ hf
    have hi := (hrall hz.1).2.mp hf
    exact (ne_of_lt hz.2) hi
  have hP := preconnected_avoiding_frontier hU hPi hPa
  have hN := preconnected_avoiding_frontier hU hNi hNa
  have hnb : χ '' B ∈ 𝓝 p := by
    rw [← hχ0, ← hχa.hasStrictDerivAt.map_nhds_eq hχd]
    exact image_mem_map (ball_mem_nhds 0 hr)
  have hpnot : p ∉ U := by rw [hU.frontier_eq] at hp; exact hp.2
  have hregular : interior (closure U) = U :=
    (hcv.interior_closure_eq_interior_of_nonempty_interior
      (by rw [hU.interior_eq]; exact hne)).trans hU.interior_eq
  have hnotboth (hPU : χ '' P ⊆ U) (hNU : χ '' N ⊆ U) : False := by
    have hbcl : χ '' B ⊆ closure U := by
      rintro y ⟨z,hz,rfl⟩
      rcases lt_trichotomy z.im 0 with hn | he | hp
      · exact subset_closure (hNU ⟨z,⟨hz,hn⟩,rfl⟩)
      · exact ((hrall hz).2.mpr he).1
      · exact subset_closure (hPU ⟨z,⟨hz,hp⟩,rfl⟩)
    have hpi : p ∈ interior (closure U) :=
      mem_interior_iff_mem_nhds.mpr (mem_of_superset hnb hbcl)
    exact hpnot (hregular ▸ hpi)
  have hnotneither (hPO : χ '' P ⊆ (closure U)ᶜ)
      (hNO : χ '' N ⊆ (closure U)ᶜ) : False := by
    have hbnot : ∀ y ∈ χ '' B, y ∉ U := by
      rintro y ⟨z,hz,rfl⟩ hi
      rcases lt_trichotomy z.im 0 with hn | he | hp
      · exact hNO ⟨z,⟨hz,hn⟩,rfl⟩ (subset_closure hi)
      · have hf := (hrall hz).2.mpr he
        rw [hU.frontier_eq] at hf
        exact hf.2 hi
      · exact hPO ⟨z,⟨hz,hp⟩,rfl⟩ (subset_closure hi)
    have he : ∀ᶠ y in 𝓝 p, y ∉ U := mem_of_superset hnb hbnot
    obtain ⟨y,hy,hyn⟩ := ((mem_closure_iff_frequently.mp hp.1).and_eventually he).exists
    exact hyn hy
  have hsideP (hPU : χ '' P ⊆ U) (hNO : χ '' N ⊆ (closure U)ᶜ) :
      ∀ z ∈ B, χ z ∈ U ↔ 0 < z.im := by
    intro z hz
    constructor
    · intro hi
      by_contra hn
      rcases lt_or_eq_of_le (le_of_not_gt hn) with hneg | heq
      · exact hNO ⟨z,⟨hz,hneg⟩,rfl⟩ (subset_closure hi)
      · have hf := (hrall hz).2.mpr heq
        rw [hU.frontier_eq] at hf
        exact hf.2 hi
    · intro hi
      exact hPU ⟨z,⟨hz,hi⟩,rfl⟩
  have hsideN (hPO : χ '' P ⊆ (closure U)ᶜ) (hNU : χ '' N ⊆ U) :
      ∀ z ∈ B, χ z ∈ U ↔ z.im < 0 := by
    intro z hz
    constructor
    · intro hi
      by_contra hn
      rcases eq_or_lt_of_le (le_of_not_gt hn) with heq | hpos
      · have hf := (hrall hz).2.mpr heq.symm
        rw [hU.frontier_eq] at hf
        exact hf.2 hi
      · exact hPO ⟨z,⟨hz,hpos⟩,rfl⟩ (subset_closure hi)
    · intro hi
      exact hNU ⟨z,⟨hz,hi⟩,rfl⟩
  rcases hP with hPU | hPO
  · have hNO : χ '' N ⊆ (closure U)ᶜ := hN.resolve_left (hnotboth hPU)
    refine ⟨χ,hχ0,hχa,hχd,?_,?_⟩
    · exact mem_of_superset (ball_mem_nhds 0 hr) (hsideP hPU hNO)
    · filter_upwards [hboundary] with z hz
      exact hz.mpr
  · have hNU : χ '' N ⊆ U := hN.resolve_right (hnotneither hPO)
    let ψ : ℂ → ℂ := fun z => χ (-z)
    have ha : AnalyticAt ℂ ψ 0 := by
      exact (show AnalyticAt ℂ χ (-(0 : ℂ)) by simpa only [neg_zero] using hχa).comp
        (analyticAt_id.neg : AnalyticAt ℂ (fun z : ℂ => -z) 0)
    have hd : deriv ψ 0 ≠ 0 := by
      have he := hχa.differentiableAt.hasDerivAt.comp_of_eq 0
        (hasDerivAt_id (0 : ℂ)).neg (by simp)
      change deriv (χ ∘ (-id)) 0 ≠ 0
      rw [he.deriv]
      exact mul_ne_zero hχd (neg_ne_zero.mpr one_ne_zero)
    refine ⟨ψ,by simpa only [ψ, neg_zero] using hχ0,ha,hd,?_,?_⟩
    · apply mem_of_superset (ball_mem_nhds 0 hr)
      intro z hz
      have hneg : -z ∈ B := by simpa only [B, mem_ball_zero_iff,norm_neg] using hz
      change χ (-z) ∈ U ↔ 0 < z.im
      simpa only [neg_im, neg_lt_zero] using hsideN hPO hNU (-z) hneg
    · apply mem_of_superset (ball_mem_nhds 0 hr)
      intro z hz him
      have hneg : -z ∈ B := by simpa only [B, mem_ball_zero_iff,norm_neg] using hz
      apply (hrall hneg).2.mpr
      simp only [neg_im,him,neg_zero]

end StructuralCrouzeix
end

end OAI
