import OAI.Analysis.CircleDomains.Uniformization.LocalizedRealLimit

namespace OAI

/-! Compact source sets stay outside fixed separated target regions in the actual models. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem eventually_image_compact_avoids_closed
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {K W : Set ℂ}
    (hK : IsCompact K) (hF : ContinuousOn F K) (hW : IsClosed W)
    (hd : Disjoint (F '' K) W) (hlim : TendstoUniformlyOn f F atTop K) :
    ∀ᶠ n in atTop, Disjoint (f n '' K) W := by
  have hsub : F '' K ⊆ Wᶜ := fun _ hx hw => Set.disjoint_left.mp hd hx hw
  obtain ⟨δ, hδ, hsmall⟩ := (hK.image_of_continuousOn hF).exists_thickening_subset_open
    hW.isOpen_compl hsub
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim δ hδ] with n hn
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, rfl⟩ hz
  apply hsmall ?_ hz
  exact mem_thickening_iff.mpr ⟨F x, mem_image_of_mem _ hx, by simpa only [dist_comm] using hn x hx⟩

namespace FiniteTransfer.AssignedRealModelLimit

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} (A : AssignedRealModelLimit M)

theorem eventually_avoids_closed
    {K W : Set ℂ} (hK : IsCompact K) (hKG : K ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hW : IsClosed W) (hd : Disjoint (A.function '' K) W) :
    ∀ᶠ n in atTop, Disjoint
      ((fun z : ℂ => finiteCoord ((M.stages (A.subsequence n)).forward z)) '' K) W := by
  have hF : ContinuousOn A.function K := by
    intro z hz
    have h := continuousAt_finite_part_of_conformalAt (A.conformal.1 _ (hKG hz))
      (by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
    simpa only [extendAtInfinity_coe, finiteCoord_coe] using h.continuousWithinAt
  exact eventually_image_compact_avoids_closed hK hF hW hd
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (A.converges.mono hKG))

theorem eventually_region_over_source_complement
    {K W : Set ℂ} (hK : IsCompact K) (hKG : K ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hW : IsClosed W) (hd : Disjoint (A.function '' K) W) :
    ∀ᶠ n in atTop,
      ((((↑) : ℂ → Sphere) ⁻¹' (M.stages (A.subsequence n)).domain) ∩ W) ⊆
        Complex.equivRealProdCLM ⁻¹'
          (sphereRealMap (M.stages (A.subsequence n)).forward ''
            (realChartDomain (openCompletedRegion (M.stages (A.subsequence n)).terminals.H) \
              (Complex.equivRealProdCLM '' K))) := by
  filter_upwards [A.eventually_avoids_closed hK hKG hW hd] with n hn
  intro z hz
  have hzreal : Complex.equivRealProdCLM z ∈ realChartDomain (M.stages (A.subsequence n)).domain := by
    simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hz.1
  have hbij := (M.stages (A.subsequence n)).equivalence.real_bijOn
    (M.stages (A.subsequence n)).source_infty (M.stages (A.subsequence n)).principal.1
  have himage := hbij.surjOn hzreal
  apply subset_image_sdiff _ _ _ ⟨himage, ?_⟩
  rintro ⟨x, ⟨w, hw, rfl⟩, he⟩
  have hweq : finiteCoord ((M.stages (A.subsequence n)).forward w) = z := by
    apply Complex.equivRealProdCLM.injective
    simpa only [sphereRealMap, ContinuousLinearEquiv.symm_apply_apply] using he
  exact Set.disjoint_left.mp hn ⟨w, hw, hweq⟩ hz.2

end FiniteTransfer.AssignedRealModelLimit

end CircleDomainRigidity

end

end OAI
