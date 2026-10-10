import OAI.Analysis.InterpolatedFactors.NormalEquiv

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.Amplification
open scoped ENNReal
variable {G : Type u_1} [Group G]

theorem finiteProjection_trace_div (n : ℕ) (hn : 0<(n:ℝ)) (t : ℝ) (ht : 0≤t)
    (p : groupVonNeumann G) (hp : IsStarProjection p) (hpτ : canonicalTrace p=((t/(n:ℝ):ℝ):ℂ)) :
    stabilizedProjectionTrace (finiteProjection n p)=ENNReal.ofReal t := by
  rw [finiteProjection_trace n p hp _ (div_nonneg ht hn.le) hpτ]
  congr 1
  field_simp

theorem preferred_scaling_model
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G,Commute T S) →
      ∃ c : ℂ,T=c • (1 : groupVonNeumann G))
    (hsmall : ∀t : ℝ,0<t → t≤1 → HasCornerScaling (canonicalTrace (G := G)) (groupUltraweakTopology G) t)
    (t : ℝ) (ht : 0<t) :
    ∃ (p : stabilization G) (hp : IsStarProjection p),
      stabilizedProjectionTrace p=ENNReal.ofReal t ∧ Nonempty (GroupCornerNormalIso t p hp) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max t 1)
  have hnt : t<(n:ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hn1 : 1<(n:ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hn0 : 0<(n:ℝ) := by linarith
  have ha : 0<t/(n:ℝ) := div_pos ht hn0
  have ha1 : t/(n:ℝ)≤1 := (div_le_one hn0).mpr hnt.le
  have hb : 0<1/(n:ℝ) := div_pos zero_lt_one hn0
  have hb1 : 1/(n:ℝ)≤1 := (div_le_one hn0).mpr hn1.le
  rcases hsmall (t/(n:ℝ)) ha ha1 with ⟨q,hq,f,hqτ,hfn,hfin,hfτ⟩
  rcases hsmall (1/(n:ℝ)) hb hb1 with ⟨r,hr,g,hrτ,hgn,hgin,hgτ⟩
  refine ⟨finiteProjection n q,finiteProjection_projection n q hq,
    finiteProjection_trace_div n hn0 t ht.le q hq hqτ,?_⟩
  have hrtr := finiteProjection_trace_div n hn0 1 zero_le_one r hr hrτ
  obtain ⟨D⟩ := preferred_unit_iso (G := G) hbase (finiteProjection n r)
    (finiteProjection_projection n r hr) hrtr
  let e : Corner q hq ≃⋆ₐ[ℂ] Corner r hr := f.symm.trans g
  have heτ (x : Corner q hq) : canonicalTrace (e x).val=(t:ℂ)⁻¹*canonicalTrace x.val :=
    scaling_ratio_trace t ht n hn0 q r hq hr f g hfτ hgτ x
  let : TopologicalSpace (groupVonNeumann G) := groupUltraweakTopology G
  let : TopologicalSpace (Corner q hq) := cornerTopology (groupUltraweakTopology G) q hq
  let : TopologicalSpace (Corner r hr) := cornerTopology (groupUltraweakTopology G) r hr
  have hen : Continuous e := hgn.comp hfin
  have hein : Continuous e.symm := hfn.comp hgin
  exact ⟨(finiteScaledIso n t q r hq hr e heτ hen hein).trans D⟩

theorem allPositiveScaling_both
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G,Commute T S) →
      ∃ c : ℂ,T=c • (1 : groupVonNeumann G))
    (hsmall : ∀t : ℝ,0<t → t≤1 → HasCornerScaling (canonicalTrace (G := G)) (groupUltraweakTopology G) t)
    (t : ℝ) (ht : 0<t) :
    (∃p : stabilization G,IsStarProjection p ∧ stabilizedProjectionTrace p=ENNReal.ofReal t) ∧
    ∀(p : stabilization G)(hp : IsStarProjection p),stabilizedProjectionTrace p=ENNReal.ofReal t →
      Nonempty (GroupCornerNormalIso t p hp) := by
  obtain ⟨q,hq,hqτ,⟨E⟩⟩ := preferred_scaling_model (G := G) hbase hsmall t ht
  refine ⟨⟨q,hq,hqτ⟩,?_⟩
  intro p hp hpτ
  obtain ⟨f,hfτ,hfn,hfin⟩ := finite_corner_choice_both (G := G) hbase t p q hp hq
    (hpτ.trans hqτ.symm) (hpτ ▸ ENNReal.ofReal_ne_top)
  let F : NormalTracialEquiv (normalizedCornerTrace stabilizedTrace t p hp)
      (normalizedCornerTrace stabilizedTrace t q hq)
      (cornerTopology (stabilizationTopology G) p hp) (cornerTopology (stabilizationTopology G) q hq) :=
    ⟨f,hfτ,hfn,hfin⟩
  exact ⟨F.trans E⟩

theorem infinite_allPositiveScaling (t : ℝ) (ht : 0<t) :
    (∃p : stabilization (FreeGroup ℕ),IsStarProjection p ∧ stabilizedProjectionTrace p=ENNReal.ofReal t) ∧
    ∀(p : stabilization (FreeGroup ℕ))(hp : IsStarProjection p),stabilizedProjectionTrace p=ENNReal.ofReal t →
      Nonempty (GroupCornerNormalIso t p hp) :=
  allPositiveScaling_both (fun T hT => ⟨canonicalTrace T,infinite_free_group_center_scalar T hT⟩)
    infinite_hasCornerScaling t ht
end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain

theorem HasNormalTracialIso.symm {G : Type u_2} {H : Type u_3} [Group G] [Group H]
    (h : HasNormalTracialIso G H) : HasNormalTracialIso H G := by
  classical
  obtain ⟨Φ,hΦ,_⟩ := h
  obtain ⟨e,hδ,he⟩ := Amplification.spatial_of_trace_iso Φ hΦ
  refine ⟨(spatialGroupIso e he).symm,?_,spatialGroupIso_symm_normal e he⟩
  intro T
  rw [canonicalTrace_eq_inner,canonicalTrace_eq_inner]
  change inner ℂ deltaOne (e.symm ((T : GroupOperator H) (e deltaOne)))=_
  rw [hδ,←e.inner_map_map,e.apply_symm_apply,hδ]

theorem center_scalar_of_iso {G : Type u_4} {H : Type u_5} [Group G] [Group H]
    (e : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H)
    (hH : ∀ T : groupVonNeumann H,(∀ S : groupVonNeumann H,Commute T S) → ∃ c : ℂ,T=c • 1)
    (T : groupVonNeumann G) (hT : ∀ S : groupVonNeumann G,Commute T S) :
    ∃ c : ℂ,T=c • 1 := by
  have he : ∀ S : groupVonNeumann H,Commute (e T) S := by
    intro S
    have hh := (hT (e.symm S)).map e
    simpa only [StarAlgEquiv.apply_symm_apply] using hh
  obtain ⟨c,hc⟩ := hH (e T) he
  have hec : e (c • (1 : groupVonNeumann G))=c • (1 : groupVonNeumann H) := by
    change e.toFun (c • (1 : groupVonNeumann G))=_
    rw [e.map_smul']
    change c • e (1 : groupVonNeumann G)=_
    rw [map_one]
  exact ⟨c,e.injective (hc.trans hec.symm)⟩

end FreeGroupFactorMain
namespace FreeGroupFactorMain.Amplification
open scoped ENNReal

theorem rankTwo_smallScaling (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    HasCornerScaling (canonicalTrace (G := FreeGroupRank 2)) (groupUltraweakTopology (FreeGroupRank 2)) t :=
  smallScaling_transport_group ((rankTwo.trans rankThreeInfinite).symm) (infinite_hasCornerScaling t ht ht1)

theorem rankTwo_center_scalar (T : groupVonNeumann (FreeGroupRank 2))
    (hT : ∀ S : groupVonNeumann (FreeGroupRank 2),Commute T S) : ∃c : ℂ,T=c • 1 := by
  obtain ⟨e,_,_⟩ := rankTwo.trans rankThreeInfinite
  exact center_scalar_of_iso e (fun S hS => ⟨canonicalTrace S,infinite_free_group_center_scalar S hS⟩) T hT

theorem rankTwo_allPositiveScaling (t : ℝ) (ht : 0<t) :
    (∃p : stabilization (FreeGroupRank 2),IsStarProjection p ∧ stabilizedProjectionTrace p=ENNReal.ofReal t) ∧
    ∀(p : stabilization (FreeGroupRank 2))(hp : IsStarProjection p),stabilizedProjectionTrace p=ENNReal.ofReal t →
      Nonempty (GroupCornerNormalIso t p hp) :=
  allPositiveScaling_both rankTwo_center_scalar rankTwo_smallScaling t ht

theorem positiveRealSelfSimilarity (t : ℝ) (ht : 0 < t)
    (p : stabilization (FreeGroupRank 2)) (hp : IsStarProjection p)
    (htrace : stabilizedProjectionTrace p = ENNReal.ofReal t) :
    HasAmplificationIso (FreeGroupRank 2) (FreeGroupRank 2) t p hp := by
  obtain ⟨E⟩ := (rankTwo_allPositiveScaling t ht).2 p hp htrace
  exact ⟨E.equiv,E.trace_eq,E.normal⟩
end FreeGroupFactorMain.Amplification

end

end OAI
