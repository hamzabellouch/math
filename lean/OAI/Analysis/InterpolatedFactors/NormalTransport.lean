import OAI.Analysis.InterpolatedFactors.CornerStabilization

namespace OAI

universe u_1 u_2 u_3

noncomputable section
namespace FreeGroupFactorMain.Amplification
variable {G : Type u_1} {H : Type u_2} [Group G] [Group H]

theorem groupNormal_of_iso (h : HasNormalTracialIso G H) :
    Nonempty (NormalTracialEquiv (canonicalTrace (G := G)) (canonicalTrace (G := H))
      (groupUltraweakTopology G) (groupUltraweakTopology H)) := by
  classical
  obtain ⟨Φ,hΦ,_⟩ := h
  obtain ⟨e,hδ,he⟩ := spatial_of_trace_iso Φ hΦ
  refine ⟨⟨spatialGroupIso e he,?_,spatialGroupIso_normal e he,spatialGroupIso_symm_normal e he⟩⟩
  intro T
  rw [canonicalTrace_eq_inner,canonicalTrace_eq_inner]
  change inner ℂ deltaOne (e ((T : GroupOperator G) (e.symm deltaOne)))=_
  rw [←hδ,e.symm_apply_apply,e.inner_map_map]

theorem groupAllPositive_of_rankTwo (h : HasNormalTracialIso G (FreeGroupRank 2))
    (t : ℝ) (ht : 0<t) :
    (∃p : stabilization G,IsStarProjection p ∧ stabilizedProjectionTrace p=ENNReal.ofReal t) ∧
    ∀(p : stabilization G)(hp : IsStarProjection p),stabilizedProjectionTrace p=ENNReal.ofReal t →
      Nonempty (GroupCornerNormalIso t p hp) := by
  have hinv := h.symm
  obtain ⟨e,_,_⟩ := h
  apply allPositiveScaling_both (fun T hT => center_scalar_of_iso e rankTwo_center_scalar T hT)
    (fun s hs hs1 => smallScaling_transport_group hinv (rankTwo_smallScaling s hs hs1)) t ht

end FreeGroupFactorMain.Amplification
namespace FreeGroupFactorMain

theorem groupIso_refl (G : Type u_3) [Group G] : HasNormalTracialIso G G :=
  ⟨StarAlgEquiv.refl ℂ (groupVonNeumann G),fun _ => rfl,@continuous_id _ (groupUltraweakTopology G)⟩

theorem finiteRank_to_two (n : ℕ) (hn : 2≤n) : HasNormalTracialIso (FreeGroupRank n) (FreeGroupRank 2) := by
  induction n, hn using Nat.le_induction with
  | base => exact groupIso_refl _
  | succ n hn ih =>
    have he : HasNormalTracialIso (FreeGroupRank n) (FreeGroupRank (n+1)) := by
      rcases eq_or_lt_of_le hn with h | h
      · subst n
        exact rankTwo
      · exact rankStep n (by omega)
    exact he.symm.trans ih

end FreeGroupFactorMain

end

end OAI
