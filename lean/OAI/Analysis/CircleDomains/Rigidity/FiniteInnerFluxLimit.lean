import OAI.Analysis.CircleDomains.Rigidity.MatchedInnerCircleFlux
import OAI.Analysis.CircleDomains.Selection.FinitePositiveMinimum

namespace OAI

/-! The actual inner-circle estimates hold simultaneously on every
finite family of matched disks. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem finite_inner_quadrantFlux_limiting_bound (E : D.MatchedRoundDisks) (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (F : Finset D.IndexedMatchedPair)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ρ ∈ Ioc (0 : ℝ) δ,
      (∑ j : F, quadrantFlux (D.selectedPlane hG hf) (E.sourceCenter j) (E.sourceRadius j+ρ)) ≤
        2*Real.pi*(∑ j ∈ F, E.sourceRadius j*E.targetRadius j)+ε := by
  classical
  have he : 0 < ε/((F.card : ℝ)+1) := div_pos hε (by positivity)
  have hj (j : F) := D.indexed_quadrantFlux_limiting_bound E hG hf j he
  choose δ hδ hbound using hj
  obtain ⟨η,hη,hηδ⟩ := finite_positive_lower_bound δ hδ
  refine ⟨η,hη,?_⟩
  intro ρ hρ
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hbound j ρ ⟨hρ.1,hρ.2.trans (hηδ j)⟩)
  have hbase : (∑ j : F, 2*Real.pi*E.sourceRadius j*E.targetRadius j) =
      2*Real.pi*(∑ j ∈ F, E.sourceRadius j*E.targetRadius j) := by
    have heq : (∑ j : F, E.sourceRadius j*E.targetRadius j) =
        ∑ j ∈ F, E.sourceRadius j*E.targetRadius j :=
      (Finset.sum_subtype F (by simp) (fun j => E.sourceRadius j*E.targetRadius j)).symm
    simp only [mul_assoc,← Finset.mul_sum,heq]
  have herr : (F.card : ℝ)*(ε/((F.card : ℝ)+1)) ≤ ε := by
    have hd : 0 < (F.card : ℝ)+1 := by positivity
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  rw [Finset.sum_add_distrib,hbase] at hs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] at hs
  exact hs.trans (add_le_add le_rfl herr)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
