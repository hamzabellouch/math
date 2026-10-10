import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeightBandCore
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingLocalFinite

namespace OAI

/-! Positive lower height cutoffs, needed when Hecke dilations move a
compact Poincare profile below the unit cusp height. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaRows_compact_below {ε : ℝ} (hε : 0<ε)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hpos : ∀ p∈K,0<p.2) :
    ∃ S : Finset CubicThetaBottomRow,∀ p∈K,∀ r∉S,r.height p<ε := by
  classical
  have hc : ContinuousOn (fun p : ℂ × ℝ => p.2*cubicThetaHeightConstant p/ε) K := by
    intro p hp
    unfold cubicThetaHeightConstant
    fun_prop (disch := first | exact hε.ne' | exact pow_ne_zero _ (hpos p hp).ne')
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hc
  have hi : Function.Injective (fun r : CubicThetaBottomRow => (r.c,r.d)) := by
    intro r t h
    exact CubicThetaBottomRow.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hfin : {r : CubicThetaBottomRow | norm r.c≤B ∧ norm r.d≤B}.Finite :=
    ((finite_norm_le B).prod (finite_norm_le B)).preimage hi.injOn
  refine ⟨hfin.toFinset,?_⟩
  intro p hp r hr
  apply lt_of_not_ge
  intro hhigh
  have hn : 0<1+norm r.c+norm r.d := by linarith [norm_nonneg r.c,norm_nonneg r.d]
  have hrow : 1+norm r.c+norm r.d≤p.2*cubicThetaHeightConstant p/ε := by
    apply (le_div_iff₀ hε).mpr
    nlinarith [(le_div_iff₀ hn).mp (hhigh.trans (r.height_le (hpos p hp)))]
  have hb : p.2*cubicThetaHeightConstant p/ε≤B := (le_abs_self _).trans (hB p hp)
  apply hr
  apply hfin.mem_toFinset.mpr
  constructor <;> linarith [norm_nonneg r.c,norm_nonneg r.d]

theorem cubicThetaPositiveHeightBand_core {ε H : ℝ} (hε : 0<ε) :
    ∃ S : Finset SL(2,Eisenstein),∀ (δ : SL(2,Eisenstein)) (p : CubicThetaPoint),
      ε≤cubicThetaPointHeight p → cubicThetaPointHeight p≤H →
        cubicThetaQuotientMap (δ • p)∈cubicThetaQuotientCore S (max H ε⁻¹) := by
  obtain ⟨S,hS⟩ := cubicThetaFiniteSiegelCover
  refine ⟨S,?_⟩
  intro δ p hp₁ hp₂
  let q := δ • p
  obtain ⟨σ,hσ,k,hk⟩ := hS q.val q.property
  let y := (σ*k.val) • q
  have hy : y.val∈cubicThetaSiegelSet := hk
  have hb : cubicThetaPointHeight y ≤ max H ε⁻¹ := by
    have he : y=(σ*k.val*δ) • p := by rw [mul_smul]
    rw [he]
    apply (cubicThetaPointHeight_full_smul_le _ p).trans
    apply max_le (hp₂.trans (le_max_left _ _))
    simpa only [one_div] using (inv_anti₀ hε hp₁).trans (le_max_right H ε⁻¹)
  have hyc : y.val∈cubicThetaSiegelCore (max H ε⁻¹) := cubicThetaSiegelSet_mem_core hy hb
  have hpoint : σ⁻¹ • y=k • q := by
    dsimp [y]
    rw [mul_smul,inv_smul_smul]
    rfl
  refine ⟨k • q,?_,cubicThetaQuotient_covering.map_smul k⟩
  change (k • q).val∈cubicThetaCompactCore S (max H ε⁻¹)
  refine mem_iUnion.mpr ⟨σ,mem_iUnion.mpr ⟨hσ,y.val,hyc,?_⟩⟩
  exact congrArg cubicThetaPointCoordinates hpoint

end CubicFirstMoment

end

end OAI
