import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingRows

namespace OAI

/-! A compact positive-height set meets only finitely many incoming
row supports. The bound is arithmetic and is uniform in the spectral
parameter, so the resulting finite-sum identities support differentiation. -/
noncomputable section
open Set
namespace CubicFirstMoment

theorem cubicThetaIncomingRows_compact {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : ∀ p∈K, 0<p.2) :
    ∃ S : Finset CubicThetaBottomRow, ∀ p∈K, ∀ r∉S, r.height p<1 := by
  classical
  have hc : ContinuousOn (fun p : ℂ × ℝ => p.2*cubicThetaHeightConstant p) K := by
    intro p hp
    unfold cubicThetaHeightConstant
    fun_prop (disch := exact pow_ne_zero _ (hpos p hp).ne')
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
  have hrow : 1+norm r.c+norm r.d≤p.2*cubicThetaHeightConstant p :=
    by simpa only [one_mul] using
      (le_div_iff₀ hn).mp (hhigh.trans (r.height_le (hpos p hp)))
  have hb : p.2*cubicThetaHeightConstant p≤B :=
    (le_abs_self _).trans (hB p hp)
  apply hr
  apply hfin.mem_toFinset.mpr
  constructor <;> linarith [norm_nonneg r.c,norm_nonneg r.d]

theorem cubicThetaIncomingEisenstein_compact_sum {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : ∀ p∈K, 0<p.2) :
    ∃ S : Finset CubicThetaBottomRow, ∀ p∈K, ∀ s : ℂ,
      cubicThetaIncomingEisenstein p s=∑ r∈S, cubicThetaIncomingTerm r p s := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hpos
  refine ⟨S,fun p hp s => ?_⟩
  apply tsum_eq_sum
  intro r hr
  unfold cubicThetaIncomingTerm
  rw [cubicThetaCuspCutoff_zero (hS p hp r hr).le,zero_mul]

theorem cubicThetaIncomingEisenstein_analytic {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    AnalyticAt ℂ (cubicThetaIncomingEisenstein p) s := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingEisenstein_compact_sum isCompact_singleton
    (show ∀ q∈({p} : Set (ℂ × ℝ)), 0<q.2 from fun q hq => by simpa only [Set.mem_singleton_iff.mp hq] using hp)
  have he : cubicThetaIncomingEisenstein p=(fun z => ∑ r∈S, cubicThetaIncomingTerm r p z) :=
    funext (hS p (Set.mem_singleton p))
  rw [he]
  apply Finset.analyticAt_fun_sum
  intro r _
  exact analyticAt_const.mul ((cubicThetaEisensteinTerm_differentiable r hp).analyticAt s)

end CubicFirstMoment

end

end OAI
