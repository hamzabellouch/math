import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialProfileSeries

namespace OAI

/-! Finite-support identities for the actual compact radial Poincaré sum. -/
noncomputable section
open Set
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialProfileSeries_sub (W V : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) (hV : ∀ v≤(1:ℝ), V v=0)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaRadialProfileSeries p (W-V)=
      cubicThetaRadialProfileSeries p W-cubicThetaRadialProfileSeries p V := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact (isCompact_singleton (x:=p))
    (by intro q hq; simpa only [mem_singleton_iff.mp hq] using hp)
  have hsum (U : C_c(ℝ,ℂ)) (hU : ∀ v≤(1:ℝ),U v=0) :
      cubicThetaRadialProfileSeries p U=∑ r∈S,cubicThetaRadialProfileTerm r p U := by
    apply tsum_eq_sum
    intro r hr
    exact mul_eq_zero_of_right _ (hU _ (hS p (mem_singleton p) r hr).le)
  rw [hsum (W-V) (by intro v hv; change W v-V v=0; rw [hW v hv,hV v hv,sub_self]),
    hsum W hW,hsum V hV,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  change star r.phase*(W (r.height p)-V (r.height p))=_
  exact mul_sub _ _ _

lemma cubicThetaRadialProfileSection_sub (W V : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) (hV : ∀ v≤(1:ℝ), V v=0) :
    cubicThetaRadialProfileSection (W-V)
        (by intro v hv; change W v-V v=0; rw [hW v hv,hV v hv,sub_self])=
      cubicThetaRadialProfileSection W hW-cubicThetaRadialProfileSection V hV := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  exact cubicThetaRadialProfileSeries_sub W V hW hV p.property

end CubicFirstMoment

end

end OAI
