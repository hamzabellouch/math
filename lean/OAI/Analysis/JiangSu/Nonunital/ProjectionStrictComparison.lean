import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.ApproximateCentralMatrixSupply
import OAI.Analysis.JiangSu.Nonunital.ProjectionGapUltrapower
import OAI.Analysis.JiangSu.MatrixAlgebras.FamilyProjectionLiftTraces

namespace OAI

section

noncomputable section
namespace NonunitalGamma
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)] (U : Ultrafilter ℕ)
local notation "T" => (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ)
local notation "D" => FamilyUltrapower T U
local notation "L" => familyLimitTrace T U
local notation "q" => Pureness.ClosedStarIdeal.quotientStarHom (familyNullIdeal T (U : Filter ℕ))

lemma projection_sequence_lift (hfree : (U : Filter ℕ)≤atTop) {p : D} (hp : IsStarProjection p) :
    ∃ e : lp (fun _ : ℕ => A) ∞,(∀ n,0≤e n) ∧ (∀ n,‖e n‖≤1) ∧ q (boundedInr (A := A) e)=p := by
  obtain ⟨x,hxn,hx⟩ := contractive_sequence_lift U hfree p hp.norm_le
  refine ⟨star x*x,fun n => star_mul_self_nonneg (x n),?_,?_⟩
  · intro n
    change ‖star (x n)*x n‖≤1
    rw [CStarRing.norm_star_mul_self]
    have hn := (lp.norm_apply_le_norm ENNReal.top_ne_zero x n).trans hxn
    exact (mul_le_mul_of_nonneg_right hn (norm_nonneg (x n))).trans (by simpa using hn)
  · rw [map_mul,map_star,map_mul,map_star,hx,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]

 theorem tracial_projection_strict_comparison (hfree : (U : Filter ℕ)≤atTop)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : StrictComparison hcone)
    {p r : D} (hp : IsStarProjection p) (hr : IsStarProjection r)
    {c : ℝ} (hc : 0<c)
    (hgap : ∀ s : ℕ → NormalizedTrace A,
      ((L s).functional p).re+2*c≤((L s).functional r).re) :
    ∃ v : D,star v*v=p ∧ r*v=v := by
  obtain ⟨e,hep,hen,he⟩ := projection_sequence_lift U hfree hp
  obtain ⟨f,hfp,hfn,hf⟩ := projection_sequence_lift U hfree hr
  have he' : IsStarProjection (q (boundedInr (A := A) e)) := he ▸ hp
  have hf' : IsStarProjection (q (boundedInr (A := A) f)) := hf ▸ hr
  have hede : ∀ t : ℝ,0<t → ∀ᶠ n in (U : Filter ℕ),∀ τ : NormalizedTrace A,
      (τ.functional (e n-e n*e n)).re<t := by
    intro t ht
    have h := FamilyProjection.projection_lift_defect T U (boundedInr (A := A) e) he' ht
    filter_upwards [h] with n hn τ
    simpa only [boundedInr_apply,←Unitization.inr_mul,←Unitization.inr_sub,
      NormalizedTrace.unitized_inr] using hn τ
  have hfde : ∀ t : ℝ,0<t → ∀ᶠ n in (U : Filter ℕ),∀ τ : NormalizedTrace A,
      (τ.functional (f n-f n*f n)).re<t := by
    intro t ht
    have h := FamilyProjection.projection_lift_defect T U (boundedInr (A := A) f) hf' ht
    filter_upwards [h] with n hn τ
    simpa only [boundedInr_apply,←Unitization.inr_mul,←Unitization.inr_sub,
      NormalizedTrace.unitized_inr] using hn τ
  have hg : ∀ᶠ n in (U : Filter ℕ),∀ τ : NormalizedTrace A,
      (τ.functional (e n)).re+c≤(τ.functional (f n)).re := by
    have h := FamilyProjection.uniform_trace_gap_eventually T U (boundedInr (A := A) e) (boundedInr (A := A) f) hc
      (by simpa only [he,hf] using hgap)
    filter_upwards [h] with n hn τ
    simpa only [boundedInr_apply,NormalizedTrace.unitized_inr] using hn τ
  obtain ⟨v,hv,hrv⟩ := projection_gap_tracial_ultrapower hcone hcmp U hfree e f hep hen hfp hfn c hc hede hg hfde
  exact ⟨v,by rwa [he] at hv,by rwa [hf] at hrv⟩

end NonunitalGamma

end
end

end OAI
