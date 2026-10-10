import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
local notation "T" => (fun τ : TracialState A => τ)
local notation "D" => FamilyUltrapower T U
local notation "q" => Pureness.ClosedStarIdeal.quotientStarHom (familyNullIdeal T (U : Filter ℕ))
local notation "L" => familyLimitTrace T U

lemma projection_lift_defect (e : lp (fun _ : ℕ => A) ∞)
    (he : IsStarProjection (q e)) {r : ℝ} (hr : 0<r) :
    ∀ᶠ n in (U : Filter ℕ),∀ τ : TracialState A,
      (τ.functional (e n-e n*e n)).re<r := by
  have hz : q (e - e * e) = 0 := by
    rw [map_sub, map_mul, he.isIdempotentElem.eq, sub_self]
  have ht := (familyQuotientMap_eq_zero T U (e-e*e)).mp hz
  filter_upwards [ht.eventually_lt_const hr] with n hn τ
  exact ((Complex.re_le_norm _).trans
    ((trace_norm_le_twoNorm τ _).trans (traceTwoNorm_le_family T τ _))).trans_lt hn

lemma uniform_trace_gap_eventually (e f : lp (fun _ : ℕ => A) ∞)
    {c : ℝ} (hc : 0<c)
    (hgap : ∀ s : ℕ → TracialState A,
      ((L s).functional (q e)).re+2*c≤((L s).functional (q f)).re) :
    ∀ᶠ n in (U : Filter ℕ),∀ τ : TracialState A,
      (τ.functional (e n)).re+c≤(τ.functional (f n)).re := by
  classical
  by_contra h
  have hn : ∀ᶠ n in (U : Filter ℕ),¬∀ τ : TracialState A,
      (τ.functional (e n)).re+c≤(τ.functional (f n)).re :=
    (Ultrafilter.eventually_not).mpr h
  let s : ℕ → TracialState A := fun n =>
    if h : ∃ τ : TracialState A,(τ.functional (f n)).re<(τ.functional (e n)).re+c
    then h.choose else Classical.choice inferInstance
  have hs : ∀ᶠ n in (U : Filter ℕ),
      ((s n).functional (f n)).re≤((s n).functional (e n)).re+c := by
    filter_upwards [hn] with n hn
    push Not at hn
    simpa only [s, dite_eq_left hn] using hn.choose_spec.le
  have he := Complex.continuous_re.continuousAt.tendsto.comp (familyLimitTrace_tendsto T U s e)
  have hf := Complex.continuous_re.continuousAt.tendsto.comp (familyLimitTrace_tendsto T U s f)
  have hle := le_of_tendsto_of_tendsto hf (he.add_const c) hs
  change ((L s).functional (q f)).re≤((L s).functional (q e)).re+c at hle
  linarith [hgap s]

end DirectComparison

end
end

end OAI
