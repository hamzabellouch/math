import OAI.NumberTheory.TotientAsymptotic.FullPrefixRatio
import OAI.NumberTheory.TotientAsymptotic.BoundedRatioValues
import OAI.NumberTheory.TotientAsymptotic.WeightedFiniteMap
import OAI.NumberTheory.TotientAsymptotic.UniqueValueNegligible

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace TotientAsymptotic

lemma bounded_ratio_tuple_weight (k : ℕ) {a b : ℝ} (hka : (k : ℝ)<a) (hb : 0<b) :
    ∃ β : ℝ, 0<β ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      β*(((boundedRatioValues x a b).card : ℝ)-(nonuniqueValues x H).card) ≤
        weightedTupleCount x H x (fk k) := by
  have ha : 0<a := (Nat.cast_nonneg k).trans_lt hka
  let ε : ℝ := (a-k)/(2*a)
  have hε : 0<ε := div_pos (sub_pos.mpr hka) (by positivity)
  let β : ℝ := min 1 ((a+k)/2-k)/b
  have hβ : 0<β := div_pos (lt_min zero_lt_one (by linarith)) hb
  refine ⟨β,hβ,?_⟩
  filter_upwards [full_prefix_defect hε,unique_prefix_finite_comparison,
    unique_tuple_least_preimage,eventually_ge_atTop 2] with H hQ hbij hleast hH
  filter_upwards [hQ,hbij,hleast] with x hQ hbij hleast
  apply FiniteMap.weighted_lower (tupleFinset x H x) (discardedTuples x H)
    (totientValues x) (nonuniqueValues x H) (boundedRatioValues x a b) tupleValue
    (fun τ => fk k ((ell τ.tail.d : ℝ)/τ.tail.d)) β hβ.le
    (Finset.filter_subset _ _) hbij.2.2
  · intro τ _
    exact fk_nonneg k (by positivity)
  · intro τ hτ hv
    have hbasic := (mem_tupleFinset (P_lt_self hH).le).mp (Finset.mem_sdiff.mp hτ).1
    obtain ⟨hq0,hql,hqu⟩ := hQ τ hbasic
    have hid := tuple_least_ratio_identity (P_lt_self hH).le hbasic (hleast τ hτ)
    obtain ⟨_,hva,hvb⟩ := Finset.mem_filter.mp hv
    have hv0 : 0≤(ell (tupleValue τ) : ℝ)/tupleValue τ := by positivity
    have hl : (a+k)/2 ≤ (ell τ.tail.d : ℝ)/τ.tail.d := by
      have hm := mul_le_mul_of_nonneg_right hva hq0.le
      have hm' := mul_le_mul_of_nonneg_left hql ha.le
      have heq : a*(1-ε)=(a+k)/2 := by dsimp [ε]; field_simp; ring
      rw [←heq]
      exact hm'.trans (hm.trans_eq hid)
    have hu : (ell τ.tail.d : ℝ)/τ.tail.d≤b := by
      rw [←hid]
      exact (mul_le_of_le_one_right hv0 hqu).trans hvb
    exact fk_lower_on_interval (by linarith : (k : ℝ)<(a+k)/2) hl hu

/-- A published positive family survives the exceptional-value discard and
has a positive, uniformly bounded-below tuple weight. -/
lemma positive_weighted_tuple_count (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input)
    {d k : ℕ} (hd : IsTotient d) (hseed : k*d<ell d) (hppt : PPTBoundedFiberPropagation d) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      c*tupleNormalization x ≤ weightedTupleCount x H x (fk k) := by
  obtain ⟨a,b,η,hka,hη,hb,hprop⟩ := bounded_ratio_positive_proportion hd hseed hppt
  obtain ⟨β,hβ,hweighted⟩ := bounded_ratio_tuple_weight k hka hb
  obtain ⟨δ,hδ,hE⟩ := nonunique_values_negligible hscale hstruct hbox hren hmertens h26 h51
  obtain ⟨c₀,c₁,hc₀,hscale⟩ := hscale
  let c := β*η*c₀/2
  refine ⟨c,by dsimp [c]; positivity,?_⟩
  filter_upwards [hweighted,hE,hδ.eventually (eventually_lt_nhds
    (show (0 : ℝ)<η*c₀/4 by positivity))] with H hw hE hδH
  filter_upwards [hw,hE (η*c₀/4) (by positivity),hprop,hscale,scale_eventually_pos]
    with x hw hE hp hs hN
  have hV : c₀*tupleNormalization x≤V x := (le_div_iff₀ hN).mp hs.1
  have hE' : ((nonuniqueValues x H).card : ℝ)≤(η*c₀/2)*tupleNormalization x := by
    apply hE.trans
    exact mul_le_mul_of_nonneg_right (by linarith) hN.le
  have hU : (η*c₀)*tupleNormalization x≤((boundedRatioValues x a b).card : ℝ) := by
    calc
      _ = η*(c₀*tupleNormalization x) := by ring
      _ ≤ η*V x := mul_le_mul_of_nonneg_left hV hη.le
      _ ≤ _ := hp
  calc
    c*tupleNormalization x ≤ β*(((boundedRatioValues x a b).card : ℝ)-(nonuniqueValues x H).card) := by
      dsimp [c]
      nlinarith
    _ ≤ _ := hw

end TotientAsymptotic

end

end OAI
