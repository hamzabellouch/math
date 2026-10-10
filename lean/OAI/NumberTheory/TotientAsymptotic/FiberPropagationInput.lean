import OAI.NumberTheory.TotientAsymptotic.LocalSuffixRegular
import OAI.NumberTheory.TotientAsymptotic.PPTOriginalRegular
import OAI.NumberTheory.TotientAsymptotic.LocalFullCandidateScale

namespace OAI

/-! Discharge the fixed-seed fiber propagation input by pruning the actual
normal candidate family. Seed one also supplies Ford's lower counting bound. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem full_fiber_scale_family (d : ℕ) (hd : IsTotient d) :
    ∃ a K : ℝ,0 < a ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      0 < x ∧ ∃ S : Finset ℕ,a*(x/Real.log x)*G x (m x) ≤ (S.card:ℝ) ∧
        ∀ b∈S,0 < b ∧ ((d*b.totient:ℕ):ℝ) ≤ x ∧
          FullFiber d b ∧ (b:ℝ)/b.totient ≤ K := by
  obtain ⟨q,hqpos,hq⟩ := hd
  have hdpos : 0 < d := hq ▸ Nat.totient_pos.mpr hqpos
  obtain ⟨c,δ,L,hc,hδ,_hL,habundance⟩ := local_normal_candidate_abundance
  apply full_fiber_scale_of_local_count hc hδ d hdpos L
  apply local_full_candidate_count hc hδ d q hdpos hqpos hq L
    (habundance d hdpos) _ (local_suffix_regular_bound hc d hdpos L)
  filter_upwards [ppt_original_regular_count hc d hdpos L] with H hH
  filter_upwards [hH] with x hx
  intro F
  dsimp only
  intro _hinj hF
  exact hx F hF

/-- Pollack–Pomerance–Treviño, Lemma 4.1, in the bounded-ratio form used here. -/
theorem pptBoundedFiberPropagation (d : ℕ) (hd : IsTotient d) :
    PPTBoundedFiberPropagation d :=
  ppt_bounded_fiber_of_scale_family d (full_fiber_scale_family d hd)

theorem ford_scale_lower :
    ∃ a : ℝ,0 < a ∧ ∀ᶠ x : ℝ in atTop,a*(x/Real.log x)*G x (m x) ≤ V x := by
  apply ford_scale_lower_of_one_family
  exact full_fiber_scale_family 1 ⟨1,by decide,by simp⟩

/-- Ford's counting scale, with both bounds proved from the finite families. -/
theorem fordScaleBounds : FordScaleBounds := by
  obtain ⟨a,ha,hlower⟩ := ford_scale_lower
  obtain ⟨C,_hC,hupper⟩ := ford_scale_upper
  refine ⟨a,C,ha,?_⟩
  filter_upwards [hlower,hupper,scale_eventually_pos] with x hl hu hp
  constructor
  · exact (le_div_iff₀ hp).mpr (by simpa only [mul_assoc] using hl)
  · exact (div_le_iff₀ hp).mpr (by simpa only [mul_assoc] using hu)

end TotientAsymptotic

end

end OAI
