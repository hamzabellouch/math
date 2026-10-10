import OAI.Probability.RadialTransition.FreeClusterCover

namespace OAI

universe uIndex

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

def badLabels {ι : Type uIndex} [Fintype ι] (t : ℝ) (x : ι → Position) : Finset ι :=
  Finset.univ.filter (fun i => ∃ j, i ≠ j ∧ dist (x i) (x j) < 1 ∧
    ¬ (microLength t ≤ dist (x i) (x j) ∧ dist (x i) (x j) ≤ (1+(1:ℝ)/1000)*microLength t))

lemma after_removal_free {ι : Type uIndex} [Fintype ι] (t : ℝ) (x : ι → Position) :
    CoreFree t (fun i : {i // i ∉ badLabels t x} => x i) := by
  intro i j hij hd
  by_contra hs
  apply i.property
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.val, fun he => hij (Subtype.ext he), hd, hs⟩

lemma badLabels_energy {ι : Type uIndex} [Fintype ι] {t : ℝ} (ht : 0 ≤ t) (x : ι → Position) :
    t^2 * (badLabels t x).card / 2 ≤ orderedEnergy (corePotential t) x := by
  classical
  have hrow (i : ι) : (if i ∈ badLabels t x then t^2 else 0) ≤
      ∑ j, if i ≠ j then corePotential t (nndist (x i) (x j)) else 0 := by
    have hnon (j : ι) : (0:ℝ) ≤ if i ≠ j then corePotential t (nndist (x i) (x j)) else 0 := by
      split_ifs
      · exact coreReal_nonneg _ _
      · rfl
    by_cases hi : i ∈ badLabels t x
    · obtain ⟨j,hij,hd,hs⟩ := (Finset.mem_filter.mp hi).2
      have hfull : corePotential t (nndist (x i) (x j)) = t^2 := coreReal_full_of_not_shell ht hd.le hs
      rw [ite_eq_left hi]
      have hh := Finset.single_le_sum (fun k _ => hnon k) (Finset.mem_univ j)
      simpa only [ite_eq_left hij, hfull] using hh
    · rw [ite_eq_right hi]
      exact Finset.sum_nonneg (fun j _ => hnon j)
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hrow i)
  have hsum : (∑ i : ι, if i ∈ badLabels t x then t^2 else 0) = t^2*(badLabels t x).card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  rw [hsum] at hh
  exact div_le_div_of_nonneg_right hh (by norm_num)

def removalWeight (t β : ℝ) (s : Multiset Position) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β*t^2*s.card/2))

lemma measurable_removalWeight (t β : ℝ) : MeasurableConfiguration (removalWeight t β) := by
  intro s ι _
  simp only [removalWeight, Multiset.card_add, configurationMultiset_card]
  exact measurable_const

lemma particleBase_removalWeight {μ : Measure Position} (hμ : μ univ ≠ ⊤) (t β z : ℝ) :
    (∫⁻ x, removalWeight t β (particleMultiset x) ∂particleBase μ z) =
      ENNReal.ofReal (Real.exp ((μ univ).toReal*Real.exp (z-β*t^2/2))) := by
  have hm := measurable_particleObservable _ (measurable_removalWeight t β) 0
  simp only [zero_add] at hm
  have hh := lintegral_particleBase μ (z-β*t^2/2) (f := fun _ => (1:ℝ≥0∞)) measurable_const
  simp only [lintegral_one] at hh
  rw [lintegral_particleBase μ z hm, ← particleBase_univ hμ (z-β*t^2/2), hh]
  apply tsum_congr
  intro n
  simp only [particleMultiset, removalWeight, configurationMultiset_card, Fintype.card_fin,
    lintegral_const]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  congr 1
  ring_nf

end RadialTransition
end

end OAI
