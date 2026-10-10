import OAI.NumberTheory.CubicMoment.Estimates.ComplementAbsoluteWeight
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedComplementMass

namespace OAI

/-! Linear complementary mass after a distinguished prime is removed.
The absolute tuple weights are collected before applying rough divisors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def complementProductSupport (S : ι → Finset Eisenstein) (i : ι) : Finset Eisenstein :=
  (coordinateComplementTuples S i).image (fun g => ∏ j, g j)

lemma complementProductSupport_primary (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    {r : Eisenstein} (hr : r ∈ complementProductSupport S i) : primary r := by
  obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hr
  exact complementTuple_primary S hS i hg

theorem complement_absolute_pair_mass (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    (W : ι → Eisenstein → ℂ) (hW : ∀ j, ∀ p ∈ S j, ‖W j p‖ ≤ 1)
    (D : Finset Eisenstein) (hD : ∀ d ∈ D, primary d) {Y w : ℝ}
    (hY : 0 ≤ Y) (hw : 1 ≤ w)
    (hrough : ∀ j, j ≠ i → ∀ p ∈ S j, W j p ≠ 0 → w ≤ norm p)
    {m : ℕ} (hsize : Y < w^m) :
    (∑ t ∈ (complementProductSupport S i ×ˢ D).filter
      (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ Y),
      complementAbsoluteWeight S i W t.1) ≤
      18*Y*((2^m:ℕ)*((Fintype.card ι)^(Fintype.card ι):ℕ)) := by
  let R := (complementProductSupport S i).filter
    (fun r => complementAbsoluteWeight S i W r ≠ 0)
  let f : Eisenstein → ℂ := fun r => (complementAbsoluteWeight S i W r : ℂ)
  have hf (r : Eisenstein) : ‖f r‖ = complementAbsoluteWeight S i W r := by
    simp only [f,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (complementAbsoluteWeight_nonneg S i W r)]
  have hbound := stopped_complement_mass R D
    (fun r hr => complementProductSupport_primary S hS i (Finset.mem_filter.mp hr).1) hD f
    (show 0 ≤ (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ) by positivity) hY
    (fun r _ => by rw [hf]; exact complementAbsoluteWeight_bound S hS i W hW r) hw
    (fun r hr p hp => complementAbsoluteWeight_rough S hS i W hrough
      (Finset.mem_filter.mp hr).2
      (primaryPrimeFactor_spec
        (complementProductSupport_primary S hS i (Finset.mem_filter.mp hr).1) hp).1
      (primaryPrimeFactor_spec
        (complementProductSupport_primary S hS i (Finset.mem_filter.mp hr).1) hp).2) hsize
  simp only [hf] at hbound
  apply le_trans ?_ hbound
  apply le_of_eq
  symm
  apply Finset.sum_subset
  · intro t ht
    obtain ⟨ht,hcond⟩ := Finset.mem_filter.mp ht
    obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hr).1,hd⟩,hcond⟩
  · intro t ht hn
    obtain ⟨ht,hcond⟩ := Finset.mem_filter.mp ht
    obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
    by_contra hne
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hr,hne⟩,hd⟩,hcond⟩)

end CubicFirstMoment

end

end OAI
