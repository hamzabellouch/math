import OAI.Probability.FreeIsing.Trees.ConeComplementField
import OAI.Probability.FreeIsing.Trees.InwardCutFields

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal
namespace Problem367.PathSideBranches
open ConnectedHull

private theorem tanh_nonneg {beta : ℝ} (hb : 0 ≤ beta) : 0 ≤ Real.tanh beta := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hb) (Real.cosh_pos beta).le

theorem inward_cut_difference_initial_sharp {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) {k : ℕ} (hk : k < v.1.length) :
    ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      |inwardGaussianField μ t v k z - cutInwardGaussianField μ t v k k z| ≤ beta := by
  by_cases hk0 : k = 0
  · subst k
    have hcone : cone (takeVertex v 0) = Set.univ := by
      ext u
      simp [cone, takeVertex]
    filter_upwards [] with z
    simp only [inwardGaussianField, cutInwardGaussianField, hcone,
      Set.compl_eq_univ_sdiff, sub_self, abs_zero]
    exact hbeta
  · let A := cone (takeVertex v k)
    let B := cone (takeVertex v (k + 1))
    have hBA : B ⊆ A := cone_takeVertex_antitone v (by omega)
    have hr : (takeVertex v k).1 ≠ [] := by
      intro h
      have hl := congrArg List.length h
      simp only [takeVertex, List.length_take, Nat.min_eq_left hk.le,
        List.length_nil] at hl
      omega
    have hparent : parentVertex (takeVertex v k) ∈ Aᶜ := parent_not_mem_cone _ hr
    have hroot : takeVertex v k ∈ A \ B :=
      ⟨List.prefix_refl _, takeVertex_not_mem_next_cone v hk⟩
    have heq : (A \ B) ∪ Aᶜ = Bᶜ := by
      ext u
      simp only [Set.mem_union, Set.mem_sdiff, Set.mem_compl_iff]
      constructor
      · rintro (h | h)
        · exact h.2
        · exact fun hb => h (hBA hb)
      · intro hb
        by_cases ha : u ∈ A
        · exact Or.inl ⟨ha, hb⟩
        · exact Or.inr ha
    have hfield := hμ.selected_gaussian_inside_subset_complement_field hbeta t
      (takeVertex v k) hr (A \ B) Aᶜ Set.sdiff_subset (fun _ h => h) hroot hparent
    have hbound := hμ.selected_gaussian_posterior_field_bound hbeta t
      (Subtype.val : (Aᶜ : Set (TreeVertex d)) → TreeVertex d)
      (parentVertex (takeVertex v k)) ⟨⟨_, hparent⟩, rfl⟩
    filter_upwards [hfield, hbound] with z hf hb
    change regionGaussianField μ t ((A \ B) ∪ Aᶜ) (takeVertex v k) z =
      regionGaussianField μ t (A \ B) (takeVertex v k) z + _ at hf
    rw [heq] at hf
    change inwardGaussianField μ t v k z = cutInwardGaussianField μ t v k k z + _ at hf
    rw [hf, add_sub_cancel_left]
    simpa only [Real.artanh_tanh] using
      statisticMessage_abs_le (tanh_nonneg hbeta) (Real.tanh_lt_one beta) (abs_lt.mpr hb.1).le

theorem inward_cut_difference_geometric {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) (k : ℕ) :
    ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      ∀ i : ℕ, k + i < v.1.length →
        |inwardGaussianField μ t v (k + i) z -
          cutInwardGaussianField μ t v k (k + i) z| ≤ beta * Real.tanh beta ^ i := by
  apply ae_all_iff.mpr
  intro i
  by_cases hi : k + i < v.1.length
  · have aux : ∀ j : ℕ, k + j < v.1.length →
        ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
          |inwardGaussianField μ t v (k + j) z -
            cutInwardGaussianField μ t v k (k + j) z| ≤ beta * Real.tanh beta ^ j := by
      intro j
      induction j with
      | zero =>
        intro hj
        simpa only [Nat.add_zero, pow_zero, mul_one] using
          inward_cut_difference_initial_sharp hμ hbeta t v hj
      | succ j ih =>
        intro hj
        have hp := ih (by omega)
        have hs := inward_cut_difference_step hμ hbeta t v
          (k := k) (i := k + j) (by omega) (by omega)
        filter_upwards [hp, hs] with z hpz hsz
        calc
          _ ≤ Real.tanh beta * |inwardGaussianField μ t v (k + j) z -
              cutInwardGaussianField μ t v k (k + j) z| := by
            simpa only [Nat.add_assoc] using hsz
          _ ≤ Real.tanh beta * (beta * Real.tanh beta ^ j) :=
            mul_le_mul_of_nonneg_left hpz (tanh_nonneg hbeta)
          _ = beta * Real.tanh beta ^ (j + 1) := by rw [pow_succ]; ring
    filter_upwards [aux i hi] with z hz
    exact fun _ => hz
  · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)

end Problem367.PathSideBranches

end

end OAI
