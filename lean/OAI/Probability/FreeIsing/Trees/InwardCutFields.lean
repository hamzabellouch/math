import OAI.Probability.FreeIsing.Trees.ConeComplementFusion
import OAI.Probability.FreeIsing.Trees.PathCutCost

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal
namespace Problem367.PathSideBranches
open ConnectedHull

def regionGaussianField {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (t : ℝ≥0) (S : Set (TreeVertex d)) (r : TreeVertex d)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) : ℝ :=
  Real.artanh (selectedPosterior
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
    (fun s x => (t : ℝ) * spinSign s + x)
    (Subtype.val : S → TreeVertex d) r z)

def inwardGaussianField {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (t : ℝ≥0) (v : TreeVertex d) (i : ℕ) :=
  regionGaussianField μ t (cone (takeVertex v (i + 1)))ᶜ (takeVertex v i)

def cutInwardGaussianField {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (t : ℝ≥0) (v : TreeVertex d) (k i : ℕ) :=
  regionGaussianField μ t
    (cone (takeVertex v k) \ cone (takeVertex v (i + 1))) (takeVertex v i)

theorem measurable_regionGaussianField_noisyRegion {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    (S : Set (TreeVertex d)) (r : TreeVertex d) :
    Measurable[noisyRegionSigma (A := ℝ) S] (regionGaussianField μ t S r) :=
  measurable_selectedField_noisyRegion _
    (((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd) S r

theorem measurable_cutInwardGaussianField_noisyRegion {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    (v : TreeVertex d) (k i : ℕ) :
    Measurable[noisyRegionSigma (A := ℝ) (cone (takeVertex v k))]
      (cutInwardGaussianField μ t v k i) :=
  (measurable_regionGaussianField_noisyRegion μ t _ _).mono
    (noisyRegionSigma_mono Set.sdiff_subset) le_rfl

theorem cone_takeVertex_antitone {d : ℕ} (v : TreeVertex d) {i j : ℕ}
    (hij : i ≤ j) : cone (takeVertex v j) ⊆ cone (takeVertex v i) := by
  apply cone_mono
  exact List.take_isPrefix_take.mpr (Or.inl hij)

theorem parent_takeVertex_succ {d : ℕ} (v : TreeVertex d) {i : ℕ}
    (hi : i < v.1.length) : parentVertex (takeVertex v (i + 1)) = takeVertex v i := by
  apply treeAdj_parent_of_length_lt (prefix_adj v hi)
  simp only [takeVertex, List.length_take, Nat.min_eq_left hi.le,
    Nat.min_eq_left (show i + 1 ≤ v.1.length by omega)]
  omega

theorem takeVertex_not_mem_next_cone {d : ℕ} (v : TreeVertex d) {i : ℕ}
    (hi : i < v.1.length) : takeVertex v i ∉ cone (takeVertex v (i + 1)) := by
  intro h
  have hl := h.length_le
  simp only [takeVertex, List.length_take, Nat.min_eq_left hi.le,
    Nat.min_eq_left (show i + 1 ≤ v.1.length by omega)] at hl
  omega

private theorem takeVertex_succ_ne_nil {d : ℕ} (v : TreeVertex d) {i : ℕ}
    (hi : i < v.1.length) : (takeVertex v (i + 1)).1 ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp only [takeVertex, List.length_take,
    Nat.min_eq_left (show i + 1 ≤ v.1.length by omega), List.length_nil] at hl
  omega

private theorem diff_union_compl_of_subset {α : Type*} {A B : Set α}
    (hBA : B ⊆ A) : (A \ B) ∪ Aᶜ = Bᶜ := by
  ext x
  simp only [Set.mem_union, Set.mem_sdiff, Set.mem_compl_iff]
  constructor
  · rintro (h | h)
    · exact h.2
    · exact fun hb => h (hBA hb)
  · intro hb
    by_cases ha : x ∈ A
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ha

private theorem diff_union_diff_of_subset {α : Type*} {A B C : Set α}
    (hBA : B ⊆ A) (hAC : A ⊆ C) : (A \ B) ∪ (C \ A) = C \ B := by
  ext x
  simp only [Set.mem_union, Set.mem_sdiff]
  constructor
  · rintro (h | h)
    · exact ⟨hAC h.1, h.2⟩
    · exact ⟨h.1, fun hb => h.2 (hBA hb)⟩
  · rintro ⟨hc, hb⟩
    by_cases ha : x ∈ A
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨hc, ha⟩

theorem inward_cut_difference_step {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) {k i : ℕ}
    (hki : k ≤ i) (hi : i + 1 < v.1.length) :
    ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      |inwardGaussianField μ t v (i + 1) z -
        cutInwardGaussianField μ t v k (i + 1) z| ≤
      Real.tanh beta * |inwardGaussianField μ t v i z -
        cutInwardGaussianField μ t v k i z| := by
  let A := cone (takeVertex v (i + 1))
  let B := cone (takeVertex v (i + 1 + 1))
  let C := cone (takeVertex v k)
  have hBA : B ⊆ A := cone_takeVertex_antitone v (by omega)
  have hAC : A ⊆ C := cone_takeVertex_antitone v (by omega)
  have hpA : takeVertex v i ∉ A := takeVertex_not_mem_next_cone v (by omega)
  have hpC : takeVertex v i ∈ C := List.take_isPrefix_take.mpr (Or.inl hki)
  have hrS : takeVertex v (i + 1) ∈ A \ B :=
    ⟨List.prefix_refl _, takeVertex_not_mem_next_cone v hi⟩
  have h := hμ.selected_gaussian_subset_complement_field_difference hbeta t
    (takeVertex v (i + 1)) (takeVertex_succ_ne_nil v (by omega))
    (A \ B) Aᶜ (C \ A) Set.sdiff_subset (fun _ hx => hx) (fun _ hx => hx.2)
    hrS (by rw [parent_takeVertex_succ v (by omega)]; exact hpA)
    (by rw [parent_takeVertex_succ v (by omega)]; exact ⟨hpC, hpA⟩)
  have hST : (A \ B) ∪ Aᶜ = Bᶜ := diff_union_compl_of_subset hBA
  have hSU : (A \ B) ∪ (C \ A) = C \ B := diff_union_diff_of_subset hBA hAC
  filter_upwards [h] with z hz
  have hz' := hz.1
  change |regionGaussianField μ t ((A \ B) ∪ Aᶜ) (takeVertex v (i + 1)) z -
    regionGaussianField μ t ((A \ B) ∪ (C \ A)) (takeVertex v (i + 1)) z| ≤
    Real.tanh beta * |regionGaussianField μ t Aᶜ
      (parentVertex (takeVertex v (i + 1))) z -
      regionGaussianField μ t (C \ A) (parentVertex (takeVertex v (i + 1))) z| at hz'
  rw [hST, hSU, parent_takeVertex_succ v (by omega)] at hz'
  exact hz'

theorem inward_cut_difference_initial {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) {k : ℕ} (hk : k < v.1.length) :
    ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      |inwardGaussianField μ t v k z - cutInwardGaussianField μ t v k k z| ≤
        2 * (d : ℝ) * beta := by
  have hn := takeVertex_not_mem_next_cone v hk
  have hfull := hμ.selected_gaussian_posterior_field_bound hbeta t
    (Subtype.val : ((cone (takeVertex v (k + 1)))ᶜ : Set (TreeVertex d)) → TreeVertex d)
    (takeVertex v k) ⟨⟨_, hn⟩, rfl⟩
  have hcut := hμ.selected_gaussian_posterior_field_bound hbeta t
    (Subtype.val : (cone (takeVertex v k) \ cone (takeVertex v (k + 1)) : Set (TreeVertex d)) → TreeVertex d)
    (takeVertex v k) ⟨⟨_, ⟨List.prefix_refl _, hn⟩⟩, rfl⟩
  filter_upwards [hfull, hcut] with z hf0 hc0
  have hf := hf0.2
  have hc := hc0.2
  change |inwardGaussianField μ t v k z - PlantedSymmetry.observation t z
    (takeVertex v k)| ≤ (d : ℝ) * beta at hf
  change |cutInwardGaussianField μ t v k k z - PlantedSymmetry.observation t z
    (takeVertex v k)| ≤ (d : ℝ) * beta at hc
  calc
    _ ≤ |inwardGaussianField μ t v k z - PlantedSymmetry.observation t z
        (takeVertex v k)| + |cutInwardGaussianField μ t v k k z -
        PlantedSymmetry.observation t z (takeVertex v k)| := by
      simpa only [abs_sub_comm] using (abs_sub_le
        (inwardGaussianField μ t v k z)
        (PlantedSymmetry.observation t z (takeVertex v k))
        (cutInwardGaussianField μ t v k k z))
    _ ≤ 2 * (d : ℝ) * beta := by linarith

end Problem367.PathSideBranches

end

end OAI
