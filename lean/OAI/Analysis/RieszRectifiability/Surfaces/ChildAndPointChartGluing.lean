import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.RescaledChildChartGluing

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_ball_lipschitz_cover_of_children_and_points {n d : ℕ} {ι κ : Type*}
    (a : ι → Ambient n) (c : ι → Ambient d) (r : ι → ℝ)
    (b : κ → Ambient n) (y : κ → Ambient d)
    (f : ∀ i : ι, ball (0 : Ambient n) (r i) → Ambient d)
    (M A L : ℝ≥0) (hA : 0 < A)
    (hsep : ∀ i j : ι, i ≠ j → r i + r j ≤ (A : ℝ) * dist (a i) (a j))
    (hcenters : ∀ i j : ι, dist (c i) (c j) ≤ (L : ℝ) * dist (a i) (a j))
    (hsepPoint : ∀ i : ι, ∀ j : κ, r i ≤ (A : ℝ) * dist (a i) (b j))
    (hcenterPoint : ∀ i : ι, ∀ j : κ, dist (c i) (y j) ≤ (L : ℝ) * dist (a i) (b j))
    (hpointLip : ∀ i j : κ, dist (y i) (y j) ≤ (L : ℝ) * dist (b i) (b j))
    (himage : ∀ i : ι, Set.range (f i) ⊆ closedBall (c i) (3 * r i))
    (hLip : ∀ i : ι, LipschitzWith M (f i))
    (ρ : ℝ) (hball : ∀ i : ι, ball (a i) (r i / (4 * (A : ℝ))) ⊆ ball (0 : Ambient n) ρ)
    (hpointBall : ∀ j : κ, b j ∈ ball (0 : Ambient n) ρ) :
    ∃ F : ball (0 : Ambient n) ρ → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) *
        separatedPatchGluingConstant (M * (4 * A)) A L) F ∧
      ((⋃ i : ι, Set.range (f i)) ∪ Set.range y) ⊆ Set.range F := by
  classical
  have hs : 0 < 4 * A := by positivity
  have hc (i : ι) := exists_rescaled_ball_chart (r i) (a i) (4 * A) hs (f i) M (hLip i)
  choose g hg hrange using hc
  have hrange' (i : ι) : g i '' ball (a i) (r i / (4 * (A : ℝ))) = Set.range (f i) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using! hrange i
  have hg' (i : ι) : LipschitzOnWith (M * (4 * A)) (g i)
      (ball (a i) (r i / (4 * (A : ℝ)))) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using! hg i
  let a' : Sum ι κ → Ambient n := Sum.elim a b
  let c' : Sum ι κ → Ambient d := Sum.elim c y
  let r' : Sum ι κ → ℝ := Sum.elim r (fun _ => 0)
  let D' : Sum ι κ → Set (Ambient n) :=
    Sum.elim (fun i => ball (a i) (r i / (4 * (A : ℝ)))) (fun j => {b j})
  let g' : Sum ι κ → Ambient n → Ambient d := Sum.elim g (fun j _ => y j)
  have hsep' (i j : Sum ι κ) (hij : i ≠ j) :
      r' i + r' j ≤ (A : ℝ) * dist (a' i) (a' j) := by
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hsep i j (fun heq => hij (congrArg Sum.inl heq))
      | inr j => simpa only [r', a', Sum.elim_inl, Sum.elim_inr, add_zero] using! hsepPoint i j
    | inr i =>
      cases j with
      | inl j => simpa only [r', a', Sum.elim_inl, Sum.elim_inr, zero_add, dist_comm] using! hsepPoint j i
      | inr j =>
        change 0 + 0 ≤ _
        rw [zero_add]
        exact mul_nonneg A.coe_nonneg dist_nonneg
  have hcenters' (i j : Sum ι κ) : dist (c' i) (c' j) ≤ (L : ℝ) * dist (a' i) (a' j) := by
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hcenters i j
      | inr j => exact hcenterPoint i j
    | inr i =>
      cases j with
      | inl j => simpa only [c', a', Sum.elim_inl, Sum.elim_inr, dist_comm] using! hcenterPoint j i
      | inr j => exact hpointLip i j
  have hparam' (i : Sum ι κ) (u : Ambient n) (hu : u ∈ D' i) :
      dist u (a' i) ≤ r' i / (4 * (A : ℝ)) := by
    cases i with
    | inl i => exact le_of_lt hu
    | inr j =>
      have heq : u = b j := hu
      simp only [a', r', Sum.elim_inr, heq, dist_self, zero_div, le_refl]
  have himage' (i : Sum ι κ) (u : Ambient n) (hu : u ∈ D' i) :
      dist (g' i u) (c' i) ≤ 3 * r' i := by
    cases i with
    | inl i => exact himage i (hrange' i ▸ mem_image_of_mem (g i) hu)
    | inr j => simp only [g', c', r', Sum.elim_inr, dist_self, mul_zero, le_refl]
  have hLip' (i : Sum ι κ) : LipschitzOnWith (M * (4 * A)) (g' i) (D' i) := by
    cases i with
    | inl i => exact hg' i
    | inr j =>
      apply LipschitzOnWith.of_dist_le_mul
      intro u hu v hv
      change dist (y j) (y j) ≤ _
      rw [dist_self]
      positivity
  have hball' : (⋃ i : Sum ι κ, D' i) ⊆ ball (0 : Ambient n) ρ := by
    apply iUnion_subset
    intro i
    cases i with
    | inl i => exact hball i
    | inr j => exact singleton_subset_iff.mpr (hpointBall j)
  obtain ⟨F, hF, hcover⟩ := exists_ball_lipschitz_cover_of_separated_parameter_patches
    a' c' r' D' g' (M * (4 * A)) A L hA hsep' hcenters' hparam' himage' hLip' ρ hball'
  refine ⟨F, hF, ?_⟩
  intro v hv
  rcases hv with hchild | hpoint
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hchild
    have hi' : v ∈ g i '' ball (a i) (r i / (4 * (A : ℝ))) := hrange' i ▸ hi
    exact hcover (mem_iUnion.mpr ⟨Sum.inl i, hi'⟩)
  · obtain ⟨j, rfl⟩ := hpoint
    exact hcover (mem_iUnion.mpr ⟨Sum.inr j, b j, mem_singleton (b j), rfl⟩)

end

end RieszRectifiability

end OAI
