import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.BallLipschitzExtension

namespace OAI

/-!
# Gluing separated parameter patches

Separation of the parameter centers and control of the image centers give a uniform
cross-patch Lipschitz estimate. The glued map extends to a parameter ball, whose
image covers all patches with an explicit Lipschitz constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def separatedPatchGluingConstant (M A L : ℝ≥0) : ℝ≥0 :=
  max M (2 * (3 * A + L))

theorem separated_parameter_patch_cross_dist_le {n d : ℕ} {ι : Type*}
    (a : ι → Ambient n) (c : ι → Ambient d) (r : ι → ℝ)
    (D : ι → Set (Ambient n)) (g : ι → Ambient n → Ambient d)
    (M A L : ℝ≥0) (hA : 0 < A)
    (hsep : ∀ i j : ι, i ≠ j → r i + r j ≤ (A : ℝ) * dist (a i) (a j))
    (hcenters : ∀ i j : ι, dist (c i) (c j) ≤ (L : ℝ) * dist (a i) (a j))
    (hparam : ∀ i : ι, ∀ u ∈ D i, dist u (a i) ≤ r i / (4 * (A : ℝ)))
    (himage : ∀ i : ι, ∀ u ∈ D i, dist (g i u) (c i) ≤ 3 * r i)
    (hLip : ∀ i : ι, LipschitzOnWith M (g i) (D i))
    (i j : ι) (u v : Ambient n) (hu : u ∈ D i) (hv : v ∈ D j) :
    dist (g i u) (g j v) ≤ (separatedPatchGluingConstant M A L : ℝ) * dist u v := by
  have hM : (M : ℝ) ≤ (separatedPatchGluingConstant M A L : ℝ) := by
    exact_mod_cast (le_max_left M (2 * (3 * A + L)))
  have hcross : 2 * (3 * (A : ℝ) + (L : ℝ)) ≤
      (separatedPatchGluingConstant M A L : ℝ) := by
    exact_mod_cast (le_max_right M (2 * (3 * A + L)))
  by_cases hij : i = j
  · subst j
    exact (hLip i |>.dist_le_mul u hu v hv).trans
      (mul_le_mul_of_nonneg_right hM dist_nonneg)
  have hAr : 0 < (A : ℝ) := hA
  have hden : 0 < 4 * (A : ℝ) := by positivity
  have hsmall : r i / (4 * (A : ℝ)) + r j / (4 * (A : ℝ)) ≤ dist (a i) (a j) / 4 := by
    calc
      _ = (r i + r j) / (4 * (A : ℝ)) := (add_div _ _ _).symm
      _ ≤ ((A : ℝ) * dist (a i) (a j)) / (4 * (A : ℝ)) :=
        div_le_div_of_nonneg_right (hsep i j hij) hden.le
      _ = _ := by field_simp
  have hcenterdist : dist (a i) (a j) ≤ 2 * dist u v := by
    have h1 := dist_triangle (a i) u (a j)
    have h2 := dist_triangle u v (a j)
    rw [dist_comm (a i) u] at h1
    have hpu := hparam i u hu
    have hpv := hparam j v hv
    have hd : 0 ≤ dist u v := dist_nonneg
    linarith
  have h1 := dist_triangle (g i u) (c i) (g j v)
  have h2 := dist_triangle (c i) (c j) (g j v)
  rw [dist_comm (c j) (g j v)] at h2
  calc
    _ ≤ 3 * (r i + r j) + (L : ℝ) * dist (a i) (a j) := by
      linarith [himage i u hu, himage j v hv, hcenters i j]
    _ ≤ (3 * (A : ℝ) + (L : ℝ)) * dist (a i) (a j) := by
      nlinarith [hsep i j hij]
    _ ≤ (3 * (A : ℝ) + (L : ℝ)) * (2 * dist u v) :=
      mul_le_mul_of_nonneg_left hcenterdist (by positivity)
    _ = (2 * (3 * (A : ℝ) + (L : ℝ))) * dist u v := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcross dist_nonneg

theorem exists_ball_lipschitz_cover_of_separated_parameter_patches {n d : ℕ} {ι : Type*}
    (a : ι → Ambient n) (c : ι → Ambient d) (r : ι → ℝ)
    (D : ι → Set (Ambient n)) (g : ι → Ambient n → Ambient d)
    (M A L : ℝ≥0) (hA : 0 < A)
    (hsep : ∀ i j : ι, i ≠ j → r i + r j ≤ (A : ℝ) * dist (a i) (a j))
    (hcenters : ∀ i j : ι, dist (c i) (c j) ≤ (L : ℝ) * dist (a i) (a j))
    (hparam : ∀ i : ι, ∀ u ∈ D i, dist u (a i) ≤ r i / (4 * (A : ℝ)))
    (himage : ∀ i : ι, ∀ u ∈ D i, dist (g i u) (c i) ≤ 3 * r i)
    (hLip : ∀ i : ι, LipschitzOnWith M (g i) (D i))
    (ρ : ℝ) (hball : (⋃ i : ι, D i) ⊆ ball (0 : Ambient n) ρ) :
    ∃ F : ball (0 : Ambient n) ρ → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) * separatedPatchGluingConstant M A L) F ∧
      (⋃ i : ι, g i '' D i) ⊆ Set.range F := by
  classical
  let U := ⋃ i : ι, D i
  let j : ∀ u : Ambient n, u ∈ U → ι := fun u hu => (mem_iUnion.mp hu).choose
  have hj (u : Ambient n) (hu : u ∈ U) : u ∈ D (j u hu) := (mem_iUnion.mp hu).choose_spec
  let G : Ambient n → Ambient d := fun u => if hu : u ∈ U then g (j u hu) u else 0
  have hG (u : Ambient n) (hu : u ∈ U) : G u = g (j u hu) u := by simp only [G, dite_eq_left hu]
  have hcross := separated_parameter_patch_cross_dist_le a c r D g M A L hA
    hsep hcenters hparam himage hLip
  have hGLip : LipschitzOnWith (separatedPatchGluingConstant M A L) G U := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    rw [hG u hu, hG v hv]
    exact hcross (j u hu) (j v hv) u v (hj u hu) (hj v hv)
  have heq (i : ι) (u : Ambient n) (hu : u ∈ D i) : G u = g i u := by
    have huU : u ∈ U := mem_iUnion.mpr ⟨i, hu⟩
    rw [hG u huU]
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    simpa only [dist_self, mul_zero] using! hcross (j u huU) i u u (hj u huU) hu
  obtain ⟨F, hFLip, hcover⟩ := exists_ball_lipschitz_extension ρ U hball G
    (separatedPatchGluingConstant M A L) hGLip
  refine ⟨F, hFLip, ?_⟩
  intro y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  obtain ⟨u, hu, rfl⟩ := hi
  exact hcover ⟨u, mem_iUnion.mpr ⟨i, hu⟩, heq i u hu⟩

end

end RieszRectifiability

end OAI
