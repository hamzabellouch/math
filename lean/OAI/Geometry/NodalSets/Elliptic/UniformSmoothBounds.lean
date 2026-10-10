import Mathlib.Analysis.Normed.Group.Bounded
import OAI.Geometry.NodalSets.Waves.UniformWaveJet
import OAI.Geometry.NodalSets.Waves.WaveSize

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

def DerivativeBound (k : ℕ) (f : Coord → ℂ) (x : Coord) (C : ℝ) : Prop :=
  ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j f x‖ ≤ C

lemma DerivativeBound.mono {k l : ℕ} {f : Coord → ℂ} {x : Coord} {C : ℝ}
    (h : DerivativeBound k f x C) (hl : l ≤ k) : DerivativeBound l f x C :=
  fun j hj ↦ h j (hj.trans hl)

lemma DerivativeBound.add {k : ℕ} {f g : Coord → ℂ} {x : Coord} {A B : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (ha : DerivativeBound k f x A) (hb : DerivativeBound k g x B) :
    DerivativeBound k (fun z ↦ f z + g z) x (A + B) := by
  intro j hj
  change ‖iteratedFDeriv ℝ j (f + g) x‖ ≤ A + B
  rw [iteratedFDeriv_add_apply (hf.of_le (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    (hg.of_le (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (ha j hj) (hb j hj))

lemma DerivativeBound.mul {k : ℕ} {f g : Coord → ℂ} {x : Coord} {A B : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : DerivativeBound k f x A) (hb : DerivativeBound k g x B) :
    DerivativeBound k (fun z ↦ f z * g z) x (2 ^ k * A * B) := by
  intro j hj
  have h := mul_derivative_power_bound hf hg j x hA (by norm_num : (0:ℝ) ≤ 1)
    (N := 1) (w := 1) (fun i hi ↦ by simpa using ha i (hi.trans hj))
    (fun i hi ↦ by simpa using hb i (hi.trans hj))
  simp only [one_pow, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hA) hB)

lemma DerivativeBound.sum {ι : Type*} (s : Finset ι) {k : ℕ}
    {f : ι → Coord → ℂ} {x : Coord} {C : ι → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ s, DerivativeBound k (f i) x (C i)) :
    DerivativeBound k (fun z ↦ ∑ i ∈ s, f i z) x (∑ i ∈ s, C i) := by
  intro j hj
  rw [iteratedFDeriv_fun_sum_apply (fun i hi ↦ ((hf i hi).of_le
    (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))).contDiffAt)]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi ↦ hb i hi j hj))

lemma coordPartial_derivative_norm_le (f : Coord → ℂ) (hf : ContDiff ℝ ∞ f)
    (i : Fin 4) (k : ℕ) (x : Coord) :
    ‖iteratedFDeriv ℝ k (coordPartial i f) x‖ ≤ ‖iteratedFDeriv ℝ (k+1) f x‖ := by
  let L : (Coord →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ (Pi.single i 1)
  have he : coordPartial i f = L ∘ fderiv ℝ f := rfl
  have hf' : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [he, L.iteratedFDeriv_comp_left hf'.contDiffAt
    (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))]
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ f) x‖ := ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ‖iteratedFDeriv ℝ k (fderiv ℝ f) x‖ := by
      gcongr
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro v
      have h := v.le_opNorm (Pi.single i (1 : ℝ))
      have hn : ‖(Pi.single i (1 : ℝ) : Coord)‖ ≤ 1 := by
        apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
        intro j
        by_cases hij : j = i <;> simp [hij]
      exact h.trans (by simpa using mul_le_mul_of_nonneg_left hn (norm_nonneg v))
    _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]

lemma DerivativeBound.coordPartial {k : ℕ} {f : Coord → ℂ} {x : Coord} {C : ℝ}
    (hf : ContDiff ℝ ∞ f) (h : DerivativeBound (k+1) f x C) (i : Fin 4) :
    DerivativeBound k (coordPartial i f) x C := by
  intro j hj
  exact (coordPartial_derivative_norm_le f hf i j x).trans (h (j+1) (by omega))

variable {T : Type*} [TopologicalSpace T]

theorem compact_smooth_derivative_bound (f : T → Coord → ℂ) (k : ℕ)
    (hc : ∀ j, j ≤ k → Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ j (f z.1) z.2))
    (s : Set T) (hs : IsCompact s) (R : ℝ) :
    ∃ C > 0, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ R → DerivativeBound k (f t) x C := by
  have hb (j : Fin (k+1)) : ∃ C > 0, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ j.val (f t) x‖ ≤ C := by
    obtain ⟨C, hC, h⟩ := ((hs.prod (isCompact_closedBall (0 : Coord) R)).image
      (hc j.val (by omega))).isBounded.exists_pos_norm_le
    refine ⟨C, hC, fun t ht x hx ↦ h _ ?_⟩
    exact ⟨(t,x), ⟨ht, by simpa using hx⟩, rfl⟩
  choose C hC h using hb
  refine ⟨∑ j, C j, ?_, ?_⟩
  · exact (hC ⟨0, by omega⟩).trans_le (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ _))
  · intro t ht x hx j hj
    exact (h ⟨j, by omega⟩ t ht x hx).trans
      (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ _))

end
end Yau.Jets

end OAI
