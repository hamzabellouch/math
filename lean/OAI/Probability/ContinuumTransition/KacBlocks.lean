import OAI.Probability.ContinuumTransition.GridCover

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def kacRowError (C : NNReal) (R u : ℝ) : ℝ :=
  (6*(C : ℝ)*u/R^4)*(2*(R+6*u))^3

noncomputable def cutKac (q : ℕ) (φ : ℝ → ℝ) (a R : ℝ) (x y : Space) : ℝ :=
  blockCut q (fun x y => φ ‖x-y‖) x y-a*scaledKernel R (x-y)

theorem measurable_cutKac (q : ℕ) {φ : ℝ → ℝ} (hφ : Measurable φ) (a R : ℝ) :
    Measurable (Function.uncurry (cutKac q φ a R)) := by
  have hb : Measurable (Function.uncurry (blockCut q (fun x y => φ ‖x-y‖))) :=
    measurable_blockCut q (hφ.comp (measurable_fst.sub measurable_snd).norm)
  apply hb.sub
  exact measurable_const.mul ((continuous_scaledKernelProfile R).measurable.comp
    (measurable_fst.sub measurable_snd).norm)

theorem kacRowError_nonneg (C : NNReal) {R u : ℝ} (hR : 0 ≤ R) (hu : 0 ≤ u) :
    0 ≤ kacRowError C R u := by unfold kacRowError; positivity

theorem kac_cut_grand_le {C : NNReal} (hC : LipschitzWith C kernel)
    {t β μ a S : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hS : 0 < S)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) {q : ℕ} (hq : 0 < q)
    (hcoeff : β*a*(1+kacRowError C S ((q : ℝ)/4))/2 ≤
      β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/((q : ℝ)/4))^3) (m : ℕ) :
    grandIntegral (gibbsFamily (cutKac q (physicalProfile t σ R) a S) β μ)
      (cube ((m : ℝ)*(q : ℝ)/2)) ≤
    (∑' n, quadraticGrandTerm (physicalProfile t σ R) β μ
      (β*a*(1+kacRowError C S ((q : ℝ)/4))/2) ((q : ℝ)/4) n)^(gridIndices m 1).card := by
  let u := (q : ℝ)/4
  let γ := a*(1+kacRowError C S u)/u^3
  let s := gridIndices m 1
  let D := ⋃ k ∈ s, gridBox u k
  have hu : 0 < u := by dsimp only [u]; positivity
  have hγ : 0 ≤ γ := div_nonneg (mul_nonneg ha (by linarith [kacRowError_nonneg C hS.le hu.le]))
    (pow_pos hu 3).le
  have hγeq : β*γ/2*u^3 = β*a*(1+kacRowError C S u)/2 := by
    dsimp only [γ]; field_simp
  have hcoeff' : β*γ/2*u^3 ≤ β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/u)^3 := by
    rw [hγeq]; exact hcoeff
  have hW := grandFinite_quadraticBlocks (μ := μ) ht hβ hγ hσ hR hs hsmall hq hcoeff' s
  have hD : MeasurableSet D := by
    exact MeasurableSet.biUnion (s.countable_toSet) (fun k _ => measurableSet_gridBox u k)
  have hle (ι : Type) [Fintype ι] (x : ι → Space) (hx : ∀ i, x i ∈ D) :
      gibbsFamily (cutKac q (physicalProfile t σ R) a S) β μ ι x ≤
        gibbsFamily (quadraticBlock q (physicalProfile t σ R) γ) β (μ+β*γ/2) ι x := by
    let c (i : ι) : s := ⟨gridIndex u (x i), gridIndex_mem_of_mem_union hu (hx i)⟩
    exact kac_gibbsFamily_le_quadratic hC hS hβ ha hq _ s c x (fun i => mem_gridBox hu (x i))
  have hF := GrandFinite.of_le_on hD hW
    (fun ι _ => measurable_gibbsFamily (measurable_cutKac q (measurable_physicalProfile t hσ hR hs) a S) β μ ι)
    (gibbsFamily_nonneg _ _ _) hle
  have hAD : cube ((m : ℝ)*(q : ℝ)/2) ⊆ D := by
    convert cube_subset_gridBlocks hu m using 1
    dsimp only [u, D, s]
    congr 1
    ring
  have hFA := hF.mono_set hAD (gibbsFamily_nonneg _ _ _)
  apply (grandIntegral_mono_set _ hAD (gibbsFamily_nonneg _ _ _)
    (fun n => hF.integrable (Fin n)) hFA.summable hF.summable).trans
  apply (grandIntegral_mono _ _ hD (fun n => hF.integrable (Fin n))
    (fun n => hW.integrable (Fin n)) hF.summable hW.summable (fun n => hle (Fin n))).trans
  have hh := quadraticBlocks_grand_le (μ := μ) ht hβ hγ hσ hR hs hsmall hq hcoeff' s
  change _ ≤ (∑' n, quadraticGrandTerm (physicalProfile t σ R) β μ (β*γ/2*u^3) u n)^s.card at hh
  rw [hγeq] at hh
  exact hh

end ContinuumTemperature
end

end OAI
