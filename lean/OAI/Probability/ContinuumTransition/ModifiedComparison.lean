import OAI.Probability.ContinuumTransition.GrandPerturbation

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gibbsFamily_perturbation (U V : Space → Space → ℝ) (β h : ℝ)
    (ι : Type) [Fintype ι] (x : ι → Space) :
    gibbsFamily U β h ι x = gibbsFamily V β h ι x *
      Real.exp (-β*gibbsEnergy (fun x y => U x y-V x y) x) := by
  unfold gibbsFamily
  split_ifs
  · rw [gibbsEnergy_sub, ← Real.exp_add]
    congr 1
    ring
  · simp

theorem modified_log_grand_comparison {t β : ℝ} (ht : 0 < t) (hβ : 0 < β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {U V : Space → Space → ℝ} (hU : CellLowerBound t σ R U) (hV : CellLowerBound t σ R V)
    (hUm : Measurable (Function.uncurry U)) (hVm : Measurable (Function.uncurry V))
    (hUs : ∀ x y, U x y = U y x) (hVs : ∀ x y, V x y = V y x)
    (hVU : ∀ x y, V x y ≤ U x y) (h L : ℝ)
    (J : cubeCells L → cubeCells L → ℝ) (hJ : ∀ k l, 0 ≤ J k l)
    (hbound : ∀ (k l : cubeCells L) x y, x ∈ cube L → y ∈ cube L →
      cellIndex x = k → cellIndex y = l → U x y-V x y ≤ J k l) :
    Real.log (grandIntegral (gibbsFamily V β h) (cube L))-
      Real.log (grandIntegral (gibbsFamily U β h) (cube L)) ≤
      β*(momentConstant t β h/2)*∑ k, ∑ l, J k l := by
  have hfin : volume (cube L) ≠ ⊤ := by rw [volume_cube]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hF := cellLowerBound_gibbs_finite ht.le hβ.le hσ hR hs hsmall hV hVm hfin h
  have hF₀ := cellLowerBound_gibbs_finite ht.le hβ.le hσ hR hs hsmall hU hUm hfin h
  have hmom (z : cubeCells L) := cellLowerBound_gibbs_moment_finite ht.le hβ.le hσ hR hs hsmall
    hV hVm hfin h z (le_refl (β*(t^2/8)/4))
  have hp (z w : cubeCells L) := GrandFinite.occupationPair (gibbsFamily_nonneg V β h)
    (fun ι _ => measurable_gibbsFamily hVm β h ι) (measurableSet_latticeCell z)
    (measurableSet_latticeCell w) (by positivity : 0 < β*(t^2/8)/4) (hmom z) (hmom w)
  have hZ := grandIntegral_gibbs_pos V β h (cube L) hF.summable
  let W := fun x y => U x y-V x y
  have hWs (x y : Space) : W x y = W y x := by dsimp only [W]; rw [hUs x y, hVs x y]
  have hWm : Measurable (Function.uncurry W) := hUm.sub hVm
  have hWx : ∀ x y, 0 ≤ W x y := fun x y => sub_nonneg.mpr (hVU x y)
  have hcover : ∀ x ∈ cube L, ∃ k : cubeCells L, cellIndex x = (k : Lattice) := fun x hx =>
    ⟨⟨cellIndex x, cellIndex_mem_cubeCells hx⟩, rfl⟩
  obtain ⟨hH, hb⟩ := grand_interaction_bound (gibbsFamily V β h) (measurableSet_cube L)
    (gibbsFamily_nonneg V β h) (fun ι _ => measurable_gibbsFamily hVm β h ι)
    (fun k : cubeCells L => (k : Lattice)) Subtype.val_injective hcover J hJ W hWs hWm hWx hbound hp hZ
    (cellLowerBound_pair_moment ht hβ hσ hR hs hsmall hV hVm hVs h L)
  have he := grand_log_perturbation_bound (gibbsFamily U β h) (gibbsFamily V β h)
    (fun ι _ x => β*interactionFamily (gibbsFamily V β h) W ι x)
    (measurableSet_cube L) hF₀ hF (hH.const_mul β) hZ (gibbsFamily_nonneg V β h)
    (fun ι _ x => β*gibbsEnergy W x)
    (fun ι _ x => by simpa only [neg_mul] using gibbsFamily_perturbation U V β h ι x)
    (fun ι _ x => by dsimp only [interactionFamily]; ring)
  rw [grandIntegral_const_mul, mul_div_assoc] at he
  exact he.trans (by nlinarith only [mul_le_mul_of_nonneg_left hb hβ.le])

end ContinuumTemperature
end

end OAI
