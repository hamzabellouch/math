import OAI.NumberTheory.Ostmann.Construction.FiniteTransfer

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
open Ostmann.Construction

def productPrior {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (μ : ι → FinitePrior κ) : FinitePrior (ι → κ) where
  mass w := ∏ i, (μ i).mass (w i)
  mass_nonneg w := Finset.prod_nonneg (fun i _ => (μ i).mass_nonneg (w i))
  mass_total := by
    rw [← Fintype.prod_sum]
    simp only [FinitePrior.mass_total, Finset.prod_const_one]

theorem productPrior_cmean {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (μ : ι → FinitePrior κ) (f : ι → κ → ℂ) :
    (productPrior μ).cmean (fun w => ∏ i, f i (w i)) =
      ∏ i, (μ i).cmean (f i) := by
  simp only [FinitePrior.cmean, productPrior, Complex.ofReal_prod,
    ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => ((μ i).mass x : ℂ)*f i x)).symm

def wordBin {κ β : Type*} [Fintype κ] [Fintype β] [DecidableEq β]
    (μ : FinitePrior κ) (f : κ → ℂ) (m : ℕ) (bin : (Fin m → κ) → β) (b : β) : ℂ :=
  (productPrior (fun _ : Fin m => μ)).cmean
    (fun w => if bin w=b then ∏ i, f (w i) else 0)

theorem sum_wordBin {κ β : Type*} [Fintype κ] [Fintype β] [DecidableEq β]
    (μ : FinitePrior κ) (f : κ → ℂ) (m : ℕ) (bin : (Fin m → κ) → β) :
    ∑ b, wordBin μ f m bin b = (μ.cmean f)^m := by
  have he : (∑ b, wordBin μ f m bin b) =
      (productPrior (fun _ : Fin m => μ)).cmean (fun w => ∏ i, f (w i)) := by
    unfold wordBin FinitePrior.cmean
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w hw
    rw [← Finset.mul_sum]
    simp
  rw [he, productPrior_cmean]
  simp

theorem exists_bin_norm {β : Type*} [Fintype β] [Nonempty β]
    (g : β → ℂ) : ∃ b, ‖∑ j, g j‖ ≤ (Fintype.card β:ℝ)*‖g b‖ := by
  classical
  obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image Finset.univ (fun b => ‖g b‖)
    Finset.univ_nonempty
  refine ⟨b,(norm_sum_le _ _).trans ?_⟩
  calc
    _ ≤ ∑ _j:β, ‖g b‖ := Finset.sum_le_sum (fun j hj => hmax j hj)
    _ = _ := by simp

theorem exists_wordBin_large {κ β : Type*} [Fintype κ] [Fintype β]
    [DecidableEq β] [Nonempty β] (μ : FinitePrior κ) (f : κ → ℂ)
    (m : ℕ) (bin : (Fin m → κ) → β) {δ:ℝ} (hδ : 0≤δ)
    (hmean : δ≤(μ.cmean f).re) :
    ∃ b, δ^m ≤ (Fintype.card β:ℝ)*‖wordBin μ f m bin b‖ := by
  obtain ⟨b,hb⟩ := exists_bin_norm (wordBin μ f m bin)
  rw [sum_wordBin, norm_pow] at hb
  exact ⟨b,(pow_le_pow_left₀ hδ (hmean.trans (Complex.re_le_norm _)) m).trans hb⟩
end Ostmann.Characters

end

end OAI
