import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceCollisionBirthday
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelectedSum
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalExpectations

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError
open Construction CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryCompensationBiasedKernelSum HistoryPairVariableBSquareErrorSelectedSum
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

def originalPrincipalSum (sources : SourceFamily) (origin τ : ι → ℕ)
    (mask : ∀p:Pattern τ,(Block p → CommonSample sources origin) → ℝ)
    (test : ∀p:Pattern τ,BlockDraw p (CommonSample sources origin) → ℂ) : ℂ :=
  ∑p:Pattern τ,∑b:BlockDraw p (CommonSample sources origin),
    (((∏q,blockWeight p (sourceWeight sources origin) q (b.val q))*
      (∏i:ι,((expand p b i).val:ℝ)):ℝ):ℂ) * ((mask p b.val:ℂ)*test p b)

def originalBulkPrincipalSum (sources : SourceFamily) (origin τ : ι → ℕ)
    (μ : FinitePrior Ω)
    (mask : Ω → ∀p:Pattern τ,(Block p → CommonSample sources origin) → ℝ)
    (test : Ω → ∀p:Pattern τ,BlockDraw p (CommonSample sources origin) → ℂ) : ℂ :=
  ∑p:Pattern τ,∑b:BlockDraw p (CommonSample sources origin),
    (((∏q,blockWeight p (sourceWeight sources origin) q (b.val q))*
      (∏i:ι,((expand p b i).val:ℝ)):ℝ):ℂ) *
      μ.cmean (fun u => (mask u p b.val:ℂ)*test u p b)

theorem originalBulkPrincipalSum_eq_cmean (sources : SourceFamily) (origin τ : ι → ℕ)
    (μ : FinitePrior Ω)
    (mask : Ω → ∀p:Pattern τ,(Block p → CommonSample sources origin) → ℝ)
    (test : Ω → ∀p:Pattern τ,BlockDraw p (CommonSample sources origin) → ℂ) :
    originalBulkPrincipalSum sources origin τ μ mask test =
      μ.cmean (fun u => originalPrincipalSum sources origin τ (mask u) (test u)) := by
  unfold originalBulkPrincipalSum originalPrincipalSum
  simp_rw [FinitePrior.cmean_sum,FinitePrior.cmean_mul_left]

theorem originalPrincipalSum_norm_le (sources : SourceFamily) (origin τ : ι → ℕ)
    (K : ∀p:Pattern τ,(Block p → CommonSample sources origin) → Block p → ℝ)
    (mask : ∀p:Pattern τ,(Block p → CommonSample sources origin) → ℝ)
    (δ : ℝ) (test : ∀p:Pattern τ,BlockDraw p (CommonSample sources origin) → ℂ)
    (hδ : 0 ≤ δ) (hK : ∀p b q,0 ≤ K p b q) (hm : ∀p b,0 ≤ mask p b)
    (ht : ∀p b,mask p b.val ≠ 0 → ‖test p b‖ ≤ δ*∏q,K p b.val q) :
    ‖originalPrincipalSum sources origin τ mask test‖ ≤
      δ*biasedKernelSum sources origin τ K mask := by
  let e := fun (p:Pattern τ) (b:BlockDraw p (CommonSample sources origin)) =>
    if mask p b.val = 0 then (0:ℂ) else test p b
  have he : ∀p b,‖e p b‖ ≤ δ*∏q,K p b.val q := by
    intro p b
    by_cases hz : mask p b.val = 0
    · simp only [e,hz,ite_true,norm_zero]
      exact mul_nonneg hδ (Finset.prod_nonneg (fun q _ => hK p b.val q))
    · simpa only [e,hz,ite_false] using ht p b hz
  have eq : originalPrincipalSum sources origin τ mask test =
      originalPrincipalSum sources origin τ mask e := by
    unfold originalPrincipalSum
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hz : mask p b.val = 0 <;> simp only [e,hz,ite_true,ite_false,Complex.ofReal_zero,zero_mul,mul_zero]
  rw [eq]
  exact original_error_sum_norm_le_biasedKernelSum sources origin τ K mask δ e hδ hK hm he

theorem originalPrincipalSum_sub (sources : SourceFamily) (origin τ : ι → ℕ)
    (mask : ∀p:Pattern τ,(Block p → CommonSample sources origin) → ℝ)
    (f g : ∀p:Pattern τ,BlockDraw p (CommonSample sources origin) → ℂ) :
    originalPrincipalSum sources origin τ mask f-originalPrincipalSum sources origin τ mask g =
      originalPrincipalSum sources origin τ mask (fun p b => f p b-g p b) := by
  simp only [originalPrincipalSum,mul_sub,Finset.sum_sub_distrib]

theorem originalBulkPrincipalSum_error_le (sources : SourceFamily) (origin τ : ι → ℕ)
    (μ : FinitePrior Ω) (Bad : Ω → Prop)
    (K : Ω → ∀p:Pattern τ,(Block p → CommonSample sources origin) → Block p → ℝ)
    (mask : Ω → ∀p:Pattern τ,(Block p → CommonSample sources origin) → ℝ)
    (f g : Ω → ∀p:Pattern τ,BlockDraw p (CommonSample sources origin) → ℂ)
    (W M : ℝ) (hW : 0 ≤ W) (_hM : 0 ≤ M)
    (hK : ∀u p b q,0 ≤ K u p b q) (hm : ∀u p b,0 ≤ mask u p b)
    (hbudget : ∀u,μ.mass u ≠ 0 → biasedKernelSum sources origin τ (K u) (mask u) ≤ M)
    (heq : ∀u,μ.mass u ≠ 0 → ¬Bad u → ∀p b,mask u p b.val ≠ 0 → f u p b=g u p b)
    (hbound : ∀u,μ.mass u ≠ 0 → Bad u → ∀p b,mask u p b.val ≠ 0 →
      ‖f u p b-g u p b‖ ≤ W*∏q,K u p b.val q) :
    ‖originalBulkPrincipalSum sources origin τ μ mask f-
      originalBulkPrincipalSum sources origin τ μ mask g‖ ≤
        W*M*μ.mean (fun u => if Bad u then 1 else 0) := by
  rw [originalBulkPrincipalSum_eq_cmean,originalBulkPrincipalSum_eq_cmean]
  let F := fun u => originalPrincipalSum sources origin τ (mask u) (f u)
  let G := fun u => originalPrincipalSum sources origin τ (mask u) (g u)
  change ‖μ.cmean F-μ.cmean G‖ ≤ _
  have hsub : μ.cmean F-μ.cmean G = μ.cmean (fun u => F u-G u) := by
    simp only [FinitePrior.cmean,mul_sub,Finset.sum_sub_distrib]
  rw [hsub]
  apply (μ.norm_cmean_le _).trans
  change (∑u,μ.mass u*‖F u-G u‖) ≤ _
  rw [FinitePrior.mean,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  by_cases hz : μ.mass u = 0
  · simp only [hz,zero_mul,mul_zero,le_refl]
  · have hnorm : ‖F u-G u‖ ≤ if Bad u then W*M else 0 := by
      dsimp only [F,G]
      rw [originalPrincipalSum_sub]
      by_cases hb : Bad u
      · rw [ite_eq_left hb]
        exact (originalPrincipalSum_norm_le sources origin τ (K u) (mask u) W _
          hW (hK u) (hm u) (hbound u hz hb)).trans
            (mul_le_mul_of_nonneg_left (hbudget u hz) hW)
      · rw [ite_eq_right hb]
        have hn := originalPrincipalSum_norm_le sources origin τ (K u) (mask u) 0
          (fun p b => f u p b-g u p b) (by norm_num) (hK u) (hm u)
          (fun p b ha => by rw [heq u hz hb p b ha]; simp only [sub_self,norm_zero,zero_mul,le_refl])
        simpa only [zero_mul] using hn
    calc
      _ ≤ μ.mass u*(if Bad u then W*M else 0) :=
        mul_le_mul_of_nonneg_left hnorm (μ.mass_nonneg u)
      _ = W*M*(μ.mass u*(if Bad u then 1 else 0)) := by split_ifs <;> ring

end Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError

end

end OAI
