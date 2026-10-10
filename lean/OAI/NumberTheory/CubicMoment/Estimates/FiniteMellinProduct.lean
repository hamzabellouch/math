import OAI.NumberTheory.CubicMoment.Estimates.MellinSeries

namespace OAI

/-! Absolute Mellin separation of a finite product-norm weight. This is the
exact analytic bridge used after the smooth short-convolution partition. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem smooth_mellin_finite {κ : Type*} [Fintype κ]
    (a : κ → ℂ) (N : κ → ℝ) (hN : ∀ i, 0 < N i)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (σ : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    (∑ i, a i*W (N i/Z)) = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, mellin W (σ+(τ:ℂ)*Complex.I)*(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*
        (∑ i, a i*(N i:ℂ)^(-(σ+(τ:ℂ)*Complex.I))) := by
  simpa only [normDirichletSeries,tsum_fintype] using
    smooth_mellin_series a N hN W hW hpos hsm σ (hasSum_fintype _).summable hZ

lemma nonnegative_product_cpow {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (hN : ∀ i ∈ S, 0 ≤ N i) (s : ℂ) :
    ((∏ i ∈ S, N i : ℝ):ℂ)^s = ∏ i ∈ S, (N i:ℂ)^s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hN i (Finset.mem_insert_self i S))
        (Finset.prod_nonneg (fun j hj => hN j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hN j (Finset.mem_insert_of_mem hj)),Finset.prod_insert hi]

theorem smooth_mellin_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (a : (i : ι) → κ i → ℂ) (N : (i : ι) → κ i → ℝ)
    (hN : ∀ i x, 0 < N i x)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (σ : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    (∑ x : (i : ι) → κ i, (∏ i, a i (x i))*W ((∏ i, N i (x i))/Z)) =
      ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
        mellin W (σ+(τ:ℂ)*Complex.I)*(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*
          ∏ i, (∑ x : κ i, a i x*(N i x:ℂ)^(-(σ+(τ:ℂ)*Complex.I))) := by
  rw [smooth_mellin_finite (fun x : (i : ι) → κ i => ∏ i, a i (x i))
    (fun x => ∏ i, N i (x i)) (fun x => Finset.prod_pos (fun i _ => hN i (x i)))
    W hW hpos hsm σ hZ]
  congr 1
  apply integral_congr_ae
  filter_upwards with τ
  congr 1
  rw [Fintype.prod_sum (fun (i : ι) (x : κ i) =>
    a i x*(N i x:ℂ)^(-(σ+(τ:ℂ)*Complex.I)))]
  apply Finset.sum_congr rfl
  intro x _
  rw [nonnegative_product_cpow _ _ (fun i _ => (hN i (x i)).le),Finset.prod_mul_distrib]

end CubicFirstMoment

end

end OAI
