import OAI.Analysis.LipschitzHilbert.Fourier.SkippedLineAverage
import OAI.Analysis.LipschitzHilbert.Phase.LocalPredictionAssembly

namespace OAI

/-! The marked-factor integral for unequal source blocks. The error is paid
through its path sum; all averaging remains on the original nested line grid. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem source_skipped_path_integral
    (g : FiniteLineGrid) (T : SlopeBox) (K D y E : ℝ)
    (hK : 1 ≤ K) (hD : 0 ≤ D) (hwidth : g.width ≤ T.length)
    (level : ℕ → ℕ) (N : ℕ) (hlevel : ∀ n ≤ N, level n ≤ g.depth)
    (hmono : ∀ n < N, level n ≤ level (n+1))
    (good : Set ℝ) (beta error Γ : ℕ → ℝ → ℝ)
    (hΓ : ∀ n < N, ∀ x, 0 ≤ Γ n x)
    (hconstant : ∀ n < N, ∀ x z,
      g.index (level (n+1)) x = g.index (level (n+1)) z → Γ n x = Γ n z)
    (haverage : ∀ n < N, ∀ i : Fin (g.branching^g.depth),
      (∫ x in {x | g.index (level n) x = i}, Γ n x ∂volume.restrict g.root) ≤
        (volume.restrict g.root).real {x | g.index (level n) x = i})
    (hbeta : ∀ x ∈ g.root ∩ good, ∀ n < N, 0 ≤ beta n x)
    (hcomparison : ∀ x ∈ g.root ∩ good, ∀ n < N,
      beta n x ≤ Real.exp (error n x)*Γ n x)
    (hbudget : ∀ x ∈ g.root ∩ good, (∑ n ∈ Finset.range N, error n x) ≤ E)
    (hf : AEStronglyMeasurable (good.indicator (fun x =>
      T.weight K D (x,y+T.slope*x)*∏ n ∈ Finset.range N, beta n x)) volume) :
    IntegrableOn (good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ n ∈ Finset.range N, beta n x)) g.root volume ∧
    (∫ x in g.root, good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ n ∈ Finset.range N, beta n x) x) ≤
      Real.exp E*Real.exp (2*D)*∫ x in g.root, T.weight K D (x,y+T.slope*x) := by
  let f := good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
    ∏ n ∈ Finset.range N, beta n x)
  let W := fun x => T.weight K D (x,y+T.slope*x)*∏ n ∈ Finset.range N, Γ n x
  obtain ⟨hW,hWbound⟩ := g.top_weight_skipped_average T y hK hD hwidth level N hlevel
    hmono Γ hΓ hconstant haverage
  have hpoint (x : ℝ) (hx : x ∈ g.root) : 0 ≤ f x ∧ f x ≤ Real.exp E*W x := by
    have hw := (T.weight_pos (zero_lt_one.trans_le hK) D (x,y+T.slope*x)).le
    by_cases hg : x ∈ good
    · have hmem : x ∈ g.root ∩ good := ⟨hx,hg⟩
      have hp := product_le_of_error_budget (fun n : Fin N => beta n.val x)
        (fun n : Fin N => Γ n.val x) (fun n : Fin N => error n.val x) E
        (fun n => hbeta x hmem n.val n.isLt) (fun n => hΓ n.val n.isLt x)
        (fun n => hcomparison x hmem n.val n.isLt)
        (by simpa only [Finset.sum_range] using hbudget x hmem)
      have hp' : (∏ n ∈ Finset.range N, beta n x) ≤
          Real.exp E*∏ n ∈ Finset.range N, Γ n x := by
        simpa only [Finset.prod_range] using hp
      dsimp only [f,W]
      rw [Set.indicator_of_mem hg]
      refine ⟨mul_nonneg hw (Finset.prod_nonneg fun n hn =>
        hbeta x hmem n (Finset.mem_range.mp hn)),?_⟩
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hp' hw
    · simp only [f,Set.indicator_of_notMem hg]
      exact ⟨le_rfl,mul_nonneg (Real.exp_pos E).le
        (mul_nonneg hw (Finset.prod_nonneg fun n hn => hΓ n (Finset.mem_range.mp hn) x))⟩
  have hpointAE : ∀ᵐ x ∂volume.restrict g.root, 0 ≤ f x ∧ f x ≤ Real.exp E*W x := by
    filter_upwards [ae_restrict_mem (show MeasurableSet g.root from measurableSet_Ico)] with x hx
    exact hpoint x hx
  have hfi : Integrable f (volume.restrict g.root) := (hW.const_mul (Real.exp E)).mono'
    hf.restrict (hpointAE.mono fun x hx => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2)
  refine ⟨hfi,?_⟩
  calc
    _ ≤ ∫ x in g.root, Real.exp E*W x :=
      integral_mono_ae hfi (hW.const_mul _) (hpointAE.mono fun _ h => h.2)
    _ = Real.exp E*∫ x in g.root, W x := integral_const_mul _ _
    _ ≤ Real.exp E*(Real.exp (2*D)*∫ x in g.root, T.weight K D (x,y+T.slope*x)) :=
      mul_le_mul_of_nonneg_left hWbound (Real.exp_pos _).le
    _ = _ := (mul_assoc _ _ _).symm

end LipschitzHilbert

end

end OAI
