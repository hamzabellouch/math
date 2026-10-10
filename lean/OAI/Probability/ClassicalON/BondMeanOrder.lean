import OAI.Probability.ClassicalON.SpinCorrelation

namespace OAI

universe uE uK uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} {K : Type uK} [Fintype V] [Fintype E] [Fintype K]

theorem freeBondMean_nonneg (l r : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    {f : (E → Bool) → ℝ} (hf : ∀ η,0≤f η) : 0≤freeBondMean l r b f := by
  rw [freeBondMean_eq_jointBondMean _ _ _ hb]
  exact jointBondMean_nonneg _ _ _ _ hb (fun _ η => hf η)

theorem freeBondMean_mono (l r : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    {f g : (E → Bool) → ℝ} (hfg : ∀ η,f η≤g η) : freeBondMean l r b f≤freeBondMean l r b g := by
  rw [freeBondMean_eq_jointBondMean _ _ _ hb,freeBondMean_eq_jointBondMean _ _ _ hb]
  exact jointBondMean_mono _ _ _ _ hb (fun _ => continuous_const) (fun _ => continuous_const) (fun _ η => hfg η)

theorem freeBondMean_sum (l r : E → V) (b : E → ℝ) (f : K → (E → Bool) → ℝ) :
    freeBondMean l r b (fun η => ∑ k,f k η)=∑ k,freeBondMean l r b (f k) := by
  unfold freeBondMean freeSpinMean weightedMean
  simp_rw [Finset.mul_sum]
  rw [show (fun s : V → Spin 3 => ∑ η,∑ k,Real.exp (freeSpinEnergy 3 l r b s)*
      (spinBondWeight l r b s η*f k η))=
    (fun s => ∑ k,∑ η,Real.exp (freeSpinEnergy 3 l r b s)*(spinBondWeight l r b s η*f k η)) by
      funext s; rw [Finset.sum_comm]]
  rw [integral_finsetSum,Finset.sum_div]
  intro k _
  exact compact_integrable (continuous_finsetSum _ (fun η _ =>
    (continuous_freeSpinEnergy _ _ _ _).rexp.mul ((continuous_spinBondWeight _ _ _ _).mul continuous_const)))

theorem freeBondMean_one (l r : E → V) (b : E → ℝ) : freeBondMean l r b (fun _ => 1)=1 := by
  unfold freeBondMean freeSpinMean weightedMean
  simp only [mul_one,spinBondWeight_sum]
  exact div_self (ne_of_gt (compact_integral_pos (continuous_freeSpinEnergy 3 l r b).rexp (fun _ => Real.exp_pos _)))

omit [Fintype K] in
theorem blockBondMean_one (l r : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (k : K) : blockBondMean l r b B label elabel k (fun _ => 1)=1 := by
  have hs (s : BlockVertex B label k → Spin 3) :
      (∑ η,blockBondWeight l r b B label elabel k s η)=1 := by
    convert spinBondWeight_sum (fun e : {e // elabel e=k} => l e.val) (fun e => r e.val)
      (fun e => b e.val) (blockSpin B label k s) using 1; congr!
  unfold blockBondMean weightedMean
  simp only [mul_one,hs]
  apply div_self
  apply ne_of_gt
  exact compact_integral_pos
    ((continuous_freeSpinEnergy _ _ _ _).comp (continuous_blockSpin B label k)).rexp
      (fun _ => Real.exp_pos _)

omit [Fintype K] in
theorem blockBondMean_nonneg (l r : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (B : Set V) (label : V → K) (elabel : E → K) (k : K)
    {f : ({e // elabel e=k} → Bool) → ℝ} (hf : ∀ η,0≤f η) :
    0≤blockBondMean l r b B label elabel k f := by
  apply weightedMean_nonneg
    ((continuous_freeSpinEnergy _ _ _ _).comp (continuous_blockSpin B label k)).rexp
    (fun _ => Real.exp_pos _)
  intro s
  exact Finset.sum_nonneg (fun η _ => mul_nonneg (spinBondWeight_nonneg (fun e : {e // elabel e=k} => l e.val)
    (fun e => r e.val) (fun e => b e.val) (fun e => hb e.val) _ _) (hf η))

end ClassicalON

end

end OAI
