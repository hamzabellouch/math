import OAI.Geometry.PinnedDistances.NormalizedGraphs

namespace OAI

universe u1 u2 u3 u4

section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace WeakPinned.Bounded
open Hierarchy Global Variance NumberField

lemma bounded_denominator_rate (x w : ℕ → ℝ) (C : ℝ)
    (hx : ∀ n,0≤x n) (hw : ∀ n,0≤w n) (hC : ∀ n,w n≤C)
    (ht : Tendsto (fun n => x n/(w n+1)) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) := by
  apply squeeze_zero hx _ (by simpa only [mul_zero] using tendsto_const_nhds.mul ht (a:=C+1))
  intro n
  have hp : 0<w n+1 := by linarith [hw n]
  calc
    x n = (w n+1)*(x n/(w n+1)) := by field_simp
    _ ≤ (C+1)*(x n/(w n+1)) :=
      mul_le_mul_of_nonneg_right (by linarith [hC n]) (div_nonneg (hx n) hp.le)

variable {P : Type u1} [Fintype P] [DecidableEq P]
variable {K : Type u2} [Field K] [NumberField K]

lemma massEval_add (q r : Finset P → ℝ) (d d' : Depth P) :
    massEval (fun C => q C+r C) d d'=massEval q d d'+massEval r d d' := by
  simp only [massEval,weightedIntegral,mul_add,Finset.sum_add_distrib]
  ring

omit [NumberField K] in
lemma archMean_mass_add (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
    (hn : 2≤Fintype.card P) (q r : Finset P → ℝ) (v : InfinitePlace K) :
    archMean Z₁ Z₂ (massEval (fun C => q C+r C)) v=
      archMean Z₁ Z₂ (massEval q) v+archMean Z₁ Z₂ (massEval r) v := by
  unfold archMean
  simp only [massEval_add]
  exact integral_add (integrable_massEval Z₁ Z₂ h₁ h₂ hn q v)
    (integrable_massEval Z₁ Z₂ h₁ h₂ hn r v)

omit [NumberField K] in
lemma archMean_mass_swap (Z₁ Z₂ : P → K) (q : Finset P → ℝ) (v : InfinitePlace K) :
    archMean Z₂ Z₁ (massEval q) v=archMean Z₁ Z₂ (massEval q) v := by
  unfold archMean
  congr 1
  funext ω
  exact add_comm _ _

omit [NumberField K] in
lemma archMean_scale_swap (Z₁ Z₂ : P → K) (v : InfinitePlace K) :
    archMean Z₂ Z₁ scaleEval v=archMean Z₁ Z₂ scaleEval v := by
  unfold archMean
  congr 1
  funext ω
  simp only [scaleEval,massEval,potentialEval]
  congr 1
  · exact add_comm _ _
  · apply Finset.sum_congr rfl
    intro x _
    rw [add_comm ((arch Z₂ v ω).potential x)]

omit [DecidableEq P] in
lemma weightedIntegral_add (m q r : Finset P → ℝ) :
    weightedIntegral m (fun C => q C+r C)=weightedIntegral m q+weightedIntegral m r := by
  simp only [weightedIntegral,mul_add,Finset.sum_add_distrib]

variable {V : ℕ → Type u3} {L : ℕ → Type u4} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)]
  [∀ n,Field (L n)] [∀ n,NumberField (L n)]

lemma bounded_place_selection (Z₁ Z₂ : ∀ n,V n → L n)
    (h₁ : ∀ n,Function.Injective (Z₁ n)) (h₂ : ∀ n,Function.Injective (Z₂ n))
    (hn : ∀ n,2≤Fintype.card (V n)) (q r : ∀ n,Finset (V n) → ℝ)
    (hq : ∀ n C,0≤q n C) (hr : ∀ n C,0≤r n C)
    (C : ℝ) (hC : 0≤C)
    (hscale : ∀ n,overlapScale (Z₁ n) (Z₂ n) (h₁ n) (h₂ n)+
      potentialScale (Z₁ n) (Z₂ n) (h₁ n) (h₂ n)≤C)
    (hqt : Tendsto (fun n => weightedIntegral (totalMass (Z₁ n) (Z₂ n) (h₁ n) (h₂ n)) (q n)) atTop (𝓝 0))
    (hrt : Tendsto (fun n => weightedIntegral (totalMass (Z₁ n) (Z₂ n) (h₁ n) (h₂ n)) (r n)) atTop (𝓝 0)) :
    ∃ v : ∀ n,InfinitePlace (L n),
      (∀ n,archMean (Z₁ n) (Z₂ n) scaleEval (v n)≤2*C+1) ∧
      Tendsto (fun n => archMean (Z₁ n) (Z₂ n) (massEval (q n)) (v n)) atTop (𝓝 0) ∧
      Tendsto (fun n => archMean (Z₁ n) (Z₂ n) (massEval (r n)) (v n)) atTop (𝓝 0) := by
  let m := fun n => totalMass (Z₁ n) (Z₂ n) (h₁ n) (h₂ n)
  let ε := fun n => weightedIntegral (m n) (q n)+weightedIntegral (m n) (r n)+1/((n:ℝ)+1)
  have hq0 (n) : 0≤weightedIntegral (m n) (q n) :=
    Finset.sum_nonneg (fun D _ => mul_nonneg (totalMass_nonneg _ _ _ _ _) (hq n D))
  have hr0 (n) : 0≤weightedIntegral (m n) (r n) :=
    Finset.sum_nonneg (fun D _ => mul_nonneg (totalMass_nonneg _ _ _ _ _) (hr n D))
  have he (n) : 0<ε n := by
    have hh : 0<1/((n:ℝ)+1) := by positivity
    dsimp only [ε]
    linarith [hq0 n,hr0 n]
  have het : Tendsto ε atTop (𝓝 0) := by
    have hi : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := by
      simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    simpa only [add_zero] using (hqt.add hrt).add hi
  have hs (n) := select_arch (Z₁ n) (Z₂ n) (h₁ n) (h₂ n) (hn n)
    (fun D => q n D+r n D) (fun D => add_nonneg (hq n D) (hr n D)) C (ε n) hC (he n) (hscale n)
    (by rw [weightedIntegral_add]; dsimp [ε,m]; linarith [show 0≤1/((n:ℝ)+1) by positivity])
  choose v hvscale hv using hs
  have hvq (n) : 0≤archMean (Z₁ n) (Z₂ n) (massEval (q n)) (v n) :=
    archMean_nonneg _ _ _ (massEval_nonneg _ (hq n)) _
  have hvr (n) : 0≤archMean (Z₁ n) (Z₂ n) (massEval (r n)) (v n) :=
    archMean_nonneg _ _ _ (massEval_nonneg _ (hr n)) _
  have hsum (n) := hv n
  simp only [archMean_mass_add _ _ (h₁ _) (h₂ _) (hn _)] at hsum
  refine ⟨v,hvscale,?_,?_⟩
  · apply squeeze_zero hvq _ (by simpa only [mul_zero] using het.const_mul 2)
    intro n
    linarith [hsum n,hvr n]
  · apply squeeze_zero hvr _ (by simpa only [mul_zero] using het.const_mul 2)
    intro n
    linarith [hsum n,hvq n]

lemma power_fraction_rate (n : ℕ → ℝ) (hn : ∀ j,0<n j)
    (ht : Tendsto n atTop atTop) (c : ℝ) (hc : 0<c) :
    Tendsto (fun j => (n j)^(1-c)/n j) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop hc).comp ht
  convert hh using 1
  funext j
  rw [show 1-c=1+(-c) by ring,Real.rpow_add (hn j),Real.rpow_one]
  simp only [Function.comp_apply]
  exact mul_div_cancel_left₀ _ (hn j).ne'

end WeakPinned.Bounded

end
end

end OAI
