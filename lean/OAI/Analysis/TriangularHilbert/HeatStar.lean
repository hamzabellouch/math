import OAI.Analysis.TriangularHilbert.GroupedGaussian

namespace OAI

universe uι

section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def heatWeights (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) : Three → ι → ℝ :=
  fun v i => weight h (u i) (p v) (σ v)

def heatArray (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) :=
  weightedArray A (heatWeights h u p σ)

def heatEnergy (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v : Three) : ℝ :=
  energy (starGram (heatArray A h u p σ) v)

def fixedBase (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v w : Three) :=
  if w = v then rowBare A g v else colBare A g v

def localGram (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) :=
  weightedGram (fixedBase A (heatWeights h u p σ) v w)
    (groupWeight h (fun a : BlockSpace ι => u a.2) Prod.fst p σ)

def localFirst (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) :=
  weightedGram (fixedBase A (heatWeights h u p σ) v w)
    (groupFirst h (fun a : BlockSpace ι => u a.2) Prod.fst p σ w)

def localSecond (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) :=
  weightedGram (fixedBase A (heatWeights h u p σ) v w)
    (groupSecond h (fun a : BlockSpace ι => u a.2) Prod.fst p σ w)

def heatFirst (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) : ℝ :=
  energyGradient (localGram A h u p σ v w) (localFirst A h u p σ v w)

def heatPure (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) : ℝ :=
  hessianCost (localGram A h u p σ v w) (localFirst A h u p σ v w) +
    energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)

def heatVariance (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) : ℝ :=
  (1/2 : ℝ) * energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)

lemma heatEnergy_eq_localGram (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    heatEnergy A h u p σ v = energy (localGram A h u p σ v w) := by
  have hg : ∀ w i, 0 ≤ heatWeights h u p σ w i := fun w i =>
    (weight_pos hh (hσ w) (u i) (p w)).le
  unfold heatEnergy localGram fixedBase
  split_ifs
  · rw [heatArray, starGram_weightedArray A _ hg]
    rfl
  · rw [starGram, energy_gram_flip, heatArray, centerGram_weightedArray_padded A _ hg]
    rfl

lemma fixedBase_update_center (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w : Three) (q : ℝ) :
    fixedBase A (heatWeights h u (Function.update p w q) σ) v w =
      fixedBase A (heatWeights h u p σ) v w := by
  unfold fixedBase
  split_ifs with hw
  · subst w
    apply rowBare_congr
    intro w hw i
    simp only [heatWeights, Function.update_of_ne hw]
  · apply colBare_congr
    intro i
    simp only [heatWeights, Function.update_of_ne (Ne.symm hw)]

lemma fixedBase_update_variance (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w : Three) (q : ℝ) :
    fixedBase A (heatWeights h u p (Function.update σ w q)) v w =
      fixedBase A (heatWeights h u p σ) v w := by
  unfold fixedBase
  split_ifs with hw
  · subst w
    apply rowBare_congr
    intro w hw i
    simp only [heatWeights, Function.update_of_ne hw]
  · apply colBare_congr
    intro i
    simp only [heatWeights, Function.update_of_ne (Ne.symm hw)]

lemma heatEnergy_hasDerivAt_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    HasDerivAt (fun q => heatEnergy A h u (Function.update p w q) σ v)
      (heatFirst A h u p σ v w) (p w) := by
  have hd := groupEnergy_hasDerivAt_center (fixedBase A (heatWeights h u p σ) v w)
    hh (fun a : BlockSpace ι => u a.2) Prod.fst p hσ w
  apply hd.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro q
  dsimp only
  rw [heatEnergy_eq_localGram A hh u _ hσ v w]
  unfold localGram
  rw [fixedBase_update_center]

lemma heatFirst_hasDerivAt_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    HasDerivAt (fun q => heatFirst A h u (Function.update p w q) σ v w)
      (heatPure A h u p σ v w) (p w) := by
  have hd := groupEnergyFirst_hasDerivAt_center (fixedBase A (heatWeights h u p σ) v w)
    hh (fun a : BlockSpace ι => u a.2) Prod.fst p hσ w
  apply hd.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro q
  dsimp only
  unfold heatFirst localGram localFirst
  rw [fixedBase_update_center]

lemma heatEnergy_hasDerivAt_variance (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    HasDerivAt (fun q => heatEnergy A h u p (Function.update σ w q) v)
      (heatVariance A h u p σ v w) (σ w) := by
  have hd := groupEnergy_hasDerivAt_variance (fixedBase A (heatWeights h u p σ) v w)
    hh (fun a : BlockSpace ι => u a.2) Prod.fst p hσ w
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (hσ w)] with q hq
  have hσ' : ∀ a, 0 < Function.update σ w q a := by
    intro a
    by_cases ha : a = w
    · simpa [ha] using hq
    · simpa [ha] using hσ a
  rw [heatEnergy_eq_localGram A hh u _ hσ' v w]
  unfold localGram
  rw [fixedBase_update_variance]

end
end TriangularHilbert.Heat
end

end OAI
