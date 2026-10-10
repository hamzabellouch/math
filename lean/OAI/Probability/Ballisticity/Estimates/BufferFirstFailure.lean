import Mathlib
import OAI.Probability.Ballisticity.Estimates.RawPairLocality

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def BelowHeight {d : ℕ} (ℓ : Vector d) (a : ℝ) : Set (Lattice d) :=
  {y | dot (realPosition y) ℓ < a}

def PairAtHeight {d : ℕ} (ℓ : Vector d) (a : ℝ) : Set (Lattice d × Lattice d) :=
  {x | dot (realPosition x.1) ℓ = a ∧ dot (realPosition x.2) ℓ = a}

noncomputable def rowHeightFiltration {d : ℕ} (ℓ : Vector d) (a : ℝ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Environment d)) where
  seq n := rowSigma (BelowHeight ℓ (a+n))
  mono' := by
    intro n m hnm
    apply rowSigma_mono
    intro y hy
    have hnmR : (n:ℝ) ≤ m := by exact_mod_cast hnm
    dsimp [BelowHeight] at hy ⊢
    linarith
  le' n := rowSigma_le _

noncomputable def bufferTraversalMass {d : ℕ} (ℓ : Vector d) (f : Direction d) (a z : ℝ)
    (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a)) (h : ℕ) (ω : Environment d) : ℝ≥0∞ :=
  if h=0 then 1 else pairKernelMass ℓ f h z (π ω).val ω

lemma bufferTraversalMass_adapted {d : ℕ} (ℓ : Vector d) (f : Direction d) (a z : ℝ)
    (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight ℓ a)) _ π) :
    Adapted (rowHeightFiltration ℓ a) (bufferTraversalMass ℓ f a z π) := by
  intro h
  by_cases hh : h=0
  · simp only [hh]
    exact measurable_const
  · have hhpos : 0 < h := Nat.pos_of_ne_zero hh
    have hle : rowSigma (BelowHeight ℓ a) ≤ rowSigma (BelowHeight ℓ (a+h)) := by
      apply rowSigma_mono
      intro y hy
      dsimp [BelowHeight] at hy ⊢
      have : (0:ℝ) ≤ h := Nat.cast_nonneg h
      linarith
    have hC (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight ℓ a) :
        Strip ℓ x.1 h ⊆ BelowHeight ℓ (a+h) ∧ Strip ℓ x.2 h ⊆ BelowHeight ℓ (a+h) := by
      constructor
      · intro y hy
        change dot (realPosition y) ℓ < a+h
        simpa only [hx.1] using hy.2
      · intro y hy
        change dot (realPosition y) ℓ < a+h
        simpa only [hx.2] using hy.2
    have hp : @Measurable _ _ (rowSigma (BelowHeight ℓ (a+h))) _ π := hπ.mono hle le_rfl
    have hm := (pairKernelMass_joint_rows ℓ f hhpos z (PairAtHeight ℓ a)
      (BelowHeight ℓ (a+h)) hC).comp (hp.prodMk measurable_id)
    change @Measurable _ _ (rowSigma (BelowHeight ℓ (a+h))) _ _
    unfold bufferTraversalMass
    simp only [ite_eq_right hh]
    exact hm

noncomputable def bufferFirstFailure {d : ℕ} (ℓ : Vector d) (f : Direction d) (a z g : ℝ)
    (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a)) (H : ℕ) : Environment d → ℕ :=
  hittingBtwn (bufferTraversalMass ℓ f a z π) (Set.Iio (ENNReal.ofReal g)) 1 H

lemma bufferFirstFailure_stopping {d : ℕ} (ℓ : Vector d) (f : Direction d) (a z g : ℝ)
    (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight ℓ a)) _ π) (H : ℕ) :
    IsStoppingTime (rowHeightFiltration ℓ a) (fun ω => (bufferFirstFailure ℓ f a z g π H ω : WithTop ℕ)) :=
  (bufferTraversalMass_adapted ℓ f a z π hπ).isStoppingTime_hittingBtwn measurableSet_Iio

lemma bufferFirstFailure_bounds {d : ℕ} (ℓ : Vector d) (f : Direction d) (a z g : ℝ)
    (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a)) {H : ℕ} (hH : 0 < H)
    (ω : Environment d) : 1 ≤ bufferFirstFailure ℓ f a z g π H ω ∧
      bufferFirstFailure ℓ f a z g π H ω ≤ H :=
  hittingBtwn_mem_Icc hH ω

lemma before_bufferFirstFailure_pass {d : ℕ} (ℓ : Vector d) (f : Direction d) (a z g : ℝ)
    (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a)) (H : ℕ)
    (ω : Environment d) {j : ℕ} (hj : 0 < j) (hjlt : j < bufferFirstFailure ℓ f a z g π H ω) :
    ENNReal.ofReal g ≤ pairKernelMass ℓ f j z (π ω).val ω := by
  have hn := notMem_of_lt_hittingBtwn hjlt hj
  simpa only [bufferTraversalMass,ite_eq_right (Nat.ne_of_gt hj),Set.mem_Iio,not_lt] using hn

lemma bufferFirstFailure_fails_of_lt {d : ℕ} (ℓ : Vector d) (f : Direction d) (a z g : ℝ)
    (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a)) {H : ℕ} (hH : 0 < H)
    (ω : Environment d) (hlt : bufferFirstFailure ℓ f a z g π H ω < H) :
    pairKernelMass ℓ f (bufferFirstFailure ℓ f a z g π H ω) z (π ω).val ω < ENNReal.ofReal g := by
  have hn := hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  change bufferTraversalMass ℓ f a z π (bufferFirstFailure ℓ f a z g π H ω) ω < ENNReal.ofReal g at hn
  have hp := (bufferFirstFailure_bounds ℓ f a z g π hH ω).1
  simpa only [bufferTraversalMass,ite_eq_right (by omega : bufferFirstFailure ℓ f a z g π H ω ≠ 0),Set.mem_Iio] using hn
end DirectionalTransience

end

end

end OAI
