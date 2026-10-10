import OAI.Probability.DilutedSpin.HeightTransport
import OAI.Probability.DilutedSpin.RootShapeEnergy

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory PrescribedTree
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {M N n L : ℕ}

lemma measurable_rootDescendantEnergy_cast (C : PrescribedTree n) (r d : ℕ)
    (h : L=n+1+r+1+d)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fun z : FullRootState Y X I M => descendantEnergyAt C r d
      (kernelHeightCast h (rootTower T Q m base old z)) (vectorHeightCast h (rootVector V z))) := by
  subst L
  exact measurable_rootDescendantEnergy C r d T Q m base old V hb

variable (k : ℕ) (C : Fin k → PrescribedTree n) (r d : ℕ) (h : L=n+1+r+1+d)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

noncomputable def rootChildSum (z : FullRootState Y X I M) : ℝ :=
  (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (C j) r d
    (kernelHeightCast h (rootTower T Q m base old z)) (vectorHeightCast h (rootVector V z)))

include hb in
lemma measurable_rootChildSum : Measurable (rootChildSum k C r d h T Q m base old V) := by
  apply Measurable.const_mul
  exact Finset.measurable_sum _ (fun j _ =>
    (measurable_rootDescendantEnergy_cast (C j) r d h T Q m base old V hb).sqrt)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootChildSum_nonneg (z : FullRootState Y X I M) :
    0 ≤ rootChildSum k C r d h T Q m base old V z := by
  unfold rootChildSum
  positivity

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootChildSum_bound (hV : ∀ x i, |V x i|≤1) (z : FullRootState Y X I M) :
    rootChildSum k C r d h T Q m base old V z ≤ 2*(k:ℝ)^2 := by
  have he (j : Fin k) : Real.sqrt (descendantEnergyAt (C j) r d
      (kernelHeightCast h (rootTower T Q m base old z)) (vectorHeightCast h (rootVector V z))) ≤ 2 := by
    have hb := Real.sqrt_le_sqrt (descendantEnergyAt_le_four (C j) r d
      (kernelHeightCast h (rootTower T Q m base old z)) (vectorHeightCast h (rootVector V z))
       (fun _ index => hV _ index))
    norm_num at hb
    exact hb
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k))) (fun j _ => he j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  unfold rootChildSum
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) k)
  nlinarith

include hb in
lemma integrable_rootChildSum (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ x i, |V x i|≤1) : Integrable (rootChildSum k C r d h T Q m base old V) μ := by
  apply Integrable.of_bound (measurable_rootChildSum k C r d h T Q m base old V hb).aestronglyMeasurable
    (2*(k:ℝ)^2)
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (rootChildSum_nonneg k C r d h T Q m base old V z)]
  exact rootChildSum_bound k C r d h T Q m base old V hV z

include hb in
lemma integrable_sqrt_rootChildSum (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ x i, |V x i|≤1) : Integrable (fun z => Real.sqrt (rootChildSum k C r d h T Q m base old V z)) μ := by
  apply Integrable.of_bound (measurable_rootChildSum k C r d h T Q m base old V hb).sqrt.aestronglyMeasurable
    (Real.sqrt (2*(k:ℝ)^2))
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (rootChildSum_bound k C r d h T Q m base old V hV z)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
