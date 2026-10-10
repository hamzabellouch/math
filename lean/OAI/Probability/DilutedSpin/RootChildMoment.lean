import OAI.Probability.DilutedSpin.RootChildSumIntegrability

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators

/-- Probability-root Jensen for the square root, proved directly from the
nonnegative centered square. It is used twice in the multileaf induction. -/
lemma integral_sqrt_le_sqrt_integral {Z : Type} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (f : Z → ℝ)
    (hf : Integrable f μ) (hs : Integrable (fun z => Real.sqrt (f z)) μ)
    (h : ∀ z, 0≤f z) : (∫ z, Real.sqrt (f z) ∂μ)≤Real.sqrt (∫ z, f z ∂μ) := by
  let t := ∫ z, Real.sqrt (f z) ∂μ
  have ht : 0≤t := integral_nonneg (fun _ => Real.sqrt_nonneg _)
  have he (z : Z) : (Real.sqrt (f z)-t)^2=f z-(2*t)*Real.sqrt (f z)+t^2 := by
    have hs := Real.sq_sqrt (h z)
    nlinarith
  have hp : 0≤∫ z, (Real.sqrt (f z)-t)^2 ∂μ := integral_nonneg (fun z => sq_nonneg _)
  simp_rw [he] at hp
  have hm : Integrable (fun z => (2*t)*Real.sqrt (f z)) μ := hs.const_mul (2*t)
  have hd : Integrable (fun z => f z-(2*t)*Real.sqrt (f z)) μ := hf.sub hm
  rw [integral_add hd (integrable_const (t^2)),
    integral_sub hf hm,integral_const_mul,integral_const] at hp
  simp only [probReal_univ,one_smul] at hp
  have hsq : t^2 ≤ ∫ z, f z ∂μ := by dsimp only [t] at *; nlinarith
  exact (Real.sqrt_sq ht).symm.le.trans (Real.sqrt_le_sqrt hsq)

namespace HeterogeneousMarks
open PrescribedTree
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {M N n L : ℕ}

lemma integrable_rootDescendantEnergy_cast (C : PrescribedTree n) (r d : ℕ)
    (h : L=n+1+r+1+d)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ] (hV : ∀ x i, |V x i|≤1) :
    Integrable (fun z : FullRootState Y X I M => descendantEnergyAt C r d
      (kernelHeightCast h (rootTower T Q m base old z)) (vectorHeightCast h (rootVector V z))) μ := by
  subst L
  exact integrable_rootDescendantEnergy C r d T Q m base old V hb μ hV

lemma integrable_sqrt_rootDescendantEnergy_cast (C : PrescribedTree n) (r d : ℕ)
    (h : L=n+1+r+1+d)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ] (hV : ∀ x i, |V x i|≤1) :
    Integrable (fun z : FullRootState Y X I M => Real.sqrt (descendantEnergyAt C r d
      (kernelHeightCast h (rootTower T Q m base old z)) (vectorHeightCast h (rootVector V z)))) μ := by
  subst L
  exact integrable_sqrt_rootDescendantEnergy C r d T Q m base old V hb μ hV

variable (k : ℕ) (C : Fin k → PrescribedTree n) (r d : ℕ) (h : L=n+1+r+1+d)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]

/-- The actual root child energies, not an independent paired-copy law. -/
noncomputable def rootChildMeanSum : ℝ :=
  (k:ℝ)*∑ j, Real.sqrt (∫ z, descendantEnergyAt (C j) r d
    (kernelHeightCast h (rootTower T Q m base old z)) (vectorHeightCast h (rootVector V z)) ∂μ)

include hb in
lemma integral_rootChildSum_le (hV : ∀ x i, |V x i|≤1) :
    (∫ z, rootChildSum k C r d h T Q m base old V z ∂μ) ≤
      rootChildMeanSum k C r d h T Q m base old V μ := by
  unfold rootChildSum rootChildMeanSum
  rw [integral_const_mul,integral_finsetSum _ (fun j _ =>
    integrable_sqrt_rootDescendantEnergy_cast (C j) r d h T Q m base old V hb μ hV)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
  apply Finset.sum_le_sum
  intro j _
  exact integral_sqrt_le_sqrt_integral μ _
    (integrable_rootDescendantEnergy_cast (C j) r d h T Q m base old V hb μ hV)
    (integrable_sqrt_rootDescendantEnergy_cast (C j) r d h T Q m base old V hb μ hV)
    (fun z => descendantEnergyAt_nonneg (C j) r d _ _)

include hb in
lemma integral_sqrt_rootChildSum_le (hV : ∀ x i, |V x i|≤1) :
    (∫ z, Real.sqrt (rootChildSum k C r d h T Q m base old V z) ∂μ) ≤
      Real.sqrt (rootChildMeanSum k C r d h T Q m base old V μ) := by
  exact (integral_sqrt_le_sqrt_integral μ _
    (integrable_rootChildSum k C r d h T Q m base old V hb μ hV)
    (integrable_sqrt_rootChildSum k C r d h T Q m base old V hb μ hV)
    (rootChildSum_nonneg k C r d h T Q m base old V)).trans
    (Real.sqrt_le_sqrt (integral_rootChildSum_le k C r d h T Q m base old V hb μ hV))

end HeterogeneousMarks
end DilutedSpinGlass
end

end

end OAI
