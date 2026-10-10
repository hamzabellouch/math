import OAI.Probability.GaussianReplacement.Comparison

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory





def blockInput {d m : ℕ} {U : Type*} (z : (Sphere d × U) × Rows m d) :
    U × (Rows m d × (Fin m → ℝ)) :=
  (z.1.2, z.2, label z.2 (z.1.1 : Vector d))

lemma measurable_blockInput {d m : ℕ} {U : Type*} [MeasurableSpace U] :
    Measurable (blockInput (d:=d) (m:=m) (U:=U)) := by
  exact measurable_fst.snd.prodMk (measurable_snd.prodMk
    ((measurable_own_label (d:=d) (k:=m)).comp
      (measurable_snd.prodMk measurable_fst.fst)))

def blockLaw {d m : ℕ} {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d × U))
    (κ : Kernel (U × (Rows m d × (Fin m → ℝ))) V) :
    Measure (((Sphere d × U) × Rows m d) × V) :=
  (P.prod (gaussianRows m d)) ⊗ₘ κ.comap blockInput measurable_blockInput

instance blockLaw_probability {d m : ℕ} {U V : Type*}
    [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d × U)) [IsProbabilityMeasure P]
    (κ : Kernel (U × (Rows m d × (Fin m → ℝ))) V) [IsMarkovKernel κ] :
    IsProbabilityMeasure (blockLaw P κ) := by
  unfold blockLaw
  infer_instance

def endingSignalLaw {d m : ℕ} {U V : Type*}
    [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d × U))
    (κ : Kernel (U × (Rows m d × (Fin m → ℝ))) V) : Measure (Sphere d × V) :=
  (blockLaw P κ).map (fun z => (z.1.1.1, z.2))

instance endingSignalLaw_probability {d m : ℕ} {U V : Type*}
    [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d × U)) [IsProbabilityMeasure P]
    (κ : Kernel (U × (Rows m d × (Fin m → ℝ))) V) [IsMarkovKernel κ] :
    IsProbabilityMeasure (endingSignalLaw P κ) := by
  unfold endingSignalLaw
  infer_instance

def freshInformation {d : ℕ} {U : Type*} [MeasurableSpace U] [StandardBorelSpace U]
    (P : Measure (Sphere d × U)) [IsFiniteMeasure P] (k : ℕ) : ℝ≥0∞ :=
  exposedInformation (P.prod (gaussianRows k d))

def hybridFirst (d : ℕ) : ℕ := (d+3)/4

def hybridLast (d : ℕ) : ℕ := d/2

def hybridCount (d : ℕ) : ℕ := hybridLast d - hybridFirst d + 1

def averagedFreshInformation {d : ℕ} {U : Type*}
    [MeasurableSpace U] [StandardBorelSpace U]
    (P : Measure (Sphere d × U)) [IsFiniteMeasure P] : ℝ :=
  (∑ k ∈ Finset.Icc (hybridFirst d) (hybridLast d), (freshInformation P k).toReal) /
    hybridCount d


def HybridBlockMain : Prop :=
  ∃ (C C' : ℝ) (d₀ : ℕ), 0 < C ∧ 0 < C' ∧ ∀ d, d₀ ≤ d →
    ∀ m, 1 ≤ m → m ≤ d/8 →
    ∀ (U V : Type) [Fintype U] [Fintype V]
      [MeasurableSpace U] [MeasurableSpace V]
      [MeasurableSingletonClass U] [MeasurableSingletonClass V],
    ∀ (P : Measure (Sphere d × U)) [IsProbabilityMeasure P],
    P.fst = uniformSphere d →
    ∀ (κ : Kernel (U × (Rows m d × (Fin m → ℝ))) V) [IsMarkovKernel κ],
    ∀ (B : ℝ), 0 ≤ B →
    shannonEntropy (endingSignalLaw P κ).snd ≤ ENNReal.ofReal B →
    averagedFreshInformation (endingSignalLaw P κ) - averagedFreshInformation P ≤
      C*m + (m:ℝ) / hybridCount d * (C + B / (d/8:ℕ)) + B / (d/32:ℕ) ∧
    (B ≤ (d:ℝ)^2 →
      averagedFreshInformation (endingSignalLaw P κ) - averagedFreshInformation P ≤ C'*d)

def FiberBlockMain : Prop :=
  ∃ (K : ℝ) (d₀ : ℕ), 0 < K ∧ ∀ d, d₀ ≤ d →
    ∀ (U V : Type) [Fintype U] [Fintype V]
      [MeasurableSpace U] [MeasurableSpace V]
      [MeasurableSingletonClass U] [MeasurableSingletonClass V],
    ∀ (P : Measure (Sphere d×U)) [IsProbabilityMeasure P],
    P.fst = uniformSphere d →
    ∀ (κ : Kernel (U×(Rows (d/10) d×(Fin (d/10)→ℝ))) V) [IsMarkovKernel κ],
    ∀ N : ℕ, 1 ≤ N → Fintype.card V ≤ N → Real.log N ≤ (d:ℝ)^2 →
    freshInformation (endingSignalLaw P κ) (d/3) ≤ freshInformation P (d/3) + ENNReal.ofReal (K*d)




end CurrentProjection

end

end OAI
