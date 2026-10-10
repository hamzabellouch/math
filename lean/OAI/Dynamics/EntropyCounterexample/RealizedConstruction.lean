import OAI.Dynamics.EntropyCounterexample.MapData
import OAI.Dynamics.EntropyCounterexample.ClockModel
import OAI.Dynamics.EntropyCounterexample.SphereCharts
import OAI.Dynamics.EntropyCounterexample.ModelTransport

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

def modelHomeomorph : RawManifold ≃ₜ CounterexampleManifold 3 :=
  ClockModel.productHomeomorph 3 complexSphereHomeomorph

def realizedMap (L : ℝ) (hL : 2 < L) :
    CounterexampleManifold 3 → CounterexampleManifold 3 :=
  conjugateMap modelHomeomorph (concreteMap L hL)

@[simp] theorem modelHomeomorph_clock (x : RawManifold) :
    (modelHomeomorph x).1 = ClockModel.clockHomeomorph x.1 := rfl

@[simp] theorem modelHomeomorph_main (x : RawManifold) :
    (modelHomeomorph x).2 0 = complexSphereHomeomorph x.2.1 := rfl

@[simp] theorem modelHomeomorph_register (x : RawManifold) (i : Fin 3) :
    (modelHomeomorph x).2 i.succ = complexSphereHomeomorph (x.2.2 i) := rfl

@[simp] theorem realizedMap_modelHomeomorph (L : ℝ) (hL : 2 < L) (x : RawManifold) :
    realizedMap L hL (modelHomeomorph x) = modelHomeomorph (concreteMap L hL x) :=
  conjugateMap_apply _ _ _

theorem realizedMap_semiconj (L : ℝ) (hL : 2 < L) :
    Function.Semiconj modelHomeomorph (concreteMap L hL) (realizedMap L hL) :=
  fun x => (realizedMap_modelHomeomorph L hL x).symm

theorem realizedMap_iterate (L : ℝ) (hL : 2 < L) (n : ℕ) (x : RawManifold) :
    (realizedMap L hL)^[n] (modelHomeomorph x) =
      modelHomeomorph ((concreteMap L hL)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      realizedMap_modelHomeomorph]

theorem realizedMap_not_bijective (L : ℝ) (hL : 2 < L) :
    ¬ Function.Bijective (realizedMap L hL) := by
  simpa only [realizedMap, bijective_conjugateMap_iff] using concreteMap_not_bijective L hL

theorem continuous_realizedMap (L : ℝ) (hL : 2 < L)
    (hf : Continuous (concreteMap L hL)) : Continuous (realizedMap L hL) :=
  continuous_conjugateMap modelHomeomorph hf

def modelEmbedding : RawManifold → CounterexampleAmbient 3 :=
  standardEmbedding 3 ∘ modelHomeomorph

private theorem localExtension_modelEmbedding :
    HasLocalC1Extension modelEmbedding (standardEmbedding 3 ∘ modelHomeomorph) := by
  apply HasLocalC1Extension.of_contDiffOn isOpen_univ (fun _ => Set.mem_univ _)
    id contDiff_id.contDiffOn
  intro x
  rfl

private theorem localExtension_modelEmbedding_inverse :
    HasLocalC1Extension (standardEmbedding 3) (modelEmbedding ∘ modelHomeomorph.symm) := by
  apply HasLocalC1Extension.of_contDiffOn isOpen_univ (fun _ => Set.mem_univ _)
    id contDiff_id.contDiffOn
  intro x
  simp [modelEmbedding]

theorem isC1SelfMap_realizedMap (L : ℝ) (hL : 2 < L)
    (hf : HasLocalC1Extension modelEmbedding (modelEmbedding ∘ concreteMap L hL)) :
    IsC1SelfMap 3 (realizedMap L hL) :=
  isC1SelfMap_conjugateMap_of_embeddings modelHomeomorph
    localExtension_modelEmbedding localExtension_modelEmbedding_inverse hf

theorem isC1SelfMap_realizedMap_iff (L : ℝ) (hL : 2 < L) :
    IsC1SelfMap 3 (realizedMap L hL) ↔
      HasLocalC1Extension modelEmbedding (modelEmbedding ∘ concreteMap L hL) := by
  constructor
  · intro hf x
    obtain ⟨U, hU, hxU, F, hF, heq⟩ := hf.2 (modelHomeomorph x)
    refine ⟨U, hU, hxU, F, hF, ?_⟩
    intro y hy
    simpa only [modelEmbedding, Function.comp_apply, realizedMap_modelHomeomorph] using
      heq (modelHomeomorph y) hy
  · exact isC1SelfMap_realizedMap L hL

@[implicit_reducible]
def modelUniformSpace : UniformSpace RawManifold := uniformSpaceOfCompactR1

section Entropy

local instance : UniformSpace RawManifold := modelUniformSpace

def concreteEntropy (L : ℝ) (hL : 2 < L) : EReal :=
  Dynamics.coverEntropy (concreteMap L hL) Set.univ

theorem coverEntropy_realizedMap (L : ℝ) (hL : 2 < L) :
    Dynamics.coverEntropy (realizedMap L hL) Set.univ = concreteEntropy L hL :=
  coverEntropy_conjugateMap modelHomeomorph (concreteMap L hL)

end Entropy

theorem realizedMap_eigenvector (L : ℝ) (hL : 2 < L)
    (hf : Continuous (concreteMap L hL)) (n : ℕ) (c : ℝ)
    (v : RealSingularHomology n RawManifold) (hv : v ≠ 0)
    (heig : realHomologyMap n (concreteMap L hL) hf v = c • v) :
    ∃ w : RealSingularHomology n (CounterexampleManifold 3), w ≠ 0 ∧
      realHomologyMap n (realizedMap L hL) (continuous_realizedMap L hL hf) w = c • w :=
  realHomologyMap_eigenvector_conjugateMap n modelHomeomorph hf c v hv heig

theorem totalRealHomologySpectralRadius_realizedMap (L : ℝ) (hL : 2 < L)
    (hf : Continuous (concreteMap L hL)) :
    totalRealHomologySpectralRadius (realizedMap L hL) (continuous_realizedMap L hL hf) =
      totalRealHomologySpectralRadius (concreteMap L hL) hf :=
  totalRealHomologySpectralRadius_conjugateMap modelHomeomorph hf

end Problem340.Construction

end

end OAI
