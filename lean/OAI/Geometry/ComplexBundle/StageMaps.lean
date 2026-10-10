import OAI.Geometry.ComplexBundle.LineStage

namespace OAI

noncomputable section

/-! Continuous stage maps and trivial input stages. -/

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} {K : ι → ℕ}

/-- A sum consisting entirely of trivial projective-product lines has a
global chart, for the existing bundle topology. -/
def lineStageTrivialTotalHomeomorph (a : LineStage K)
    (h : ∀ s, a.label s=none) (y₀ : ProjectiveProduct K) :
    TotalSpace a.Model a.Fiber ≃ₜ ProjectiveProduct K × a.Model := by
  let C := smoothLineSumCore K a.label
  let chart := C.indexAt y₀
  have hb : (C.localTriv chart).baseSet = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      change ∀ s, y ∈ (productLineCore K (a.label s)).baseSet (chart s)
      intro s
      have hz (l : Option ι) (hl : l=none) (c : productLineChartIndex K l) :
          y ∈ (productLineCore K l).baseSet c := by
        subst l
        exact Set.mem_univ _
      exact hz (a.label s) (h s) (chart s)

  exact (C.localTriv chart).toOpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv
    (by rw [(C.localTriv chart).source_eq,hb]; simp)
    (by rw [(C.localTriv chart).target_eq,hb]; simp)

@[simp] theorem lineStageTrivialTotalHomeomorph_apply (a : LineStage K)
    (h : ∀ s, a.label s=none) (y₀ : ProjectiveProduct K)
    (z : TotalSpace a.Model a.Fiber) :
    lineStageTrivialTotalHomeomorph a h y₀ z = (z.proj,(show a.Model from z.2)) := by
  apply Prod.ext
  · rfl
  · ext s
    change (productLineCore K (a.label s)).coordChange _ _ z.proj
      ((show a.Model from z.2) s) = _
    have hz (l : Option ι) (hl : l=none) (c e : productLineChartIndex K l) (v : ℂ) :
        (productLineCore K l).coordChange c e z.proj v=v := by
      subst l
      rfl
    exact hz (a.label s) (h s) _ _ _

/-- Constant model vectors are genuine continuous sections of this trivial
bundle in its original topology. -/
theorem lineStageTrivial_section (a : LineStage K) (h : ∀ s, a.label s=none)
    (y₀ : ProjectiveProduct K) (v : a.Model) :
    Continuous (fun y => TotalSpace.mk' a.Model y (show a.Fiber y from v)) := by
  let e := lineStageTrivialTotalHomeomorph a h y₀
  have he : (fun y => TotalSpace.mk' a.Model y (show a.Fiber y from v)) =
      e.symm ∘ (fun y => (y,v)) := by
    funext y
    apply e.injective
    exact (lineStageTrivialTotalHomeomorph_apply a h y₀ _).trans (e.apply_symm_apply (y,v)).symm
  rw [he]
  exact e.symm.continuous.comp (continuous_id.prodMk continuous_const)

end Kaplansky

end

open Bundle Topology
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} [Fintype ι] {K : ι → ℕ}

/-- A linear map between the actual bundles, continuous on total spaces. -/
structure ContinuousStageMap (a b : LineStage K) where
  map : ∀ y, a.Fiber y →ₗ[ℂ] b.Fiber y
  continuous_map : Continuous (fun z : TotalSpace a.Model a.Fiber =>
    TotalSpace.mk' b.Model z.proj (map z.proj z.2))

namespace ContinuousStageMap
variable {a b c : LineStage K}

def comp (g : ContinuousStageMap b c) (f : ContinuousStageMap a b) :
    ContinuousStageMap a c :=
  ⟨fun y => (g.map y).comp (f.map y),g.continuous_map.comp f.continuous_map⟩

def smul (z : ℂ) (f : ContinuousStageMap a b) : ContinuousStageMap a b where
  map y := z • f.map y
  continuous_map := by
    apply continuousOn_univ.mp
    exact continuousOn_bundle_smul_over (𝕜 := ℂ) _
      (FiberBundle.continuous_proj _ _).continuousOn (fun _ => z) _
      continuousOn_const f.continuous_map.continuousOn

def sum {T : Type*} (s : Finset T) (f : T → ContinuousStageMap a b) :
    ContinuousStageMap a b where
  map y := ∑ t ∈ s, (f t).map y
  continuous_map := by
    simp only [LinearMap.sum_apply]
    apply continuousOn_univ.mp
    exact continuousOn_bundle_sum_over (𝕜 := ℂ) _
      (FiberBundle.continuous_proj _ _).continuousOn s
      (fun t z => (f t).map z.proj z.2) (fun t _ => (f t).continuous_map.continuousOn)

def proj {J : Type} [Fintype J] (a : J → LineStage K) (j : J) :
    ContinuousStageMap (LineStage.sum a) (a j) :=
  ⟨LineStage.sumProj a j,LineStage.continuous_sumProj a j⟩

def inj {J : Type} [Fintype J] (a : J → LineStage K) (j : J) :
    ContinuousStageMap (a j) (LineStage.sum a) :=
  ⟨LineStage.sumInj a j,LineStage.continuous_sumInj a j⟩

end ContinuousStageMap
end Kaplansky

end

end OAI
