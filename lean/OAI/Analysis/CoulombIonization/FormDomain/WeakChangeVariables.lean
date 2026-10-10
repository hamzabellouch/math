import Mathlib
import OAI.Analysis.CoulombIonization.Model
import OAI.Analysis.CoulombIonization.FormDomain.WeakDerivative

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
section WeakChangeVariables
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in

lemma IsWeakDerivative.comp_linearEquiv {v w : E} {f g : E → ℂ}
    (hw : IsWeakDerivative v f g) (e : E ≃L[ℝ] E)
    (he : MeasurePreserving e) (hv : e w = v) :
    IsWeakDerivative w (f ∘ e) (g ∘ e) := by
  intro φ hφ hcφ
  let ψ : E → ℝ := φ ∘ e.symm
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp e.symm.contDiff
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph e.symm.toHomeomorph
  have hev : e.symm v = w := by rw [← hv, e.symm_apply_apply]
  have hd (x : E) : lineDeriv ℝ ψ (e x) v = lineDeriv ℝ φ x w := by
    rw [(hψ.differentiable (by simp) (e x)).lineDeriv_eq_fderiv,
      (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv]
    have hh := (hφ.differentiable (by simp) (e.symm (e x))).hasFDerivAt.comp
      (e x) (e.symm.hasFDerivAt)
    have hh' := congrArg (fun A : E →L[ℝ] ℝ => A v) hh.fderiv
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      e.symm_apply_apply, hev] using hh'
  have hi1 : (∫ x, f (e x) * Complex.ofReal (lineDeriv ℝ ψ (e x) v)) =
      ∫ x, f x * Complex.ofReal (lineDeriv ℝ ψ x v) :=
    he.integral_comp e.toHomeomorph.measurableEmbedding
      (fun x => f x * Complex.ofReal (lineDeriv ℝ ψ x v))
  have hi2 : (∫ x, g (e x) * (ψ (e x) : ℂ)) = ∫ x, g x * (ψ x : ℂ) :=
    he.integral_comp e.toHomeomorph.measurableEmbedding
      (fun x => g x * (ψ x : ℂ))
  have hh := hw ψ hψ hcψ
  rw [← hi1, ← hi2] at hh
  simpa only [hd, ψ, Function.comp_apply, e.symm_apply_apply] using hh

end WeakChangeVariables

section WeakGraphChange
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι]

def weakGraphChangeAmbient (v : ι → E) (e : E ≃L[ℝ] E) (he : MeasurePreserving e)
    (κ : ι → ι) : weakGraph v →L[ℂ] WeakGraphAmbient E ι :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Option ι => Lp ℂ 2 (volume : Measure E))
    ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j =>
      (Lp.compMeasurePreservingₗᵢ ℂ e he).toContinuousLinearMap.comp
        ((PiLp.proj 2 (fun _ : Option ι => Lp ℂ 2 (volume : Measure E)) (j.map κ)).comp
          (weakGraph v).subtypeL))

omit [Fintype ι] in
lemma weakGraphChangeAmbient_mem (v : ι → E) (e : E ≃L[ℝ] E) (he : MeasurePreserving e)
    (κ : ι → ι) (hv : ∀ i, e (v i) = v (κ i)) (F : weakGraph v) :
    weakGraphChangeAmbient v e he κ F ∈ weakGraph v := by
  rw [mem_weakGraph]
  intro i
  have hh := ((mem_weakGraph v F.val).mp F.property (κ i)).comp_linearEquiv e he (hv i)
  exact hh.congr_ae (Lp.coeFn_compMeasurePreserving (F.val none) he).symm
    (Lp.coeFn_compMeasurePreserving (F.val (some (κ i))) he).symm

def weakGraphChange (v : ι → E) (e : E ≃L[ℝ] E) (he : MeasurePreserving e)
    (κ : ι → ι) (hv : ∀ i, e (v i) = v (κ i)) : weakGraph v →L[ℂ] weakGraph v :=
  (weakGraphChangeAmbient v e he κ).codRestrict (weakGraph v)
    (weakGraphChangeAmbient_mem v e he κ hv)

end WeakGraphChange

abbrev SectorHilbert (N : ℕ) := PiLp 2 (fun _ : Spins N => Lp ℂ 2 (volume : Measure (Configuration N)))

def permuteConfiguration {N : ℕ} (π : Equiv.Perm (Fin N)) : Configuration N ≃L[ℝ] Configuration N :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin N => Space) π.symm

@[simp] lemma permuteConfiguration_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : Configuration N) :
    permuteConfiguration π x = x ∘ π := by
  ext i
  simp [permuteConfiguration, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft]

lemma permuteConfiguration_preserving {N : ℕ} (π : Equiv.Perm (Fin N)) :
    MeasurePreserving (permuteConfiguration π) := by
  exact volume_measurePreserving_piCongrLeft (fun _ : Fin N => Space) π.symm

def fermionPermutation {N : ℕ} (π : Equiv.Perm (Fin N)) : SectorHilbert N →L[ℂ] SectorHilbert N :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Spins N => Lp ℂ 2 (volume : Measure (Configuration N)))
    ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun s =>
      ((((Equiv.Perm.sign π : ℤ) : ℂ)) •
        (Lp.compMeasurePreservingₗᵢ ℂ (permuteConfiguration π)
          (permuteConfiguration_preserving π)).toContinuousLinearMap).comp
        (PiLp.proj 2 (fun _ : Spins N => Lp ℂ 2 (volume : Measure (Configuration N))) (s ∘ π)))

def fermionSpace (N : ℕ) : Submodule ℂ (SectorHilbert N) :=
  ⨅ π : Equiv.Perm (Fin N), (fermionPermutation π - ContinuousLinearMap.id ℂ _).ker

lemma mem_fermionSpace {N : ℕ} (F : SectorHilbert N) :
    F ∈ fermionSpace N ↔ ∀ π : Equiv.Perm (Fin N), fermionPermutation π F = F := by
  simp [fermionSpace, sub_eq_zero]

lemma fermionSpace_isClosed (N : ℕ) : IsClosed (fermionSpace N : Set (SectorHilbert N)) := by
  simp only [fermionSpace, Submodule.coe_iInf]
  exact isClosed_iInter fun π => (fermionPermutation π - ContinuousLinearMap.id ℂ _).isClosed_ker

instance fermionSpace_completeSpace (N : ℕ) : CompleteSpace (fermionSpace N) :=
  (fermionSpace_isClosed N).completeSpace_coe

abbrev sectorDirections (N : ℕ) : Fin N × Fin 3 → Configuration N := fun k => direction k.1 k.2

instance weakSectorGraph_normedAddCommGroup (N : ℕ) : NormedAddCommGroup (weakGraph (sectorDirections N)) :=
  Submodule.normedAddCommGroup _
instance weakSectorGraph_innerProductSpace (N : ℕ) : InnerProductSpace ℂ (weakGraph (sectorDirections N)) :=
  Submodule.innerProductSpace _
instance weakSectorGraph_normedSpace (N : ℕ) : NormedSpace ℂ (weakGraph (sectorDirections N)) :=
  Submodule.normedSpace _

abbrev SectorGraph (N : ℕ) := PiLp 2 (fun _ : Spins N => weakGraph (sectorDirections N))

instance sectorGraph_normedAddCommGroup (N : ℕ) : NormedAddCommGroup (SectorGraph N) :=
  PiLp.normedAddCommGroup 2 _
instance sectorGraph_innerProductSpace (N : ℕ) : InnerProductSpace ℂ (SectorGraph N) :=
  PiLp.innerProductSpace _
instance sectorGraph_normedSpace (N : ℕ) : NormedSpace ℂ (SectorGraph N) :=
  PiLp.normedSpace 2 ℂ _

def sectorGraphValue (N : ℕ) : SectorGraph N →L[ℂ] SectorHilbert N :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Spins N => Lp ℂ 2 (volume : Measure (Configuration N)))
    ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun s => (weakGraphValue (sectorDirections N)).comp
      (PiLp.proj 2 (fun _ : Spins N => weakGraph (sectorDirections N)) s))

@[simp] lemma sectorGraphValue_apply {N : ℕ} (F : SectorGraph N) (s : Spins N) :
    sectorGraphValue N F s = (F s).val none := rfl

lemma sectorGraphValue_injective (N : ℕ) : Function.Injective (sectorGraphValue N) := by
  intro F G hFG
  apply PiLp.ext
  intro s
  apply weakGraphValue_injective (sectorDirections N)
  exact congrArg (fun h : SectorHilbert N => h s) hFG

def fermionGraph (N : ℕ) : Submodule ℂ (SectorGraph N) :=
  (fermionSpace N).comap (sectorGraphValue N).toLinearMap

instance fermionGraph_normedAddCommGroup (N : ℕ) : NormedAddCommGroup (fermionGraph N) :=
  Submodule.normedAddCommGroup _
instance fermionGraph_innerProductSpace (N : ℕ) : InnerProductSpace ℂ (fermionGraph N) :=
  Submodule.innerProductSpace _
instance fermionGraph_normedSpace (N : ℕ) : NormedSpace ℂ (fermionGraph N) :=
  Submodule.normedSpace _

lemma fermionGraph_isClosed (N : ℕ) : IsClosed (fermionGraph N : Set (SectorGraph N)) :=
  (fermionSpace_isClosed N).preimage (sectorGraphValue N).continuous

instance fermionGraph_completeSpace (N : ℕ) : CompleteSpace (fermionGraph N) :=
  (fermionGraph_isClosed N).completeSpace_coe

def fermionGraphValue (N : ℕ) : fermionGraph N →L[ℂ] fermionSpace N :=
  ((sectorGraphValue N).comp (fermionGraph N).subtypeL).codRestrict (fermionSpace N)
    (fun F => F.property)

lemma fermionGraphValue_injective (N : ℕ) : Function.Injective (fermionGraphValue N) := by
  intro F G hFG
  apply Subtype.ext
  apply sectorGraphValue_injective N
  exact congrArg Subtype.val hFG

end CoulombAtom

end

end OAI
