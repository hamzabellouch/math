import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.WeakChangeVariables

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

@[simp] lemma fermionPermutation_apply {N : ℕ} (π : Equiv.Perm (Fin N))
    (F : SectorHilbert N) (s : Spins N) :
    fermionPermutation π F s = (((Equiv.Perm.sign π : ℤ) : ℂ)) •
      Lp.compMeasurePreserving (permuteConfiguration π) (permuteConfiguration_preserving π)
        (F (s ∘ π)) := rfl

lemma permuteConfiguration_mul {N : ℕ} (π σ : Equiv.Perm (Fin N)) :
    (permuteConfiguration (π * σ) : Configuration N → Configuration N) =
      permuteConfiguration σ ∘ permuteConfiguration π := by
  funext x i
  simp only [Function.comp_apply, permuteConfiguration_apply, Equiv.Perm.coe_mul]

lemma fermionPermutation_mul {N : ℕ} (π σ : Equiv.Perm (Fin N)) (F : SectorHilbert N) :
    fermionPermutation π (fermionPermutation σ F) = fermionPermutation (π * σ) F := by
  apply PiLp.ext
  intro s
  simp only [fermionPermutation_apply]
  change _ • (Lp.compMeasurePreservingₗ ℂ (permuteConfiguration π)
    (permuteConfiguration_preserving π)) (_ • _) = _
  rw [map_smul]
  rw [smul_smul]
  have hsign : (((Equiv.Perm.sign (π * σ) : ℤ) : ℂ)) =
      (((Equiv.Perm.sign π : ℤ) : ℂ)) * (((Equiv.Perm.sign σ : ℤ) : ℂ)) := by
    simp
  rw [hsign]
  congr 1
  have hs : (s ∘ π) ∘ σ = s ∘ (π * σ) := rfl
  rw [hs]
  change Lp.compMeasurePreserving (permuteConfiguration π) _
    (Lp.compMeasurePreserving (permuteConfiguration σ) _ _) = _
  rw [← Lp.compMeasurePreserving_comp_apply]
  simp only [← permuteConfiguration_mul]

lemma sectorDirections_permute {N : ℕ} (π : Equiv.Perm (Fin N)) (k : Fin N × Fin 3) :
    permuteConfiguration π (sectorDirections N k) = sectorDirections N (π.symm k.1, k.2) := by
  classical
  ext i a
  simp only [permuteConfiguration_apply, Function.comp_apply, sectorDirections, direction]
  by_cases h : i = π.symm k.1
  · subst i
    simp
  · have h' : π i ≠ k.1 := by
      intro hh
      apply h
      exact π.injective (by simpa using hh)
    simp [h, h']

def sectorGraphPermutation {N : ℕ} (π : Equiv.Perm (Fin N)) : SectorGraph N →L[ℂ] SectorGraph N :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Spins N => weakGraph (sectorDirections N))
    ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun s =>
      ((((Equiv.Perm.sign π : ℤ) : ℂ)) • weakGraphChange (sectorDirections N)
        (permuteConfiguration π) (permuteConfiguration_preserving π)
        (fun k => (π.symm k.1, k.2)) (sectorDirections_permute π)).comp
        (PiLp.proj 2 (fun _ : Spins N => weakGraph (sectorDirections N)) (s ∘ π)))

lemma sectorGraphPermutation_value {N : ℕ} (π : Equiv.Perm (Fin N)) (F : SectorGraph N) :
    sectorGraphValue N (sectorGraphPermutation π F) = fermionPermutation π (sectorGraphValue N F) := by
  rfl

def fermionAverage (N : ℕ) : SectorHilbert N →L[ℂ] SectorHilbert N :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ • ∑ π : Equiv.Perm (Fin N), fermionPermutation π

lemma fermionAverage_mem {N : ℕ} (F : SectorHilbert N) : fermionAverage N F ∈ fermionSpace N := by
  classical
  rw [mem_fermionSpace]
  intro π
  simp only [fermionAverage, smul_apply, sum_apply,
    map_smul, map_sum, fermionPermutation_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft π) _ _ (fun σ => rfl)

lemma fermionAverage_eq_self {N : ℕ} (F : fermionSpace N) : fermionAverage N F = F := by
  classical
  have hF := (mem_fermionSpace F.val).mp F.property
  simp only [fermionAverage, smul_apply, sum_apply, hF]
  simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]

lemma sectorGraphValue_average (N : ℕ) (F : SectorGraph N) :
    sectorGraphValue N (((Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ •
      ∑ π : Equiv.Perm (Fin N), sectorGraphPermutation π) F) =
      fermionAverage N (sectorGraphValue N F) := by
  simp only [smul_apply, sum_apply, map_smul, map_sum, sectorGraphPermutation_value,
    fermionAverage]

def fermionGraphAverage (N : ℕ) : SectorGraph N →L[ℂ] fermionGraph N :=
  ((Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ • ∑ π : Equiv.Perm (Fin N), sectorGraphPermutation π
    ).codRestrict (fermionGraph N) (by
      intro F
      change sectorGraphValue N _ ∈ fermionSpace N
      rw [sectorGraphValue_average]
      exact fermionAverage_mem _)

lemma fermionGraphAverage_value {N : ℕ} (F : SectorGraph N) :
    (fermionGraphValue N (fermionGraphAverage N F)).val = fermionAverage N (sectorGraphValue N F) :=
  sectorGraphValue_average N F

lemma sectorGraphValue_denseRange (N : ℕ) : DenseRange (sectorGraphValue N) := by
  let eV := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Spins N => weakGraph (sectorDirections N))
  let eH := PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : Spins N => Lp ℂ 2 (volume : Measure (Configuration N)))
  have hd := DenseRange.piMap (fun _ : Spins N => weakGraphValue_denseRange (sectorDirections N))
  have hc : Continuous (Pi.map (fun _ : Spins N => weakGraphValue (sectorDirections N))) := by
    fun_prop
  exact eH.symm.surjective.denseRange.comp (hd.comp eV.surjective.denseRange hc) eH.symm.continuous

theorem fermionGraphValue_denseRange (N : ℕ) : DenseRange (fermionGraphValue N) := by
  let p : SectorHilbert N →L[ℂ] fermionSpace N :=
    (fermionAverage N).codRestrict (fermionSpace N) fermionAverage_mem
  have hp : Function.Surjective p := by
    intro F
    exact ⟨F.val, Subtype.ext (fermionAverage_eq_self F)⟩
  have hd := hp.denseRange.comp (sectorGraphValue_denseRange N) p.continuous
  have he : p ∘ sectorGraphValue N = fermionGraphValue N ∘ fermionGraphAverage N := by
    funext F
    exact Subtype.ext (fermionGraphAverage_value F).symm
  rw [he] at hd
  exact hd.of_comp

end CoulombAtom

end

end OAI
