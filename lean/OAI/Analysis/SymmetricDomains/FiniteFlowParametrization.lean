import Mathlib
import OAI.Analysis.SymmetricDomains.FlowWordFirstJet

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (p : U)
include hU hc hbd Γ hhol

theorem exists_finite_flow_parametrization_with_regular_jets
    (P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p))
    (hP : ∀ X : completeGeneratorSpace hU hc hbd Γ hhol,
        (P (completeGeneratorFirstJet hU hc hbd Γ hhol p X)).val=
          completeGeneratorFirstJet hU hc hbd Γ hhol p X) :
    ∃ F : LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p) → Biholomorph U U,
      Continuous F ∧ F 0=1 ∧
      HasStrictFDerivAt (fun t => P (ambientFirstJet p (F t)))
        (ContinuousLinearMap.id ℝ _) 0 ∧
      HasStrictFDerivAt (𝕜 := ℝ) (E := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p))
        (F := Affine n × (Affine n →L[ℂ] Affine n)) (fun t => ambientFirstJet p (F t))
        (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)).subtypeL 0 ∧
      ∀ (p' : U) (t₀ : LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)),
        ∃ L : LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p) →L[ℝ]
          (Affine n × (Affine n →L[ℂ] Affine n)),
          HasStrictFDerivAt (𝕜 := ℝ) (E := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p))
            (F := Affine n × (Affine n →L[ℂ] Affine n)) (fun t => ambientFirstJet p' (F t)) L t₀ := by
  classical
  let J := completeGeneratorFirstJet hU hc hbd Γ hhol p
  let R : Type := ↥(LinearMap.range J)
  let _ : Module.Free ℝ R := Module.Free.of_divisionRing ℝ R
  let _ : AddCommMonoid (R →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n))) := ContinuousLinearMap.addCommMonoid
  let d := Module.finrank ℝ R
  let b : Module.Basis (Fin d) ℝ R := Module.finBasis ℝ R
  have hex (i : Fin d) : ∃ X : completeGeneratorSpace hU hc hbd Γ hhol,
      J X=(b i).val := (b i).property
  choose X hX using hex
  have hflow (i : Fin d) := (X i).property
  choose a ha ha0 ham hgen using hflow
  let l : Fin d → R →L[ℝ] ℝ := fun i =>
    ⟨b.coord i, LinearMap.continuous_of_finiteDimensional (𝕜 := ℝ) (E := R) (F' := ℝ) (b.coord i)⟩
  let is : List (Fin d) := List.ofFn id
  let F : R → Biholomorph U U := flowWord (E := R) a l is
  let L : R →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)) :=
    (is.map (fun i => (ContinuousLinearMap.toSpanSingleton ℝ
      (infinitesimalGenerator (a i) p.val,fderiv ℂ (infinitesimalGenerator (a i)) p.val)).comp (l i))).sum
  have hf : HasStrictFDerivAt (fun t => ambientFirstJet p (F t)) L 0 :=
    flowWord_firstJet_hasStrictFDerivAt_zero (E := R) hU hbd p a l ha ha0 ham is
  have hL : L=J.range.subtypeL := by
    apply DFunLike.ext
    intro v
    change L v=v.val
    dsimp only [L,is]
    rw [List.map_ofFn, List.sum_ofFn]
    simp only [Function.comp_apply,id_eq,sum_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply]
    have he (i : Fin d) : (infinitesimalGenerator (a i) p.val,
        fderiv ℂ (infinitesimalGenerator (a i)) p.val)=(b i).val := by
      rw [hgen i]
      exact hX i
    simp_rw [he]
    have hv := congrArg J.range.subtype (b.sum_repr v)
    rw [map_sum] at hv
    simp only [map_smul] at hv
    exact hv
  rw [hL] at hf
  have hPc := ContinuousLinearMap.hasStrictFDerivAt (𝕜 := ℝ) (E := Affine n × (Affine n →L[ℂ] Affine n)) (F := R) (x := ambientFirstJet p (F 0)) P
  have hp := HasStrictFDerivAt.comp (𝕜 := ℝ) (E := R) (F := Affine n × (Affine n →L[ℂ] Affine n)) (G := R) 0 hPc hf
  have hPL : P.comp J.range.subtypeL=ContinuousLinearMap.id ℝ R := by
    apply DFunLike.ext
    intro v
    apply Subtype.ext
    change (P v.val).val=v.val
    obtain ⟨X,hXv⟩ := v.property
    rw [←hXv]
    exact hP X
  rw [hPL] at hp
  refine ⟨F,flowWord_continuous (E := R) a l ha is,flowWord_zero (E := R) a l ha0 is,hp,hf,?_⟩
  intro p' t₀
  exact flowWord_exists_firstJet_strictFDeriv (E := R) hU hbd p' a l ha ha0 ham is t₀

theorem exists_finite_flow_parametrization
    (P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p))
    (hP : ∀ X : completeGeneratorSpace hU hc hbd Γ hhol,
        (P (completeGeneratorFirstJet hU hc hbd Γ hhol p X)).val=
          completeGeneratorFirstJet hU hc hbd Γ hhol p X) :
    ∃ F : LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p) → Biholomorph U U,
      Continuous F ∧ F 0=1 ∧
      HasStrictFDerivAt (fun t => P (ambientFirstJet p (F t)))
        (ContinuousLinearMap.id ℝ _) 0 := by
  obtain ⟨F,hF,hF0,hd,_⟩ := exists_finite_flow_parametrization_with_regular_jets hU hc hbd Γ hhol p P hP
  exact ⟨F,hF,hF0,hd⟩

end Biholomorph
end Release061

end

end OAI
