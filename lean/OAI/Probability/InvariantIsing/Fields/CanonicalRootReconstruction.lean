import OAI.Probability.InvariantIsing.Spectral.SpectralGroupIdentification
import OAI.Probability.InvariantIsing.Spectral.SpectralReconstruction
import OAI.Probability.InvariantIsing.Arrays.ReplicaProductRoots

namespace OAI

/-! Root reconstruction for a finite family of canonical overlap paths.
The Ward equations and reconstructed symbols determine the roots, whose
sum follows from the almost-everywhere path sum. -/

noncomputable section

open MeasureTheory Set Filter Function
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma projectedResolvent_deficit_path_root_tendsto (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) :
    Tendsto (fun s => projectedResolvent ρ eig hρ hρsum a (deficit p (p s)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (projectedResolvent ρ eig hρ hρsum a (deficit p (Function.rightLim p.val 0)))) := by
  have hc : ContinuousOn (fun r => projectedResolvent ρ eig hρ hρsum a (deficit p r))
      (Icc (0 : ℝ) 1) :=
    (continuousOn_projectedResolvent ρ eig hρ hρsum a).comp
      (continuous_deficit p).continuousOn (fun _ hr => deficit_mem_unit p hr)
  have hp : Tendsto p.val (𝓝[>] (0 : ℝ)) (𝓝[Icc (0 : ℝ) 1] (Function.rightLim p.val 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨p.monotone.tendsto_rightLim 0,
      Filter.Eventually.of_forall fun s => ⟨p.nonneg s, p.le_one s⟩⟩
  exact (hc _ p.rightLim_mem_unit).tendsto.comp hp

lemma canonical_symbol_root_eq (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p q : OverlapPath) (d : ℝ) (a : ι)
    (hsymbol : ∀ᵐ s ∂pathMeasure, pathSymbol d q.val s =
      projectedResolvent ρ eig hρ hρsum a (deficit p (p s))) :
    d - (∫ u in 0..1, q u) =
      projectedResolvent ρ eig hρ hρsum a (deficit p (Function.rightLim p.val 0)) := by
  have hqB (u : ℝ) : |q u| ≤ 1 := by
    rw [abs_of_nonneg (q.nonneg u)]
    exact q.le_one u
  have he : ∀ᵐ s ∂pathMeasure, pathSymbol d q.val s -
      projectedResolvent ρ eig hρ hρsum a (deficit p (p s)) = 0 := by
    filter_upwards [hsymbol] with s hs
    exact sub_eq_zero.mpr hs
  have ht := (pathSymbol_root_tendsto d q.val q.measurable hqB
    (q.monotone.tendsto_rightLim 0)).sub
      (projectedResolvent_deficit_path_root_tendsto ρ eig hρ hρsum p a)
  have hz := ae_constant_right_root he ht
  linarith

lemma canonical_group_roots_sum (p : OverlapPath) (q : ι → OverlapPath)
    (hsum : ∀ᵐ s ∂pathMeasure, ∑ a, q a s = p s) :
    (∑ a, Function.rightLim (q a).val 0) = Function.rightLim p.val 0 := by
  classical
  have hs : Tendsto (fun s => ∑ a, q a s) (𝓝[>] (0 : ℝ))
      (𝓝 (∑ a, Function.rightLim (q a).val 0)) := by
    exact tendsto_finsetSum Finset.univ (fun a _ => (q a).monotone.tendsto_rightLim 0)
  have he : ∀ᵐ s ∂pathMeasure, (∑ a, q a s) - p s = 0 := by
    filter_upwards [hsum] with s hs
    exact sub_eq_zero.mpr hs
  have hz := ae_constant_right_root he (hs.sub (p.monotone.tendsto_rightLim 0))
  linarith

/-- The actual root Ward equations fix every canonical group root once
the symbols and the total path have been identified. -/
theorem canonical_group_root_reconstruction (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p : OverlapPath)
    (q : ι → OverlapPath) (d : ι → ℝ)
    (hsymbol : ∀ a, ∀ᵐ s ∂pathMeasure, pathSymbol (d a) (q a).val s =
      projectedResolvent ρ eig hρ hρsum a (deficit p (p s)))
    (hsum : ∀ᵐ s ∂pathMeasure, ∑ a, q a s = p s)
    (hward : ∀ a b, ρ b * Function.rightLim (q a).val 0 -
      ρ a * Function.rightLim (q b).val 0 = (eig a - eig b) *
        ((d a - ∫ u in 0..1, q a u) * Function.rightLim (q b).val 0 +
          Function.rightLim (q a).val 0 * (d b - ∫ u in 0..1, q b u))) (a : ι) :
    Function.rightLim (q a).val 0 = Function.rightLim p.val 0 *
      projectedResolventDerivative ρ eig hρ hρsum a (deficit p (Function.rightLim p.val 0)) := by
  have hsym (b : ι) := canonical_symbol_root_eq ρ eig hρ hρsum p (q b) (d b) b (hsymbol b)
  have hw (b c : ι) : ρ c * Function.rightLim (q b).val 0 -
      ρ b * Function.rightLim (q c).val 0 = (eig b - eig c) *
        (projectedResolvent ρ eig hρ hρsum b (deficit p (Function.rightLim p.val 0)) *
            Function.rightLim (q c).val 0 +
          Function.rightLim (q b).val 0 *
            projectedResolvent ρ eig hρ hρsum c (deficit p (Function.rightLim p.val 0))) := by
    simpa only [hsym b, hsym c] using hward b c
  have he := spectral_root_reconstruction ρ eig hρ hρsum
    (deficit_mem_unit p p.rightLim_mem_unit).1 (fun b => Function.rightLim (q b).val 0) hw a
  rwa [canonical_group_roots_sum p q hsum] at he

/-- The symbols, path sum and root Ward equations determine the complete
canonical spectral family, including its diagonal. -/
theorem canonical_groups_identification_of_symbols_rootWard (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p : OverlapPath)
    (q : ι → OverlapPath) (d : ι → ℝ)
    (hsymbol : ∀ a, ∀ᵐ s ∂pathMeasure, pathSymbol (d a) (q a).val s =
      projectedResolvent ρ eig hρ hρsum a (deficit p (p s)))
    (hsum : ∀ᵐ s ∂pathMeasure, ∑ a, q a s = p s)
    (hward : ∀ a b, ρ b * Function.rightLim (q a).val 0 -
      ρ a * Function.rightLim (q b).val 0 = (eig a - eig b) *
        ((d a - ∫ u in 0..1, q a u) * Function.rightLim (q b).val 0 +
          Function.rightLim (q a).val 0 * (d b - ∫ u in 0..1, q b u))) :
    (∀ a, d a = spectralGroupDiagonal ρ eig hρ hρsum p a) ∧
      ∀ᵐ s ∂pathMeasure, ∀ a, q a s = spectralGroupPath ρ eig hρ hρsum p a s :=
  spectralGroups_identification_of_symbols_roots ρ eig hρ hρsum p q d hsymbol
    (canonical_group_root_reconstruction ρ eig hρ hρsum p q d hsymbol hsum hward)

end InvariantIsing

end

end OAI
