import Mathlib
import OAI.Analysis.Conductivity.Fourier.SpectralExtensionMono
import OAI.Analysis.Conductivity.Flux.SmoothFluxIntegrable

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise ENNReal

def CompactGlobalUpdate.refl
    (μ : Measure Coord3) (U : Set Coord3) (u : Coord3 → Fin 2 → ℝ)
    (A : Coord3 → Symmetric3) (hA : Measurable A) : CompactGlobalUpdate μ U u A where
  du := 0
  dF := 0
  tensor := A
  smooth_du := contDiff_const
  compact_du := by simp [HasCompactSupport]
  support_du := by simp
  smooth_dF := contDiff_const
  compact_dF := by simp [HasCompactSupport]
  support_dF := by simp
  cauchy_dF := by
    intro j ψ _
    change (∫ x, fderiv ℝ ψ x (0 : Coord3) ∂μ) = 0
    simp
  measurable_tensor := hA
  constitutive := by intro x; simp only [Pi.zero_apply,add_zero]

lemma spectral_depth_nonempty {T : Set DiagonalTriple}
    (hT : (spectralExtension T).Nonempty) (n : ℕ) :
    (spectralExtension (depthClass T n)).Nonempty := by
  obtain ⟨A,hA⟩ := hT
  exact ⟨A,spectral_depth_mono T (Nat.zero_le n) hA⟩

theorem global_finite_depth_iteration
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : IsOpen T) (hsub : ∀ d ∈ T, IsFiniteLaminate a b d)
    (hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T)
    (hsc : (spectralExtension T).Nonempty)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (n : ℕ)
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : CompactGlobalUpdate μ U u A,
      μ (U \ regularRegion (fun x => u x+R.du x) R.tensor U) = 0 ∧
      (∀ᵐ x ∂μ, x ∈ U → R.tensor x ∈ matrixFiniteLaminate a b) ∧
      μ (U \ R.tensor ⁻¹' spectralExtension T) ≤
        μ (U \ A ⁻¹' spectralExtension (depthClass T n)) + ENNReal.ofReal ε := by
  induction n generalizing u A ε with
  | zero =>
    refine ⟨CompactGlobalUpdate.refl μ U u A hAm,?_,hgraph,?_⟩
    · simpa only [CompactGlobalUpdate.refl,Pi.zero_apply,add_zero] using hreg
    · change μ (U \ A ⁻¹' spectralExtension T) ≤ μ (U \ A ⁻¹' spectralExtension T) + ENNReal.ofReal ε
      exact le_add_right le_rfl
  | succ n ih =>
    let G := regularRegion u A U ∩ A ⁻¹' spectralExtension (depthClass T (n+1))
    have hGm : MeasurableSet G := (isOpen_regular_tensor_target u A U
      (isOpen_spectralExtension (isOpen_depthClass ha hT hsub (n+1)) (depthClass_permute hperm (n+1)))).measurableSet
    obtain ⟨R,hRreg,hRG,hRloss⟩ := global_regular_depth_reduction μ u A hAm hUb hdiv hreg
      ha hT hsub hperm hgraph (spectral_depth_nonempty hsc n) hGm (Subset.rfl) (by linarith : 0 < ε/2)
    obtain ⟨hRint,hRdiv⟩ := R.preserves_harmonic μ hint hdiv
    obtain ⟨S,hSreg,hSG,hSloss⟩ := ih (fun x => u x+R.du x) R.tensor R.measurable_tensor
      hRint hRdiv hRreg hRG (by linarith : 0 < ε/2)
    refine ⟨R.trans μ S,?_,hSG,?_⟩
    · simpa only [CompactGlobalUpdate.trans,Pi.add_apply,← add_assoc] using hSreg
    · have hGbad : μ (U \ G) ≤ μ (U \ A ⁻¹' spectralExtension (depthClass T (n+1))) := by
        have hs : U \ G ⊆ (U \ regularRegion u A U) ∪
            (U \ A ⁻¹' spectralExtension (depthClass T (n+1))) := by
          intro x hx
          by_cases hr : x ∈ regularRegion u A U
          · exact Or.inr ⟨hx.1,fun ht => hx.2 ⟨hr,ht⟩⟩
          · exact Or.inl ⟨hx.1,hr⟩
        simpa only [hreg,zero_add] using (measure_mono (μ := μ) hs).trans (measure_union_le _ _)
      calc
        μ (U \ (R.trans μ S).tensor ⁻¹' spectralExtension T) ≤
            μ (U \ R.tensor ⁻¹' spectralExtension (depthClass T n)) + ENNReal.ofReal (ε/2) := hSloss
        _ ≤ (μ (U \ G) + ENNReal.ofReal (ε/2)) + ENNReal.ofReal (ε/2) := add_le_add hRloss le_rfl
        _ ≤ (μ (U \ A ⁻¹' spectralExtension (depthClass T (n+1))) + ENNReal.ofReal (ε/2)) + ENNReal.ofReal (ε/2) :=
          add_le_add (add_le_add hGbad le_rfl) le_rfl
        _ = μ (U \ A ⁻¹' spectralExtension (depthClass T (n+1))) + ENNReal.ofReal ε := by
          rw [add_assoc,← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 2
          ring

end ScalarConductivity

end

end OAI
