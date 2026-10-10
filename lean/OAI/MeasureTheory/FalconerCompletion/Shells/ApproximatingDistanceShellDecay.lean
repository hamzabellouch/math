import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Estimates.AssemblySmallParameters
import OAI.MeasureTheory.FalconerCompletion.Graphs.AssemblyPairCoefficientSum
import OAI.MeasureTheory.FalconerCompletion.Shells.TwoProfileComponentShell

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical Topology ENNReal NNReal
variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin (n+1))

theorem actual_approximating_distance_shell_decay (hn : 1 ≤ n) (Ctest chi : ℝ) (hchi : 0 < chi) :
    ∃ beta : ℝ, 0 < beta ∧ beta < min (chi/10) (1/10) ∧
    ∃ kap : ℝ, 0 < kap ∧ kap ≤ 1/1000 ∧
    ∃ sig : ℝ, 0 < sig ∧ sig < kap/1000 ∧ beta+(n+4:ℝ)*sig < chi/4 ∧
    ∃ omega gamma : ℝ, 0 < omega ∧ 4*(n+1:ℝ)*omega < beta/8 ∧ 0 < gamma ∧
      ∀ (Ψ : ℝ → ℝ), ContDiff ℝ ∞ Ψ → tsupport Ψ ⊆ Ioo (1/4:ℝ) 4 →
        (∀ r, 0 ≤ Ψ r) → (∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r) →
      ∀ (ψ : (EuclideanSpace ℝ (Fin (n+1))) → ℂ), ContDiff ℝ ∞ ψ → (∀ w, ‖w‖=1 → ‖ψ w‖ ≤ 1) →
      ∀ (δ K A : ℝ), 0 < δ → 0 < K → 0 < A → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {ι κ : Type} [Fintype ι] [Fintype κ]
        (μ ν : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
        (B : ℕ) (F : AssemblyClassFamily ι μ N B chi sig)
        (G : AssemblyClassFamily κ ν N B chi sig)
        (I : Finset ℕ) (X Y : ℕ → Set (EuclideanSpace ℝ (Fin (n+1)))),
        (∀ l ∈ I, MeasurableSet (X l) ∧ MeasurableSet (Y l)) →
        (∀ l ∈ I, X l ⊆ treeCell [] ∧ Y l ⊆ treeCell []) →
        (∀ l ∈ I, ∀ x ∈ X l, ∀ y ∈ Y l, δ ≤ dist x y ∧ dist x y ≤ K) →
        (∀ l ∈ I, ∀ x ∈ X l, ∀ y ∈ Y l,
          ψ =ᶠ[𝓝 ((dist x y)⁻¹ • (x-y))] (fun _ => 1) ∧
          ψ =ᶠ[𝓝 (-((dist x y)⁻¹ • (x-y)))] (fun _ => 0)) →
        (Set.Pairwise (↑I : Set ℕ) (fun l m => Disjoint (X l ×ˢ Y l) (X m ×ˢ Y m))) →
        (I.card : ℝ) ≤ A*((2:ℝ)^N)^(2*(n+1:ℝ)*omega) →
      (∫ r in {r : ℝ | ((2:ℝ)^N)/2 ≤ |r| ∧ |r| ≤ 2*((2:ℝ)^N)},
        ‖charFun (assemblyTau F G kap Ctest beta I X Y) r‖^2) ≤
          2*A^2*((2:ℝ)^N)^(-gamma)
 := by
  obtain ⟨Cd,hCd,hshell⟩ := actual_two_profile_component_shell hn Ctest
  obtain ⟨beta,hbeta,hbetasm,kap,hkap,hkap1,sig,hsig,hsigkap,hsmall,omega,homega,homegasm,hexp⟩ :=
    assembly_small_parameters n hchi hCd
  refine ⟨beta,hbeta,hbetasm,kap,hkap,hkap1,sig,hsig,hsigkap,hsmall,omega,beta/2,homega,homegasm,
    by positivity,?_⟩
  intro Ψ hΨ hsupp hΨnon hΨone ψ hψ hψone δ K A hδ hK hA
  obtain ⟨N₀,hN₀⟩ := hshell chi beta sig kap (beta/8) hchi hbeta hbetasm hkap hkap1 hsig
    hsigkap hsmall (by positivity) Ψ hΨ hsupp hΨnon hΨone ψ hψ hψone δ K hδ hK
  refine ⟨N₀,?_⟩
  intro N hN ι κ _ _ μ ν _ _ B F G I X Y hXY hroot hsep hout hdis hcard
  let R : ℝ := (2:ℝ)^N
  let E : ℝ := -beta+Cd*(kap+sig/kap)+beta/8
  have hR : 1≤R := one_le_pow₀ (by norm_num)
  have hRp : 0<R := by dsimp[R];positivity
  have hcomp (i : ι) (j : κ) (l : ℕ) (hl : l∈I) :
      assemblyPositiveEnergy (assemblyComponentMeasure (F.env kap Ctest i) (G.env kap Ctest j)
        (assemblyPairEntry F G kap Ctest beta i j) (X l) (Y l)) R ≤ R^E := by
    let := (F.profile i).probability
    let := (G.profile j).probability
    have hm : ∀ᵐ z ∂((assemblyClassLaw μ (F.domain i)).restrict (X l)).prod
        ((assemblyClassLaw ν (G.domain j)).restrict (Y l)), z.1∈X l ∧ z.2∈Y l :=
      (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem (hXY l hl).1)).and
        (Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (hXY l hl).2))
    have ho : ∀ᵐ z ∂((assemblyClassLaw μ (F.domain i)).restrict (X l)).prod
        ((assemblyClassLaw ν (G.domain j)).restrict (Y l)),
        ψ =ᶠ[𝓝 ((dist z.1 z.2)⁻¹ • (z.1-z.2))] (fun _ => 1) ∧
        ψ =ᶠ[𝓝 (-((dist z.1 z.2)⁻¹ • (z.1-z.2)))] (fun _ => 0) := by
      filter_upwards [hm] with z hz
      exact hout l hl z.1 hz.1 z.2 hz.2
    have hh := hN₀ N hN (assemblyClassLaw μ (F.domain i)) (assemblyClassLaw ν (G.domain j))
      B (F.mass i) (G.mass j) (F.profile i) (G.profile j) (F.law_root i) (G.law_root j)
      (X l) (Y l) (fun _ => 1) (fun _ => 1) (hXY l hl).1 (hXY l hl).2
      (hroot l hl).1 (hroot l hl).2 measurable_const measurable_const
      (by intro x;simp) (by intro x;simp) (hsep l hl) ho
    have heq (r : ℝ) := assemblyComponentMeasure_fourier (F.env kap Ctest i)
      (G.env kap Ctest j) (assemblyPairEntry F G kap Ctest beta i j) (X l) (Y l)
      (F.profile i).zero (G.profile j).zero r
    unfold assemblyPositiveEnergy
    simp_rw [heq]
    exact hh.2
  obtain ⟨hfinite,hpos⟩ := assemblyTau_positive_energy F G kap Ctest beta I X Y hXY hdis hδ
    (fun l hl x hx y hy => (hsep l hl x hx y hy).1) R (R^E) (Real.rpow_nonneg hRp.le E) hcomp
  let := hfinite
  rw [assemblyEnergy_two_sided _ hRp]
  have hcard2 : (I.card:ℝ)^2 ≤ A^2*R^(4*(n+1:ℝ)*omega) := by
    change (I.card:ℝ) ≤ A*R^(2*(n+1:ℝ)*omega) at hcard
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg I.card) hcard 2
    have hp : (R^(2*(n+1:ℝ)*omega))^2 = R^(4*(n+1:ℝ)*omega) := by
      rw [← Real.rpow_mul_natCast hRp.le]
      congr 1
      push_cast
      ring
    simpa only [mul_pow,hp] using hh
  have hbound : (I.card:ℝ)^2*R^E ≤ A^2*R^(-(beta/2)) := by
    calc
      _ ≤ (A^2*R^(4*(n+1:ℝ)*omega))*R^E :=
        mul_le_mul_of_nonneg_right hcard2 (Real.rpow_nonneg hRp.le E)
      _ = A^2*R^(E+4*(n+1:ℝ)*omega) := by
        rw [mul_assoc,← Real.rpow_add hRp]
        congr 2
        ring
      _ ≤ _ := by
        simpa only [neg_div] using
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR hexp) (sq_nonneg A)
  have hh := mul_le_mul_of_nonneg_left (hpos.trans hbound) (by norm_num : (0:ℝ)≤2)
  simpa only [mul_assoc] using hh

end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
