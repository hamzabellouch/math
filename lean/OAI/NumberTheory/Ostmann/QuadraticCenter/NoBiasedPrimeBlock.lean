import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualBiasedPopulations
import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualKernelSieveBound
import OAI.NumberTheory.Ostmann.QuadraticCenter.CommonCenterMultiplierScale
import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericKernelPopulationsActual
import OAI.NumberTheory.Ostmann.QuadraticCenter.RootCollisionContradiction

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem eventually_no_biased_prime_block (d : Decomposition)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) →
      (∀ p ∈ P, Z ≤ p ∧ p ≤ 2*Z) → c*(Z : ℝ)/Real.log Z ≤ P.card →
      ∀ ε t : ℕ → ℤ,
      (∀ p ∈ P, (ε p=1 ∨ ε p=-1) ∧
        δ/4 ≤ (∑ x ∈ positiveIntegerWindow d.A (parameterX T),
          ((ε p*jacobiSym (x-t p) p : ℤ) : ℝ))/(positiveIntegerWindow d.A (parameterX T)).card ∧
        (∑ x ∈ negativeIntegerWindow d.B (parameterX T),
          ((ε p*jacobiSym (x-t p) p : ℤ) : ℝ))/(negativeIntegerWindow d.B (parameterX T)).card ≤ -δ/4) →
      False := by
  classical
  obtain ⟨η,hη,hηu,hcollision⟩ := eventually_no_large_canonical_kernel_roots
  obtain ⟨cA,hcA,hpopulations⟩ := eventually_actual_biased_populations d c δ hc hδ
  have hηsmall : η ≤ 1/10 := by linarith
  have hηten : 0 < η/10 := by positivity
  have hcollisionT := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp parameterX_tendsto).eventually hcollision
  filter_upwards [hpopulations,
    actual_affine_kernel_image_card_eventually c (δ/8) (η/10) hc (by positivity) hηten,
    eventually_actual_numericKernel_populations cA η hcA hη hηsmall,
    eventually_commonCenter_multiplier_rpow (η/10) hηten,
    hcollisionT, parameterX_tendsto.eventually_ge_atTop 1]
    with T hpopulation hcount hroots hmult hcollision hX
  intro Z hZl hZu P hP ho hband hJ ε t hbias
  obtain ⟨h,m,P₀,e,A₀,D₀,hm,hmcap,_hmZ,hcop,hhcap,hP₀,hcut,hpower,he,
    hA,hD,hAmass,hDmass,hbias₀,hAdiam,hDdiam,hcross⟩ :=
    hpopulation Z hZl hZu P hP ho hband hJ ε t hbias
  have hJupper : P.card ≤ 2*Z := by
    have hs : P ⊆ Finset.Icc 1 (2*Z) := fun p hp =>
      Finset.mem_Icc.mpr ⟨(hP p hp).pos,(hband p hp).2⟩
    simpa using Finset.card_le_card hs
  have hsubset : A₀ ∪ D₀ ⊆ positiveIntegerWindow d.A (parameterX T) ∪
      negativeIntegerWindow d.B (parameterX T) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (hA hx)
    · exact Finset.mem_union_right _ (hD hx)
  have hK := hcount Z P.card P₀ hZl hZu hJ hJupper hcut hpower
    (fun p hp => hP p (hP₀ hp)) (fun p hp => ho p (hP₀ hp))
    (fun p hp => (hband p (hP₀ hp)).1) (fun p hp => (hband p (hP₀ hp)).2)
    e (fun p hp => (he p hp).symm) d.A d.B (A₀ ∪ D₀) hsubset m h hm hmcap hhcap
    (fun x hx => (hbias₀ x hx).1)
  have hKA : ((canonicalKernelImage A₀ m h).card : ℝ) ≤ (parameterX T : ℝ)^(η/10) := by
    apply le_trans _ hK
    exact Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image Finset.subset_union_left))
  have hKD : ((canonicalKernelImage D₀ m h).card : ℝ) ≤ (parameterX T : ℝ)^(η/10) := by
    apply le_trans _ hK
    exact Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image Finset.subset_union_right))
  have hmX : (m : ℝ) ≤ (parameterX T : ℝ)^(η/10) :=
    (Nat.cast_le.mpr hmcap).trans (hmult Z hZl hZu)
  obtain ⟨u,_hu,hup,huX,_husf,_hUr,hUc,_hUdiam⟩ := hroots A₀ m h hm hmX hcop
    (fun x hx => (hbias₀ x (Finset.mem_union_left _ hx)).2) hAdiam hAmass hKA
  obtain ⟨v,_hv,hvp,hvX,_hvsf,_hVr,hVc,_hVdiam⟩ := hroots D₀ m h hm hmX hcop
    (fun x hx => (hbias₀ x (Finset.mem_union_right _ hx)).2) hDdiam hDmass hKD
  have hu : u ≠ 0 := by exact_mod_cast (abs_pos.mp hup)
  have hv : v ≠ 0 := by exact_mod_cast (abs_pos.mp hvp)
  have hmη : (m : ℝ) ≤ (parameterX T : ℝ)^η := hmX.trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX) (by linarith : η/10 ≤ η))
  exact hcollision η hη.le le_rfl m hm hmη h u v hu hv huX hvX A₀ D₀
    (fun x hx y hy => (hcross x hx y hy).1)
    (fun x hx y hy => (hcross x hx y hy).2) hAdiam hDdiam hUc hVc

end Ostmann.QuadraticCenter

end

end OAI
