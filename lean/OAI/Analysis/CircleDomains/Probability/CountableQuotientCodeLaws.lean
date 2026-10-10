import OAI.Analysis.CircleDomains.Probability.CountableDiffuseCodeLaws
import OAI.Analysis.CircleDomains.Sobolev.UniformSphericalBallArea

namespace OAI

/-! The actual component quotient supplies the common collar basis and
uniform area constant in the countability theorem. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem countable_quotient_code_laws {I : Type*} [LinearOrder I]
    (hcross : UnitDiskAlternatingContinua)
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G U B E : Set Sphere) (hG : IsOpen G) (hU : IsOpen U)
    (hdisj : Disjoint U B) (hBU : Bᶜ ⊆ U) (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hE : IsClosed E) (hEU : E ⊆ U)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B) (hinf : π OnePoint.infty ∉ B)
    (d : I → PathCodeData Sphere Sphere)
    (hGd : ∀ i, (d i).physicalDomain = G) (hUd : ∀ i, (d i).quotientDomain = U)
    (hBd : ∀ i, (d i).dust = B) (hEd : ∀ i, (d i).anchor = E)
    (hed : ∀ i, ∀ y : (d i).physicalDomain, ((d i).domainEquiv y).val = π y.val)
    (htarget : ∀ i, (d i).target ∈ B \ {OnePoint.infty})
    (hinj : Injective (fun i => (d i).target))
    (P : ∀ i, ProbabilityMeasure (BasePathCode (d i)))
    [∀ i, SigmaFinite (meanCodeOccupation (d i) (P i))]
    (g : I → Sphere → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
    (hocc : ∀ i, meanCodeOccupation (d i) (P i) = sphericalArea.withDensity (g i))
    (henergy : ∀ i, (∫⁻ x, g i x ^ 2 ∂sphericalArea) < ∞)
    (hhit : ∀ i, (∑' x : B, codeHitProbability (d i) (P i) x.val ^ 2) < ∞)
    (hcontacts : ∀ i j, i < j → ∃ D : Set Sphere, D.Countable ∧
      ∀ᵐ z ∂((P i : Measure (BasePathCode (d i))).prod (P j : Measure (BasePathCode (d j)))),
        range z.1.val.1 ∩ range z.2.val.1 ∩ (d i).dust ⊆ D) : Countable I := by
  obtain ⟨K, hK, hgood, hbasis⟩ := exists_countable_jordan_collars hcoarea hsard hsch
    G U B E π hπ hclosed hsurj hr hB hTD hBU hdisj hbad hE hEU hinf
  obtain ⟨W, hW, hBW, hWi⟩ := normal_exists_closure_subset hB
    (isClosed_singleton (x := π OnePoint.infty)).isOpen_compl
    (fun x hx h => hinf (h ▸ hx))
  let K' := {k | k ∈ K ∧ quotientJordanDisk k ⊆ W}
  have hK' : K'.Countable := hK.mono (fun _ h => h.1)
  have hg' : ∀ k ∈ K', frontier (quotientJordanDisk k) ⊆ U ∧
      π OnePoint.infty ∉ closure (quotientJordanDisk k) ∧ Disjoint E (quotientJordanDisk k) :=
    fun k hk => hgood k hk.1
  have hb' : ∀ p ∈ B \ {OnePoint.infty}, ∀ O : Set Sphere, IsOpen O → p ∈ O →
      ∃ k ∈ K', p ∈ quotientJordanDisk k ∧ quotientJordanDisk k ⊆ O := by
    intro p hp O hO hpO
    obtain ⟨k, hk, hpk, hsub⟩ := hbasis p hp (O ∩ W) (hO.inter hW) ⟨hpO, hBW hp.1⟩
    exact ⟨k, ⟨hk, hsub.trans inter_subset_right⟩, hpk, hsub.trans inter_subset_left⟩
  let A := π ⁻¹' W
  have hsub : closure A ⊆ π ⁻¹' closure W :=
    closure_minimal (preimage_mono subset_closure) (isClosed_closure.preimage hπ)
  have hAi : OnePoint.infty ∉ closure A := fun h => hWi (hsub h) rfl
  let a : ℕ → ℝ≥0 := fun n => ⟨1 / ((n : ℝ) + 1), by positivity⟩
  have ha (n : ℕ) : 0 < a n := by change 0 < 1 / ((n : ℝ) + 1); positivity
  have hat : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨C, hC, hball⟩ := spherical_ball_sequence_area_bound A hAi a hat
  exact countable_diffuse_code_laws hcross G U B E hG hU hdisj hBU π hπ hclosed hsurj hr
    d hGd hUd hBd hEd hed htarget hinj P g hg hocc henergy hhit hcontacts
    K' hK' hg' hb' a ha hat C hC A (fun _ hk => preimage_mono hk.2) hball

end CircleDomainRigidity

end

end OAI
