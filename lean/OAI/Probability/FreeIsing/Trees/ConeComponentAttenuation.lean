import OAI.Probability.FreeIsing.Energy.RelabeledComponentAttenuation
import OAI.Probability.FreeIsing.Trees.NoisyPathLocality

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.PathSideBranches

theorem range_relabel_componentIndexVertex_eq_cone
    {d : ℕ} (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1) :
    Set.range (fun i => g.toEquiv.symm (componentIndexVertex (c := c) i)) =
      Set.range (Subtype.val : cone r → TreeVertex d) := by
  rw [Subtype.range_coe_subtype]
  ext u
  constructor
  · rintro ⟨i, rfl⟩
    apply (hgeo _).mpr
    simp only [Equiv.apply_symm_apply]
    change [c] <+: c :: i.2.1
    simp
  · intro hu
    have hp := (hgeo u).mp hu
    have hm : g.toEquiv u ∈ Set.range (componentIndexVertex (c := c)) := by
      apply mem_range_componentIndexVertex.mpr
      obtain ⟨w, hw⟩ := hp
      exact ⟨w, by simpa using hw.symm⟩
    obtain ⟨i, hi⟩ := hm
    refine ⟨i, ?_⟩
    change g.toEquiv.symm (componentIndexVertex i) = u
    rw [hi, Equiv.symm_apply_apply]

end Problem367.PathSideBranches

namespace Problem367.ComponentSignalAttenuation

open PlantedSymmetry PathSideBranches

theorem condExp_attenuation_le_critical_cone_complement
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (r : TreeVertex d) (hr : r.1 ≠ [])
    {B : Type*} [mB : MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (G : (({u : TreeVertex d // u ∉ cone r} → IsingSpin) ×
      ({u : TreeVertex d // u ∉ cone r} → ℝ)) → B) (hG : Measurable G)
    (shift : B → ℝ) (hs : Measurable shift) :
    let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
    let X := G ∘ noisyRegionArray (cone r)ᶜ
    let Q := selectedPosterior P (fun s z => (t : ℝ) * spinSign s + z)
      (Subtype.val : cone r → TreeVertex d) r
    ∀ᵐ w ∂P,
      (P[fun v => responseAttenuation theta
        (shift (X v) + statisticMessage theta (Q v)) ^ 2 | mB.comap X]) w ≤
        1 - lossCoefficient theta * min (Real.sqrt (t : ℝ)) 1 := by
  obtain ⟨g, c, hp, hc, hgeo⟩ := exists_reroot_cone r hr
  have hroot : g.toEquiv.symm (RootedBroadcast.branchRoot c) = r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hc]
    rfl
  have hchannelField := selectedObservationField_eq_of_range_eq
    (fun s z => (t : ℝ) * spinSign s + z)
    (range_relabel_componentIndexVertex_eq_cone g r c hgeo)
  have hX : ((G ∘ decodeConeComplement (A := ℝ) g r c hgeo) ∘ noisyRootOtherArray c) ∘
      Prod.map (relabel g) (relabel g) = G ∘ noisyRegionArray (cone r)ᶜ := by
    funext z
    exact congrArg G (decodeConeComplement_relabel g r c hgeo z)
  have h := condExp_attenuation_le_critical_relabel_root_others
    hμ hθ0 hθ1 c hcritical ht g (G ∘ decodeConeComplement g r c hgeo)
    (hG.comp (measurable_decodeConeComplement g r c hgeo)) shift hs
  dsimp only at h ⊢
  simpa only [hX, hroot, selectedPosterior, hchannelField] using h

theorem condExp_attenuation_le_critical_cone_of_measurable
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (r : TreeVertex d) (hr : r.1 ≠ [])
    {B : Type*} [mB : MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (X : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) → B)
    (hX : Measurable[noisyRegionSigma (A := ℝ) (cone r)ᶜ] X)
    (shift : B → ℝ) (hs : Measurable shift) :
    let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
    let Q := selectedPosterior P (fun s z => (t : ℝ) * spinSign s + z)
      (Subtype.val : cone r → TreeVertex d) r
    ∀ᵐ w ∂P,
      (P[fun v => responseAttenuation theta
        (shift (X v) + statisticMessage theta (Q v)) ^ 2 | mB.comap X]) w ≤
        1 - lossCoefficient theta * min (Real.sqrt (t : ℝ)) 1 := by
  obtain ⟨G, hG, rfl⟩ := hX.exists_eq_measurable_comp
  exact condExp_attenuation_le_critical_cone_complement
    hμ hθ0 hθ1 hcritical ht r hr G hG shift hs

end Problem367.ComponentSignalAttenuation

end

end OAI
