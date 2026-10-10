import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

def IsingSpin.flip : IsingSpin → IsingSpin
  | .neg => .pos
  | .pos => .neg

@[simp] theorem IsingSpin.flip_flip (s : IsingSpin) : s.flip.flip = s := by
  cases s <;> rfl

theorem IsingSpin.flip_injective : Function.Injective IsingSpin.flip :=
  Function.LeftInverse.injective IsingSpin.flip_flip

@[simp] theorem IsingSpin.flip_eq_flip (s t : IsingSpin) :
    s.flip = t.flip ↔ s = t := IsingSpin.flip_injective.eq_iff

@[simp] theorem IsingSpin.flip_eq_iff (s t : IsingSpin) :
    s.flip = t ↔ s = t.flip := by
  cases s <;> cases t <;> simp [IsingSpin.flip]

theorem IsingSpin.measurable_flip : Measurable IsingSpin.flip := by
  intro s hs
  trivial

def flipConfig {ι : Type*} (x : ι → IsingSpin) : ι → IsingSpin :=
  fun v => (x v).flip

@[simp] theorem flipConfig_apply {ι : Type*} (x : ι → IsingSpin) (v : ι) :
    flipConfig x v = (x v).flip := rfl

@[simp] theorem flipConfig_flipConfig {ι : Type*} (x : ι → IsingSpin) :
    flipConfig (flipConfig x) = x := by
  funext v
  exact IsingSpin.flip_flip (x v)

theorem measurable_flipConfig {ι : Type*} :
    Measurable (flipConfig : (ι → IsingSpin) → (ι → IsingSpin)) := by
  exact Measurable.of_eval (fun vertex =>
    IsingSpin.measurable_flip.comp (measurable_pi_apply vertex))

def flipConfigMeasurableEquiv (ι : Type*) : (ι → IsingSpin) ≃ᵐ (ι → IsingSpin) where
  toFun := flipConfig
  invFun := flipConfig
  left_inv := flipConfig_flipConfig
  right_inv := flipConfig_flipConfig
  measurable_toFun := measurable_flipConfig
  measurable_invFun := measurable_flipConfig

theorem integral_eq_zero_of_flipConfig_odd {ι : Type*}
    {mu : Measure (ι → IsingSpin)} (hmu : mu.map flipConfig = mu)
    (f : (ι → IsingSpin) → ℝ) (hf : ∀ x, f (flipConfig x) = -f x) :
    ∫ x, f x ∂mu = 0 := by
  have h := integral_map_equiv (μ := mu) (flipConfigMeasurableEquiv ι) f
  change (∫ x, f x ∂mu.map flipConfig) = ∫ x, f (flipConfig x) ∂mu at h
  rw [hmu] at h
  simp only [hf, integral_neg] at h
  linarith

@[simp] theorem flipConfig_preimage_spin {ι : Type*} (v : ι) (s : IsingSpin) :
    flipConfig ⁻¹' {x : ι → IsingSpin | x v = s} =
      {x : ι → IsingSpin | x v = s.flip} := by
  ext x
  simp [flipConfig]

theorem measurableSet_spin_event {ι : Type*} (v : ι) (s : IsingSpin) :
    MeasurableSet {x : ι → IsingSpin | x v = s} :=
  (show MeasurableSet ({s} : Set IsingSpin) from trivial).preimage (measurable_pi_apply v)

theorem measure_even_event_inter_spin {ι : Type*} {mu : Measure (ι → IsingSpin)}
    (hmu : mu.map flipConfig = mu) {A : Set (ι → IsingSpin)}
    (hA : MeasurableSet A) (hAflip : flipConfig ⁻¹' A = A) (v : ι) (s : IsingSpin) :
    mu (A ∩ {x | x v = s}) = mu (A ∩ {x | x v = s.flip}) := by
  calc
    mu (A ∩ {x | x v = s}) = (mu.map flipConfig) (A ∩ {x | x v = s}) := by rw [hmu]
    _ = mu (A ∩ {x | x v = s.flip}) := by
      rw [Measure.map_apply measurable_flipConfig (hA.inter (measurableSet_spin_event v s)),
        Set.preimage_inter, hAflip, flipConfig_preimage_spin]

theorem twice_measure_even_event_inter_spin {ι : Type*} {mu : Measure (ι → IsingSpin)}
    (hmu : mu.map flipConfig = mu) {A : Set (ι → IsingSpin)}
    (hA : MeasurableSet A) (hAflip : flipConfig ⁻¹' A = A) (v : ι) (s : IsingSpin) :
    2 * mu (A ∩ {x | x v = s}) = mu A := by
  have hunion : A = (A ∩ {x | x v = s}) ∪ (A ∩ {x | x v = s.flip}) := by
    ext x
    cases hs : x v <;> cases s <;> simp [hs, IsingSpin.flip]
  have hdisjoint : Disjoint (A ∩ {x | x v = s}) (A ∩ {x | x v = s.flip}) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have heq : s = s.flip := hx.2.symm.trans hy.2
    cases s <;> cases heq
  calc
    2 * mu (A ∩ {x | x v = s}) =
        mu (A ∩ {x | x v = s}) + mu (A ∩ {x | x v = s.flip}) := by
      rw [← measure_even_event_inter_spin hmu hA hAflip v s, two_mul]
    _ = mu A := by
      rw [← measure_union hdisjoint (hA.inter (measurableSet_spin_event v s.flip)), ← hunion]

theorem setIntegral_spin_eq_half_of_flipConfig_even {ι : Type*}
    {mu : Measure (ι → IsingSpin)} (hmu : mu.map flipConfig = mu)
    {f : (ι → IsingSpin) → ℝ} (hf : Integrable f mu)
    (heven : ∀ x, f (flipConfig x) = f x) (v : ι) (s : IsingSpin) :
    ∫ x in {x | x v = s}, f x ∂mu = (1 / 2 : ℝ) * ∫ x, f x ∂mu := by
  classical
  let A : Set (ι → IsingSpin) := {x | x v = s}
  have hA : MeasurableSet A := measurableSet_spin_event v s
  have htransport := integral_map_equiv (μ := mu) (flipConfigMeasurableEquiv ι) (A.indicator f)
  change (∫ x, A.indicator f x ∂mu.map flipConfig) =
    ∫ x, A.indicator f (flipConfig x) ∂mu at htransport
  rw [hmu] at htransport
  have hindicator : (fun x => A.indicator f (flipConfig x)) = Aᶜ.indicator f := by
    funext x
    cases hx : x v <;> cases s <;>
      simp [A, Set.indicator, flipConfig, hx, IsingSpin.flip, heven x]
  rw [hindicator, integral_indicator hA, integral_indicator hA.compl] at htransport
  have hsum := integral_add_compl hA hf
  change (∫ x in A, f x ∂mu) = (1 / 2 : ℝ) * ∫ x, f x ∂mu
  linarith

@[simp] theorem freeCylinderWeight_flipConfig {d : ℕ} (theta : ℝ)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta D (flipConfig eta) = freeCylinderWeight theta D eta := by
  simp [freeCylinderWeight, flipConfig]

theorem HasFreeIsingLaw.map_flipConfig {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu) :
    HasFreeIsingLaw theta (mu.map flipConfig) := by
  intro D hD eta
  have hmeas : MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} := by
    simp only [Set.ofPred_forall]
    apply D.measurableSet_biInter
    intro v hv
    exact (show MeasurableSet ({eta v} : Set IsingSpin) from trivial).preimage
      (measurable_pi_apply v)
  rw [Measure.map_apply measurable_flipConfig hmeas]
  have hpre : flipConfig ⁻¹' {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} =
      {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = flipConfig eta v} := by
    ext x
    simp [flipConfig]
  rw [hpre, hmu D hD (flipConfig eta), freeCylinderWeight_flipConfig]

end Problem367

end

end OAI
