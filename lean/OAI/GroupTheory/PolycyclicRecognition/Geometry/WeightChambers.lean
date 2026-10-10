import OAI.GroupTheory.PolycyclicRecognition.Algebra.ActiveRayConstraints
import OAI.GroupTheory.PolycyclicRecognition.Geometry.GenericWeightDirections

namespace OAI

/-! # Incident weight chambers determine an extreme ray

Both signs of every active hyperplane occur among genuine open chambers.
Intersecting their closures therefore imposes the active equations; actual
extremality, rather than a rank assumption, identifies the resulting ray.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Finite I]

def orientedWeight (α : I → W →L[ℝ] ℝ) (σ : I → Bool) (i : I) : W →L[ℝ] ℝ :=
  if σ i then α i else -α i

def weightChamber (α : I → W →L[ℝ] ℝ) (σ : I → Bool) : Set W :=
  {w | ∀ i, 0 < orientedWeight α σ i w}

def closedWeightChamber (α : I → W →L[ℝ] ℝ) (σ : I → Bool) : Set W :=
  linearInequalityCone (orientedWeight α σ)

def incidentWeightChamber (α : I → W →L[ℝ] ℝ) (w : W) (σ : I → Bool) : Prop :=
  (weightChamber α σ).Nonempty ∧ w ∈ closedWeightChamber α σ

def weightSigns (α : I → W →L[ℝ] ℝ) (w : W) (i : I) : Bool := decide (0 < α i w)

omit [FiniteDimensional ℝ W] in
theorem exists_positive_chamber_perturbation (α : I → W →L[ℝ] ℝ)
    (σ : I → Bool) {w v : W} (hw : w ∈ closedWeightChamber α σ)
    (hv : ∀ i, orientedWeight α σ i w = 0 → 0 < orientedWeight α σ i v) :
    ∃ t : ℝ, 0 < t ∧ w + t • v ∈ weightChamber α σ := by
  have hevent (i : I) : ∀ᶠ t : ℝ in 𝓝 0,
      0 < t → 0 < orientedWeight α σ i (w + t • v) := by
    by_cases hi : orientedWeight α σ i w = 0
    · exact Eventually.of_forall (fun t ht => by
        simpa only [map_add, map_smul, hi, zero_add, smul_eq_mul]
          using mul_pos ht (hv i hi))
    · have hp : 0 < orientedWeight α σ i w :=
        lt_of_le_of_ne (hw i) (Ne.symm hi)
      have hc : Continuous (fun t : ℝ => orientedWeight α σ i (w + t • v)) := by
        fun_prop
      have h0 : 0 < orientedWeight α σ i (w + (0 : ℝ) • v) := by simpa using hp
      filter_upwards [(isOpen_lt continuous_const hc).mem_nhds h0] with t ht
      exact fun _ => ht
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp (eventually_all.mpr hevent)
  have hsmall : dist (ε / 2) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact ⟨ε / 2, half_pos hε, fun i => he hsmall i (half_pos hε)⟩

omit [FiniteDimensional ℝ W] in
/-- Break ties at the active hyperplanes using a generic direction. -/
theorem exists_incident_chamber_of_generic (α : I → W →L[ℝ] ℝ) (w : W)
    {v : W} (hv : v ∈ genericWeightDirections α) :
    ∃ σ : I → Bool, incidentWeightChamber α w σ ∧
      ∀ i, α i w = 0 → σ i = weightSigns α v i := by
  classical
  let σ : I → Bool := fun i => if α i w = 0 then weightSigns α v i else weightSigns α w i
  have hw : w ∈ closedWeightChamber α σ := by
    intro i
    by_cases hi : α i w = 0
    · cases hs : σ i <;> simp [orientedWeight, hs, hi]
    · by_cases hp : 0 < α i w
      · simpa [orientedWeight, σ, hi, weightSigns, hp] using hp.le
      · simpa [orientedWeight, σ, hi, weightSigns, hp] using neg_nonneg.mpr (le_of_not_gt hp)
  have hv' : ∀ i, orientedWeight α σ i w = 0 → 0 < orientedWeight α σ i v := by
    intro i hi
    have hw0 : α i w = 0 := by
      by_cases hs : σ i = true
      · simpa [orientedWeight, hs] using hi
      · simpa [orientedWeight, hs] using hi
    by_cases hp : 0 < α i v
    · simp [orientedWeight, σ, hw0, weightSigns, hp]
    · have hn : α i v < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hv i)
      simpa [orientedWeight, σ, hw0, weightSigns, hp] using neg_pos.mpr hn
  obtain ⟨t, _, ht⟩ := exists_positive_chamber_perturbation α σ hw hv'
  exact ⟨σ, ⟨⟨w + t • v, ht⟩, hw⟩, fun i hi => by simp [σ, hi]⟩

theorem exists_incident_chamber_positive (α : I → W →L[ℝ] ℝ)
    (hα : ∀ i, α i ≠ 0) (w : W) (i : I) (hi : α i w = 0) :
    ∃ σ : I → Bool, incidentWeightChamber α w σ ∧ σ i = true := by
  obtain ⟨v, hv, hp⟩ := exists_generic_weight_positive α hα i
  obtain ⟨σ, hs, he⟩ := exists_incident_chamber_of_generic α w hv
  exact ⟨σ, hs, by simpa [weightSigns, hp] using he i hi⟩

theorem exists_incident_chamber_negative (α : I → W →L[ℝ] ℝ)
    (hα : ∀ i, α i ≠ 0) (w : W) (i : I) (hi : α i w = 0) :
    ∃ σ : I → Bool, incidentWeightChamber α w σ ∧ σ i = false := by
  obtain ⟨v, hv, hp⟩ := exists_generic_weight_negative α hα i
  obtain ⟨σ, hs, he⟩ := exists_incident_chamber_of_generic α w hv
  refine ⟨σ, hs, ?_⟩
  rw [he i hi]
  simp [weightSigns, not_lt.mpr hp.le]

theorem incident_chamber_intersection_eq_ray (α : I → W →L[ℝ] ℝ)
    (hα : ∀ i, α i ≠ 0)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0)
    {w : W} (σ₀ : I → Bool) (hσ₀ : (weightChamber α σ₀).Nonempty)
    (hExt : IsExtreme ℝ (closedWeightChamber α σ₀) (nonnegativeRay w)) :
    {x | ∀ σ, incidentWeightChamber α w σ → x ∈ closedWeightChamber α σ} =
      nonnegativeRay w := by
  ext x
  constructor
  · intro hx
    have hw : w ∈ closedWeightChamber α σ₀ := hExt.subset ⟨1, zero_le_one, by simp⟩
    have hsep' : ∀ y : W, (∀ i, orientedWeight α σ₀ i y = 0) → y = 0 := by
      intro y hy
      apply hsep y
      intro i
      have hi := hy i
      cases hs : σ₀ i <;> simpa [orientedWeight, hs] using hi
    apply mem_ray_of_active_constraints (orientedWeight α σ₀) hsep' hExt
      (hx σ₀ ⟨hσ₀, hw⟩)
    intro i hi
    have hw0 : α i w = 0 := by
      cases hs : σ₀ i <;> simpa [orientedWeight, hs] using hi
    obtain ⟨σp, hσp, hp⟩ := exists_incident_chamber_positive α hα w i hw0
    obtain ⟨σm, hσm, hm⟩ := exists_incident_chamber_negative α hα w i hw0
    have hpos : 0 ≤ α i x := by
      simpa [orientedWeight, hp] using hx σp hσp i
    have hneg : α i x ≤ 0 := by
      simpa [orientedWeight, hm] using hx σm hσm i
    have hzero := le_antisymm hneg hpos
    cases hs : σ₀ i <;> simp [orientedWeight, hs, hzero]
  · rintro ⟨r, hr, rfl⟩ σ hσ i
    simpa only [map_smul, smul_eq_mul] using mul_nonneg hr (hσ.2 i)

end PolycyclicRecognition

end

end OAI
