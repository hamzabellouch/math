import OAI.Analysis.IrrationalRotation.Sampling.SamplingCylinderWeak

namespace OAI

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology

namespace Invariant233.SamplingWeak

theorem tendsto_finiteMeasure_of_piSystem
    {X J : Type*} [Nonempty X] [MeasurableSpace X]
    [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
    {S : Set (Set X)} (hS : IsPiSystem S)
    {μ : J → FiniteMeasure X} {ν : FiniteMeasure X}
    {l : Filter J} [l.IsCountablyGenerated]
    (hmeas : ∀ s ∈ S, MeasurableSet s)
    (hsmall : ∀ u : Set X, IsOpen u → ∀ x ∈ u,
      ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u)
    (hmass : Tendsto (fun j => (μ j).mass) l (𝓝 ν.mass))
    (hconv : ∀ s ∈ S, Tendsto (fun j => μ j s) l (𝓝 (ν s))) :
    Tendsto μ l (𝓝 ν) := by
  exact SamplingCylinderWeak.tendsto_finiteMeasure_of_piSystem hS hmeas hsmall hmass hconv

abbrev rationalCylinder {ι : Type*} (F : Finset (ι × ℚ × ℚ)) : Set (ι → ℝ) :=
  SamplingCylinderWeak.cylinder F

@[simp] theorem rationalCylinder_empty {ι : Type*} :
    rationalCylinder (∅ : Finset (ι × ℚ × ℚ)) = Set.univ := by
  exact SamplingCylinderWeak.cylinder_empty

@[simp] theorem rationalCylinder_union {ι : Type*} [DecidableEq ι]
    (F G : Finset (ι × ℚ × ℚ)) :
    rationalCylinder (F ∪ G) = rationalCylinder F ∩ rationalCylinder G := by
  exact SamplingCylinderWeak.cylinder_union F G

theorem rationalCylinder_isOpen {ι : Type*} (F : Finset (ι × ℚ × ℚ)) :
    IsOpen (rationalCylinder F) := by
  exact SamplingCylinderWeak.cylinder_isOpen F

theorem rationalCylinder_isPiSystem (ι : Type*) :
    IsPiSystem (Set.range (rationalCylinder (ι := ι))) := by
  exact SamplingCylinderWeak.cylinder_piSystem

theorem rationalCylinder_isBasis (ι : Type*) :
    IsTopologicalBasis (Set.range (rationalCylinder (ι := ι))) := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨F, rfl⟩
    exact rationalCylinder_isOpen F
  · intro x u hx hu
    obtain ⟨F, hF, hFu⟩ := SamplingCylinderWeak.exists_cylinder_nhds_subset u hu x hx
    exact ⟨rationalCylinder F, ⟨F, rfl⟩, mem_of_mem_nhds hF, hFu⟩

theorem rationalCylinder_normal_form {ι : Type*} (F : Finset (ι × ℚ × ℚ)) :
    ∃ (D : Finset ι) (a b : ι → ℚ),
      rationalCylinder F = {x | ∀ i ∈ D, (a i : ℝ) < x i ∧ x i < (b i : ℝ)} := by
  classical
  let D : Finset ι := F.image Prod.fst
  have hinterval (i : D) : ∃ a b : ℚ, ∀ r : ℝ,
      (∀ p ∈ F, p.1 = i.val → (p.2.1 : ℝ) < r ∧ r < (p.2.2 : ℝ)) ↔
        (a : ℝ) < r ∧ r < (b : ℝ) := by
    let G := F.filter (fun p => p.1 = i.val)
    have hG : G.Nonempty := by
      obtain ⟨p, hp, hpi⟩ := Finset.mem_image.mp i.property
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpi⟩⟩
    obtain ⟨p, hp, hsup⟩ := Finset.exists_mem_eq_sup' hG (fun p => (p.2.1 : ℝ))
    obtain ⟨q, hq, hinf⟩ := Finset.exists_mem_eq_inf' hG (fun p => (p.2.2 : ℝ))
    refine ⟨p.2.1, q.2.2, fun r => ?_⟩
    rw [← hsup, ← hinf, Finset.sup'_lt_iff, Finset.lt_inf'_iff]
    constructor
    · intro h
      exact ⟨fun p hp => (h p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2).1,
        fun p hp => (h p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2).2⟩
    · rintro ⟨hl, hu⟩ p hp hpi
      have hpg : p ∈ G := Finset.mem_filter.mpr ⟨hp, hpi⟩
      exact ⟨hl p hpg, hu p hpg⟩
  choose a b hab using hinterval
  let a' : ι → ℚ := fun i => if hi : i ∈ D then a ⟨i, hi⟩ else 0
  let b' : ι → ℚ := fun i => if hi : i ∈ D then b ⟨i, hi⟩ else 0
  refine ⟨D, a', b', ?_⟩
  ext x
  constructor
  · intro hx i hi
    simp only [a', b', dite_eq_left hi]
    apply (hab ⟨i, hi⟩ (x i)).mp
    intro p hp hpi
    simpa only [hpi] using hx p hp
  · intro hx p hp
    have hi : p.1 ∈ D := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hxi := hx p.1 hi
    simp only [a', b', dite_eq_left hi] at hxi
    exact (hab ⟨p.1, hi⟩ (x p.1)).mpr hxi p hp rfl

theorem tendsto_of_rationalCylinder
    {ι J : Type*} [Countable ι]
    {μ : J → FiniteMeasure (ι → ℝ)} {ν : FiniteMeasure (ι → ℝ)}
    {l : Filter J} [l.IsCountablyGenerated]
    (h : ∀ F : Finset (ι × ℚ × ℚ),
      Tendsto (fun j => μ j (rationalCylinder F)) l (𝓝 (ν (rationalCylinder F)))) :
    Tendsto μ l (𝓝 ν) := by
  exact SamplingCylinderWeak.tendsto_finiteMeasure_of_cylinders h

end Invariant233.SamplingWeak

end

end OAI
