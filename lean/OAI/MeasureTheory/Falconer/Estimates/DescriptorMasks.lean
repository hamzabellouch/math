import OAI.MeasureTheory.Falconer.Estimates.DescriptorTests
import OAI.MeasureTheory.Falconer.Estimates.AnchoredBufferedMasks
import OAI.MeasureTheory.Falconer.Angular.SphereNormalization

namespace OAI

/-! # Actual anchored masks and retained pair tests in every dimension

The angular set at an anchor is tested against the full conditional law.
Masks use finite spherical nets at one eighth of the manuscript's buffer
radius. Their construction is independent of the number of anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
variable {d : ℕ}

noncomputable def descriptorMaskRadius (N : ℕ) (σ : ℝ) (b : PolicyDescriptor) : ℝ :=
  angularTestRadius N σ (descriptorLength b)/8

theorem descriptorMaskRadius_pos (N : ℕ) (σ : ℝ) (b : PolicyDescriptor) :
    0 < descriptorMaskRadius N σ b := by
  exact div_pos (angularTestRadius_pos N σ _) (by norm_num)

noncomputable def descriptorMask (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) : Space d → Sphere d → ℝ :=
  anchoredBufferedMask Q (descriptorAnchor b) (descriptorMaskRadius N σ b)
    (descriptorMaskRadius_pos N σ b) S
    (fun p => descriptorGoodDirections Q ρ m N σ J (i+1) p b)

def descriptorEndpointGood (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor) :
    Set (Space d × Sphere d) :=
  {z | ∀ p ∈ cubePaths d (descriptorAnchor b), z.1 ∈ (Q.descendant p).carrier →
    z.2 ∈ descriptorGoodDirections Q ρ m N σ J i p b}

theorem descriptorEndpointGood_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) :
    MeasurableSet (descriptorEndpointGood Q ρ m N σ J i b) := by
  classical
  have hm : MeasurableSet (⋂ p ∈ cubePaths d (descriptorAnchor b),
      {z : Space d × Sphere d | z.1 ∈ (Q.descendant p).carrier →
        z.2 ∈ descriptorGoodDirections Q ρ m N σ J i p b}) := by
    apply Finset.measurableSet_biInter
    intro p _
    convert ((Q.descendant p).measurable.preimage measurable_fst).compl.union
      ((descriptorGoodDirections_measurable Q ρ m N σ J i p b).preimage measurable_snd) using 1
    ext z
    simp only [mem_ofPred_eq,mem_union,mem_compl_iff,mem_preimage,imp_iff_not_or]
  convert hm using 1
  ext z
  simp [descriptorEndpointGood]

theorem descriptorEndpointGood_on_cell (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (p : List (Fin d → Bool)) (hp : p.length = descriptorAnchor b)
    {x : Space d} (hx : x ∈ (Q.descendant p).carrier) (w : Sphere d) :
    (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b ↔
      w ∈ descriptorGoodDirections Q ρ m N σ J i p b := by
  constructor
  · exact fun h => h p ((mem_cubePaths _ _ _).mpr hp) hx
  · intro hw q hq hxq
    have hqp : q = p := by
      by_contra hn
      exact Set.disjoint_left.mp
        (Q.descendants_disjoint (((mem_cubePaths _ _ _).mp hq).trans hp.symm) hn) hxq hx
    simpa only [hqp] using hw

theorem descriptorMask_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) : Measurable (Function.uncurry (descriptorMask Q ρ m N σ J i b S)) :=
  anchoredBufferedMask_measurable Q _ (descriptorMaskRadius_pos N σ b) S _

theorem descriptorMask_bounds (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ descriptorMaskRadius N σ b/2)
    (x : Space d) (w : Sphere d) :
    0 ≤ descriptorMask Q ρ m N σ J i b S x w ∧
      descriptorMask Q ρ m N σ J i b S x w ≤ 1 :=
  anchoredBufferedMask_bounds Q _ (descriptorMaskRadius_pos N σ b) S hcover _ x w

theorem descriptorMask_support (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ descriptorMaskRadius N σ b/2)
    {x : Space d} (w : Sphere d)
    (hw : descriptorMask Q ρ m N σ J i b S x w ≠ 0) :
    (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  intro p hp hx
  exact anchoredBufferedMask_support Q (descriptorMaskRadius_pos N σ b) S hcover _ p
    ((mem_cubePaths _ _ _).mp hp) hx w hw

theorem uniform_descriptorMask_core {σ : ℝ} (hσ : 0 < σ) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
        (b : PolicyDescriptor), descriptorValid N b →
      ∀ (S : Finset (Sphere d)),
      (∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ descriptorMaskRadius N σ b/2) →
      ∀ (i : ℕ) (x : Space d), x ∈ Q.carrier → ∀ w : Sphere d,
      (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b →
      descriptorMask Q ρ m N σ J i b S x w = 1 := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptor_direction_buffer (d := d) hσ hJ (C := 1) (by norm_num)
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ m b hb S hcover i x hx w hw
  obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth (descriptorAnchor b) hx
  apply anchoredBufferedMask_core Q (descriptorMaskRadius_pos N σ b) S hcover _ p
    ((mem_cubePaths _ _ _).mp hp) hxp w
  intro z hz
  apply h₀ N hN Q hQ ρ m b hb p ((mem_cubePaths _ _ _).mp hp) i w z _ (hw p hp hxp)
  have hr := angularTestRadius_pos N σ (descriptorLength b)
  dsimp only [descriptorMaskRadius] at hz
  rw [dist_comm] at hz
  linarith

theorem uniform_descriptorEndpointGood_buffer {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
        (b : PolicyDescriptor), descriptorValid N b →
      ∀ (i : ℕ) (x : Space d) (w u : Sphere d),
        dist w u ≤ angularTestRadius N σ (descriptorLength b) →
        (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b →
        (x,u) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptor_direction_buffer (d := d) hσ hJ (C := 1) (by norm_num)
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ m b hb i x w u hwu hw P hP hx
  apply h₀ N hN Q hQ ρ m b hb P ((mem_cubePaths _ _ _).mp hP) i w u
  · simpa only [one_mul] using hwu
  · exact hw P hP hx

noncomputable def descriptorPairTests (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PolicyDescriptor) : Set (Space d × Space d) :=
  {z | ∀ b ∈ B,
    (z.1,normalizeToSphere w₀ (z.1-z.2)) ∈ descriptorEndpointGood Q ρ m N σ J i b ∧
    (z.2,normalizeToSphere w₀ (z.1-z.2)) ∈ descriptorEndpointGood Q ρ m N σ J i b}

theorem descriptorPairTests_measurable (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor) :
    MeasurableSet (descriptorPairTests w₀ Q ρ m N σ J i B) := by
  classical
  have hm := (normalizeToSphere_measurable w₀).comp (measurable_fst.sub measurable_snd)
  have hset : MeasurableSet (⋂ b ∈ B, {z : Space d × Space d |
      (z.1,normalizeToSphere w₀ (z.1-z.2)) ∈ descriptorEndpointGood Q ρ m N σ J i b ∧
      (z.2,normalizeToSphere w₀ (z.1-z.2)) ∈ descriptorEndpointGood Q ρ m N σ J i b}) := by
    apply Finset.measurableSet_biInter
    intro b _
    exact ((descriptorEndpointGood_measurable Q ρ m N σ J i b).preimage
      (measurable_fst.prodMk hm)).inter
        ((descriptorEndpointGood_measurable Q ρ m N σ J i b).preimage
          (measurable_snd.prodMk hm))
  convert hset using 1
  ext z
  simp [descriptorPairTests]

theorem descriptorPairTests_mono (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    {A B : Finset PolicyDescriptor} (hAB : A ⊆ B) :
    descriptorPairTests w₀ Q ρ m N σ J i B ⊆ descriptorPairTests w₀ Q ρ m N σ J i A :=
  fun _ hz b hb => hz b (hAB hb)

end Falconer

end OAI
