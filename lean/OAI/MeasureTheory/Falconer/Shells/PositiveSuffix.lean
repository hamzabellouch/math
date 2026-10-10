import OAI.MeasureTheory.Falconer.Estimates.SuffixScales

namespace OAI

/-! # The actual policy suffix transition for positive distance counts -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem suffix_policy_projection_mem (A : ℕ → ℝ) {N q a t : ℕ}
    (ht : t ≤ N) (hw : a+100*q < t)
    (hs : a+t < 2*PlanarFalconer.policyDepth A N q a t) :
    PolicyDescriptor.projection (PlanarFalconer.policyDepth A N q a t) t ∈
      PlanarFalconer.policyDescriptorList A N q a t := by
  apply Finset.mem_biUnion.mpr
  refine ⟨(a,t),?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,
      le_rfl,le_rfl,hw⟩
  · apply Finset.mem_union_right
    simp [hs]

theorem policy_descriptor_end_bounds (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    {b : PolicyDescriptor} (hb : b ∈ PlanarFalconer.policyDescriptorList A N q a t) :
    descriptorAnchor b ≤ t ∧ descriptorLength b ≤ t-a := by
  obtain ⟨u,v,hau,hvt,_,_,_,hleft,hright⟩ := PlanarFalconer.policyDescriptor_origin A hq hb
  omega

noncomputable def policyTestPairs (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (A : ℕ → ℝ)
    (N : ℕ) (σ : ℝ) (J i q a t : ℕ) : Set (Space d × Space d) :=
  descriptorPairTests w₀ Q ρ m N σ J i (PlanarFalconer.policyDescriptorList A N q a t)

/-- The suffix collision estimate uses the actual tested pair measures,
with a coarser policy list at the next smoothing index. -/
theorem uniform_policy_suffix_collision {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (A : ℕ → ℝ)
        (q a p t i : ℕ), 0 < q → t ≤ N → a+100*q < t →
        p = PlanarFalconer.policyDepth A N q a t → a+t < 2*p → i ≤ J →
      ∀ (w₀ : Sphere d) (X Y : List (Fin d → Bool)), X.length = a → Y.length = a →
      125*((d:ℝ)+1)*(Q.descendant X).side ≤
        ‖(Q.descendant X).center-(Q.descendant Y).center‖ →
      ((testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
          (policyTestPairs w₀ Q ρ m A N σ J i q a t)).prod
        (testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
          (policyTestPairs w₀ Q ρ m A N σ J i q a t)))
        {z : ℝ × ℝ | |z.1-z.2| ≤ (100*((d:ℝ)+1))/(2:ℝ)^t} ≤
      (((PlanarFalconer.bandOffsets (100*((d:ℝ)+1))).card : ℝ≥0∞) *
        ((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞) *
        ENNReal.ofReal ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^(
          Regularization.profileDrop m N ((d:ℝ)/2) p t+1000*((d:ℝ)+1)*σ))) *
      ((testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
          (policyTestPairs w₀ Q ρ m A N σ J (i+1) q a p)).prod
        (testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
          (policyTestPairs w₀ Q ρ m A N σ J (i+1) q a p)))
        {z : ℝ × ℝ | |z.1-z.2| ≤ (100*((d:ℝ)+1))/(2:ℝ)^p} := by
  obtain ⟨N₁,h₁⟩ := uniform_suffix_witness_width d hσ hJ
  obtain ⟨N₂,h₂⟩ := uniform_full_cell_tests_of_witness (d := d) hσ hJ
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q hQ ρ _ m A q a p t i hq htN hwide hp hapt hi w₀ X Y hX hY hsep
  have hne := PlanarFalconer.policyBlocks_nonempty hq htN hwide
  have hpi := PlanarFalconer.policyDepth_interior A hq hne
  rw [← hp] at hpi
  have hap : a ≤ p := by omega
  have hpt : p ≤ t := by omega
  have hQp : 0 < Q.side := by rw [hQ]; norm_num
  have hPX : (Q.descendant X).side = 1/(2:ℝ)^a := by rw [Q.descendant_side,hX,hQ]
  have hPY : (Q.descendant Y).side = (Q.descendant X).side := by
    rw [Q.descendant_side,Q.descendant_side,hX,hY]
  have hsmallSide : (Q.descendant X).side/(2:ℝ)^(p-a) = 1/(2:ℝ)^p := by
    rw [hPX,div_div,← pow_add,Nat.add_sub_of_le hap]
  let G := policyTestPairs w₀ Q ρ m A N σ J i q a t
  let H := policyTestPairs w₀ Q ρ m A N σ J (i+1) q a p
  let g := 100*((d:ℝ)+1)/(2:ℝ)^a
  have hg : 0 < g := by dsimp [g]; positivity
  have hpoints {x y : Space d} (hx : x ∈ (Q.descendant X).carrier)
      (hy : y ∈ (Q.descendant Y).carrier) : g ≤ ‖x-y‖ := by
    simpa only [g,hPX,div_eq_mul_inv,one_mul] using
      (Q.descendant X).separated_pairs_lower (Q.descendant Y)
        (Q.descendant_side_pos hQp X) hPY hsep hx hy
  have hlength (c : List (Fin d → Bool) × List (Fin d → Bool))
      (hc : c ∈ retainedCellPairs ρ ρ (Q.descendant X) (Q.descendant Y) (p-a) G) :
      c.1.length = p-a ∧ c.2.length = p-a := by
    obtain ⟨hc,_⟩ := Finset.mem_filter.mp hc
    exact ⟨(mem_cubePaths _ _ _).mp (Finset.mem_filter.mp (Finset.mem_product.mp hc).1).1,
      (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp (Finset.mem_product.mp hc).2).1⟩
  have hcenters (c) (hc : c ∈ retainedCellPairs ρ ρ (Q.descendant X) (Q.descendant Y) (p-a) G) :
      g ≤ ‖((Q.descendant X).descendant c.1).center-((Q.descendant Y).descendant c.2).center‖ :=
    hpoints ((Q.descendant X).descendant_subset c.1
      (((Q.descendant X).descendant c.1).center_mem
        ((Q.descendant X).descendant_side_pos (Q.descendant_side_pos hQp X) c.1)))
      ((Q.descendant Y).descendant_subset c.2
        (((Q.descendant Y).descendant c.2).center_mem
          ((Q.descendant Y).descendant_side_pos (Q.descendant_side_pos hQp Y) c.2)))
  have hproj := retained_projection_test w₀ Q ρ m N σ J i a p t hap X Y hY
    (PlanarFalconer.policyDescriptorList A N q a t)
    (by rw [hp]; exact suffix_policy_projection_mem A htN hwide (by simpa only [← hp] using hapt))
    G (fun _ h => h) (fun x hx y hy => sub_ne_zero.mp (norm_pos_iff.mp (hg.trans_le (hpoints hx hy))))
  have hchild (c) (hc : c ∈ retainedCellPairs ρ ρ (Q.descendant X) (Q.descendant Y) (p-a) G) :
      ((Q.descendant X).descendant c.1).carrier ×ˢ ((Q.descendant Y).descendant c.2).carrier ⊆ H := by
    obtain ⟨hxlen,hylen⟩ := hlength c hc
    obtain ⟨_,x,hx,y,hy,hxy⟩ := Finset.mem_filter.mp hc
    have hsub := PlanarFalconer.policyDescriptorList_mono A (N := N) (q := q) (le_refl a) hpt
    have hboth := descriptorPairTests_mono w₀ Q ρ m N σ J i hsub hxy
    have hX' : (X++c.1).length = p := by simp only [List.length_append,hX,hxlen]; omega
    have hY' : (Y++c.2).length = p := by simp only [List.length_append,hY,hylen]; omega
    have hside : (Q.descendant (X++c.1)).side = 1/(2:ℝ)^p := by rw [Q.descendant_side,hX',hQ]
    have hh := h₂ N ((le_max_right _ _).trans hN) Q hQ ρ m
      (PlanarFalconer.policyDescriptorList A N q a p)
      (fun b hb => policy_descriptor_valid A hq (hpt.trans htN) hb)
      p (X++c.1) (Y++c.2) hX' hY'
      (fun b hb => (policy_descriptor_end_bounds A hq hb).1)
      g hg (by simpa only [Q.descendant_append] using hcenters c hc)
      (by rw [hside]; exact suffix_direction_small d hap)
      (fun b hb => by
        rw [hside]
        exact suffix_direction_buffer d hσ.le N hap
          (policy_descriptor_end_bounds A hq hb).2)
      i w₀ x y (by simpa only [Q.descendant_append] using hx)
      (by simpa only [Q.descendant_append] using hy) hboth
    simpa only [Q.descendant_append, H, policyTestPairs] using hh
  have hbound := tested_suffix_collision_bound ρ ρ (Q.descendant X) (Q.descendant Y)
    (p-a) G H (descriptorPairTests_measurable w₀ Q ρ m N σ J i _)
    (Q.descendant_side_pos hQp X) hPY hg (by positivity : 0 < 1/(2:ℝ)^t)
    (by rw [hsmallSide]; exact dyadic_side_mono hpt)
    (by rw [hsmallSide]; exact suffix_linearization_scale d (by omega))
    (by rw [hsmallSide]; exact h₁ N ((le_max_left _ _).trans hN) a p t (by omega) i hi)
    hcenters _ hproj hchild (100*((d:ℝ)+1))
  rw [hsmallSide] at hbound
  simp only [div_eq_mul_inv,one_mul] at hbound ⊢
  apply hbound.trans
  apply mul_le_mul' le_rfl
  apply measure_mono
  intro z hz
  change |z.1-z.2| ≤ _ at hz
  change |z.1-z.2| ≤ _
  apply hz.trans
  have hs := sqrt_dimension_le d
  have he : 1+4*Real.sqrt d ≤ 100*((d:ℝ)+1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  simpa only [mul_one,one_mul,div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ 1/(2:ℝ)^p)

noncomputable def positiveCollisionCount (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (A : ℕ → ℝ)
    (N : ℕ) (σ : ℝ) (J i q a t : ℕ) (X Y : List (Fin d → Bool)) : ℝ≥0∞ :=
  ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a)) *
    ((testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
        (policyTestPairs w₀ Q ρ m A N σ J i q a t)).prod
      (testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
        (policyTestPairs w₀ Q ρ m A N σ J i q a t)))
      {z : ℝ × ℝ | |z.1-z.2| ≤ (100*((d:ℝ)+1))/(2:ℝ)^t}

theorem positiveCollisionCount_ne_top (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (A : ℕ → ℝ)
    (N : ℕ) (σ : ℝ) (J i q a t : ℕ) (X Y : List (Fin d → Bool)) :
    positiveCollisionCount w₀ Q ρ m A N σ J i q a t X Y ≠ ⊤ := by
  unfold positiveCollisionCount
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

theorem positive_suffix_prefactor (N : ℕ) (M K : ℝ) {a p t : ℕ}
    (hap : a ≤ p) (hpt : p ≤ t) :
    ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*M)) *
        ENNReal.ofReal ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^K) =
      ENNReal.ofReal (((2:ℝ)^N)^K) *
        ENNReal.ofReal ((2:ℝ)^(p-a)*((2:ℝ)^N)^(4*M)) := by
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hp : (2:ℝ)^(t-a) = (2:ℝ)^(p-a)*(2:ℝ)^(t-p) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp]
  field_simp

theorem uniform_policy_suffix_count {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (A : ℕ → ℝ)
        (q a p t i : ℕ), 0 < q → t ≤ N → a+100*q < t →
        p = PlanarFalconer.policyDepth A N q a t → a+t < 2*p → i ≤ J →
      ∀ (w₀ : Sphere d) (X Y : List (Fin d → Bool)), X.length = a → Y.length = a →
      125*((d:ℝ)+1)*(Q.descendant X).side ≤
        ‖(Q.descendant X).center-(Q.descendant Y).center‖ →
      positiveCollisionCount w₀ Q ρ m A N σ J i q a t X Y ≤
        (((PlanarFalconer.bandOffsets (100*((d:ℝ)+1))).card : ℝ≥0∞) *
          ((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞) *
          ENNReal.ofReal (((2:ℝ)^N)^(
            Regularization.profileDrop m N ((d:ℝ)/2) p t+1000*((d:ℝ)+1)*σ))) *
        positiveCollisionCount w₀ Q ρ m A N σ J (i+1) q a p X Y := by
  obtain ⟨N₀,h₀⟩ := uniform_policy_suffix_collision (d := d) hσ hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ m A q a p t i hq htN hwide hp hapt hi w₀ X Y hX hY hsep
  have hc := h₀ N hN Q hQ ρ m A q a p t i hq htN hwide hp hapt hi w₀ X Y hX hY hsep
  have hpi := PlanarFalconer.policyDepth_interior A hq
    (PlanarFalconer.policyBlocks_nonempty hq htN hwide)
  rw [← hp] at hpi
  have hap : a ≤ p := by omega
  have hpt : p ≤ t := by omega
  unfold positiveCollisionCount
  apply (mul_le_mul' (le_refl (ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a)))) hc).trans_eq
  let K := Regularization.profileDrop m N ((d:ℝ)/2) p t+1000*((d:ℝ)+1)*σ
  let B : ℝ≥0∞ := ((PlanarFalconer.bandOffsets (100*((d:ℝ)+1))).card : ℝ≥0∞) *
    ((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞)
  let C : ℝ≥0∞ := ((testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
    (policyTestPairs w₀ Q ρ m A N σ J (i+1) q a p)).prod
    (testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
    (policyTestPairs w₀ Q ρ m A N σ J (i+1) q a p)))
      {z : ℝ × ℝ | |z.1-z.2| ≤ (100*((d:ℝ)+1))/(2:ℝ)^p}
  change ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a)) *
      (B*ENNReal.ofReal ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^K)*C) =
    (B*ENNReal.ofReal (((2:ℝ)^N)^K)) *
      (ENNReal.ofReal ((2:ℝ)^(p-a)*((2:ℝ)^N)^(4*m a))*C)
  calc
    _ = B*(ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a)) *
        ENNReal.ofReal ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^K))*C := by ring
    _ = _ := by rw [positive_suffix_prefactor N (m a) K hap hpt]; ring

end Falconer

end OAI
