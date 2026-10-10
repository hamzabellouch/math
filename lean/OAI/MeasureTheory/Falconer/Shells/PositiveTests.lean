import OAI.MeasureTheory.Falconer.Estimates.DescriptorMasks
import OAI.MeasureTheory.Falconer.Estimates.SuffixReduction

namespace OAI

/-! # Full-cell projection estimates extracted from actual retained pairs -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem DyadicCube.mem_ancestor (Q : DyadicCube d) (P : List (Fin d → Bool))
    (g : ℕ) {x : Space d} (hx : x ∈ (Q.descendant P).carrier) :
    x ∈ (Q.descendant (P.take g)).carrier := by
  rw [← List.take_append_drop g P, Q.descendant_append] at hx
  exact (Q.descendant (P.take g)).descendant_subset (P.drop g) hx

theorem descriptorEndpointGood_reached (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (P : List (Fin d → Bool)) (hg : descriptorAnchor b ≤ P.length)
    {x y : Space d} (hx : x ∈ (Q.descendant P).carrier)
    (hy : y ∈ (Q.descendant P).carrier) (w : Sphere d) :
    (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b ↔
      (y,w) ∈ descriptorEndpointGood Q ρ m N σ J i b := by
  have hl : (P.take (descriptorAnchor b)).length = descriptorAnchor b := by
    rw [List.length_take, Nat.min_eq_left hg]
  rw [descriptorEndpointGood_on_cell Q ρ m N σ J i b _ hl
    (Q.mem_ancestor P _ hx), descriptorEndpointGood_on_cell Q ρ m N σ J i b _ hl
    (Q.mem_ancestor P _ hy)]

theorem retained_projection_test (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i a p t : ℕ) (hap : a ≤ p)
    (X Y : List (Fin d → Bool)) (hY : Y.length = a)
    (B : Finset PolicyDescriptor) (hb : PolicyDescriptor.projection p t ∈ B)
    (G : Set (Space d × Space d))
    (hG : G ⊆ descriptorPairTests w₀ Q ρ m N σ J i B)
    (hne : ∀ x ∈ (Q.descendant X).carrier, ∀ y ∈ (Q.descendant Y).carrier, x ≠ y) :
    ∀ c ∈ retainedCellPairs ρ ρ (Q.descendant X) (Q.descendant Y) (p-a) G,
      ∃ x ∈ ((Q.descendant X).descendant c.1).carrier,
        ∃ y ∈ ((Q.descendant Y).descendant c.2).carrier, x ≠ y ∧
        ((ρ.restrict ((Q.descendant Y).descendant c.2).carrier).prod
          (ρ.restrict ((Q.descendant Y).descendant c.2).carrier))
          {z : Space d × Space d |
            |inner ℝ (‖x-y‖⁻¹ • (x-y)) (z.1-z.2)| ≤ angularTestWidth N σ J i t} ≤
          ENNReal.ofReal ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^(
            Regularization.profileDrop m N ((d:ℝ)/2) p t+1000*((d:ℝ)+1)*σ)) *
              (ρ ((Q.descendant Y).descendant c.2).carrier)^2 := by
  intro c hc
  obtain ⟨hocc,x,hx,y,hy,hxy⟩ := Finset.mem_filter.mp hc
  have hlen : c.2.length = p-a :=
    (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp (Finset.mem_product.mp hocc).2).1
  have hanchor : (Y++c.2).length = descriptorAnchor (.projection p t) := by
    simp only [List.length_append,hY,hlen,descriptorAnchor]
    omega
  have hy' : y ∈ (Q.descendant (Y++c.2)).carrier := by
    simpa only [Q.descendant_append] using hy
  have hgood := ((hG hxy) (.projection p t) hb).2
  have htest := (descriptorEndpointGood_on_cell Q ρ m N σ J i (.projection p t)
    (Y++c.2) hanchor hy' (normalizeToSphere w₀ (x-y))).mp hgood
  have hbound := descriptor_projection_original_bound Q ρ m N σ J i p t
    (Y++c.2) (normalizeToSphere w₀ (x-y)) htest
  have hneq : x ≠ y := hne x ((Q.descendant X).descendant_subset c.1 hx)
    y ((Q.descendant Y).descendant_subset c.2 hy)
  refine ⟨x,hx,y,hy,hneq,?_⟩
  simpa only [Q.descendant_append,normalizeToSphere_coe_of_ne w₀
    (sub_ne_zero.mpr hneq),NormedSpace.normalize] using hbound

theorem DyadicCube.pair_ne_of_separation (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    {g : ℝ} (hsep : g ≤ ‖P.center-Q.center‖)
    (hsmall : 2*Real.sqrt d*P.side < g)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) : x ≠ y := by
  have hQp : 0 < Q.side := by rwa [hQ]
  have h₁ := P.dist_le hP.le hx (P.center_mem hP)
  have h₂ := Q.dist_le hQp.le hy (Q.center_mem hQp)
  rw [hQ] at h₂
  have hδ : ‖(x-y)-(P.center-Q.center)‖ ≤ 2*Real.sqrt d*P.side := by
    simpa only [dist_eq_norm,two_mul,mul_add,add_mul] using
      pair_displacement_bound x y P.center Q.center h₁ h₂
  intro he
  rw [he,sub_self,zero_sub,norm_neg] at hδ
  linarith

theorem DyadicCube.pair_sphere_direction_dist (w₀ : Sphere d) (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    {g : ℝ} (hg : 0 < g) (hsep : g ≤ ‖P.center-Q.center‖)
    (hsmall : 2*Real.sqrt d*P.side < g)
    {x y x' y' : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier)
    (hx' : x' ∈ P.carrier) (hy' : y' ∈ Q.carrier) :
    dist (normalizeToSphere w₀ (x-y)) (normalizeToSphere w₀ (x'-y')) ≤
      8*Real.sqrt d*P.side/g := by
  have hxy := P.pair_ne_of_separation Q hP hQ hsep hsmall hx hy
  have hxy' := P.pair_ne_of_separation Q hP hQ hsep hsmall hx' hy'
  rw [Subtype.dist_eq,dist_eq_norm,normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr hxy),
    normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr hxy')]
  change ‖‖x-y‖⁻¹ • (x-y)-‖x'-y'‖⁻¹ • (x'-y')‖ ≤ _
  calc
    _ ≤ ‖‖x-y‖⁻¹ • (x-y)-‖P.center-Q.center‖⁻¹ • (P.center-Q.center)‖ +
        ‖‖P.center-Q.center‖⁻¹ • (P.center-Q.center)-‖x'-y'‖⁻¹ • (x'-y')‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 4*Real.sqrt d*P.side/g+4*Real.sqrt d*P.side/g :=
      add_le_add (P.pair_direction_approximation Q hP hQ hg hsep hx hy hxy)
        (by simpa only [norm_sub_rev] using
          P.pair_direction_approximation Q hP hQ hg hsep hx' hy' hxy')
    _ = _ := by ring

theorem uniform_full_cell_tests_of_witness {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
        (B : Finset PolicyDescriptor), (∀ b ∈ B, descriptorValid N b) →
      ∀ (p : ℕ) (X Y : List (Fin d → Bool)), X.length = p → Y.length = p →
      (∀ b ∈ B, descriptorAnchor b ≤ p) →
      ∀ (g : ℝ), 0 < g → g ≤ ‖(Q.descendant X).center-(Q.descendant Y).center‖ →
      2*Real.sqrt d*(Q.descendant X).side < g →
      (∀ b ∈ B, 8*Real.sqrt d*(Q.descendant X).side/g ≤
        angularTestRadius N σ (descriptorLength b)) →
      ∀ (i : ℕ) (w₀ : Sphere d) (x y : Space d),
      x ∈ (Q.descendant X).carrier → y ∈ (Q.descendant Y).carrier →
      (x,y) ∈ descriptorPairTests w₀ Q ρ m N σ J i B →
      (Q.descendant X).carrier ×ˢ (Q.descendant Y).carrier ⊆
        descriptorPairTests w₀ Q ρ m N σ J (i+1) B := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptorEndpointGood_buffer (d := d) hσ hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ m B hB p X Y hX hY hanchor g hg hsep hsmall hrad i w₀ x y hx hy hgood
  have hQp : 0 < Q.side := by rw [hQ]; norm_num
  have hside : (Q.descendant Y).side = (Q.descendant X).side := by
    rw [Q.descendant_side,Q.descendant_side,hX,hY]
  intro z hz b hb
  have hdist := (Q.descendant X).pair_sphere_direction_dist w₀ (Q.descendant Y)
    (Q.descendant_side_pos hQp X) hside hg hsep hsmall hx hy hz.1 hz.2
  constructor
  · apply h₀ N hN Q hQ ρ m b (hB b hb) i z.1
      (normalizeToSphere w₀ (x-y)) (normalizeToSphere w₀ (z.1-z.2))
      (hdist.trans (hrad b hb))
    exact (descriptorEndpointGood_reached Q ρ m N σ J i b X
      (by rw [hX]; exact hanchor b hb) hx hz.1 _).mp (hgood b hb).1
  · apply h₀ N hN Q hQ ρ m b (hB b hb) i z.2
      (normalizeToSphere w₀ (x-y)) (normalizeToSphere w₀ (z.1-z.2))
      (hdist.trans (hrad b hb))
    exact (descriptorEndpointGood_reached Q ρ m N σ J i b Y
      (by rw [hY]; exact hanchor b hb) hy hz.2 _).mp (hgood b hb).2

end Falconer

end OAI
