import OAI.NumberTheory.TotientAsymptotic.PrimeGridLower
import OAI.NumberTheory.TotientAsymptotic.StrictPrefixContraction

namespace OAI

/-! Finite prime grids covering concrete bounded prefix regions. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def prefixBoxGrid (N : ℕ) (B : ℝ) : Finset (Fin N → ℕ) :=
  Fintype.piFinset (fun i => Finset.Icc 1 (⌊B/a (i.val+1)⌋₊+1))

lemma prefixRegion_coordinate_upper {N : ℕ} {B : ℝ} {u : Fin N → ℝ}
    (hu : u ∈ prefixRegion N B 0 0) (i : Fin N) : u i ≤ B/a (i.val+1) := by
  apply (le_div_iff₀ (a_pos (by omega))).mpr
  have hh : a (i.val+1)*u i ≤ ∑ j : Fin N,a (j.val+1)*u j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (a_pos (j:=j.val+1) (by omega)).le
      (prefixRegion_coordinate_nonneg hu j)) (Finset.mem_univ i)
  have hb := hh.trans (by simpa only [sub_zero] using hu.2)
  simpa only [mul_comm] using hb

lemma prefixBoxGrid_covers (N : ℕ) (B : ℝ) :
    prefixRegion N B 0 0 ⊆ gridRegion (prefixBoxGrid N B) := by
  intro u hu
  let b : Fin N → ℕ := fun i => ⌊u i⌋₊+1
  have hgrid : b ∈ prefixBoxGrid N B := by
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_Icc.mpr
    exact ⟨by dsimp [b]; omega,
      Nat.add_le_add_right (Nat.floor_mono (prefixRegion_coordinate_upper hu i)) 1⟩
  have hcell : u ∈ unitGridCell b := by
    intro i _
    dsimp [b]
    rw [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
    exact ⟨Nat.floor_le (prefixRegion_coordinate_nonneg hu i),Nat.lt_floor_add_one _⟩
  exact Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr ⟨hgrid,hcell⟩⟩

lemma prefixBoxGrid_positive {N : ℕ} {B : ℝ} {b : Fin N → ℕ}
    (hb : b ∈ prefixBoxGrid N B) (i : Fin N) : 1 ≤ b i :=
  (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hb i)).1

lemma prefix_outer_grid_covers {N : ℕ} {B : ℝ} {S : Set (Fin N → ℝ)}
    (hS : S ⊆ prefixRegion N B 0 0) :
    S ⊆ gridRegion (gridOuter (prefixBoxGrid N B) S) := by
  intro u hu
  obtain ⟨b,hb⟩ := Set.mem_iUnion.mp (prefixBoxGrid_covers N B (hS hu))
  obtain ⟨hb,hcell⟩ := Set.mem_iUnion.mp hb
  exact Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr
    ⟨Finset.mem_filter.mpr ⟨hb,u,hcell,hu⟩,hcell⟩⟩

theorem positive_prefix_grid_mass : ∃ c : ℝ,0 < c ∧
    ∀ {N : ℕ} (B : ℝ) (S : Set (Fin N → ℝ)),
      S ⊆ prefixRegion N B 0 0 →
      (∀ u ∈ S,∀ i,c*(N-i.val:ℕ) ≤ u i) →
      volume.real S/2 ≤ gridPrimeMass (gridOuter (prefixBoxGrid N B) S) := by
  obtain ⟨c,hc,hprime⟩ := grid_prime_mass_lower
  refine ⟨c,hc,?_⟩
  intro N B S hS hlower
  let K := gridOuter (prefixBoxGrid N B) S
  have hK : ∀ b ∈ K,∀ i,1 ≤ b i ∧ c*(N-i.val:ℕ) ≤ (b i:ℝ) := by
    intro b hb i
    obtain ⟨hb,u,hcell,hu⟩ := Finset.mem_filter.mp hb
    exact ⟨prefixBoxGrid_positive hb i,(hlower u hu i).trans
      (hcell i (Set.mem_univ _)).2.le⟩
  have hcard : volume.real S ≤ (K.card:ℝ) := by
    have hh := measureReal_mono (prefix_outer_grid_covers hS)
      (by rw [volume_gridRegion]; exact ENNReal.natCast_ne_top _)
    simpa only [Measure.real,gridRegion_volume_real] using hh
  exact (div_le_div_of_nonneg_right hcard (by norm_num : (0:ℝ) ≤ 2)).trans (hprime K hK)

end TotientAsymptotic

end

end OAI
