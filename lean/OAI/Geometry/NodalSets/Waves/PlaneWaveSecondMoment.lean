import OAI.Geometry.NodalSets.Waves.LatticeFrequencyAnnulus
import OAI.Geometry.NodalSets.Waves.LatticeNormalizedWeights

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section

lemma coordinate_second_moment {ι : Type*} (F : Finset ι) (α : ι → ℂ)
    (k : ι → Coord) (κ : ℝ) (hκ : 0 ≤ κ)
    (hmass : (1/2:ℝ) ≤ ∑ i ∈ F, ‖α i‖^2)
    (hk : ∀ i ∈ F, κ ≤ sourceEuclideanNorm (k i)) :
    ∃ j : Fin 4, κ^2/8 ≤ ∑ i ∈ F, ‖α i‖^2*(k i j)^2 := by
  classical
  have hsq (i : ι) (hi : i ∈ F) : κ^2 ≤ ∑ j : Fin 4, (k i j)^2 := by
    have hh := pow_le_pow_left₀ hκ (hk i hi) 2
    have he : (sourceEuclideanNorm (k i))^2 = ∑ j : Fin 4, (k i j)^2 :=
      Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
    rwa [he] at hh
  have htotal : κ^2/2 ≤ ∑ j : Fin 4, ∑ i ∈ F, ‖α i‖^2*(k i j)^2 := by
    calc
      _ ≤ κ^2*(∑ i ∈ F, ‖α i‖^2) := by nlinarith [sq_nonneg κ]
      _ = ∑ i ∈ F, ‖α i‖^2*κ^2 := by rw [Finset.mul_sum]; congr 1; funext i; ring
      _ ≤ ∑ i ∈ F, ‖α i‖^2*(∑ j : Fin 4, (k i j)^2) :=
        Finset.sum_le_sum (fun i hi ↦ mul_le_mul_of_nonneg_left (hsq i hi) (sq_nonneg _))
      _ = _ := by simp only [Finset.mul_sum]; rw [Finset.sum_comm]
  by_contra h
  push Not at h
  have hh := Finset.sum_lt_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) ↦ (h j).le)
    ⟨0,Finset.mem_univ _,h 0⟩
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  linarith

theorem lattice_main_coordinate_moment
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) {H : Set Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ c > 0, ∀ (w S : Coord → ℝ) (D U Q : Set Coord) (m J K k0 : ℕ)
      (a : LocalCompactWaveData g w S D m J K k0), H ⊆ D → ∀ (hUD : U ⊆ D),
      U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
      ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
        ∀ x ∈ Q, ∃ j : Fin 4,
        c ≤ ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ)),
          ‖a.latticeAlpha hUD n x i‖^2 *
            (sourceFrequency (g (scaledLatticePoint n i.1))
              (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2)
              (sourceSignScale g S x) j)^2 := by
  classical
  obtain ⟨κ,hκ,B,hB,hann⟩ := lattice_main_frequency_annulus g hH hg hp
  refine ⟨κ^2/8,by positivity,?_⟩
  intro w S D U Q m J K k0 a hHD hUD hUH hU hUb hQ hQU
  have hm := a.latticeAlpha_main_mass hUD hU hUb hQ hQU (1/2) (by norm_num)
  filter_upwards [hann w S D U m J K k0 a hHD hUD hUH,hm] with n hn hmass
  obtain ⟨hfin,hmass⟩ := hmass
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx
  apply coordinate_second_moment _ _ _ κ hκ.le
  · linarith [(hmass x hx).2]
  · intro i hi
    exact (hn x (hUH (hQU hx)) i (Finset.mem_filter.mp hi).2).1

end
end Yau.Geometry

end OAI
