import OAI.Geometry.NodalSets.Elliptic.HalfScaleLemmas
import OAI.Geometry.NodalSets.Waves.LatticeCount
import OAI.Geometry.NodalSets.Waves.ShiftedGaussianSum

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability
noncomputable section

lemma scaled_lattice_squared_distance {n : ℕ} (hn : 0 < n) (x : Coord)
    (z : Fin 4 → ℤ) :
    (n:ℝ)*(sourceEuclideanNorm (x-scaledLatticePoint n z))^2 =
      ∑ i, (Real.sqrt n*x i-(z i:ℝ))^2 := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ n by positivity)
  rw [sourceEuclideanNorm,Real.sq_sqrt (by positivity),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (n:ℝ)*(x i-(n:ℝ)^(-1/2:ℝ)*(z i:ℝ))^2 = _
  rw [lattice_scale_eq_inv_sqrt]
  field_simp
  nlinarith [hs2]

theorem source_lattice_gaussian_sum {a : ℝ} (ha : 0 < a) :
    ∃ C > 0, ∀ (U : Set Coord) (n : ℕ), 0 < n → ∀ [Fintype (SourceGrid U n)],
      ∀ x : Coord, ∑ z : SourceGrid U n,
        Real.exp (-a*(n:ℝ)*(sourceEuclideanNorm (x-scaledLatticePoint n z))^2) ≤ C := by
  classical
  obtain ⟨C,hC,hb⟩ := finite_shifted_gaussian_sum_pi (d := 4) ha
  refine ⟨C,hC,?_⟩
  intro U n hn hfin x
  let s : Finset (Fin 4 → ℤ) := Finset.univ.image (fun z : SourceGrid U n ↦ z.val)
  have h := hb (fun i ↦ Real.sqrt n*x i) s
  rw [Finset.sum_image (by intro u _ v _ huv; exact Subtype.ext huv)] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  rw [mul_assoc,scaled_lattice_squared_distance hn]

end
end Yau.Geometry

end OAI
