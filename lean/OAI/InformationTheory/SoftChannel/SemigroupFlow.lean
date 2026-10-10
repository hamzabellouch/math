import OAI.InformationTheory.BooleanNoise.SemigroupFlow
import OAI.InformationTheory.SoftChannel.Rearrangement

namespace OAI

section

noncomputable section

open scoped BigOperators Topology
open Filter

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem SemigroupFlow_noiseKernel_flip_derivative_term (u : ℝ)
    (x y : Cube n) (i : Fin n) :
    (∏ j ∈ Finset.univ.erase i,
      if x j = y j then (1 + u) / 2 else (1 - u) / 2) *
      (if x i = y i then -u / 2 else u / 2) =
        -((noiseKernel u x y - noiseKernel u (flip i x) y) / 2) := by
  have hrest : (∏ j ∈ Finset.univ.erase i,
      if (flip i x) j = y j then (1 + u) / 2 else (1 - u) / 2) =
      ∏ j ∈ Finset.univ.erase i,
        if x j = y j then (1 + u) / 2 else (1 - u) / 2 := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [flip, LeanBlast.GotsmanLinial.flip, Function.update_of_ne hji]
  rw [noiseKernel_split_coord u x y i, noiseKernel_split_coord u (flip i x) y i, hrest]
  cases hx : x i <;> cases hy : y i <;>
    simp [flip, LeanBlast.GotsmanLinial.flip, hx] <;> ring

theorem SemigroupFlow_hasDerivAt_noise_factor (x y : Cube n) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
      if x i = y i then (1 + Real.exp (-s)) / 2 else (1 - Real.exp (-s)) / 2)
      (if x i = y i then -Real.exp (-t) / 2 else Real.exp (-t) / 2) t := by
  have hu : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  by_cases hxy : x i = y i
  · simp only [ite_eq_left hxy]
    exact (hu.const_add 1).div_const 2
  · simp only [ite_eq_right hxy]
    simpa using (hu.const_sub 1).div_const 2

end LeanBlast.CourtadeKumar
end
end

end OAI
