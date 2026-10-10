import OAI.Analysis.Cotype.CompactDomain

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem fixedCotypeBound_pos [Nontrivial X] {m : ℕ} (hm : 0 < m) {D : ℝ}
    (hD : FixedCotypeBound X m D) : 0 < D := by
  obtain ⟨x,hx⟩ := exists_ne (0 : X)
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hs : 0 < Real.sqrt (∑ _ : Fin m, ‖x‖^2) := by
    apply Real.sqrt_pos.mpr
    simpa using mul_pos (show (0:ℝ) < m by exact_mod_cast hm) (sq_pos_of_pos hxpos)
  have h := hD.2 (fun _ : Fin m => x)
  by_contra hn
  have hn' : D ≤ 0 := le_of_not_gt hn
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg hn' (cubeL2_nonneg (rademacherSum X (fun _ : Fin m => x)))
  linarith

theorem dual_fixedCotypeBound_pos [Nontrivial X] {m : ℕ} (hm : 0 < m) {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D) : 0 < D := by
  obtain ⟨x,hx⟩ := exists_ne (0 : X)
  obtain ⟨f,_,hf⟩ := exists_dual_vector'' ℝ x
  have hf0 : f ≠ 0 := by
    intro h
    have he : f x = ‖x‖ := by exact_mod_cast hf
    rw [h] at he
    have hxpos := norm_pos_iff.mpr hx
    exact hxpos.ne' (by simpa using he.symm)
  let : Nontrivial (X →L[ℝ] ℝ) := ⟨⟨f,0,hf0⟩⟩
  exact fixedCotypeBound_pos hm hD

theorem exists_compactDomain_source [CompleteSpace X] [Nontrivial X]
    {m : ℕ} (hm : 0 < m) {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D)
    (E : Submodule ℝ X) [FiniteDimensional ℝ E] :
    Nonempty (CompactDomainWitness E m D) :=
  exists_compactDomain hD (dual_fixedCotypeBound_pos hm hD) E

end Cotype

end

end OAI
