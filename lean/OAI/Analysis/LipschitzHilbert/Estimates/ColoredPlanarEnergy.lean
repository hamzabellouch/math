import OAI.Analysis.LipschitzHilbert.Estimates.PlanarSeparatedEnergy
import OAI.Analysis.LipschitzHilbert.Fourier.DyadicAnnularSeparation
import OAI.Analysis.LipschitzHilbert.Estimates.FiniteEnergySchur

namespace OAI

/-! Summing a fixed number of disjoint annular lists costs only that
number. In particular the ordinary dyadic synthesis constant is uniform
in the number of scales. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert

theorem planar_colored_energy {ι : Type*} [Fintype ι] {q : ℕ}
    (f : ι → SchwartzMap (ℝ×ℝ) ℂ) (color : ι → Fin q) (slope : ℝ)
    (hdisjoint : ∀ y ξ i j, i ≠ j → color i = color j →
      𝓕 (planarSchwartzSlice (f i) y slope) ξ = 0 ∨
        𝓕 (planarSchwartzSlice (f j) y slope) ξ = 0) :
    (∫ z, ‖∑ i, f i z‖^2 ∂volume.prod volume) ≤
      (q:ℝ)*∑ i, ∫ z, ‖f i z‖^2 ∂volume.prod volume := by
  classical
  let selected := fun (r : Fin q) (i : ι) =>
    if color i = r then f i else (0 : SchwartzMap (ℝ×ℝ) ℂ)
  let G := fun r : Fin q => (∑ i, selected r i : SchwartzMap (ℝ×ℝ) ℂ)
  have hzero (y : ℝ) : planarSchwartzSlice (0 : SchwartzMap (ℝ×ℝ) ℂ) y slope = 0 := by
    ext x
    simp [planarSchwartzSlice_apply]
  have hg (r : Fin q) : (∫ z, ‖G r z‖^2 ∂volume.prod volume) =
      ∑ i, if color i = r then (∫ z, ‖f i z‖^2 ∂volume.prod volume) else 0 := by
    have hd : ∀ y ξ i j, i ≠ j →
        𝓕 (planarSchwartzSlice (selected r i) y slope) ξ = 0 ∨
          𝓕 (planarSchwartzSlice (selected r j) y slope) ξ = 0 := by
      intro y ξ i j hij
      by_cases hi : color i = r
      · by_cases hj : color j = r
        · simpa only [selected,ite_eq_left hi,ite_eq_left hj] using
            hdisjoint y ξ i j hij (hi.trans hj.symm)
        · right
          simp only [selected,ite_eq_right hj,hzero]
          simp
      · left
        simp only [selected,ite_eq_right hi,hzero]
        simp
    have h := planar_energy_of_slice_fourier_disjoint (selected r) slope hd
    have hleft (z : ℝ×ℝ) : G r z = ∑ i, selected r i z := by
      simp [G]
    simp_rw [hleft]
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : color i = r <;> simp [selected,hi]
  have hpart (z : ℝ×ℝ) : (∑ r, G r z) = ∑ i, f i z := by
    simp only [G,sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single (color i)]
    · simp [selected]
    · intro r _ hr
      simp [selected,Ne.symm hr]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hcost := weighted_integral_sum_square (volume.prod volume)
    (fun r z => G r z) (fun r => (G r).memLp 2 (volume.prod volume))
    (fun _ => (1:ℝ)) (fun _ => by norm_num)
  simp only [hpart,div_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_one] at hcost
  rw [show (∑ r, ∫ z, ‖G r z‖^2 ∂volume.prod volume) =
      ∑ i, ∫ z, ‖f i z‖^2 ∂volume.prod volume by
    simp_rw [hg]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp] at hcost
  exact hcost

theorem exists_planar_dyadic_energy_constant {lower upper : ℝ} (hlower : 0 < lower) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (f : Fin N → SchwartzMap (ℝ×ℝ) ℂ) (slope : ℝ),
      (∀ j ξ η, planarFourier (f j) (ξ,η) ≠ 0 →
        lower*(2:ℝ)^j.val ≤ |ξ+slope*η| ∧ |ξ+slope*η| ≤ upper*(2:ℝ)^j.val) →
      (∫ z, ‖∑ j, f j z‖^2 ∂volume.prod volume) ≤
        C*∑ j, ∫ z, ‖f j z‖^2 ∂volume.prod volume := by
  obtain ⟨q,hq,hsep⟩ := exists_dyadic_annular_separation (upper := upper) hlower
  refine ⟨q,by exact_mod_cast (Nat.succ_le_of_lt hq),?_⟩
  intro N f slope hspectrum
  apply planar_colored_energy f (fun j => ⟨j.val % q,Nat.mod_lt _ hq⟩) slope
  intro y ξ i j hij hcolor
  have hmod : i.val % q = j.val % q := congrArg Fin.val hcolor
  have hout (j : Fin N)
      (hξ : |ξ| < lower*(2:ℝ)^j.val ∨ upper*(2:ℝ)^j.val < |ξ|) :
      𝓕 (planarSchwartzSlice (f j) y slope) ξ = 0 := by
    apply planarSchwartzSlice_fourier_eq_zero
    intro η
    by_contra hne
    have hs := hspectrum j (ξ-slope*η) η hne
    have he : ξ-slope*η+slope*η = ξ := by ring
    rw [he] at hs
    rcases hξ with h | h
    · exact (not_lt_of_ge hs.1) h
    · exact (not_lt_of_ge hs.2) h
  rcases lt_or_gt_of_ne hij with hij | hji
  · by_cases hj : |ξ| < lower*(2:ℝ)^j.val
    · exact Or.inr (hout j (Or.inl hj))
    · exact Or.inl (hout i (Or.inr ((hsep i.val j.val hij hmod).trans_le (le_of_not_gt hj))))
  · by_cases hi : |ξ| < lower*(2:ℝ)^i.val
    · exact Or.inl (hout i (Or.inl hi))
    · exact Or.inr (hout j (Or.inr ((hsep j.val i.val hji hmod.symm).trans_le (le_of_not_gt hi))))

end LipschitzHilbert

end

end OAI
