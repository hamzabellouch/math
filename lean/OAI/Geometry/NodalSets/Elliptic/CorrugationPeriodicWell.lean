import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import OAI.Geometry.NodalSets.Elliptic.CorrugationDiskWell

namespace OAI

namespace Yau.Geometry
open Real Set Filter
open scoped ContDiff Topology
noncomputable section

def corrugationPeriodicWell (a : ℝ) (z : ℝ × ℝ) : ℝ :=
  ∑' k : ℤ × ℤ, corrugationDiskWell a (1/4) (z.1-(k.1:ℝ),z.2-(k.2:ℝ))

lemma corrugation_translate_zero (a : ℝ) (N : ℕ) (z : ℝ × ℝ)
    (hz₁ : |z.1| < (N:ℝ)-1) (hz₂ : |z.2| < (N:ℝ)-1)
    (k : ℤ × ℤ) (hk : k ∉ Finset.Icc (-(N:ℤ),-(N:ℤ)) ((N:ℤ),(N:ℤ))) :
    corrugationDiskWell a (1/4) (z.1-(k.1:ℝ),z.2-(k.2:ℝ)) = 0 := by
  apply corrugationDiskWell_zero
  have hz1 := abs_lt.mp hz₁
  have hz2 := abs_lt.mp hz₂
  simp only [Finset.mem_Icc,Prod.le_def,not_and_or,not_le] at hk
  rcases hk with (hk | hk) | (hk | hk)
  all_goals
    have hk' := (Int.cast_lt (R := ℝ)).mpr hk
    push_cast at hk'
    dsimp only
    nlinarith [sq_nonneg (z.1-(k.1:ℝ)),sq_nonneg (z.2-(k.2:ℝ))]

lemma corrugationPeriodicWell_eq_sum (a : ℝ) (N : ℕ) (z : ℝ × ℝ)
    (hz₁ : |z.1| < (N:ℝ)-1) (hz₂ : |z.2| < (N:ℝ)-1) :
    corrugationPeriodicWell a z =
      ∑ k ∈ Finset.Icc (-(N:ℤ),-(N:ℤ)) ((N:ℤ),(N:ℤ)),
        corrugationDiskWell a (1/4) (z.1-(k.1:ℝ),z.2-(k.2:ℝ)) := by
  apply tsum_eq_sum
  intro k hk
  exact corrugation_translate_zero a N z hz₁ hz₂ k hk

lemma corrugationPeriodicWell_smooth (a : ℝ) : ContDiff ℝ ∞ (corrugationPeriodicWell a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  obtain ⟨N,hN⟩ := exists_nat_gt (max |z.1| |z.2|+1)
  have hz₁ : |z.1| < (N:ℝ)-1 := by have := le_max_left |z.1| |z.2|; linarith
  have hz₂ : |z.2| < (N:ℝ)-1 := by have := le_max_right |z.1| |z.2|; linarith
  have hsum : ContDiff ℝ ∞ (fun w : ℝ × ℝ ↦
      ∑ k ∈ Finset.Icc (-(N:ℤ),-(N:ℤ)) ((N:ℤ),(N:ℤ)),
        corrugationDiskWell a (1/4) (w.1-(k.1:ℝ),w.2-(k.2:ℝ))) := by
    apply ContDiff.sum
    intro k _
    exact (corrugationDiskWell_smooth a (1/4)).comp
      ((contDiff_fst.sub contDiff_const).prodMk (contDiff_snd.sub contDiff_const))
  apply hsum.contDiffAt.congr_of_eventuallyEq
  have h1 : ∀ᶠ w : ℝ × ℝ in 𝓝 z, |w.1| < (N:ℝ)-1 :=
    (continuous_fst.abs.continuousAt).eventually_lt_const hz₁
  have h2 : ∀ᶠ w : ℝ × ℝ in 𝓝 z, |w.2| < (N:ℝ)-1 :=
    (continuous_snd.abs.continuousAt).eventually_lt_const hz₂
  filter_upwards [h1,h2] with w hw1 hw2
  exact corrugationPeriodicWell_eq_sum a N w hw1 hw2

lemma corrugationPeriodicWell_periodic (a : ℝ) (m : ℤ × ℤ) (z : ℝ × ℝ) :
    corrugationPeriodicWell a (z.1+(m.1:ℝ),z.2+(m.2:ℝ)) = corrugationPeriodicWell a z := by
  unfold corrugationPeriodicWell
  have h := (Equiv.addRight m).tsum_eq
    (fun k : ℤ × ℤ ↦ corrugationDiskWell a (1/4) (z.1+(m.1:ℝ)-(k.1:ℝ),z.2+(m.2:ℝ)-(k.2:ℝ)))
  simpa only [Equiv.coe_addRight,Prod.fst_add,Prod.snd_add,Int.cast_add,add_sub_add_right_eq_sub] using h.symm

end
end Yau.Geometry

end OAI
