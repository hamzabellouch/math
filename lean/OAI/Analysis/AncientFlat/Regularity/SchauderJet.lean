import OAI.Analysis.AncientFlat.Kernel.ClassicalBase

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff BoundedContinuousFunction SchwartzMap
namespace ParabolicSchauder
open SourceFrozenRows SchwartzTimeScale
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
def jet (K : SchwartzMap V ℂ) (t : ℝ) (f : V →ᵇ ℂ) (j : ℕ) :=
  row K (fun _ => 1) (t^(1/4 : ℝ)) f j
lemma exists_jet_bound (K : SchwartzMap V ℂ) (j : ℕ) (hj : 0<j)
    (α : ℝ) (hα : 0≤α) (hα1 : α≤1) :
    ∃ C : ℝ, 0≤C ∧ ∀ (f : V →ᵇ ℂ) (H : ℝ), 0≤H →
      (∀ x y, ‖f x-f y‖≤H*‖x-y‖^α) → ∀ t : ℝ, 0<t → ∀ x,
      ‖jet K t f j x‖≤C*H*t^((α-j)/4) := by
  obtain ⟨C,D,hC,hD,hb⟩ := exists_row_holder_bound K j hj 1 1 zero_lt_one α hα hα1
  refine ⟨C,hC,fun f H hH hf t ht x => ?_⟩
  have he := hb (fun _ : V => (1:ℝ)) continuous_const (fun _ => ⟨le_rfl,le_rfl⟩)
    0 le_rfl (by intro x y; simp) f H hH hf (t^(1/4 : ℝ)) (by positivity) x
  simp only [mul_zero,zero_mul,add_zero] at he
  have hp : ((t^(1/4 : ℝ))⁻¹)^j*(t^(1/4 : ℝ))^α=t^((α-j)/4) := by
    rw [← Real.rpow_natCast,← Real.rpow_neg ht.le,← Real.rpow_mul ht.le,
      ← Real.rpow_mul ht.le,← Real.rpow_add ht]
    congr 1
    ring
  calc
    _ ≤ (t^(1/4 : ℝ))⁻¹^j*(H*(t^(1/4 : ℝ))^α*C) := he
    _ = C*H*((t^(1/4 : ℝ))⁻¹^j*(t^(1/4 : ℝ))^α) := by ring
    _ = _ := by rw [hp]
lemma exists_jet_lipschitz (K : SchwartzMap V ℂ) (j : ℕ)
    (α : ℝ) (hα : 0≤α) (hα1 : α≤1) :
    ∃ C : ℝ, 0≤C ∧ ∀ (f : V →ᵇ ℂ) (H : ℝ), 0≤H →
      (∀ x y, ‖f x-f y‖≤H*‖x-y‖^α) → ∀ t : ℝ, 0<t → ∀ x y,
      ‖jet K t f j x-jet K t f j y‖≤C*H*t^((α-(j+1))/4)*‖x-y‖ := by
  obtain ⟨C,hC,hb⟩ := exists_jet_bound K (j+1) (Nat.zero_lt_succ _) α hα hα1
  refine ⟨C,hC,fun f H hH hf t ht x y => ?_⟩
  apply Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (s := (univ : Set V)) (fun z _ => (hasFDerivAt_row K (fun _ => 1) continuous_const
      1 1 zero_lt_one (fun _ => ⟨le_rfl,le_rfl⟩) _ (Real.rpow_pos_of_pos ht _) f j z).hasFDerivWithinAt)
    (fun z _ => ?_) (convex_univ) (mem_univ y) (mem_univ x)
  rw [LinearIsometryEquiv.norm_map]
  simpa only [jet,Nat.cast_add,Nat.cast_one] using hb f H hH hf t ht z
end ParabolicSchauder

end

end OAI
