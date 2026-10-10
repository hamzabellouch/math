import OAI.Analysis.RCDHeat.InnerPath
import OAI.Analysis.RCDHeat.KantorovichRadius

namespace OAI

/-! # Compact contact completion by two quadratic transforms

The completion preserves every contact of the original compact potential.
It also keeps an explicit compact support radius for the right potential.
-/

open Set Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem compact_contact_completion (hgeo : IsGeodesicSpace X)
    (p : X) {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    {R : ℝ} (hzero : ∀ x, R < dist p x → φ x = 0) :
    ∃ (ψ : X → ℝ) (r : ℝ), LipschitzWith L ψ ∧ HasCompactSupport ψ ∧
      (∀ x, r < dist p x → ψ x = 0) ∧
      LipschitzWith L (hopfLax (-ψ) 1) ∧ HasCompactSupport (hopfLax (-ψ) 1) ∧
      (∀ x y, hopfLax (-ψ) 1 x + ψ y ≤ dist x y ^ 2 / 2) ∧
      (∀ x, φ x ≤ hopfLax (-ψ) 1 x) ∧
      ∀ x y b, (∀ z, φ z + b ≤ dist z y ^ 2 / 2) →
        φ x + b = dist x y ^ 2 / 2 →
        hopfLax (-ψ) 1 x = φ x ∧ ψ y = b := by
  let ψ := hopfLax (-φ) 1
  have hpos : (0 : ℝ) < 1 := by norm_num
  have hψ : LipschitzWith L ψ := hopfLax_lipschitz hφ.neg hgeo hpos
  have hnegzero (x : X) (hx : R < dist p x) : (-φ) x = 0 := by
    simp only [Pi.neg_apply,hzero x hx,neg_zero]
  have hψs : HasCompactSupport ψ := hopfLax_hasCompactSupport hφ.neg p R hnegzero hpos
  have hψzero (x : X) (hx : R+2*(L:ℝ) < dist p x) : ψ x = 0 := by
    apply hopfLax_zero_outside hφ.neg p R hnegzero hpos
    simpa only [mul_one] using hx
  have hψnegzero (x : X) (hx : R+2*(L:ℝ) < dist p x) : (-ψ) x = 0 := by
    simp only [Pi.neg_apply,hψzero x hx,neg_zero]
  have hχ : LipschitzWith L (hopfLax (-ψ) 1) := hopfLax_lipschitz hψ.neg hgeo hpos
  have hχs : HasCompactSupport (hopfLax (-ψ) 1) :=
    hopfLax_hasCompactSupport hψ.neg p (R+2*(L:ℝ)) hψnegzero hpos
  have had (x y : X) : φ x + ψ y ≤ dist x y ^ 2 / 2 := by
    have hh := hopfLax_le_cost hφ.neg hpos y x
    simp only [Pi.neg_apply,mul_one,dist_comm y x] at hh
    dsimp only [ψ]
    linarith
  refine ⟨ψ,R+2*(L:ℝ),hψ,hψs,hψzero,hχ,hχs,?_,?_,?_⟩
  · intro x y
    have hh := hopfLax_le_cost hψ.neg hpos x y
    simp only [Pi.neg_apply,mul_one] at hh
    linarith
  · intro x
    apply le_csInf ⟨_,mem_range_self x⟩
    rintro _ ⟨y,rfl⟩
    have hh := had x y
    simp only [Pi.neg_apply,mul_one]
    linarith
  · intro x y b hb hxy
    have hby : b ≤ ψ y := by
      apply le_csInf ⟨_,mem_range_self x⟩
      rintro _ ⟨z,rfl⟩
      have hh := hb z
      simp only [Pi.neg_apply,mul_one,dist_comm y z]
      linarith
    have hyb : ψ y ≤ b := by linarith [had x y]
    have he : ψ y = b := le_antisymm hyb hby
    refine ⟨(hopfLax_of_contact hψ had (x := x) (y := y) ?_).1,he⟩
    rwa [he]

end RegularPointCoordinates

end

end OAI
