import OAI.MeasureTheory.Falconer.Estimates.ScalarSumCells

namespace OAI

/-! Stability of scalar covering numbers under bounded perturbations.
These fixed constants keep the later projection changes at one scale. -/
namespace Falconer
open scoped Pointwise

theorem scalarCells_near_card {δ : ℝ} (hδ : 0 < δ) (A B : Finset ℝ)
    (hcover : ∀ a ∈ A, ∃ b ∈ B, |a-b| ≤ 2*δ) :
    (scalarCells δ A).card ≤ 7*(scalarCells δ B).card := by
  classical
  let I := fun k : ℤ => Finset.Icc (k-3) (k+3)
  have hsub : scalarCells δ A ⊆ (scalarCells δ B).biUnion I := by
    intro k hk
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨b,hb,hab⟩ := hcover a ha
    apply Finset.mem_biUnion.mpr
    refine ⟨⌊b/δ⌋,Finset.mem_image.mpr ⟨b,hb,rfl⟩,?_⟩
    have hh := floor_div_near hδ hab
    rw [abs_le] at hh
    apply Finset.mem_Icc.mpr
    omega
  have hI (k : ℤ) : (I k).card = 7 := by
    dsimp [I]
    rw [Int.card_Icc]
    have he : k+3+1-(k-3) = (7 : ℤ) := by omega
    rw [he]
    rfl
  calc
    _ ≤ ((scalarCells δ B).biUnion I).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ scalarCells δ B, (I k).card := Finset.card_biUnion_le
    _ = _ := by simp [hI,Nat.mul_comm]

theorem scalar_linear_sum_stability {δ R a b : ℝ} (hδ : 0 < δ)
    (X Y : Finset ℝ) (hY : ∀ y ∈ Y, |y| ≤ R) (hab : |a-b| * R ≤ 2*δ) :
    (scalarCells δ (X+Y.image (fun y => a*y))).card ≤
      7*(scalarCells δ (X+Y.image (fun y => b*y))).card := by
  classical
  apply scalarCells_near_card hδ
  intro z hz
  obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
  refine ⟨x+b*y,Finset.add_mem_add hx (Finset.mem_image.mpr ⟨y,hy,rfl⟩),?_⟩
  calc
    |(x+a*y)-(x+b*y)| = |a-b| * |y| := by
      rw [show (x+a*y)-(x+b*y) = (a-b)*y by ring,abs_mul]
    _ ≤ |a-b| * R := mul_le_mul_of_nonneg_left (hY y hy) (abs_nonneg _)
    _ ≤ 2*δ := hab

end Falconer

end OAI
