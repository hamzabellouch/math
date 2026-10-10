import OAI.Analysis.TriangularHilbert.MeshJump

namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators
noncomputable section

lemma sum_lineMax_scalar_product_bound (D : Finset ℤ) (f g : D → D → ℂ) (u : D → D → ℤ)
    (hu : ∀ i, Function.Injective (u i)) :
    (∑ i, ∑ j, ‖g i j‖*lineMax D (fun m => ‖f i m‖^2) (u i j)) ≤
      ((∑ i, ∑ j, ‖g i j‖^3)+36*Real.sqrt 2*(∑ i, ∑ m, ‖f i m‖^3))/3 := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset D)) =>
    lineMax_scalar_product_bound D (f i) (u i) (hu i) (fun j => ‖g i j‖) (fun j => norm_nonneg _))
  simpa only [← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum] using hs

def jumpScalarConstant : ℝ := 2+48*Real.sqrt 2

lemma jumpScalarConstant_pos : 0 < jumpScalarConstant := by unfold jumpScalarConstant; positivity

lemma sum_jumpMax_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) :
    (∑ i, ∑ j, ‖A 0 i j‖*jumpMax D A i j) ≤
      jumpScalarConstant * (∑ v, ∑ i, ∑ j, ‖A v i j‖^3) := by
  have hu : Function.Injective (fun i : D => (i:ℤ)) := Subtype.val_injective
  have hn (i : D) : Function.Injective (fun j : D => -(i:ℤ)-(j:ℤ)) := by
    intro j k hjk
    apply Subtype.ext
    dsimp at hjk
    omega
  have hX := sum_lineMax_scalar_product_bound D (fun i m => A 0 i m) (fun i j => A 0 i j)
    (fun _ j => (j:ℤ)) (fun _ => hu)
  have hY := sum_lineMax_scalar_product_bound D (fun j m => A 0 m j) (fun j i => A 0 i j)
    (fun _ i => (i:ℤ)) (fun _ => hu)
  have hH := sum_lineMax_scalar_product_bound D (fun i m => A 2 m i) (fun i j => A 0 i j)
    (fun i j => -(i:ℤ)-(j:ℤ)) hn
  have hK := sum_lineMax_scalar_product_bound D (fun j m => A 1 j m) (fun j i => A 0 i j)
    (fun j i => -(j:ℤ)-(i:ℤ)) hn
  have hc (v : Three) : (∑ j : D, ∑ i : D, ‖A v i j‖^3) = ∑ i : D, ∑ j : D, ‖A v i j‖^3 := by rw [Finset.sum_comm]
  rw [hc] at hY hH hK
  have hYe : (∑ j : D, ∑ i : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 0 m j‖^2) (i:ℤ)) =
      ∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 0 m j‖^2) (i:ℤ) := by rw [Finset.sum_comm]
  rw [hYe] at hY
  have hKe : (∑ j : D, ∑ i : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 1 j m‖^2) (-(j:ℤ)-(i:ℤ))) =
      ∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 1 j m‖^2) (-(i:ℤ)-(j:ℤ)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    omega
  rw [hKe] at hK
  have hb (v : Three) : 0 ≤ ∑ i : D, ∑ j : D, ‖A v i j‖^3 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => pow_nonneg (norm_nonneg _) _))
  have he : (∑ i : D, ∑ j : D, ‖A 0 i j‖*jumpMax D A i j) =
      2*(∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 0 i m‖^2) j)+
      2*(∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 0 m j‖^2) i)+
      (∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 2 m i‖^2) (-(i:ℤ)-(j:ℤ)))+
      (∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 1 j m‖^2) (-(i:ℤ)-(j:ℤ))) := by
    simp only [jumpMax,mul_add,Finset.sum_add_distrib,Finset.mul_sum,
      mul_left_comm]
  rw [he,Fin.sum_univ_three]
  unfold jumpScalarConstant
  nlinarith [hb 0,hb 1,hb 2,Real.sqrt_nonneg (2:ℝ)]
end
end TriangularHilbert.Heat
end

end OAI
