import OAI.Geometry.NodalSets.Elliptic.RealEllipticLinearity

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section

lemma real_coordDiv_add (F G : Yau.Jets.Coord → Yau.Jets.Coord)
    (hF : ∀ i, ContDiff ℝ ∞ (fun x ↦ F x i)) (hG : ∀ i, ContDiff ℝ ∞ (fun x ↦ G x i))
    (x : Yau.Jets.Coord) :
    Yau.coordDiv (fun y i ↦ F y i+G y i) x = Yau.coordDiv F x+Yau.coordDiv G x := by
  simp only [Yau.coordDiv,Yau.real_coordPartial_add _ _ (hF _) (hG _),Finset.sum_add_distrib]

lemma real_coordDiv_partial (F : Yau.Jets.Coord → Yau.Jets.Coord)
    (hF : ∀ i, ContDiff ℝ ∞ (fun x ↦ F x i)) (x : Yau.Jets.Coord) (k : Fin 4) :
    Yau.coordPartial (Yau.coordDiv F) x k =
      Yau.coordDiv (fun y i ↦ Yau.coordPartial (fun z ↦ F z i) y k) x := by
  unfold Yau.coordDiv
  rw [Yau.real_coordPartial_sum _ (fun i ↦ Yau.real_coordPartial_smooth _ (hF i) i)]
  apply Finset.sum_congr rfl; intro i _
  exact Yau.real_coordPartial_commute _ (hF i) x k i

def realDerivativeErrorFlux (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (W : Yau.Jets.Coord → ℝ) (k : Fin 4) (x : Yau.Jets.Coord) (i : Fin 4) : ℝ :=
  ∑ j, Yau.coordPartial (fun y ↦ C y i j) x k*Yau.coordPartial W x j

lemma realDerivativeErrorFlux_smooth (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (W : Yau.Jets.Coord → ℝ) (k : Fin 4)
    (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) (hW : ContDiff ℝ ∞ W) (i : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ realDerivativeErrorFlux C W k x i) :=
  ContDiff.sum (fun j _ ↦ (Yau.real_coordPartial_smooth _ (hC i j) k).mul
    (Yau.real_coordPartial_smooth W hW j))

lemma realMatrixFlux_partial (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (W : Yau.Jets.Coord → ℝ) (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j))
    (hW : ContDiff ℝ ∞ W) (x : Yau.Jets.Coord) (i k : Fin 4) :
    Yau.coordPartial (fun y ↦ realMatrixFlux C W y i) x k =
      realDerivativeErrorFlux C W k x i+realMatrixFlux C (fun y ↦ Yau.coordPartial W y k) x i := by
  unfold realMatrixFlux realDerivativeErrorFlux
  rw [Yau.real_coordPartial_sum _ (fun j ↦ (hC i j).mul (Yau.real_coordPartial_smooth W hW j))]
  simp only [Yau.real_coordPartial_mul _ _ (hC i _) (Yau.real_coordPartial_smooth W hW _),
    Yau.real_coordPartial_commute W hW x k,Finset.sum_add_distrib]

theorem real_differentiated_density_equation (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V W : Yau.Jets.Coord → ℝ) (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j))
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (he : ∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) (k : Fin 4) (x : Yau.Jets.Coord) :
    Yau.coordDiv (realMatrixFlux C (fun y ↦ Yau.coordPartial W y k)) x+V x*Yau.coordPartial W x k =
      -Yau.coordDiv (realDerivativeErrorFlux C W k) x-Yau.coordPartial V x k*W x := by
  have hflux := realMatrixFlux_smooth C W hC hW
  have hdiv : ContDiff ℝ ∞ (Yau.coordDiv (realMatrixFlux C W)) :=
    ContDiff.sum (fun i _ ↦ Yau.real_coordPartial_smooth _ (hflux i) i)
  have hefun : (fun y ↦ Yau.coordDiv (realMatrixFlux C W) y+V y*W y) = fun _ ↦ 0 := funext he
  have hd : Yau.coordPartial (fun y ↦ Yau.coordDiv (realMatrixFlux C W) y+V y*W y) x k=0 := by
    rw [hefun]; simp [Yau.coordPartial]
  rw [Yau.real_coordPartial_add _ _ hdiv (hV.mul hW),
    Yau.real_coordPartial_mul _ _ hV hW,real_coordDiv_partial _ hflux] at hd
  have hpart : (fun y i ↦ Yau.coordPartial (fun z ↦ realMatrixFlux C W z i) y k) =
      fun y i ↦ realDerivativeErrorFlux C W k y i+realMatrixFlux C (fun z ↦ Yau.coordPartial W z k) y i := by
    funext y i; exact realMatrixFlux_partial C W hC hW y i k
  rw [hpart,real_coordDiv_add _ _ (realDerivativeErrorFlux_smooth C W k hC hW)
    (realMatrixFlux_smooth C _ hC (Yau.real_coordPartial_smooth W hW k))] at hd
  linarith

lemma real_density_equation_of_weighted (gamma potential W : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (hgp : ∀ x, gamma x ≠ 0)
    (he : ∀ x, realEllipticResidual gamma potential B W x = 0) :
    ∀ x, Yau.coordDiv (realMatrixFlux (fun y i j ↦ gamma y*B y i j) W) x+
      (gamma x*potential x)*W x=0 := by
  have hflux : realMatrixFlux (fun y i j ↦ gamma y*B y i j) W =
      fun y i ↦ gamma y*realMatrixFlux B W y i := by
    funext y i
    simp only [realMatrixFlux,Finset.mul_sum,mul_assoc]
  intro x
  have hh := congrArg (fun t : ℝ ↦ gamma x*t) (he x)
  unfold realEllipticResidual realWeightedElliptic Yau.weightedDiv at hh
  rw [mul_add,← mul_assoc,mul_inv_cancel₀ (hgp x),one_mul,mul_zero] at hh
  rw [hflux]
  nlinarith only [hh]

end
end Yau.Geometry

end OAI
