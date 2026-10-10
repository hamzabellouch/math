import OAI.Analysis.TriangularHilbert.FiniteDual

namespace OAI

universe uι uκ

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

def matrixCubic {ι : Type uι} [Fintype ι] (B : Matrix ι ι ℂ) (h : ℝ) : ℝ := ∑ i, ∑ j, h^2*‖B i j‖^3

def momentConstant : ℝ := 4*hardPairingConstant*(hardPairingConstant+1)
lemma momentConstant_pos : 0 < momentConstant := by
  unfold momentConstant
  have hp := hardPairingConstant_pos
  positivity

lemma hardOutput_moment (D : Finset ℤ) (B C : Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    (r R : Matrix D D ℝ) (hr : ∀ i j, h ≤ r i j) (hb : ∀ i j, r i j ≤ R i j) :
    (∑ i, ∑ j, h^2*complexMoment (kernelOutput B C h (fun m => h*(m:ℤ))
      (fun i j => hardKernel (r i j) (R i j)) i j)) ≤
      momentConstant*(matrixCubic B h+matrixCubic C h) := by
  classical
  let u : D×D → ℂ := fun p => kernelOutput B C h (fun m => h*(m:ℤ))
    (fun i j => hardKernel (r i j) (R i j)) p.1 p.2
  have HH (f : D×D → ℂ) : ‖∑ p, (h^2:ℝ)*f p*u p‖ ≤ hardPairingConstant*
      ((∑ p, h^2*‖f p‖^3)+(matrixCubic B h+matrixCubic C h)) := by
    let A : Three → Matrix D D ℂ := ![fun i j => f (i,j),B,C]
    have ha := hardPairing_le D A hh r R hr hb
    have hA0 : A 0 = fun i j => f (i,j) := rfl
    have hA1 : A 1 = B := rfl
    have hA2 : A 2 = C := rfl
    simpa only [kernelPairing,arrayCubic,Fin.sum_univ_three,hA0,hA1,hA2,
      Fintype.sum_prod_type,matrixCubic,u,add_assoc] using ha
  have hh' := finite_cubic_dual u (fun _ => h^2) (fun _ => sq_nonneg h) hardPairingConstant_pos HH
  simpa only [Fintype.sum_prod_type,u,complexMoment,momentConstant] using hh'

lemma finiteHardOutput_moment (D : Finset ℤ) (B C : Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (r R : κ → ℝ)
    (hr : ∀ k, h ≤ r k) (hb : ∀ k, r k ≤ R k) :
    (∑ i, ∑ j, h^2*finiteMoment (fun k => kernelOutput B C h (fun m => h*(m:ℤ))
      (fun _ _ => hardKernel (r k) (R k)) i j)) ≤
      momentConstant*(matrixCubic B h+matrixCubic C h) := by
  classical
  let U (i j : D) (k : κ) := kernelOutput B C h (fun m => h*(m:ℤ))
    (fun _ _ => hardKernel (r k) (R k)) i j
  choose s hs using (fun i j : D => finiteMoment_eq (U i j))
  have ha := hardOutput_moment D B C hh (fun i j => r (s i j)) (fun i j => R (s i j))
    (fun i j => hr (s i j)) (fun i j => hb (s i j))
  have he (i j : D) : finiteMoment (U i j) = complexMoment (kernelOutput B C h (fun m => h*(m:ℤ))
      (fun i j => hardKernel (r (s i j)) (R (s i j))) i j) := hs i j
  simp_rw [← he] at ha
  exact ha
end
end TriangularHilbert.Heat
end

end OAI
