import OAI.InformationTheory.Entanglement.ProjectionMain

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace ProjectionCriterion
open ChannelCompletion TensorCriterion

lemma hsAdjoint_left_ad {n m p : Type} [Fintype n] [Fintype m] [Fintype p]
    [DecidableEq n] {F : Map n m} (hF : CP F) (S : Matrix p m ℂ) :
    hsAdjoint ((ad S).comp F)=(hsAdjoint F).comp (ad Sᴴ) := by
  ext X i j
  have he (Y : Mat n) : Matrix.trace (Y*hsAdjoint ((ad S).comp F) X)=
      Matrix.trace (Y*hsAdjoint F (ad Sᴴ X)) := by
    rw [trace_hsAdjoint (cp_comp (cp_ad S) hF),trace_hsAdjoint hF]
    simp only [LinearMap.comp_apply,ad_apply,Matrix.conjTranspose_conjTranspose]
    calc
      Matrix.trace (S*F Y*Sᴴ*X)=Matrix.trace (S*(F Y*Sᴴ*X)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((F Y*Sᴴ*X)*S) := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  change hsAdjoint ((ad S).comp F) X i j=hsAdjoint F (ad Sᴴ X) i j
  simpa only [Matrix.trace_single_mul,one_smul] using he (Matrix.single j i 1)

namespace Data
variable {Q K : Type} [Fintype Q] [Fintype K] [DecidableEq Q] [DecidableEq K]
  {D n : ℕ} (d : Data Q K (Fin D) (Fin n)) (h : D ≤ n)

def firstCoordinates (_d : Data Q K (Fin D) (Fin n)) (h : D ≤ n) :
    Matrix (Fin n) (Fin D) ℂ := coord (Fin.castLE h)
def Xi1 : Map (Fin n) (Fin n) := (ad (d.firstCoordinates h)).comp d.Psi
def Xi2 : Map (Fin n) (Fin n) := (hsAdjoint d.Psi).comp (ad (d.firstCoordinates h)ᴴ)

omit [DecidableEq K] in
lemma Xi1_ppt : PPT (d.Xi1 h) := ppt_ad_comp d.Psi_ppt _
omit [DecidableEq K] in
lemma Xi2_ppt : PPT (d.Xi2 h) := ppt_comp_cp d.adjoint_ppt (cp_ad _)
omit [DecidableEq K] in
lemma Xi2_adjoint : d.Xi2 h=hsAdjoint (d.Xi1 h) := (hsAdjoint_left_ad d.Psi_cp _).symm
omit [DecidableEq K] in
lemma Xi_composite : (d.Xi2 h).comp (d.Xi1 h)=(hsAdjoint d.Psi).comp d.Psi := by
  ext X a b
  simp only [Xi1,Xi2,LinearMap.comp_apply,ad_apply,Matrix.conjTranspose_conjTranspose]
  have hh : (d.firstCoordinates h)ᴴ*d.firstCoordinates h=1 :=
    coord_isometry _ (Fin.castLE_injective h)
  have he : (d.firstCoordinates h)ᴴ*((d.firstCoordinates h)*d.Psi X*(d.firstCoordinates h)ᴴ)*
      (d.firstCoordinates h)=d.Psi X := by
    calc
      _ = ((d.firstCoordinates h)ᴴ*d.firstCoordinates h)*d.Psi X*
          ((d.firstCoordinates h)ᴴ*d.firstCoordinates h) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hh,Matrix.one_mul,Matrix.mul_one]
  rw [he]
lemma Xi_not_eb [Nonempty Q] [Nonempty K] [NeZero D] :
    ¬ EntanglementBreaking ((d.Xi2 h).comp (d.Xi1 h)) := by
  intro heb
  rw [d.Xi_composite h] at heb
  exact d.C_nonseparable (eb_choi heb)
end Data

theorem square_embedding {Q K : Type} [Fintype Q] [Fintype K]
    [DecidableEq Q] [DecidableEq K] [Nonempty Q] [Nonempty K]
    {D n : ℕ} [NeZero D] (d : Data Q K (Fin D) (Fin n)) (h : D ≤ n) :
    PPT (d.Xi1 h) ∧ PPT (d.Xi2 h) ∧ d.Xi2 h=hsAdjoint (d.Xi1 h) ∧
    (d.Xi2 h).comp (d.Xi1 h)=(hsAdjoint d.Psi).comp d.Psi ∧
    ¬ EntanglementBreaking ((d.Xi2 h).comp (d.Xi1 h)) := by
  exact ⟨d.Xi1_ppt h,d.Xi2_ppt h,d.Xi2_adjoint h,d.Xi_composite h,d.Xi_not_eb h⟩

end ProjectionCriterion

end

end OAI
