import OAI.InformationTheory.Entanglement.CombinatorialAssembly
import OAI.InformationTheory.Entanglement.ProjectionReindex
import OAI.InformationTheory.Entanglement.ProjectionRealMain
import OAI.InformationTheory.Entanglement.ProjectionSquare
import OAI.Analysis.Quantum.PPTSquare.ChannelModel
import OAI.Analysis.Quantum.PPTSquare.TraceCompletion
import OAI.Analysis.Quantum.PPTSquare.Compression
import OAI.Analysis.Quantum.PPTSquare.ChannelCompletion

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace ProjectionCriterion.Data
variable {Q K D I D' I' : Type} [Fintype Q] [Fintype K] [Fintype D] [Fintype I]
  [Fintype D'] [Fintype I'] [DecidableEq Q] [DecidableEq K] [DecidableEq D]
  [DecidableEq I] [DecidableEq D'] [DecidableEq I']
omit [DecidableEq K] [DecidableEq I'] in
lemma real_reindex (d : Data Q K D I) (eD : D' ≃ D) (eI : I' ≃ I)
    (hr : d.RealProjections) : (d.reindex eD eI).RealProjections :=
  fun i a b => hr (eI i) (eD a) (eD b)
end ProjectionCriterion.Data
namespace FiniteConstruction
open ChannelCompletion TensorCriterion SecretKey ProjectionCriterion

lemma Q_pos : 0 < Q := pow_pos b_pos 3
lemma D_pos : 0 < D := pow_pos (by norm_num : (0:ℕ)<4) L
instance questionNonempty : Nonempty Question :=
  Fintype.card_pos_iff.mp (question_card.symm ▸ Q_pos)
instance dNeZero : NeZero D := ⟨ne_of_gt D_pos⟩
lemma D_le_m : D ≤ m := by
  have h : 1 ≤ Q := Q_pos
  simpa only [m,one_mul] using (Nat.mul_le_mul_right D h : 1*D ≤ Q*D)

def concreteData : ProjectionCriterion.Data Question Coordinate (Fin D) (Fin m) :=
  data.reindex outputEnumeration labelEnumeration
lemma data_real : data.RealProjections := by
  intro i a b
  change (P i a b).im=0
  have h := congrArg Complex.im (P_real i a b)
  simp only [Complex.star_def,Complex.conj_im] at h
  linarith
lemma concrete_real : concreteData.RealProjections :=
  ProjectionCriterion.Data.real_reindex data outputEnumeration labelEnumeration data_real

def Psi : Map (Fin m) (Fin D) := concreteData.Psi
def Lambda : Map (Fin D) (Fin m) := hsAdjoint Psi
def localChannel : Map (Fin D) (Fin m) := concreteData.localChannel
def rho : Mat (Fin m × Fin m) := concreteData.rho
def Phi1 : Map (Fin m) (Fin m) := concreteData.Xi1 D_le_m
def Phi2 : Map (Fin m) (Fin m) := concreteData.Xi2 D_le_m
def Theta : Map (Space m) (Space m) := theta m Phi1 Phi2

lemma localChannel_exact : localChannel=((Q : ℂ)⁻¹) • Lambda := by
  simp only [localChannel,ProjectionCriterion.Data.localChannel,question_card,
    Complex.ofReal_inv,Complex.ofReal_natCast,Lambda,Psi]
lemma rho_exact : rho=((Q : ℂ)^2*(D : ℂ))⁻¹ • choi (Lambda.comp Psi) := by
  simp only [rho,ProjectionCriterion.Data.rho,ProjectionCriterion.Data.C,question_card,
    Fintype.card_fin,Complex.ofReal_inv,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_natCast,Lambda,Psi]
lemma Phi1_ppt : PPT Phi1 := concreteData.Xi1_ppt D_le_m
lemma Phi2_ppt : PPT Phi2 := concreteData.Xi2_ppt D_le_m
lemma pair_identification : choi (Phi2.comp Phi1)=((Q : ℂ)^2*(D : ℂ)) • rho := by
  have hq : (Q : ℂ)≠0 := Nat.cast_ne_zero.mpr (ne_of_gt Q_pos)
  have hd : (D : ℂ)≠0 := Nat.cast_ne_zero.mpr (ne_of_gt D_pos)
  rw [rho_exact,smul_smul]
  rw [mul_inv_cancel₀ (mul_ne_zero (pow_ne_zero _ hq) hd),one_smul]
  exact congrArg choi (concreteData.Xi_composite D_le_m)
lemma composite_nonseparable : ¬ Separable (choi (Phi2.comp Phi1)) := by
  change ¬ Separable (choi ((concreteData.Xi2 D_le_m).comp (concreteData.Xi1 D_le_m)))
  rw [concreteData.Xi_composite D_le_m]
  exact concreteData.C_nonseparable
lemma pair_not_eb : ¬ EntanglementBreaking (Phi2.comp Phi1) := concreteData.Xi_not_eb D_le_m
lemma theta_ppt : PPT Theta := ChannelCompletion.theta_ppt m Phi1_ppt Phi2_ppt
lemma theta_tp : TracePreserving Theta := theta_tracePreserving m Phi1 Phi2
lemma theta_corner :
    (W0 m ⊗ₖ W0 m)ᴴ*choi (Theta.comp Theta)*(W0 m ⊗ₖ W0 m)=
      (((coefficient Phi1*coefficient Phi2 : ℝ) : ℂ)*((Q : ℂ)^2*(D : ℂ))) • rho := by
  rw [Theta,choi_corner,pair_identification,smul_smul]
lemma theta_not_eb : ¬ EntanglementBreaking (Theta.comp Theta) :=
  (channel_completion m Phi1 Phi2 Phi1_ppt Phi2_ppt).2.2.2.2.2.2.2.2 composite_nonseparable

theorem combinatorial_algebraic_clauses :
    (κ : ℝ)<(Q : ℝ)/(K : ℝ) ∧
    PPT localChannel ∧ TracePreserving localChannel ∧
    rho=tensorMap localChannel localChannel (projector (ProjectionCriterion.Phi D)) ∧
    rho=((Q : ℂ)^2*(D : ℂ))⁻¹ • choi (Lambda.comp Psi) ∧
    rho.PosSemidef ∧ Matrix.trace rho=1 ∧ Represented rho ∧ ¬ Separable rho ∧
    PPT Phi1 ∧ PPT Phi2 ∧ Phi2=hsAdjoint Phi1 ∧
    choi (Phi2.comp Phi1)=((Q : ℂ)^2*(D : ℂ)) • rho ∧
    ¬ EntanglementBreaking (Phi2.comp Phi1) ∧
    0<coefficient Phi1 ∧ 0<coefficient Phi2 ∧
    Fintype.card (Space m)=2*m+1 ∧
    (W0 m)ᴴ*W0 m=1 ∧ (∀ i j, (W0 m i j).im=0) ∧
    PPT Theta ∧ TracePreserving Theta ∧
    (W0 m ⊗ₖ W0 m)ᴴ*choi (Theta.comp Theta)*(W0 m ⊗ₖ W0 m)=
      (((coefficient Phi1*coefficient Phi2 : ℝ) : ℂ)*((Q : ℂ)^2*(D : ℂ))) • rho ∧
    ¬ EntanglementBreaking (Theta.comp Theta) := by
  exact ⟨strict_gap,concreteData.localChannel_ppt,concreteData.localChannel_tp,
    concreteData.rho_identification concrete_real,rho_exact,concreteData.rho_psd,
    concreteData.rho_trace,concreteData.rho_represented concrete_real,
    concreteData.rho_nonseparable,Phi1_ppt,Phi2_ppt,concreteData.Xi2_adjoint D_le_m,
    pair_identification,pair_not_eb,coefficient_pos Phi1_ppt.1,coefficient_pos Phi2_ppt.1,
    dimension m,W0_isometry m,coord_real _,theta_ppt,theta_tp,theta_corner,theta_not_eb⟩

end FiniteConstruction

end

end OAI
