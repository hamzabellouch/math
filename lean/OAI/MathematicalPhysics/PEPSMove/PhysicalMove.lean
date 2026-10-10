import Mathlib
import OAI.MathematicalPhysics.PEPSMove.PhysicalCoordinates

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open Matrix

namespace PolynomialPEPS.PhysicalMove.LocalMove
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

                                                                        
                                                      
def spectralPower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (a : ℝ) : Matrix ι ι ℂ :=
  cfc (fun s : ℝ => Real.rpow s a) A

                                                                           
                                                                        
def Subdensity {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : Prop :=
  A.PosSemidef ∧ (Matrix.trace A).re ≤ 1

                                                                        
                                                          
def moveVector {L q : ℕ} (θ : State L q) (X P Y : Finset (Vertex L))
    (σ : Matrix (RegionConfiguration q (X∪P)) (RegionConfiguration q (X∪P)) ℂ)
    (τ : Matrix (RegionConfiguration q (X∪Y)) (RegionConfiguration q (X∪Y)) ℂ)
    (a : ℝ) : State L q :=
  asMap (liftLocal (X∪P) (spectralPower σ (a/2)) *
    liftLocal P (spectralPower (reducedDensity θ P) (-a/2)) *
    liftLocal (X∪Y) (spectralPower τ (a/2)) *
    liftLocal Y (spectralPower (reducedDensity θ Y) (-a/2))) θ

def eta {L q : ℕ} (θ : State L q) (X P Y : Finset (Vertex L)) : ℝ :=
  vonNeumannEntropy θ (X∪P)-vonNeumannEntropy θ P+
    vonNeumannEntropy θ (X∪Y)-vonNeumannEntropy θ Y

def ell {L : ℕ} (q : ℕ) (X : Finset (Vertex L)) : ℝ :=
  Real.log (Real.exp 1*(Fintype.card (RegionConfiguration q X):ℝ))

                                                                          
                                                                      
                                                                         
                                                                        
                                                                           
                                                                            
def OneCopyMoveBound : Prop :=
  ∃ C : ℝ, 0<C ∧ ∃ c : ℝ, 0<c ∧
    ∀ (L q : ℕ), 2≤q → ∀ (θ : State L q), ‖θ‖=1 →
    ∀ (X P Y : Finset (Vertex L)), Disjoint X P → Disjoint X Y → Disjoint P Y →
    ∀ (σ : Matrix (RegionConfiguration q (X∪P)) (RegionConfiguration q (X∪P)) ℂ)
      (τ : Matrix (RegionConfiguration q (X∪Y)) (RegionConfiguration q (X∪Y)) ℂ),
    Subdensity σ → Subdensity τ → ∀ a : ℝ, 0<a → a*ell q X≤c →
    ‖moveVector θ X P Y σ τ a‖ ≤
      Real.exp (-a*eta θ X P Y/2+C*Real.rpow a (5/4:ℝ)*(ell q X)^2)

end PolynomialPEPS.PhysicalMove.LocalMove
namespace PolynomialPEPS.PhysicalMove.LocalMovePhysical
open Matrix QuantumSSA SupportedCurve SpectralCurve MatrixInterpolation LocalMove
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
variable {L q : ℕ}

theorem asMap_mul_apply (A B : Operator L q) (ψ : State L q) :
    asMap (A*B) ψ=asMap A (asMap B ψ) := by
  simp only [asMap,map_mul,mul_apply_eq_comp]

theorem fourCoefficient_move (θ : State L q) (X P Y : Finset (Vertex L))
    (hXP : Disjoint X P) (hXY : Disjoint X Y) (hPY : Disjoint P Y)
    (σ : Matrix (RegionConfiguration q (X∪P)) (RegionConfiguration q (X∪P)) ℂ)
    (τ : Matrix (RegionConfiguration q (X∪Y)) (RegionConfiguration q (X∪Y)) ℂ)
    (hσ : σ.PosSemidef) (hτ : τ.PosSemidef) (a : ℝ) :
    reshuffle (fourCoefficient (moveVector θ X P Y σ τ a) X Y P hXY hXP hPY.symm)=
      cfc (fun t : ℝ => Real.rpow t (a/2)) (reindexHom (unionEquiv X P hXP).symm σ)*
      tensorRightHom (spectralPower (reducedDensity θ P) (-a/2))*
      reshuffle (cfc (fun t : ℝ => Real.rpow t (a/2)) (reindexHom (unionEquiv X Y hXY).symm τ)*
        tensorRightHom (spectralPower (reducedDensity θ Y) (-a/2))*
        fourCoefficient θ X Y P hXY hXP hPY.symm) := by
  simp only [moveVector,asMap_mul_apply]
  rw [fourCoefficient_action_XP,fourCoefficient_action_P,
    fourCoefficient_action_XY,fourCoefficient_action_Y,
    cfc_reindex _ _ hσ.isHermitian,cfc_reindex _ _ hτ.isHermitian]
  simp only [spectralPower,Matrix.mul_assoc]
  rfl

theorem fourCoefficient_eta (θ : State L q) (X P Y : Finset (Vertex L))
    (hXP : Disjoint X P) (hXY : Disjoint X Y) (hPY : Disjoint P Y) :
    QuantumSSA.conditionalEntropy (fourCoefficient θ X Y P hXY hXP hPY.symm*
      (fourCoefficient θ X Y P hXY hXP hPY.symm).conjTranspose)+
    QuantumSSA.conditionalEntropy (reshuffle (fourCoefficient θ X Y P hXY hXP hPY.symm)*
      (reshuffle (fourCoefficient θ X Y P hXY hXP hPY.symm)).conjTranspose)=eta θ X P Y := by
  rw [QuantumSSA.conditionalEntropy,QuantumSSA.conditionalEntropy,
    fourCoefficient_gram,fourCoefficient_reshuffle_gram,
    density_union_ptrL,density_union_ptrL,
    entropy_reindexHom _ (reducedDensity_isHermitian θ (X∪Y)),
    entropy_reindexHom _ (reducedDensity_isHermitian θ (X∪P))]
  simp only [traceEntropy_spectral _ (reducedDensity_isHermitian _ _),eta,vonNeumannEntropy]
  ring

theorem one_copy_move_bound : OneCopyMoveBound := by
  refine ⟨200000,by norm_num,1/8,by norm_num,?_⟩
  intro L q hq θ hθ X P Y hXP hXY hPY σ τ hσ hτ a ha hsmall
  have hqpos : 0<q := by omega
  let : NeZero q := ⟨ne_of_gt hqpos⟩
  let C := fourCoefficient θ X Y P hXY hXP hPY.symm
  have hC : hsEnergy C=1 := by
    have hh := coefficient_hsEnergy θ (X∪Y) (unionEquiv X Y hXY)
      (complementEquiv (X∪Y) P ((X∪Y)∪P)ᶜ (Finset.disjoint_union_left.mpr ⟨hXP,hPY.symm⟩) rfl)
    simpa only [C,fourCoefficient,hθ,one_pow] using hh
  have hdim : (1:ℝ)≤(Fintype.card (RegionConfiguration q X):ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty (RegionConfiguration q X))))
  have hlid : ell q X=1+Real.log (Fintype.card (RegionConfiguration q X):ℝ) := by
    rw [ell,Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt (by linarith)),Real.log_exp]
  have hl : 1≤ell q X := by rw [hlid]; have := Real.log_nonneg hdim; linarith
  have hl' : Real.log (Fintype.card (RegionConfiguration q X):ℝ)≤ell q X := by rw [hlid]; linarith
  have hh := one_copy_move_cfc C hC
    (reindexHom (unionEquiv X P hXP).symm σ) (reindexHom (unionEquiv X Y hXY).symm τ)
    (reindexHom_posSemidef _ hσ.1) (reindexHom_posSemidef _ hτ.1)
    (by rw [reindexHom_trace]; exact hσ.2) (by rw [reindexHom_trace]; exact hτ.2)
    a (ell q X) ha hl hl' hsmall
  have hY : ptrL (C*C.conjTranspose)=reducedDensity θ Y := by
    dsimp only [C]
    rw [fourCoefficient_gram,density_union_ptrL]
  have hP : ptrL (reshuffle C*(reshuffle C).conjTranspose)=reducedDensity θ P := by
    dsimp only [C]
    rw [fourCoefficient_reshuffle_gram,density_union_ptrL]
  have he : QuantumSSA.conditionalEntropy (C*C.conjTranspose)+
      QuantumSSA.conditionalEntropy (reshuffle C*(reshuffle C).conjTranspose)=eta θ X P Y :=
    fourCoefficient_eta θ X P Y hXP hXY hPY
  rw [hY,hP,he] at hh
  change ‖flattenCLM (_*tensorRightHom (spectralPower (reducedDensity θ P) (-a/2))*
    reshuffle (_*tensorRightHom (spectralPower (reducedDensity θ Y) (-a/2))*
      fourCoefficient θ X Y P hXY hXP hPY.symm))‖≤_ at hh
  rw [←fourCoefficient_move θ X P Y hXP hXY hPY σ τ hσ.1 hτ.1 a,
    fourCoefficient_norm] at hh
  exact hh

end PolynomialPEPS.PhysicalMove.LocalMovePhysical

end

end OAI
