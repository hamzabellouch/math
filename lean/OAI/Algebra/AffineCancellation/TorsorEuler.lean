import OAI.Algebra.AffineCancellation.ReplicaLift
import OAI.Algebra.AffineCancellation.LaurentEuler
import OAI.Algebra.AffineCancellation.Intertwining

namespace OAI

noncomputable section

namespace ComplexCancellation.Torsor
open LaurentPolynomial
variable {P : Type*} [CommRing P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P) (Q : Frame ρ)
lemma frameMap_intertwining (r : Determinant.T) :
    LaurentEuler.derivation (k := ℂ) (frameMap ρ Q r)=frameMap ρ Q (Determinant.Euler r) := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (Ideal.span {Determinant.relation}) r
  apply DerivationIntertwining.mvPolynomial (frameMap ρ Q) Determinant.Euler LaurentEuler.derivation Determinant.π p
  intro i
  fin_cases i
  · change LaurentEuler.derivation (k := ℂ) (frameMap ρ Q Determinant.a)=frameMap ρ Q (Determinant.Euler Determinant.a)
    rw [Determinant.Euler_a,frameMap_a,LaurentEuler.monomial,one_zsmul]
  · change LaurentEuler.derivation (k := ℂ) (frameMap ρ Q Determinant.d)=frameMap ρ Q (Determinant.Euler Determinant.d)
    rw [Determinant.Euler_d,frameMap_d,LaurentEuler.monomial,one_zsmul]
  · change LaurentEuler.derivation (k := ℂ) (frameMap ρ Q Determinant.b)=frameMap ρ Q (Determinant.Euler Determinant.b)
    rw [Determinant.Euler_b,map_neg,frameMap_b,LaurentEuler.monomial,neg_one_zsmul]
  · change LaurentEuler.derivation (k := ℂ) (frameMap ρ Q Determinant.c)=frameMap ρ Q (Determinant.Euler Determinant.c)
    rw [Determinant.Euler_c,map_neg,frameMap_c,LaurentEuler.monomial,neg_one_zsmul]
  · change LaurentEuler.derivation (k := ℂ) (frameMap ρ Q Determinant.u)=frameMap ρ Q (Determinant.Euler Determinant.u)
    rw [Determinant.Euler_u,map_zero,frameMap_u,LaurentEuler.coefficient]
lemma forwardEuler_τ : LaurentEuler.derivation (k := ℂ) (forward ρ Q Bundle.τ)=0 := by
  rw [forward_τ]
  exact LaurentEuler.coefficient _
lemma forwardEuler_j (r : Determinant.T) :
    LaurentEuler.derivation (k := ℂ) (forward ρ Q (Bundle.j r))=forward ρ Q (Bundle.fiberEuler (Bundle.j r)) := by
  change _=forward ρ Q (AffineModification.euler _ _ _ (AffineModification.coefficientHom (k := ℂ) _ r))
  rw [AffineModification.euler_coefficient,forward_j,frameMap_intertwining]
  exact (forward_j ρ Q (Determinant.Euler r)).symm
variable [IsDomain P]
lemma forwardEuler_V (hρ : Function.Injective ρ) :
    LaurentEuler.derivation (k := ℂ) (forward ρ Q Bundle.V)=2*forward ρ Q Bundle.V := by
  have hτ : forward ρ Q Bundle.τ≠0 := by rw [forward_τ]; exact base_p_ne_zero ρ hρ
  apply mul_left_cancel₀ (pow_ne_zero 2 hτ)
  have he := congrArg (LaurentEuler.derivation (k := ℂ) : L (P := P) → L (P := P))
    (congrArg (forward ρ Q) Bundle.equation)
  rw [map_mul,map_pow,Derivation.leibniz,Derivation.leibniz_pow,forwardEuler_τ,
    smul_zero,smul_zero,smul_zero,add_zero,smul_eq_mul,forward_j,frameMap_intertwining,
    Determinant.Euler_v,map_mul,map_ofNat] at he
  rw [he,← forward_j,← Bundle.equation,map_mul,map_pow]
  ring
lemma forward_intertwining (hρ : Function.Injective ρ) (r : Bundle.B) :
    LaurentEuler.derivation (k := ℂ) (forward ρ Q r)=forward ρ Q (Bundle.fiberEuler r) := by
  change r ∈ DerivationIntertwining.subalgebra (forward ρ Q) Bundle.fiberEuler LaurentEuler.derivation
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective Determinant.T (Ideal.span {AffineModification.rel Determinant.T Determinant.v}) r
  change AffineModification.π Determinant.T Determinant.v p ∈ _
  induction p using MvPolynomial.induction_on with
  | C a => exact forwardEuler_j ρ Q a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    apply mul_mem hp
    fin_cases i
    · change LaurentEuler.derivation (k := ℂ) (forward ρ Q Bundle.τ)=forward ρ Q (Bundle.fiberEuler Bundle.τ)
      rw [forwardEuler_τ]
      change 0=forward ρ Q (AffineModification.euler _ _ _ (AffineModification.τ _ _))
      rw [AffineModification.euler_τ,map_zero]
    · change LaurentEuler.derivation (k := ℂ) (forward ρ Q Bundle.V)=forward ρ Q (Bundle.fiberEuler Bundle.V)
      rw [forwardEuler_V ρ Q hρ]
      change _=forward ρ Q (AffineModification.euler _ _ _ (AffineModification.V _ _))
      rw [AffineModification.euler_V,map_mul,map_ofNat]
      rfl
lemma replica_commute (hρ : Function.Injective ρ) (hf : Function.Injective (forward ρ Q))
    (Dp : Derivation ℂ P P) (E : Derivation ℂ Bundle.B Bundle.B) (c : Degeneration.G)
    (hs : ∀ b, forward ρ Q (E b)=base ρ c*LaurentDerivation.extension Dp (forward ρ Q b))
    (b : Bundle.B) : Bundle.fiberEuler (E b)=E (Bundle.fiberEuler b) := by
  apply hf
  rw [← forward_intertwining ρ Q hρ,hs,hs,← forward_intertwining ρ Q hρ]
  exact LaurentEuler.commute_replica Dp (ρ c) (forward ρ Q b)
end ComplexCancellation.Torsor

end

end OAI
