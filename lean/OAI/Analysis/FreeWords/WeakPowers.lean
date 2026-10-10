import Mathlib
import OAI.Analysis.FreeWords.CyclicBasis
import OAI.Analysis.FreeWords.MatrixReindex
import OAI.Analysis.FreeWords.MatrixSubfactor

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKFactorSupport KKProjectionSupport KKMatrixQuantization

noncomputable section

def embeddedShift {G A : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    (ρ : Matrix G G ℂ →⋆ₐ[ℂ] A) : Multiplicative G →* unitary A :=
  let f : Matrix G G ℂ →⋆* A := {
    toFun := ρ
    map_one' := map_one ρ
    map_mul' := map_mul ρ
    map_star' := map_star ρ }
  (Unitary.map f).toMonoidHom.comp shiftHom

@[simp] theorem embeddedShift_val {G A : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    (ρ : Matrix G G ℂ →⋆ₐ[ℂ] A) (g : G) :
    (embeddedShift ρ (Multiplicative.ofAdd g)).val = ρ (shiftMatrix g) := rfl

@[simp] theorem embeddedShift_power {G A : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    (ρ : Matrix G G ℂ →⋆ₐ[ℂ] A) (g : G) (k : ℤ) :
    ((embeddedShift ρ (Multiplicative.ofAdd g))^k).val = ρ (shiftMatrix (k • g)) := by
  rw [← map_zpow]
  rfl

theorem weakly_small_powers
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} [Fintype ι]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hF : IsFactor M) (hD : IsDiffuse M)
    (x : ι → ConcreteAlgebra M) (k : ι → ℤ) (hk : ∀ i, k i ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary (ConcreteAlgebra M),
      ∀ i, ‖τ.map ((u^(k i) : unitary (ConcreteAlgebra M)).val*x i)‖ < ε := by
  classical
  let S := ∑ i, (traceNorm τ (x i))^2
  obtain ⟨N,hN⟩ := exists_nat_gt (S/ε^2)
  let K := Finset.univ.sup (fun i => (k i).natAbs)
  obtain ⟨p,hpN,hpPrime⟩ := Nat.exists_infinite_primes (N+K+1)
  have : Fact (Nat.Prime p) := ⟨hpPrime⟩
  have : NeZero p := ⟨hpPrime.ne_zero⟩
  have hp : 0<p := hpPrime.pos
  have hep : S < (p:ℝ)*ε^2 := by
    have hNp : N≤p := by omega
    have hsp : S/ε^2 < (p:ℝ) := hN.trans_le (Nat.cast_le.mpr hNp)
    exact (div_lt_iff₀ (sq_pos_of_pos hε)).mp hsp
  have hkz (i : ι) : (k i : ZMod p) ≠ 0 := by
    intro hz
    have hd : (p:ℤ) ∣ k i := (ZMod.intCast_zmod_eq_zero_iff_dvd (k i) p).mp hz
    have hd' : p ∣ (k i).natAbs := by exact_mod_cast Int.natAbs_dvd_natAbs.mpr hd
    have hK : (k i).natAbs≤K := Finset.le_sup (f:=fun i => (k i).natAbs) (Finset.mem_univ i)
    have hpos : 0<(k i).natAbs := Int.natAbs_pos.mpr (hk i)
    have hle := Nat.le_of_dvd hpos hd'
    omega
  obtain ⟨ρ,_,hρ⟩ := exists_matrix_subfactor M τ hF hD p hp
  let e : Fin p ≃ ZMod p := (ZMod.finEquiv p).toEquiv
  let σ := ρ.comp (matrixReindex e.symm)
  have hσ (a : Matrix (ZMod p) (ZMod p) ℂ) :
      τ.map (σ a)=(Fintype.card (ZMod p):ℂ)⁻¹*Matrix.trace a := by
    rw [show σ a=ρ (matrixReindex e.symm a) from rfl,hρ,ZMod.card]
    congr 1
    exact Fintype.sum_equiv e _ _ (fun i => rfl)
  let f (g : ZMod p) (i : ι) := ‖τ.map (σ (shiftMatrix ((k i : ZMod p)*g))*x i)‖^2
  have hsum (i:ι) : ∑ g, f g i ≤ (traceNorm τ (x i))^2 := by
    have heq : ∑ g, f g i=∑ g:ZMod p, ‖τ.map (σ (shiftMatrix g)*x i)‖^2 :=
      Fintype.sum_equiv (Equiv.mulLeft₀ (k i : ZMod p) (hkz i)) _ _ (fun _ => rfl)
    rw [heq]
    exact cyclic_bessel τ σ hσ (x i)
  have htotal : (∑ g:ZMod p, ∑ i, f g i) < ∑ g:ZMod p, ε^2 := by
    rw [Finset.sum_comm,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
    exact (Finset.sum_le_sum (fun i _ => hsum i)).trans_lt hep
  obtain ⟨g,_,hg⟩ := Finset.exists_lt_of_sum_lt htotal
  refine ⟨embeddedShift σ (Multiplicative.ofAdd g),fun i => ?_⟩
  rw [embeddedShift_power,zsmul_eq_mul]
  have hi : f g i≤∑ j, f g j := Finset.single_le_sum (fun j _ => show 0≤f g j from sq_nonneg _) (Finset.mem_univ i)
  have hh : ‖τ.map (σ (shiftMatrix ((k i : ZMod p)*g))*x i)‖^2 < ε^2 := hi.trans_lt hg
  nlinarith [norm_nonneg (τ.map (σ (shiftMatrix ((k i : ZMod p)*g))*x i))]

end

end KKLocalPatching
end

end OAI
