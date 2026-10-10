import Mathlib
import OAI.Analysis.Commutator.CornerPhaseSelectionCore
import OAI.Analysis.Commutator.NormalTraceProjection

namespace OAI

noncomputable section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.CornerPhase

section Represented

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

include hτ in
theorem exists_corner_phase {J : Type*} [Fintype J]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0)
    (hM : DiffuseProjection.HasNoMinimalProjections M)
    (q : M) (hq : IsStarProjection q) (hqt : 0<(τ q).re)
    (a : J → M) (k : J → ℕ) (hk : ∀ j,0<k j) {ε : ℝ} (hε : 0<ε) :
    ∃ u : M, star u*u=q ∧ u*star u=q ∧ u*q=u ∧ q*u=u ∧ ‖u‖ ≤ 1 ∧
      ∀ j, ‖τ (u^k j*a j)‖<ε*(τ q).re := by
  classical
  obtain ⟨L,hL⟩ := exists_nat_gt ((∑ j,‖a j‖^2)/ε^2)
  obtain ⟨N,hN,hprime⟩ := Nat.exists_infinite_primes (max L (1+Finset.univ.sup k))
  have hLN : L ≤ N := (le_max_left _ _).trans hN
  have hkN (j : J) : k j<N := by
    have hj := Finset.le_sup (s:=Finset.univ) (f:=k) (Finset.mem_univ j)
    have hh : 1+Finset.univ.sup k ≤ N := (le_max_right _ _).trans hN
    omega
  let : Fact N.Prime := ⟨hprime⟩
  let : NeZero N := ⟨hprime.ne_zero⟩
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hprime.pos
  have hbudget : (∑ j,‖a j‖^2)<(N:ℝ)*ε^2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hε)).mp
    exact hL.trans_le (by exact_mod_cast hLN)
  obtain ⟨p,hp,ho,hsum⟩ := NormalGNS.exists_projection_partition M τ hτ hnormal hfaith hM
    N q hq (t:=(τ q).re/N) (by positivity) (by field_simp)
  let e : ZMod N → M := fun i => p ((ZMod.finEquiv N).symm i)
  have he : ∀ i,IsStarProjection (e i) := fun i => (hp _).1
  have heo : ∀ i j,i≠j → e i*e j=0 := fun i j hij =>
    ho _ _ (fun hh => hij ((ZMod.finEquiv N).symm.injective hh))
  have hep : ∑ i,e i=q := by
    rw [←hsum]
    exact Fintype.sum_equiv (ZMod.finEquiv N).symm.toEquiv _ _ (fun _ => rfl)
  obtain ⟨u,h1,h2,h3,h4,h5,h6,_⟩ := exists_phase_finite τ hτ e he heo q hq hep
    (fun _ => (hp _).2.2) hqt a k (fun j => ⟨hk j,hkN j⟩) hε hbudget
  exact ⟨u,h1,h2,h3,h4,h5,h6⟩

end Represented

end Kadison.CornerPhase
end
end

end OAI
