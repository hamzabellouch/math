import Mathlib
import OAI.Analysis.Commutator.CornerPhaseSelectionCore
import OAI.Analysis.Commutator.NormalSubalgebra
import OAI.Analysis.Commutator.NormalTraceProjection
import OAI.Analysis.Commutator.PartialUnitaryAlgebra
import OAI.Analysis.Commutator.TracialL2Continuity

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.CornerPhase

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M N : VonNeumannAlgebra H) (hNM : N ≤ M)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

include hτ hNM in
theorem exists_relative_corner_phase {J : Type*} [Fintype J]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0)
    (hN : DiffuseProjection.HasNoMinimalProjections N)
    (q : M) (hq : IsStarProjection q) (hqN : (q : H →L[ℂ] H)∈N)
    (hqt : 0<(τ q).re)
    (a : J → M) (k : J → ℕ) (hk : ∀ j,0<k j) {ε : ℝ} (hε : 0<ε) :
    ∃ u : M, star u*u=q ∧ u*star u=q ∧ u*q=u ∧ q*u=u ∧ ‖u‖ ≤ 1 ∧
      (∀ j, ‖τ (u^k j*a j)‖<ε*(τ q).re) ∧ (u : H →L[ℂ] H)∈N := by
  classical
  obtain ⟨L,hL⟩ := exists_nat_gt ((∑ j,‖a j‖^2)/ε^2)
  obtain ⟨n,hn,hprime⟩ := Nat.exists_infinite_primes (max L (1+Finset.univ.sup k))
  have hLn : L ≤ n := (le_max_left _ _).trans hn
  have hkn (j : J) : k j<n := by
    have hj := Finset.le_sup (s:=Finset.univ) (f:=k) (Finset.mem_univ j)
    have hh : 1+Finset.univ.sup k ≤ n := (le_max_right _ _).trans hn
    omega
  let : Fact n.Prime := ⟨hprime⟩
  let : NeZero n := ⟨hprime.ne_zero⟩
  have hnpos : 0<(n:ℝ) := Nat.cast_pos.mpr hprime.pos
  have hbudget : (∑ j,‖a j‖^2)<(n:ℝ)*ε^2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hε)).mp
    exact hL.trans_le (by exact_mod_cast hLn)
  let ι := NormalSubalgebra.inclusion M N hNM
  let σ := NormalSubalgebra.trace M N hNM τ
  let qN : N := ⟨q,hqN⟩
  have hqNproj : IsStarProjection qN := by
    constructor
    · exact Subtype.ext (congrArg (fun a : M => (a : H →L[ℂ] H)) hq.isIdempotentElem.eq)
    · exact Subtype.ext (congrArg (fun a : M => (a : H →L[ℂ] H)) hq.isSelfAdjoint.star_eq)
  obtain ⟨p,hp,ho,hsum⟩ := NormalGNS.exists_projection_partition N σ
    (NormalSubalgebra.tracial M N hNM τ hτ)
    (NormalSubalgebra.normal M N hNM τ hnormal)
    (NormalSubalgebra.faithful M N hNM τ hfaith) hN
    n qN hqNproj (t:=(τ q).re/n) (by positivity) (by change (τ q).re=_; field_simp)
  let e : ZMod n → M := fun i => ι (p ((ZMod.finEquiv n).symm i))
  have he : ∀ i,IsStarProjection (e i) := fun i => (hp _).1.map ι
  have heo : ∀ i j,i≠j → e i*e j=0 := by
    intro i j hij
    change ι (p _)*ι (p _)=0
    rw [←map_mul,ho _ _ (fun hh => hij ((ZMod.finEquiv n).symm.injective hh)),map_zero]
  have hep : ∑ i,e i=q := by
    change ∑ i,ι (p ((ZMod.finEquiv n).symm i))=ι qN
    rw [←map_sum,←hsum]
    congr 1
    exact Fintype.sum_equiv (ZMod.finEquiv n).symm.toEquiv _ _ (fun _ => rfl)
  obtain ⟨u,h1,h2,h3,h4,h5,h6,hmem⟩ := exists_phase_finite τ hτ e he heo q hq hep
    (fun _ => (hp _).2.2) hqt a k (fun j => ⟨hk j,hkn j⟩) hε hbudget
  refine ⟨u,h1,h2,h3,h4,h5,h6,?_⟩
  exact hmem (N.toStarSubalgebra.comap M.toStarSubalgebra.subtype)
    (fun i => (p _).property)

include hτ hNM in
theorem exists_relative_signed_phase {J : Type*} [Fintype J]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0)
    (hN : DiffuseProjection.HasNoMinimalProjections N)
    (q : M) (hq : IsStarProjection q) (hqN : (q : H →L[ℂ] H)∈N)
    (hqt : 0<(τ q).re)
    (a : J → M) (k : J → ℤ) (hk : ∀ j,k j≠0) {ε : ℝ} (hε : 0<ε) :
    ∃ u : FinitePatching.PartialUnitary M, u.support=q ∧
      (∀ j, ‖τ (u.power (k j)*a j)‖<ε*(τ q).re) ∧ (u.val : H →L[ℂ] H)∈N := by
  let b : J → M := fun j => match k j with
    | .ofNat _ => a j
    | .negSucc _ => star (a j)
  obtain ⟨u,h1,h2,h3,h4,_,hu,hmem⟩ := exists_relative_corner_phase M N hNM τ hτ
    hnormal hfaith hN q hq hqN hqt b (fun j => (k j).natAbs)
    (fun j => Int.natAbs_pos.mpr (hk j)) hε
  let v : FinitePatching.PartialUnitary M := ⟨u,q,hq,h1,h2,h3,h4⟩
  refine ⟨v,rfl,?_,hmem⟩
  intro j
  have hj := hu j
  cases he : k j with
  | ofNat n =>
    cases n with
    | zero => exact (hk j he).elim
    | succ n =>
      change ‖τ (u^(n+1)*a j)‖<ε*(τ q).re
      simpa only [b,he,Int.natAbs_ofNat',Int.natAbs_negSucc] using hj
  | negSucc n =>
    change ‖τ ((star u)^(n+1)*a j)‖<ε*(τ q).re
    rw [←star_pow,TracialL2.norm_trace_star_mul τ hτ]
    simpa only [b,he,Int.natAbs_ofNat',Int.natAbs_negSucc] using hj

end Kadison.CornerPhase

end

end
end

end OAI
