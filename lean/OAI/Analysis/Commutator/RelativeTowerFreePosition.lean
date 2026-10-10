import Mathlib
import OAI.Analysis.Commutator.AllUnitaryTests
import OAI.Analysis.Commutator.FreeCornerFromUnitary
import OAI.Analysis.Commutator.FreeSequenceUnitary

namespace OAI

noncomputable section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Matrix.Norms.L2Operator Topology

open Filter

namespace Kadison.TracialSequence

open FinitePatching FinitePatching.ConjugatedWords

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H) (hRM : R≤M)

variable (τ : M →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (size : ℕ → ℕ)

variable (stage : ∀ n,Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] M)

variable (inc : ∀ {n m : ℕ},n ≤ m → Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ]
  Matrix (Fin (size m+1)) (Fin (size m+1)) ℂ)

theorem exists_freeCornerPosition_of_relative_tower [TopologicalSpace.SeparableSpace τ.GNS]
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤atTop)
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ),
      stage n a*b=b*stage n a) → ∃ c : ℂ,b=algebraMap ℂ M c)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hinc : ∀ n m (h : n ≤ m) a,stage m (inc h a)=stage n a)
    (hgrow : Tendsto (fun n => (size n+1:ℝ)) atTop atTop)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R) :
    Nonempty (FreeCornerPosition τ ω R (NormalSubalgebra.inclusion M R hRM)) := by
  have hmono : ∀ {n m : ℕ},n ≤ m → (stage n).range≤(stage m).range := by
    intro n m h a ha
    obtain ⟨b,rfl⟩ := ha
    exact ⟨inc h b,hinc n m h b⟩
  obtain ⟨u,huR,_,huword⟩ := exists_all_unitary_tests M R hRM τ hτ stage hmono
    hnormal hfaith hone hirr (by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hgrow)
    hstage hdiffuse
  refine freeCornerPosition_of_unitary M R hRM τ ω size stage inc hτ hω hnormal hfaith hone hirr
    hstage hinc ?_ (sequenceUnitary τ ω u) (sequenceUnitary_in_relative_range M R hRM τ ω u huR) ?_
  · intro n q
    have he := (tendsto_atTop.1 hgrow) (q:ℝ)
    obtain ⟨m,hmn,hm⟩ := (he.and (eventually_ge_atTop n)).exists
    exact ⟨m,hm,by exact_mod_cast hmn⟩
  · apply sequenceUnitary_free τ ω hτ hω u
    intro J x hx hxc l hl hv
    exact huword J Bool x signPower hx hxc (by intro b; cases b <;> norm_num [signPower]) l hl hv

end Kadison.TracialSequence
end
end

end OAI
