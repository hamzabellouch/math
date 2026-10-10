import Mathlib
import OAI.Analysis.Commutator.AbstractFreeCornerFromUnitary
import OAI.Analysis.Commutator.AllUnitaryTests
import OAI.Analysis.Commutator.ConstantSequenceClosedTransport
import OAI.Analysis.Commutator.UnitaryEquivMoments

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Matrix.Norms.L2Operator Topology

open Filter

namespace Kadison.TracialSequence

open FinitePatching FinitePatching.ConjugatedWords

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (M R : VonNeumannAlgebra H) (hRM : R ≤ M) (e : A ≃⋆ₐ[ℂ] M) (j : R →⋆ₐ[ℂ] A)
    (hj : ∀ q,e (j q)=NormalSubalgebra.inclusion M R hRM q)

variable (τ : A →ₚ[ℂ] ℂ) (σ : M →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (size : ℕ → ℕ)

variable (stage : ∀ n,Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] M)

variable (inc : ∀ {n m : ℕ},n ≤ m → Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ]
  Matrix (Fin (size m+1)) (Fin (size m+1)) ℂ)

include hRM hj in
theorem exists_freeCornerPosition_of_equiv_tower [TopologicalSpace.SeparableSpace σ.GNS]
    (htrace : ∀ a,σ (e a)=τ a)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hσ : ∀ a b : M,σ (a*b)=σ (b*a))
    (hω : (ω : Filter ℕ) ≤ atTop)
    (hnormal : NormalGNS.BoundedWOTContinuous M σ)
    (hfaith : ∀ a : M,σ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ),
      stage n a*b=b*stage n a) → ∃ c : ℂ,b=algebraMap ℂ M c)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hinc : ∀ n m (h : n ≤ m) a,stage m (inc h a)=stage n a)
    (hgrow : Tendsto (fun n => (size n+1:ℝ)) atTop atTop)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R) :
    Nonempty (FreeCornerPosition τ ω R j) := by
  have hσone : σ 1=1 := by rw [←map_one e,htrace,hone]
  have hmono : ∀ {n m : ℕ},n ≤ m → (stage n).range ≤ (stage m).range := by
    intro n m h a ha
    obtain ⟨b,rfl⟩ := ha
    exact ⟨inc h b,hinc n m h b⟩
  obtain ⟨u,huR,_,huword⟩ := exists_all_unitary_tests M R hRM σ hσ stage hmono
    hnormal hfaith hσone hirr (by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hgrow)
    hstage hdiffuse
  let v := fun n => pullUnitary e (u n)
  have hfree := sequenceUnitary_free τ ω hτ hω v (pullUnitary_moment_limits e τ σ htrace u (by
    intro J x hx hxc l hl hv
    exact huword J Bool x signPower hx hxc (by intro b; cases b <;> norm_num [signPower]) l hl hv))
  let stageA := fun n => e.symm.toStarAlgHom.comp (stage n)
  have hfaithA (a : A) (ha : τ (star a*a)=0) : a=0 := by
    apply (show Function.Injective e from e.injective)
    rw [map_zero]
    apply hfaith
    rw [←map_star e,←map_mul e,htrace,ha]
  have hirrA (b : A) (hb : ∀ n a,stageA n a*b=b*stageA n a) :
      ∃ c : ℂ,b=algebraMap ℂ A c := by
    obtain ⟨c,hc⟩ := hirr (e b) (by
      intro n a
      have hh := congrArg e (hb n a)
      have hsa : e (stageA n a)=stage n a := e.apply_symm_apply _
      simpa only [map_mul,hsa] using hh)
    refine ⟨c,(show Function.Injective e from e.injective) ?_⟩
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one]
    exact hc
  have hstageA (n : ℕ) (a : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ) : stageA n a∈Set.range j := by
    refine ⟨⟨stage n a,hstage n a⟩,(show Function.Injective e from e.injective) ?_⟩
    rw [hj]
    change (stage n a)=e (e.symm (stage n a))
    rw [e.apply_symm_apply]
  apply freeCornerPosition_of_unitary_abstract R j τ ω size stageA inc hτ hω
    (constant_range_bicommutant_of_equiv τ ω M e σ hτ htrace hnormal) hfaithA hone hirrA hstageA
    (fun n m h a => congrArg e.symm (hinc n m h a)) _ (sequenceUnitary τ ω v)
    (pullUnitary_in_relative_range M R hRM e j hj τ ω u huR) hfree
  intro n q
  have he := (tendsto_atTop.1 hgrow) (q:ℝ)
  obtain ⟨m,hmq,hmn⟩ := (he.and (eventually_ge_atTop n)).exists
  exact ⟨m,hmn,by exact_mod_cast hmq⟩

end Kadison.TracialSequence

end

end
end

end OAI
