import Mathlib
import OAI.Analysis.Commutator.CenteredContractionDensity
import OAI.Analysis.Commutator.CountableUnitaryTests
import OAI.Analysis.Commutator.WordCoefficientContinuity

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology

open Filter

namespace Kadison.FinitePatching

open Words

abbrev NonzeroInteger := {k : ℤ // k≠0}

def integerEnumeration : ℕ → NonzeroInteger :=
  letI := Encodable.ofCountable NonzeroInteger
  fun n => (Encodable.decode (α:=NonzeroInteger) n).getD ⟨1,by norm_num⟩

lemma integerEnumeration_surjective : Function.Surjective integerEnumeration := by
  let := Encodable.ofCountable NonzeroInteger
  intro k
  refine ⟨Encodable.encode k,?_⟩
  simp [integerEnumeration,Encodable.encodek]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H) (hRM : R ≤ M)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n,Fintype (ι n)] [∀ n,LinearOrder (ι n)]
  [∀ n,Nonempty (ι n)]

variable (stage : ∀ n,Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ},n ≤ m → (stage n).range ≤ (stage m).range)

include hRM hτ hmono in
theorem exists_all_unitary_tests [TopologicalSpace.SeparableSpace τ.GNS]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (ι n) (ι n) ℂ),stage n a*b=b*stage n a) →
      ∃ c : ℂ,b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R) :
    ∃ u : ℕ → unitary M, (∀ n, ((u n:M) : H →L[ℂ] H)∈R) ∧
      (∀ k : ℤ,k≠0 → Tendsto (fun n => τ ((PartialUnitary.ofUnitary (u n)).power k)) atTop (𝓝 0)) ∧
      (∀ (J K : Type) (x : J → M) (k : K → ℤ), (∀ j,‖x j‖≤1) →
        (∀ j,τ (x j)=0) → (∀ i,k i≠0) →
        ∀ l : List (Letter J K), l≠[] → Valid l →
          Tendsto (fun n => τ (word x k (PartialUnitary.ofUnitary (u n)) l)) atTop (𝓝 0)) := by
  classical
  obtain ⟨x,hx,hxc,hxd⟩ := TracialL2.exists_centered_contraction_dense_sequence τ
  obtain ⟨u,huR,hpow,hword⟩ := exists_countable_unitary_tests M R hRM τ hτ stage hmono
    hnormal hfaith hone hirr hgrow hstage hdiffuse x (fun i => (integerEnumeration i).val)
    hx hxc (fun i => (integerEnumeration i).property)
  refine ⟨u,huR,?_,?_⟩
  · intro k hk
    obtain ⟨i,hi⟩ := integerEnumeration_surjective ⟨k,hk⟩
    simpa only [hi] using hpow i
  · intro J K y k hy hyc hk l hl hv
    choose g hg using (fun i => integerEnumeration_surjective ⟨k i,hk i⟩)
    have hl' (l' : List (Letter ℕ K)) (hne : l'≠[]) (hvl : Valid l') :
        Tendsto (fun n => τ (word x k (PartialUnitary.ofUnitary (u n)) l')) atTop (𝓝 0) := by
      have hh := hword (l'.map (mapLetter id g)) (by simpa using hne) (valid_map id g hvl)
      have he : (fun i => (integerEnumeration i).val) ∘ g=k := by
        funext i
        exact congrArg Subtype.val (hg i)
      simpa only [word_reindex,Function.comp_id,he] using hh
    exact moment_limit_of_dense_coefficients τ hτ hone x k hx hxd
      (fun n => PartialUnitary.ofUnitary (u n)) hl' y hy hyc l hl hv

end Kadison.FinitePatching

end

end
end

end OAI
