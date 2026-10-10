import Mathlib
import OAI.Analysis.Commutator.FiniteStandardGauge

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace Kadison.MatrixTower

open OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι]

local instance finiteStandardRangeIndexDecidableEq : DecidableEq ι := Classical.decEq ι

private lemma diagonal_range_of_closed_range
    {A K : Type*} [CStarAlgebra A]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (N : VonNeumannAlgebra K)
    (hN : ∀ b : K →L[ℂ] K, b∈N ↔ ∃ a : A, π a=b)
    (T : SumSpace (H:=K) ι →L[ℂ] SumSpace (H:=K) ι) :
    T∈NormalGNS.bicommutant (((diagonal (H:=K) ι).comp π).range) ↔
      ∃ a : A, diagonal (H:=K) ι (π a)=T := by
  let ρ := (diagonal (H:=K) ι).comp π
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  let Q := diagonalVonNeumann ι i₀ N
  have hQ : (Q : Set (SumSpace (H:=K) ι →L[ℂ] SumSpace (H:=K) ι))=Set.range ρ := by
    ext S
    change (∃ b∈N,diagonal (H:=K) ι b=S) ↔ ∃ a : A,ρ a=S
    constructor
    · rintro ⟨b,hb,hbS⟩
      obtain ⟨a,rfl⟩ := (hN b).mp hb
      exact ⟨a,hbS⟩
    · rintro ⟨a,rfl⟩
      exact ⟨π a,(hN _).mpr ⟨a,rfl⟩,rfl⟩
  change T∈NormalGNS.bicommutant ρ.range ↔ ∃ a : A,ρ a=T
  rw [NormalGNS.mem_bicommutant]
  change T∈Set.centralizer (Set.centralizer (Set.range ρ)) ↔ T∈Set.range ρ
  rw [←hQ,Q.centralizer_centralizer]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

theorem finiteStandard_range
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι) :
    T∈finiteStandardAlgebra ι M τ ↔
      ∃ a : M,diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)=T := by
  let N := NormalGNS.bicommutant τ.gnsStarAlgHom.range
  have hrange := NormalGNS.range_bicommutant M τ hτ hnormal
  have hN := fun b => (NormalGNS.mem_bicommutant τ.gnsStarAlgHom.range b).trans
    (Set.ext_iff.mp hrange b)
  exact diagonal_range_of_closed_range ι τ.gnsStarAlgHom N hN T

end Kadison.MatrixTower

end

end OAI
