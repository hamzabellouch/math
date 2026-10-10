import Mathlib
import OAI.Analysis.FreeWords.FactorStructure
import OAI.Analysis.FreeWords.MatrixCorner

namespace OAI

noncomputable section

namespace KKMatrixQuantization

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vnaCentralizer (s : Set (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ s
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (Set.centralizer (s ∪ star s))) = _
    exact Set.centralizer_centralizer_centralizer _

def vnaMeet (M N : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := M.toStarSubalgebra ⊓ N.toStarSubalgebra
  centralizer_centralizer' := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨by
        have hh := Set.centralizer_subset (Set.centralizer_subset (show
          (M.toStarSubalgebra ⊓ N.toStarSubalgebra : Set (H →L[ℂ] H)) ⊆ M from fun _ h => h.1)) hx
        simpa only [M.centralizer_centralizer,VonNeumannAlgebra.coe_toStarSubalgebra] using hh,
        by
        have hh := Set.centralizer_subset (Set.centralizer_subset (show
          (M.toStarSubalgebra ⊓ N.toStarSubalgebra : Set (H →L[ℂ] H)) ⊆ N from fun _ h => h.2)) hx
        simpa only [N.centralizer_centralizer,VonNeumannAlgebra.coe_toStarSubalgebra] using hh⟩
    · exact Set.subset_centralizer_centralizer

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : VonNeumannAlgebra H}

variable (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] ConcreteAlgebra M)

def matrixCommutant : VonNeumannAlgebra H :=
  vnaMeet M (vnaCentralizer (Set.range fun a : Matrix ι ι ℂ => (ρ a : H →L[ℂ] H)))

theorem mem_matrixCommutant (x : H →L[ℂ] H) :
    x ∈ matrixCommutant ρ ↔ x ∈ M ∧ ∀ i j, Commute x ((matrixUnit ρ i j : ConcreteAlgebra M) : H →L[ℂ] H) := by
  change (x ∈ M ∧ x ∈ StarSubalgebra.centralizer ℂ _) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · rintro ⟨hx,hc⟩
    refine ⟨hx,fun i j => ?_⟩
    exact ((hc _ ⟨Matrix.single i j 1,rfl⟩).1).symm
  · rintro ⟨hx,hc⟩
    refine ⟨hx,?_⟩
    have ha (a : Matrix ι ι ℂ) : Commute x (ρ a : H →L[ℂ] H) := by
      change Commute x ((M.toStarSubalgebra.subtype.comp ρ) a)
      rw [matrix_representation]
      apply Commute.sum_right
      intro i hi
      apply Commute.sum_right
      intro j hj
      exact (hc i j).smul_right (a i j)
    rintro y ⟨a,rfl⟩
    exact ⟨(ha a).eq.symm,by
      have hh := (ha (star a)).eq.symm
      rw [map_star] at hh
      exact hh⟩

def commutantInclusion : ConcreteAlgebra (matrixCommutant ρ) →⋆ₐ[ℂ] ConcreteAlgebra M where
  toFun x := ⟨x.val,((mem_matrixCommutant ρ _).mp x.property).1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem commutantInclusion_injective : Function.Injective (commutantInclusion ρ) :=
  fun _ _ h => Subtype.ext (congrArg (fun z : ConcreteAlgebra M => z.val) h)

def inCommutant (x : ConcreteAlgebra M) (hx : ∀ i j, Commute x (matrixUnit ρ i j)) :
    ConcreteAlgebra (matrixCommutant ρ) :=
  ⟨x.val,(mem_matrixCommutant ρ _).mpr ⟨x.property,fun i j => congrArg Subtype.val (hx i j).eq⟩⟩

@[simp] theorem inclusion_inCommutant (x : ConcreteAlgebra M) (hx) :
    commutantInclusion ρ (inCommutant ρ x hx)=x := rfl

theorem inclusion_commute (x : ConcreteAlgebra (matrixCommutant ρ)) (i j : ι) :
    Commute (commutantInclusion ρ x) (matrixUnit ρ i j) := by
  apply Subtype.ext
  exact ((mem_matrixCommutant ρ _).mp x.property).2 i j

theorem matrixCommutant_factor [Nonempty ι] (hF : IsFactor M) : IsFactor (matrixCommutant ρ) := by
  intro x hx
  let o : ι := Classical.choice inferInstance
  obtain ⟨c,hc⟩ := hF (commutantInclusion ρ x) (commute_of_matrix_coordinates ρ o _
    (inclusion_commute ρ x) (fun y => by
      have hh := congrArg (commutantInclusion ρ) (hx (inCommutant ρ (cornerLift ρ o y) (cornerLift_commute ρ o y))).eq
      change _ * _ = _ * _
      simpa only [map_mul,inclusion_inCommutant] using hh))
  refine ⟨c, ?_⟩
  apply commutantInclusion_injective ρ
  exact hc

end

end KKMatrixQuantization
end

end OAI
