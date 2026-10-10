import OAI.RepresentationTheory.RestrictedTilting.GoodKernel
import OAI.RepresentationTheory.RestrictedTilting.TensorWeights

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe u
variable (k : Type u) [Field k] [Infinite k]

lemma costandard_zero_tilting : IsTilting k (costandard k 0) :=
  costandard_tilting_of_choose_ne_zero k 0 (by intro i; fin_cases i; norm_num)
lemma costandard_one_tilting : IsTilting k (costandard k 1) :=
  costandard_tilting_of_choose_ne_zero k 1 (by intro i; fin_cases i <;> norm_num)

noncomputable def tensorPowerFrom (A : FDRep k (SL2 k)) : ℕ → FDRep k (SL2 k)
  | 0 => A
  | n+1 => tensorPowerFrom A n ⊗ costandard k 1

noncomputable def polynomialPowerMap (m : ℕ) : ∀ n,
    tensorPowerFrom k (costandard k m) n ⟶ costandard k (m+n)
  | 0 => 𝟙 _
  | n+1 => (tensorRight (costandard k 1)).map (polynomialPowerMap m n) ≫
      costandardMultiply k (m+n) 1

omit [Infinite k] in
lemma polynomialPowerMap_goodKernel (m n : ℕ) :
    HasGoodKernel k (polynomialPowerMap k m n) := by
  induction n with
  | zero => exact HasGoodKernel.id k _
  | succ n ih =>
    exact (ih.tensor_right k _ (costandard_hasGoodFiltration k 1)).comp k
      (costandardMultiply_goodKernel k (m+n) 1)

lemma tensorPowerFrom_tilting {A : FDRep k (SL2 k)} (hA : IsTilting k A) (n : ℕ) :
    IsTilting k (tensorPowerFrom k A n) := by
  induction n with
  | zero => exact hA
  | succ n ih => exact ih.tensor k (costandard_one_tilting k)

omit [Infinite k] in
lemma tensorPowerFrom_rational {A : FDRep k (SL2 k)}
    (hA : IsRational k A.ρ) (n : ℕ) : IsRational k (tensorPowerFrom k A n).ρ := by
  induction n with
  | zero => exact hA
  | succ n ih =>
    exact IsRational.tensor k (tensorPowerFrom k A n).ρ (costandard k 1).ρ ih
      (costandard_rational k 1)

lemma tensorPowerFrom_weights {A : FDRep k (SL2 k)}
    (hA : IsRational k A.ρ) (a : ℕ) (ha : HasWeightsBetween A.ρ (-(a : ℤ)) a) (n : ℕ) :
    HasWeightsBetween (tensorPowerFrom k A n).ρ (-((a+n : ℕ) : ℤ)) (a+n) := by
  induction n with
  | zero =>
    change HasWeightsBetween A.ρ (-((a+0 : ℕ) : ℤ)) (a+0)
    simpa only [Nat.add_zero, add_zero] using ha
  | succ n ih =>
    exact hasWeightsBetween_tensor (tensorPowerFrom k A n).ρ (costandard k 1).ρ
      (tensorPowerFrom_rational k hA n) (costandard_rational k 1) (a+n) 1 ih
      (fun m v hm hv => costandard_weight_bound k 1 m hm v hv)

 

omit [Infinite k] in
lemma tensorPowerFrom_factor (m n : ℕ) :
    Nonempty (tensorPowerFrom k (costandard k m) n ≅
      costandard k m ⊗ tensorPowerFrom k (costandard k 0) n) := by
  induction n with
  | zero =>
    have := costandardMultiply_isIso_of_zero k m 0 (Or.inr rfl)
    exact ⟨(asIso (costandardMultiply k m 0)).symm⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    exact ⟨(tensorRight (costandard k 1)).mapIso e ≪≫
      α_ (costandard k m) (tensorPowerFrom k (costandard k 0) n) (costandard k 1)⟩
end FiberFunctorProof

end OAI
