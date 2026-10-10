import OAI.NumberTheory.Ostmann.Characters.PrimitiveCharacterReduction
import OAI.NumberTheory.Ostmann.Arithmetic.CRTResidueAverage

namespace OAI

/-! # Product characters and their active conductor support -/
namespace Ostmann
open scoped Classical BigOperators

theorem character_prod_apply {I : Type*} {N : ℕ} (S : Finset I)
    (χ : I → DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    (∏ i ∈ S, χ i) u = ∏ i ∈ S, χ i u := by
  induction S using Finset.induction_on with
  | empty => simp [MulChar.one_apply_coe]
  | @insert i S hi ih => simp only [Finset.prod_insert hi, MulChar.mul_apply, ih]

noncomputable def sparseProductCharacter {I : Type*} [Fintype I]
    (p : I → ℕ) (χ : ∀ i, DirichletCharacter ℂ (p i)) :
    DirichletCharacter ℂ (∏ i, p i) :=
  ∏ i, DirichletCharacter.changeLevel (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (χ i)

theorem sparseProductCharacter_apply {I : Type*} [Fintype I]
    (p : I → ℕ) (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (u : (ZMod (∏ i, p i))ˣ) :
    sparseProductCharacter p χ u = ∏ i, χ i (crtUnitEquiv p hc u i) := by
  rw [sparseProductCharacter, character_prod_apply]
  apply Finset.prod_congr rfl
  intro i _
  rw [crtUnitEquiv_apply]
  simp only [DirichletCharacter.changeLevel_def, MulChar.ofUnitHom_coe, MonoidHom.comp_apply,
    MulChar.coe_toUnitHom, ZMod.unitsMap_def]
  rfl

theorem sparseProductCharacter_injective {I : Type*} [Fintype I]
    (p : I → ℕ) (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    Function.Injective (sparseProductCharacter p) := by
  intro χ ψ he
  funext i
  apply MulChar.ext
  intro u
  let x : ∀ j, (ZMod (p j))ˣ := Pi.mulSingle i u
  have hh := congrArg (fun c : DirichletCharacter ℂ (∏ j, p j) =>
    c ((crtUnitEquiv p hc).symm x)) he
  simp only [sparseProductCharacter_apply p hc, MulEquiv.apply_symm_apply] at hh
  have hprod (θ : ∀ j, DirichletCharacter ℂ (p j)) : (∏ j, θ j (x j)) = θ i u := by
    calc
      _ = θ i (x i) := by
        apply Finset.prod_eq_single i
        · intro j _ hji
          simp [x, Pi.mulSingle, hji, MulChar.map_one]
        · intro hi
          exact (hi (Finset.mem_univ i)).elim
      _ = _ := by simp [x, Pi.mulSingle]
  rw [hprod, hprod] at hh
  exact hh

theorem sparseProductCharacter_factorsThrough {I : Type*} [Fintype I]
    (p : I → ℕ) (χ : ∀ i, DirichletCharacter ℂ (p i)) (S : Finset I)
    (hχ : ∀ i, i ∉ S → χ i = 1) :
    (sparseProductCharacter p χ).FactorsThrough (∏ i ∈ S, p i) := by
  have hSN : (∏ i ∈ S, p i) ∣ ∏ i, p i :=
    Finset.prod_dvd_prod_of_subset S Finset.univ p S.subset_univ
  let ψ : DirichletCharacter ℂ (∏ i ∈ S, p i) :=
    ∏ i : S, DirichletCharacter.changeLevel (Finset.dvd_prod_of_mem p i.property) (χ i)
  refine ⟨hSN, ψ, ?_⟩
  rw [show DirichletCharacter.changeLevel hSN ψ =
      ∏ i ∈ S, DirichletCharacter.changeLevel (Finset.dvd_prod_of_mem p (Finset.mem_univ i))
        (χ i) by
    dsimp [ψ]
    rw [map_prod]
    calc
      _ = ∏ i : S, DirichletCharacter.changeLevel
          (Finset.dvd_prod_of_mem p (Finset.mem_univ i.val)) (χ i) := by
        apply Finset.prod_congr rfl
        intro i _
        exact (DirichletCharacter.changeLevel_trans (χ i) _ hSN).symm
      _ = _ := Finset.prod_coe_sort S (fun i : I => DirichletCharacter.changeLevel
        (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (χ i))]
  symm
  change (∏ i ∈ S, _) = ∏ i, _
  apply Finset.prod_subset S.subset_univ
  intro i _ hi
  rw [hχ i hi, map_one]

end Ostmann

end OAI
