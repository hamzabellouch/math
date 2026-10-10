import OAI.Algebra.OddKaplansky.WeightedGram

namespace OAI

universe portUniverse1 portUniverse2

section
namespace OddKaplansky.PolynomialGrid
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} [Field K] [Fintype K] [DecidableEq K]

lemma card_units_zero_le (n : ℕ) (P : MvPolynomial (Fin n) K) (hP : P ≠ 0) :
    Fintype.card {f : Fin n → Kˣ // MvPolynomial.eval (fun i => (f i : K)) P = 0} * Fintype.card Kˣ ≤
      P.totalDegree * Fintype.card Kˣ ^ n := by
  let S : Finset K := Finset.univ.erase 0
  let Z := {f ∈ Fintype.piFinset (fun _ : Fin n => S) | MvPolynomial.eval f P = 0}
  have hS : S.card = Fintype.card Kˣ := by
    simp only [S,Finset.card_erase_of_mem (Finset.mem_univ (0 : K)),Finset.card_univ]
    exact (Fintype.card_units (α := K)).symm
  let e : {f : Fin n → Kˣ // MvPolynomial.eval (fun i => (f i : K)) P = 0} ≃ Z := {
    toFun := fun f => ⟨fun i => (f.val i : K), by
      apply Finset.mem_filter.mpr
      constructor
      · apply Fintype.mem_piFinset.mpr
        intro i
        simp only [S, Finset.mem_erase,Finset.mem_univ,and_true]
        exact Units.ne_zero _
      · exact f.property⟩
    invFun := fun f => ⟨fun i => Units.mk0 (f.val i) (by
      have h := (Fintype.mem_piFinset.mp (Finset.mem_filter.mp f.property).1) i
      exact (Finset.mem_erase.mp h).1), (Finset.mem_filter.mp f.property).2⟩
    left_inv := fun f => by ext i; rfl
    right_inv := fun f => rfl }
  have hz : Fintype.card {f : Fin n → Kˣ // MvPolynomial.eval (fun i => (f i : K)) P = 0} = Z.card :=
    (Fintype.card_congr e).trans (Fintype.card_coe Z)
  have hs := MvPolynomial.schwartz_zippel_totalDegree hP S
  change (Z.card : ℚ≥0)/(S.card : ℚ≥0)^n ≤ (P.totalDegree : ℚ≥0)/S.card at hs
  have hp : (0 : ℚ≥0) < S.card := by rw [hS]; exact_mod_cast Fintype.card_pos (α := Kˣ)
  have hm := (div_le_div_iff₀ (pow_pos hp n) hp).mp hs
  rw [hz,← hS]
  exact_mod_cast hm

lemma card_units_zero_le_general {X : Type portUniverse2} [Fintype X] (P : MvPolynomial X K) (hP : P ≠ 0) :
    Fintype.card {f : X → Kˣ // MvPolynomial.eval (fun i => (f i : K)) P = 0} * Fintype.card Kˣ ≤
      P.totalDegree * Fintype.card Kˣ ^ Fintype.card X := by
  let e := Fintype.equivFin X
  let Q := MvPolynomial.rename e P
  have hQ : Q ≠ 0 := by
    intro h
    apply hP
    apply MvPolynomial.rename_injective e e.injective
    simpa only [map_zero] using h
  let E : {f : X → Kˣ // MvPolynomial.eval (fun i => (f i : K)) P = 0} ≃
      {f : Fin (Fintype.card X) → Kˣ // MvPolynomial.eval (fun i => (f i : K)) Q = 0} := {
    toFun := fun f => ⟨fun i => f.val (e.symm i),by
      simpa only [Q,MvPolynomial.eval_rename,Function.comp_def,Equiv.symm_apply_apply] using f.property⟩
    invFun := fun f => ⟨fun i => f.val (e i),by
      simpa only [Q,MvPolynomial.eval_rename,Function.comp_def] using f.property⟩
    left_inv := fun f => by ext i; simp only [Equiv.symm_apply_apply]
    right_inv := fun f => by ext i; simp only [Equiv.apply_symm_apply] }
  have h := card_units_zero_le (Fintype.card X) Q hQ
  rw [← Fintype.card_congr E] at h
  exact h.trans (Nat.mul_le_mul_right _ (MvPolynomial.totalDegree_rename_le e P))

end
end OddKaplansky.PolynomialGrid

end

end OAI
