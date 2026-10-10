import Mathlib.Data.Fintype.EquivFin
import OAI.Analysis.MutuallyUnbiased.Cubic.CubicHadamard
import OAI.Analysis.MutuallyUnbiased.Cubic.CubicBlock

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def enumerateThree (S : Finset Coord) (hS : S.card = 3) : Fin 3 ≃ S :=
  (Finset.equivFinOfCardEq hS).symm

theorem sum_enumerateThree (S : Finset Coord) (hS : S.card = 3) (f : Coord → ℂ) :
    (∑ i, f (enumerateThree S hS i)) = ∑ i ∈ S, f i := by
  rw [← Finset.sum_coe_sort S f]
  exact Equiv.sum_comp (enumerateThree S hS) (fun i : S => f i)

theorem no_hadamard_orthogonal_restrictions {H : CMatrix} (hH : IsHadamard H)
    (R S : Finset Coord) (hR : R.card = 3) (hS : S.card = 3)
    (hcross : ∀ r ∈ R, ∀ s ∈ Rᶜ, ∑ c ∈ S, H r c * conj (H s c) = 0) : False := by
  have hRc : Rᶜ.card = 3 := by simp [Finset.card_compl, hR]
  let r := enumerateThree R hR
  let s := enumerateThree Rᶜ hRc
  let c := enumerateThree S hS
  let A : Matrix (Fin 3) (Fin 3) ℂ := fun i j => H (r i) (c j)
  let B : Matrix (Fin 3) (Fin 3) ℂ := fun i j => H (s i) (c j)
  apply no_cubic_three_by_three_block A B (fun i j => hH.1 _ _) ?_ ?_
  · ext i j
    change (∑ k, H (r i) (c k) * conj (H (s j) (c k))) = 0
    rw [sum_enumerateThree S hS (fun k => H (r i) k * conj (H (s j) k))]
    exact hcross (r i) (r i).property (s j) (s j).property
  · ext i j
    change (∑ k, conj (H (r k) (c i)) * H (r k) (c j)) +
        (∑ k, conj (H (s k) (c i)) * H (s k) (c j)) =
      (6 : ℂ) * (if i = j then 1 else 0)
    rw [sum_enumerateThree R hR (fun k => conj (H k (c i)) * H k (c j)),
      sum_enumerateThree Rᶜ hRc (fun k => conj (H k (c i)) * H k (c j)),
      Finset.sum_add_sum_compl, hH.column_orthogonal]
    by_cases hij : i = j
    · simp [hij]
    · have hc : (c i : Coord) ≠ c j := by
        intro h
        exact hij (c.injective (Subtype.ext h))
      simp [hij, hc]

theorem cubic_block_cross_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2))
    (R S : Finset Coord) (hS : S.card = 3) (x : ℂ) (hx : x ≠ 1)
    (hblock : ∀ r c, H r c ^ 3 = if r ∈ R ∧ c ∈ S then x else 1)
    (r : Coord) (hr : r ∈ R) (s : Coord) (hs : s ∈ Rᶜ) :
    ∑ c ∈ S, H r c * conj (H s c) = 0 := by
  classical
  have hsR : s ∉ R := Finset.mem_compl.mp hs
  have hrs : r ≠ s := by intro h; exact hsR (h ▸ hr)
  let v : Coord → ℂ := fun c => H r c / H s c
  obtain ⟨hu, h1, h2⟩ := hadamard_row_ratio_moments hH hH2 r s hrs
  have hv (c : Coord) : v c ^ 3 = if c ∈ S then x else 1 := by
    by_cases hc : c ∈ S <;> simp [v, div_pow, hblock, hr, hsR, hc]
  have hvalues : ∀ c, v c ^ 3 = x ∨ v c ^ 3 = 1 := by
    intro c
    by_cases hc : c ∈ S <;> simp [hv, hc]
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hSc : Sᶜ.card = 3 := by simp [Finset.card_compl, hS]
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < Sᶜ.card by omega)
  have hav : v a ^ 3 = x := by simp [hv, ha]
  have hbv : v b ^ 3 = 1 := by simp [hv, Finset.mem_compl.mp hb]
  have hm := two_cube_classes_card_three v hu h1 h2 x 1 hx hvalues a b hav hbv
  have hset : cubeClass v x = S := by
    ext c
    by_cases hc : c ∈ S <;> simp [cubeClass, hv, hc, Ne.symm hx]
  have hz : (∑ c ∈ S, v c) = 0 := by simpa only [hset] using hm.2.2.1
  simpa only [v, div_eq_mul_inv, unit_inv_eq_conj (hH.1 s _)] using hz

/-- An arbitrary dephased complex Hadamard matrix whose entrywise square is
Hadamard has only cube roots of unity as entries. -/
theorem dephased_hadamard_cubes_one {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2))
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1) :
    ∀ i j, H i j ^ 3 = 1 := by
  intro i j
  by_contra hij
  obtain ⟨R, S, x, hR, hS, _, _, _, hx, hblock⟩ :=
    dephased_hadamard_cubes_block hH hH2 h0row h0col i j hij
  exact no_hadamard_orthogonal_restrictions hH R S hR hS
    (cubic_block_cross_orthogonal hH hH2 R S hS x hx hblock)

end MUB6

end

end OAI
