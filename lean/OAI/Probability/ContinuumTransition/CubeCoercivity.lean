import OAI.Probability.ContinuumTransition.Stability

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

noncomputable def cubeCells (L : ℝ) : Finset Lattice :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc ⌊-2 * L⌋ ⌊2 * L⌋)

theorem cellIndex_mem_cubeCells {L : ℝ} {x : Space} (hx : x ∈ cube L) :
    cellIndex x ∈ cubeCells L := by
  classical
  simp only [cubeCells, Fintype.mem_piFinset, Finset.mem_Icc, cellIndex]
  intro k
  constructor
  · apply Int.floor_mono
    have h := (hx k).1
    linarith
  · apply Int.floor_mono
    have h := (hx k).2
    linarith

theorem card_cubeCells_le {L : ℝ} (hL : 0 ≤ L) :
    ((cubeCells L).card : ℝ) ≤ (4 * L + 2) ^ 3 := by
  classical
  let m := (Finset.Icc ⌊-2 * L⌋ ⌊2 * L⌋).card
  have horder : ⌊-2 * L⌋ ≤ ⌊2 * L⌋ + 1 := by
    have hh := Int.floor_mono (show -2 * L ≤ 2 * L by linarith)
    omega
  have hcInt := Int.card_Icc_of_le ⌊-2 * L⌋ ⌊2 * L⌋ horder
  have hcReal : (m : ℝ) = (⌊2 * L⌋ : ℝ) + 1 - (⌊-2 * L⌋ : ℝ) := by
    dsimp only [m]
    exact_mod_cast hcInt
  have hm : (m : ℝ) ≤ 4 * L + 2 := by
    rw [hcReal]
    have hu := Int.floor_le (2 * L)
    have hl := Int.lt_floor_add_one (-2 * L)
    linarith
  have hc : ((cubeCells L).card : ℝ) = (m : ℝ) ^ 3 := by
    simp [cubeCells, Fintype.card_piFinset, m]
  rw [hc]
  exact pow_le_pow_left₀ (Nat.cast_nonneg m) hm 3

theorem physicalProfile_energy_coercive {t L : ℝ} (ht : 0 ≤ t) (hL : 0 ≤ L)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197 * t * kernelHeight * (∑' n, σ n) / 2 ≤ t ^ 2 / 8)
    (N : ℕ) (x : Fin N → Space) (hx : ∀ i, x i ∈ cube L) :
    (((t ^ 2 / 8 - 2197 * t * kernelHeight * (∑' n, σ n) / 2) *
      ((N : ℝ) ^ 2 / (4 * L + 2) ^ 3) - t ^ 2 / 2 * N : ℝ) : EReal) ≤
      energy (physicalProfile t σ R) x := by
  classical
  let κ := (cubeCells L : Type)
  let c (i : Fin N) : κ := ⟨cellIndex (x i), cellIndex_mem_cubeCells (hx i)⟩
  let n (k : κ) : ℝ := Fintype.card {i // c i = k}
  have hsN : (∑ k : κ, n k) = N := by
    have hh := sum_comp_eq_sum_fibres c (fun _ => (1 : ℝ))
    simpa only [n, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] using hh.symm
  have hquad : (N : ℝ) ^ 2 ≤ (Fintype.card κ : ℝ) * ∑ k, n k ^ 2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset κ) (fun _ => (1 : ℝ)) n
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, hsN] using hh
  have hquad' : (N : ℝ) ^ 2 ≤ (4 * L + 2) ^ 3 * ∑ k, n k ^ 2 := by
    apply hquad.trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    simpa only [κ, Fintype.card_coe] using card_cubeCells_le hL
  have hden : 0 < (4 * L + 2) ^ 3 := by positivity
  have hquot : (N : ℝ) ^ 2 / (4 * L + 2) ^ 3 ≤ ∑ k, n k ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_comm] using hquad'
  have hsuper := physicalProfile_superstable ht hσ hR hs x c
    (fun k : κ => (k : Lattice)) Subtype.val_injective (fun _ => rfl)
  have he := coe_pairSum_le_energy (physicalProfile t σ R) x
  apply le_trans _ he
  apply EReal.coe_le_coe_iff.mpr
  have hm := mul_le_mul_of_nonneg_left hquot (sub_nonneg.mpr hsmall)
  simp only [Fintype.card_fin] at hsuper
  exact (sub_le_sub_right hm _).trans hsuper

end

end ContinuumTemperature

end

end OAI
