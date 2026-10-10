import OAI.Probability.ContinuumTransition.PhysicalInsertion

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

def CellLowerBound (t : ℝ) (σ R : ℕ → ℝ) (V : Space → Space → ℝ) : Prop :=
  ∀ x y, (if cellIndex x = cellIndex y then coreProfile t ‖x-y‖ else 0)-
    physicalCoupling t σ R (cellIndex x) (cellIndex y) ≤ V x y

theorem gibbsEnergy_mono {U V : Space → Space → ℝ} {ι : Type} [Fintype ι]
    (x : ι → Space) (h : ∀ i j, U (x i) (x j) ≤ V (x i) (x j)) :
    gibbsEnergy U x ≤ gibbsEnergy V x := by
  unfold gibbsEnergy
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · rfl
  · exact h i j

theorem gibbsEnergy_partition_le (U : Space → Space → ℝ)
    (hU : ∀ x y, 0 ≤ U x y) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ι → κ) (x : ι → Space) :
    (∑ k, gibbsEnergy U (fun i : {i : ι // c i = k} => x i)) ≤ gibbsEnergy U x := by
  let f (i j : ι) := if i = j then 0 else U (x i) (x j)
  have hf (i j : ι) : 0 ≤ f i j := by dsimp only [f]; split_ifs; rfl; exact hU _ _
  have he (k : κ) : gibbsEnergy U (fun i : {i : ι // c i = k} => x i) =
      (∑ i : {i : ι // c i = k}, ∑ j : {j : ι // c j = k}, f i j)/2 := by
    unfold gibbsEnergy
    simp only [f, Subtype.ext_iff]
  simp_rw [he]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑ k : κ, ∑ i : {i : ι // c i = k}, ∑ j : ι, f i j := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro i _
      exact sum_subtype_le_of_nonneg (fun j => c j = k) (f i) (hf i)
    _ = _ := Fintype.sum_fiberwise c (fun i => ∑ j, f i j)

theorem retained_core_partition_bound (t : ℝ) {ι κ : Type}
    [Fintype ι] [Fintype κ] [DecidableEq κ] (x : ι → Space) (c : ι → κ) (e : κ → Lattice)
    (hc : ∀ i, cellIndex (x i) = e (c i)) :
    t^2/8*(∑ k, (Fintype.card {i : ι // c i = k} : ℝ)^2)-t^2/2*Fintype.card ι ≤
      gibbsEnergy (fun x y => if cellIndex x = cellIndex y then coreProfile t ‖x-y‖ else 0) x := by
  let U : Space → Space → ℝ := fun x y => if cellIndex x = cellIndex y then coreProfile t ‖x-y‖ else 0
  have hU (x y : Space) : 0 ≤ U x y := by dsimp only [U]; split_ifs; exact coreProfile_nonneg _ _; rfl
  have he (k : κ) : gibbsEnergy U (fun i : {i : ι // c i = k} => x i) =
      gibbsEnergy (fun x y => coreProfile t ‖x-y‖) (fun i : {i : ι // c i = k} => x i) := by
    unfold gibbsEnergy
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hij : cellIndex (x i) = cellIndex (x j) := by rw [hc i, hc j, i.property, j.property]
    simp only [U, ite_eq_left hij]
  have hs (k : κ) := core_gibbsEnergy_one_cell t (fun i : {i : ι // c i = k} => x i) (e k)
    (fun i => by change cellIndex (x i) = e k; rw [hc i, i.property])
  have hh := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset κ)) => hs k)
  have hp := gibbsEnergy_partition_le U hU c x
  simp_rw [he] at hp
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hh
  have hcard : (∑ k, (Fintype.card {i : ι // c i = k} : ℝ)) = Fintype.card ι := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
      Fintype.sum_fiberwise c (fun _ => (1 : ℝ))
  rw [hcard] at hh
  exact hh.trans hp

theorem cellLowerBound_superstable {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    {V : Space → Space → ℝ} (hV : CellLowerBound t σ R V)
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (x : ι → Space) (c : ι → κ) (e : κ → Lattice) (he : Function.Injective e)
    (hc : ∀ i, cellIndex (x i) = e (c i)) :
    (t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)*
      (∑ k, (Fintype.card {i : ι // c i = k} : ℝ)^2)-t^2/2*Fintype.card ι ≤ gibbsEnergy V x := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let U : Space → Space → ℝ := fun x y => if cellIndex x = cellIndex y then coreProfile t ‖x-y‖ else 0
  let W : Space → Space → ℝ := fun x y => physicalCoupling t σ R (cellIndex x) (cellIndex y)
  have hWsym (x y : Space) : W x y = W y x := by simp only [W, physicalCoupling, mixedEnvelope_symm]
  have hwl := pairSum_le_cell_quadratic c (fun k l => physicalCoupling t σ R (e k) (e l))
    (fun i j => W (x i) (x j)) (fun _ _ => physicalCoupling_nonneg ht hσ hR _ _)
    (fun i j => hWsym _ _) (fun i j => le_of_eq (by dsimp only [W]; rw [hc i, hc j]))
  rw [← gibbsEnergy_eq_pairSum W hWsym x] at hwl
  have hquad := row_sum_quadratic_bound (fun k l => physicalCoupling t σ R (e k) (e l))
    (fun k => (Fintype.card {i : ι // c i = k} : ℝ)) (2197*t*kernelHeight*(∑' n, σ n))
    (fun _ _ => physicalCoupling_nonneg ht hσ hR _ _)
    (fun k l => by simp only [physicalCoupling, mixedEnvelope_symm])
    (fun k => physicalCoupling_row ht hσ hR hs e he (e k))
  have hcore := retained_core_partition_bound t x c e hc
  have hlo := gibbsEnergy_mono (U := fun x y => U x y-W x y) (V := V) x
    (fun i j => hV (x i) (x j))
  change gibbsEnergy (fun x y => U x y-W x y) x ≤ gibbsEnergy V x at hlo
  rw [gibbsEnergy_sub] at hlo
  change _ ≤ gibbsEnergy U x at hcore
  nlinarith only [hwl, hquad, hcore, hlo]

theorem cellLowerBound_moment_energy {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {V : Space → Space → ℝ} (hV : CellLowerBound t σ R V)
    {ι : Type} [Fintype ι] (x : ι → Space) (z : Lattice) :
    (t^2/8)/4*(occupation (latticeCell z) x)^2 ≤ gibbsEnergy V x+t^2/2*Fintype.card ι := by
  let S : Finset Lattice := insert z (Finset.univ.image (fun i => cellIndex (x i)))
  let c (i : ι) : S := ⟨cellIndex (x i), Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨i, Finset.mem_univ i, rfl⟩)⟩
  let k : S := ⟨z, Finset.mem_insert_self _ _⟩
  have hcard : (Fintype.card {i : ι // c i = k} : ℝ) = occupation (latticeCell z) x := by
    unfold occupation
    congr 1
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun i => by simp only [Subtype.ext_iff, c, k, latticeCell,
      mem_ofPred_eq])
  have hsq : (occupation (latticeCell z) x)^2 ≤ ∑ j : S, (Fintype.card {i : ι // c i = j} : ℝ)^2 := by
    rw [← hcard]
    exact Finset.single_le_sum (s := Finset.univ) (f := fun j : S => (Fintype.card {i : ι // c i = j} : ℝ)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  have hp := cellLowerBound_superstable ht hσ hR hs hV x c
    (fun j : S => (j : Lattice)) Subtype.val_injective (fun _ => rfl)
  have hcoef : (t^2/8)/4 ≤ t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2 := by
    nlinarith only [hsmall, sq_nonneg t]
  have h0 : 0 ≤ (t^2/8)/4 := by positivity
  have hb := (mul_le_mul_of_nonneg_left hsq h0).trans
    (mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  linarith only [hb, hp]

end ContinuumTemperature
end

end OAI
