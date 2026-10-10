import OAI.Combinatorics.EditDistance.FourierAverages
import OAI.Combinatorics.EditDistance.Cuts

namespace OAI

/-!
# Prime-product displacement for absolutely summable maps
-/

namespace EditFourier
open scoped BigOperators
open Finset EditAverage

noncomputable def variation {G E : Type*} [AddCommGroup G] [Fintype G]
    [NormedAddCommGroup E] (H : G → E) (l : G) : ℝ :=
  avg (fun z => ‖H (z + l) - H z‖)

section CutTransport
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma quadraticVariation_cut (A : Finset G) (l : G) :
    quadraticVariation (fun z => (EditCuts.cut A z : ℂ)) l =
      variation (EditCuts.cut A) l := by
  unfold quadraticVariation variation avg
  congr 1
  apply sum_congr rfl
  intro z _
  by_cases hz : z ∈ A <;> by_cases hzl : z + l ∈ A <;>
    simp [EditCuts.cut, hz, hzl]

lemma variation_cut_decomposition (H : G → EditCuts.RealL1) (c : Finset G → ℝ)
    (hd : ∀ x y, ‖H x - H y‖ = ∑ A : Finset G, c A * |EditCuts.cut A x - EditCuts.cut A y|)
    (l : G) : variation H l = ∑ A : Finset G, c A * variation (EditCuts.cut A) l := by
  simp_rw [variation, hd, avg_sum, avg_mul, Real.norm_eq_abs]

end CutTransport

section PrimeProductL1
variable {J : Type*} [Fintype J] [DecidableEq J]
variable (p : J → ℕ) [∀ j, NeZero (p j)]
variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem prime_product_displacement
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (B : ℝ) (hB : 1 ≤ B) (hpB : ∀ j, (p j : ℝ) ≤ B)
    (h : ℕ) (hh : 0 < h) (φ : (∀ j, ZMod (p j)) →+ G)
    (H : G → EditCuts.RealL1) (i : J) (u : ZMod (p i)) :
    variation H (φ (Pi.single i u)) ≤
      B ^ (2 * h) * variation H (φ 1) + (2 / (h : ℝ)) *
        ∑ j, avg (fun a : ZMod (p j) => variation H (φ (Pi.single j a))) := by
  classical
  have hcut (A : Finset G) :
      variation (EditCuts.cut A) (φ (Pi.single i u)) ≤
        B ^ (2 * h) * variation (EditCuts.cut A) (φ 1) + (2 / (h : ℝ)) *
          ∑ j, avg (fun a : ZMod (p j) => variation (EditCuts.cut A) (φ (Pi.single j a))) := by
    simpa only [quadraticVariation_cut] using group_quadratic_comparison p hcop B hB hpB h hh φ
      (fun z => (EditCuts.cut A z : ℂ)) i u
  obtain ⟨c, hc, _, _, hd⟩ := EditCuts.l1_decomposition H
  simp_rw [variation_cut_decomposition H c hd]
  calc
    _ ≤ ∑ A : Finset G, c A *
        (B ^ (2 * h) * variation (EditCuts.cut A) (φ 1) + (2 / (h : ℝ)) *
          ∑ j, avg (fun a : ZMod (p j) => variation (EditCuts.cut A) (φ (Pi.single j a)))) := by
      apply sum_le_sum
      intro A _
      exact mul_le_mul_of_nonneg_left (hcut A) (hc A)
    _ = _ := by
      simp_rw [mul_add, sum_add_distrib, avg_sum, avg_mul]
      congr 1
      · simp_rw [mul_left_comm _ (B ^ (2 * h)), ← mul_sum]
      · simp_rw [mul_left_comm _ (2 / (h : ℝ)), ← mul_sum, mul_sum]
        rw [sum_comm]

end PrimeProductL1
end EditFourier

namespace EditFourier
open scoped BigOperators
open Finset EditAverage

def torsionHom {G : Type*} [AddCommGroup G] (p : ℕ) (v : G) (hv : p • v = 0) :
    ZMod p →+ G :=
  ZMod.lift p ⟨{ toFun := fun z : ℤ => z • v
                 map_zero' := zero_zsmul v
                 map_add' := fun x y => add_zsmul v x y }, by simpa using hv⟩

lemma torsionHom_natCast {G : Type*} [AddCommGroup G] (p : ℕ) (v : G) (hv : p • v = 0)
    (a : ℕ) : torsionHom p v hv (a : ZMod p) = a • v := by
  simpa [torsionHom] using ZMod.lift_coe p
    (⟨{ toFun := fun z : ℤ => z • v
        map_zero' := zero_zsmul v
        map_add' := fun x y => add_zsmul v x y }, by simpa using hv⟩) (a : ℤ)

lemma torsionHom_apply {G : Type*} [AddCommGroup G] (p : ℕ) [NeZero p]
    (v : G) (hv : p • v = 0) (a : ZMod p) : torsionHom p v hv a = a.val • v := by
  rw [← torsionHom_natCast p v hv a.val, ZMod.natCast_zmod_val]

section Vectors
variable {J G : Type*} [Fintype J] [DecidableEq J] [AddCommGroup G]
variable (p : J → ℕ) (v : J → G) (hv : ∀ j, p j • v j = 0)

def vectorHom : (∀ j, ZMod (p j)) →+ G where
  toFun a := ∑ j, torsionHom (p j) (v j) (hv j) (a j)
  map_zero' := by simp
  map_add' a b := by simp [map_add, Finset.sum_add_distrib]

lemma vectorHom_single (i : J) (a : ZMod (p i)) :
    vectorHom p v hv (Pi.single i a) = torsionHom (p i) (v i) (hv i) a := by
  classical
  simp only [vectorHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

omit [DecidableEq J] in
lemma vectorHom_one : vectorHom p v hv 1 = ∑ j, v j := by
  change (∑ j, torsionHom (p j) (v j) (hv j) 1) = _
  apply Finset.sum_congr rfl
  intro j _
  simpa using torsionHom_natCast (p j) (v j) (hv j) 1

variable [Fintype G] [∀ j, NeZero (p j)]

include hv

theorem vector_displacement
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (B : ℝ) (hB : 1 ≤ B) (hpB : ∀ j, (p j : ℝ) ≤ B)
    (h : ℕ) (hh : 0 < h) (H : G → EditCuts.RealL1) (i : J) (u : ZMod (p i)) :
    variation H (u.val • v i) ≤ B ^ (2 * h) * variation H (∑ j, v j) +
      (2 / (h : ℝ)) * ∑ j, avg (fun a : ZMod (p j) => variation H (a.val • v j)) := by
  simpa only [vectorHom_single, vectorHom_one, torsionHom_apply] using
    prime_product_displacement p hcop B hB hpB h hh (vectorHom p v hv) H i u

theorem prime_vector_displacement (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (P : ℝ) (hP : 1 ≤ 2 * P) (hpP : ∀ j, (p j : ℝ) ≤ 2 * P)
    (h : ℕ) (hh : 0 < h) (H : G → EditCuts.RealL1) (i : J) (u : ZMod (p i)) :
    variation H (u.val • v i) ≤ (2 * P) ^ (2 * h) * variation H (∑ j, v j) +
      (2 / (h : ℝ)) * ∑ j, avg (fun a : ZMod (p j) => variation H (a.val • v j)) := by
  apply vector_displacement p v hv (fun i j hij => ?_) (2 * P) hP hpP h hh H i u
  exact (hp i).coprime_iff_not_dvd.mpr (fun hd =>
    hij (hinj ((Nat.dvd_prime (hp j)).mp hd |>.resolve_left (hp i).ne_one)))

end Vectors
end EditFourier

end OAI
