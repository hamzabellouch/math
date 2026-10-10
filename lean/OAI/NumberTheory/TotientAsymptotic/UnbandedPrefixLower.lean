import OAI.NumberTheory.TotientAsymptotic.FordSimplexEmbedding
import OAI.NumberTheory.TotientAsymptotic.RenewalInput
import OAI.NumberTheory.TotientAsymptotic.SimplexScaling

namespace OAI

/-! Terminal lower bounds for finite unbanded simplex prefixes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma enlargedSimplex_mul_const {N : ℕ} {B β₀ c : ℝ} {β u : Fin N → ℝ}
    (hu : u ∈ enlargedSimplex N B β₀ β) (hc : 0 ≤ c) :
    (fun i => c*u i) ∈ enlargedSimplex N (c*B) β₀ β := by
  refine ⟨fun i => mul_nonneg hc (hu.1 i),?_,?_⟩
  · intro i
    calc
      _ = c*∑ j : Fin N, if i < j then a (j.val-i.val)*u j else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ ≤ c*(β i*u i) := mul_le_mul_of_nonneg_left (hu.2.1 i) hc
      _ = _ := by ring
  · calc
      _ = c*∑ i : Fin N, a (i.val+1)*u i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ c*(β₀*B) := mul_le_mul_of_nonneg_left hu.2.2 hc
      _ = _ := by ring

lemma prefixRegion_last_lower {N : ℕ} {B : ℝ} {u : Fin (N+1) → ℝ}
    (hu : u ∈ prefixRegion (N+1) B 0 0) (i : Fin (N+1)) :
    g (N-i.val)*u (Fin.last N) ≤ u i := by
  let v : ℕ → ℝ := fun j => if hj : j < N+1 then u ⟨j,hj⟩ else 0
  have hv (j) (hj : j < N+1) : v j = u ⟨j,hj⟩ := by simp only [v,dite_eq_left hj]
  have hs (j : ℕ) (hj : j < N) :
      (∑ r ∈ Finset.Icc (j+1) N, a (r-j)*v r) ≤ v j := by
    have hh := hu.1 ⟨j,by omega⟩
    rw [prefixLinear_apply] at hh
    have he : (∑ r : Fin (N+1), if (⟨j,by omega⟩:Fin (N+1)) < r then
        a (r.val-j)*u r else 0) =
        ∑ r ∈ Finset.Icc (j+1) N, a (r-j)*v r := by
      have hv' : (∑ r : Fin (N+1), if j < r.val then a (r.val-j)*u r else 0) =
          ∑ r : Fin (N+1), if j < r.val then a (r.val-j)*v r.val else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hv r.val r.isLt]
      change (∑ r : Fin (N+1), if j < r.val then a (r.val-j)*u r else 0) = _
      rw [hv',Fin.sum_univ_eq_sum_range
        (fun r => if j < r then a (r-j)*v r else 0), ← Finset.sum_filter]
      congr 1
      ext r
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
      omega
    rw [he] at hh
    rw [hv j (by omega)]
    change 0 ≤ u ⟨j,by omega⟩-_ at hh
    linarith
  have hh := renewal_prefix_lower N v hs (show i.val ≤ N by omega)
  simpa only [hv N (by omega),hv i.val i.isLt,Fin.eta,Fin.last] using hh

lemma renewal_linear_lower : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c*((n:ℝ)+1) ≤ g n := by
  obtain ⟨d,hd,hg⟩ := renewal_uniform_lower fordRenewalInput
  let r := min 1 (rho⁻¹-1)
  have hrpos : 0 < r := lt_min (by norm_num) (by
    have hh : 1 < rho⁻¹ := (one_lt_inv₀ rho_pos).mpr rho_lt_one
    linarith)
  refine ⟨d*r,mul_pos hd hrpos,fun n => ?_⟩
  have hp := one_add_mul_sub_le_pow (show (-1:ℝ) ≤ rho⁻¹ from (by norm_num : (-1:ℝ) ≤ 0).trans (inv_pos.mpr rho_pos).le) n
  have hr1 : r ≤ 1 := min_le_left _ _
  have hr2 : r ≤ rho⁻¹-1 := min_le_right _ _
  have hn := mul_le_mul_of_nonneg_left hr2 (Nat.cast_nonneg n (α:=ℝ))
  have hh : r*((n:ℝ)+1) ≤ (rho^n)⁻¹ := by
    rw [← inv_pow]
    nlinarith only [hr1,hn,hp]
  calc
    _ = d*(r*((n:ℝ)+1)) := by ring
    _ ≤ d*(rho^n)⁻¹ := mul_le_mul_of_nonneg_left hh hd.le
    _ ≤ g n := hg n

/-- The linear lower envelope survives every bounded diagonal enlargement. -/
theorem enlarged_prefix_linear_lower : ∃ d : ℝ, 0 < d ∧
    ∀ {N : ℕ} {B β₀ K : ℝ} {β κ u : Fin (N+1) → ℝ},
      0 < K → 0 < β₀ → (∀ i, 0 < β i) →
      (∀ i, 1 ≤ κ i ∧ κ i ≤ K) →
      (∀ i, β₀ ≤ κ i) → (∀ i j, i < j → β i*κ i ≤ κ j) →
      u ∈ enlargedSimplex (N+1) B β₀ β → 1 ≤ u (Fin.last N) →
      ∀ i, d/K*((N+1-i.val:ℕ):ℝ) ≤ u i := by
  obtain ⟨d,hd,hg⟩ := renewal_linear_lower
  refine ⟨d,hd,?_⟩
  intro N B β₀ K β κ u hK hβ₀ hβ hκ htop hstep hu hlast i
  have hκpos (j) : 0 < κ j := zero_lt_one.trans_le (hκ j).1
  have hv := enlargedSimplex_mapsTo hβ₀ hβ hκpos htop hstep hu
  have hterminal : 1/K ≤ simplexScale κ u (Fin.last N) := by
    rw [simplexScale_apply]
    calc
      _ ≤ 1/κ (Fin.last N) := div_le_div_of_nonneg_left (by norm_num)
        (hκpos _) (hκ _).2
      _ ≤ _ := div_le_div_of_nonneg_right hlast (hκpos _).le
  have hrec := prefixRegion_last_lower hv i
  have huupper : simplexScale κ u i ≤ u i := by
    rw [simplexScale_apply]
    exact div_le_self (hu.1 i) (hκ i).1
  have hN : ((N+1-i.val:ℕ):ℝ)=((N-i.val:ℕ):ℝ)+1 := by
    exact_mod_cast (show N+1-i.val=(N-i.val)+1 by have := i.isLt; omega)
  calc
    _ = (d*((N-i.val:ℕ):ℝ)+d)*(1/K) := by rw [hN]; ring
    _ ≤ g (N-i.val)*(1/K) := mul_le_mul_of_nonneg_right
      (by simpa only [mul_add,mul_one] using hg (N-i.val)) (by positivity)
    _ ≤ g (N-i.val)*simplexScale κ u (Fin.last N) :=
      mul_le_mul_of_nonneg_left hterminal (g_pos _).le
    _ ≤ simplexScale κ u i := hrec
    _ ≤ u i := huupper

end TotientAsymptotic

end

end OAI
