import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.PolynomialDephasing01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
namespace FejerDetection
open PolynomialWeyl
open scoped BigOperators ComplexConjugate
noncomputable section

lemma mean_near_one (R : ℕ) (hR : 0 < R) (f : ℕ → ℂ)
    (hf : ∀ a ∈ Finset.range R, ‖f a - 1‖ ≤ (1:ℝ)/2) :
    (1:ℝ)/4 ≤ ‖mean R f‖^2 := by
  have he : mean R f - 1 = mean R (fun a => f a - 1) := by
    simp [mean,Finset.expect_sub_distrib,Finset.expect_const
      (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hR))]
  have h : ‖mean R f - 1‖ ≤ (1:ℝ)/2 := by
    rw [he]
    exact (RCLike.norm_expect_le (K := ℂ)).trans
      (Finset.expect_le (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hR)) hf)
  have ht := norm_le_norm_add_norm_sub (mean R f) (1:ℂ)
  norm_num at ht
  nlinarith [norm_nonneg (mean R f)]

lemma near_integer_phase (x ε : ℝ) (z : ℤ) (R : ℕ)
    (hx : |x-z| ≤ ε) (hε : 0 ≤ ε) (hsmall : 2*Real.pi*R*ε ≤ (1:ℝ)/2)
    (a : ℕ) (ha : a < R) :
    ‖phase ((a:ℝ)*x) - 1‖ ≤ (1:ℝ)/2 := by
  have h := PolynomialDephasing.norm_phase_sub_le ((a:ℝ)*x) ((a:ℝ)*(z:ℝ))
  rw [show (a:ℝ)*(z:ℝ) = ((a:ℤ)*z:ℤ) by push_cast; rfl,phase_int] at h
  push_cast at h
  have he : (a:ℝ)*x - (a:ℝ)*(z:ℝ) = (a:ℝ)*(x-z) := by ring
  have hr : ‖phase ((a:ℝ)*x) - 1‖ ≤ 2*Real.pi*((a:ℝ)*|x-z|) := by
    simpa only [he,abs_mul,abs_of_nonneg (Nat.cast_nonneg a : (0:ℝ) ≤ a)] using h
  have hbound : (a:ℝ)*|x-z| ≤ (R:ℝ)*ε :=
    (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg a)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast ha.le) hε)
  exact hr.trans ((mul_le_mul_of_nonneg_left hbound (by positivity)).trans (by nlinarith))

lemma energy_identity (N R : ℕ) (f : ℕ → ℝ) :
    (𝔼 n ∈ Finset.range N, ‖mean R (fun a => phase ((a:ℝ)*f n))‖^2) =
      𝔼 a ∈ Finset.range R, 𝔼 b ∈ Finset.range R,
        (mean N (fun n => phase (((a:ℝ)-b)*f n))).re := by
  simp only [mean,norm_expect_sq_eq]
  have hre {ι : Type} (S : Finset ι) (F : ι → ℂ) :
      (𝔼 i ∈ S, F i).re = 𝔼 i ∈ S, (F i).re :=
    map_expect (Complex.reLm.restrictScalars ℚ≥0) F S
  simp_rw [hre]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro a ha
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro b hb
  apply Finset.expect_congr rfl
  intro n hn
  rw [sub_mul,phase_sub]

 

theorem detect (N R : ℕ) (hN : 0 < N) (hR : 0 < R)
    (δ ε : ℝ) (hδ : 0 < δ) (hRδ : 16 ≤ δ*R) (hε : 0 ≤ ε)
    (hsmall : 2*Real.pi*R*ε ≤ (1:ℝ)/2)
    (S : Finset ℕ) (hSN : S ⊆ Finset.range N) (hS : δ*N ≤ (S.card:ℝ))
    (f : ℕ → ℝ) (hgood : ∀ n ∈ S, ∃ z : ℤ, |f n-z| ≤ ε) :
    ∃ a ∈ Finset.range R, ∃ b ∈ Finset.range R, a ≠ b ∧
      δ/16 ≤ ‖mean N (fun n => phase (((a:ℝ)-b)*f n))‖ := by
  classical
  let E (n : ℕ) := ‖mean R (fun a => phase ((a:ℝ)*f n))‖^2
  have hgoodE : ∀ n ∈ S, (1:ℝ)/4 ≤ E n := by
    intro n hn
    obtain ⟨z,hz⟩ := hgood n hn
    exact mean_near_one R hR _ (fun a ha =>
      near_integer_phase (f n) ε z R hz hε hsmall a (Finset.mem_range.mp ha))
  have hlow : δ/4 ≤ 𝔼 n ∈ Finset.range N, E n := by
    rw [Finset.expect_eq_sum_div_card,Finset.card_range]
    apply (le_div_iff₀ (Nat.cast_pos.mpr hN)).mpr
    have h₁ := Finset.sum_le_sum hgoodE
    have h₂ := Finset.sum_le_sum_of_subset_of_nonneg hSN
      (fun n _ _ => sq_nonneg ‖mean R (fun a => phase ((a:ℝ)*f n))‖)
    simp only [Finset.sum_const,nsmul_eq_mul] at h₁
    dsimp only [E] at h₁
    nlinarith
  by_contra hx
  push Not at hx
  have hub (a : ℕ) (ha : a ∈ Finset.range R) (b : ℕ) (hb : b ∈ Finset.range R) :
      (mean N (fun n => phase (((a:ℝ)-b)*f n))).re ≤
        (if a=b then (1:ℝ) else 0) + δ/16 := by
    by_cases he : a=b
    · subst b
      simp [phase,mean,Finset.expect_const
        (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN))]
      positivity
    · exact (Complex.re_le_norm _).trans (by simpa [he] using (hx a ha b hb he).le)
  have hup := Finset.expect_le_expect (fun a ha =>
    Finset.expect_le_expect (fun b hb => hub a ha b hb))
  have he (a : ℕ) (ha : a ∈ Finset.range R) :
      (𝔼 b ∈ Finset.range R, ((if a=b then (1:ℝ) else 0)+δ/16)) = 1/(R:ℝ)+δ/16 := by
    rw [Finset.expect_add_distrib,
      Finset.expect_const (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hR)),
      Finset.expect_eq_sum_div_card]
    simp [Finset.sum_ite_eq,ha]
  have he' : (𝔼 a ∈ Finset.range R, 𝔼 b ∈ Finset.range R,
      ((if a=b then (1:ℝ) else 0)+δ/16)) = 1/(R:ℝ)+δ/16 := by
    rw [Finset.expect_congr rfl he,
      Finset.expect_const (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hR))]
  rw [he'] at hup
  have henergy := energy_identity N R f
  change (𝔼 n ∈ Finset.range N, E n) = _ at henergy
  rw [← henergy] at hup
  have hrecip : 1/(R:ℝ) ≤ δ/16 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hR)).mpr
    nlinarith
  linarith

end
end FejerDetection

 

open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators

namespace LagrangeBounds

variable {ι : Type*} [DecidableEq ι]

 
lemma basis_bound (s : Finset ι) (v : ι → ℝ) {i : ι} (hi : i ∈ s)
    {a b d x : ℝ} (hd : 0 < d) (hv : ∀ j ∈ s, v j ∈ Set.Icc a b)
    (hsep : ∀ j ∈ s, j ≠ i → d ≤ |v i - v j|) (hx : x ∈ Set.Icc a b) :
    |(Lagrange.basis s v i).eval x| ≤ ((b - a) / d) ^ (s.card - 1) := by
  rw [Lagrange.basis, eval_prod, Finset.abs_prod]
  calc
    (∏ j ∈ s.erase i, |eval x (Lagrange.basisDivisor (v i) (v j))|) ≤
        ∏ _j ∈ s.erase i, (b - a) / d := by
      apply prod_le_prod₀
      · intro _ _; positivity
      · intro j hj
        obtain ⟨hji, hjs⟩ := mem_erase.mp hj
        simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X,
          abs_mul, abs_inv]
        rw [mul_comm, ← div_eq_mul_inv]
        have hnum : |x - v j| ≤ b - a := by
          rw [abs_le]
          have := hv j hjs
          constructor <;> linarith [hx.1, hx.2, this.1, this.2]
        exact div_le_div₀ (by linarith [hx.1, hx.2]) hnum hd (hsep j hjs hji)
    _ = _ := by rw [prod_const, card_erase_of_mem hi]

 
theorem interpolate_error (s : Finset ι) (v : ι → ℝ) (hv_inj : Set.InjOn v s)
    {a b d ε x : ℝ} (hd : 0 < d) (hε : 0 ≤ ε)
    (hv : ∀ j ∈ s, v j ∈ Set.Icc a b)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → d ≤ |v i - v j|)
    (hx : x ∈ Set.Icc a b) (T : ℝ[X]) (hT : T.degree < s.card)
    (r : ι → ℝ) (hr : ∀ i ∈ s, |r i - T.eval (v i)| ≤ ε) :
    |(Lagrange.interpolate s v r).eval x - T.eval x| ≤
      (s.card : ℝ) * ((b - a) / d) ^ (s.card - 1) * ε := by
  have heq : Lagrange.interpolate s v (fun i => T.eval (v i)) = T :=
    (Lagrange.eq_interpolate hv_inj hT).symm
  rw [← heq, ← eval_sub, ← map_sub]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  calc
    |∑ i ∈ s, eval x (C ((r - fun i => T.eval (v i)) i) * Lagrange.basis s v i)| ≤
        ∑ i ∈ s, ε * ((b - a) / d) ^ (s.card - 1) := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro i hi
      simp only [eval_mul, eval_C, Pi.sub_apply, abs_mul]
      exact mul_le_mul (hr i hi) (basis_bound s v hi hd hv (hsep i hi) hx)
        (abs_nonneg _) hε
    _ = _ := by simp [mul_left_comm, mul_comm]

end LagrangeBounds

 

namespace DenseIntegerNodes
open Finset

lemma strictMono_int_gap {N : ℕ} (f : Fin N → ℤ) (hf : StrictMono f)
    {i j : Fin N} (hij : i ≤ j) : (j.val : ℤ) - i.val ≤ f j - f i := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ N =>
    have hg : Monotone (fun i : Fin (N+1) => f i - (i.val : ℤ)) := by
      apply Fin.monotone_iff_le_succ.mpr
      intro k
      have h := hf (Fin.castSucc_lt_succ (i := k))
      simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
      omega
    have h := hg hij
    dsimp only at h
    omega

 
theorem separated (E : Finset ℤ) (q : ℕ) (hE : 2 * (q+1) ≤ E.card) :
    ∃ v : Fin (q+1) → ℤ, (∀ i, v i ∈ E) ∧
      ∀ i j, i ≠ j → (E.card : ℝ) / (2 * (q+1)) ≤ |(v i : ℝ) - v j| := by
  let K := E.card
  let h := K / (q+1)
  have hq : 0 < q+1 := by omega
  have hh : 1 ≤ h := by
    dsimp [h, K]
    exact (Nat.le_div_iff_mul_le hq).mpr (by omega)
  have hmul : h * (q+1) ≤ K := Nat.div_mul_le_self K (q+1)
  have hrem := Nat.mod_lt K hq
  have hdiv : K % (q+1) + (q+1) * h = K := Nat.mod_add_div K (q+1)
  have hhalf : K ≤ 2 * (q+1) * h := by
    have htwo : 2 ≤ h := by
      dsimp [h, K]
      exact (Nat.le_div_iff_mul_le hq).mpr (by omega)
    have hd : K < (q+1) * (h+1) := by nlinarith
    have hh' : h+1 ≤ 2*h := by omega
    have := Nat.mul_le_mul_left (q+1) hh'
    nlinarith
  let idx : Fin (q+1) → Fin K := fun i => ⟨h * i.val, by
    have hi : i.val ≤ q := by omega
    have hlt : h * i.val < h * (q+1) := Nat.mul_lt_mul_of_pos_left i.isLt (by omega)
    exact hlt.trans_le hmul⟩
  let v : Fin (q+1) → ℤ := fun i => E.orderEmbOfFin rfl (idx i)
  refine ⟨v, fun i => E.orderEmbOfFin_mem rfl (idx i), ?_⟩
  have hbound : (K : ℝ) / (2 * (q+1)) ≤ (h : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (q+1))).mpr
    exact_mod_cast (show K ≤ h * (2 * (q+1)) by nlinarith)
  have hsep (i j : Fin (q+1)) (hij : i < j) : (h : ℝ) ≤ (v j : ℝ) - v i := by
    have hj : i.val + 1 ≤ j.val := hij
    have hidx : idx i ≤ idx j := by
      change h * i.val ≤ h * j.val
      exact Nat.mul_le_mul_left h (by omega)
    have hgap := strictMono_int_gap (E.orderEmbOfFin rfl) (E.orderEmbOfFin rfl).strictMono hidx
    change (h * j.val : ℕ) - (h * i.val : ℤ) ≤ v j - v i at hgap
    have hmulij := Nat.mul_le_mul_left h hj
    have hhgap : (h : ℤ) ≤ (h * j.val : ℕ) - (h * i.val : ℤ) := by
      have hm : ((h + h * i.val : ℕ) : ℤ) ≤ (h * j.val : ℕ) := by
        exact_mod_cast (show h + h * i.val ≤ h * j.val by nlinarith)
      push_cast at hm ⊢
      omega
    have hx : (h : ℤ) ≤ v j - v i := hhgap.trans hgap
    exact_mod_cast hx
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hij
  · have hj := hsep i j hij
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ v j - v i)]
    exact hbound.trans hj
  · have hi := hsep j i hij
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ v i - v j)]
    exact hbound.trans hi

 
theorem separated_of_density (E : Finset ℤ) (q : ℕ) {H α : ℝ}
    (hE : 2 * (q+1) ≤ E.card) (hdens : α * H ≤ E.card) :
    ∃ v : Fin (q+1) → ℤ, (∀ i, v i ∈ E) ∧
      ∀ i j, i ≠ j → α * H / (2 * (q+1)) ≤ |(v i : ℝ) - v j| := by
  obtain ⟨v, hv, hs⟩ := separated E q hE
  exact ⟨v, hv, fun i j hij => (div_le_div_of_nonneg_right hdens (by positivity)).trans
    (hs i j hij)⟩

end DenseIntegerNodes

end
end
end
end

end OAI
