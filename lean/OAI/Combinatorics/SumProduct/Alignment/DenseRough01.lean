import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughInterpolation01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
namespace DenseRoughInterpolation
open LagrangeBounds RoughInterpolation ExactInterpolation
noncomputable section

def uniformBound (q : ℕ) (α : ℝ) : ℝ :=
  (q + 1 : ℝ) * (2 * (q+1) / α) ^ q

def derivativeBound {q : ℕ} (v : Fin (q+1) → ℤ) : ℝ :=
  1 + ∑ j ∈ range q, ∑ i : Fin (q+1), coefficientBound
    (derivative^[j] (Lagrange.basis univ (fun i => (v i : ℝ)) i)) q

lemma derivativeBound_pos {q : ℕ} (v : Fin (q+1) → ℤ) : 0 < derivativeBound v := by
  have : 0 ≤ ∑ j ∈ range q, ∑ i : Fin (q+1), coefficientBound
      (derivative^[j] (Lagrange.basis univ (fun i => (v i : ℝ)) i)) q :=
    sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => coefficientBound_nonneg _ _))
  unfold derivativeBound
  linarith

lemma derivative_sum_le {q j : ℕ} (v : Fin (q+1) → ℤ) (hj : j < q) :
    (∑ i : Fin (q+1), coefficientBound
      (derivative^[j] (Lagrange.basis univ (fun i => (v i : ℝ)) i)) q) ≤
        derivativeBound v := by
  have h := single_le_sum (s := range q)
    (f := fun j => ∑ i : Fin (q+1), coefficientBound
      (derivative^[j] (Lagrange.basis univ (fun i => (v i : ℝ)) i)) q)
    (fun _ _ => sum_nonneg (fun _ _ => coefficientBound_nonneg _ _)) (mem_range.mpr hj)
  unfold derivativeBound
  linarith

lemma nodes_injective {q N : ℕ} {α : ℝ} (hN : 0 < N) (hα : 0 < α)
    (v : Fin (q+1) → ℤ)
    (hsep : ∀ i j, i ≠ j → α * N / (2 * (q+1)) ≤ |(v i : ℝ) - v j|) :
    Function.Injective (fun i => (v i : ℝ)) := by
  intro i j hij
  by_contra hne
  have h := hsep i j hne
  dsimp only at hij
  rw [hij, sub_self, abs_zero] at h
  have : 0 < α * N / (2 * (q+1)) := by positivity
  linarith

lemma interpolation_error {q N : ℕ} {α : ℝ} (hN : 0 < N) (hα : 0 < α)
    (v : Fin (q+1) → ℤ) (hv : ∀ i, (v i : ℝ) ∈ Set.Icc 0 (N : ℝ))
    (hsep : ∀ i j, i ≠ j → α * N / (2 * (q+1)) ≤ |(v i : ℝ) - v j|)
    (T : ℝ[X]) (hT : T.natDegree ≤ q) (r : Fin (q+1) → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (hr : ∀ i, |r i - T.eval (v i : ℝ)| ≤ ε)
    {x : ℝ} (hx : x ∈ Set.Icc 0 (N : ℝ)) :
    |(Lagrange.interpolate univ (fun i => (v i : ℝ)) r).eval x - T.eval x| ≤
      uniformBound q α * ε := by
  have hdeg : T.degree < ((univ : Finset (Fin (q+1))).card : WithBot ℕ) := by
    simp only [card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (degree_le_natDegree.trans
      (show (T.natDegree : WithBot ℕ) ≤ (q : WithBot ℕ) by exact_mod_cast hT))
      (by exact_mod_cast Nat.lt_succ_self q)
  have h := LagrangeBounds.interpolate_error univ (fun i => (v i : ℝ))
    (nodes_injective hN hα v hsep).injOn
    (by positivity : (0 : ℝ) < α * N / (2 * (q+1))) hε
    (fun i _ => hv i) (fun i _ j _ hji => hsep i j hji.symm) hx T hdeg r (fun i _ => hr i)
  have heq : ((N : ℝ) - 0) / (α * N / (2 * (q+1))) = 2 * (q+1) / α := by
    have hn : (N : ℝ) ≠ 0 := by positivity
    field_simp
    simp
  rw [heq] at h
  simpa only [uniformBound, card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one,
    Nat.add_sub_cancel] using h

 

theorem quantitative_exact_division {N q : ℕ} {α : ℝ} (hN : 0 < N) (hα : 0 < α)
    (E : Finset ℤ) (hE : ∀ z ∈ E, 0 ≤ z ∧ z ≤ N)
    (v : Fin (q+1) → ℤ) (hv : ∀ i, v i ∈ E)
    (hsep : ∀ i j, i ≠ j → α * N / (2 * (q+1)) ≤ |(v i : ℝ) - v j|) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (a b : ℤ) (e : ℕ) (θ : ℝ[X]) (ε : ℝ),
      b ≠ 0 → IsCoprime a b → e ≤ q → 0 ≤ ε →
      ((C (a : ℝ) + C (b : ℝ) * X) ^ e * θ).natDegree ≤ q →
      (∀ z ∈ E, ∃ n : ℤ,
        |((C (a : ℝ) + C (b : ℝ) * X) ^ e * θ).eval (z : ℝ) - (n : ℝ)| ≤ ε) →
      (∀ z ∈ E, IsCoprime D (a + b * z)) →
      (uniformBound q α + 1) * ε < 1 / |(D : ℝ)| →
      ε * K * (1 + |-(a : ℝ) / b|) ^ q <
        1 / (|(D : ℝ)| * |(b : ℝ)| ^ q) →
      ∃ M : ℚ[X], M.natDegree ≤ q - e ∧
        C (D : ℚ) * M ∈ lifts (algebraMap ℤ ℚ) ∧
        (∀ z ∈ E, Integral (M.eval (z : ℚ))) ∧
        ∀ x : ℝ, x ∈ Set.Icc 0 (N : ℝ) →
          |((M.map (algebraMap ℚ ℝ)).eval x - θ.eval x) * ((a : ℝ) + b * x) ^ e| ≤
            uniformBound q α * ε := by
  obtain ⟨D, hD, hden⟩ := interpolation_common_denominator
    (univ : Finset (Fin (q+1))) (fun i => (v i : ℚ))
  refine ⟨D, hD, derivativeBound v, derivativeBound_pos v, ?_⟩
  intro a b e θ ε hb hab he hε hT hnear hcop hsmall hderiv
  let T : ℝ[X] := (C (a : ℝ) + C (b : ℝ) * X) ^ e * θ
  have hnear' : ∀ i : Fin (q+1), ∃ n : ℤ, |T.eval (v i : ℝ) - n| ≤ ε :=
    fun i => hnear (v i) (hv i)
  choose r hr using hnear'
  let R : ℚ[X] := Lagrange.interpolate univ (fun i => (v i : ℚ)) (fun i => (r i : ℚ))
  have hRlifts : C (D : ℚ) * R ∈ lifts (algebraMap ℤ ℚ) := hden r
  have hvreal : ∀ i, (v i : ℝ) ∈ Set.Icc 0 (N : ℝ) := by
    intro i
    exact ⟨by exact_mod_cast (hE (v i) (hv i)).1,
      by exact_mod_cast (hE (v i) (hv i)).2⟩
  have hvinj := nodes_injective hN hα v hsep
  have hinj : Function.Injective (fun i : Fin (q+1) => (v i : ℚ)) := by
    intro i j hij
    apply hvinj
    dsimp only at hij ⊢
    have hz : v i = v j := by exact_mod_cast hij
    exact_mod_cast hz
  have hRdeg : R.natDegree ≤ q := by
    apply natDegree_le_of_degree_le
    have h := Lagrange.degree_interpolate_le (s := univ) (fun i => (r i : ℚ)) hinj.injOn
    simpa only [card_univ, Fintype.card_fin, Nat.add_sub_cancel] using h
  have hRmap : R.map (algebraMap ℚ ℝ) =
      Lagrange.interpolate univ (fun i => (v i : ℝ)) (fun i => (r i : ℝ)) := by
    change (Lagrange.interpolate univ (fun i => (v i : ℚ)) (fun i => (r i : ℚ))).map _ = _
    rw [map_interpolate]
    simp only [map_intCast]
  have herr (x : ℝ) (hx : x ∈ Set.Icc 0 (N : ℝ)) :
      |(R.map (algebraMap ℚ ℝ)).eval x - T.eval x| ≤ uniformBound q α * ε := by
    rw [hRmap]
    apply interpolation_error hN hα v hvreal hsep T hT _ hε _ hx
    intro i
    simpa only [abs_sub_comm] using hr i
  have hzero : ∀ j < e, (derivative^[j] R).eval (-(a : ℚ) / b) = 0 := by
    intro j hj
    apply derivative_eq_zero_of_small (a := -a) hRlifts hRdeg hD hb j
    have hTd : T.degree < ((univ : Finset (Fin (q+1))).card : WithBot ℕ) := by
      simp only [card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt (degree_le_natDegree.trans
        (show (T.natDegree : WithBot ℕ) ≤ (q : WithBot ℕ) by exact_mod_cast hT))
        (by exact_mod_cast Nat.lt_succ_self q)
    have h := derivative_interpolation_error univ (fun i => (v i : ℝ))
      hvinj.injOn (q := q) (by simp) T hTd (fun i => (r i : ℝ))
      hε (fun i _ => by simpa only [abs_sub_comm] using hr i) j (-(a : ℝ) / b)
    rw [← hRmap, iterate_derivative_sub, eval_sub,
      linear_power_derivative_zero (by exact_mod_cast hb) θ hj, sub_zero] at h
    have h' : |(derivative^[j] (R.map (algebraMap ℚ ℝ))).eval (-(a : ℝ) / b)| <
        1 / (|(D : ℝ)| * |(b : ℝ)| ^ q) := by
      apply lt_of_le_of_lt h
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (derivative_sum_le v (by omega : j < q)) hε)
        (by positivity)).trans_lt hderiv
    rw [iterate_derivative_map] at h'
    have heval : ((derivative^[j] R).map (algebraMap ℚ ℝ)).eval (-(a : ℝ) / b) =
        (((derivative^[j] R).eval (-(a : ℚ) / b) : ℚ) : ℝ) := by
      rw [eval_map]
      simpa only [eq_ratCast, Rat.cast_div, Rat.cast_neg, Rat.cast_intCast] using
        (eval₂_at_apply (p := derivative^[j] R) (algebraMap ℚ ℝ) (-(a : ℚ) / b))
    rw [heval] at h'
    exact_mod_cast h'
  obtain ⟨M, hdiv⟩ := exact_linear_division (by exact_mod_cast hb) hzero
  refine ⟨M, quotient_degree (by exact_mod_cast hb) hRdeg hdiv,
    integral_scaled_quotient hab e hRlifts hdiv, ?_, ?_⟩
  · intro z hz
    apply quotient_integral_at hab (hcop z hz) e hRlifts _ hdiv
    have hx : (z : ℝ) ∈ Set.Icc 0 (N : ℝ) :=
      ⟨by exact_mod_cast (hE z hz).1, by exact_mod_cast (hE z hz).2⟩
    obtain ⟨n, hn⟩ := hnear z hz
    have hscaled := integral_eval_of_lifts hRlifts z
    simp only [eval_mul, eval_C] at hscaled
    have hRn : |(R.map (algebraMap ℚ ℝ)).eval (z : ℝ) - (n : ℝ)| < 1 / |(D : ℝ)| := by
      calc
        _ ≤ |(R.map (algebraMap ℚ ℝ)).eval (z : ℝ) - T.eval (z : ℝ)| +
            |T.eval (z : ℝ) - (n : ℝ)| := abs_sub_le _ _ _
        _ ≤ uniformBound q α * ε + ε := add_le_add (herr _ hx) hn
        _ = (uniformBound q α + 1) * ε := by ring
        _ < _ := hsmall
    have heval : (R.map (algebraMap ℚ ℝ)).eval (z : ℝ) = ((R.eval (z : ℚ) : ℚ) : ℝ) := by
      rw [eval_map]
      simpa only [eq_ratCast, Rat.cast_intCast] using
        (eval₂_at_apply (p := R) (algebraMap ℚ ℝ) (z : ℚ))
    rw [heval] at hRn
    have heq := integral_eq_of_near hD hscaled n (by exact_mod_cast hRn)
    exact ⟨n, heq.symm⟩
  · intro x hx
    have h := herr x hx
    rw [hdiv] at h
    simp [T] at h
    simp only [eval_map_algebraMap]
    convert h using 1
    ring_nf

end
end DenseRoughInterpolation

 

open _root_.Polynomial _root_.OAI.Polynomial Filter
open scoped Topology
 

namespace DenseRoughScaleCompletion
open DenseRoughInterpolation RoughScales RoughInterpolation Filter
open scoped Topology

 

theorem eventually_exact_division_fixed_set {e q N : ℕ} (he : 1 ≤ e) (heq : e ≤ q)
    (hN : 0 < N) {α A : ℝ} (hα : 0 < α) (hA : 0 < A)
    (E : Finset ℤ) (hE : ∀ z ∈ E, 0 ≤ z ∧ z ≤ N)
    (hcard : 2*(q+1) ≤ E.card) (hdens : α*N ≤ E.card)
    {w : ℕ → ℕ} {S Z : ℕ → ℝ}
    (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ k : ℕ, Tendsto (fun n => Z n / S n ^ k) atTop atTop) :
    ∀ᶠ n in atTop, ∀ (a b : ℤ) (θ : ℝ[X]),
      0 < b → Smooth (w n) b →
      (∀ z : ℤ, 0 ≤ z → z ≤ N → S n ≤ (a + b * z : ℤ) ∧
        ((a + b * z : ℤ) : ℝ) < 2 * S n) →
      (∀ z ∈ E, Rough (w n) (a + b * z)) →
      ((C (a : ℝ) + C (b : ℝ) * X) ^ e * θ).natDegree ≤ q →
      (∀ z ∈ E, ∃ k : ℤ,
        |((C (a : ℝ) + C (b : ℝ) * X) ^ e * θ).eval (z : ℝ) - (k : ℝ)| ≤
          A * (S n / Z n) ^ e) →
      ∃ M : ℚ[X], M.natDegree ≤ q - e ∧
        (∀ j p : ℕ, p.Prime → p ∣ (M.coeff j).den → p ≤ w n) ∧
        (∀ z ∈ E, Integral (M.eval (z : ℚ))) ∧
        ∀ z : ℤ, 0 ≤ z → z ≤ N →
          |θ.eval (z : ℝ) - (M.map (algebraMap ℚ ℝ)).eval (z : ℝ)| ≤
            uniformBound q α * A / Z n ^ e := by
  obtain ⟨v,hv,hsep⟩ := DenseIntegerNodes.separated_of_density E q hcard hdens
  obtain ⟨D,hD,K,hK,hquant⟩ := DenseRoughInterpolation.quantitative_exact_division
    hN hα E hE v hv hsep
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hDa : 0 < |(D : ℝ)| := abs_pos.mpr hDr
  have hC : 0 ≤ uniformBound q α := by unfold uniformBound; positivity
  have hsmall := (inverse_ratio_tendsto (hZ 1)).const_mul
    ((uniformBound q α + 1) * A)
  simp only [pow_one, mul_zero] at hsmall
  have hderiv := (inverse_ratio_tendsto (hZ (2 * q + 1))).const_mul
    (A * K * |(D : ℝ)| * 3 ^ q)
  simp only [mul_zero] at hderiv
  filter_upwards [hS.eventually (eventually_ge_atTop (1 : ℝ)),
    (hZ 1).eventually (eventually_ge_atTop (1 : ℝ)),
    hw.eventually (eventually_ge_atTop D.natAbs),
    hsmall.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / |(D : ℝ)|)),
    hderiv.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hnS hnZ hnw hnsmall hnderiv
  intro a b θ hb hbs hp hr hdeg hnear
  have hSn : 0 < S n := by linarith
  have hZn : S n ≤ Z n := by
    have h := hnZ
    simp only [pow_one] at h
    simpa only [one_mul] using (le_div_iff₀ hSn).mp h
  have hZpos : 0 < Z n := hSn.trans_le hZn
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hbr : 0 < (b : ℝ) := by exact_mod_cast hb
  have hbr1 : 1 ≤ |(b : ℝ)| := by
    rw [abs_of_pos hbr]
    exact_mod_cast hb
  have hp0 := hp 0 (by norm_num) (by omega)
  have hp1 := hp 1 (by norm_num) (by omega)
  simp only [mul_zero, add_zero] at hp0
  simp only [mul_one, Int.cast_add] at hp1
  have hbS : |(b : ℝ)| ≤ S n := by
    rw [abs_of_pos hbr]
    linarith [hp0.1, hp1.2]
  have ha : |(a : ℝ)| ≤ 2 * S n := by
    rw [abs_of_nonneg (hSn.le.trans hp0.1)]
    exact hp0.2.le
  have hDs : Smooth (w n) D := smooth_of_abs_le hD hnw
  have hcop : IsCoprime a b := by
    have h := coprime_smooth_rough hbs (hr (v 0) (hv 0))
    exact h.symm.of_add_mul_left_left
  have hε : 0 ≤ A * (S n / Z n) ^ e := by positivity
  have hratio : 0 ≤ S n / Z n := by positivity
  have hratio1 : S n / Z n ≤ 1 := (div_le_one hZpos).mpr hZn
  have hpow : (S n / Z n) ^ e ≤ S n / Z n := by
    simpa only [pow_one] using pow_le_pow_of_le_one hratio hratio1 he
  have hsmall' : (uniformBound q α + 1) * (A * (S n / Z n) ^ e) <
      1 / |(D : ℝ)| := by
    apply lt_of_le_of_lt _ hnsmall
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hderiv' : A * (S n / Z n) ^ e * K *
      (1 + |-(a : ℝ) / b|) ^ q < 1 / (|(D : ℝ)| * |(b : ℝ)| ^ q) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    exact (derivative_error_bound hA.le hK.le hDa.le hnS hZn ha hbr1 hbS he).trans_lt
      hnderiv
  obtain ⟨M,hMdeg,hMD,hMint,hMerr⟩ := hquant a b e θ (A*(S n/Z n)^e)
    hb0 hcop heq hε hdeg hnear
    (fun z hz => coprime_smooth_rough hDs (hr z hz)) hsmall' hderiv'
  refine ⟨M,hMdeg,coefficients_smooth hD hDs hMD,hMint,?_⟩
  intro z hz0 hzN
  have htz : S n ≤ (a : ℝ) + b*(z : ℝ) := by
    simpa only [Int.cast_add, Int.cast_mul] using (hp z hz0 hzN).1
  have htpos : 0 < (a : ℝ) + b*(z : ℝ) := hSn.trans_le htz
  have hx : (z : ℝ) ∈ Set.Icc 0 (N : ℝ) :=
    ⟨by exact_mod_cast hz0, by exact_mod_cast hzN⟩
  apply (mul_le_mul_iff_left₀ (pow_pos hSn e)).mp
  calc
    _ ≤ |θ.eval (z : ℝ)-(M.map (algebraMap ℚ ℝ)).eval (z : ℝ)| *
        ((a : ℝ)+b*(z : ℝ))^e := by gcongr
    _ = |((M.map (algebraMap ℚ ℝ)).eval (z : ℝ)-θ.eval (z : ℝ)) *
        ((a : ℝ)+b*(z : ℝ))^e| := by
      rw [abs_mul, abs_of_pos (pow_pos htpos e), abs_sub_comm]
    _ ≤ uniformBound q α * (A*(S n/Z n)^e) := hMerr _ hx
    _ = (uniformBound q α*A/Z n^e)*S n^e := by rw [div_pow]; ring

 

theorem eventually_exact_division {e q N : ℕ} (he : 1 ≤ e) (heq : e ≤ q)
    (hN : 0 < N) {α A : ℝ} (hα : 0 < α) (hA : 0 < A)
    {w : ℕ → ℕ} {S Z : ℕ → ℝ}
    (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ k : ℕ, Tendsto (fun n => Z n / S n ^ k) atTop atTop) :
    ∀ᶠ n in atTop, ∀ E : Finset ℤ,
      (∀ z ∈ E, 0 ≤ z ∧ z ≤ N) →
      2*(q+1) ≤ E.card → α*N ≤ E.card →
      ∀ (a b : ℤ) (θ : ℝ[X]),
      0 < b → Smooth (w n) b →
      (∀ z : ℤ, 0 ≤ z → z ≤ N → S n ≤ (a + b * z : ℤ) ∧
        ((a + b * z : ℤ) : ℝ) < 2 * S n) →
      (∀ z ∈ E, Rough (w n) (a + b * z)) →
      ((C (a : ℝ) + C (b : ℝ) * X) ^ e * θ).natDegree ≤ q →
      (∀ z ∈ E, ∃ k : ℤ,
        |((C (a : ℝ) + C (b : ℝ) * X) ^ e * θ).eval (z : ℝ) - (k : ℝ)| ≤
          A * (S n / Z n) ^ e) →
      ∃ M : ℚ[X], M.natDegree ≤ q - e ∧
        (∀ j p : ℕ, p.Prime → p ∣ (M.coeff j).den → p ≤ w n) ∧
        (∀ z ∈ E, Integral (M.eval (z : ℚ))) ∧
        ∀ z : ℤ, 0 ≤ z → z ≤ N →
          |θ.eval (z : ℝ) - (M.map (algebraMap ℚ ℝ)).eval (z : ℝ)| ≤
            uniformBound q α * A / Z n ^ e := by
  classical
  let P : Finset ℤ → ℕ → Prop := fun E n =>
    ∀ (a b : ℤ) (θ : ℝ[X]),
      0 < b → Smooth (w n) b →
      (∀ z : ℤ, 0 ≤ z → z ≤ N → S n ≤ (a + b * z : ℤ) ∧
        ((a + b * z : ℤ) : ℝ) < 2 * S n) →
      (∀ z ∈ E, Rough (w n) (a + b * z)) →
      ((C (a : ℝ) + C (b : ℝ) * X) ^ e * θ).natDegree ≤ q →
      (∀ z ∈ E, ∃ k : ℤ,
        |((C (a : ℝ) + C (b : ℝ) * X) ^ e * θ).eval (z : ℝ) - (k : ℝ)| ≤
          A * (S n / Z n) ^ e) →
      ∃ M : ℚ[X], M.natDegree ≤ q - e ∧
        (∀ j p : ℕ, p.Prime → p ∣ (M.coeff j).den → p ≤ w n) ∧
        (∀ z ∈ E, Integral (M.eval (z : ℚ))) ∧
        ∀ z : ℤ, 0 ≤ z → z ≤ N →
          |θ.eval (z : ℝ) - (M.map (algebraMap ℚ ℝ)).eval (z : ℝ)| ≤
            uniformBound q α * A / Z n ^ e
  change ∀ᶠ n in atTop, ∀ E : Finset ℤ,
    (∀ z ∈ E, 0 ≤ z ∧ z ≤ N) → 2*(q+1) ≤ E.card → α*N ≤ E.card → P E n
  have hs : ∀ E ∈ (Finset.Icc (0 : ℤ) (N : ℤ)).powerset,
      ∀ᶠ n in atTop, 2*(q+1) ≤ E.card → α*N ≤ E.card → P E n := by
    intro E hE
    by_cases hc : 2*(q+1) ≤ E.card
    · by_cases hd : α*N ≤ E.card
      · have hb : ∀ z ∈ E, 0 ≤ z ∧ z ≤ N := fun z hz =>
          Finset.mem_Icc.mp (Finset.mem_powerset.mp hE hz)
        have h := eventually_exact_division_fixed_set he heq hN hα hA E hb hc hd hw hS hZ
        filter_upwards [h] with n hn
        exact fun _ _ => hn
      · exact Filter.Eventually.of_forall (fun n _ hd' => (hd hd').elim)
    · exact Filter.Eventually.of_forall (fun n hc' _ => (hc hc').elim)
  have hh := (Filter.eventually_all_finset _).mpr hs
  filter_upwards [hh] with n hn E hE hc hd
  exact hn E (Finset.mem_powerset.mpr (fun z hz => Finset.mem_Icc.mpr (hE z hz))) hc hd

end DenseRoughScaleCompletion

 

end
end
end

end OAI
