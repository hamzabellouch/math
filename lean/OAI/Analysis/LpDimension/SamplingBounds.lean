import OAI.Analysis.LpDimension.GradientSampling

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace
universe u uX

namespace SubpolynomialLp

lemma log_nat_lower (n : ℕ) (hn : 2 ≤ n) : (1/2:ℝ) ≤ Real.log n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hh := Real.one_sub_inv_le_log_of_pos hn0
  have hi : (n:ℝ)⁻¹ ≤ 1/2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) hn2
  linarith

lemma sampling_dimension_estimate (p r A : ℝ) (hp : 0 < p) (hr : 0 < r) (hA : 0 ≤ A)
    (n : ℕ) (hn : 2 ≤ n) :
    let H := 4*Real.log (n:ℝ)
    let K := H^2*Real.exp (A*(H^r+1))
    let d := ⌈(K^p)^2*(H+1)⌉₊+1
    (d:ℝ) ≤ Real.exp ((3+(4*p+1)/r+4*p*A)*4^r*(Real.log (n:ℝ))^r) := by
  dsimp only
  let H := 4*Real.log (n:ℝ)
  let K := H^2*Real.exp (A*(H^r+1))
  have hL := log_nat_lower n hn
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hHr : 1 ≤ H^r := Real.one_le_rpow hH hr.le
  have hK : 1 ≤ K := by
    have he : 1 ≤ Real.exp (A*(H^r+1)) := Real.one_le_exp_iff.mpr (by positivity)
    dsimp [K]
    nlinarith [sq_nonneg (H-1)]
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hM : 1 ≤ K^p := Real.one_le_rpow hK hp.le
  have hX : 1 ≤ (K^p)^2*(H+1) := by nlinarith [sq_nonneg (K^p-1)]
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (K^p)^2*(H+1) by positivity)
  have hd : (⌈(K^p)^2*(H+1)⌉₊+1:ℕ) ≤ (3:ℝ)*((K^p)^2*(H+1)) := by
    push_cast
    nlinarith
  have hlogH : Real.log H ≤ H^r/r := Real.log_le_rpow_div hH0.le hr
  have hlogK : Real.log K ≤ (2/r+2*A)*H^r := by
    rw [show K = H^2*Real.exp (A*(H^r+1)) from rfl,
      Real.log_mul (pow_ne_zero _ hH0.ne') (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
    have he := mul_le_mul_of_nonneg_left hHr hA
    simp only [div_eq_mul_inv] at hlogH ⊢
    nlinarith
  have hlogHp : Real.log (H+1) ≤ (1+1/r)*H^r := by
    have hh := Real.log_le_log (by positivity : 0 < H+1) (show H+1 ≤ 2*H by linarith)
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hH0.ne'] at hh
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    simp only [div_eq_mul_inv] at hlogH ⊢
    nlinarith
  have hlog3 : Real.log (3:ℝ) ≤ 2*H^r := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
    nlinarith
  have hlog : Real.log (3*((K^p)^2*(H+1))) ≤ (3+(4*p+1)/r+4*p*A)*H^r := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_rpow hK0]
    have hh := mul_le_mul_of_nonneg_left hlogK (by positivity : 0 ≤ 2*p)
    calc
      _ ≤ 2*H^r+(2*p)*((2/r+2*A)*H^r)+(1+1/r)*H^r := by linarith
      _ = _ := by ring
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by positivity)] at he
  have hHr' : H^r = 4^r*(Real.log (n:ℝ))^r := by
    exact Real.mul_rpow (by norm_num) (by linarith)
  have ht := hd.trans he
  rw [hHr'] at ht
  simpa only [mul_assoc] using ht

lemma sampling_probability_estimate (M ε : ℝ) (hM : 0 < M) (hε : 1 ≤ ε)
    (n N : ℕ) (hn : 2 ≤ n) (hN : 0 < N) (hNn : N ≤ n^2) :
    let H := 4*Real.log (n:ℝ)
    let d := ⌈M^2*(H+1)⌉₊+1
    (2*N:ℝ)*Real.exp (-((d:ℝ)*ε)^2/(2*d*(M/2)^2)) < 1 := by
  dsimp only
  let H := 4*Real.log (n:ℝ)
  let d := ⌈M^2*(H+1)⌉₊+1
  have hL := log_nat_lower n hn
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hd : (0:ℝ) < d := by dsimp [d]; positivity
  have hdM : M^2*(H+1) ≤ (d:ℝ) := by
    have hh := Nat.le_ceil (M^2*(H+1))
    dsimp [d]
    push_cast
    linarith
  have heps : 1 ≤ ε^2 := by nlinarith
  have halg : -((d:ℝ)*ε)^2/(2*d*(M/2)^2) = -(2*(d:ℝ)*ε^2/M^2) := by
    field_simp
  have hexp : -((d:ℝ)*ε)^2/(2*d*(M/2)^2) ≤ -2*(H+1) := by
    rw [halg]
    have hh : 2*(H+1) ≤ 2*(d:ℝ)*ε^2/M^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hM)).mpr
      have ht := mul_le_mul_of_nonneg_left heps hd.le
      nlinarith
    linarith
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log (2*(N:ℝ)) ≤ 1+2*Real.log (n:ℝ) := by
    have hh := Real.log_le_log (by positivity : 0 < 2*(N:ℝ))
      (show 2*(N:ℝ) ≤ 2*(n:ℝ)^2 by exact_mod_cast Nat.mul_le_mul_left 2 hNn)
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hn0.ne'), Real.log_pow] at hh
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at hh
    linarith
  change (2*(N:ℝ))*Real.exp (-((d:ℝ)*ε)^2/(2*d*(M/2)^2)) < 1
  calc
    _ = Real.exp (Real.log (2*(N:ℝ))+-((d:ℝ)*ε)^2/(2*d*(M/2)^2)) := by
      rw [Real.exp_add, Real.exp_log (by positivity)]
    _ < 1 := Real.exp_lt_one_iff.mpr (by dsimp [H] at hexp; linarith)

lemma coordinateDistance_comm (p : ℝ) {d : ℕ} (x y : Fin d → ℝ) :
    coordinateDistance p x y = coordinateDistance p y x := by
  unfold coordinateDistance
  congr 1
  exact Finset.sum_congr rfl (fun a _ => by rw [abs_sub_comm])

lemma coordinateDistance_self (p : ℝ) (hp : 0 < p) {d : ℕ} (x : Fin d → ℝ) :
    coordinateDistance p x x = 0 := by
  simp [coordinateDistance, Real.zero_rpow hp.ne', Real.zero_rpow (inv_ne_zero hp.ne')]

lemma all_pairs_of_edge_bounds {X : Type uX} [SeminormedAddCommGroup X] (p D s : ℝ) (hp : 0 < p)
    {n d : ℕ} (x : Fin n → X) (y : Fin n → Fin d → ℝ)
    (h : ∀ e : PairIndex n,
      s*‖x e.val.1-x e.val.2‖ ≤ coordinateDistance p (y e.val.1) (y e.val.2) ∧
      coordinateDistance p (y e.val.1) (y e.val.2) ≤ D*s*‖x e.val.1-x e.val.2‖) :
    ∀ i j, s*‖x i-x j‖ ≤ coordinateDistance p (y i) (y j) ∧
      coordinateDistance p (y i) (y j) ≤ D*s*‖x i-x j‖ := by
  intro i j
  rcases lt_trichotomy i j with hij|hij|hij
  · exact h ⟨(i,j),hij⟩
  · subst j
    simp [coordinateDistance_self p hp]
  · have hh := h ⟨(j,i),hij⟩
    simpa only [coordinateDistance_comm p (y j), norm_sub_rev (x j)] using hh

lemma pairIndex_card_le_square (n : ℕ) : Fintype.card (PairIndex n) ≤ n^2 := by
  calc
    _ ≤ Fintype.card (Fin n × Fin n) := Fintype.card_subtype_le _
    _ = n^2 := by simp [pow_two]

end SubpolynomialLp

end

end OAI
