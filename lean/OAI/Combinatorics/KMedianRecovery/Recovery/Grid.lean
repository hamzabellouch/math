import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.InitialState

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

lemma advance_upper {n : ℕ} (T t : ℕ) (ht : t≤T) (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef)
    (hlo : (realMatrix S.shape-(1/3:ℝ)^t • (1:Matrix (Fin n) (Fin n) ℝ)).PosSemidef) :
    ((2:ℝ) • realMatrix S.shape-realMatrix (advance (gridDenominator n T) rows S).shape).PosSemidef := by
  unfold advance
  split
  · simpa only [one_smul] using form_scalar_mono _ hS.posSemidef 1 2 (by norm_num)
  · split_ifs with ha
    · simpa only [one_smul] using form_scalar_mono _ hS.posSemidef 1 2 (by norm_num)
    · apply stepShape_upper _ (gridDenominator_pos n T (by omega)) _ _ (by simpa using hn) hS ha
        ((1/3:ℝ)^(T+1))
        (inflatedShape_precision _ _ (by simpa using hn) hS ha t T ht hlo)
      simpa only [Fintype.card_fin] using (gridDenominator_precision n T (by omega)).le

lemma iterate_shape_upper {n : ℕ} (T : ℕ) (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (h0 : (realMatrix S.shape-1).PosSemidef)
    (t : ℕ) (ht : t≤T) :
    ((2:ℝ)^t • realMatrix S.shape-realMatrix (iterate (gridDenominator n T) rows S t).shape).PosSemidef := by
  induction t with
  | zero => simp only [iterate,pow_zero,one_smul,sub_self]; exact PosSemidef.zero
  | succ t ih =>
    have hi := ih (by omega)
    have hp := iterate_pos _ (gridDenominator_pos n T (by omega)) rows S hn hS t
    have hl := iterate_shape_lower _ (gridDenominator_pos n T (by omega)) rows S hn hS h0 t
    have ha := advance_upper T t (by omega) rows _ hn hp hl
    have hs := form_le_smul _ _ hi 2 (by norm_num)
    rw [smul_smul,←pow_succ'] at hs
    exact form_le_trans _ _ _ ha hs

lemma iterate_shape_entry_bound (n T R : ℕ) (rows : List (Row n)) (hn : 2≤n) (hR : 1≤R)
    (t : ℕ) (ht : t≤T) (i j : Fin n) :
    |(iterate (gridDenominator n T) rows (Ellipsoid.initialState n (R:ℚ)) t).shape i j|≤(2:ℚ)^t*(R:ℚ)^2 := by
  have hRq : (1:ℚ)≤R := by exact_mod_cast hR
  have hp := iterate_pos _ (gridDenominator_pos n T (by omega)) rows _ hn
    (initial_pos n R (by positivity)) t
  have hb := iterate_shape_upper T rows _ hn (initial_pos n R (by positivity))
    (initial_shape_lower n R hRq) t ht
  rw [initial_realShape,smul_smul] at hb
  have hd (k : Fin n) : realMatrix (iterate (gridDenominator n T) rows (Ellipsoid.initialState n R) t).shape k k
      ≤(2:ℝ)^t*(R:ℝ)^2 := by
    have hh := hb.diag_nonneg (i:=k)
    simpa only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one,
      Rat.cast_natCast,sub_nonneg] using hh
  have hh := entry_bound_of_diagonal _ hp.posSemidef _ hd i j
  change |((iterate (gridDenominator n T) rows (Ellipsoid.initialState n R) t).shape i j:ℝ)|≤_ at hh
  exact_mod_cast hh

def OnGrid (D : ℕ) (q : ℚ) : Prop := ∃ z : ℤ, q=(z:ℚ)/(D:ℚ)

lemma onGrid_den (D : ℕ) (hD : 0<D) (q : ℚ) (h : OnGrid D q) : q.den≤D := by
  obtain ⟨z,rfl⟩ := h
  have hh := Rat.den_dvd z (D:ℤ)
  rw [←Rat.intCast_div_eq_divInt] at hh
  simp only [Int.cast_natCast] at hh
  exact Nat.le_of_dvd hD (Int.natCast_dvd_natCast.mp hh)

lemma gridShape_onGrid {n : ℕ} (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    OnGrid D (gridShape D A i j) := by
  by_cases hij : i=j
  · subst j
    refine ⟨⌊(D:ℚ)*A i i⌋+(n:ℤ),?_⟩
    simp only [gridShape,Matrix.add_apply,gridMatrix,gridFloor,Matrix.smul_apply,
      Matrix.one_apply_eq,smul_eq_mul,mul_one,Fintype.card_fin,Int.cast_add,Int.cast_natCast]
    exact (add_div _ _ _).symm
  · refine ⟨⌊(D:ℚ)*A i j⌋,?_⟩
    simp [gridShape,gridMatrix,gridFloor,hij]

lemma initial_onGrid (n D R : ℕ) (hD : 0<D) (i j : Fin n) :
    OnGrid D ((Ellipsoid.initialState n (R:ℚ)).shape i j) := by
  have hDq : (D:ℚ)≠0 := by exact_mod_cast hD.ne'
  by_cases hij : i=j
  · subst j
    refine ⟨(D:ℤ)*(R:ℤ)^2,?_⟩
    simp only [initialState,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one,
      Int.cast_mul,Int.cast_pow,Int.cast_natCast]
    field_simp
  · refine ⟨0,?_⟩
    simp [initialState,hij]

lemma iterate_onGrid {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n)
    (hS : ∀ i j,OnGrid D (S.shape i j)) (t : ℕ) :
    ∀ i j,OnGrid D ((iterate D rows S t).shape i j) := by
  induction t with
  | zero => exact hS
  | succ t ih =>
    intro i j
    simp only [iterate,advance]
    split
    · exact ih i j
    · split_ifs
      · exact ih i j
      · exact gridShape_onGrid D _ i j

lemma numerator_bound (q : ℚ) (D K : ℕ) (hd : q.den≤D) (hq : |q|≤(K:ℚ)) :
    q.num.natAbs≤K*D := by
  have he : (q.num.natAbs:ℚ)=|q| *(q.den:ℚ) := by
    have hm : (q.num:ℚ)=q*(q.den:ℚ) :=
      (div_eq_iff (by exact_mod_cast q.den_nz)).mp (Rat.num_div_den q)
    rw [Nat.cast_natAbs,Int.cast_abs,hm,abs_mul,abs_of_nonneg (by positivity : (0:ℚ)≤q.den)]
  have hh : (q.num.natAbs:ℚ)≤(K:ℚ)*(D:ℚ) := by
    rw [he]
    exact mul_le_mul hq (by exact_mod_cast hd) (by positivity) (by positivity)
  exact_mod_cast hh

theorem iterate_shape_height (n T R r : ℕ) (rows : List (Row n)) (hn : 2≤n) (hR : 1≤R)
    (hRr : R≤2^r) (t : ℕ) (ht : t≤T) (i j : Fin n) :
    let q := (iterate (gridDenominator n T) rows (Ellipsoid.initialState n (R:ℚ)) t).shape i j
    q.den≤2^(4+3*n+2*(T+1)) ∧
    q.num.natAbs≤2^(T+2*r+(4+3*n+2*(T+1))) := by
  dsimp only
  have hD := gridDenominator_pos n T (by omega)
  have hg := iterate_onGrid (gridDenominator n T) rows (Ellipsoid.initialState n (R:ℚ))
    (initial_onGrid n _ R hD) t i j
  have hd := onGrid_den _ hD _ hg
  refine ⟨hd.trans (gridDenominator_size n T),?_⟩
  have hv := iterate_shape_entry_bound n T R rows hn hR t ht i j
  have hv' : |(iterate (gridDenominator n T) rows (Ellipsoid.initialState n (R:ℚ)) t).shape i j|
      ≤((2^t*R^2:ℕ):ℚ) := by exact_mod_cast hv
  have hnum := numerator_bound _ _ _ hd hv'
  have hpow : 2^t*R^2≤2^(T+2*r) := by
    calc
      _ ≤2^T*(2^r)^2 := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) ht)
        (Nat.pow_le_pow_left hRr 2)
      _ = _ := by rw [←pow_mul,←pow_add]; congr 1; omega
  exact hnum.trans ((Nat.mul_le_mul hpow (gridDenominator_size n T)).trans_eq (pow_add _ _ _).symm)

end MetricKMedianRecovery.Ellipsoid

end OAI
