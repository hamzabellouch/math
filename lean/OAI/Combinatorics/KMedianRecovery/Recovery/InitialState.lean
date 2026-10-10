import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ExecutionState
import OAI.Combinatorics.KMedianRecovery.Recovery.IterationBlocks

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

lemma realMatrix_one {V : Type*} [DecidableEq V] :
    realMatrix (1:Matrix V V ℚ)=(1:Matrix V V ℝ) := by
  ext i j
  by_cases h : i=j <;> simp [realMatrix,Matrix.one_apply,h]

def initialState (n : ℕ) (R : ℚ) : State n := ⟨(R^2) • 1,0⟩

lemma initial_realShape (n : ℕ) (R : ℚ) :
    realMatrix (initialState n R).shape=(R:ℝ)^2 • (1:Matrix (Fin n) (Fin n) ℝ) := by
  simp only [initialState,real_smul_matrix,realMatrix_one,Rat.cast_pow]

lemma initial_pos (n : ℕ) (R : ℚ) (hR : 0<R) :
    (realMatrix (initialState n R).shape).PosDef := by
  rw [initial_realShape]
  exact Matrix.PosDef.one.smul (sq_pos_of_pos (Rat.cast_pos.mpr hR))

lemma initial_shape_lower (n : ℕ) (R : ℚ) (hR : 1≤R) :
    (realMatrix (initialState n R).shape-1).PosSemidef := by
  rw [initial_realShape]
  have hRr : (1:ℝ)≤(R:ℝ) := by exact_mod_cast hR
  simpa only [one_smul] using form_scalar_mono (1:Matrix (Fin n) (Fin n) ℝ)
    Matrix.PosSemidef.one 1 ((R:ℝ)^2) (by nlinarith)

lemma initial_inverse (n : ℕ) (R : ℚ) (hR : 0<R) :
    (realMatrix (initialState n R).shape)⁻¹=
      (1/(R:ℝ)^2) • (1:Matrix (Fin n) (Fin n) ℝ) := by
  rw [initial_realShape,inv_smul_real _ Matrix.PosDef.one _
    (pow_ne_zero _ (Rat.cast_ne_zero.mpr hR.ne')),inv_one,one_div]

lemma initial_inverse_det (n : ℕ) (R : ℚ) (hR : 0<R) :
    (realMatrix (initialState n R).shape)⁻¹.det=(1/(R:ℝ)^2)^n := by
  rw [initial_inverse n R hR,Matrix.det_smul,Matrix.det_one,mul_one,Fintype.card_fin]

lemma initial_contains_box (n : ℕ) (hn : 1≤n) (R : ℚ) (hR : 0<R) (B : ℝ)
    (hB : 0≤B) (hRB : (n:ℝ)*B≤(R:ℝ)) (x : Fin n → ℝ) (hx : ∀ i, |x i|≤B) :
    quad (realMatrix (initialState n R).shape)⁻¹ (x-realVector (initialState n R).center)≤1 := by
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hR' : 0<(R:ℝ) := Rat.cast_pos.mpr hR
  have hc : realVector (initialState n R).center=0 := by ext i; simp [initialState,realVector]
  rw [hc,sub_zero,initial_inverse n R hR,quad_smul_matrix,quad_one]
  have hs : sqNorm x≤(n:ℝ)*B^2 := by
    unfold sqNorm
    have hh := Finset.sum_le_sum (fun i (_hi : i∈(Finset.univ:Finset (Fin n))) =>
      sq_le_sq₀ (abs_nonneg (x i)) hB |>.mpr (hx i))
    simpa only [sq_abs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have hrr : (n:ℝ)*B^2≤(R:ℝ)^2 := by
    have hnB : 0≤(n:ℝ)*B := mul_nonneg (by positivity) hB
    have hsq := (sq_le_sq₀ hnB hR'.le).mpr hRB
    nlinarith [mul_nonneg (show 0≤(n:ℝ)-1 by linarith) (sq_nonneg B)]
  have hmul := mul_le_mul_of_nonneg_left (hs.trans hrr) (by positivity : 0≤1/(R:ℝ)^2)
  simpa only [one_div_mul_cancel (pow_ne_zero _ hR'.ne')] using hmul

lemma single_diameter_bound {n : ℕ} (x : Fin n → ℝ) (B r : ℝ) (hB : ∀ i, |x i|≤B)
    (hr : |r|≤1) (i j : Fin n) : |(x+r • (Pi.single i (1:ℝ) : Fin n → ℝ)) j|≤B+1 := by
  calc
    _ ≤ |x j|+|r*((Pi.single i (1:ℝ) : Fin n → ℝ) j)| := abs_add_le _ _
    _ ≤ B+1 := by
      apply add_le_add (hB j)
      by_cases he : j=i
      · subst j
        simpa using hr
      · simp [Pi.single_eq_of_ne he]

lemma initial_diameters (n : ℕ) (hn : 1≤n) (B : ℚ) (hB : 0≤B)
    (x : Fin n → ℝ) (hx : ∀ i, |x i|≤(B:ℝ)) (r : ℝ) (hr : 0<r) (hr1 : r≤1) :
    ∀ i, quad (realMatrix (initialState n ((n:ℚ)*(B+1))).shape)⁻¹
      (x+r • Pi.single i 1-realVector (initialState n ((n:ℚ)*(B+1))).center)≤1 ∧
      quad (realMatrix (initialState n ((n:ℚ)*(B+1))).shape)⁻¹
      (x+(-r) • Pi.single i 1-realVector (initialState n ((n:ℚ)*(B+1))).center)≤1 := by
  have hnq : (0:ℚ)<n := by exact_mod_cast (show 0<n by omega)
  have hRq : 0<(n:ℚ)*(B+1) := mul_pos hnq (by linarith)
  have hB' : 0≤(B:ℝ)+1 := by exact_mod_cast (show (0:ℚ)≤B+1 by linarith)
  have hRB : (n:ℝ)*((B:ℝ)+1)≤((n:ℚ)*(B+1):ℚ) := by push_cast; rfl
  intro i
  constructor
  · exact initial_contains_box n hn _ hRq _ hB' hRB _
      (fun j => single_diameter_bound x (B:ℝ) r hx (by rwa [abs_of_pos hr]) i j)
  · exact initial_contains_box n hn _ hRq _ hB' hRB _
      (fun j => single_diameter_bound x (B:ℝ) (-r) hx (by rwa [abs_neg,abs_of_pos hr]) i j)

def weakSolve {n : ℕ} (rows : List (Row n)) (R : ℚ) (p s : ℕ) : Option (Fin n → ℚ) :=
  let T := iterationBudget n p s
  let c := (iterate (gridDenominator n T) rows (initialState n R) T).center
  if badRow rows c=none then some c else none

lemma weakSolve_sound {n : ℕ} (rows : List (Row n)) (R : ℚ) (p s : ℕ) (c : Fin n → ℚ)
    (hc : weakSolve rows R p s=some c) : ∀ r∈rows, r.Holds c := by
  dsimp only [weakSolve] at hc
  split_ifs at hc with hh
  · cases hc
    exact (badRow_none _ _).mp hh

lemma weakSolve_complete_diameters {n : ℕ} (rows : List (Row n)) (hn : 2≤n)
    (R : ℚ) (hR : 1≤R) (p s : ℕ) (r : ℝ) (hr : 0<r)
    (hRp : (R:ℝ)≤(2:ℝ)^s) (hrp : 1/r≤(2:ℝ)^p)
    (x : Fin n → ℝ) (hx : ∀ q∈rows, q.RealHolds x)
    (hdiam : ∀ i, (∀ q∈rows, q.RealHolds (x+r • Pi.single i 1)) ∧
      (∀ q∈rows, q.RealHolds (x+(-r) • Pi.single i 1)))
    (hinit : ∀ i, quad (realMatrix (initialState n R).shape)⁻¹
      (x+r • Pi.single i 1-realVector (initialState n R).center)≤1 ∧
      quad (realMatrix (initialState n R).shape)⁻¹
      (x+(-r) • Pi.single i 1-realVector (initialState n R).center)≤1) :
    ∃ c, weakSolve rows R p s=some c := by
  let T := iterationBudget n p s
  let D := gridDenominator n T
  let S := initialState n R
  have hRq : 0<R := lt_of_lt_of_le (by norm_num) hR
  have hRr : 0<(R:ℝ) := Rat.cast_pos.mpr hRq
  have hS := initial_pos n R hRq
  have h0 := initial_shape_lower n R hR
  have hD := gridDenominator_pos n T (by omega)
  have hvalid : ∀ q∈rows, q.Holds (iterate D rows S T).center := by
    by_contra hbad
    have hdet := iterate_block_growth rows S hn hS h0 (iterationBlocks n p s) hbad x hx
    have hM := (iterate_pos D hD rows S hn hS T).inv
    have hd := det_bound_of_diameters _ hM
      (x-realVector (iterate D rows S T).center) r hr (fun i => ?_)
    · have hb := determinant_budget n p s (R:ℝ) r hRr hr hRp hrp
      rw [initial_inverse_det n R hRq] at hdet
      simp only [Fintype.card_fin] at hd
      exact (not_lt_of_ge (hdet.trans hd)) hb
    · have hp := iterate_contains D hD rows S hn hS (x+r • Pi.single i 1) (hdiam i).1 (hinit i).1 T
      have hm := iterate_contains D hD rows S hn hS (x+(-r) • Pi.single i 1) (hdiam i).2 (hinit i).2 T
      have he (v : Fin n → ℝ) : x+v-realVector (iterate D rows S T).center=
          (x-realVector (iterate D rows S T).center)+v := by abel
      simpa only [he] using And.intro hp hm
  refine ⟨(iterate D rows S T).center,?_⟩
  exact ite_eq_left ((badRow_none _ _).mpr hvalid)

def relaxedRow {n : ℕ} (eps : ℚ) (r : Row n) : Row n := ⟨r.coeff,r.bound+eps⟩

def relaxedRows {n : ℕ} (eps : ℚ) (rows : List (Row n)) : List (Row n) := rows.map (relaxedRow eps)

lemma relaxedRows_feasible {n : ℕ} (eps : ℚ) (heps : 0≤eps) (rows : List (Row n))
    (x : Fin n → ℝ) (hx : ∀ q∈rows, q.RealHolds x) :
    ∀ q∈relaxedRows eps rows, q.RealHolds x := by
  intro q hq
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
  have hh := hx a ha
  change a.realValue x≤((a.bound+eps:ℚ):ℝ)
  push_cast
  exact le_trans hh (le_add_of_nonneg_right (Rat.cast_nonneg.mpr heps))

lemma row_value_single {n : ℕ} (q : Row n) (x : Fin n → ℝ) (r : ℝ) (i : Fin n) :
    q.realValue (x+r • Pi.single i 1)=q.realValue x+r*(q.coeff i:ℝ) := by
  change realVector q.coeff ⬝ᵥ (x+r • Pi.single i 1)=realVector q.coeff ⬝ᵥ x+r*(q.coeff i:ℝ)
  rw [dotProduct_add,dotProduct_smul,smul_eq_mul,dotProduct_single]
  simp [realVector]

lemma relaxed_diameter {n : ℕ} (eps H : ℚ) (rows : List (Row n))
    (hH : 0≤(H:ℝ)) (hcoeff : ∀ q∈rows, ∀ j, |(q.coeff j:ℝ)|≤(H:ℝ))
    (x : Fin n → ℝ) (hx : ∀ q∈rows, q.RealHolds x) (r : ℝ)
    (hr : |r| *(H:ℝ)≤(eps:ℝ)) (i : Fin n) :
    ∀ q∈relaxedRows eps rows, q.RealHolds (x+r • Pi.single i 1) := by
  intro q hq
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
  change a.realValue (x+r • Pi.single i 1)≤((a.bound+eps:ℚ):ℝ)
  rw [row_value_single]
  push_cast
  have hb := mul_le_mul_of_nonneg_left (hcoeff a ha i) (abs_nonneg r)
  have hab := le_abs_self (r*(a.coeff i:ℝ))
  rw [abs_mul] at hab
  have _ := hH
  exact add_le_add (hx a ha) (hab.trans (hb.trans hr))

theorem weakSolve_complete {n : ℕ} (rows : List (Row n)) (hn : 2≤n)
    (B H eps : ℚ) (hB : 0≤B) (hH : 1≤H) (heps : 0<eps) (heps1 : eps≤1)
    (p s : ℕ) (hRp : ((n:ℚ)*(B+1):ℚ)≤(2:ℚ)^s) (hrp : H/eps≤(2:ℚ)^p)
    (hcoeff : ∀ q∈rows, ∀ j, |q.coeff j|≤H)
    (x : Fin n → ℝ) (hx : ∀ q∈rows, q.RealHolds x) (hbox : ∀ i, |x i|≤(B:ℝ)) :
    ∃ c, weakSolve (relaxedRows eps rows) ((n:ℚ)*(B+1)) p s=some c := by
  let r : ℝ := (eps:ℝ)/(H:ℝ)
  have hHp : 0<(H:ℝ) := by exact_mod_cast (show (0:ℚ)<H by linarith)
  have hep : 0<(eps:ℝ) := Rat.cast_pos.mpr heps
  have hr : 0<r := div_pos hep hHp
  have hr1 : r≤1 := (div_le_one hHp).mpr (by exact_mod_cast (show eps≤H by linarith))
  have hR : (1:ℚ)≤(n:ℚ)*(B+1) := by
    have hnq : (1:ℚ)≤n := by exact_mod_cast (show 1≤n by omega)
    nlinarith
  have hpr : 1/r≤(2:ℝ)^p := by
    have hh : ((H/eps:ℚ):ℝ)≤((2:ℚ)^p:ℚ) := by exact_mod_cast hrp
    simpa only [r,one_div_div,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using hh
  have hcoef : ∀ q∈rows, ∀ j, |(q.coeff j:ℝ)|≤(H:ℝ) := by
    intro q hq j
    exact_mod_cast hcoeff q hq j
  have heq : r*(H:ℝ)=(eps:ℝ) := div_mul_cancel₀ _ hHp.ne'
  apply weakSolve_complete_diameters _ hn _ hR p s r hr (by exact_mod_cast hRp) hpr x
    (relaxedRows_feasible eps heps.le rows x hx) _ (initial_diameters n (by omega) B hB x hbox r hr hr1)
  intro i
  constructor
  · exact relaxed_diameter eps H rows hHp.le hcoef x hx r (by rw [abs_of_pos hr,heq]) i
  · exact relaxed_diameter eps H rows hHp.le hcoef x hx (-r) (by rw [abs_neg,abs_of_pos hr,heq]) i

end MetricKMedianRecovery.Ellipsoid

end OAI
