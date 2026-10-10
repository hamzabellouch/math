import OAI.Combinatorics.SquareDifference.PhaseBounds

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

lemma sum_square_cells {E : Type*} [AddCommGroup E] (f : ℕ → E) (M : ℕ) :
    ∑ m ∈ range M, ∑ n ∈ Ico (m^2) ((m+1)^2), f n = ∑ n ∈ range (M^2), f n := by
  have hstep (m : ℕ) : ∑ n ∈ Ico (m^2) ((m+1)^2), f n =
      (∑ n ∈ range ((m+1)^2), f n)-(∑ n ∈ range (m^2), f n) :=
    sum_Ico_eq_sub f (by gcongr; omega)
  simp_rw [hstep]
  rw [sum_range_sub (fun m => ∑ n ∈ range (m^2), f n)]
  simp

lemma square_cell_card (m : ℕ) : (Ico (m^2) ((m+1)^2)).card = 2*m+1 := by
  have he : (m+1)^2=m^2+(2*m+1) := by ring
  simp [he]

lemma square_phase_cell (y : ℝ) (m M : ℕ) (hm : m < M) :
    ‖(2*((m : ℝ)+1)) • expPhase (y*(m+1)^2)-
      ∑ n ∈ Ico (m^2) ((m+1)^2), expPhase (y*(n+1))‖ ≤
      1+8*Real.pi*|y| *(M : ℝ)^2 := by
  have he : (2*((m : ℝ)+1)) • expPhase (y*(m+1)^2)-
      ∑ n ∈ Ico (m^2) ((m+1)^2), expPhase (y*(n+1)) =
      expPhase (y*(m+1)^2)+∑ n ∈ Ico (m^2) ((m+1)^2),
        (expPhase (y*(m+1)^2)-expPhase (y*(n+1))) := by
    simp only [sum_sub_distrib, sum_const, square_cell_card, nsmul_eq_mul, Complex.real_smul]
    push_cast
    ring
  rw [he]
  have hmR : (m : ℝ)+1 ≤ M := by exact_mod_cast (Nat.succ_le_of_lt hm)
  have hb (n : ℕ) (hn : n ∈ Ico (m^2) ((m+1)^2)) :
      ‖expPhase (y*(m+1)^2)-expPhase (y*(n+1))‖ ≤ 4*Real.pi*|y| *(M : ℝ) := by
    have hn0 : (m : ℝ)^2 ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
    have hn1 : (n : ℝ)+1 ≤ ((m : ℝ)+1)^2 := by
      exact_mod_cast Nat.succ_le_of_lt (mem_Ico.mp hn).2
    apply (expPhase_lipschitz _ _).trans
    rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith : 0 ≤ ((m : ℝ)+1)^2-((n : ℝ)+1))]
    have ht : ((m : ℝ)+1)^2-((n : ℝ)+1) ≤ 2*M := by nlinarith
    calc
      _ ≤ 2*Real.pi*(|y| *(2*M)) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ 1+∑ _n ∈ Ico (m^2) ((m+1)^2), 4*Real.pi*|y| *(M : ℝ) := by
      apply (norm_add_le _ _).trans
      rw [norm_expPhase]
      exact add_le_add le_rfl ((norm_sum_le _ _).trans (sum_le_sum hb))
    _ ≤ _ := by
      simp only [sum_const, square_cell_card, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      have hh : 2*(m : ℝ)+1 ≤ 2*M := by linarith
      calc
        _ ≤ 1+(2*(M : ℝ))*(4*Real.pi*|y| *M) := by gcongr
        _ = _ := by ring

lemma square_phase_riemann (y : ℝ) (M : ℕ) :
    ‖(∑ m ∈ range M, (2*((m : ℝ)+1)) • expPhase (y*(m+1)^2))-
      ∑ n ∈ range (M^2), expPhase (y*(n+1))‖ ≤
      (M : ℝ)*(1+8*Real.pi*|y| *(M : ℝ)^2) := by
  rw [← sum_square_cells (fun n => expPhase (y*(n+1))) M, ← sum_sub_distrib]
  calc
    _ ≤ ∑ _m ∈ range M, (1+8*Real.pi*|y| *(M : ℝ)^2) := by
      exact (norm_sum_le _ _).trans (sum_le_sum (fun m hm => square_phase_cell y m M (mem_range.mp hm)))
    _ = _ := by simp; ring

noncomputable def normalizedLinearSum (N : ℕ) (y : ℝ) : ℂ :=
  (N : ℝ)⁻¹ • ∑ n ∈ range N, expPhase (y*(n+1))

lemma squareWeight_riemann (N M : ℕ) (hlo : M^2 ≤ N) (hhi : N < (M+1)^2) (y : ℝ) :
    ‖(∑ m ∈ range M, squareWeight N y m)-normalizedLinearSum N y‖ ≤
      (3+8*Real.pi*|y| *(M : ℝ)^2)*M/N := by
  have hn : N-M^2 ≤ 2*M := by nlinarith [Nat.sub_add_cancel hlo]
  have hs : ‖(∑ n ∈ range N, expPhase (y*(n+1)))-
      ∑ n ∈ range (M^2), expPhase (y*(n+1))‖ ≤ 2*(M : ℝ) := by
    rw [← sum_Ico_eq_sub _ hlo]
    calc
      _ ≤ ∑ _n ∈ Ico (M^2) N, (1 : ℝ) := by
        simpa only [norm_expPhase] using
          (norm_sum_le (Ico (M^2) N) (fun n => expPhase (y*(n+1))))
      _ ≤ _ := by simpa using (show ((N-M^2 : ℕ) : ℝ) ≤ 2*(M : ℝ) by exact_mod_cast hn)
  have ht : ‖(∑ m ∈ range M, (2*((m : ℝ)+1)) • expPhase (y*(m+1)^2))-
      ∑ n ∈ range N, expPhase (y*(n+1))‖ ≤
      (3+8*Real.pi*|y| *(M : ℝ)^2)*M := by
    have := norm_sub_le_norm_sub_add_norm_sub
      (∑ m ∈ range M, (2*((m : ℝ)+1)) • expPhase (y*(m+1)^2))
      (∑ n ∈ range (M^2), expPhase (y*(n+1)))
      (∑ n ∈ range N, expPhase (y*(n+1)))
    rw [norm_sub_rev (∑ n ∈ range (M^2), _) (∑ n ∈ range N, _)] at this
    nlinarith [square_phase_riemann y M]
  have he : (∑ m ∈ range M, squareWeight N y m)-normalizedLinearSum N y =
      (N : ℝ)⁻¹ • ((∑ m ∈ range M, (2*((m : ℝ)+1)) • expPhase (y*(m+1)^2))-
        ∑ n ∈ range N, expPhase (y*(n+1))) := by
    simp only [squareWeight, normalizedLinearSum, smul_sub, smul_sum, smul_smul]
    congr 1
    apply sum_congr rfl
    intro m _
    congr 1
    ring
  rw [he, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (N : ℝ)⁻¹)]
  calc
    _ ≤ (N : ℝ)⁻¹*((3+8*Real.pi*|y| *(M : ℝ)^2)*M) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

lemma rational_quadratic_sum (α θ : ℝ) (a : ℤ) (q : ℕ) (hq : 8 ≤ q)
    (hc : IsCoprime a (q : ℤ)) (ha : |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2)
    (L M : ℕ) (hLM : L ≤ M) :
    ‖∑ m ∈ range L, expPhase (α*m^2+θ*m)‖ ≤
      Real.sqrt (M+2*(8*(M : ℝ)/q+1)*(2*M+4*q*(1+Real.log q))) := by
  apply Real.le_sqrt_of_sq_le
  apply (quadratic_sum_differencing α θ L M hLM).trans
  have hs : ∑ j ∈ Ico 1 M, phaseBound M (2*α*j) ≤
      (8*(M : ℝ)/q+1)*(2*M+4*q*(1+Real.log q)) := by
    apply le_trans _ (rational_spacing_sum α a q hq hc ha M)
    apply sum_le_sum_of_subset_of_nonneg
    · intro j hj; exact mem_range.mpr (mem_Ico.mp hj).2
    · intro j _ _; exact phaseBound_nonneg (Nat.cast_nonneg _) _
  nlinarith

lemma quadratic_sum_shift (α θ : ℝ) (L : ℕ) :
    ‖∑ m ∈ range L, expPhase (α*(m+1)^2+θ*(m+1))‖ =
      ‖∑ m ∈ range L, expPhase (α*m^2+(θ+2*α)*m)‖ := by
  have he (m : ℕ) : α*((m : ℝ)+1)^2+θ*((m : ℝ)+1) =
      (α+θ)+(α*m^2+(θ+2*α)*m) := by ring
  simp_rw [he, expPhase_add, ← mul_sum, norm_mul, norm_expPhase, one_mul]

lemma norm_linear_weighted_sum (z : ℕ → ℂ) (M : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ L ≤ M, ‖∑ m ∈ range L, z m‖ ≤ B) :
    ‖∑ m ∈ range M, ((m : ℝ)+1) • z m‖ ≤ 2*M*B := by
  rw [sum_range_by_parts]
  calc
    _ ≤ ‖((M-1 : ℕ) : ℝ)+1‖ * ‖∑ m ∈ range M, z m‖ +
        ∑ m ∈ range (M-1), ‖(((m+1 : ℕ) : ℝ)+1) - ((m : ℝ)+1)‖ *
          ‖∑ j ∈ range (m+1), z j‖ := by
      apply (norm_sub_le _ _).trans
      rw [norm_smul]
      exact add_le_add le_rfl ((norm_sum_le _ _).trans (le_of_eq (by simp)))
    _ ≤ (M : ℝ)*B+(M : ℝ)*B := by
      by_cases hM : M=0
      · simp [hM]
      have hlast : ((M-1 : ℕ) : ℝ)+1 = M := by
        exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ M by omega))
      rw [hlast, Real.norm_of_nonneg (Nat.cast_nonneg _)]
      apply add_le_add (mul_le_mul_of_nonneg_left (hb M le_rfl) (Nat.cast_nonneg _))
      calc
        _ ≤ ∑ _m ∈ range (M-1), B := by
          apply sum_le_sum
          intro m hm
          simp only [Nat.cast_add, Nat.cast_one]
          rw [show (m : ℝ)+1+1-((m : ℝ)+1)=1 by ring, norm_one, one_mul]
          exact hb (m+1) (by have := mem_range.mp hm; omega)
        _ ≤ (M : ℝ)*B := by
          simp only [sum_const, card_range, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le M 1)) hB
    _ = _ := by ring

lemma rational_weighted_quadratic_sum (α θ : ℝ) (a : ℤ) (q : ℕ) (hq : 8 ≤ q)
    (hc : IsCoprime a (q : ℤ)) (ha : |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2)
    (M N : ℕ) :
    ‖∑ m ∈ range M, (2*((m : ℝ)+1)/(N : ℝ)) •
      expPhase (α*(m+1)^2+θ*(m+1))‖ ≤
      (4*(M : ℝ)/N)*Real.sqrt
        (M+2*(8*(M : ℝ)/q+1)*(2*M+4*q*(1+Real.log q))) := by
  let B := Real.sqrt (M+2*(8*(M : ℝ)/q+1)*(2*M+4*q*(1+Real.log q)))
  have hb : ∀ L ≤ M, ‖∑ m ∈ range L,
      expPhase (α*(m+1)^2+θ*(m+1))‖ ≤ B := by
    intro L hLM
    rw [quadratic_sum_shift]
    exact rational_quadratic_sum α (θ+2*α) a q hq hc ha L M hLM
  have hm := norm_linear_weighted_sum
    (fun m => expPhase (α*(m+1)^2+θ*(m+1))) M B (Real.sqrt_nonneg _) hb
  simp_rw [show ∀ m : ℕ, 2*((m : ℝ)+1)/(N : ℝ) = (2/(N : ℝ))*((m : ℝ)+1) by
    intro m; ring, mul_smul, ← smul_sum]
  rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 2/(N : ℝ))]
  calc
    _ ≤ (2/(N : ℝ))*(2*M*B) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by dsimp only [B]; ring

lemma periodic_square_main (a : ℕ → ℂ) (T : ℕ) (hT : 0 < T)
    (hp : Function.Periodic a T) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ m, ‖a m‖ ≤ B) (M N : ℕ) (hM : 1 ≤ M)
    (hlo : M^2 ≤ N) (hhi : N < (M+1)^2) (y : ℝ) :
    ‖(∑ m ∈ range M, squareWeight N y m*a m)-
      periodicMean a T*normalizedLinearSum N y‖ ≤
      (2*T+1)*B*((4+8*Real.pi*|y| *(M : ℝ)^2)*M/N) := by
  have h1 := periodic_squareWeight_error a T hT hp B hB ha M N hM y
  have h2 := squareWeight_riemann N M hlo hhi y
  have h3 := norm_periodicMean a T hT B ha
  calc
    _ ≤ ‖(∑ m ∈ range M, squareWeight N y m*a m)-
        periodicMean a T*(∑ m ∈ range M, squareWeight N y m)‖ +
        ‖periodicMean a T*((∑ m ∈ range M, squareWeight N y m)-normalizedLinearSum N y)‖ := by
      convert norm_sub_le_norm_sub_add_norm_sub
        (∑ m ∈ range M, squareWeight N y m*a m)
        (periodicMean a T*(∑ m ∈ range M, squareWeight N y m))
        (periodicMean a T*normalizedLinearSum N y) using 1; rw [mul_sub]
    _ ≤ (2*T*B)*((4+8*Real.pi*|y| *(M : ℝ)^2)*M/N) +
        B*((3+8*Real.pi*|y| *(M : ℝ)^2)*M/N) := by
      rw [norm_mul]
      exact add_le_add h1 (mul_le_mul h3 h2 (norm_nonneg _) hB)
    _ ≤ _ := by
      calc
        _ ≤ (2*T*B)*((4+8*Real.pi*|y| *(M : ℝ)^2)*M/N) +
            B*((4+8*Real.pi*|y| *(M : ℝ)^2)*M/N) := by gcongr; norm_num
        _ = _ := by ring

lemma quadratic_fourier_weight (ι : Type*) [Fintype ι] (w : ι → ℂ) (θ : ι → ℝ)
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 8 ≤ q)
    (hc : IsCoprime a (q : ℤ)) (ha : |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2)
    (M N : ℕ) :
    ‖∑ m ∈ range M, squareWeight N α m *
       ∑ i, w i*expPhase (θ i*(m+1))‖ ≤
      (∑ i, ‖w i‖)*(4*(M : ℝ)/N)*Real.sqrt
        (M+2*(8*(M : ℝ)/q+1)*(2*M+4*q*(1+Real.log q))) := by
  let B := (4*(M : ℝ)/N)*Real.sqrt
        (M+2*(8*(M : ℝ)/q+1)*(2*M+4*q*(1+Real.log q)))
  have he : (∑ m ∈ range M, squareWeight N α m * ∑ i, w i*expPhase (θ i*(m+1))) =
      ∑ i, w i * ∑ m ∈ range M, (2*((m : ℝ)+1)/(N : ℝ)) •
        expPhase (α*(m+1)^2+θ i*(m+1)) := by
    simp_rw [mul_sum, squareWeight, expPhase_add, smul_mul_assoc, mul_smul_comm]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro m _
    congr 1
    ring
  rw [he]
  calc
    _ ≤ ∑ i, ‖w i‖*B := (norm_sum_le _ _).trans (sum_le_sum (fun i _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (rational_weighted_quadratic_sum α (θ i) a q hq hc ha M N)
        (norm_nonneg _)))
    _ = _ := by dsimp only [B]; rw [← sum_mul]; ring

lemma dirichlet_fraction (α : ℝ) (T : ℕ) (hT : 0<T) :
    ∃b : ℚ, b.den≤T ∧ |α-(b : ℝ)|≤1/(((T : ℝ)+1)*b.den) ∧
      |α-(b.num : ℝ)/b.den|≤1/(b.den : ℝ)^2 := by
  obtain ⟨b,hb,hd⟩ := Real.exists_rat_abs_sub_le_and_den_le α hT
  refine ⟨b,hd,hb,?_⟩
  rw [← Rat.cast_def]
  apply hb.trans
  have hp : (0 : ℝ)<b.den := Nat.cast_pos.mpr b.pos
  apply one_div_le_one_div_of_le (by positivity)
  rw [pow_two]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ_of_le hd) hp.le

lemma rational_weighted_quadratic_uniform (α θ : ℝ) (b : ℚ) (T : ℕ) (R : ℝ)
    (hR : 0<R) (hb8 : 8≤b.den) (hRT : R≤b.den) (hbT : b.den≤T)
    (ha : |α-(b : ℝ)|≤1/(b.den : ℝ)^2) (M N : ℕ) :
    ‖∑m∈range M, (2*((m : ℝ)+1)/(N : ℝ)) •
      expPhase (α*(m+1)^2+θ*(m+1))‖ ≤
      (4*(M : ℝ)/N)*Real.sqrt
        (5*M+32*(M : ℝ)^2/R+(64*M+8*T)*(1+Real.log T)) := by
  have h := rational_weighted_quadratic_sum α θ b.num b.den hb8
    b.isCoprime_num_den (by simpa only [Rat.cast_def] using ha) M N
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  have hb0 : (0 : ℝ)<b.den := Nat.cast_pos.mpr b.pos
  have hT0 : (0 : ℝ)<T := lt_of_lt_of_le hb0 (Nat.cast_le.mpr hbT)
  have hlog : Real.log b.den≤Real.log T := Real.log_le_log hb0 (Nat.cast_le.mpr hbT)
  have hL : 0≤1+Real.log T := by
    have : (1 : ℝ)≤T := by exact_mod_cast (b.pos.trans_le hbT)
    positivity
  have hedge : (M : ℝ)+2*(8*M/b.den+1)*(2*M+4*b.den*(1+Real.log b.den)) =
      5*M+32*(M : ℝ)^2/b.den+(64*M+8*b.den)*(1+Real.log b.den) := by
    field_simp
    ring
  rw [hedge]
  apply add_le_add
  · exact add_le_add le_rfl (div_le_div_of_nonneg_left (by positivity) hR hRT)
  · exact mul_le_mul (by exact_mod_cast (show 64*M+8*b.den≤64*M+8*T by omega))
      (by linarith) (by positivity) (by positivity)

lemma rational_difference_lower (b c : ℚ)
    (hnot : ¬ ∃k : ℤ, b-c=(k : ℚ)) :
    1/((b.den : ℝ)*c.den)≤circleDistance ((b : ℝ)-c) := by
  let k : ℤ := b.num*c.den-c.num*b.den
  let q : ℕ := b.den*c.den
  have hq : 0<q := Nat.mul_pos b.pos c.pos
  have hfrac : (b : ℝ)-(c : ℝ)=(k : ℝ)/q := by
    dsimp only [k,q]
    rw [Rat.cast_def b,Rat.cast_def c]
    push_cast
    field_simp
  have hnd : ¬ (q : ℤ)∣k := by
    rintro ⟨n,hn⟩
    apply hnot
    refine ⟨n,?_⟩
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_sub,Rat.cast_intCast,hfrac]
    have hh : (k : ℝ)=(q : ℝ)*(n : ℝ) := by exact_mod_cast hn
    rw [hh]
    field_simp
  rw [hfrac]
  simpa only [q,Nat.cast_mul] using rational_circleDistance_lower k q hq hnd

lemma normalizedLinearSum_norm (N : ℕ) (y : ℝ) : ‖normalizedLinearSum N y‖≤1 := by
  rw [normalizedLinearSum, norm_smul, Real.norm_of_nonneg (by positivity : 0≤(N : ℝ)⁻¹)]
  calc
    _ ≤ (N : ℝ)⁻¹*(N : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sum_le _ _).trans (by simp)
    _ ≤ 1 := inv_mul_le_one_of_le₀ le_rfl (by positivity)

lemma normalizedLinearSum_distance (N : ℕ) (y : ℝ) (hy : 0<circleDistance y) :
    ‖normalizedLinearSum N y‖≤1/(2*(N : ℝ)*circleDistance y) := by
  have he (n : ℕ) : y*((n : ℝ)+1)=y+(n : ℝ)*y := by ring
  simp only [normalizedLinearSum,he,expPhase_add,← mul_sum,norm_smul,norm_mul,
    norm_expPhase,one_mul,Real.norm_of_nonneg (by positivity : 0≤(N : ℝ)⁻¹)]
  calc
    _ ≤ (N : ℝ)⁻¹*(1/(2*circleDistance y)) :=
      mul_le_mul_of_nonneg_left (linear_phase_sum_distance y N hy) (by positivity)
    _ = _ := by ring

lemma normalizedLinearSum_add_int (N : ℕ) (y : ℝ) (k : ℤ) :
    normalizedLinearSum N (y+k)=normalizedLinearSum N y := by
  have he (n : ℕ) : expPhase ((y+k)*((n : ℝ)+1))=expPhase (y*(n+1)) := by
    rw [add_mul,expPhase_add]
    have hk : expPhase ((k : ℝ)*((n : ℝ)+1))=1 := by
      convert expPhase_int (k*((n : ℤ)+1)) using 1
      push_cast
      rfl
    rw [hk,mul_one]
  simp only [normalizedLinearSum,he]

lemma rational_approximation_separation (α : ℝ) (b c : ℚ) (T : ℕ)
    (he : |α-(b : ℝ)|≤1/(((T : ℝ)+1)*b.den)) (hT : 2*c.den≤T+1)
    (hnot : ¬ ∃k : ℤ, b-c=(k : ℚ)) :
    1/(2*(b.den : ℝ)*c.den)≤circleDistance (α-c) := by
  have hb : (0 : ℝ)<b.den := Nat.cast_pos.mpr b.pos
  have hc : (0 : ℝ)<c.den := Nat.cast_pos.mpr c.pos
  have hsmall : |α-(b : ℝ)|≤1/(2*(b.den : ℝ)*c.den) := by
    apply he.trans
    apply one_div_le_one_div_of_le (by positivity)
    have hT' : 2*(c.den : ℝ)≤(T : ℝ)+1 := by exact_mod_cast hT
    nlinarith
  have hsep := rational_difference_lower b c hnot
  have hdist := circleDistance_lipschitz ((b : ℝ)-c) (α-c)
  rw [show ((b : ℝ)-c)-(α-c)=(b : ℝ)-α by ring, abs_sub_comm (b : ℝ) α] at hdist
  have hhalf : 1/((b.den : ℝ)*c.den)=2*(1/(2*(b.den : ℝ)*c.den)) := by ring
  linarith

lemma normalizedLinearSum_rational_bound (N : ℕ) (α : ℝ) (b c : ℚ) (T : ℕ)
    (he : |α-(b : ℝ)|≤1/(((T : ℝ)+1)*b.den)) (hT : 2*c.den≤T+1)
    (hnot : ¬ ∃k : ℤ, b-c=(k : ℚ)) :
    ‖normalizedLinearSum N (α-c)‖≤((b.den : ℝ)*c.den)/N := by
  have hb : (0 : ℝ)<b.den := Nat.cast_pos.mpr b.pos
  have hc : (0 : ℝ)<c.den := Nat.cast_pos.mpr c.pos
  have hs := rational_approximation_separation α b c T he hT hnot
  have hd : 0<circleDistance (α-c) := lt_of_lt_of_le (by positivity) hs
  apply (normalizedLinearSum_distance N (α-c) hd).trans
  by_cases hn : N=0
  · simp [hn]
  have hN : (0 : ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  apply (div_le_div_iff₀ (by positivity : 0<2*(N : ℝ)*circleDistance (α-c)) hN).mpr
  have hs' : 1≤(2*(b.den : ℝ)*c.den)*circleDistance (α-c) :=
    by simpa only [mul_comm] using
      (div_le_iff₀ (by positivity : 0<2*(b.den : ℝ)*c.den)).mp hs
  nlinarith

noncomputable def modelCenterCoefficient {I : Type*} [Fintype I]
    (c : I → ℚ) (z : I → ℂ) (b : ℚ) : ℂ := by
  classical
  exact ∑i, if ∃k : ℤ, b-c i=(k : ℚ) then z i else 0

lemma rational_model_approximation {I : Type*} [Fintype I]
    (c : I → ℚ) (z : I → ℂ) (N : ℕ) (α : ℝ) (b : ℚ) (T L : ℕ)
    (hc : ∀i, (c i).den≤L) (hT : 2*L≤T+1)
    (he : |α-(b : ℝ)|≤1/(((T : ℝ)+1)*b.den)) :
    ‖(∑i, z i*normalizedLinearSum N (α-c i))-
      modelCenterCoefficient c z b*normalizedLinearSum N (α-b)‖≤
      (∑i, ‖z i‖)*((b.den : ℝ)*L/N) := by
  classical
  unfold modelCenterCoefficient
  rw [sum_mul, ← sum_sub_distrib, sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i _
  by_cases hi : ∃k : ℤ, b-c i=(k : ℚ)
  · rw [ite_eq_left hi]
    obtain ⟨k,hk⟩ := hi
    have hk' : (b : ℝ)-(c i : ℝ)=(k : ℝ) := by exact_mod_cast hk
    have hv : normalizedLinearSum N (α-c i)=normalizedLinearSum N (α-b) := by
      rw [show α-c i=(α-b)+(k : ℝ) by linarith, normalizedLinearSum_add_int]
    rw [hv, sub_self, norm_zero]
    positivity
  · rw [ite_eq_right hi,zero_mul,sub_zero,norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (normalizedLinearSum_rational_bound N α b (c i) T he
      (by have := hc i; omega) hi).trans
    gcongr
    exact_mod_cast hc i

lemma modelCenterCoefficient_zero {I : Type*} [Fintype I]
    (c : I → ℚ) (z : I → ℂ) (b : ℚ) (L : ℕ)
    (hc : ∀i, (c i).den≤L) (hb : L<b.den) : modelCenterCoefficient c z b=0 := by
  classical
  apply sum_eq_zero
  intro i _
  rw [ite_eq_right]
  rintro ⟨k,hk⟩
  have hbc : b=c i+k := by linarith
  have hd : b.den=(c i).den := by rw [hbc,Rat.add_intCast_den]
  have := hc i
  omega

lemma expPhase_rat_square_periodic (b : ℚ) (t : ℕ) (ht : b.den∣t) :
    Function.Periodic (fun m : ℕ => expPhase ((b : ℝ)*(m+1)^2)) t := by
  obtain ⟨k,rfl⟩ := ht
  intro m
  dsimp only
  rw [show (b : ℝ)*((m+(b.den*k) : ℕ)+1)^2 =
      (b : ℝ)*((m : ℝ)+1)^2 +
      ((b.num*(2*((m : ℤ)+1)*k+(b.den : ℤ)*k^2) : ℤ) : ℝ) by
    rw [Rat.cast_def]
    push_cast
    field_simp
    ring]
  rw [expPhase_add,expPhase_int,mul_one]

lemma periodic_rational_quadratic (v : ℕ → ℂ) (t : ℕ)
    (hv : Function.Periodic v t) (b : ℚ) :
    Function.Periodic (fun m : ℕ => v (m+1)*expPhase ((b : ℝ)*(m+1)^2)) (b.den*t) := by
  apply Function.Periodic.mul
  · have h := hv.nsmul b.den
    intro m
    simpa only [nsmul_eq_mul,Nat.cast_id,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h (m+1)
  · exact expPhase_rat_square_periodic b (b.den*t) (dvd_mul_right _ _)

lemma rational_kernel_major (v : ℕ → ℂ) (t : ℕ) (ht : 0<t)
    (hv : Function.Periodic v t) (B : ℝ) (hB : 0≤B) (hb : ∀m, ‖v m‖≤B)
    (b : ℚ) (α : ℝ) (M N : ℕ) (hM : 1≤M) (hlo : M^2≤N) (hhi : N<(M+1)^2) :
    ‖(∑m∈range M, squareWeight N α m*v (m+1))-
      periodicMean (fun m => v (m+1)*expPhase ((b : ℝ)*(m+1)^2)) (b.den*t)*
        normalizedLinearSum N (α-b)‖≤
      (2*((b.den*t : ℕ) : ℝ)+1)*B*
        ((4+8*Real.pi*|α-(b : ℝ)| *(M : ℝ)^2)*M/N) := by
  have he (m : ℕ) : squareWeight N α m*v (m+1)=
      squareWeight N (α-b) m*(v (m+1)*expPhase ((b : ℝ)*(m+1)^2)) := by
    unfold squareWeight
    have hx : expPhase (α*((m : ℝ)+1)^2)=
        expPhase ((α-b)*((m : ℝ)+1)^2)*expPhase ((b : ℝ)*(m+1)^2) := by
      rw [← expPhase_add]
      congr 1
      ring
    simp only [smul_mul_assoc]
    congr 1
    rw [hx]
    ring
  simp_rw [he]
  apply periodic_square_main _ (b.den*t) (Nat.mul_pos b.pos ht)
    (periodic_rational_quadratic v t hv b) B hB _ M N hM hlo hhi (α-b)
  intro m
  simpa only [norm_mul,norm_expPhase,mul_one] using hb (m+1)

lemma rational_kernel_major_uniform (v : ℕ → ℂ) (t : ℕ) (ht : 0<t)
    (hv : Function.Periodic v t) (B : ℝ) (hB : 0≤B) (hb : ∀m, ‖v m‖≤B)
    (b : ℚ) (α : ℝ) (T : ℕ) (R : ℝ) (hq : (b.den : ℝ)≤R)
    (ha : |α-(b : ℝ)|≤1/(((T : ℝ)+1)*b.den))
    (M N : ℕ) (hM : 1≤M) (hlo : M^2≤N) (hhi : N<(M+1)^2) :
    ‖(∑m∈range M, squareWeight N α m*v (m+1))-
      periodicMean (fun m => v (m+1)*expPhase ((b : ℝ)*(m+1)^2)) (b.den*t)*
        normalizedLinearSum N (α-b)‖≤
      (2*(t : ℝ)+1)*B*(4*R+8*Real.pi*N/((T : ℝ)+1))*M/N := by
  apply (rational_kernel_major v t ht hv B hB hb b α M N hM hlo hhi).trans
  have hq0 : (0 : ℝ)<b.den := Nat.cast_pos.mpr b.pos
  have hq1 : (1 : ℝ)≤b.den := by exact_mod_cast b.pos
  have hT0 : (0 : ℝ)<(T : ℝ)+1 := by positivity
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (show 0<N by nlinarith)
  have hscale : |α-(b : ℝ)| *(M : ℝ)^2≤(N : ℝ)/(((T : ℝ)+1)*b.den) := by
    calc
      _ ≤ (1/(((T : ℝ)+1)*b.den))*(N : ℝ) := by
        gcongr
        exact_mod_cast hlo
      _ = _ := by ring
  have hedge : 2*(b.den : ℝ)*t+1≤(2*(t : ℝ)+1)*b.den := by nlinarith
  have hmid : (b.den : ℝ)*(4+8*Real.pi*(|α-(b : ℝ)| *(M : ℝ)^2))≤
      4*R+8*Real.pi*N/((T : ℝ)+1) := by
    calc
      _ ≤ (b.den : ℝ)*(4+8*Real.pi*((N : ℝ)/(((T : ℝ)+1)*b.den))) := by gcongr
      _ = 4*(b.den : ℝ)+8*Real.pi*N/((T : ℝ)+1) := by field_simp
      _ ≤ _ := by gcongr
  push_cast
  calc
    _ = (2*(b.den : ℝ)*t+1)*B*(4+8*Real.pi*(|α-(b : ℝ)| *(M : ℝ)^2))*M/N := by ring
    _ ≤ ((2*(t : ℝ)+1)*b.den)*B*(4+8*Real.pi*(|α-(b : ℝ)| *(M : ℝ)^2))*M/N := by gcongr
    _ = (2*(t : ℝ)+1)*B*((b.den : ℝ)*(4+8*Real.pi*(|α-(b : ℝ)| *(M : ℝ)^2)))*M/N := by ring
    _ ≤ _ := by gcongr

lemma quadratic_fourier_weight_uniform {I : Type*} [Fintype I]
    (w : I → ℂ) (θ : I → ℝ) (α : ℝ) (b : ℚ) (T : ℕ) (R : ℝ)
    (hR : 0<R) (hb8 : 8≤b.den) (hRT : R≤b.den) (hbT : b.den≤T)
    (ha : |α-(b : ℝ)|≤1/(b.den : ℝ)^2) (M N : ℕ) :
    ‖∑m∈range M, squareWeight N α m*∑i, w i*expPhase (θ i*(m+1))‖≤
      (∑i, ‖w i‖)*(4*(M : ℝ)/N)*Real.sqrt
        (5*M+32*(M : ℝ)^2/R+(64*M+8*T)*(1+Real.log T)) := by
  have he : (∑m∈range M, squareWeight N α m*∑i, w i*expPhase (θ i*(m+1))) =
      ∑i, w i*∑m∈range M, (2*((m : ℝ)+1)/(N : ℝ)) •
        expPhase (α*(m+1)^2+θ i*(m+1)) := by
    simp_rw [mul_sum,squareWeight,expPhase_add,smul_mul_assoc,mul_smul_comm]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro m _
    congr 1
    ring
  rw [he]
  calc
    _ ≤ ∑i, ‖w i‖*((4*(M : ℝ)/N)*Real.sqrt
        (5*M+32*(M : ℝ)^2/R+(64*M+8*T)*(1+Real.log T))) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (rational_weighted_quadratic_uniform α (θ i) b T R hR hb8 hRT hbT ha M N) (norm_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

end SquareDifference
end

end OAI
