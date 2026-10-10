import OAI.NumberTheory.PowerFree.WeightedFunctions

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped Classical BigOperators

noncomputable def coordinateLinearForm {n d : ℕ} {K : Type*} [Field K]
    (x : Fin d → Fin n) (c : Fin d → K) : MvPolynomial (Fin n) K :=
  ∑ j, C (c j)*X (x j)

theorem coordinateLinearForm_weighted {n d : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x : Fin d → Fin n) (c : Fin d → K) (U : ℝ) (hx : ∀ j, ω (x j) ≤ U) :
    Ideal.Quotient.mk I (coordinateLinearForm x c) ∈ weightedFunctions I ω U := by
  rw [coordinateLinearForm,map_sum]
  apply Submodule.sum_mem
  intro j _
  have he : Ideal.Quotient.mk I (C (c j)*X (x j)) = c j • Ideal.Quotient.mk I (X (x j)) := by
    change (Ideal.Quotient.mkₐ K I) (C (c j)*X (x j)) = _
    rw [←smul_eq_C_mul,map_smul]
    rfl
  rw [he]
  exact (weightedFunctions I ω U).smul_mem _ (weightedFunctions_mono I ω hω (hx j)
    (weightedFunctions_coordinate I ω hω (x j)))

theorem conjugateLinePolynomial_aeval {n d : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (s : Fin n) (x : Fin d → Fin n)
    (v : Fin d → K) (σ : K →+* ℂ) (P : Fin n → Polynomial ℂ)
    (hP : ∀ j, Polynomial.aeval (Ideal.Quotient.mk I (X s)) (P j) = Ideal.Quotient.mk I (X j)) :
    Polynomial.aeval (Ideal.Quotient.mk I (X s)) (conjugateLinePolynomial v σ (P ∘ x)) =
      Ideal.Quotient.mk I (coordinateLinearForm x (σ ∘ v)) := by
  simp only [conjugateLinePolynomial,coordinateLinearForm,map_sum,map_mul,Polynomial.aeval_C,
    Function.comp_apply,hP]
  congr 1

theorem norm_polynomial_line_degrees {n d : ℕ} {K : Type*} [Field K] [CharZero K]
    (hd : 0 < d) (I : Ideal (MvPolynomial (Fin n) ℂ))
    (x : Fin d → Fin n) (s : Fin d)
    (v : Fin d → K) (hv : LinearIndependent ℚ v) (σ : Fin d → K →+* ℂ)
    (θ : Fin d → ℂ) (hθ : Function.Injective θ)
    (b : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (k : ℕ) (hk : 0 < k)
    (hs : Transcendental ℂ (Ideal.Quotient.mk I (X (x s))))
    (hq : Transcendental ℂ (Ideal.Quotient.mk I q))
    (heq : ∀ i, Ideal.Quotient.mk I (coordinateLinearForm x (σ i ∘ v))^k * Ideal.Quotient.mk I (b i) =
      Ideal.Quotient.mk I q-algebraMap ℂ _ (θ i))
    (P : Fin n → Polynomial ℂ)
    (hP : ∀ j, Polynomial.aeval (Ideal.Quotient.mk I (X (x s))) (P j) = Ideal.Quotient.mk I (X j))
    (hPx : ∀ j, (P (x j)).natDegree ≤ 1)
    (z w : Fin n → ℤ) (hz : PointOn I z) (hw : PointOn I w) (hne : z (x s) ≠ w (x s)) :
    1+d*(k-1) ≤ (MvPolynomial.aeval P q).natDegree ∧
      ∀ i, (d-1)*(k-1) ≤ (MvPolynomial.aeval P (b i)).natDegree := by
  let : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
  let N : Polynomial ℂ := MvPolynomial.aeval P q
  let B : Fin d → Polynomial ℂ := fun i => MvPolynomial.aeval P (b i)
  let A : Fin d → Polynomial ℂ := fun i => conjugateLinePolynomial v (σ i) (P ∘ x)
  have hN : 0 < N.natDegree := by
    by_contra h
    have hp := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos h)
    have hev := curve_polynomial_substitution I (x s) P hP q
    change Polynomial.aeval _ N = _ at hev
    rw [hp,Polynomial.aeval_C] at hev
    exact hq (hev ▸ isAlgebraic_algebraMap (N.coeff 0))
  have hzP (j) : (P (x j)).eval (z (x s):ℂ) = (z (x j):ℂ) := by
    have hh := congrArg (pointEvaluation I z hz) (hP (x j))
    rw [←Polynomial.aeval_algHom_apply] at hh
    simpa only [pointEvaluation_X,Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id] using hh
  have hwP (j) : (P (x j)).eval (w (x s):ℂ) = (w (x j):ℂ) := by
    have hh := congrArg (pointEvaluation I w hw) (hP (x j))
    rw [←Polynomial.aeval_algHom_apply] at hh
    simpa only [pointEvaluation_X,Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id] using hh
  have hr (i) : (A i).coeff 1 ≠ 0 :=
    conjugateLinePolynomial_slope_ne_zero v hv (σ i) (P ∘ x) hPx s (z ∘ x) (w ∘ x) hne hzP hwP
  have hA (i) : A i = Polynomial.C ((A i).coeff 1)*Polynomial.X+Polynomial.C ((A i).coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one (conjugateLinePolynomial_degree v (σ i) (P ∘ x) hPx)
  have hid (i) : (Polynomial.C ((A i).coeff 1)*Polynomial.X+Polynomial.C ((A i).coeff 0))^k * B i =
      N-Polynomial.C (θ i) := by
    rw [←hA i]
    apply (transcendental_iff_injective.mp hs)
    simp only [map_mul,map_pow,map_sub,Polynomial.aeval_C]
    rw [conjugateLinePolynomial_aeval I (x s) x v (σ i) P hP,
      curve_polynomial_substitution I (x s) P hP (b i),curve_polynomial_substitution I (x s) P hP q]
    exact heq i
  have hh := curve_polynomial_degrees N hN θ (fun i => (A i).coeff 1) (fun i => (A i).coeff 0) B hθ hr hk hid
  simpa only [Fintype.card_fin,N,B] using And.intro hh.1 (fun i => (hh.2 i).2)

theorem norm_polynomial_line_hilbert {n d : ℕ} {K : Type*} [Field K] [CharZero K]
    (hd : 2 ≤ d) (I : Ideal (MvPolynomial (Fin n) ℂ))
    (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x : Fin d → Fin n) (s : Fin d) (U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (hxw : ω (x s) = U)
    (v : Fin d → K) (hv : LinearIndependent ℚ v) (σ : Fin d → K →+* ℂ)
    (θ : Fin d → ℂ) (hθ : Function.Injective θ)
    (b : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (hbw : ∀ i, Ideal.Quotient.mk I (b i) ∈ weightedFunctions I ω V)
    (k : ℕ) (hk : 2 ≤ k)
    (hs : Transcendental ℂ (Ideal.Quotient.mk I (X (x s))))
    (hq : Transcendental ℂ (Ideal.Quotient.mk I q))
    (heq : ∀ i, Ideal.Quotient.mk I (coordinateLinearForm x (σ i ∘ v))^k * Ideal.Quotient.mk I (b i) =
      Ideal.Quotient.mk I q-algebraMap ℂ _ (θ i))
    (P : Fin n → Polynomial ℂ)
    (hP : ∀ j, Polynomial.aeval (Ideal.Quotient.mk I (X (x s))) (P j) = Ideal.Quotient.mk I (X j))
    (hPx : ∀ j, (P (x j)).natDegree ≤ 1)
    (z w : Fin n → ℤ) (hz : PointOn I z) (hw : PointOn I w) (hne : z (x s) ≠ w (x s)) :
    let g := (d-1)*(k-1)
    ∀ T : ℝ, 0 ≤ T → T/U ≤ weightedHilbert I ω T ∧
      (g:ℝ)*T/V-(g:ℝ)*U*(g-1:ℕ)/V ≤ weightedHilbert I ω T := by
  dsimp only
  let g := (d-1)*(k-1)
  have hg : 0 < g := Nat.mul_pos (by omega) (by omega)
  have hdeg := (norm_polynomial_line_degrees (by omega) I x s v hv σ θ hθ b q k (by omega) hs hq heq P hP hPx z w hz hw hne).2
  have hsw : Ideal.Quotient.mk I (X (x s)) ∈ weightedFunctions I ω U := hxw ▸ weightedFunctions_coordinate I ω hω (x s)
  intro T hT
  constructor
  · have hh := polynomial_curve_hilbert_gain I ω hω _ _ hs Polynomial.X (Polynomial.aeval_X _) 1 (by decide)
      (by simp) U U hU.le hU hsw hsw T hT
    simpa only [Nat.cast_one,one_mul,Nat.sub_self,Nat.cast_zero,mul_zero,zero_div,sub_zero] using hh
  · let i : Fin d := ⟨0,by omega⟩
    exact polynomial_curve_hilbert_gain I ω hω _ _ hs (MvPolynomial.aeval P (b i))
      (curve_polynomial_substitution I (x s) P hP (b i)) g hg (hdeg i) U V hU.le hV hsw (hbw i) T hT

theorem polynomial_coordinates_injOn {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (s : Fin n)
    (P : Fin n → Polynomial ℂ)
    (hP : ∀ j, Polynomial.aeval (Ideal.Quotient.mk I (X s)) (P j) = Ideal.Quotient.mk I (X j)) :
    Set.InjOn (fun z : Fin n → ℤ => z s) {z | PointOn I z} := by
  intro z hz w hw he
  funext j
  have hzP := congrArg (pointEvaluation I z hz) (hP j)
  have hwP := congrArg (pointEvaluation I w hw) (hP j)
  rw [←Polynomial.aeval_algHom_apply] at hzP hwP
  simp only [pointEvaluation_X,Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id] at hzP hwP
  change z s = w s at he
  rw [he] at hzP
  exact Int.cast_injective (α := ℂ) (hzP.symm.trans hwP)

theorem norm_curve_alternatives {n d : ℕ}
    (hd : 2 ≤ d) (k : ℕ) (hk : 2 ≤ k)
    (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j) (x : Fin d → Fin n)
    (U V W Cbox : ℝ) (hU : 0 < U) (hV : 0 < V) (hW : 0 < W) (hCbox : 0 < Cbox)
    (hxw : ∀ j, ω (x j) = U) (hωW : ∀ j, ω j ≤ W)
    (e : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C H : ℝ, 0 < C ∧ 0 ≤ H ∧
      ∀ (K : Type) [Field K] [CharZero K] (v : Fin d → K), LinearIndependent ℚ v →
      ∀ (σ : Fin d → K →+* ℂ) (θ : Fin d → ℂ), Function.Injective θ →
      ∀ (X : ℝ), 2 ≤ X → ∀ (S : Finset (Fin n → ℤ)),
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime →
      affineDimension I ≤ 1 → affineDegree I ≤ e → (∀ z ∈ S, PointOn I z) →
      ∀ (b : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ),
      (∀ i, Ideal.Quotient.mk I (b i) ∈ weightedFunctions I ω V) →
      Transcendental ℂ (Ideal.Quotient.mk I q) →
      (∀ i, Ideal.Quotient.mk I (coordinateLinearForm x (σ i ∘ v))^k * Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I q-algebraMap ℂ _ (θ i)) →
      ∀ s : Fin d, Transcendental ℂ (Ideal.Quotient.mk I (MvPolynomial.X (x s))) →
      (S.card:ℝ) ≤ C*X^ε ∨
      (∀ T : ℝ, 0 ≤ T →
        min (2/U) (max (1/U) (((d-1)*(k-1):ℕ)/V))*T-H ≤ weightedHilbert I ω T) := by
  classical
  obtain ⟨C,hC,hred⟩ := norm_curve_polynomial_reduction ω hω x U W Cbox hU hW hCbox hxw hωW e ε hε
  let g := (d-1)*(k-1)
  let H := 2*(W/U+1)+(g:ℝ)*U*(g-1:ℕ)/V
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨max C 1,H,lt_of_lt_of_le hC (le_max_left _ _),hH,?_⟩
  intro K _ _ v hv σ θ hθ X hX S hbox I hI hdim hdeg hon b q hbw hq heq s hs
  have hCge : C*X^ε ≤ max C 1*X^ε := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
  rcases hred X hX S hbox I hI hdim hdeg hon s hs with hc | hh | ⟨P,hP,hPx⟩
  · exact Or.inl (hc.trans hCge)
  · right
    intro T hT
    have hl : min (2/U) (max (1/U) ((g:ℝ)/V))*T ≤ (2/U)*T :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hT
    have her : 2*(W/U+1) ≤ H := by
      dsimp [H]
      exact le_add_of_nonneg_right (by positivity)
    have hb := hh T hT
    change min (2/U) (max (1/U) ((g:ℝ)/V))*T-H ≤ _
    calc
      _ ≤ (2/U)*T-2*(W/U+1) := sub_le_sub hl her
      _ = 2*T/U-2*(W/U+1) := by ring
      _ ≤ _ := hb
  have hinj := polynomial_coordinates_injOn I (x s) P (fun j => (hP j).2)
  by_cases hp : ∃ z ∈ S, ∃ w ∈ S, z (x s) ≠ w (x s)
  · obtain ⟨z,hz,w,hw,hne⟩ := hp
    have hh := norm_polynomial_line_hilbert hd I ω hω x s U V hU hV (hxw s) v hv σ θ hθ b q hbw k hk hs hq heq
      P (fun j => (hP j).2) hPx z w (hon z hz) (hon w hw) hne
    right
    intro T hT
    have h1 := (hh T hT).1
    have h2 := (hh T hT).2
    have her : (g:ℝ)*U*(g-1:ℕ)/V ≤ H := by
      dsimp [H]
      exact le_add_of_nonneg_left (by positivity)
    have hl : min (2/U) (max (1/U) ((g:ℝ)/V))*T ≤ max (1/U) ((g:ℝ)/V)*T :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hT
    change min (2/U) (max (1/U) ((g:ℝ)/V))*T-H ≤ _
    apply (sub_le_sub_right hl H).trans
    rcases le_total (1/U) ((g:ℝ)/V) with hl' | hl'
    · rw [max_eq_right hl']
      calc
        _ = (g:ℝ)*T/V-H := by ring
        _ ≤ (g:ℝ)*T/V-(g:ℝ)*U*(g-1:ℕ)/V := sub_le_sub_left her _
        _ ≤ _ := h2
    · rw [max_eq_left hl']
      calc
        _ = T/U-H := by ring
        _ ≤ T/U := sub_le_self _ hH
        _ ≤ _ := h1
  · left
    have hcard : S.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro z hz w hw
      apply hinj (hon z hz) (hon w hw)
      by_contra he
      exact hp ⟨z,hz,w,hw,he⟩
    have hx : 1 ≤ X^ε := Real.one_le_rpow (by linarith) hε.le
    have hc : 1 ≤ max C 1 := le_max_right _ _
    calc
      (S.card:ℝ) ≤ 1 := by exact_mod_cast hcard
      _ ≤ max C 1*X^ε := one_le_mul_of_one_le_of_one_le hc hx

end

open scoped BigOperators

noncomputable def normBoxEnvelope (d h : ℕ) : ℝ :=
  if d = 5 then if h ≤ 2 then 196/1000 else if h = 3 then 154/1000 else 150/1000
  else if d = 6 then if h ≤ 2 then 176/1000 else if h = 3 then 134/1000 else 121/1000
  else if d = 7 then if h = 1 then 167/1000 else if h = 2 then 161/1000 else if h = 3 then 119/1000 else if h = 4 then 102/1000 else 100/1000
  else if h = 1 then 167/1000 else if h = 2 then 150/1000 else if h = 3 then 108/1000 else if h = 4 then 92/1000 else 85/1000

noncomputable def normBoxStage (d : ℕ) (i : Fin (d+1)) : ℝ := normBoxEnvelope d (d+1-i.val)
noncomputable def normBoxIncrement (d : ℕ) (i : Fin (d+1)) : ℝ :=
  if i.val = 0 then normBoxStage d i else normBoxStage d i - normBoxEnvelope d (d+2-i.val)

theorem normBoxEnvelope_pos (d h : ℕ) : 0 < normBoxEnvelope d h := by
  unfold normBoxEnvelope
  split_ifs <;> norm_num

theorem normBox_generic_certificate (d h : ℕ) (hd : 5 ≤ d) (hd' : d ≤ 8)
    (hh : 2 ≤ h) (hh' : h ≤ d) :
    1 ≤ (5:ℝ)*((d-2)*5+6:ℕ)^(h-1)*15^h/(5^h*6^h)*(normBoxEnvelope d h)^h := by
  interval_cases d <;> interval_cases h <;> norm_num [normBoxEnvelope] at *

theorem normBox_full_certificate (d : ℕ) (hd : 5 ≤ d) (hd' : d ≤ 8) :
    1 ≤ (((d-2)*5+6:ℕ):ℝ)^(d-1)*15^(d+1)/(5^d*6^d)*(normBoxEnvelope d (d+1))^(d+1) := by
  interval_cases d <;> norm_num [normBoxEnvelope]

theorem normBox_curve_certificate (d : ℕ) (hd : 5 ≤ d) (hd' : d ≤ 8) :
    1 ≤ 6*normBoxEnvelope d 1 := by
  interval_cases d <;> norm_num [normBoxEnvelope]

theorem normBox_increment_nonneg_5 (i : Fin (5+1)) : 0 ≤ normBoxIncrement 5 i := by
  fin_cases i <;> norm_num [normBoxIncrement,normBoxStage,normBoxEnvelope]

theorem normBox_prefix_5 (i : Fin (5+1)) :
    normBoxStage 5 i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (5+1) => j.val ≤ i.val), normBoxIncrement 5 j := by
  fin_cases i <;> norm_num [normBoxStage,normBoxIncrement,normBoxEnvelope,Fin.sum_univ_succ,Finset.sum_filter]

theorem normBox_sum_5 :
    (∑ i : Fin (5+1), ((5+1-i.val:ℕ):ℝ)*normBoxIncrement 5 i)+1/1000 ≤ 997/1000 := by
  norm_num [normBoxIncrement,normBoxStage,normBoxEnvelope,Fin.sum_univ_succ]

theorem normBox_increment_nonneg_6 (i : Fin (6+1)) : 0 ≤ normBoxIncrement 6 i := by
  fin_cases i <;> norm_num [normBoxIncrement,normBoxStage,normBoxEnvelope]

theorem normBox_prefix_6 (i : Fin (6+1)) :
    normBoxStage 6 i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (6+1) => j.val ≤ i.val), normBoxIncrement 6 j := by
  fin_cases i <;> norm_num [normBoxStage,normBoxIncrement,normBoxEnvelope,Fin.sum_univ_succ,Finset.sum_filter]

theorem normBox_sum_6 :
    (∑ i : Fin (6+1), ((6+1-i.val:ℕ):ℝ)*normBoxIncrement 6 i)+1/1000 ≤ 997/1000 := by
  norm_num [normBoxIncrement,normBoxStage,normBoxEnvelope,Fin.sum_univ_succ]

theorem normBox_increment_nonneg_7 (i : Fin (7+1)) : 0 ≤ normBoxIncrement 7 i := by
  fin_cases i <;> norm_num [normBoxIncrement,normBoxStage,normBoxEnvelope]

theorem normBox_prefix_7 (i : Fin (7+1)) :
    normBoxStage 7 i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (7+1) => j.val ≤ i.val), normBoxIncrement 7 j := by
  fin_cases i <;> norm_num [normBoxStage,normBoxIncrement,normBoxEnvelope,Fin.sum_univ_succ,Finset.sum_filter]

theorem normBox_sum_7 :
    (∑ i : Fin (7+1), ((7+1-i.val:ℕ):ℝ)*normBoxIncrement 7 i)+1/1000 ≤ 997/1000 := by
  norm_num [normBoxIncrement,normBoxStage,normBoxEnvelope,Fin.sum_univ_succ]

theorem normBox_increment_nonneg_8 (i : Fin (8+1)) : 0 ≤ normBoxIncrement 8 i := by
  fin_cases i <;> norm_num [normBoxIncrement,normBoxStage,normBoxEnvelope]

theorem normBox_prefix_8 (i : Fin (8+1)) :
    normBoxStage 8 i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (8+1) => j.val ≤ i.val), normBoxIncrement 8 j := by
  fin_cases i <;> norm_num [normBoxStage,normBoxIncrement,normBoxEnvelope,Fin.sum_univ_succ,Finset.sum_filter]

theorem normBox_sum_8 :
    (∑ i : Fin (8+1), ((8+1-i.val:ℕ):ℝ)*normBoxIncrement 8 i)+1/1000 ≤ 997/1000 := by
  norm_num [normBoxIncrement,normBoxStage,normBoxEnvelope,Fin.sum_univ_succ]

theorem normBox_increment_nonneg (d : ℕ) (hd : 5 ≤ d) (hd' : d ≤ 8)
    (i : Fin (d+1)) : 0 ≤ normBoxIncrement d i := by
  interval_cases d
  · exact normBox_increment_nonneg_5 i
  · exact normBox_increment_nonneg_6 i
  · exact normBox_increment_nonneg_7 i
  · exact normBox_increment_nonneg_8 i

theorem normBox_prefix (d : ℕ) (hd : 5 ≤ d) (hd' : d ≤ 8)
    (i : Fin (d+1)) :
    normBoxStage d i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (d+1) => j.val ≤ i.val), normBoxIncrement d j := by
  interval_cases d
  · exact normBox_prefix_5 i
  · exact normBox_prefix_6 i
  · exact normBox_prefix_7 i
  · exact normBox_prefix_8 i

theorem normBox_sum (d : ℕ) (hd : 5 ≤ d) (hd' : d ≤ 8) :
    (∑ i : Fin (d+1), ((d+1-i.val:ℕ):ℝ)*normBoxIncrement d i)+1/1000 ≤ 997/1000 := by
  interval_cases d
  · exact normBox_sum_5
  · exact normBox_sum_6
  · exact normBox_sum_7
  · exact normBox_sum_8
theorem normBox_generic_threshold (d h : ℕ) (hd : 5 ≤ d) (hd' : d ≤ 8)
    (hh : 2 ≤ h) (hh' : h ≤ d) :
    1/((h.factorial:ℝ)*(normBoxEnvelope d h)^h) ≤
      (5:ℝ)*(((d-2)*5+6:ℕ):ℝ)^(h-1)*15^h/((h.factorial:ℝ)*5^h*6^h) := by
  interval_cases d <;> interval_cases h <;> norm_num [normBoxEnvelope] at *

theorem normBox_full_threshold (d : ℕ) (hd : 5 ≤ d) (hd' : d ≤ 8) :
    1/(((d+1).factorial:ℝ)*(normBoxEnvelope d (d+1))^(d+1)) ≤
      (((d-2)*5+6:ℕ):ℝ)^(d-1)*15^(d+1)/(((d+1).factorial:ℝ)*5^d*6^d) := by
  interval_cases d <;> norm_num [normBoxEnvelope]

theorem normBox_curve_threshold (d : ℕ) (hd : 5 ≤ d) (hd' : d ≤ 8) :
    1/normBoxEnvelope d 1 ≤ min (2/(1/3:ℝ)) (max (1/(1/3:ℝ)) (((d-1)*(d-2-1):ℕ)/(2/5:ℝ))) := by
  interval_cases d <;> norm_num [normBoxEnvelope]
end QuarticPowerFree

end OAI
