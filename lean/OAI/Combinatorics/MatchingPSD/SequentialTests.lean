import OAI.Combinatorics.MatchingPSD.SquareRootDisturbance

namespace OAI

universe u_1 u_2

namespace PerfectMatchingPSD
open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius
variable {R : Type u_1} [Fintype R] [DecidableEq R]

omit [DecidableEq R] in
lemma congruence_mono {A B : Matrix R R ℝ} (h : A ≤ B) (X : Matrix R R ℝ) :
    Xᵀ * A * X ≤ Xᵀ * B * X := by
  change (Xᵀ * B * X - Xᵀ * A * X).PosSemidef
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, mul_sub, sub_mul]
    using h.conjTranspose_mul_mul_same X

omit [Fintype R] in
lemma effect_le_one (F : Bool → Matrix R R ℝ) (hF : ∀ b, 0 ≤ F b)
    (hs : F false + F true ≤ 1) (b : Bool) : F b ≤ 1 := by
  cases b
  · exact (le_add_of_nonneg_right (hF true)).trans hs
  · exact (le_add_of_nonneg_left (hF false)).trans hs

lemma effects_square_sum_le (F : Bool → Matrix R R ℝ) (hF : ∀ b, 0 ≤ F b)
    (hs : F false + F true ≤ 1) :
    (F false)ᵀ * F false + (F true)ᵀ * F true ≤ 1 := by
  have h0 : (F false)ᵀ = F false := (hF false).posSemidef.isHermitian.eq
  have h1 : (F true)ᵀ = F true := (hF true).posSemidef.isHermitian.eq
  rw [h0, h1, ← pow_two, ← pow_two]
  exact (add_le_add (square_le_self (hF false) (effect_le_one F hF hs false))
    (square_le_self (hF true) (effect_le_one F hF hs true))).trans hs

def sequentialProduct : {q : ℕ} → (Fin q → Bool → Matrix R R ℝ) →
    (Fin q → Bool) → Matrix R R ℝ
  | 0, _, _ => 1
  | _+1, F, y => F 0 (y 0) * sequentialProduct (Fin.tail F) (Fin.tail y)

lemma sum_function_succ {q : ℕ} {A : Type u_2} [AddCommMonoid A]
    (f : (Fin (q+1) → Bool) → A) :
    ∑ y, f y = ∑ z : Fin q → Bool, (f (Fin.cons false z) + f (Fin.cons true z)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (q+1) => Bool)).sum_comp f,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp [Fin.consEquiv, add_comm]

lemma sequentialProduct_sum_le {q : ℕ} (F : Fin q → Bool → Matrix R R ℝ)
    (hF : ∀ i b, 0 ≤ F i b) (hs : ∀ i, F i false + F i true ≤ 1) :
    ∑ y, (sequentialProduct F y)ᵀ * sequentialProduct F y ≤ 1 := by
  induction q with
  | zero => simp [sequentialProduct]
  | succ q ih =>
    rw [sum_function_succ]
    apply le_trans _ (ih (Fin.tail F) (fun i => hF i.succ) (fun i => hs i.succ))
    apply Finset.sum_le_sum
    intro z _
    simp only [sequentialProduct, Fin.cons_zero, Fin.tail_cons, Matrix.transpose_mul]
    have h := congruence_mono (effects_square_sum_le (F 0) (hF 0) (hs 0))
      (sequentialProduct (Fin.tail F) z)
    simpa only [mul_add, add_mul, mul_one, mul_assoc] using h

lemma sequentialProduct_error {q : ℕ} (F : Fin q → Bool → Matrix R R ℝ)
    (y : Fin q → Bool) (G : Matrix R R ℝ) (δ : ℝ)
    (hF : ∀ i b, (F i b)ᵀ * F i b ≤ 1)
    (herr : ∀ i, ‖(F i (y i)-1)*G‖ ≤ δ) :
    ‖(sequentialProduct F y-1)*G‖ ≤ (q:ℝ)*δ := by
  induction q with
  | zero => simp [sequentialProduct]
  | succ q ih =>
    have ht := ih (Fin.tail F) (Fin.tail y)
      (fun i b => hF i.succ b) (fun i => herr i.succ)
    have hid : (sequentialProduct F y-1)*G =
        F 0 (y 0) * ((sequentialProduct (Fin.tail F) (Fin.tail y)-1)*G) +
          (F 0 (y 0)-1)*G := by
      simp only [sequentialProduct]
      noncomm_ring
    rw [hid]
    calc
      _ ≤ ‖F 0 (y 0) * ((sequentialProduct (Fin.tail F) (Fin.tail y)-1)*G)‖ +
          ‖(F 0 (y 0)-1)*G‖ := norm_add_le _ _
      _ ≤ (q:ℝ)*δ + δ := add_le_add
        ((frobenius_mul_contraction (hF 0 (y 0)) _).trans ht) (herr 0)
      _ = _ := by push_cast; ring

lemma norm_sqrt_trace_one {ρ : Matrix R R ℝ} (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1) :
    ‖CFC.sqrt ρ‖ = 1 := by
  have hG : (CFC.sqrt ρ).PosSemidef := (CFC.sqrt_nonneg ρ).posSemidef
  have hGt : (CFC.sqrt ρ)ᵀ = CFC.sqrt ρ := hG.isHermitian.eq
  have hsq : ‖CFC.sqrt ρ‖^2 = 1 := by
    rw [frobenius_sq_trace, hGt, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg, htρ]
  nlinarith [norm_nonneg (CFC.sqrt ρ)]

lemma norm_mul_sqrt_sq {ρ : Matrix R R ℝ} (hρ : ρ.PosSemidef)
    (V : Matrix R R ℝ) : ‖V*CFC.sqrt ρ‖^2 = (ρ*(Vᵀ*V)).trace := by
  let G := CFC.sqrt ρ
  have hGt : Gᵀ = G := (CFC.sqrt_nonneg ρ).posSemidef.isHermitian.eq
  have hGG : G*G = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  change ‖V*G‖^2 = _
  rw [frobenius_sq_trace, Matrix.transpose_mul, hGt]
  have hid : G*Vᵀ*(V*G) = G*(Vᵀ*V)*G := by simp only [mul_assoc]
  rw [hid, Matrix.trace_mul_cycle, hGG]

lemma norm_mul_sq_lower (G V : Matrix R R ℝ) (hG : ‖G‖ = 1)
    (δ : ℝ) (hδ : δ ≤ 1/4) (he : ‖(V-1)*G‖ ≤ δ) :
    1/2 ≤ ‖V*G‖^2 := by
  have hh := norm_sub_le (V*G) ((V-1)*G)
  have hid : V*G - (V-1)*G = G := by rw [sub_mul, one_mul, sub_sub_cancel]
  rw [hid, hG] at hh
  nlinarith [sq_nonneg (‖V*G‖-3/4)]

lemma trace_product_upper {ρ : Matrix R R ℝ} (hρ : ρ.PosSemidef)
    (htρ : ρ.trace = 1) (V : Matrix R R ℝ) :
    (ρ*(Vᵀ*V)).trace ≤ (Vᵀ*V).trace := by
  have hρle : ρ ≤ 1 := by simpa only [htρ, one_smul] using posSemidef_le_trace hρ
  have hp : (Vᵀ*V).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial]
      using Matrix.posSemidef_conjTranspose_mul_self V
  have hub := trace_mul_le_of_le hp hρle
  rwa [Matrix.trace_mul_comm (Vᵀ*V) ρ, mul_one] at hub

lemma sequentialProduct_trace_lower {q : ℕ}
    (ρ : Matrix R R ℝ) (F : Fin q → Bool → Matrix R R ℝ) (y : Fin q → Bool)
    (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (hF : ∀ i b, 0 ≤ F i b) (hpair : ∀ i, F i false + F i true ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hsmall : (q:ℝ)*Real.sqrt ε ≤ 1/4)
    (hsuccess : ∀ i, 1-ε ≤ (ρ * F i (y i)).trace) :
    1/2 ≤ ((sequentialProduct F y)ᵀ * sequentialProduct F y).trace := by
  have heffect (i : Fin q) (b : Bool) : F i b ≤ 1 :=
    effect_le_one (F i) (hF i) (hpair i) b
  have hlocal (i : Fin q) : ‖(F i (y i)-1)*CFC.sqrt ρ‖ ≤ Real.sqrt ε :=
    test_error hρ htρ (hF i (y i)) (heffect i (y i)) ε hε (hsuccess i)
  have he := sequentialProduct_error F y (CFC.sqrt ρ) (Real.sqrt ε)
    (fun i b => transpose_mul_self_le_one (hF i b) (heffect i b)) hlocal
  have hsq := norm_mul_sq_lower (CFC.sqrt ρ) (sequentialProduct F y)
    (norm_sqrt_trace_one hρ htρ) _ hsmall he
  rw [norm_mul_sqrt_sq hρ] at hsq
  exact hsq.trans (trace_product_upper hρ htρ _)

lemma nearly_perfect_bit_tests {q : ℕ}
    (ρ : (Fin q → Bool) → Matrix R R ℝ) (F : Fin q → Bool → Matrix R R ℝ)
    (hρ : ∀ y, (ρ y).PosSemidef) (htρ : ∀ y, (ρ y).trace = 1)
    (hF : ∀ i b, 0 ≤ F i b) (hpair : ∀ i, F i false + F i true ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hsmall : (q:ℝ)*Real.sqrt ε ≤ 1/4)
    (hsuccess : ∀ y i, 1-ε ≤ (ρ y * F i (y i)).trace) :
    (2:ℝ)^q / 2 ≤ Fintype.card R := by
  classical
  have hper (y : Fin q → Bool) :
      1/2 ≤ ((sequentialProduct F y)ᵀ * sequentialProduct F y).trace :=
    sequentialProduct_trace_lower (ρ y) F y (hρ y) (htρ y) hF hpair ε hε hsmall
      (hsuccess y)
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hper y)
  have hupper := trace_mono_matrix (sequentialProduct_sum_le F hF hpair)
  rw [Matrix.trace_sum, Matrix.trace_one] at hupper
  have hcard : (∑ _y : Fin q → Bool, (1/2:ℝ)) = (2:ℝ)^q/2 := by
    simp [Fintype.card_bool, Fintype.card_fin, div_eq_mul_inv]
  rw [hcard] at hsum
  exact hsum.trans hupper

end PerfectMatchingPSD

end OAI
