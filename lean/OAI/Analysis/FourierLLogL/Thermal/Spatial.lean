import OAI.Analysis.FourierLLogL.Thermal.Order
import OAI.Analysis.FourierLLogL.Dyadic.Circle

/-! # The spatial form and the discrete Gaussian bounds -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate Real
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Period Real

variable {M : ℕ}

lemma wave_at_one (x : Grid M) :
    wave 1 x = cos (2*π * pos x) := by
  have H := chi_cast (1:ℤ) x
  unfold wave; norm_num [phase] at H
  rw [H,Complex.exp_re]
  simp

lemma wave_at_diam (x : Grid M) :
    wave 1 x = cos (2*π * Dyadic.diam x) := by
  rw [diam_min]
  rcases le_total (pos x) (pos (-x)) with h | h
  · rw [min_eq_left h,wave_at_one]
  rw [min_eq_right h,← wave_at_one,wave_even _ _]

theorem cost_diam (x : Grid M) :
    8*(Dyadic.diam x)^2 ≤ cost 1 x ∧ cost 1 x ≤ 32*(Dyadic.diam x)^2 := by
  let y := Dyadic.diam x
  have hy := diam_nonneg x
  have hY := diam_le_half x
  unfold cost
  rw [wave_at_diam]
  have hp : 0 ≤ 2*π*y := mul_nonneg (by positivity) hy
  have he : |2*π*y| ≤ π := by rw [abs_of_nonneg hp]; unfold y at *; nlinarith [pi_pos]
  have H := cos_le_one_sub_mul_cos_sq he
  have H' := @one_sub_sq_div_two_le_cos (2*π*y)
  have hh : 2/π^2 * (2*π*y)^2 = 8*y^2 := by field_simp [pi_pos.ne']; ring
  have hh' : (2*π*y)^2/2 ≤ 32*y^2 := by
    calc
      _ = (2*π^2)*y^2 := by ring
      _ ≤ _ := by gcongr; nlinarith [pi_le_four,pi_pos]
  rw [hh] at H
  change 8*y^2 ≤ _ ∧ _ ≤ 32*y^2
  dsimp only [y] at *
  constructor <;> linarith

/-- Spatial form, specified by inverse width -/
def S (M : ℕ) (R : ℝ) : Form M := fun s => if s=1 then R^2 else 0

lemma S_nonneg (M : ℕ) (R : ℝ) : 0 ≤ S M R := by
  intro i
  change 0 ≤ if i=1 then _ else _
  split_ifs <;> positivity

lemma form_S (R : ℝ) (x : Grid M) : form (S M R) x = R^2*cost 1 x := by simp [form,S,ite_mul]

lemma scale_S (M : ℕ) (t R : ℝ) : t^2 • S M R = S M (t*R) := by
  funext i
  change t^2*(if i=1 then _ else _) = if i=1 then _ else _
  split_ifs <;> ring

lemma S_mono {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : S M a ≤ S M b := by
  intro i; unfold S
  split_ifs <;> nlinarith

private lemma expU_ray (R : ℝ) (h : 0 < R) :
    expU (fun x : Grid M => exp (-R * pos x)) ≤ side M + 1/R := by
  let a := R*side M
  have ha : 0 < a := mul_pos h (side_pos M)
  let q := exp (-a)
  have hq : 0 ≤ q := exp_nonneg _
  let m := 2^M
  let b := ∑ i ∈ Finset.range m, q^i
  have heq : expU (fun x : Grid M => exp (-R*pos x)) = side M * b := by
    have he (x : Grid M) : exp (-R*pos x) = q^x.val := by
      unfold q pos a
      rw [← Real.exp_nat_mul]; congr 1; ring
    simp_rw [he,expU,smul_eq_mul]
    rw [sum_grid (M:=M) (fun i => q^i)]
  have h1 : b * (1-q) ≤ 1 := by
    rw [show b*(1-q) = _ from geom_sum_mul_neg q m]
    have hh : 0 ≤ q^m := pow_nonneg hq _
    linarith
  have h2 : 1-q ≥ a/(1+a) := by
    have H := Real.add_one_le_exp a
    have HH : q*exp a = 1 := by unfold q; rw [← exp_add]; simp
    apply (div_le_iff₀ (by linarith)).mpr; nlinarith
  have hb : 0 ≤ b := Finset.sum_nonneg fun i _ => pow_nonneg hq _
  have hu : b*a ≤ 1+a := by
    apply (div_le_one (by linarith)).mp
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_left h2 hb).trans h1
  rw [heq,← mul_le_mul_iff_left₀ h]
  unfold a at hu
  field_simp
  nlinarith

lemma q_S_upper (R : ℝ) (h : 0 < R) :
    q (S M R) 0 ≤ 6*(side M+1/R) := by
  let f (x : Grid M) := exp (-R*pos x)
  have H (x : Grid M) :
      boltz (S M R) x ≤ 3*(f x + f (-x)) := by
    let y := Dyadic.diam x
    have H := mul_le_mul_of_nonneg_left (cost_diam x).1 (sq_nonneg R)
    calc
      _ ≤ exp (1 + -R*y) := by
          unfold boltz
          rw [form_S]
          apply Real.exp_monotone
          dsimp only [y]
          nlinarith [sq_nonneg (4*R*Dyadic.diam x-1/4)]
      _ = exp 1 * exp (-R*y) := exp_add _ _
      _ ≤ _ := by
        apply mul_le_mul Real.exp_one_lt_three.le _ (Real.exp_nonneg _) (by norm_num : (0:ℝ) ≤ 3)
        dsimp only [y]; rw [diam_min]
        rcases le_total (pos x) (pos (-x)) with hh|hh
        · rw [min_eq_left hh]; exact le_add_of_nonneg_right (exp_nonneg _)
        rw [min_eq_right hh]; exact le_add_of_nonneg_left (exp_nonneg _)
  rw [q_origin,expU_ex]
  apply le_trans (Ex_mono _ H)
  rw [Ex_lmul,Ex_add]
  simp_rw [← expU_ex,expU_reflect]
  have he : expU f ≤ side M+1/R := expU_ray R h
  simp only [div_eq_mul_inv] at *; linarith

lemma q_S_lower (R : ℝ) (h : 1 ≤ R) :
    (1/30:ℝ)/R ≤ q (S M R) 0 := by
  rw [q_origin]
  let m : ℝ := 2^M
  let r := (m/10)/R
  let s := arc M r
  have hR : 0 < R := by linarith
  have hm : 0 < m := by unfold m; positivity
  have hr : 0 ≤ r := by unfold r; positivity
  have hsr : side M * m = 1 := side_card _
  have hsr' : side M * r = (1/10)/R := by unfold r; rw [← hsr]; ring
  have h1 : r ≤ s.card := arc_card_lo _ _ hr (by
    unfold r; apply (div_le_iff₀ hR).mpr; change m/10 ≤ m*R; nlinarith)
  have h2 (i : Grid M) (hi : i∈s) : 1/3 ≤ boltz (S M R) i := by
    have hy : 0 ≤ Dyadic.diam i := diam_nonneg i
    have hh : Dyadic.diam i * R ≤ 1/10 := by
      apply (le_div_iff₀ hR).mp
      rw [← hsr']
      exact mul_le_mul_of_nonneg_left ((mem_arc _ _).mp hi) (side_pos _).le
    have hj : form (S M R) i ≤ 1 := by
      rw [form_S]
      apply le_trans (mul_le_mul_of_nonneg_left (cost_diam i).2 (sq_nonneg _))
      have H : (Dyadic.diam i * R)^2 ≤ (1/10:ℝ)^2 :=
        pow_le_pow_left₀ (mul_nonneg hy hR.le) hh 2
      nlinarith
    apply le_trans (b:=exp (-1))
    · rw [exp_neg,one_div]; exact (inv_le_inv₀ (by norm_num : (0:ℝ) < 3) (exp_pos 1)).mpr Real.exp_one_lt_three.le
    exact Real.exp_monotone (by linarith)
  unfold expU; rw [smul_eq_mul]
  calc
    _ = side M * r * (1/3) := by rw [hsr']; ring
    _ ≤ side M * s.card * (1/3) := by have := side_pos M; gcongr
    _ = side M * (∑ _i ∈ s, (1/3:ℝ)) := by simp; ring
    _ ≤ side M * ∑ i ∈ s, boltz (S M R) i :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum h2) (side_pos M).le
    _ ≤ side M * ∑ i, boltz (S M R) i :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => (boltz_pos _ _).le)) (side_pos M).le

lemma q_S_upper' (R : ℝ) (h : 0 < R) (hR : R ≤ 2^M) :
    q (S M R) 0 ≤ 12/R := by
  apply le_trans (q_S_upper R h)
  have hh : side M ≤ 1/R := by rw [side_pow_two,one_div]; exact (inv_le_inv₀ (by positivity : (0:ℝ) < 2^M) h).mpr hR
  simp only [div_eq_mul_inv] at *; linarith

lemma F_S_lower (R : ℝ) (h : 0 < R) (hR : R ≤ 2^M) :
    log R - 12 ≤ F (S M R) := by
  have H := log_le_log (q_origin_pos _) (q_S_upper' R h hR)
  rw [Real.log_div (by norm_num) h.ne'] at H
  unfold F
  linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<12 by norm_num)]

lemma F_S_upper (M : ℕ) (R : ℝ) (h : 1 ≤ R) :
    F (S M R) ≤ log R+30 := by
  have hp : 0 < R := by linarith
  have H := log_le_log (by positivity) (q_S_lower (M:=M) R h)
  rw [Real.log_div (by norm_num) hp.ne',one_div,Real.log_inv] at H
  unfold F
  linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<30 by norm_num)]

lemma S_energy (R : ℝ) (h : 1 ≤ R) (hR : R ≤ 2^M) (A : Form M) (hA : S M R ≤ A) :
    (label A).Ex (form (S M R)) ≤ 100 := by
  let B := S M R
  apply le_trans (form_energy_mono (S_nonneg _ _) hA (S_nonneg _ _))
  let C := S M (R/2)
  have He : C+(3/4:ℝ) • B = B := by
    have HH := scale_S M (1/2) R
    rw [show 1/2*R=R/2 by ring] at HH
    unfold B C
    rw [← HH,← add_smul,show (1/2:ℝ)^2+3/4=1 by norm_num,one_smul]
  have H := mean_energy C ((3/4:ℝ) • B)
  rw [He,show form ((3/4:ℝ) • B) = _ from funext (fun x => form_smul _ _ x),Ex_lmul] at H
  have hP : 0 < R := by linarith
  have h1 : F B ≤ log R + 30 := F_S_upper M R h
  have h2 : log (R/2)-12 ≤ F C := F_S_lower _ (by positivity) (by linarith)
  rw [log_div hP.ne' (by norm_num)] at h2
  change (label B).Ex (form B) ≤ 100
  linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]

lemma S_cost (R : ℝ) (h : 1 ≤ R) (hR : R ≤ 2^M) (A : Form M) (hA : S M R ≤ A) :
    (label A).Ex (cost 1) ≤ 100/R^2 := by
  have H := S_energy R h hR A hA
  rw [show form (S M R) = _ from funext (form_S R),Ex_lmul] at H
  exact (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < R))).mpr (by rwa [mul_comm])

lemma S_variance (R : ℝ) (h : 1 ≤ R) (hR : R ≤ 2^M) (A : Form M) (hA : S M R ≤ A) :
    (label A).Ex (fun i => (Dyadic.diam i)^2) ≤ 100/R^2 := by
  apply le_trans _ (S_cost _ h hR A hA)
  exact Ex_mono _ fun x => (le_mul_of_one_le_left (sq_nonneg _) (by norm_num : (1:ℝ)≤8)).trans (cost_diam x).1

lemma delta_S (R : ℝ) (h : 1 ≤ R) (hR : R ≤ 2^M) (A : Form M) (hA : S M R ≤ A)
    (s : Grid M) : delta A s ≤ rad s * (20/R) := by
  have hp : 0 < R := by linarith
  have h1 := S_cost R h hR A hA
  rw [cred_cost] at h1
  have h2 := delta_sq A 1
  have h3 : delta A 1 ≤ 20/R := by
    have h4 : delta A 1^2 ≤ (20/R)^2 := by
      apply le_trans (b:=2*(100/R^2)); rw [h2]; linarith
      rw [div_pow,← mul_div_assoc]; apply div_le_div_of_nonneg_right _ (sq_nonneg _); norm_num
    nlinarith [show 0 < 20/R by positivity]
  calc
    _ ≤ rad s * delta A 1 := by simpa only [rad_abs,liftInt_cast] using delta_int A (liftInt s)
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (rad_nonneg _)

lemma cred_short (R : ℝ) (h : 1 ≤ R) (hR : R ≤ 2^M) (A : Form M) (hA : S M R ≤ A)
    (s : Grid M) (hs : rad s ≤ R/20) :
    1/2 ≤ cred A s := by
  have hp : 0 < R := by linarith
  have hi : delta A s ≤ 1 := calc
    _ ≤ _ := delta_S _ h hR A hA s
    _ ≤ (R/20) * (20/R) := by gcongr
    _ = 1 := by field_simp
  nlinarith [delta_sq A s,(show 0 ≤ delta A s from sqrt_nonneg _)]

lemma q_short (R : ℝ) (h : 1 ≤ R) (hR : R ≤ 2^M)
    (s : Grid M) (hs : rad s ≤ R/20) :
    (1/60:ℝ)/R ≤ q (S M R) s := by
  let B := S M R
  change _ ≤ q B s
  have hh := cred_short R h hR B le_rfl s hs
  rw [q_express,F_origin]
  calc
    (1/60:ℝ)/R = ((1/30)/R)*(1/2) := by ring
    _ ≤ _ := mul_le_mul (q_S_lower R h) hh (by norm_num) (q_origin_pos _).le

end FourierLLogL.Dyadic.Thermal

end OAI
