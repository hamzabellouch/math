import OAI.Analysis.FourierLLogL.Thermal.Levels

/-! # Selecting a flat coefficient -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Real Period Compress.Params

/-- Find `λ` after the width estimate. -/
lemma flat_selection (D : ℝ) (hD : 1 ≤ D) :
    ∀ᶠ j : ℕ in atTop, ∀ (M : ℕ) (A B : Form M), 0 ≤ A → 0 ≤ B →
      ∀ t : ℝ, t ≤ D*height j →
        F (A+long j • B)-F A ≤ 400*t →
      ∃ c : ℝ, height j * H j^200 ≤ c ∧ H j^140*c ≤ long j ∧
        flat (H j) (plateErr j) A (c • B) ∧
        F (A+c • B)-F A ≤ 400*t ∧
        (label (A+c • B)).Ex (form B) ≤ 400*t/c := by
  filter_upwards [nat_pow_small_slow 402 10000,h_large (1000*D)] with j hj h M A B hA hB t ht hw
  let d := height j
  let a := H j
  have H1 : 1 ≤ a := H_ge j
  have hp : 0 < a := H_pos j
  have hd : 0 < d := d_pos j
  let m := slow j ^ 401
  let curve (i : ℕ) := d*a^200 * (2*a^140)^i
  have hm : 0 < m := pow_pos (slow_pos j) _
  have he : curve m ≤ long j := by
    have Hm : ell j *200 + (1+ell j *140)*m ≤ wide j := by
      apply le_trans _ hj
      have h1 := ell_le_h j
      have h2 : 1 ≤ slow j := slow_pos j
      have h3 : slow j ≤ slow j ^402 := le_self_pow h2 (by decide)
      have h4 : 1+ell j * 140 ≤ 141 * slow j := by omega
      calc
        _ ≤ ell j *200 + (141*slow j)*m := Nat.add_le_add_left (Nat.mul_le_mul_right m h4) _
        _ = ell j *200 + 141*slow j^402 := by unfold m; ring
        _ ≤ 10000*slow j^402 := by omega
    have HE : a = (2:ℝ)^(ell j) := by unfold a H slow; push_cast; rfl
    unfold curve long
    calc
      _ = d*(2:ℝ)^(ell j*200+(1+ell j*140)*m) := by
          rw [HE, pow_add, pow_mul,pow_mul,pow_add,pow_one,pow_mul]; ring
      _ ≤ _ := by
        change d*_ ≤ d*_
        gcongr; norm_num
  have h_step (i : ℕ) : a^140*curve i = 2⁻¹*curve (i+1) := by unfold curve; rw [pow_succ]; ring
  have hn (i) : d*a^200 ≤ curve i := by
    apply le_mul_of_one_le_right (by positivity)
    exact one_le_pow₀ (by have := one_le_pow₀ H1 (n:=140); linarith)
  have hu (i : ℕ) (hi : i < m) : a^140*curve i ≤ long j := by
    rw [h_step]
    refine le_trans ?_ he
    have HE : curve (i+1) ≤ curve m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀
        (by have := one_le_pow₀ H1 (n:=140); linarith) hi) (by positivity)
    have HP : 0 ≤ curve m := by unfold curve; positivity
    norm_num; linarith
  let E (i : ℕ) := F (A+(2⁻¹*curve i) • B)
  have Hlow (i : ℕ) : F A ≤ E i := by
    apply F_mono (le_add_of_nonneg_right _)
    intro x
    apply mul_nonneg _ (hB x)
    unfold curve; positivity
  have Hhi : E m ≤ F A + 400*t := by
    apply le_trans (b:=F (A+long j • B))
    · refine F_mono (add_le_add_right ?_ _)
      intro x
      have hhP : 0 ≤ curve m := by unfold curve; positivity
      have hh : 2⁻¹*curve m ≤ long j := by norm_num; linarith
      exact mul_le_mul_of_nonneg_right hh (hB x)
    linarith
  have hi' : ∃ i, i < m ∧ E (i+1)-E i ≤ plateErr j := by
    by_contra! Hh
    have hi : ∀ l : ℕ, l ≤ m → E 0+l*plateErr j ≤ E l := by
      intro l hll; induction l with
      | zero => simp
      | succ l ih =>
        have hh := ih (by omega)
        have hl := Hh l hll
        push_cast; linarith
    have HH := hi m le_rfl
    have HG : (m:ℝ)*plateErr j = a*d := by
      have He : (m:ℝ) = a^401 := by unfold m a H; push_cast; rfl
      rw [He]
      change a^401 * (d/a^400)=a*d
      rw [pow_succ]; field_simp
    have HL := Hlow 0
    rw [HG] at HH
    change _ ≤ a at h
    change _ ≤ D*d at ht
    nlinarith
  obtain ⟨i,hi,hF⟩ := hi'
  have hiP : 0 < curve i := by unfold curve; positivity
  have heq := hu _ hi
  have HH : F (A+curve i • B)-F A ≤ 400*t := by
    refine (sub_le_sub_right (F_mono (add_le_add_right ?_ A)) _).trans hw
    intro x
    exact mul_le_mul_of_nonneg_right ((le_mul_of_one_le_left hiP.le (one_le_pow₀ H1)).trans heq) (hB x)
  refine ⟨curve i, hn i,heq,?_,HH,?_⟩
  · unfold flat
    rw [smul_smul,smul_smul]
    exact (by rw [show H j ^140*curve i = _ from h_step i]; exact hF)
  apply (le_div_iff₀ hiP).mpr
  have H := mean_energy A (curve i • B)
  rw [funext (fun x => form_smul B (curve i) x), Ex_lmul] at H
  rw [mul_comm]
  exact H.trans HH

end FourierLLogL.Dyadic.Thermal

end OAI
