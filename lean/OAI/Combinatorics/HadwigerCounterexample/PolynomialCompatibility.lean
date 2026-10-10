import OAI.Combinatorics.HadwigerCounterexample.FourPhaseBits

namespace OAI

/-! # Polynomial Compatibility -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module Finset Filter
variable {p : Shape} {n N d : ℕ}

def poll (d N : ℕ) := (1+(1+d*(N:ℝ))^2)^2

set_option maxHeartbeats 600000 in
theorem tiny_poll (p : Shape) {n N : ℕ} (Δ : UnitType p n N→Ambient p N)
    (w : Wgt (UnitType p n N)) (hw : IsLaw w)
    (h : tonalTiny p Δ w d)
    (hd : ∀ x, w x≠0 → tone p x allSide (Δ x) = 0) (i : F) :
    (1/4 : ℝ)/poll d N-bp (-0.24*N)≤
      pr (pairW w w) (fun x => quench p Δ x=repeatQ i) := by
  classical
  obtain ⟨T,hT,hZ,hE⟩ := h
  let M := circus p T Δ w
  have hM : M.rank≤ d*N := (circus_rank ..).trans ((Nat.mul_le_mul_left N hT).trans_eq
    (Nat.mul_comm _ _))
  have hB (x y) (hx : w x≠0) :
      tone p y allSide (Δ x)=M x y := (shadow_valid p T Δ hZ x y allSide hx).symm
  have hD x : M x x=0 := by
    by_cases hx : w x=0
    · change juris p T x _ (cutDown p T Δ w x) = _
      simp [cutDown,hx]
    exact (hB _ _ hx).symm.trans (hd x hx)
  let u := pairW w w
  have hX :
      pr u (fun x => M x.1 x.2=0 ∧ M x.2 x.1=0)=
        pr u (fun x => repeated (quench p Δ x)) := by
    refine avg_congr (fun x hx => ?_)
    congr 1
    have h1 := hB x.1 x.2 (left_ne_zero_of_mul hx)
    have h2 := hB x.2 x.1 (right_ne_zero_of_mul hx)
    unfold repeated quench
    simp only [←tone_vec,h1,h2]
  have hi : 1 ≤ poll d N*pr u (fun x => repeated (quench p Δ x)) := by
    have hh := simultaneous_czeros M (1+d*N) w hw (by omega) hD
    rw [show pairW w w=u from rfl,hX] at hh
    refine le_trans hh (le_of_eq ?_)
    push_cast; unfold poll
    ring
  have hh : 0 < poll d N := by unfold poll; positivity
  apply le_trans _ (tiny_pattern p Δ w i (bp_pos _).le hE)
  apply sub_le_sub_right
  exact (div_le_iff₀ hh).mpr (by linarith only [hi])

theorem eventually_tiny_poll (d : ℕ) :
    ∃ b> (0:ℝ),∀ᶠ N : ℕ in atTop,
      b/N^ (4:ℕ) ≤ (1/4:ℝ)/poll d N-bp (-0.24*N) := by
  classical
  let B : ℝ := (1+(1+(d:ℝ))^2)^2
  have hb : 0 < B := by unfold B; positivity
  let c := B⁻¹/8
  have hc : 0 < c := by unfold c; positivity
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop 1,bp_poly_dom_nat (by norm_num : 0<(0.24:ℝ)) c⁻¹ 4] with
    N hN hE
  have h : 1≤ (N:ℝ) := by exact_mod_cast hN
  have hh : poll d N ≤ B*N^(4:ℕ) := by
    unfold poll B
    have hf : 1+d*(N:ℝ) ≤ (1+d)*N := by linarith only [h]
    calc (1+(1+d*(N:ℝ))^2)^2
      _ ≤ ((N:ℝ)^2+((1+d)*N)^2)^2 := by
        have hi : 1 ≤ (N:ℝ)^2 := by nlinarith
        gcongr
      _ = _ := by ring
  have hB : 2*(c / N^(4:ℕ)) ≤ (1/4:ℝ)/poll d N := by
    have hf : 0 < poll d N := by unfold poll; positivity
    calc 2*(c/N^(4:ℕ)) = (1/4:ℝ)/(B*N^(4:ℕ)) := by unfold c; field_simp; norm_num
         _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hf hh
  have hx := bp_pos (0.24*N)
  have hζ : bp (-0.24*N) ≤ c/N^(4:ℕ) := by rw [neg_mul,bp_neg]; field_simp; field_simp at hE; rw [mul_comm _ (0.24:ℝ)] at hE; linarith
  linarith only [hB,hζ]
end HadwigerCounterexample

end

end OAI
