import Mathlib
import OAI.Combinatorics.KMedian.Probability.SignedStars
import OAI.Combinatorics.KMedian.Rounding.GridClipping

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
variable {Ω : Type} [Fintype Ω]
 theorem prob_mono_support (μ : FiniteLaw Ω) {P Q : Ω → Prop}
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ ω, 0 < μ.weight ω → P ω → Q ω) : μ.prob P ≤ μ.prob Q := by
  apply μ.expect_mono_support
  intro ω hω
  by_cases hp : P ω
  · simp only [ite_eq_left hp,ite_eq_left (h ω hω hp),le_refl]
  · simp only [ite_eq_right hp]
    split_ifs <;> norm_num
end MetricKMedian.FiniteLaw

namespace MetricKMedian.Preparation
open Finset WeightedRounding
variable {E T : Type} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

theorem outer_grid_law (D : E → Finset T) (a w : E → ℝ) (c : T → ℝ)
    {g γ B : ℝ} {Δ : ℕ} (hg : 0 < g) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (heven : Even Δ) (hunit : g*(Δ:ℝ)=1)
    (ha0 : ∀ e, 0 ≤ a e) (ha1 : ∀ e, a e ≤ 1) (hw : ∀ e, 0 ≤ w e)
    (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1/8)
    (htarget : ∀ t, (∑ e, if t ∈ D e then w e else 0)=(1+γ)*c t)
    (hplanned : (Fintype.card T:ℝ)+(∑ e, (a e-((D e).card:ℝ))*w e)=B-γ*∑ t, c t) :
    ∃ (Ω : Type) (inst : Fintype Ω), letI := inst;
      ∃ (μ : FiniteLaw Ω) (m : E → ℕ) (S : Ω → E → Finset T)
        (O N : Ω → E → ℝ) (K : Ω → T → ℕ),
      (∀ ω, 0 < μ.weight ω →
        (∀ e, S ω e ⊆ D e) ∧
        (∀ e, O ω e=(m e:ℝ) ∨ O ω e=(m e:ℝ)+1) ∧
        (∀ e, N ω e=(m e:ℝ) ∨ N ω e=(m e:ℝ)+1) ∧
        (∀ e, w e=0 → O ω e=0) ∧
        (∀ e, w e ≤ 1 → g*O ω e ≤ 1) ∧
        (∀ e, N ω e ≤ O ω e) ∧
        (∀ e t, (m e:ℝ)+indicator (S ω e) t ≤ O ω e)) ∧
      (∀ e, μ.expect (fun ω => g*N ω e)=w e) ∧
      (∀ e, μ.variance (fun ω => g*N ω e) ≤ g*w e) ∧
      (∀ e f, e ≠ f → μ.expect (fun ω => (g*N ω e)*(g*N ω f)) ≤ w e*w f) ∧
      (∀ e t, μ.expect (fun ω => g*(activationCount D m S t e ω:ℝ))=
        if t ∈ D e then w e else 0) ∧
      (∀ t, μ.expect (deficit D m S g t)=(1+γ)*c t ∧
        μ.variance (deficit D m S g t) ≤ g*(1+γ)*c t) ∧
      (∀ ω t, g*(K ω t:ℝ)=1-min (deficit D m S g t ω) (1/2) ∧
        (1/2:ℝ) ≤ g*(K ω t:ℝ) ∧ g*(K ω t:ℝ) ≤ 1) ∧
      1-4*g*(1+γ)/γ ≤ μ.prob (fun ω =>
        (g*∑ e, a e*O ω e)+(∑ t, g*(K ω t:ℝ)) ≤ B+3*g) := by
  classical
  let q := fun e => w e/g
  let m := fun e => ⌊q e⌋₊
  let p := fun e => q e-(m e:ℝ)
  have hq : ∀ e, 0 ≤ q e := fun e => div_nonneg (hw e) hg.le
  have hp0 : ∀ e, 0 ≤ p e := fun e => sub_nonneg.mpr (Nat.floor_le (hq e))
  have hp1 : ∀ e, p e ≤ 1 := by
    intro e
    have h := Nat.lt_floor_add_one (q e)
    dsimp only [p,m]
    linarith only [h]
  have hdecomp : ∀ e, g*((m e:ℝ)+p e)=w e := by
    intro e
    dsimp only [p,q]
    rw [add_sub_cancel,mul_div_cancel₀ _ hg.ne']
  obtain ⟨Ω,inst,hex⟩ := signed_star_law D a p m ha0 ha1 hp0 hp1
  let := inst
  obtain ⟨μ,S,O,N,hs,hm,hpair,hact,hactpair⟩ := hex
  let Z := deficit D m S g
  let K := fun ω t => Δ-min (∑ e, activationCount D m S t e ω) (Δ/2)
  have hz : ∀ t, μ.expect (Z t)=(1+γ)*c t ∧ μ.variance (Z t) ≤ g*(1+γ)*c t := by
    intro t
    have h := activation_deficit_moments μ D m p S g hact hactpair t
    have he : g*(∑ e, if t ∈ D e then (m e:ℝ)+p e else 0)=(1+γ)*c t := by
      rw [mul_sum]
      simp only [mul_ite,mul_zero,hdecomp]
      exact htarget t
    refine ⟨h.1.trans he,?_⟩
    calc
      μ.variance (Z t) ≤ g^2*(∑ e, if t ∈ D e then (m e:ℝ)+p e else 0) := h.2
      _ = g*(g*(∑ e, if t ∈ D e then (m e:ℝ)+p e else 0)) := by ring
      _ = g*(1+γ)*c t := by rw [he]; ring
  have hk : ∀ ω t, g*(K ω t:ℝ)=1-min (Z t ω) (1/2) ∧
      (1/2:ℝ) ≤ g*(K ω t:ℝ) ∧ g*(K ω t:ℝ) ≤ 1 := by
    intro ω t
    have h := grid_clip hg heven hunit (∑ e, activationCount D m S t e ω)
    refine ⟨?_,h.2.2.1,h.2.2.2⟩
    exact h.2.1.symm.trans (by dsimp only [Z]; rw [deficit_cast])
  refine ⟨Ω,inst,μ,m,S,O,N,K,?_,?_,?_,?_,?_,hz,hk,?_⟩
  · intro ω hω
    have h := hs ω hω
    refine ⟨h.1,h.2.1,h.2.2.1,?_,?_,h.2.2.2.2.1,h.2.2.2.2.2.1⟩
    · intro e he
      have hqz : q e=0 := by simp only [q,he,zero_div]
      have hmz : m e=0 := by simp only [m,hqz,Nat.floor_zero]
      have hpz : p e=0 := by simp only [p,hqz,hmz,Nat.cast_zero,sub_zero]
      simpa only [hmz,Nat.cast_zero] using h.2.2.2.1 e hpz
    · intro e he
      have hqL : q e ≤ (Δ:ℝ) := (div_le_iff₀ hg).mpr (by rw [mul_comm,hunit]; exact he)
      have hmf : (m e:ℝ) ≤ q e := Nat.floor_le (hq e)
      have hmL : m e ≤ Δ := by exact_mod_cast hmf.trans hqL
      by_cases hml : m e=Δ
      · have hqz : q e=(Δ:ℝ) := le_antisymm hqL (by simpa only [hml] using hmf)
        have hpz : p e=0 := by simp only [p,hqz,hml,sub_self]
        rw [h.2.2.2.1 e hpz,hml,hunit]
      · have hm1 : (m e:ℝ)+1 ≤ (Δ:ℝ) := by exact_mod_cast (show m e+1 ≤ Δ by omega)
        have ho : O ω e ≤ (Δ:ℝ) := by
          rcases h.2.1 e with ho | ho <;> rw [ho]
          · exact_mod_cast hmL
          · exact hm1
        exact (mul_le_mul_of_nonneg_left ho hg.le).trans_eq hunit
  · intro e
    rw [FiniteLaw.expect_mul,hm,hdecomp]
  · intro e
    rw [FiniteLaw.variance_mul]
    have hv := μ.adjacent_variance (fun ω => N ω e) (Nat.cast_nonneg (m e))
      (fun ω hω => (hs ω hω).2.2.1 e) (hm e)
    calc
      _ ≤ g^2*((m e:ℝ)+p e) := mul_le_mul_of_nonneg_left hv (sq_nonneg g)
      _ = g*(g*((m e:ℝ)+p e)) := by ring
      _ = g*w e := by rw [hdecomp]
  · intro e f hef
    have he : (fun ω => (g*N ω e)*(g*N ω f))=(fun ω => g^2*(N ω e*N ω f)) := by funext ω; ring
    rw [he,FiniteLaw.expect_mul]
    calc
      _ ≤ g^2*(((m e:ℝ)+p e)*((m f:ℝ)+p f)) :=
        mul_le_mul_of_nonneg_left (hpair e f hef) (sq_nonneg g)
      _ = (g*((m e:ℝ)+p e))*(g*((m f:ℝ)+p f)) := by ring
      _ = w e*w f := by rw [hdecomp,hdecomp]
  · intro e t
    simp_rw [activationCount_cast]
    by_cases ht : t ∈ D e
    · simp only [activation,ite_eq_left ht,FiniteLaw.expect_mul,FiniteLaw.expect_add,FiniteLaw.expect_const]
      have hprob := hact e t
      rw [ite_eq_left ht] at hprob
      change μ.expect (fun ω => indicator (S ω e) t)=p e at hprob
      rw [hprob,hdecomp]
    · simp only [activation,ite_eq_right ht,mul_zero,FiniteLaw.expect_const]
  · have hmean : ∀ t, μ.expect (Z t) ≤ 1/4 := by
      intro t
      rw [(hz t).1]
      calc
        (1+γ)*c t ≤ 2*c t := mul_le_mul_of_nonneg_right (by linarith only [hγ1]) (hc0 t)
        _ ≤ 1/4 := by linarith only [hc1 t]
    have hprob := FiniteLaw.clipping_budget μ Z c hg.le hγ hc0 hmean (fun t => (hz t).2)
    apply hprob.trans
    apply μ.prob_mono_support
    intro ω hω hgood
    have hpl : (Fintype.card T:ℝ)+g*(∑ e, (a e-((D e).card:ℝ))*((m e:ℝ)+p e))=B-γ*∑ t, c t := by
      rw [mul_sum]
      have he : ∀ e, g*((a e-((D e).card:ℝ))*((m e:ℝ)+p e))=(a e-((D e).card:ℝ))*w e := by
        intro e
        rw [mul_left_comm,hdecomp]
      simp_rw [he]
      exact hplanned
    have hb := actual_opening_budget D a p m S O c hg.le ω (hs ω hω).1
      (hs ω hω).2.2.2.2.2.2 hpl hgood
    have he : (g*∑ e, a e*O ω e)+(∑ t, g*(K ω t:ℝ))=
        ((Fintype.card T:ℝ)+g*∑ e, a e*O ω e)-(∑ t, min (Z t ω) (1/2)) := by
      simp_rw [(hk ω _).1]
      rw [sum_sub_distrib]
      simp only [sum_const,card_univ,nsmul_eq_mul,mul_one]
      ring
    exact he.le.trans hb

end MetricKMedian.Preparation
end
end

end OAI
