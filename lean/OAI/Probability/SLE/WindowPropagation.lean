import Mathlib
import OAI.Probability.SLE.PhysicalMeshPast

namespace OAI

/-! Window Propagation for chordal SLE. -/

section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma geometric_over_quartic_ge_linear {β : ℝ} (hβ : 1 < β) :
    ∃ k : ℝ, 0 < k ∧ ∀ n : ℕ, k*(n+1:ℝ) ≤ β^n/(n+1:ℝ)^4 := by
  have hβ0 : 0 < β := by linarith
  have hir : 0 < β⁻¹ := inv_pos.mpr hβ0
  have hi1 : β⁻¹ < 1 := (inv_lt_one₀ hβ0).mpr hβ
  have hnorm : ‖β⁻¹‖ < 1 := by simpa only [Real.norm_eq_abs,abs_of_pos hir] using hi1
  have hs := summable_pow_mul_geometric_of_norm_lt_one 5 hnorm
  have hss := ((summable_nat_add_iff 1).mpr hs).div_const (β⁻¹)
  have hseq : Summable (fun n : ℕ => (n+1:ℝ)^5/β^n) := by
    apply hss.congr
    intro n
    simp only [Nat.cast_add,Nat.cast_one,pow_succ,inv_pow]
    field_simp [ne_of_gt hβ0]
  let T : ℝ := ∑' n : ℕ, (n+1:ℝ)^5/β^n
  have hn (n : ℕ) : (n+1:ℝ)^5/β^n ≤ T :=
    hseq.le_tsum n (fun j _ => by positivity)
  have hT : 0 < T := by have := hn 0; norm_num at this; linarith
  refine ⟨T⁻¹,inv_pos.mpr hT,fun n => ?_⟩
  have hn0 : 0 < (n+1:ℝ) := by positivity
  have hp0 : 0 < β^n := pow_pos hβ0 _
  have hn' : (n+1:ℝ)^5 ≤ T*β^n := (div_le_iff₀ hp0).mp (hn n)
  apply (le_div_iff₀ (pow_pos hn0 4)).mpr
  apply (mul_le_mul_iff_right₀ hT).mp
  calc
    T * (T⁻¹ * (n+1:ℝ) * (n+1:ℝ)^4) = (n+1:ℝ)^5 := by field_simp
    _ ≤ T * β^n := hn'

lemma all_levels_exceptional_sum {b β : ℝ} (hb : 0 < b) (hβ : 1 < β) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ D T : ℝ, 0 ≤ D → 1 ≤ T →
      (∑' n : ℕ, ENNReal.ofReal (D*Real.exp (-b*T*(β^n/(n+1:ℝ)^4)))) ≤
        ENNReal.ofReal (D*C*Real.exp (-c*T)) := by
  obtain ⟨k,hk,hkn⟩ := geometric_over_quartic_ge_linear hβ
  let c := b*k
  have hc : 0 < c := mul_pos hb hk
  let r := Real.exp (-c)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := (Real.exp_lt_one_iff).mpr (neg_neg_of_pos hc)
  refine ⟨(1-r)⁻¹,c,inv_pos.mpr (sub_pos.mpr hr1),hc,?_⟩
  intro D T hD hT
  have hT0 : 0 ≤ T := by linarith
  have hn (n : ℕ) : D*Real.exp (-b*T*(β^n/(n+1:ℝ)^4)) ≤
      (D*Real.exp (-c*T))*r^n := by
    have hbound := mul_le_mul_of_nonneg_left (hkn n) (mul_nonneg hb.le hT0)
    have hneg : -b*T*(β^n/(n+1:ℝ)^4) ≤ -c*T + (n:ℝ)*(-c) := by
      have hh : c*(T-1)*(n:ℝ) ≥ 0 := by positivity
      dsimp [c] at *
      nlinarith
    calc
      _ ≤ D*Real.exp (-c*T + (n:ℝ)*(-c)) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hneg) hD
      _ = _ := by rw [Real.exp_add,Real.exp_nat_mul]; ring
  have hsum := (hasSum_geometric_of_lt_one hr.le hr1).mul_left (D*Real.exp (-c*T))
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((D*Real.exp (-c*T))*r^n) :=
      ENNReal.tsum_le_tsum (fun n => ENNReal.ofReal_le_ofReal (hn n))
    _ = ENNReal.ofReal ((D*Real.exp (-c*T))*(1-r)⁻¹) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable,hsum.tsum_eq]
    _ = _ := by congr 1; ring

 
lemma reciprocal_square_partial_sum_strong (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), 1/(j+1:ℝ)^2) ≤ 2 - 1/(n+1:ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : 0 < (n+1:ℝ) := by positivity
    have hn2 : 0 < (n+2:ℝ) := by positivity
    have hp : 1/(n+2:ℝ)^2 ≤ 1/(n+1:ℝ) - 1/(n+2:ℝ) := by
      calc
        _ ≤ 1/((n+1:ℝ)*(n+2:ℝ)) := by
          apply one_div_le_one_div_of_le (mul_pos hn hn2)
          nlinarith
        _ = _ := by field_simp; ring
    simp only [Nat.cast_add,Nat.cast_one] at *
    rw [show (n:ℝ)+1+1 = n+2 by ring]
    linarith

lemma reciprocal_square_partial_sum_le_two (n : ℕ) :
    (∑ j ∈ Finset.range n, 1/(j+1:ℝ)^2) ≤ 2 := by
  cases n with
  | zero => norm_num
  | succ n =>
    have := reciprocal_square_partial_sum_strong n
    have : 0 ≤ 1/(n+1:ℝ) := by positivity
    linarith [reciprocal_square_partial_sum_strong n]

lemma discrete_gronwall_exp (U α e : ℕ → ℝ) (hU : 0 ≤ U 0)
    (hα : ∀ n, 0 ≤ α n) (he : ∀ n, 0 ≤ e n)
    (hrec : ∀ n, U (n+1) ≤ (1+α n)*U n+e n) :
    ∀ n, U n ≤ (U 0 + ∑ j ∈ Finset.range n, e j) *
      Real.exp (∑ j ∈ Finset.range n, α j) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    have hV : 0 ≤ U 0 + ∑ j ∈ Finset.range n, e j :=
      add_nonneg hU (Finset.sum_nonneg (fun j _ => he j))
    have hsum : 0 ≤ (∑ j ∈ Finset.range n, α j) + α n :=
      add_nonneg (Finset.sum_nonneg (fun j _ => hα j)) (hα n)
    have hExp : 1 ≤ Real.exp ((∑ j ∈ Finset.range n, α j)+α n) :=
      Real.one_le_exp_iff.mpr hsum
    have hfac : 1+α n ≤ Real.exp (α n) := by linarith [Real.add_one_le_exp (α n)]
    calc
      U (n+1) ≤ (1+α n)*U n+e n := hrec n
      _ ≤ (1+α n)*((U 0+∑ j ∈ Finset.range n,e j)*
          Real.exp (∑ j ∈ Finset.range n,α j))+e n :=
        by
          gcongr
          · linarith [hα n]
      _ ≤ (U 0+∑ j ∈ Finset.range n,e j)*
          Real.exp ((∑ j ∈ Finset.range n,α j)+α n) +
          e n*Real.exp ((∑ j ∈ Finset.range n,α j)+α n) := by
        apply add_le_add
        · rw [Real.exp_add]
          nlinarith [mul_le_mul_of_nonneg_right hfac
            (mul_nonneg hV (Real.exp_pos (∑ j ∈ Finset.range n,α j)).le)]
        · exact le_mul_of_one_le_right (he n) hExp
      _ = _ := by ring

lemma two_recurrences_normalized (S A α e : ℕ → ℝ) (C₁ K : ℝ)
    (hC : 0 ≤ C₁) (hK : 1 ≤ K) (hCK : C₁ ≤ K)
    (hnonneg : ∀ n, 0 ≤ S n ∧ 0 ≤ A n)
    (hα : ∀ n, 0 ≤ α n) (he : ∀ n, 0 ≤ e n)
    (hrec : ∀ n, S (n+1) ≤ S n+α n*A n+e n ∧
      A (n+1) ≤ C₁*S n+α n*A n+e n) :
    ∀ n, max (S (n+1)) (A (n+1)/K) ≤
      (1+K*α n)*max (S n) (A n/K)+e n := by
  have hK0 : 0 < K := by linarith
  intro n
  let U := max (S n) (A n/K)
  have hS : S n ≤ U := le_max_left _ _
  have hA : A n ≤ K*U := by
    have := (div_le_iff₀ hK0).mp (le_max_right (S n) (A n/K))
    simpa only [mul_comm] using this
  have hU : 0 ≤ U := (hnonneg n).1.trans hS
  apply max_le
  · calc
      S (n+1) ≤ S n+α n*A n+e n := (hrec n).1
      _ ≤ U+α n*(K*U)+e n := by gcongr; exact hα n
      _ = _ := by ring
  · apply (div_le_iff₀ hK0).mpr
    calc
      A (n+1) ≤ C₁*S n+α n*A n+e n := (hrec n).2
      _ ≤ K*U+K*(K*α n*U)+K*e n := by
        apply add_le_add
        · apply add_le_add
          · exact (mul_le_mul_of_nonneg_left hS hC).trans
              (mul_le_mul_of_nonneg_right hCK hU)
          · calc
              α n*A n ≤ α n*(K*U) := mul_le_mul_of_nonneg_left hA (hα n)
              _ = K*α n*U := by ring
              _ ≤ K*(K*α n*U) := le_mul_of_one_le_left (mul_nonneg (mul_nonneg hK0.le (hα n)) hU) hK
        · exact le_mul_of_one_le_left (he n) hK
      _ = _ := by ring

lemma window_recurrences_uniform (C₀ C₁ E θ a d : ℝ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hE : 0 ≤ E)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (ha1 : a ≤ 1/2)
    (hd : 0 < d) (S A : ℕ → ℝ)
    (hnonneg : ∀ n, 0 ≤ S n ∧ 0 ≤ A n)
    (hini : S 0 ≤ C₀*d ∧ A 0 ≤ C₀*d)
    (hrec : ∀ n, S (n+1) ≤ S n+(a*θ^n)*A n+E*d/(n+1:ℝ)^2 ∧
      A (n+1) ≤ C₁*S n+(a*θ^n)*A n+E*d/(n+1:ℝ)^2) :
    ∀ n, S n ≤ ((C₀+2*E)*Real.exp ((max 1 (2*C₁))/2/(1-θ)))*d := by
  let K := max 1 (2*C₁)
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := by linarith
  have hCK : C₁ ≤ K := (by linarith : C₁ ≤ 2*C₁).trans (le_max_right _ _)
  let U := fun n => max (S n) (A n/K)
  let α := fun n : ℕ => a*θ^n
  let e := fun n : ℕ => E*d/(n+1:ℝ)^2
  have hα (n : ℕ) : 0 ≤ α n := mul_nonneg ha (pow_nonneg hθ _)
  have he (n : ℕ) : 0 ≤ e n := by dsimp [e]; positivity
  have hU0 : 0 ≤ U 0 := (hnonneg 0).1.trans (le_max_left _ _)
  have hrecU := two_recurrences_normalized S A α e C₁ K hC₁ hK hCK hnonneg hα he hrec
  have hG := discrete_gronwall_exp U (fun n => K*α n) e hU0
    (fun n => mul_nonneg hK0.le (hα n)) he hrecU
  have hIni : U 0 ≤ C₀*d := by
    apply max_le hini.1
    apply (div_le_iff₀ hK0).mpr
    exact hini.2.trans (le_mul_of_one_le_right (mul_nonneg hC₀ hd.le) hK)
  have hGeom := hasSum_geometric_of_lt_one hθ hθ1
  intro n
  have hsum_geom : (∑ j ∈ Finset.range n, θ^j) ≤ (1-θ)⁻¹ := by
    rw [← hGeom.tsum_eq]
    exact hGeom.summable.sum_le_tsum _ (fun j _ => pow_nonneg hθ j)
  have he_sum : (∑ j ∈ Finset.range n, e j) ≤ 2*E*d := by
    calc
      _ = (E*d)*(∑ j ∈ Finset.range n, 1/(j+1:ℝ)^2) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; dsimp [e]; ring
      _ ≤ (E*d)*2 := mul_le_mul_of_nonneg_left
        (reciprocal_square_partial_sum_le_two n) (mul_nonneg hE hd.le)
      _ = _ := by ring
  have hα_sum : (∑ j ∈ Finset.range n, K*α j) ≤ K/2/(1-θ) := by
    calc
      _ = (K*a)*(∑ j ∈ Finset.range n, θ^j) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; dsimp [α]; ring
      _ ≤ (K*a)*(1-θ)⁻¹ := mul_le_mul_of_nonneg_left hsum_geom (mul_nonneg hK0.le ha)
      _ ≤ (K*(1/2))*(1-θ)⁻¹ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha1 hK0.le) (inv_nonneg.mpr (sub_pos.mpr hθ1).le)
      _ = _ := by ring
  calc
    S n ≤ U n := le_max_left _ _
    _ ≤ (U 0+∑ j ∈ Finset.range n,e j)*Real.exp (∑ j ∈ Finset.range n,K*α j) := hG n
    _ ≤ (C₀*d+2*E*d)*Real.exp (K/2/(1-θ)) := by
      apply mul_le_mul (add_le_add hIni he_sum) (Real.exp_le_exp.mpr hα_sum)
      · exact (Real.exp_pos _).le
      · positivity
    _ = _ := by dsimp [K]; ring

universe u
 

def SourceWindowPropagationTarget : Prop :=
  ∀ p C₀ C₁ E D b θ β : ℝ,
    0 < p → p < 1 → 0 ≤ C₀ → 0 ≤ C₁ → 0 ≤ E → 0 ≤ D → 0 < b →
    0 ≤ θ → θ < 1 → 1 < β →
    ∃ M C c : ℝ, 0 < M ∧ 0 < C ∧ 0 < c ∧
      ∀ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
      ∀ δ a : ℝ, 0 < δ → δ ≤ 1 → 0 ≤ a → a ≤ 1/2 →
      ∀ (S A : ℕ → Ω → ℝ) (B : ℕ → Set Ω),
      (∀ n ω, 0 ≤ S n ω ∧ 0 ≤ A n ω) →
      (∀ ω, S 0 ω ≤ C₀*δ^(-p) ∧ A 0 ω ≤ C₀*δ^(-p)) →
      (∀ n, P (B n) ≤ ENNReal.ofReal
        (D*Real.exp (-b*δ^(-2:ℝ)*(β^n/(n+1:ℝ)^4)))) →
      (∀ n ω, ω ∉ B n →
        S (n+1) ω ≤ S n ω + (a*θ^n)*A n ω + E*δ^(-p)/(n+1:ℝ)^2 ∧
        A (n+1) ω ≤ C₁*S n ω + (a*θ^n)*A n ω + E*δ^(-p)/(n+1:ℝ)^2) →
      P {ω | ∃ n, M*δ^(-p) < S n ω} ≤ ENNReal.ofReal (C*Real.exp (-c*δ^(-2:ℝ)))

theorem sourceWindowPropagation : SourceWindowPropagationTarget := by
  intro p C₀ C₁ E D b θ β hp hp1 hC₀ hC₁ hE hD hb hθ hθ1 hβ
  obtain ⟨C,c,hC,hc,hseries⟩ := all_levels_exceptional_sum hb hβ
  let M₀ := (C₀+2*E)*Real.exp ((max 1 (2*C₁))/2/(1-θ))
  have hM₀ : 0 ≤ M₀ := mul_nonneg (by linarith) (Real.exp_pos _).le
  refine ⟨M₀+1,D*C+1,c,by linarith,by positivity,hc,?_⟩
  intro Ω m P hP δ a hδ hδ1 ha ha1 S A B hnonneg hini hfail hrec
  have hd : 0 < δ^(-p) := Real.rpow_pos_of_pos hδ _
  have hT : 1 ≤ δ^(-2:ℝ) := by
    rw [Real.rpow_neg hδ.le,Real.rpow_two]
    exact one_le_inv₀ (sq_pos_of_pos hδ) |>.mpr (by nlinarith)
  have hsubset : {ω | ∃ n, (M₀+1)*δ^(-p) < S n ω} ⊆ ⋃ n, B n := by
    intro ω hω
    by_contra hnot
    have hgood (n : ℕ) : ω ∉ B n := by
      intro hn
      exact hnot (mem_iUnion.mpr ⟨n,hn⟩)
    have hbound := window_recurrences_uniform C₀ C₁ E θ a (δ^(-p))
      hC₀ hC₁ hE hθ hθ1 ha ha1 hd (fun n => S n ω) (fun n => A n ω)
      (fun n => hnonneg n ω) (hini ω) (fun n => hrec n ω (hgood n))
    obtain ⟨n,hn⟩ := hω
    have hn' : S n ω ≤ M₀*δ^(-p) := hbound n
    nlinarith
  calc
    _ ≤ P (⋃ n, B n) := measure_mono hsubset
    _ ≤ ∑' n, P (B n) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal
        (D*Real.exp (-b*δ^(-2:ℝ)*(β^n/(n+1:ℝ)^4))) := ENNReal.tsum_le_tsum hfail
    _ ≤ ENNReal.ofReal (D*C*Real.exp (-c*δ^(-2:ℝ))) := hseries D _ hD hT
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [Real.exp_pos (-c*δ^(-2:ℝ))])

end SLEExactGauge
end

 
section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma source_mesh_finite_measure_propagation (p C₀ C₁ E b θ β : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hE : 0 ≤ E)
    (hb : 0 < b) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hβ : 1 < β) :
    ∃ M C c : ℝ, 0 < M ∧ 0 < C ∧ 0 < c ∧
      ∀ (Ω : Type) (_ : MeasurableSpace Ω) (ν : Measure Ω) (v δ a : ℝ),
      0 ≤ v → 0 < δ → δ ≤ 1 → 0 ≤ a → a ≤ 1/2 →
      ∀ (S A : ℕ → Ω → ℝ) (B : ℕ → Set Ω),
      (∀ n ω, 0 ≤ S n ω ∧ 0 ≤ A n ω) →
      (∀ ω, S 0 ω ≤ C₀*δ^(-p) ∧ A 0 ω ≤ C₀*δ^(-p)) →
      (∀ n, ν (B n) ≤ ENNReal.ofReal
        (3*v*Real.exp (-b*δ^(-2:ℝ)*(β^n/(n+1:ℝ)^4)))) →
      (∀ n ω, ω ∉ B n →
        S (n+1) ω ≤ S n ω + (a*θ^n)*A n ω + E*δ^(-p)/(n+1:ℝ)^2 ∧
        A (n+1) ω ≤ C₁*S n ω + (a*θ^n)*A n ω + E*δ^(-p)/(n+1:ℝ)^2) →
      ν {ω | ∃ n, M*δ^(-p) < S n ω} ≤ ENNReal.ofReal (v*C*Real.exp (-c*δ^(-2:ℝ))) := by
  obtain ⟨C,c,hC,hc,hseries⟩ := all_levels_exceptional_sum hb hβ
  let M₀ := (C₀+2*E)*Real.exp ((max 1 (2*C₁))/2/(1-θ))
  have hM₀ : 0 ≤ M₀ := mul_nonneg (by linarith) (Real.exp_pos _).le
  refine ⟨M₀+1,3*C,c,by linarith,by positivity,hc,?_⟩
  intro Ω m ν v δ a hv hδ hδ1 ha ha1 S A B hnonneg hini hfail hrec
  have hd : 0 < δ^(-p) := Real.rpow_pos_of_pos hδ _
  have hT : 1 ≤ δ^(-2:ℝ) := by
    rw [Real.rpow_neg hδ.le,Real.rpow_two]
    exact one_le_inv₀ (sq_pos_of_pos hδ) |>.mpr (by nlinarith)
  have hsubset : {ω | ∃ n, (M₀+1)*δ^(-p) < S n ω} ⊆ ⋃ n, B n := by
    intro ω hω
    by_contra hnot
    have hgood (n : ℕ) : ω ∉ B n := fun hn => hnot (mem_iUnion.mpr ⟨n,hn⟩)
    have hbound := window_recurrences_uniform C₀ C₁ E θ a (δ^(-p))
      hC₀ hC₁ hE hθ hθ1 ha ha1 hd (fun n => S n ω) (fun n => A n ω)
      (fun n => hnonneg n ω) (hini ω) (fun n => hrec n ω (hgood n))
    obtain ⟨n,hn⟩ := hω
    have hn' : S n ω ≤ M₀*δ^(-p) := hbound n
    nlinarith
  calc
    _ ≤ ν (⋃ n, B n) := measure_mono hsubset
    _ ≤ ∑' n, ν (B n) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal
        (3*v*Real.exp (-b*δ^(-2:ℝ)*(β^n/(n+1:ℝ)^4))) := ENNReal.tsum_le_tsum hfail
    _ ≤ ENNReal.ofReal (3*v*C*Real.exp (-c*δ^(-2:ℝ))) := hseries (3*v) _ (by positivity) hT
    _ = _ := by congr 1; ring

end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_uniform_past_tail (κ : ℝ) (hκ : 4 < κ) (hκ8 : κ < 8)
    (m : SourceMeshParameters κ) :
    ∃ M C c : ℝ, 0 < M ∧ 0 < C ∧ 0 < c ∧
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
      (c₀ : ℂ) (r δ : ℝ), 0 < r → m.q*δ ≤ r → r ≤ δ → δ ≤ 1 → 3*m.L*δ ≤ 1 →
      (hy : ∀ z ∈ ball c₀ 1, δ < z.im) →
      ∀ (E : Set a.samples), MeasurableSet E →
      (∀ (v : ℝ) (_hv : 0 < v) (hvd : v ≤ δ) (z : ℂ),
        MeasurableSet[(source_collarStart_stopping a (ball c₀ 1) v
          (fun z hz => hvd.trans (hy z hz).le) z).measurableSpace] E) →
      ((P.comap Subtype.val).restrict E) {ω | ∃ n : ℕ, M*δ^(-codimension κ) <
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*m.q^n) (ball c₀ 1)} ≤
        ENNReal.ofReal ((P.comap Subtype.val).real E*C*Real.exp (-c*δ^(-2:ℝ))) := by
  let p := codimension κ
  let K := m.q^(-p)
  let b := 1/(512*K^2*m.L^2)
  let θ := m.u^(-m.c)
  let β := (m.q^p/(m.u*m.q))^2
  have hk : 0 < κ := by linarith
  have hp : 0 < p := by dsimp [p,codimension,dimension]; linarith
  have hp1 : p < 1 := by dsimp [p,codimension,dimension]; linarith
  have hK : 0 < K := Real.rpow_pos_of_pos m.hq _
  have hL : 0 < m.L := zero_lt_one.trans m.hL
  have hu : 0 < m.u := zero_lt_one.trans m.hu
  have hb : 0 < b := by dsimp [b]; positivity
  have hθ : 0 < θ := Real.rpow_pos_of_pos hu _
  have hθ1 : θ < 1 := Real.rpow_lt_one_of_one_lt_of_neg m.hu (neg_neg_of_pos m.hc)
  have hβ : 1 < β := by dsimp [β]; nlinarith [m.hratio]
  obtain ⟨M,C,c,hM,hC,hc,hprop⟩ := source_mesh_finite_measure_propagation p
    ((volume (ball (0:ℂ) 1)).toReal*K) m.C (2*K) b θ β hp hp1 (by positivity) m.hC.le
    (by positivity) hb hθ.le hθ1 hβ
  refine ⟨M,C,c,hM,hC,hc,?_⟩
  intro Ω ms P hP γ a c₀ r δ hr hqr hrδ hδ1 hR hy E hE hEs
  let : IsProbabilityMeasure P := hP
  let μ := P.comap (Subtype.val : a.samples → Ω)
  have hδ : 0 < δ := hr.trans_le hrδ
  let S (n : ℕ) (ω : a.samples) := spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
    (γ ω) (a.G ω) (r*m.q^n) (ball c₀ 1)
  let A (n : ℕ) (ω : a.samples) := sourceMeshCount p (ball c₀ 1) (γ ω) (r*m.q^n)
  have hrn (n : ℕ) : 0 < r*m.q^n := mul_pos hr (pow_pos m.hq _)
  have hyr (n : ℕ) (z : ℂ) (hz : z ∈ ball c₀ 1) : r*m.q^n ≤ z.im :=
    (source_mesh_grid_radius_le m.hq m.hq1 hr hrδ n).trans (hy z hz).le
  have hfin : volume (ball c₀ 1) ≠ ∞ := by finiteness
  have hnonneg (n : ℕ) (ω : a.samples) : 0 ≤ S n ω ∧ 0 ≤ A n ω :=
    ⟨(a.spatialRealMass_bound hk hκ8 _ (hrn n) _ measurableSet_ball hfin (hyr n) ω).1,
      (source_mesh_count_bound a _ measurableSet_ball hfin p _ (hrn n) (hyr n) ω).1⟩
  have hini (ω : a.samples) : S 0 ω ≤ ((volume (ball (0:ℂ) 1)).toReal*K)*δ^(-p) ∧
      A 0 ω ≤ ((volume (ball (0:ℂ) 1)).toReal*K)*δ^(-p) := by
    have hs := (a.spatialRealMass_bound hk hκ8 r hr _ measurableSet_ball hfin
      (fun z hz => hrδ.trans (hy z hz).le) ω).2
    have ha := (source_mesh_count_bound a _ measurableSet_ball hfin p r hr
      (fun z hz => hrδ.trans (hy z hz).le) ω).2
    have hbound : (volume (ball c₀ 1)).toReal*r^(-p) ≤ ((volume (ball (0:ℂ) 1)).toReal*K)*δ^(-p) := by
      rw [source_mesh_ball_volume c₀]
      calc
        _ ≤ (volume (ball (0:ℂ) 1)).toReal*(m.q^(-p)*δ^(-p)) :=
          mul_le_mul_of_nonneg_left (source_mesh_initial_scale hp m.hq hδ hqr) ENNReal.toReal_nonneg
        _ = _ := by ring
    constructor
    · simpa only [S,pow_zero,mul_one] using hs.trans hbound
    · change (r*m.q^0)^(-p)*(∫ z in ball c₀ 1, if sourceCollarStart (ball c₀ 1) (γ ω) z (r*m.q^0) = ⊤ then (0:ℝ) else 1) ≤ _
      rw [pow_zero,mul_one]
      exact ha.trans hbound
  have hstep (n : ℕ) := source_mesh_grid_step a hκ hκ8 m (ball c₀ 1) measurableSet_ball c₀
    subset_rfl r δ hr hrδ hR hy n E hE
    (hEs _ (hrn n) (source_mesh_grid_radius_le m.hq m.hq1 hr hrδ n))
  choose F hFm hFt hFg using hstep
  exact hprop a.samples inferInstance (μ.restrict E) (μ.real E) δ (m.Cbad*m.L^(-m.c)*K)
    measureReal_nonneg hδ hδ1 (mul_nonneg (mul_nonneg m.hCb.le (Real.rpow_nonneg hL.le _)) hK.le) m.halpha S A F hnonneg hini hFt hFg
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_conditional_indicator_bound_on
    {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ) (B F : Set Ω)
    (hB : MeasurableSet[m] B) (hF : MeasurableSet F) (G : ℝ) (hG : 0 ≤ G)
    (ht : ∀ A : Set Ω, MeasurableSet[m] A →
      (μ.restrict (A∩B)) F ≤ ENNReal.ofReal (μ.real (A∩B)*G)) :
    ∀ᵐ ω ∂μ, ω ∈ B → μ[(fun ω => if ω ∈ F then (1:ℝ) else 0) | m] ω ≤ G := by
  let f : Ω → ℝ := fun ω => if ω ∈ F then 1 else 0
  have hf : Integrable f μ := by
    exact (integrable_const (1:ℝ)).indicator hF
  have hBm : MeasurableSet B := hm _ hB
  have hfg : μ[B.indicator f | m] ≤ᵐ[μ] B.indicator (fun _ => G) := by
    apply source_condExp_le_of_setIntegral_le hm (hf.indicator hBm)
      ((integrable_const _).indicator hBm) (stronglyMeasurable_const.indicator hB)
    intro A hA
    rw [setIntegral_indicator hBm,setIntegral_indicator hBm]
    change (∫ ω in A∩B, F.indicator (fun _ => (1:ℝ)) ω ∂μ) ≤ _
    have he : (∫ ω in A∩B, F.indicator (fun _ => (1:ℝ)) ω ∂μ) = (μ.restrict (A∩B)).real F := by
      exact integral_indicator_one hF
    rw [he]
    have hh := (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity : 0 ≤ μ.real (A∩B)*G)).mp (ht A hA)
    simpa only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,measureReal_def] using hh
  filter_upwards [hfg,condExp_indicator hf hB] with ω hg he
  intro hω
  rw [he,Set.indicator_of_mem hω,Set.indicator_of_mem hω] at hg
  exact hg
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
 

def SourcePhysicalMeshTailTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 → ∀ η : ℝ, 0 < η →
  ∃ C c δ₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ₀ ∧ δ₀ < η ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
    (ρ : a.samples → WithTop ℝ≥0) (hρ : IsStoppingTime a.filtration ρ)
    (z₀ : ℂ) (r_f δ : ℝ), 0 < r_f → r_f ≤ δ → δ ≤ δ₀ →
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let E := {ω : a.samples | C*δ^(-codimension κ) < spatialRealMass κ
    (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r_f (Metric.ball z₀ 1)}
  ∀ᵐ ω ∂μ, ρ ω ≠ ⊤ →
    Metric.closedBall z₀ (1+η) ⊆ survivingDomain (γ ω) ((ρ ω).untopD 0) →
    μ[(fun ω => if ω ∈ E then (1:ℝ) else 0) | hρ.measurableSpace] ω ≤
      C*Real.exp (-c*δ^(-2:ℝ))

theorem sourcePhysicalMeshTail_proved : SourcePhysicalMeshTailTarget := by
  intro κ hκ hκ8 η hη
  obtain ⟨m⟩ := source_mesh_parameters κ hκ hκ8
  obtain ⟨M,C,c,hM,hC,hc,htail⟩ := source_mesh_uniform_past_tail κ hκ hκ8 m
  obtain ⟨δ₀,hδ₀,hδη,hδ1,hδR⟩ := source_mesh_choose_delta η m.L hη (zero_lt_one.trans m.hL)
  let CT := max M C
  have hCT : 0 < CT := hM.trans_le (le_max_left _ _)
  refine ⟨CT,c,δ₀,hCT,hc,hδ₀,by linarith,?_⟩
  intro Ω ms P hP γ a ρ hρ z₀ rf δ hf hfδ hδsmall μ F
  let : IsProbabilityMeasure P := hP
  have hδ : 0 < δ := hf.trans_le hfδ
  have hδh : δ < η/2 := hδsmall.trans_lt hδη
  by_cases hz : 1+η ≤ z₀.im
  · obtain ⟨r,n,hr,hqr,hrδ,hfr⟩ := source_mesh_select_start m.hq m.hq1 hf hfδ
    have hy (z : ℂ) (hz' : z ∈ ball z₀ 1) : δ < z.im :=
      source_mesh_height hz hz' (by linarith)
    let τ (ω : a.samples) := spatialHitTime (γ ω) z₀ (1+η/2)
    have hτ : IsStoppingTime a.filtration τ := source_mesh_center_stopping a z₀ η
    let B := {ω : a.samples | ρ ω ≤ τ ω}
    have hB : MeasurableSet[hρ.measurableSpace] B := hρ.measurableSet_le_stopping_time hτ
    have hF : MeasurableSet F := measurableSet_lt measurable_const (a.spatialRealMass_measurable (ball z₀ 1) rf)
    have hbound : ∀ᵐ ω ∂μ, ω ∈ B →
        μ[(fun ω => if ω ∈ F then (1:ℝ) else 0) | hρ.measurableSpace] ω ≤ CT*Real.exp (-c*δ^(-2:ℝ)) := by
      apply source_conditional_indicator_bound_on hρ.measurableSpace_le B F hB hF _ (by positivity)
      intro A hA
      have hE : MeasurableSet (A∩B) := hρ.measurableSpace_le _ (hA.inter hB)
      have hEτ : MeasurableSet[hτ.measurableSpace] (A∩B) :=
        ((hρ.min hτ).measurableSpace_mono hτ (fun ω => min_le_right _ _)) _ (hρ.measurableSet_inter_le hτ A hA)
      have hEs (v : ℝ) (hv : 0 < v) (hvd : v ≤ δ) (z : ℂ) :
          MeasurableSet[(source_collarStart_stopping a (ball z₀ 1) v
            (fun z hz => hvd.trans (hy z hz).le) z).measurableSpace] (A∩B) := by
        apply (hτ.measurableSpace_mono (source_collarStart_stopping a (ball z₀ 1) v
          (fun z hz => hvd.trans (hy z hz).le) z) _ ) _ hEτ
        intro ω
        exact source_mesh_center_before a (ball z₀ 1) z₀ subset_rfl η v hη
          (hvd.trans_lt hδh) hz (fun z hz => hvd.trans (hy z hz).le) z ω
      have hR : 3*m.L*δ ≤ 1 := (mul_le_mul_of_nonneg_left hδsmall (mul_nonneg (by norm_num) (zero_lt_one.trans m.hL).le)).trans hδR
      have ht := htail Ω ms P hP γ a z₀ r δ hr hqr hrδ (hδsmall.trans hδ1) hR hy (A∩B) hE hEs
      have hsub : F ⊆ {ω : a.samples | ∃ k : ℕ, M*δ^(-codimension κ) <
          spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*m.q^k) (ball z₀ 1)} := by
        intro ω hω
        refine ⟨n,?_⟩
        have hh : M*δ^(-codimension κ) ≤ CT*δ^(-codimension κ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hδ.le _)
        change CT*δ^(-codimension κ) < spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1) at hω
        rw [hfr] at hω
        exact hh.trans_lt hω
      calc
        _ ≤ ((P.comap Subtype.val).restrict (A∩B)) {ω : a.samples | ∃ k : ℕ, M*δ^(-codimension κ) <
            spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*m.q^k) (ball z₀ 1)} := measure_mono hsub
        _ ≤ _ := ht.trans (ENNReal.ofReal_le_ofReal (by
          have hh := mul_le_mul_of_nonneg_left (le_max_right M C) (measureReal_nonneg (μ := μ) (s := A∩B))
          have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-c*δ^(-2:ℝ))).le
          simpa only [mul_assoc] using hh'))
    filter_upwards [hbound] with ω hω
    intro hρfin hfree
    apply hω
    change ρ ω ≤ spatialHitTime (γ ω) z₀ (1+η/2)
    obtain ⟨s,hs⟩ := WithTop.ne_top_iff_exists.mp hρfin
    rw [←hs] at hfree ⊢
    simp only [WithTop.untopD_coe] at hfree
    exact source_mesh_free_before_center (a.trace_continuous ω) s z₀ η hη hfree
  · exact Eventually.of_forall fun ω _ hfree => False.elim (hz (source_mesh_free_im hη hfree).le)
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
lemma source_indicator_integral_tail {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : m ≤ mΩ) (E : Set Ω) (hE : MeasurableSet E) (K : ℝ) (hK : 0 ≤ K)
    (ht : μ[(fun ω => if ω ∈ E then (1:ℝ) else 0) | m] ≤ᵐ[μ] fun _ => K) :
    μ E ≤ ENNReal.ofReal K := by
  have hi : Integrable (fun ω => if ω ∈ E then (1:ℝ) else 0) μ :=
    (integrable_const (1:ℝ)).indicator hE
  have hh := integral_mono_ae integrable_condExp (integrable_const K) ht
  rw [integral_condExp hm] at hh
  have he : (∫ ω, (if ω ∈ E then (1:ℝ) else 0) ∂μ) = μ.real E := integral_indicator_one hE
  rw [he] at hh
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hh
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hK).mpr hh

lemma source_initial_unit_mesh_tail (κ : ℝ) (hκ : 4 < κ) (hκ8 : κ < 8) :
    ∃ C c δ₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ₀ ∧ δ₀ < 1 ∧
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ), 2 < z₀.im →
    ∀ (rf δ : ℝ), 0 < rf → rf ≤ δ → δ ≤ δ₀ →
      (P.comap Subtype.val) {ω : a.samples | C*δ^(-codimension κ) <
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1)} ≤
        ENNReal.ofReal (C*Real.exp (-c*δ^(-2:ℝ))) := by
  obtain ⟨C,c,δ₀,hC,hc,hδ,hδ1,ht⟩ := sourcePhysicalMeshTail_proved κ hκ hκ8 1 (by norm_num)
  refine ⟨C,c,δ₀,hC,hc,hδ,hδ1,?_⟩
  intro Ω m P hP γ a z₀ hz rf δ hf hfd hd
  let : IsProbabilityMeasure P := hP
  let ρ : a.samples → WithTop ℝ≥0 := fun _ => 0
  have hρ : IsStoppingTime a.filtration ρ := isStoppingTime_const a.filtration 0
  have hb := ht Ω m P hP γ a ρ hρ z₀ rf δ hf hfd hd
  apply source_indicator_integral_tail hρ.measurableSpace_le _
    (measurableSet_lt measurable_const (a.spatialRealMass_measurable _ _)) _ (by positivity)
  filter_upwards [hb] with ω hω
  apply hω (by simp [ρ])
  change closedBall z₀ (1+1) ⊆ survivingDomain (γ ω) 0
  rw [source_witness_initial_domain (a.witness ω)]
  intro z hz'
  have hdist : abs (z.im-z₀.im) ≤ dist z z₀ := by
    simpa only [dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (z-z₀)
  have hh : dist z z₀ ≤ 1+1 := hz'
  have ha := neg_abs_le (z.im-z₀.im)
  change 0 < z.im
  linarith

lemma source_mesh_tail_to_linear {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (p C c δ₀ v rf : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hC : 0 < C) (hc : 0 < c) (hδ : 0 < δ₀) (hv : 0 ≤ v) (_hf : 0 < rf)
    (hbound : ∀ ω, X ω ≤ v*rf^(-p))
    (ht : ∀ δ : ℝ, rf ≤ δ → δ ≤ δ₀ → μ {ω | C*δ^(-p) < X ω} ≤
      ENNReal.ofReal (C*Real.exp (-c*δ^(-2:ℝ)))) :
    ∀ t : ℝ, 1 ≤ t →
      μ {ω | max C v*δ₀^(-p)*t < X ω} ≤
        ENNReal.ofReal (C*Real.exp (-(c*δ₀^(-2:ℝ))*t)) := by
  intro t ht1
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  let δ := δ₀/t
  have hδp : 0 < δ := div_pos hδ ht0
  have hδd : δ ≤ δ₀ := by dsimp [δ]; exact div_le_self hδ.le ht1
  have he : δ^(-p) = δ₀^(-p)*t^p := by
    dsimp [δ]
    rw [Real.div_rpow hδ.le ht0.le,Real.rpow_neg ht0.le,div_inv_eq_mul]
  have htp : t^p ≤ t := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ht1 hp1
  have hM : 0 < max C v := hC.trans_le (le_max_left _ _)
  have hn (a : ℝ) (ha : a ≤ max C v) (ha0 : 0 ≤ a) :
      a*δ^(-p) ≤ max C v*δ₀^(-p)*t := by
    rw [he,←mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hδ.le _))
      htp (Real.rpow_nonneg ht0.le _) (by positivity)
  by_cases hfd : rf ≤ δ
  · apply (measure_mono (show {ω | max C v*δ₀^(-p)*t < X ω} ⊆
        {ω | C*δ^(-p) < X ω} from fun ω hω => (hn C (le_max_left _ _) hC.le).trans_lt hω)).trans
    apply (ht δ hfd hδd).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    have hex : δ^(-2:ℝ) = δ₀^(-2:ℝ)*t^2 := by
      dsimp [δ]
      rw [Real.div_rpow hδ.le ht0.le,Real.rpow_neg ht0.le,div_inv_eq_mul,Real.rpow_two]
    rw [hex]
    have hsq : t ≤ t^2 := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hc.le (Real.rpow_nonneg hδ.le (-2))) (sub_nonneg.mpr hsq)]
  · have hx (ω : Ω) : X ω ≤ max C v*δ₀^(-p)*t := by
      calc
        X ω ≤ v*rf^(-p) := hbound ω
        _ ≤ v*δ^(-p) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hδp (le_of_not_ge hfd) (by linarith)) hv
        _ ≤ _ := hn v (le_max_right _ _) hv
    have he : {ω | max C v*δ₀^(-p)*t < X ω} = ∅ := by
      ext ω; simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]; exact not_lt_of_ge (hx ω)
    rw [he,measure_empty]
    exact bot_le
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_linear_tail_all {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (M C b : ℝ)
    (hM : 0 < M) (_hC : 0 < C) (hb : 0 < b)
    (ht : ∀ t : ℝ, 1 ≤ t → μ {ω | M*t < X ω} ≤ ENNReal.ofReal (C*Real.exp (-b*t))) :
    ∀ x : ℝ, 0 < x → μ {ω | x < X ω} ≤
      ENNReal.ofReal ((max 1 C*Real.exp b)*Real.exp (-(b/M)*x)) := by
  intro x hx
  by_cases hxM : M ≤ x
  · have hh := ht (x/M) ((one_le_div hM).mpr hxM)
    rw [mul_div_cancel₀ _ hM.ne'] at hh
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    have hm : C ≤ max 1 C*Real.exp b := by
      calc
        C ≤ max 1 C := le_max_right _ _
        _ ≤ _ := le_mul_of_one_le_right (by positivity) ((Real.one_le_exp_iff).mpr hb.le)
    convert mul_le_mul_of_nonneg_right hm (Real.exp_pos (-(b/M)*x)).le using 1
    congr 2
    ring
  · apply (prob_le_one : μ {ω | x < X ω} ≤ 1).trans
    apply (ENNReal.one_le_ofReal).mpr
    rw [mul_assoc,←Real.exp_add]
    have he : 1 ≤ Real.exp (b+-(b/M)*x) := by
      apply Real.one_le_exp_iff.mpr
      have hh : (b/M)*x ≤ b := by
        calc
          (b/M)*x ≤ (b/M)*M := mul_le_mul_of_nonneg_left (le_of_not_ge hxM) (by positivity)
          _ = b := div_mul_cancel₀ _ hM.ne'
      linarith
    calc
      1 ≤ max 1 C := le_max_left _ _
      _ ≤ _ := le_mul_of_one_le_right (by positivity) he

lemma source_exponential_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hXm : Measurable X) (hX : ∀ ω, 0 ≤ X ω)
    (A b : ℝ) (hA : 0 ≤ A) (hb : 0 < b)
    (ht : ∀ t : ℝ, 0 < t → μ {ω | t < X ω} ≤ ENNReal.ofReal (A*Real.exp (-b*t))) :
    (∫⁻ ω, ENNReal.ofReal (X ω)^2 ∂μ) ≤ ENNReal.ofReal (8*A/b^2) := by
  have h0 : ∀ x : ℝ, (∫ t in (0:ℝ)..x, (2:ℝ)*t) = x^2 := by
    intro x
    rw [intervalIntegral.integral_const_mul,integral_id]
    ring
  have he := lintegral_comp_eq_lintegral_meas_lt_mul μ (Eventually.of_forall hX)
    hXm.aemeasurable (g := fun t : ℝ => 2*t)
    (fun t ht => (continuous_const.mul continuous_id).intervalIntegrable 0 t)
    (ae_restrict_mem measurableSet_Ioi |>.mono fun t ht => mul_nonneg (by norm_num) (show 0 < t from ht).le)
  simp only [h0,ENNReal.ofReal_pow (hX _)] at he
  rw [he]
  have hbi : IntegrableOn (fun t : ℝ => Real.exp (-(b/2)*t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith : -(b/2) < 0) 0
  calc
    _ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal ((4*A/b)*Real.exp (-(b/2)*t)) := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht0
      have htpos : 0 < t := ht0
      calc
        _ ≤ ENNReal.ofReal (A*Real.exp (-b*t))*ENNReal.ofReal (2*t) :=
          by gcongr; exact ht t htpos
        _ = ENNReal.ofReal ((A*Real.exp (-b*t))*(2*t)) := (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hte : (b/2)*t ≤ Real.exp ((b/2)*t) := (Real.add_one_le_exp _).trans' (by linarith)
          have hmul := mul_le_mul_of_nonneg_left hte (Real.exp_pos (-(b/2)*t)).le
          have hev : Real.exp (-(b/2)*t)*Real.exp ((b/2)*t) = 1 := by
            rw [←Real.exp_add]; ring_nf; exact Real.exp_zero
          rw [hev] at hmul
          have hex : Real.exp (-b*t) = Real.exp (-(b/2)*t)*Real.exp (-(b/2)*t) := by
            rw [←Real.exp_add]; congr 1; ring
          rw [hex]
          have htb : t*Real.exp (-(b/2)*t) ≤ 2/b := by
            apply (le_div_iff₀ hb).mpr
            nlinarith
          calc
            A*(Real.exp (-(b/2)*t)*Real.exp (-(b/2)*t))*(2*t) =
                (2*A*Real.exp (-(b/2)*t))*(t*Real.exp (-(b/2)*t)) := by ring
            _ ≤ (2*A*Real.exp (-(b/2)*t))*(2/b) :=
              mul_le_mul_of_nonneg_left htb (by positivity)
            _ = (4*A/b)*Real.exp (-(b/2)*t) := by ring
    _ = ENNReal.ofReal (8*A/b^2) := by
      rw [←ofReal_integral_eq_lintegral_ofReal (hbi.const_mul (4*A/b))
        (Eventually.of_forall (fun t => by positivity))]
      rw [integral_const_mul,integral_exp_mul_Ioi (by linarith : -(b/2) < 0)]
      simp only [mul_zero,Real.exp_zero]
      congr 1
      field_simp
      ring
end
end SLEExactGauge
end

end OAI
