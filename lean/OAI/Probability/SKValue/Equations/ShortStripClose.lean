import Mathlib
import OAI.Probability.SKValue.Evolution.ShortStrip

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma weighted_bound_algebra {a b t A Γ K R D : ℝ} (ht : t∈Ico a b)
    (hΓ : 0 ≤ Γ) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hD : D ≤ A/Real.sqrt (b-t)+Γ*(8*R+2*K*Real.sqrt (b-t))) :
    Real.sqrt (b-t)*D ≤ (A+2*Γ*K*(b-a))+(8*Γ*Real.sqrt (b-a))*R := by
  have hs := Real.sqrt_pos.mpr (sub_pos.mpr ht.2)
  calc
    _  ≤  Real.sqrt (b-t)*(A/Real.sqrt (b-t)+Γ*(8*R+2*K*Real.sqrt (b-t))) :=
      mul_le_mul_of_nonneg_left hD hs.le
    _ = A+2*Γ*K*(b-t)+(8*Γ*Real.sqrt (b-t))*R := by
      rw [mul_add,mul_comm (Real.sqrt (b-t)) (A/Real.sqrt (b-t)),div_mul_cancel₀ _ hs.ne']
      ring_nf
      rw [Real.sq_sqrt (sub_nonneg.mpr ht.2.le)]
      ring
    _  ≤  _ := by
      have hr := Real.sqrt_le_sqrt (sub_le_sub_left ht.1 b)
      have h1 := mul_le_mul_of_nonneg_left (sub_le_sub_left ht.1 b) (by positivity : 0 ≤ 2*Γ*K)
      have h2 := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 8*Γ*R)
      nlinarith

lemma SmoothEvolution.short_strip_jet_bound {T a b Γ A K : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (ha : 0 ≤ a) (hab : a<b) (hb : b ≤ T) (m : ℕ)
    (hΓ : 0 ≤ Γ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hγbd : ∀ s∈Icc a b, |γ s| ≤ Γ)
    (hprev : ∀ s∈Icc a b, ∀ x, |iteratedDeriv m (deriv (V s)) x| ≤ A)
    (hprod : ∀ s∈Icc a b, ∀ x,
      |iteratedDeriv m (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x| ≤
        |iteratedDeriv (m+1) (deriv (V s)) x|+K)
    (hshort : 8*Γ*Real.sqrt (b-a) ≤ 1/2) (x : ℝ) :
    |iteratedDeriv (m+1) (deriv (V a)) x| ≤ 2*(A+2*Γ*K*(b-a))/Real.sqrt (b-a) := by
  let F := fun s ↦ iteratedDeriv (m+1) (deriv (V s))
  obtain ⟨C,hC,hbd⟩ := h.bound (m+1)
  have hbd' : ∀ s∈Icc a b, ∀ y, |F s y| ≤ C := fun s hs y ↦ hbd s ⟨ha.trans hs.1,hs.2.trans hb⟩ y
  have hR := weightedCap_nonneg hab.le hC hbd'
  have hcap : weightedCap a b F ≤ 2*(A+2*Γ*K*(b-a)) := by
    apply weightedCap_absorb hab.le hC hbd' hshort
    intro t ht y
    rcases ht.2.eq_or_lt with rfl | htb
    · simp only [sub_self,Real.sqrt_zero,zero_mul]
      positivity
    · exact weighted_bound_algebra ⟨ht.1,htb⟩ hΓ hK hR
        (h.jet_mild_bound hm hγ hi ha hab hb m hΓ hA hK hγbd hprev hprod ⟨ht.1,htb⟩ y)
  apply (abs_le_weightedCap_div hab.le hC hbd' ⟨le_rfl,hab⟩ x).trans
  exact div_le_div_of_nonneg_right hcap (Real.sqrt_nonneg _)

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

noncomputable def lowerJetConstant (m : ℕ) (A : ℝ) : ℝ :=
  ∑ i∈Finset.range m, (m.choose (i+1) : ℝ)*A*A

lemma lowerJetConstant_nonneg (m : ℕ) {A : ℝ} (hA : 0 ≤ A) : 0 ≤ lowerJetConstant m A := by
  unfold lowerJetConstant
  exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hA) hA)

lemma SmoothTerminal.product_jet_bound {f : ℝ → ℝ} (hf : SmoothTerminal f)
    (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ k ≤ m, ∀ x, |iteratedDeriv k (deriv f) x| ≤ A) (x : ℝ) :
    |iteratedDeriv m (fun y ↦ deriv f y*deriv (deriv f) y) x| ≤
      |iteratedDeriv (m+1) (deriv f) x|+lowerJetConstant m A := by
  have horder := ENat.natCast_le_of_coe_top_le_withTop le_rfl m
  rw [iteratedDeriv_fun_mul (hf.jets.smooth.of_le horder).contDiffAt
    (hf.jets.deriv.smooth.of_le horder).contDiffAt,Finset.sum_range_succ']
  have hstep (n : ℕ) : iteratedDeriv n (deriv (deriv f))=iteratedDeriv (n+1) (deriv f) :=
    (iteratedDeriv_succ').symm
  simp only [Nat.choose_zero_right,Nat.cast_one,one_mul,iteratedDeriv_zero,Nat.sub_zero,hstep]
  apply (abs_add_le _ _).trans
  have hfirst : |deriv f x*iteratedDeriv (m+1) (deriv f) x| ≤
      |iteratedDeriv (m+1) (deriv f) x| := by
    rw [abs_mul]
    have hgrad := norm_deriv_le_of_lipschitz hf.lipschitz (x₀ := x)
    simp only [Real.norm_eq_abs,NNReal.coe_one] at hgrad
    nlinarith [abs_nonneg (iteratedDeriv (m+1) (deriv f) x)]
  have hrest : |∑ i∈Finset.range m, (m.choose (i+1) : ℝ)*iteratedDeriv (i+1) (deriv f) x*
      iteratedDeriv (m-(i+1)+1) (deriv f) x| ≤ lowerJetConstant m A := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (m.choose (i+1)))]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hb (i+1) (by omega) x) (Nat.cast_nonneg _))
      (hb (m-(i+1)+1) (by omega) x) (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
  exact (add_le_add hrest hfirst).trans_eq (add_comm _ _)

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma exists_short_length {Γ d : ℝ} (hΓ : 0 ≤ Γ) (hd : 0<d) :
    ∃ δ : ℝ, 0<δ ∧ δ ≤ d ∧ 8*Γ*Real.sqrt δ ≤ 1/2 := by
  let e := min (1 : ℝ) (min d (1/(16*(Γ+1))))
  have hden : 0<16*(Γ+1) := by positivity
  have he : 0<e := lt_min zero_lt_one (lt_min hd (one_div_pos.mpr hden))
  have he1 : e ≤ 1 := min_le_left _ _
  have hed : e ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hei : e ≤ 1/(16*(Γ+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hei' := (le_div_iff₀ hden).mp hei
  refine ⟨e^2,sq_pos_of_pos he,?_,?_⟩
  · nlinarith
  · rw [Real.sqrt_sq he.le]
    nlinarith

theorem uniform_bulk_jets (Γ : ℝ) (hΓ : 0 ≤ Γ) (T : ℝ) (m : ℕ) :
    ∀ S : ℝ, 0 ≤ S → S<T → ∃ A : ℝ, 0 ≤ A ∧
      ∀ (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ), SmoothEvolution T γ V → Measurable γ →
        MonotoneOn γ (Icc (0 : ℝ) T) → (∀ t∈Icc (0 : ℝ) T, |γ t| ≤ Γ) →
        ∀ t∈Icc (0 : ℝ) S, ∀ k ≤ m, ∀ x, |iteratedDeriv k (deriv (V t)) x| ≤ A := by
  induction m with
  | zero =>
    intro S hS hST
    refine ⟨1,by norm_num,?_⟩
    intro γ V h hm hmono hbd t ht k hk x
    have hk' : k=0 := by omega
    subst k
    simpa only [iteratedDeriv_zero] using h.deriv_bound ⟨ht.1,ht.2.trans hST.le⟩ x
  | succ m ih =>
    intro S hS hST
    let S' := (S+T)/2
    have hSS' : S<S' := by dsimp only [S']; linarith
    have hS'T : S'<T := by dsimp only [S']; linarith
    obtain ⟨A,hA,hAall⟩ := ih S' (hS.trans hSS'.le) hS'T
    obtain ⟨δ,hδ,hδgap,hshort⟩ := exists_short_length hΓ (sub_pos.mpr hSS')
    let K := lowerJetConstant m A
    have hK : 0 ≤ K := lowerJetConstant_nonneg m hA
    let B := 2*(A+2*Γ*K*δ)/Real.sqrt δ
    have hB : 0 ≤ B := by dsimp only [B]; positivity
    refine ⟨max A B,le_max_of_le_left hA,?_⟩
    intro γ V h hm hmono hbd t ht k hk x
    have hprev := hAall γ V h hm hmono hbd
    by_cases hkm : k ≤ m
    · exact (hprev t ⟨ht.1,ht.2.trans hSS'.le⟩ k hkm x).trans (le_max_left _ _)
    · have hk' : k=m+1 := by omega
      subst k
      have htδ : t<t+δ := by linarith
      have htδS' : t+δ ≤ S' := by linarith [ht.2]
      have hi : IntervalIntegrable γ volume 0 T := by
        apply MonotoneOn.intervalIntegrable
        simpa only [uIcc_of_le (hS.trans hST.le)] using hmono
      have hh := h.short_strip_jet_bound hm hmono hi ht.1 htδ (htδS'.trans hS'T.le) m
        hΓ hA hK
        (fun s hs ↦ hbd s ⟨ht.1.trans hs.1,hs.2.trans (htδS'.trans hS'T.le)⟩)
        (fun s hs y ↦ hprev s ⟨ht.1.trans hs.1,hs.2.trans htδS'⟩ m le_rfl y)
        (fun s hs y ↦ (h.slices s ⟨ht.1.trans hs.1,hs.2.trans (htδS'.trans hS'T.le)⟩).product_jet_bound
          m hA (fun j hj z ↦ hprev s ⟨ht.1.trans hs.1,hs.2.trans htδS'⟩ j hj z) y)
        (by simpa only [add_sub_cancel_left] using hshort) x
      have hh' : |iteratedDeriv (m+1) (deriv (V t)) x| ≤ B := by
        simpa only [add_sub_cancel_left] using hh
      exact hh'.trans (le_max_right _ _)

end SKValue

end

end OAI
