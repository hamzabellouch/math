import OAI.Combinatorics.PolynomialVacuum.Algebra.PairImage

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

abbrev ThreeTensor := Spin → Spin → Spin → ℂ

def tripleBitSupported (b₁ b₂ b₃ : Bool) (v : ThreeTensor) : Prop :=
  ∀ a b c, ¬(allowedSpin b₁ a ∧ allowedSpin b₂ b ∧ allowedSpin b₃ c) → v a b c=0

theorem insertion_edges_ne_zero (b : Bool) :
    insertion (occupiedSpin b,.zero) (occupiedSpin b) ≠ 0 ∧
    insertion (.zero,occupiedSpin b) (occupiedSpin b) ≠ 0 := by
  have hx : xStar ≠ 0 := by
    unfold xStar
    exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity : (0:ℝ)<2+Real.sqrt 2))
  have hq : q ≠ 0 := Complex.exp_ne_zero _
  cases b <;> simp [occupiedSpin,insertion,charge,zpow_neg,hx,hq]

theorem pair_equal_bit_zeros (b : Bool) (v : Pair → ℂ)
    (hv : Pone.mulVec v=v) (hs : pairSupported b v) :
    v (.zero,.zero)=0 ∧ v (occupiedSpin b,occupiedSpin b)=0 := by
  obtain ⟨c,hc⟩ := pairImage_equal_bits b v hv hs
  constructor
  · rw [hc]; cases b <;> norm_num [occupiedSpin,insertion,charge]
  · rw [hc]; cases b <;> norm_num [occupiedSpin,insertion,charge]

 

theorem triple_bit_first_equal (b d : Bool) (v : ThreeTensor)
    (hs : tripleBitSupported b b d v)
    (hfirst : ∀ c, Pone.mulVec (fun ab => v ab.1 ab.2 c) = fun ab => v ab.1 ab.2 c)
    (hlast : b=d → ∀ a, Pone.mulVec (fun bc => v a bc.1 bc.2) = fun bc => v a bc.1 bc.2)
    (hcup : ∀ a, ∑ bc : Pair, cup bc*v a bc.1 bc.2 = 0) :
    ∀ a b c, v a b c=0 := by
  have hp (c : Spin) : pairSupported b (fun ab => v ab.1 ab.2 c) := by
    intro ab hab
    exact hs _ _ _ (fun hh => hab ⟨hh.1,hh.2.1⟩)
  choose u hu using fun c => pairImage_equal_bits b _ (hfirst c) (hp c)
  have hv (a b' c : Spin) : v a b' c=insertion (a,b') (occupiedSpin b)*u c := hu c (a,b')
  have hus (s : Spin) (h : ¬allowedSpin d s) : u s=0 := by
    have hvs := hs (occupiedSpin b) .zero s (fun hh => h hh.2.2)
    rw [hv] at hvs
    exact (mul_eq_zero.mp hvs).resolve_left (insertion_edges_ne_zero b).1
  have hx : xStar ≠ 0 := by
    unfold xStar
    exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity : (0:ℝ)<2+Real.sqrt 2))
  have hq : q ≠ 0 := Complex.exp_ne_zero _
  have huall : ∀ s, u s=0 := by
    by_cases hbd : b=d
    · subst d
      have hz (a : Spin) : v a .zero .zero=0 ∧ v a (occupiedSpin b) (occupiedSpin b)=0 := by
        apply pair_equal_bit_zeros b _ (hlast rfl a)
        intro bc hbc
        exact hs _ _ _ (fun hh => hbc hh.2)
      have h0 := (hz (occupiedSpin b)).1
      rw [hv] at h0
      have hu0 := (mul_eq_zero.mp h0).resolve_left (insertion_edges_ne_zero b).1
      have h1 := (hz .zero).2
      rw [hv] at h1
      have hu1 := (mul_eq_zero.mp h1).resolve_left (insertion_edges_ne_zero b).2
      intro s
      by_cases ha : allowedSpin b s
      · rcases ha with rfl | rfl
        · exact hu0
        · exact hu1
      · exact hus s ha
    · have h0 := hcup (occupiedSpin b)
      have h1 := hcup .zero
      simp only [hv] at h0 h1
      cases b <;> cases d
      · exact (hbd rfl).elim
      · have hu0 : u .zero=0 := by
          simpa [sum_pair,occupiedSpin,insertion,cup,charge,zpow_neg,q_five_inv,hx,hq] using h0
        have hu1 : u .minus=0 := by
          simpa [sum_pair,occupiedSpin,insertion,cup,charge,zpow_neg,q_five_inv,hx,hq] using h1
        intro s
        cases s
        · exact hu0
        · exact hus .plus (by simp [allowedSpin,occupiedSpin])
        · exact hu1
      · have hu0 : u .zero=0 := by
          simpa [sum_pair,occupiedSpin,insertion,cup,charge,zpow_neg,q_five_inv,hx,hq] using h0
        have hu1 : u .plus=0 := by
          simpa [sum_pair,occupiedSpin,insertion,cup,charge,zpow_neg,q_five_inv,hx,hq] using h1
        intro s
        cases s
        · exact hu0
        · exact hu1
        · exact hus .minus (by simp [allowedSpin,occupiedSpin])
      · exact (hbd rfl).elim
  intro a b' c
  rw [hv,huall,mul_zero]

 

theorem triple_bit_last_equal (b d : Bool) (v : ThreeTensor)
    (hs : tripleBitSupported d b b v)
    (hlast : ∀ a, Pone.mulVec (fun bc => v a bc.1 bc.2) = fun bc => v a bc.1 bc.2)
    (hfirst : b=d → ∀ c, Pone.mulVec (fun ab => v ab.1 ab.2 c) = fun ab => v ab.1 ab.2 c)
    (hcup : ∀ c, ∑ ab : Pair, cup ab*v ab.1 ab.2 c = 0) :
    ∀ a b c, v a b c=0 := by
  have hp (a : Spin) : pairSupported b (fun bc => v a bc.1 bc.2) := by
    intro bc hbc
    exact hs _ _ _ (fun hh => hbc hh.2)
  choose u hu using fun a => pairImage_equal_bits b _ (hlast a) (hp a)
  have hv (a b' c : Spin) : v a b' c=insertion (b',c) (occupiedSpin b)*u a := hu a (b',c)
  have hus (s : Spin) (h : ¬allowedSpin d s) : u s=0 := by
    have hvs := hs s .zero (occupiedSpin b) (fun hh => h hh.1)
    rw [hv] at hvs
    exact (mul_eq_zero.mp hvs).resolve_left (insertion_edges_ne_zero b).2
  have hx : xStar ≠ 0 := by
    unfold xStar
    exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity : (0:ℝ)<2+Real.sqrt 2))
  have hq : q ≠ 0 := Complex.exp_ne_zero _
  have huall : ∀ s, u s=0 := by
    by_cases hbd : b=d
    · subst d
      have hz (c : Spin) : v .zero .zero c=0 ∧ v (occupiedSpin b) (occupiedSpin b) c=0 := by
        apply pair_equal_bit_zeros b _ (hfirst rfl c)
        intro ab hab
        exact hs _ _ _ (fun hh => hab ⟨hh.1,hh.2.1⟩)
      have h0 := (hz (occupiedSpin b)).1
      rw [hv] at h0
      have hu0 := (mul_eq_zero.mp h0).resolve_left (insertion_edges_ne_zero b).2
      have h1 := (hz .zero).2
      rw [hv] at h1
      have hu1 := (mul_eq_zero.mp h1).resolve_left (insertion_edges_ne_zero b).1
      intro s
      by_cases ha : allowedSpin b s
      · rcases ha with rfl | rfl
        · exact hu0
        · exact hu1
      · exact hus s ha
    · have h0 := hcup (occupiedSpin b)
      have h1 := hcup .zero
      simp only [hv] at h0 h1
      cases b <;> cases d
      · exact (hbd rfl).elim
      · have hu0 : u .zero=0 := by
          simpa [sum_pair,occupiedSpin,insertion,cup,charge,zpow_neg,q_five_inv,hx,hq] using h0
        have hu1 : u .minus=0 := by
          simpa [sum_pair,occupiedSpin,insertion,cup,charge,zpow_neg,q_five_inv,hx,hq] using h1
        intro s
        cases s
        · exact hu0
        · exact hus .plus (by simp [allowedSpin,occupiedSpin])
        · exact hu1
      · have hu0 : u .zero=0 := by
          simpa [sum_pair,occupiedSpin,insertion,cup,charge,zpow_neg,q_five_inv,hx,hq] using h0
        have hu1 : u .plus=0 := by
          simpa [sum_pair,occupiedSpin,insertion,cup,charge,zpow_neg,q_five_inv,hx,hq] using h1
        intro s
        cases s
        · exact hu0
        · exact hu1
        · exact hus .minus (by simp [allowedSpin,occupiedSpin])
      · exact (hbd rfl).elim
  intro a b' c
  rw [hv,huall,mul_zero]

end PolynomialVacuumAlgebra

end OAI
