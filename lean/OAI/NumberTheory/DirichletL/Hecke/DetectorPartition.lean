import OAI.NumberTheory.DirichletL.Hecke.DetectorWitnessArithmetic

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeDetectorPartition
open DyadicTransfer

theorem partition (V : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (n J : ℕ) (hn : 1 ≤ n) (hJ : (n : ℝ) ≤ (2 : ℝ)^J) :
    (∑ j ∈ Finset.range (J+1), annularCutoff V ((n : ℝ)/(2 : ℝ)^j)) = 1 := by
  rw [partial_partition]
  rw [hsmall _ (by positivity) ((div_le_one (by positivity)).mpr hJ)]
  rw [hlarge _ (by exact_mod_cast (show 2 ≤ 2*n by omega))]
  ring

theorem finite_pair_reassembly {A : Type*} (S : Finset A) (a : A → ℂ)
    (n m : A → ℕ) (V : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (J K : ℕ)
    (hn : ∀ p ∈ S, 1 ≤ n p ∧ (n p : ℝ) ≤ (2 : ℝ)^J)
    (hm : ∀ p ∈ S, 1 ≤ m p ∧ (m p : ℝ) ≤ (2 : ℝ)^K) :
    (∑ p ∈ S, a p) =
      ∑ j ∈ Finset.range (J+1), ∑ k ∈ Finset.range (K+1), ∑ p ∈ S,
        a p * annularCutoff V ((n p : ℝ)/(2 : ℝ)^j) *
          annularCutoff V ((m p : ℝ)/(2 : ℝ)^k) := by
  symm
  calc
    _ = ∑ p ∈ S, ∑ j ∈ Finset.range (J+1), ∑ k ∈ Finset.range (K+1),
        a p * annularCutoff V ((n p : ℝ)/(2 : ℝ)^j) *
          annularCutoff V ((m p : ℝ)/(2 : ℝ)^k) := by
      calc
        _ = ∑ j ∈ Finset.range (J+1), ∑ p ∈ S, ∑ k ∈ Finset.range (K+1),
            a p * annularCutoff V ((n p : ℝ)/(2 : ℝ)^j) *
              annularCutoff V ((m p : ℝ)/(2 : ℝ)^k) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      simp_rw [← Finset.mul_sum]
      rw [partition V hsmall hlarge (m p) K (hm p hp).1 (hm p hp).2]
      simp only [mul_one]
      rw [← Finset.mul_sum, partition V hsmall hlarge (n p) J (hn p hp).1 (hn p hp).2,
        mul_one]

theorem annular_support (V : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (x : ℝ) (hx : 0 ≤ x) (j : ℕ)
    (hne : annularCutoff V (x/(2 : ℝ)^j) ≠ 0) :
    (2 : ℝ)^j / 2 < x ∧ x < 2*(2 : ℝ)^j := by
  have hp : 0 < (2 : ℝ)^j := by positivity
  have hy : 0 ≤ x/(2 : ℝ)^j := div_nonneg hx hp.le
  have hlo : 1/2 < x/(2 : ℝ)^j := by
    by_contra h
    have hh := le_of_not_gt h
    apply hne
    rw [annularCutoff, hsmall _ hy (by linarith), hsmall _ (by positivity) (by linarith)]
    ring
  have hhi : x/(2 : ℝ)^j < 2 := by
    by_contra h
    apply hne
    exact annularCutoff_eq_zero_of_two_le V hlarge (le_of_not_gt h)
  constructor
  · have := (lt_div_iff₀ hp).mp hlo
    linarith
  · exact (div_lt_iff₀ hp).mp hhi

def length (X : ℝ) : ℕ := ⌈Real.logb 2 X⌉₊

theorem norm_le_last_scale (X : ℝ) (hX : 0 < X) : X ≤ (2 : ℝ)^(length X) := by
  have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hX).mp
    (Nat.le_ceil (Real.logb 2 X))
  simpa only [Real.rpow_natCast, length] using h

theorem length_bound (X : ℝ) (hX : 1 ≤ X) :
    (length X : ℝ) + 1 < Real.logb 2 X + 2 := by
  have hlog : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX
  have h := Nat.ceil_lt_add_one hlog
  change (⌈Real.logb 2 X⌉₊ : ℝ) + 1 < _
  linarith

theorem pair_scale_bounds (V T : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (hterm : ∀ y : ℝ, 2 ≤ y → T y = 0)
    (x y D U : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hD : 0 < D) (hU : 0 < U)
    (j k : ℕ)
    (hj : annularCutoff V (x/(2 : ℝ)^j) ≠ 0)
    (hk : annularCutoff V (y/(2 : ℝ)^k) ≠ 0)
    (hfirst : V (x/D) ≠ 0)
    (hproduct : 1 - V (2*(x*y)/D) ≠ 0)
    (hterminal : T (x*y/U) ≠ 0) :
    (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
      (2 : ℝ)^j*(2 : ℝ)^k < 8*U := by
  obtain ⟨hjlo,hjhi⟩ := annular_support V hsmall hlarge x hx j hj
  obtain ⟨hklo,hkhi⟩ := annular_support V hsmall hlarge y hy k hk
  have hJ : 0 < (2 : ℝ)^j := by positivity
  have hK : 0 < (2 : ℝ)^k := by positivity
  have hxd : x < 2*D := by
    by_contra h
    apply hfirst
    apply hlarge
    exact (le_div_iff₀ hD).mpr (le_of_not_gt h)
  have hprod : D < 2*(x*y) := by
    by_contra h
    apply hproduct
    rw [hsmall _ (by positivity) ((div_le_one hD).mpr (le_of_not_gt h))]
    ring
  have hxyU : x*y < 2*U := by
    by_contra h
    apply hterminal
    apply hterm
    exact (le_div_iff₀ hU).mpr (le_of_not_gt h)
  have hlo : (2 : ℝ)^j*(2 : ℝ)^k/4 < x*y := by
    have h1 := mul_lt_mul_of_pos_right hjlo (show 0 < y by linarith)
    have h2 := mul_lt_mul_of_pos_left hklo (show 0 < (2 : ℝ)^j/2 by positivity)
    nlinarith
  have hhi : x*y < 4*((2 : ℝ)^j*(2 : ℝ)^k) := by
    have h1 := mul_lt_mul_of_pos_right hjhi (show 0 < y by linarith)
    have h2 := mul_lt_mul_of_pos_left hkhi (show 0 < 2*(2 : ℝ)^j by positivity)
    nlinarith
  constructor
  · linarith
  constructor <;> linarith

def pairCoefficient (χ : HeckeFamily.Character) (V T : ℝ → ℂ)
    (D Y U : ℝ) (s : ℂ) (p : Ideal HeckeFamily.O × Ideal HeckeFamily.O) : ℂ :=
  (UniqueFactorizationMonoid.moebius p.1 : ℂ) * V ((Ideal.absNorm p.1 : ℝ)/D) *
    IdealEuler.weighted (HeckeFamily.idealCoeff χ) s (p.1*p.2) *
    Complex.exp (-((Ideal.absNorm (p.1*p.2) : ℝ) : ℂ)/(Y : ℂ)) *
    (1-V (2*(Ideal.absNorm (p.1*p.2) : ℝ)/D)) * T ((Ideal.absNorm (p.1*p.2) : ℝ)/U)

theorem actual_pair_reassembly (χ : HeckeFamily.Character) (V T : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (D Y U X Z : ℝ) (hX : 0 < X) (hZ : 0 < Z) (s : ℂ)
    (S : Finset (Ideal HeckeFamily.O × Ideal HeckeFamily.O))
    (hS : ∀ p ∈ S, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧
      (Ideal.absNorm p.1 : ℝ) ≤ X ∧ (Ideal.absNorm p.2 : ℝ) ≤ Z) :
    (∑ p ∈ S, pairCoefficient χ V T D Y U s p) =
      ∑ j ∈ Finset.range (length X+1), ∑ k ∈ Finset.range (length Z+1), ∑ p ∈ S,
        pairCoefficient χ V T D Y U s p *
          annularCutoff V ((Ideal.absNorm p.1 : ℝ)/(2 : ℝ)^j) *
          annularCutoff V ((Ideal.absNorm p.2 : ℝ)/(2 : ℝ)^k) := by
  apply finite_pair_reassembly S _ _ _ V hsmall hlarge
  · intro p hp
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS p hp).1),
      (hS p hp).2.2.1.trans (norm_le_last_scale X hX)⟩
  · intro p hp
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS p hp).2.1),
      (hS p hp).2.2.2.trans (norm_le_last_scale Z hZ)⟩

theorem exists_large_pair (J K : ℕ) (F : ℕ → ℕ → ℂ) :
    ∃ j ∈ Finset.range (J+1), ∃ k ∈ Finset.range (K+1),
      ‖∑ j ∈ Finset.range (J+1), ∑ k ∈ Finset.range (K+1), F j k‖ ≤
        ((J+1 : ℕ) : ℝ)*((K+1 : ℕ) : ℝ)*‖F j k‖ := by
  let S := (Finset.range (J+1)) ×ˢ (Finset.range (K+1))
  have hS : S.Nonempty := ⟨(0,0), by simp [S]⟩
  obtain ⟨p,hp,hmax⟩ := S.exists_max_image (fun p => ‖F p.1 p.2‖) hS
  obtain ⟨hj,hk⟩ := Finset.mem_product.mp hp
  refine ⟨p.1,hj,p.2,hk,?_⟩
  calc
    _ = ‖∑ q ∈ S, F q.1 q.2‖ := by rw [Finset.sum_product]
    _ ≤ ∑ q ∈ S, ‖F q.1 q.2‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ S, ‖F p.1 p.2‖ := Finset.sum_le_sum (fun q hq => hmax q hq)
    _ = _ := by simp [S, Finset.card_product, mul_assoc]

end SevenEighths.HeckeDetectorPartition

end

end OAI
