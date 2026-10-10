import OAI.NumberTheory.JointDickman.Analysis.ShortMellinDyadicEnergy
import OAI.NumberTheory.JointDickman.Analysis.MellinFloorEndpoints

namespace OAI

/-! # A quantitative short-average consequence of two affine dyadic bounds -/
namespace JointDickman
open Finset MeasureTheory PublishedInputs

lemma short_affine_budget {X H a b : ℝ} {N : ℕ}
    (hN : 1≤(N:ℝ)) (hXN : X≤2*N) (hH : 0<H) (_ha : 0≤a) (hb : 0≤b) :
    8*a+(8*b/(N:ℝ)+3/(N:ℝ)^2)*X/H ≤ 8*a+16*b/H+6/H := by
  have hn : (0:ℝ)<N := by linarith
  have h1 : X/(N:ℝ)≤2 := (div_le_iff₀ hn).mpr (by nlinarith only [hXN])
  have h2 : X/(N:ℝ)^2≤2 := (div_le_iff₀ (sq_pos_of_pos hn)).mpr (by
    nlinarith only [hXN,hN])
  have hb' := mul_le_mul_of_nonneg_left h1 (show 0≤8*b/H by positivity)
  have hc' := mul_le_mul_of_nonneg_left h2 (show 0≤3/H by positivity)
  linear_combination hb'+hc'

theorem shortAverage_of_dyadic_affine (η : ℝ) (hη : 0<η) (hηhalf : η<1/2)
    (m : ℕ) (hm : 0<m) :
    ∃ C : ℝ, 0<C ∧ ∀ f : ArithmeticFunction ℂ, (∀ n, ‖f n‖≤1) →
      ∀ X H a b : ℝ, 2≤X → 1≤H → H^2≤X → 0≤a → 0≤b →
      (∀ (N : ℕ), N=⌊X⌋₊ ∨ N=2*⌊X⌋₊ → ∀ T : ℝ, 1≤T →
        (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) ≤ a+b*T/N) →
      (1/X)*(∫ x in X..2*X, ‖complexShortAverage f H x‖^2) ≤
        C*(8*a+16*b/H+6/H)+2*(3/(m:ℝ)+13/H+16*η)^2 := by
  obtain ⟨C,hC,hshort⟩ := shortAverage_dyadic_energy η hη hηhalf m hm
  refine ⟨C,hC,?_⟩
  intro f hf X H a b hX hH hHX ha hb hspec
  let N := ⌊X⌋₊
  have hXp : 0<X := by linarith
  have hHp : 0<H := by linarith
  have hNnat : 1≤N := (Nat.le_floor_iff hXp.le).mpr (by simp only [Nat.cast_one]; linarith)
  have hN : 1≤(N:ℝ) := by exact_mod_cast hNnat
  have hNp : (0:ℝ)<N := by linarith
  have hXN : X≤2*N := by
    have hh := Nat.lt_floor_add_one X
    change X<(N:ℝ)+1 at hh
    linarith
  have hNX : H≤X := by nlinarith only [hH,hHX]
  have htwo := mellinPolynomial_two_dyadic_energy f N ha (by positivity : 0≤b/(N:ℝ))
    (by intro T hT; convert hspec N (Or.inl rfl) T hT using 1; ring)
    (by
      intro T hT
      have hh := hspec (2*N) (Or.inr rfl) T hT
      rw [show 2*(2*N)=4*N by omega] at hh
      have hn2 : (N:ℝ)≤((2*N:ℕ):ℝ) := by push_cast; linarith
      have hbT : 0≤b*T := by positivity
      apply hh.trans
      have hd := div_le_div_of_nonneg_left hbT hNp hn2
      convert add_le_add_left hd a using 1 <;> ring)
  have hfull := mellinPolynomial_real_cutoff_energy f hf (by linarith : 1≤X) htwo
  have hi := hshort f hf X H hXp hH hNX
    (8*a) (8*b/(N:ℝ)+3/(N:ℝ)^2) (by positivity) (by positivity) (by
      intro T hT
      convert hfull T hT using 1; ring)
  have hbgt := short_affine_budget hN hXN hHp ha hb
  have hHratio : H/X≤1/H := by
    apply (div_le_div_iff₀ hXp hHp).mpr
    nlinarith only [hHX]
  have hXinv : 1/X≤1/H := one_div_le_one_div_of_le hHp hNX
  have hsmooth : 2*(3/(m:ℝ)+11/H+H/X+1/X+16*η)^2 ≤
      2*(3/(m:ℝ)+13/H+16*η)^2 := by
    have hsum : 3/(m:ℝ)+11/H+H/X+1/X+16*η ≤ 3/(m:ℝ)+13/H+16*η := by
      linear_combination hHratio+hXinv
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum 2) (by norm_num)
  exact hi.trans (add_le_add (mul_le_mul_of_nonneg_left hbgt hC.le) hsmooth)

end JointDickman

end OAI
