import Mathlib
import OAI.Probability.SKGap.Brownian.PathBias

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology

theorem actual_path_equivalents {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (hs : sqrt j*A < 1) :
    ∃ (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (lo hi C : ℝ) (N : ℕ),
      R = 2*sqrt j+1+1 ∧ lo = (1-sqrt j*A)^2/4 ∧ hi = 2+A*(2*sqrt j+1+j*A) ∧
      0 < lo ∧ (∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹) ∧ (∀ x, star (f x)=f x) ∧
      0 < C ∧ 0 < N ∧
      (∀ (n : ℕ), N ≤ n → ∀ (a : Fin n → ℝ), (∀ i, 0 ≤ a i) →
        (∀ i, a i ≤ A) → ∀ z ∈ Icc (0:ℝ) 1, ∀ i,
          |pathExpected f R hR j a z i-1| ≤ C/(n:ℝ) ∧
          |pathExpectedWK f R hR j a z i-z*((j/(n:ℝ))*∑ b, a b)| ≤ C/(n:ℝ)) := by
  obtain ⟨f,R,hR,lo,hi,CK,N,hReq,hloeq,hhieq,hlo,hf,hfr,hCK,hN,hK⟩ := actual_path_bias hj hA hs
  let B := pathBound f R j A
  let L := pathLip f R j A
  let rate := pathRate j A
  have hrate : 0 < rate := pathRate_pos hj hA hs
  have hBL := path_constants_nonneg f hR hj.le hA.le
  let C₁ := loopErrorConstantOne j A B L rate
  have hC₁ : 0 ≤ C₁ := (loopErrorConstants_nonneg j A B L rate hj.le hA.le hBL.1 hBL.2 hrate).1
  have hB : 0 ≤ B := hBL.1
  let CW := C₁+j*A*CK*(B+1)
  have hCW : 0 ≤ CW := by dsimp [CW]; positivity
  let C := CK+CW+1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp (path_size_eventually hs)
  refine ⟨f,R,hR,lo,hi,C,max N N₁,hReq,hloeq,hhieq,hlo,hf,hfr,hC,
    lt_of_lt_of_le hN (le_max_left _ _),?_⟩
  intro n hn a ha haA z hz i
  have hnN : N ≤ n := (le_max_left N N₁).trans hn
  have hn0 : 0 < n := hN.trans_le hnN
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  have hnr : (0:ℝ) < n := Nat.cast_pos.mpr hn0
  have hk := hK n hnN a ha haA z hz
  have hp := path_goodSet_exponential hj hA ha haA hs
    (by simpa only [Fintype.card_fin] using hN₁ n ((le_max_right N N₁).trans hn)) hz
  rw [← hReq,← hloeq,← hhieq] at hp
  have hw := path_wk_bias f hlo hf hR hj.le hA.le hrate
    (div_nonneg hCK.le hnr.le) ha haA hz hp hk i
  simp only [Fintype.card_fin] at hw
  constructor
  · apply (hk i).trans
    apply div_le_div_of_nonneg_right _ hnr.le
    dsimp [C]; linarith
  · apply hw.trans
    calc
      _ = CW/(n:ℝ) := by dsimp [CW,C₁,B,L,rate]; ring
      _ ≤ C/(n:ℝ) := by
        apply div_le_div_of_nonneg_right _ hnr.le
        dsimp [C]; linarith
end SKGap
end
end

end OAI
