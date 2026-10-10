import Mathlib
import OAI.Probability.SKGap.Brownian.PathExpectation

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology

theorem actual_path_bias_of_cutoff {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (hs : sqrt j*A < 1) (f : 𝓢(ℝ,ℂ))
    (hf : ∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹)
    (hR : 0 ≤ 2*sqrt j+1+1) :
    ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧
      ∀ n,N≤n → ∀ a : Fin n→ℝ,(∀ i,0≤a i) → (∀ i,a i≤A) →
        ∀ z∈Icc (0:ℝ) 1,∀ i,
          |pathExpected f (2*sqrt j+1+1) hR j a z i-1|≤C/(n:ℝ) := by
  let R := 2*sqrt j+1+1
  let lo := (1-sqrt j*A)^2/4
  let hi := 2+A*(2*sqrt j+1+j*A)
  have hinterval := path_interval hj.le hA.le hs
  let B := pathBound f R j A
  let L := pathLip f R j A
  let rate := pathRate j A
  have hrate : 0 < rate := pathRate_pos hj hA hs
  have hBL := path_constants_nonneg f hR hj.le hA.le
  have hB : 0 ≤ B := hBL.1
  let C₁ := loopErrorConstantOne j A B L rate
  let C₂ := loopErrorConstantTwo j A B rate
  let C₀ := C₂+A*C₁
  have hCs := loopErrorConstants_nonneg j A B L rate hj.le hA.le hBL.1 hBL.2 hrate
  have hC₀ : 0 ≤ C₀ := add_nonneg hCs.2 (mul_nonneg hA.le hCs.1)
  have hsub : j*A^2 < 1 := by
    have hp := mul_nonneg (sqrt_nonneg j) hA.le
    have he : (sqrt j*A)^2=j*A^2 := by rw [mul_pow,sq_sqrt hj.le]
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hs.le)]
  obtain ⟨δ,γ,e,hδ,hγ,he,hboot⟩ := exists_bootstrap_constants hj.le hA.le hBL.1 hsub
  have hev : ∀ᶠ n : ℕ in atTop, C₀/(n:ℝ) < e :=
    (tendsto_const_div_atTop_nhds_zero_nat C₀).eventually (gt_mem_nhds he)
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((path_size_eventually hs).and hev)
  let C := (j*A*B*A/γ+1)*C₀+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,N+1,hC,Nat.succ_pos _,?_⟩
  intro n hn a ha haA z hz i
  have hn0 : 0 < n := lt_of_lt_of_le (Nat.succ_pos N) hn
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  have hnr : (0:ℝ) < n := Nat.cast_pos.mpr hn0
  have hsize := (hN n (Nat.le_of_succ_le hn)).1
  have hsmall := (hN n (Nat.le_of_succ_le hn)).2
  have hm := hboot (C₀/(n:ℝ)) (div_nonneg hC₀ hnr.le) hsmall.le
  have hw : ∀ _ : Fin n, 0 ≤ (1/(n:ℝ)) := fun _ => by positivity
  have hws : (∑ _ : Fin n, (1/(n:ℝ)))=1 := by simp [hn0.ne']
  have hb := loop_global_control hw hws ha haA hA.le hj.le
    (fun b => pathExpected_continuous f hR hj.le hA.le ha haA b)
    (fun b => pathExpected_zero f hR j a b)
    (fun u hu b => pathExpected_bound f hR hj.le hA.le ha haA hu b)
    (div_nonneg hC₀ hnr.le) hδ hγ
    (fun u hu b => by
      have hp := path_goodSet_exponential hj hA ha haA hs
        (by simpa only [Fintype.card_fin] using hsize) hu
      simpa only [Fintype.card_fin] using path_self_consistency f hinterval.1 hf hR
        hj.le hA.le hrate ha haA hu hp b)
    hm.1 hm.2 z hz
  have hh := hb.2 i
  apply hh.trans
  change j*A*B*(A*(C₀/(n:ℝ))/γ)+C₀/(n:ℝ) ≤ C/(n:ℝ)
  calc
    _ = ((j*A*B*A/γ+1)*C₀)/(n:ℝ) := by ring
    _ ≤ C/(n:ℝ) := by apply div_le_div_of_nonneg_right _ hnr.le; dsimp [C]; linarith
end SKGap
end
end

end OAI
