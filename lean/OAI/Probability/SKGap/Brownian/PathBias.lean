import Mathlib
import OAI.Probability.SKGap.Brownian.PathExpectation

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology

theorem actual_path_bias {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (hs : sqrt j*A < 1) :
    ∃ (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (lo hi C : ℝ) (N : ℕ),
      R = 2*sqrt j+1+1 ∧ lo = (1-sqrt j*A)^2/4 ∧ hi = 2+A*(2*sqrt j+1+j*A) ∧
      0 < lo ∧ (∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹) ∧ (∀ x, star (f x)=f x) ∧
      0 < C ∧ 0 < N ∧
      (∀ (n : ℕ), N ≤ n → ∀ (a : Fin n → ℝ), (∀ i, 0 ≤ a i) →
        (∀ i, a i ≤ A) → ∀ z ∈ Icc (0:ℝ) 1, ∀ i,
          |pathExpected f R hR j a z i-1| ≤ C/(n:ℝ)) := by
  let R := 2*sqrt j+1+1
  let lo := (1-sqrt j*A)^2/4
  let hi := 2+A*(2*sqrt j+1+j*A)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hinterval := path_interval hj.le hA.le hs
  obtain ⟨f,hf,hfr⟩ := exists_schwartz_inverse hinterval.1 hinterval.2
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
  refine ⟨f,R,hR,lo,hi,C,N+1,rfl,rfl,rfl,hinterval.1,hf,hfr,hC,Nat.succ_pos _,?_⟩
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

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def pathExpectedWK (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (j : ℝ) (a : ι → ℝ)
    (z : ℝ) (i : ι) : ℝ :=
  ∫ g, (goeMatrix (j/(Fintype.card ι:ℝ)) g * realTruncatedK f R hR (pathDiagonal a z)
    (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)) (goeMatrix (j/(Fintype.card ι:ℝ)) g)) i i
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)

lemma path_wk_bias (f : 𝓢(ℝ,ℂ)) {lo hi R j A rate z ε : ℝ} {a : ι → ℝ}
    (hlo : 0 < lo) (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA0 : 0 ≤ A) (hrate : 0 < rate) (hε : 0 ≤ ε)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hz : z ∈ Icc (0:ℝ) 1)
    (hp : (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      (truncationGoodSet (j/(Fintype.card ι:ℝ)) R lo hi (pathDiagonal a z)
        (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)))ᶜ ≤
          3*Real.exp (-rate*(Fintype.card ι:ℝ)))
    (hk : ∀ i, |pathExpected f R hR j a z i-1| ≤ ε) (i : ι) :
    |pathExpectedWK f R hR j a z i-z*((j/(Fintype.card ι:ℝ))*∑ b, a b)| ≤
      loopErrorConstantOne j A (pathBound f R j A) (pathLip f R j A) rate/(Fintype.card ι:ℝ)+
        j*A*ε*(pathBound f R j A+1) := by
  let n : ℝ := Fintype.card ι
  let q := (j/n)*∑ b, a b
  let d : ι → ℝ := fun b => sqrt z*sqrt (a b)
  let c : ι → ℝ := fun _ => z*q
  let k := pathExpected f R hR j a z
  let B := pathBound f R j A
  let L := pathLip f R j A
  let t := (j/n)*∑ b, (d b)^2*k b
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast Fintype.card_pos (α := ι)
  have hq := diagonal_mean_bounds hj ha hA
  have hcst := path_constants_bound f hR hj hA0 hA hq.1 hq.2 hz
  have hconst := path_constants_nonneg f hR hj hA0
  have hd (b : ι) : (d b)^2=z*a b := by
    dsimp [d]; rw [mul_pow,sq_sqrt hz.1,sq_sqrt (ha b)]
  have he1 := (cutoffErrorOne_bound f (pathDiagonal a z) (pathShift z q) hj hA0 hconst.1 hconst.2 hR
    hcst.1 hcst.2.1 hcst.2.2 (le_refl _)).trans
      (loop_error_one_absorption hj hA0 hconst.1 hconst.2 hrate hn1 hp)
  have he := realTruncatedK_first_loop f hlo hf hR (div_nonneg hj hn.le)
    (diagonal d) (diagonal c) (diagonal_transpose _) (diagonal_transpose _) i
  dsimp only at he
  rw [integrated_diagonal_trace] at he
  change |pathExpectedWK f R hR j a z i-t*k i| ≤ cutoffErrorOne f (j/n) R lo hi (diagonal d) (diagonal c) at he
  have he' := he.trans he1
  have hm : |∑ b, (1/n)*a b*(k b-1)| ≤ A*ε := by
    have hws : (∑ _ : ι, (1/n))=1 := by simp [n,Fintype.card_ne_zero]
    have hh := weighted_abs_sum_le (w := fun _ : ι => 1/n) (v := fun b => a b*(k b-1))
      (by intro b; positivity) (C := A*ε) (fun b => by
        rw [abs_mul,abs_of_nonneg (ha b)]
        exact mul_le_mul (hA b) (hk b) (abs_nonneg _) hA0)
    rw [hws,one_mul] at hh
    simpa only [mul_assoc] using hh
  have hs : t-z*q = z*j*(∑ b, (1/n)*a b*(k b-1)) := by
    dsimp only [t,q]
    simp_rw [hd,Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have ht : |t-z*q| ≤ j*A*ε := by
    rw [hs,abs_mul,abs_mul,abs_of_nonneg hz.1,abs_of_nonneg hj]
    calc
      _ ≤ 1*j*(A*ε) := mul_le_mul (mul_le_mul_of_nonneg_right hz.2 hj) hm (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hzq : |z*q| ≤ j*A := by
    rw [abs_of_nonneg (mul_nonneg hz.1 hq.1)]
    exact (mul_le_of_le_one_left hq.1 hz.2).trans hq.2
  have hkB : |k i| ≤ B := pathExpected_bound f hR hj hA0 ha hA hz i
  have heq : pathExpectedWK f R hR j a z i-z*q =
      (pathExpectedWK f R hR j a z i-t*k i)+(t-z*q)*k i+z*q*(k i-1) := by ring
  change |pathExpectedWK f R hR j a z i-z*q| ≤ _
  rw [heq]
  calc
    _ ≤ |pathExpectedWK f R hR j a z i-t*k i|+|(t-z*q)*k i|+|z*q*(k i-1)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ loopErrorConstantOne j A B L rate/n+(j*A*ε)*B+(j*A)*ε := by
      apply add_le_add
      · apply add_le_add he'
        rw [abs_mul]
        exact mul_le_mul ht hkB (abs_nonneg _) (by positivity)
      · rw [abs_mul]
        exact mul_le_mul hzq (hk i) (abs_nonneg _) (mul_nonneg hj hA0)
    _ = _ := by ring
end SKGap
end
end

end OAI
