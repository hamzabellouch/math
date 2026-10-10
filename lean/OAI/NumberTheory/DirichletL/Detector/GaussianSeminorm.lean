import OAI.NumberTheory.DirichletL.Detector.GaussianDerivative

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open Filter Set
namespace SevenEighths.ProbePhysical

def gaussianFixedWindow (y : ℝ) : ℂ := gaussianAnnulus y/(Real.sqrt y:ℂ)
lemma gaussianFixedWindow_small (y : ℝ) (hy : y≤1/2) : gaussianFixedWindow y=0 := by
  simp only [gaussianFixedWindow,gaussianAnnulus_small y hy,zero_div]
lemma gaussianFixedWindow_large (y : ℝ) (hy : 2≤y) : gaussianFixedWindow y=0 := by
  simp only [gaussianFixedWindow,gaussianAnnulus_large y hy,zero_div]
lemma gaussianFixedWindow_compact : HasCompactSupport gaussianFixedWindow := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianFixedWindow y≠0 at hy
  constructor
  · by_contra h; exact hy (gaussianFixedWindow_small y (le_of_lt (lt_of_not_ge h)))
  · by_contra h; exact hy (gaussianFixedWindow_large y (le_of_lt (lt_of_not_ge h)))
lemma gaussianFixedWindow_contDiff : ContDiff ℝ ∞ gaussianFixedWindow := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0<y
  · have hs : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
    have hf : ContDiffAt ℝ ∞ (fun x : ℝ=>(Real.sqrt x:ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y (Real.contDiffAt_sqrt hy.ne')
    unfold gaussianFixedWindow
    simp only [div_eq_mul_inv]
    exact gaussianAnnulus_contDiff.contDiffAt.mul (hf.fun_inv hs)
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (show y<(1/2:ℝ) by linarith)] with x hx
    exact gaussianFixedWindow_small x hx.le

def gaussianFixedSchwartz : SchwartzMap ℝ ℂ := gaussianFixedWindow_compact.toSchwartzMap gaussianFixedWindow_contDiff

lemma gaussianProfile_scaled_smooth (r : ℝ) (hr : 0<r) (y : ℝ) (hy : 0<y) :
    ContDiffAt ℝ ∞ (fun x : ℝ=>gaussianMellinProfile (r*x)) y := by
  have hf : ContDiffAt ℂ ∞ (fun z : ℂ=>gaussianLog ((r:ℂ)*z)) (y:ℂ) :=
    (gaussianLog_scaled_analytic r hr (y:ℂ) hy).contDiffAt
  have hh := (hf.restrict_scalars ℝ).comp y Complex.ofRealCLM.contDiff.contDiffAt
  simpa only [Function.comp_def,Complex.ofRealCLM_apply,←Complex.ofReal_mul,gaussianLog_ofReal] using hh

lemma gaussianDyadicProfile_factor (Z : ℝ) (j : ℕ) :
    gaussianDyadicProfile Z j=(fun y : ℝ=>gaussianFixedWindow y*
      gaussianMellinProfile (((2:ℝ)^j/Z)*y)) := by
  funext y
  unfold gaussianDyadicProfile gaussianFixedWindow
  rw [show (2:ℝ)^j*y/Z=((2:ℝ)^j/Z)*y by ring]
  ring

lemma gaussianDyadicProfile_derivative_outside (Z : ℝ) (j n : ℕ) (y : ℝ)
    (hy : y∉Set.Icc (1/2:ℝ) 2) : iteratedDeriv n (gaussianDyadicProfile Z j) y=0 := by
  have he : gaussianDyadicProfile Z j=ᶠ[𝓝 y](fun _=>0) := by
    simp only [Set.mem_Icc,not_and_or,not_le] at hy
    rcases hy with hy|hy
    · filter_upwards [eventually_lt_nhds hy] with x hx
      exact gaussianDyadicProfile_small Z j x hx.le
    · filter_upwards [eventually_gt_nhds hy] with x hx
      exact gaussianDyadicProfile_large Z j x hx.le
  rw [he.iteratedDeriv_eq n]
  simp

lemma gaussianDyadicProfile_derivative_uniform (a : ℝ) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,0<Z→∀j : ℕ,∀y∈Set.Icc (1/2:ℝ) 2,
      ‖iteratedDeriv n (gaussianDyadicProfile Z j) y‖≤C*(((2:ℝ)^j/Z)^(-a)) := by
  choose B hB hbound using fun i : ℕ=>gaussianLog_scaled_derivative_bound a i
  let A (i : ℕ) := SchwartzMap.seminorm ℝ 0 i gaussianFixedSchwartz
  let C := ∑i∈Finset.range (n+1),(n.choose i:ℝ)*A i*B (n-i)
  have hA (i : ℕ) : 0≤A i := by exact apply_nonneg _ _
  have hC : 0≤C := Finset.sum_nonneg (fun i _=>mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _).le)
  refine ⟨C+1,by positivity,?_⟩
  intro Z hZ j y hy
  have hr : 0<(2:ℝ)^j/Z := div_pos (by positivity) hZ
  have hy0 : 0<y := by linarith [hy.1]
  rw [gaussianDyadicProfile_factor,iteratedDeriv_fun_mul
    (gaussianFixedWindow_contDiff.contDiffAt.of_le (by simp))
    ((gaussianProfile_scaled_smooth _ hr y hy0).of_le (by simp))]
  calc
    _ ≤ ∑i∈Finset.range (n+1),‖(n.choose i:ℂ)*iteratedDeriv i gaussianFixedWindow y*
        iteratedDeriv (n-i) (fun x : ℝ=>gaussianMellinProfile (((2:ℝ)^j/Z)*x)) y‖ := norm_sum_le _ _
    _ ≤ ∑i∈Finset.range (n+1),((n.choose i:ℝ)*A i)*(B (n-i)*(((2:ℝ)^j/Z)^(-a))) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,norm_mul,Complex.norm_natCast]
      have hfixed : ‖iteratedDeriv i gaussianFixedWindow y‖≤A i := by
        have hh := SchwartzMap.le_seminorm' ℝ 0 i gaussianFixedSchwartz y
        simp only [pow_zero,one_mul] at hh
        exact hh
      exact mul_le_mul (mul_le_mul_of_nonneg_left hfixed (Nat.cast_nonneg _))
        (hbound _ _ hr y hy) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
    _ = C*(((2:ℝ)^j/Z)^(-a)) := by simp only [C,Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ (C+1)*(((2:ℝ)^j/Z)^(-a)) := by nlinarith [Real.rpow_pos_of_pos hr (-a)]

theorem gaussianDyadicSchwartz_seminorm (a : ℝ) (k n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,∀j : ℕ,
      SchwartzMap.seminorm ℝ k n (gaussianDyadicSchwartz Z hZ j)≤C*(((2:ℝ)^j/Z)^(-a)) := by
  obtain ⟨B,hB,hbound⟩ := gaussianDyadicProfile_derivative_uniform a n
  refine ⟨(2:ℝ)^k*B,by positivity,?_⟩
  intro Z hZ j
  have hr : 0<(2:ℝ)^j/Z := div_pos (by positivity) hZ
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro y
  change |y|^k*‖iteratedDeriv n (gaussianDyadicProfile Z j) y‖≤_
  by_cases hy : y∈Set.Icc (1/2:ℝ) 2
  · have habs : |y|≤2 := by rw [abs_of_nonneg (by linarith [hy.1])]; exact hy.2
    calc
      _ ≤ (2:ℝ)^k*(B*(((2:ℝ)^j/Z)^(-a))) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) habs k) (hbound Z hZ j y hy)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [gaussianDyadicProfile_derivative_outside Z j n y hy,norm_zero,mul_zero]
    positivity

theorem gaussianDyadicSchwartz_finite_seminorm (a : ℝ) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,∀j : ℕ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
        C*(((2:ℝ)^j/Z)^(-a)) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1,by norm_num,?_⟩
    intro Z hZ j
    simp only [Finset.sup_empty,one_mul]
    change 0≤(((2:ℝ)^j/Z)^(-a))
    exact Real.rpow_nonneg (by positivity) _
  | @insert p S hp ih =>
    obtain ⟨B,hB,hbound⟩ := gaussianDyadicSchwartz_seminorm a p.1 p.2
    obtain ⟨C,hC,hrest⟩ := ih
    refine ⟨B+C,by positivity,?_⟩
    intro Z hZ j
    rw [Finset.sup_insert,Seminorm.sup_apply]
    apply max_le
    · exact (hbound Z hZ j).trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) (-a)])
    · exact (hrest Z hZ j).trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) (-a)])

theorem gaussianDyadicSchwartz_two_sided (A : ℝ) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,∀j : ℕ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
        C*min (((2:ℝ)^j/Z)^A) (((2:ℝ)^j/Z)^(-A)) := by
  obtain ⟨B,hB,hlo⟩ := gaussianDyadicSchwartz_finite_seminorm (-A) S
  obtain ⟨C,hC,hhi⟩ := gaussianDyadicSchwartz_finite_seminorm A S
  refine ⟨B+C,by positivity,?_⟩
  intro Z hZ j
  rw [mul_min_of_nonneg _ _ (by positivity : 0≤B+C)]
  apply le_min
  · have hh := hlo Z hZ j
    rw [neg_neg] at hh
    exact hh.trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) A])
  · exact (hhi Z hZ j).trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) (-A)])

end SevenEighths.ProbePhysical
end

end OAI
