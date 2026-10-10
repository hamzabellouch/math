import OAI.Analysis.Littlewood.SamplingTail

namespace OAI

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

/-- The off-diagonal average with nonzero curvature, used in the sampled
energy calculation. The amplitude bound is later applied to the squared cutoff. -/
theorem curved_average_zero {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {A D β : ℝ} (hA : 0≤A) (hD : 0≤D)
    (hsupp : tsupport g⊆Set.Icc (-A) A) (hbound : ∀ x, ‖g x‖≤D)
    (hβ : β≠0) (b : ℝ) :
    Tendsto (fun N : ℕ ↦ ‖(1/(N : ℂ))*(∑' k : ℤ,
      g ((k : ℝ)/N)*phase (β/N) (-b) k)‖) atTop (𝓝 0) := by
  obtain ⟨J,C,hC,herr⟩ := uniform_poisson_chirp hg hgs hA (abs_nonneg b) hsupp hβ
  let R := (J.card : ℝ)*D/Real.sqrt |β|+C
  have hR : 0≤R := by dsimp [R]; positivity
  have ht : Tendsto (fun N : ℕ ↦ R/Real.sqrt (N : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop R
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ norm_nonneg _)) ?_ ht
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : 1≤(N : ℝ) := by exact_mod_cast hN
  have hN0 : 0<(N : ℝ) := by positivity
  have hsN : 0<Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have he := (herr N b hNr le_rfl).2
  let S : ℂ := ∑' k : ℤ, g ((k : ℝ)/N)*phase (β/N) (-b) k
  have hw : ‖∑ l∈J, stationaryWave g N β b l‖≤(J.card : ℝ)*D/Real.sqrt |β| := by
    calc
      _ ≤ ∑ l∈J, ‖stationaryWave g N β b l‖ := norm_sum_le _ _
      _ ≤ ∑ _l∈J, D/Real.sqrt |β| := Finset.sum_le_sum (fun l _ ↦ by
        rw [stationaryWave_norm]; exact div_le_div_of_nonneg_right (hbound _) (Real.sqrt_nonneg _))
      _ = _ := by simp; ring
  have he' : ‖(1/(Real.sqrt (N : ℝ) : ℂ))*S‖≤R := by
    have hh := norm_add_le ((1/(Real.sqrt (N : ℝ) : ℂ))*S-∑ l∈J, stationaryWave g N β b l)
      (∑ l∈J, stationaryWave g N β b l)
    rw [sub_add_cancel] at hh
    have hdiv : C/(N : ℝ)≤C := (div_le_iff₀ hN0).mpr (by nlinarith)
    dsimp [R]
    linarith
  have heq : ‖(1/(N : ℂ))*S‖=‖(1/(Real.sqrt (N : ℝ) : ℂ))*S‖/Real.sqrt (N : ℝ) := by
    simp only [norm_mul,norm_div,norm_one,Complex.norm_natCast,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hsN]
    have hsq := Real.sq_sqrt hN0.le
    field_simp
    rw [hsq]
    ring
  change ‖(1/(N : ℂ))*S‖≤_
  rw [heq]
  exact div_le_div_of_nonneg_right he' hsN.le

/-- The linear (equal-curvature) case of the same off-diagonal calculation. -/
theorem linear_integral_decay {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {b : ℝ} {l : ℤ} (hl : (l : ℝ)≠b) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℝ, 0<N →
      N^2*‖∫ x : ℝ, g x*phase 0 (N*((l : ℝ)-b)) x‖≤C := by
  obtain ⟨C,hC,h⟩ := polynomial_decay 2 |(l : ℝ)-b| 0
    (abs_pos.mpr (sub_ne_zero.mpr hl)) le_rfl g hg hgs 0
  refine ⟨C,hC,?_⟩
  intro N hN
  have he := h 0 (N*((l : ℝ)-b)) N hN (by simp) (by
    intro x hx
    simp only [zero_mul,zero_sub,abs_neg,abs_mul,abs_of_pos hN]
    exact le_of_eq (mul_comm _ _))
  simpa only [Nat.zero_add,osc,amp,pow_zero,div_one] using he

/-- Averaged Poisson summation after removing a finite resonant set. This
single estimate handles both the diagonal Riemann sum and equal-curvature
cross terms without any uniformity in the packing data. -/
theorem linear_average_error {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {A : ℝ} (hA : 0≤A)
    (hsupp : tsupport g⊆Set.Icc (-A) A) (b : ℝ) (S : Finset ℤ)
    (hres : ∀ l∉S, (l : ℝ)≠b) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℝ, 0<N →
      ‖(1/(N : ℂ))*(∑' k : ℤ, g ((k : ℝ)/N)*phase 0 (-b) k)-
        ∑ l∈S, ∫ x : ℝ, g x*phase 0 (N*((l : ℝ)-b)) x‖≤C/N^2 := by
  classical
  obtain ⟨R,hR⟩ := exists_nat_gt (2*|b|+1)
  let J : Finset ℤ := Finset.Icc (-(R : ℤ)) R
  obtain ⟨C₀,hC₀,ht⟩ := poisson_tail_bound hg hgs (β := 0) hA (abs_nonneg b) hsupp
    (by simpa using hR.le)
  have hex (l : ℤ) : ∃ C : ℝ, 0≤C ∧ ∀ N : ℝ, 0<N → l∉S →
      N^2*‖∫ x : ℝ, g x*phase 0 (N*((l : ℝ)-b)) x‖≤C := by
    by_cases hl : l∈S
    · exact ⟨0,le_rfl,fun _ _ hn ↦ False.elim (hn hl)⟩
    · obtain ⟨C,hC,h⟩ := linear_integral_decay hg hgs (hres l hl)
      exact ⟨C,hC,fun N hN _ ↦ h N hN⟩
  choose c hc hdec using hex
  let w (l : ℤ) : ℝ := (if l∈J then c l else 0)+C₀*latticeWeight l
  have hw0 (l : ℤ) : 0≤w l := by
    dsimp [w]
    exact add_nonneg (by split_ifs; exact hc l; exact le_rfl)
      (mul_nonneg hC₀ (latticeWeight_pos l).le)
  have hw : Summable w := (summable_of_ne_finset_zero (s := J) (by
    intro l hl; simp [hl])).add (latticeWeight_summable.mul_left C₀)
  refine ⟨∑' l, w l,tsum_nonneg hw0,?_⟩
  intro N hN
  let I (l : ℤ) : ℂ := ∫ x : ℝ, g x*phase 0 (N*((l : ℝ)-b)) x
  let E (l : ℤ) : ℂ := if l∈S then 0 else I l
  have he (l : ℤ) : ‖E l‖≤w l/N^2 := by
    by_cases hs : l∈S
    · simp only [E,ite_eq_left hs,norm_zero]; exact div_nonneg (hw0 l) (sq_nonneg N)
    · simp only [E,ite_eq_right hs]
      rw [le_div_iff₀ (sq_pos_of_pos hN)]
      rw [mul_comm]
      by_cases hl : l∈J
      · exact (hdec l N hN hs).trans (by dsimp [w]; rw [ite_eq_left hl]; exact le_add_of_nonneg_right (mul_nonneg hC₀ (latticeWeight_pos l).le))
      · have hh := ht N b hN le_rfl l (int_abs_large_of_not_mem hl)
        simpa only [mul_zero,w,ite_eq_right hl,zero_add,I] using hh
  have hE : Summable E := (hw.div_const (N^2)).of_norm_bounded he
  have hIS : Summable (fun l ↦ if l∈S then I l else 0) :=
    summable_of_ne_finset_zero (s := S) (by intro l hl; simp [hl])
  have hI : Summable I := by
    convert hE.add hIS using 1
    funext l
    dsimp [E]
    split_ifs <;> simp
  have hsum : (∑' l, I l)-(∑ l∈S, I l)=∑' l, E l := by
    have ht : (∑' l, if l∈S then I l else 0)=∑ l∈S, I l := by
      rw [tsum_eq_sum (s := S) (by intro l hl; simp [hl])]
      exact Finset.sum_congr rfl (fun l hl ↦ ite_eq_left hl)
    rw [← ht]
    rw [← hI.tsum_sub hIS]
    apply tsum_congr
    intro l
    dsimp [E]; split_ifs <;> simp
  rw [show (∑' k : ℤ, g ((k : ℝ)/N)*phase 0 (-b) k)=
      (N : ℂ)*∑' l, I l by simpa only [mul_zero,zero_div,I] using poisson_chirp hg hgs hN 0 b]
  rw [← mul_assoc,one_div_mul_cancel (Complex.ofReal_ne_zero.mpr hN.ne'),one_mul,hsum]
  apply (norm_tsum_le_tsum_norm hE.norm).trans
  rw [← tsum_div_const]
  exact Summable.tsum_le_tsum he hE.norm (hw.div_const (N^2))

lemma linear_average_zero {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {A : ℝ} (hA : 0≤A)
    (hsupp : tsupport g⊆Set.Icc (-A) A) (b : ℝ)
    (hb : ∀ l : ℤ, (l : ℝ)≠b) :
    Tendsto (fun N : ℕ ↦ ‖(1/(N : ℂ))*(∑' k : ℤ,
      g ((k : ℝ)/N)*phase 0 (-b) k)‖) atTop (𝓝 0) := by
  obtain ⟨C,hC,h⟩ := linear_average_error hg hgs hA hsupp b ∅ (fun l _ ↦ hb l)
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ norm_nonneg _)) ?_
    (tendsto_const_div_atTop_nhds_zero_nat C)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : 1≤(N : ℝ) := by exact_mod_cast hN
  have hN0 : 0<(N : ℝ) := by positivity
  have hh := h N hN0
  simp only [Finset.sum_empty,sub_zero] at hh
  apply hh.trans
  exact div_le_div_of_nonneg_left hC hN0 (by nlinarith)

lemma phase_zero (x : ℝ) : phase 0 0 x=1 := by simp [phase]

lemma unphased_average {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {A : ℝ} (hA : 0≤A)
    (hsupp : tsupport g⊆Set.Icc (-A) A) :
    Tendsto (fun N : ℕ ↦ (1/(N : ℂ))*(∑' k : ℤ, g ((k : ℝ)/N)))
      atTop (𝓝 (∫ x : ℝ, g x)) := by
  obtain ⟨C,hC,h⟩ := linear_average_error hg hgs hA hsupp 0 {0} (by
    intro l hl
    exact_mod_cast (show l≠0 by simpa only [Finset.mem_singleton] using hl))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ norm_nonneg _)) ?_
    (tendsto_const_div_atTop_nhds_zero_nat C)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : 1≤(N : ℝ) := by exact_mod_cast hN
  have hN0 : 0<(N : ℝ) := by positivity
  have hh := h N hN0
  simp only [neg_zero,phase_zero,mul_one,Finset.sum_singleton,Int.cast_zero,
    sub_zero,mul_zero] at hh
  exact hh.trans (div_le_div_of_nonneg_left hC hN0 (by nlinarith))

lemma tsum_eq_sum_fin {N : ℕ} (f : ℤ → ℂ)
    (hf : ∀ k : ℤ, k<0 ∨ (N : ℤ)≤k → f k=0) :
    (∑' k : ℤ, f k)=∑ k : Fin N, f k.val := by
  classical
  let s : Finset ℤ := Finset.univ.image (fun k : Fin N ↦ (k.val : ℤ))
  have hz (k : ℤ) (hk : k∉s) : f k=0 := by
    apply hf
    by_contra he
    push Not at he
    apply hk
    have hknat : k.toNat<N := by omega
    exact Finset.mem_image.mpr ⟨⟨k.toNat,hknat⟩,Finset.mem_univ _,by
      change (k.toNat : ℤ)=k
      exact Int.toNat_of_nonneg (by omega)⟩
  rw [tsum_eq_sum hz]
  exact Finset.sum_image (by
    intro i _ j _ he
    apply Fin.ext
    change (i.val : ℤ)=(j.val : ℤ) at he
    exact_mod_cast he)

lemma sampled_support_zero {g : ℝ → ℂ} (hg : tsupport g⊆Set.Ioo (0:ℝ) 1)
    {N : ℕ} (hN : 0<N) {k : ℤ} (hk : k<0 ∨ (N : ℤ)≤k) :
    g ((k : ℝ)/N)=0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  have hh := hg hx
  have hNr : 0<(N : ℝ) := by exact_mod_cast hN
  rcases hk with hk | hk
  · have hkr : (k : ℝ)<0 := by exact_mod_cast hk
    have : (k : ℝ)/N<0 := div_neg_of_neg_of_pos hkr hNr
    linarith [hh.1]
  · have hkr : (N : ℝ)≤k := by exact_mod_cast hk
    have : 1≤(k : ℝ)/N := (le_div_iff₀ hNr).mpr (by simpa using hkr)
    linarith [hh.2]

def finiteAverage (g : ℝ → ℂ) (N : ℕ) (β b : ℝ) : ℂ :=
  (1/(N : ℂ))*∑ k : Fin N, g ((k : ℝ)/N)*phase (β/N) (-b) k

lemma finiteAverage_eq {g : ℝ → ℂ} (hg : tsupport g⊆Set.Ioo (0:ℝ) 1)
    {N : ℕ} (hN : 0<N) (β b : ℝ) :
    finiteAverage g N β b=(1/(N : ℂ))*(∑' k : ℤ, g ((k : ℝ)/N)*phase (β/N) (-b) k) := by
  rw [tsum_eq_sum_fin _ (fun k hk ↦ by rw [sampled_support_zero hg hN hk,zero_mul])]
  rfl

lemma finiteAverage_zero {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hsupp : tsupport g⊆Set.Ioo (0:ℝ) 1)
    {D β b : ℝ} (hD : 0≤D) (hbound : ∀ x, ‖g x‖≤D)
    (hfreq : β≠0 ∨ ∀ l : ℤ, (l : ℝ)≠b) :
    Tendsto (fun N : ℕ ↦ ‖finiteAverage g N β b‖) atTop (𝓝 0) := by
  have hs : tsupport g⊆Set.Icc (-1:ℝ) 1 := fun x hx ↦
    ⟨by linarith [(hsupp hx).1],(hsupp hx).2.le⟩
  have ht : Tendsto (fun N : ℕ ↦ ‖(1/(N : ℂ))*(∑' k : ℤ,
      g ((k : ℝ)/N)*phase (β/N) (-b) k)‖) atTop (𝓝 0) := by
    by_cases hβ : β=0
    · rw [hβ]
      simpa only [zero_div] using linear_average_zero hg hgs (by norm_num : (0:ℝ)≤1) hs b
        (hfreq.resolve_left (not_not.mpr hβ))
    · exact curved_average_zero hg hgs (by norm_num : (0:ℝ)≤1) hD hs hbound hβ b
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [finiteAverage_eq hsupp (by omega)]

lemma finiteAverage_diagonal {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hsupp : tsupport g⊆Set.Ioo (0:ℝ) 1) :
    Tendsto (fun N : ℕ ↦ finiteAverage g N 0 0) atTop (𝓝 (∫ x : ℝ, g x)) := by
  have hs : tsupport g⊆Set.Icc (-1:ℝ) 1 := fun x hx ↦
    ⟨by linarith [(hsupp hx).1],(hsupp hx).2.le⟩
  apply (unphased_average hg hgs (by norm_num : (0:ℝ)≤1) hs).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [finiteAverage_eq hsupp (by omega)]
  simp only [zero_div,neg_zero,phase_zero,mul_one]

lemma phase_mul (t u s v x : ℝ) : phase t u x*phase s v x=phase (t+s) (u+v) x := by
  rw [phase,phase,phase,← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma phase_conj (t u x : ℝ) : conj (phase t u x)=phase (-t) (-u) x := by
  rw [phase,phase,← Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.conj_I,Complex.conj_ofReal]
  push_cast
  ring

lemma phase_mul_conj (t u s v x : ℝ) :
    phase t u x*conj (phase s v x)=phase (t-s) (u-v) x := by
  rw [phase_conj,phase_mul]
  rfl

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI
