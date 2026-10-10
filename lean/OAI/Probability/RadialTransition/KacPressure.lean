import OAI.Probability.RadialTransition.KacDeletion

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def kernelUpperError (q : ℕ) (R : ℝ) : ℝ := 10000*(bumpLip:ℝ)*q/R

def kacSeries (φ : Potential) (q : ℕ) (R t a β h : ℝ) : ℕ → ℝ :=
  quadraticTerm φ ((q:ℝ)/4) β (t*h) (β*(t*a)*(1+kernelUpperError q R)/2)

lemma kacPartition_ge_one {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {m q : ℕ} (hq : 0 < q) {R t a β h : ℝ} (hβ : 0 ≤ β) (hR : (q:ℝ)/4 ≤ R) (hta : 0 ≤ t*a)
    (hs : Summable (kacSeries φ q R t a β h)) :
    1 ≤ boltzmannPartition (macroMeasure m q (t*h)) (fun x => β*macroKacEnergy φ m q R (t*a) x) := by
  have hi := integrable_macroKac (m := m) hφ hb hq hβ hR hta hs
  have hh := macroKac_partition_lower hφ hb hq hβ hR hta hi 0
  simpa only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div, Real.exp_zero,
    partition_zero, one_mul, one_pow] using hh

lemma deletedKacPressure_upper {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {m q : ℕ} (hm : 0 < m) (hq : 0 < q) {R t a β h : ℝ} (ht : 0 < t)
    (hβ : 0 ≤ β) (hR : (q:ℝ)/4 ≤ R) (ha : 0 ≤ a)
    (hs : Summable (kacSeries φ q R t a β h)) :
    deletedKacPressure φ m q R t a β h ≤ Real.log (∑' n, kacSeries φ q R t a β h n)/(t*((q:ℝ)/4)^3) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hta : 0 ≤ t*a := mul_nonneg ht.le ha
  have hpos := (zero_lt_one.trans_le (kacPartition_ge_one hφ hb hq hβ hR hta hs (m := m)))
  have hh := Real.log_le_log hpos (macroKac_partition_upper (m := m) hφ hb hq hβ hR hta hs)
  rw [Real.log_pow] at hh
  change _ ≤ ((m^3:ℕ):ℝ)*Real.log (∑' n, kacSeries φ q R t a β h n) at hh
  have hden : 0 < t*((m:ℝ)*q/4)^3 := by positivity
  unfold deletedKacPressure
  apply (div_le_iff₀ hden).mpr
  convert hh using 1
  first
  | rfl
  | simp only [Nat.cast_pow]; field_simp [ht.ne', hq0.ne']

lemma deletedKacPressure_sector_lower {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {m q : ℕ} (hm : 0 < m) (hq : 0 < q) {R t a β h : ℝ} (ht : 0 < t)
    (hβ : 0 ≤ β) (hR : (q:ℝ)/4 ≤ R) (ha : 0 ≤ a)
    (hs : Summable (kacSeries φ q R t a β h)) (n : ℕ) :
    h*((n:ℝ)/((q:ℝ)/4)^3)-finiteCanonical φ t ((q:ℝ)/4) n β+
      β*a/2*((kernelInterior m q R).card/(m:ℝ)^3)*(1-kernelRowError q R)*((n:ℝ)/((q:ℝ)/4)^3)^2 ≤
      deletedKacPressure φ m q R t a β h := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hs0 : 0 < (q:ℝ)/4 := by positivity
  have hta : 0 ≤ t*a := mul_nonneg ht.le ha
  have hi := integrable_macroKac (m := m) hφ hb hq hβ hR hta hs
  have hpos : 0 < Real.exp (t*h*n)*partition φ ((q:ℝ)/4) n β :=
    mul_pos (Real.exp_pos _) (partition_pos hφ hb hs0 n β)
  have hh := Real.log_le_log (mul_pos (Real.exp_pos _) (pow_pos hpos _))
    (macroKac_partition_lower hφ hb hq hβ hR hta hi n)
  rw [Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hpos.ne'), Real.log_exp, Real.log_pow,
    Real.log_mul (Real.exp_ne_zero _) (partition_pos hφ hb hs0 n β).ne', Real.log_exp] at hh
  unfold deletedKacPressure
  apply (le_div_iff₀ (by positivity : 0 < t*((m:ℝ)*q/4)^3)).mpr
  convert hh using 1
  first
  | rfl
  | unfold finiteCanonical
    simp only [Nat.cast_pow]
    field_simp [ht.ne', hq0.ne', hm0.ne']
    ring

lemma kernelInterior_fraction {m q : ℕ} (hm : 0 < m) (R : ℝ) :
    (0:ℝ) ≤ (kernelInterior m q R).card/(m:ℝ)^3 ∧ (kernelInterior m q R).card/(m:ℝ)^3 ≤ 1 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  refine ⟨by positivity, (div_le_one (by positivity)).mpr ?_⟩
  have hc := Finset.card_le_card (Finset.subset_univ (kernelInterior m q R))
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using (by exact_mod_cast hc : ((kernelInterior m q R).card:ℝ) ≤ (Fintype.card (GridIndex m):ℝ))

lemma deletedKacPressure_branch_lower {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {m q : ℕ} (hm : 0 < m) (hq : 0 < q) {B R t a β h D u : ℝ}
    (hst : StableWith φ B) (ht : 0 < t) (hq1 : 1 ≤ (q:ℝ)/4)
    (hβ : 0 ≤ β) (hR : (q:ℝ)/4 ≤ R) (ha : 0 ≤ a)
    (hs : Summable (kacSeries φ q R t a β h)) (hD : Real.exp (β*B+t*(h+β*a*u)+1) ≤ D) :
    finiteGrandPressure φ t ((q:ℝ)/4) β (h+β*a*u)-β*a/2*u^2 ≤
      deletedKacPressure φ m q R t a β h+
        β*a/2*(1-((kernelInterior m q R).card/(m:ℝ)^3)*(1-kernelRowError q R))*D^2+
        Real.log ((D+2)*((q:ℝ)/4)^3)/(t*((q:ℝ)/4)^3) := by
  obtain ⟨n, hn, hmax⟩ := finiteGrandPressure_max_term hφ hb hst ht hq1 hβ hD
  have hsector := deletedKacPressure_sector_lower hφ hb hm hq ht hβ hR ha hs n
  let d := (n:ℝ)/((q:ℝ)/4)^3
  let v := ((kernelInterior m q R).card:ℝ)/(m:ℝ)^3
  have hv := kernelInterior_fraction (q := q) hm R
  have he := kernelRowError_nonneg q (le_trans (by linarith) hR)
  have hv' : 0 ≤ 1-v*(1-kernelRowError q R) := by dsimp only [v]; nlinarith [mul_nonneg hv.1 he]
  have hb0 : 0 ≤ β*a/2 := by positivity
  have hD0 : 0 ≤ D := hn.1.trans hn.2
  have hsq : d^2 ≤ D^2 := (sq_le_sq₀ hn.1 hD0).mpr hn.2
  have herror := mul_le_mul_of_nonneg_left hsq (mul_nonneg hb0 hv')
  have hdiff := mul_nonneg hb0 (sq_nonneg (u-d))
  dsimp only [d, v] at herror hdiff
  nlinarith

end RadialTransition
end

end OAI
