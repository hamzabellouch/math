import Mathlib
import OAI.Combinatorics.StripMass.PositiveAssociation

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory Filter
theorem ordered_density_covariance_exhaustion {N : ℕ} {I : Set ℝ} (l u : ℕ → ℝ)
    (hl : ∀ n, 0 < l n) (hlu : ∀ n, l n ≤ u n)
    (hm : Monotone (fun n => Icc (l n) (u n)))
    (hc : (⋃ n, Icc (l n) (u n)) = I)
    (w : Fin N → ℝ → ℝ) (hwc : ∀ i, ContinuousOn (w i) I)
    (hw : ∀ i x, x ∈ I → 0 ≤ w i x)
    (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) I))
    (hgc : ContinuousOn g (coordinateBox (Fin N) I))
    (hfm : MonotoneOn f (coordinateBox (Fin N) I))
    (hgm : MonotoneOn g (coordinateBox (Fin N) I))
    (hh : IntegrableOn (rawProductDensity N w) (orderedChamber N I))
    (hf : IntegrableOn (fun x => rawProductDensity N w x * f x) (orderedChamber N I))
    (hg : IntegrableOn (fun x => rawProductDensity N w x * g x) (orderedChamber N I))
    (hfg : IntegrableOn (fun x => rawProductDensity N w x * (f x * g x)) (orderedChamber N I)) :
    (∫ x in orderedChamber N I, rawProductDensity N w x * f x) *
      (∫ x in orderedChamber N I, rawProductDensity N w x * g x) ≤
    (∫ x in orderedChamber N I, rawProductDensity N w x) *
      (∫ x in orderedChamber N I, rawProductDensity N w x * (f x * g x)) := by
  have hsub (n : ℕ) : Icc (l n) (u n) ⊆ I := hc ▸ subset_iUnion (fun n => Icc (l n) (u n)) n
  have hB : (⋃ n, coordinateBox (Fin N) (Icc (l n) (u n))) = coordinateBox (Fin N) I := by
    rw [coordinateBox_iUnion_of_monotone hm, hc]
  have ht (F : (Fin N → ℝ) → ℝ)
      (hi : IntegrableOn (fun x => rawProductDensity N w x * F x) (orderedChamber N I)) :
      Tendsto (fun n => ∫ x in coordinateBox (Fin N) (Icc (l n) (u n)),
        orderedProductDensity N w x * F x) atTop
        (nhds (∫ x in orderedChamber N I, rawProductDensity N w x * F x)) := by
    rw [← integral_orderedProductDensity_mul]
    have hi' := (integrable_orderedProductDensity_mul_iff I w F).2 hi
    rw [← hB] at hi' ⊢
    exact tendsto_setIntegral_of_monotone (fun _ => measurableSet_coordinateBox measurableSet_Icc)
      (fun i j hij => coordinateBox_mono (hm hij)) hi'
  have hht : Tendsto (fun n => ∫ x in coordinateBox (Fin N) (Icc (l n) (u n)),
        orderedProductDensity N w x) atTop
        (nhds (∫ x in orderedChamber N I, rawProductDensity N w x)) := by
    simpa using ht (fun _ => 1) (by simpa using hh)
  exact le_of_tendsto_of_tendsto ((ht f hf).mul (ht g hg))
    (hht.mul (ht (fun x => f x * g x) hfg))
    (Eventually.of_forall fun n => ordered_density_covariance_compact (hl n) (hlu n) w
      (fun i => (hwc i).mono (hsub n)) (fun i x hx => hw i x (hsub n hx)) f g
      (hfc.mono (coordinateBox_mono (hsub n))) (hgc.mono (coordinateBox_mono (hsub n)))
      (hfm.mono (coordinateBox_mono (hsub n))) (hgm.mono (coordinateBox_mono (hsub n))))

lemma positiveWindow_mono : Monotone (fun n : ℕ => Icc (1 / (n + 1 : ℝ)) (n + 1 : ℝ)) := by
  intro n m hnm x hx
  have hnm' : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
  exact ⟨(one_div_le_one_div_of_le (by positivity) (by linarith)).trans hx.1, by linarith [hx.2]⟩

lemma positiveWindow_cover : (⋃ n : ℕ, Icc (1 / (n + 1 : ℝ)) (n + 1 : ℝ)) = Ioi (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact (by positivity : (0 : ℝ) < 1 / (n + 1 : ℝ)).trans_le hn.1
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < x from hx)
    obtain ⟨m, hm⟩ := exists_nat_gt x
    apply mem_iUnion.mpr
    refine ⟨max n m, ?_, ?_⟩
    · exact (one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right (le_max_left n m) 1)).trans hn.le
    · have h : (m : ℝ) ≤ max n m := by exact_mod_cast le_max_right n m
      linarith

 

theorem ordered_density_covariance_Ioi {N : ℕ} (w : Fin N → ℝ → ℝ)
    (hwc : ∀ i, ContinuousOn (w i) (Ioi 0))
    (hw : ∀ i x, 0 < x → 0 ≤ w i x) (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioi 0)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioi 0)))
    (hfm : MonotoneOn f (coordinateBox (Fin N) (Ioi 0)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Ioi 0)))
    (hh : IntegrableOn (rawProductDensity N w) (laguerreDomain N))
    (hf : IntegrableOn (fun x => rawProductDensity N w x * f x) (laguerreDomain N))
    (hg : IntegrableOn (fun x => rawProductDensity N w x * g x) (laguerreDomain N))
    (hfg : IntegrableOn (fun x => rawProductDensity N w x * (f x * g x)) (laguerreDomain N)) :
    (∫ x in laguerreDomain N, rawProductDensity N w x * f x) *
      (∫ x in laguerreDomain N, rawProductDensity N w x * g x) ≤
    (∫ x in laguerreDomain N, rawProductDensity N w x) *
      (∫ x in laguerreDomain N, rawProductDensity N w x * (f x * g x)) := by
  apply ordered_density_covariance_exhaustion (fun n => 1 / (n + 1 : ℝ)) (fun n => n + 1)
      (fun _ => by positivity) (fun n => ?_) positiveWindow_mono positiveWindow_cover
      w hwc hw f g hfc hgc hfm hgm hh hf hg hfg
  have hn : (1 : ℝ) ≤ n + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact le_trans (one_div_le_one_div_of_le (by norm_num) hn) (by simp)

lemma boundedWindow_mono {R : ℝ} (hR : 0 ≤ R) :
    Monotone (fun n : ℕ => Icc (R / (n + 3 : ℝ)) (R - R / (n + 3 : ℝ))) := by
  intro n m hnm x hx
  have hnm' : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
  have hd : R / (m + 3 : ℝ) ≤ R / (n + 3 : ℝ) :=
    div_le_div_of_nonneg_left hR (by positivity) (by linarith)
  exact ⟨hd.trans hx.1, by linarith [hx.2]⟩

lemma boundedWindow_cover {R : ℝ} (hR : 0 < R) :
    (⋃ n : ℕ, Icc (R / (n + 3 : ℝ)) (R - R / (n + 3 : ℝ))) = Ioo 0 R := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    have hp : 0 < R / (n + 3 : ℝ) := by positivity
    exact ⟨hp.trans_le hn.1, by linarith [hn.2]⟩
  · rintro ⟨hx, hxr⟩
    have heps : 0 < min x (R - x) / R := div_pos (lt_min hx (sub_pos.mpr hxr)) hR
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt heps
    have hsmall : R / (n + 3 : ℝ) < min x (R - x) := by
      have hnd : R / (n + 3 : ℝ) ≤ R / (n + 1 : ℝ) :=
        div_le_div_of_nonneg_left hR.le (by positivity) (by norm_num)
      rw [lt_div_iff₀ hR] at hn
      have hn' : R / (n + 1 : ℝ) < min x (R - x) := by simpa [div_eq_mul_inv, mul_comm] using hn
      exact hnd.trans_lt hn'
    exact mem_iUnion.mpr ⟨n, (hsmall.trans_le (min_le_left _ _)).le,
      by have h := hsmall.trans_le (min_le_right _ _); linarith⟩

 

theorem ordered_density_covariance_Ioo {N : ℕ} {R : ℝ} (hR : 0 < R)
    (w : Fin N → ℝ → ℝ) (hwc : ∀ i, ContinuousOn (w i) (Ioo 0 R))
    (hw : ∀ i x, x ∈ Ioo 0 R → 0 ≤ w i x) (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioo 0 R)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioo 0 R)))
    (hfm : MonotoneOn f (coordinateBox (Fin N) (Ioo 0 R)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Ioo 0 R)))
    (hh : IntegrableOn (rawProductDensity N w) (orderedChamber N (Ioo 0 R)))
    (hf : IntegrableOn (fun x => rawProductDensity N w x * f x) (orderedChamber N (Ioo 0 R)))
    (hg : IntegrableOn (fun x => rawProductDensity N w x * g x) (orderedChamber N (Ioo 0 R)))
    (hfg : IntegrableOn (fun x => rawProductDensity N w x * (f x * g x)) (orderedChamber N (Ioo 0 R))) :
    (∫ x in orderedChamber N (Ioo 0 R), rawProductDensity N w x * f x) *
      (∫ x in orderedChamber N (Ioo 0 R), rawProductDensity N w x * g x) ≤
    (∫ x in orderedChamber N (Ioo 0 R), rawProductDensity N w x) *
      (∫ x in orderedChamber N (Ioo 0 R), rawProductDensity N w x * (f x * g x)) := by
  apply ordered_density_covariance_exhaustion (fun n => R / (n + 3 : ℝ))
      (fun n => R - R / (n + 3 : ℝ)) (fun _ => by positivity) (fun n => ?_)
      (boundedWindow_mono hR.le) (boundedWindow_cover hR)
      w hwc hw f g hfc hgc hfm hgm hh hf hg hfg
  have hd : R / (n + 3 : ℝ) ≤ R / 2 :=
    div_le_div_of_nonneg_left hR.le (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  linarith

lemma weighted_covariance_normalize {Af Ag Afg Z : ℝ} (hZ : 0 < Z)
    (h : Af * Ag ≤ Z * Afg) : (Af / Z) * (Ag / Z) ≤ Afg / Z := by
  apply (le_div_iff₀ hZ).2
  calc
    (Af / Z * (Ag / Z)) * Z = (Af * Ag) / Z := by field_simp
    _ ≤ Afg := (div_le_iff₀ hZ).2 (by simpa [mul_comm] using h)

lemma continuousOn_laguerreWeight (a : ℝ) : ContinuousOn (laguerreWeight a) (Ioi 0) := by
  unfold laguerreWeight
  exact (continuousOn_id.rpow_const (fun _ hx => Or.inl (ne_of_gt hx))).mul
    ((Real.continuous_exp.comp continuous_neg).continuousOn)

 

theorem integrable_laguerreLaw_iff {N : ℕ} {a : ℝ} (ha : 0 < a)
    {f : (Fin N → ℝ) → ℝ} :
    Integrable f (laguerreLaw N a) ↔
      IntegrableOn (fun r => laguerreDensity N a r * f r) (laguerreDomain N) := by
  rw [laguerreLaw, integrable_smul_measure (by simp)
    (by simpa using laguerreNormalizer_pos N ha),
    integrable_withDensity_iff_integrable_smul' (measurable_laguerreDensity N a).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  simp [smul_eq_mul, ENNReal.toReal_ofReal (laguerreDensity_pos a hr).le]

 

theorem laguerreLaw_covariance {N : ℕ} {a : ℝ} (ha : 0 < a)
    (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioi 0)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioi 0)))
    (hfm : MonotoneOn f (coordinateBox (Fin N) (Ioi 0)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Ioi 0)))
    (hf : Integrable f (laguerreLaw N a)) (hg : Integrable g (laguerreLaw N a))
    (hfg : Integrable (fun r => f r * g r) (laguerreLaw N a)) :
    (∫ r, f r ∂laguerreLaw N a) * (∫ r, g r ∂laguerreLaw N a) ≤
      ∫ r, f r * g r ∂laguerreLaw N a := by
  simp only [integral_laguerreLaw N ha, laguerreExpectation]
  apply weighted_covariance_normalize (laguerreNormalizer_pos N ha)
  have h := ordered_density_covariance_Ioi (fun _ : Fin N => laguerreWeight a)
    (fun _ => continuousOn_laguerreWeight a) (fun _ _ hx => (laguerreWeight_pos a hx).le)
    f g hfc hgc hfm hgm (integrableOn_laguerreDensity N ha)
    ((integrable_laguerreLaw_iff ha).1 hf) ((integrable_laguerreLaw_iff ha).1 hg)
    ((integrable_laguerreLaw_iff ha).1 hfg)
  simpa only [rawProductDensity, laguerreNormalizer, laguerreDensity, mul_comm] using h

 

theorem laguerreLaw_reverse_covariance {N : ℕ} {a : ℝ} (ha : 0 < a)
    (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioi 0)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioi 0)))
    (hfm : AntitoneOn f (coordinateBox (Fin N) (Ioi 0)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Ioi 0)))
    (hf : Integrable f (laguerreLaw N a)) (hg : Integrable g (laguerreLaw N a))
    (hfg : Integrable (fun r => f r * g r) (laguerreLaw N a)) :
    (∫ r, f r * g r ∂laguerreLaw N a) ≤
      (∫ r, f r ∂laguerreLaw N a) * (∫ r, g r ∂laguerreLaw N a) := by
  have h := laguerreLaw_covariance ha (fun r => -f r) g hfc.neg hgc
    (fun _ hx _ hy hxy => neg_le_neg (hfm hx hy hxy)) hgm hf.neg hg (by simpa using hfg.neg)
  simpa only [neg_mul, integral_neg, neg_le_neg_iff] using h

 

lemma continuousOn_omega_Ioi : ContinuousOn omega (Ioi 0) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  apply ContinuousAt.continuousWithinAt
  unfold omega
  fun_prop (disch := positivity)

 
theorem expectation_covariance {N : ℕ} (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioo 0 1)))
    (hfm : MonotoneOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Ioo 0 1)))
    (hf : IntegrableOn (fun y => f y * density N y) (orderedDomain N))
    (hg : IntegrableOn (fun y => g y * density N y) (orderedDomain N))
    (hfg : IntegrableOn (fun y => (f y * g y) * density N y) (orderedDomain N)) :
    expectation N f * expectation N g ≤ expectation N (fun y => f y * g y) := by
  unfold expectation
  apply weighted_covariance_normalize (normalizer_pos N)
  have h := ordered_density_covariance_Ioo (by norm_num : (0 : ℝ) < 1)
    (fun _ : Fin N => omega) (fun _ => continuousOn_omega_Ioi.mono (fun _ hx => hx.1))
    (fun _ x _ => omega_nonneg x) f g hfc hgc hfm hgm (integrableOn_density N)
    (by simpa only [rawProductDensity, density, orderedChamber, orderedDomain, mul_comm] using hf)
    (by simpa only [rawProductDensity, density, orderedChamber, orderedDomain, mul_comm] using hg)
    (by simpa only [rawProductDensity, density, orderedChamber, orderedDomain, mul_comm] using hfg)
  simpa only [rawProductDensity, density, orderedChamber, orderedDomain, normalizer, mul_comm] using h

lemma expectation_neg (N : ℕ) (f : (Fin N → ℝ) → ℝ) :
    expectation N (fun y => -f y) = -expectation N f := by
  simp only [expectation, neg_mul, integral_neg, neg_div]

 

theorem expectation_reverse_covariance {N : ℕ} (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioo 0 1)))
    (hfm : AntitoneOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Ioo 0 1)))
    (hf : IntegrableOn (fun y => f y * density N y) (orderedDomain N))
    (hg : IntegrableOn (fun y => g y * density N y) (orderedDomain N))
    (hfg : IntegrableOn (fun y => (f y * g y) * density N y) (orderedDomain N)) :
    expectation N (fun y => f y * g y) ≤ expectation N f * expectation N g := by
  have h := expectation_covariance (fun y => -f y) g hfc.neg hgc
    (fun _ hx _ hy hxy => neg_le_neg (hfm hx hy hxy)) hgm
    (by simpa using hf.neg) hg (by simpa using hfg.neg)
  simpa only [neg_mul, expectation_neg, neg_le_neg_iff] using h

 

theorem laguerreLaw_increasing_tilt {N : ℕ} {a : ℝ} (ha : 0 < a)
    (f L : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioi 0)))
    (hLc : ContinuousOn L (coordinateBox (Fin N) (Ioi 0)))
    (hfm : AntitoneOn f (coordinateBox (Fin N) (Ioi 0)))
    (hLm : MonotoneOn L (coordinateBox (Fin N) (Ioi 0)))
    (hf : Integrable f (laguerreLaw N a)) (hL : Integrable L (laguerreLaw N a))
    (hfL : Integrable (fun r => f r * L r) (laguerreLaw N a))
    (hLpos : 0 < ∫ r, L r ∂laguerreLaw N a) :
    (∫ r, f r * L r ∂laguerreLaw N a) / (∫ r, L r ∂laguerreLaw N a) ≤
      ∫ r, f r ∂laguerreLaw N a := by
  exact (div_le_iff₀ hLpos).2 (laguerreLaw_reverse_covariance ha f L hfc hLc hfm hLm hf hL hfL)

 
theorem laguerreLaw_covariance_antitone {N : ℕ} {a : ℝ} (ha : 0 < a)
    (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioi 0)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioi 0)))
    (hfm : AntitoneOn f (coordinateBox (Fin N) (Ioi 0)))
    (hgm : AntitoneOn g (coordinateBox (Fin N) (Ioi 0)))
    (hf : Integrable f (laguerreLaw N a)) (hg : Integrable g (laguerreLaw N a))
    (hfg : Integrable (fun r => f r * g r) (laguerreLaw N a)) :
    (∫ r, f r ∂laguerreLaw N a) * (∫ r, g r ∂laguerreLaw N a) ≤
      ∫ r, f r * g r ∂laguerreLaw N a := by
  have h := laguerreLaw_covariance ha (fun r => -f r) (fun r => -g r) hfc.neg hgc.neg
    (fun _ hx _ hy hxy => neg_le_neg (hfm hx hy hxy))
    (fun _ hx _ hy hxy => neg_le_neg (hgm hx hy hxy)) hf.neg hg.neg (by simpa using hfg)
  simpa only [integral_neg, neg_mul_neg] using h



 
def cutoffRamp (n : ℕ) (R x : ℝ) : ℝ := min 1 (max 0 ((n + 1 : ℝ) * (R - x)))

lemma cutoffRamp_bounds (n : ℕ) (R x : ℝ) :
    0 ≤ cutoffRamp n R x ∧ cutoffRamp n R x ≤ 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

lemma continuous_cutoffRamp (n : ℕ) (R : ℝ) : Continuous (cutoffRamp n R) := by
  unfold cutoffRamp
  fun_prop

lemma antitone_cutoffRamp (n : ℕ) (R : ℝ) : Antitone (cutoffRamp n R) := by
  intro x y hxy
  exact min_le_min_left 1 (max_le_max_left 0
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hxy R) (by positivity)))

lemma cutoffRamp_tendsto (R x : ℝ) :
    Tendsto (fun n => cutoffRamp n R x) atTop (nhds (if x < R then 1 else 0)) := by
  split_ifs with hx
  · obtain ⟨b, hb⟩ := exists_nat_gt (1 / (R - x))
    have hb' : 1 < (b : ℝ) * (R - x) := (div_lt_iff₀ (sub_pos.mpr hx)).mp hb
    have he : (fun n => cutoffRamp n R x) =ᶠ[atTop] (fun _ => 1) := by
      filter_upwards [eventually_ge_atTop b] with n hn
      have hn' : (b : ℝ) ≤ n := Nat.cast_le.mpr hn
      have hm : 1 ≤ (n + 1 : ℝ) * (R - x) := by nlinarith
      exact min_eq_left (hm.trans (le_max_right _ _))
    exact (tendsto_congr' he).2 tendsto_const_nhds
  · have he : (fun n => cutoffRamp n R x) = (fun _ => 0) := by
      funext n
      have hm : (n + 1 : ℝ) * (R - x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr (le_of_not_gt hx))
      simp only [cutoffRamp, max_eq_left hm, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    rw [he]
    exact tendsto_const_nhds

 

def cutoffEvent (N : ℕ) (R : ℝ) : Set (Fin N → ℝ) := coordinateBox (Fin N) (Iio R)

def cutoffProduct (N n : ℕ) (R : ℝ) (r : Fin N → ℝ) : ℝ :=
  ∏ i, cutoffRamp n R (r i)

lemma measurableSet_cutoffEvent (N : ℕ) (R : ℝ) : MeasurableSet (cutoffEvent N R) :=
  measurableSet_coordinateBox measurableSet_Iio

lemma cutoffProduct_bounds (N n : ℕ) (R : ℝ) (r : Fin N → ℝ) :
    0 ≤ cutoffProduct N n R r ∧ cutoffProduct N n R r ≤ 1 := by
  refine ⟨Finset.prod_nonneg (fun i _ => (cutoffRamp_bounds n R (r i)).1), ?_⟩
  exact Finset.prod_le_one₀ (fun i _ => (cutoffRamp_bounds n R (r i)).1)
    (fun i _ => (cutoffRamp_bounds n R (r i)).2)

lemma cutoffProduct_norm_le (N n : ℕ) (R : ℝ) (r : Fin N → ℝ) :
    ‖cutoffProduct N n R r‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (cutoffProduct_bounds N n R r).1]
  exact (cutoffProduct_bounds N n R r).2

lemma continuous_cutoffProduct (N n : ℕ) (R : ℝ) : Continuous (cutoffProduct N n R) := by
  unfold cutoffProduct
  exact continuous_finsetProd _ fun i _ => (continuous_cutoffRamp n R).comp (continuous_apply i)

lemma antitone_cutoffProduct (N n : ℕ) (R : ℝ) : Antitone (cutoffProduct N n R) := by
  intro r s hrs
  exact Finset.prod_le_prod₀ (fun i _ => (cutoffRamp_bounds n R (s i)).1)
    (fun i _ => antitone_cutoffRamp n R (hrs i))

lemma cutoffProduct_tendsto (N : ℕ) (R : ℝ) (r : Fin N → ℝ) :
    Tendsto (fun n => cutoffProduct N n R r) atTop
      (nhds ((cutoffEvent N R).indicator (fun _ => (1 : ℝ)) r)) := by
  classical
  have he : (∏ i : Fin N, if r i < R then (1 : ℝ) else 0) =
      (cutoffEvent N R).indicator (fun _ => (1 : ℝ)) r := by
    by_cases hr : ∀ i, r i < R
    · simp [cutoffEvent, coordinateBox, hr]
    · have hr' : r ∉ cutoffEvent N R := hr
      rw [indicator_of_notMem hr']
      obtain ⟨i, hi⟩ := not_forall.mp hr
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  simpa only [cutoffProduct, he] using
    tendsto_finsetProd Finset.univ (fun i _ => cutoffRamp_tendsto R (r i))

lemma cutoffProduct_integrable {N : ℕ} (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ]
    (n : ℕ) (R : ℝ) : Integrable (cutoffProduct N n R) μ :=
  (integrable_const (1 : ℝ)).mono' (continuous_cutoffProduct N n R).aestronglyMeasurable
    (Eventually.of_forall (cutoffProduct_norm_le N n R))

lemma cutoffProduct_integral_tendsto {N : ℕ} (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ]
    (R : ℝ) : Tendsto (fun n => ∫ r, cutoffProduct N n R r ∂μ) atTop
      (nhds (μ.real (cutoffEvent N R))) := by
  rw [← integral_indicator_one (measurableSet_cutoffEvent N R)]
  exact tendsto_integral_of_dominated_convergence (fun _ => 1)
    (fun n => (continuous_cutoffProduct N n R).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall (cutoffProduct_norm_le N n R))
    (Eventually.of_forall (cutoffProduct_tendsto N R))

lemma cutoffProduct_weighted_tendsto {N : ℕ} (μ : Measure (Fin N → ℝ)) (R : ℝ)
    (f : (Fin N → ℝ) → ℝ) (hf : Integrable f μ) :
    Tendsto (fun n => ∫ r, f r * cutoffProduct N n R r ∂μ) atTop
      (nhds (∫ r in cutoffEvent N R, f r ∂μ)) := by
  have he : (fun r => f r * (cutoffEvent N R).indicator (fun _ => (1 : ℝ)) r) =
      (cutoffEvent N R).indicator f := by
    funext r
    by_cases hr : r ∈ cutoffEvent N R <;> simp [hr]
  have ht := tendsto_integral_of_dominated_convergence (μ := μ) (fun r => ‖f r‖)
    (fun n => hf.aestronglyMeasurable.mul (continuous_cutoffProduct N n R).aestronglyMeasurable) hf.norm
    (fun n => Eventually.of_forall fun r =>
      calc ‖f r * cutoffProduct N n R r‖ = ‖f r‖ * ‖cutoffProduct N n R r‖ := norm_mul _ _
           _ ≤ ‖f r‖ * 1 := mul_le_mul_of_nonneg_left (cutoffProduct_norm_le N n R r) (norm_nonneg _)
           _ = ‖f r‖ := mul_one _)
    (Eventually.of_forall fun r => tendsto_const_nhds.mul (cutoffProduct_tendsto N R r))
  simpa only [Pi.mul_apply, he, integral_indicator (measurableSet_cutoffEvent N R)] using ht

 

theorem laguerreLaw_cutoff_covariance {N : ℕ} {a : ℝ} (ha : 0 < a) (R : ℝ)
    (f : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioi 0)))
    (hfm : AntitoneOn f (coordinateBox (Fin N) (Ioi 0)))
    (hf : Integrable f (laguerreLaw N a)) :
    (∫ r, f r ∂laguerreLaw N a) * (laguerreLaw N a).real (cutoffEvent N R) ≤
      ∫ r in cutoffEvent N R, f r ∂laguerreLaw N a := by
  let := laguerreLaw_isProbabilityMeasure N ha
  apply le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul (cutoffProduct_integral_tendsto (laguerreLaw N a) R))
    (cutoffProduct_weighted_tendsto (laguerreLaw N a) R f hf)
  apply Eventually.of_forall
  intro n
  exact laguerreLaw_covariance_antitone ha f (cutoffProduct N n R) hfc
    (continuous_cutoffProduct N n R).continuousOn hfm
    ((antitone_cutoffProduct N n R).antitoneOn _) hf (cutoffProduct_integrable _ n R)
    (hf.mul_bdd (continuous_cutoffProduct N n R).aestronglyMeasurable
      (Eventually.of_forall (cutoffProduct_norm_le N n R)))

end
end CriticalStrip

end OAI
