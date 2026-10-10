import OAI.MathematicalPhysics.Boltzmann.Branching.PhaseDecompositionNorm
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Jets.JetFamilyBounds

namespace OAI

section

/-! # The attained cap ratio and its uniform perturbation bound -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.Cap

def peak (T δ : ℝ) (z : ℝ → ℝ) : ℝ := sSup ((fun t => z t/(t+δ)) '' Icc 0 T)

theorem peak_eq_of_max {T δ t : ℝ} {z : ℝ → ℝ} (ht : t ∈ Icc 0 T)
    (hmax : ∀ s ∈ Icc 0 T, z s/(s+δ) ≤ z t/(t+δ)) :
    peak T δ z = z t/(t+δ) := by
  have hmem : z t/(t+δ) ∈ (fun t => z t/(t+δ)) '' Icc 0 T := mem_image_of_mem _ ht
  have hbd : BddAbove ((fun t => z t/(t+δ)) '' Icc 0 T) :=
    ⟨z t/(t+δ),by rintro y ⟨s,hs,rfl⟩; exact hmax s hs⟩
  exact le_antisymm (csSup_le ⟨_,hmem⟩ (by rintro y ⟨s,hs,rfl⟩; exact hmax s hs)) (le_csSup hbd hmem)

theorem peak_attained {T δ : ℝ} {z : ℝ → ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hz : ContinuousOn z (Icc 0 T)) :
    ∃ t ∈ Icc 0 T, peak T δ z = z t/(t+δ) ∧ ∀ s ∈ Icc 0 T, z s/(s+δ) ≤ peak T δ z := by
  have hc : ContinuousOn (fun t => z t/(t+δ)) (Icc 0 T) :=
    hz.div (by fun_prop) (fun t ht => ne_of_gt (by linarith [ht.1]))
  obtain ⟨t,ht,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT) hc
  have he := peak_eq_of_max ht hm
  exact ⟨t,ht,he,fun s hs => (hm hs).trans_eq he.symm⟩

theorem peak_difference {T δ E : ℝ} {z w : ℝ → ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hE : 0 ≤ E) (hz : ContinuousOn z (Icc 0 T)) (hw : ContinuousOn w (Icc 0 T))
    (hzw : ∀ t ∈ Icc 0 T, |z t-w t| ≤ E) : |peak T δ z-peak T δ w| ≤ E/δ := by
  obtain ⟨s,hs,hsp,hsm⟩ := peak_attained hT hδ hz
  obtain ⟨t,ht,htp,htm⟩ := peak_attained hT hδ hw
  have hrat (r : ℝ) (hr : r ∈ Icc 0 T) : |z r/(r+δ)-w r/(r+δ)| ≤ E/δ := by
    rw [← sub_div,abs_div,abs_of_pos (by linarith [hr.1] : 0 < r+δ)]
    exact (div_le_div_of_nonneg_right (hzw r hr) (by linarith [hr.1])).trans
      (div_le_div_of_nonneg_left hE hδ (by linarith [hr.1]))
  apply abs_sub_le_iff.mpr
  constructor
  · have h := (abs_sub_le_iff.mp (hrat s hs)).1
    rw [hsp]
    linarith [htm s hs]
  · have h := (abs_sub_le_iff.mp (hrat t ht)).2
    rw [htp]
    linarith [hsm t ht]

end BoltzmannNonuniqueness.Cap

end

end

section

/-! # The hot cap cancels the smallest scale in the source majorant -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.ZeroProfile

theorem source_le_cap {M C B δ t z : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hδ : 0 < δ) (ht : 0 ≤ t) (hz : 0 ≤ z) (hcap : z ≤ t+δ) (m : ℕ) :
    source M C B δ m t z ≤ M+C*(t+δ)^2+B*t^m := by
  have hd : 0 < t+δ := by linarith
  have hl : M/(t+δ)*z ≤ M := by
    calc
      _ ≤ M/(t+δ)*(t+δ) := mul_le_mul_of_nonneg_left hcap (div_nonneg hM hd.le)
      _ = M := div_mul_cancel₀ M hd.ne'
  have hq : C*z^2 ≤ C*(t+δ)^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hcap 2) hC
  exact add_le_add (add_le_add hl hq) le_rfl

theorem source_cap_dilation {M C B r t l δ : ℝ} {m : ℕ}
    (hδ : δ = r*l) :
    M+C*(r*t+δ)^2+B*(r*t)^m = M+C*r^2*(t+l)^2+B*r^m*t^m := by
  rw [hδ,mul_pow]
  ring

theorem source_cap_error_tendsto {C B t : ℝ} {r l : ℕ → ℝ} {l₀ : ℝ} {m : ℕ}
    (hr : Tendsto r atTop (𝓝 0)) (hl : Tendsto l atTop (𝓝 l₀)) (hm : 0 < m) :
    Tendsto (fun n => C*(r n)^2*(t+l n)^2+B*(r n)^m*t^m) atTop (𝓝 0) := by
  have hleft := ((hr.pow 2).const_mul C).mul (((tendsto_const_nhds (x := t)).add hl).pow 2)
  have hright := ((hr.pow m).const_mul B).mul_const (t^m)
  simpa only [zero_pow (by omega : 2 ≠ 0),zero_pow (Nat.ne_zero_of_lt hm),
    mul_zero,zero_mul,add_zero] using hleft.add hright

end BoltzmannNonuniqueness.ZeroProfile

end

end

section

/-! # Relative entropy convergence of the actual cap-shooting initial data -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem periodicInitial_entropy_tendsto {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64) (hα : 0 ≤ α) (hαmax : α ≤ 1/4)
    (hq : 1 < q) (hqmax : q < 2)
    {ell : ℕ → ℝ} (hell : ∀ n, ell n ∈ Set.Icc (0:ℝ) 2) :
    Tendsto (fun n => relativeEntropy (periodicInitial s₀ η K α γ d₀ q n (ell n)))
      atTop (𝓝 (relativeEntropy (JetPeriodicDatum.datum s₀ η K α γ d₀))) := by
  let δ : ℕ → ℝ := fun n => DatumBounds.scale s₀ η (n+1)
  let C : ℝ := 2*(HotSeedProfile.bound/HotSeedProfile.normLower q)
  have hC : 0 ≤ C := mul_nonneg (by norm_num)
    (div_nonneg HotSeedProfile.bound_pos.le (HotSeedProfile.normLower_pos q).le)
  have hδ (n : ℕ) : 0 < δ n := DatumBounds.scale_pos hs₀ _
  have hδmax (n : ℕ) : δ n ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (n+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    exact h.trans (by linarith)
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    (DatumBounds.scale_tendsto_zero s₀ hη).comp (tendsto_add_atTop_nat 1)
  let a : ℕ → Density := fun n => JetPeriodicDatum.truncated s₀ η K α γ d₀ n
  let b : ℕ → Density := fun n z => ell n*HotSeedProfile.periodicDensity q (δ n) z
  have ha : ∀ n z, 0 ≤ a n z ∧ a n z ≤ JetPeriodicDatum.datum s₀ η K α γ d₀ z := by
    intro n z
    have hn := JetDatumMoments.datum_nonneg hs₀ hK.le hd₀.le η α γ
      (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z))
    rcases JetTruncation.truncated_eq_or_zero hs₀ hsmax hη hηmax K α γ d₀ n
      (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z)) with he | he
    · change 0 ≤ JetTruncation.truncated s₀ η K α γ d₀ n
        (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z)) ∧
        JetTruncation.truncated s₀ η K α γ d₀ n
          (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z)) ≤
        JetDatum.datum s₀ η K α γ d₀ (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z))
      rw [he]
      exact ⟨hn,le_rfl⟩
    · change 0 ≤ JetTruncation.truncated s₀ η K α γ d₀ n
        (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z)) ∧
        JetTruncation.truncated s₀ η K α γ d₀ n
          (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z)) ≤
        JetDatum.datum s₀ η K α γ d₀ (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z))
      rw [he]
      exact ⟨le_rfl,hn⟩
  have hb (n : ℕ) (z : Phase) : 0 ≤ b n z ∧ b n z ≤ C*δ n*H q z.2 := by
    refine ⟨mul_nonneg (hell n).1 (HotSeedProfile.periodicDensity_nonneg (hδ n) (hδmax n) z),?_⟩
    have h := mul_le_mul (hell n).2 (HotSeedProfile.periodicDensity_bound (by linarith : 0 ≤ q)
      (hδ n) (hδmax n) z) (HotSeedProfile.periodicDensity_nonneg (hδ n) (hδmax n) z) (by norm_num : (0:ℝ) ≤ 2)
    exact h.trans_eq (by dsimp [C]; ring)
  obtain ⟨p,hp,hpi⟩ := exists_integrable_rpow_H hq hqmax
  have hlim := entropy_truncation_perturbation_tendsto hqmax hC hp hpi
    (JetPeriodicDatum.finiteEntropy hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα hαmax)
    (a := a) (b := b)
    (fun n => JetPeriodicDatum.measurable_pullback (JetTruncation.truncated_measurable s₀ η K α γ d₀ n))
    (fun n => (HotSeedProfile.periodicDensity_measurable q (δ n)).const_mul (ell n)) ha
    (fun n z => ⟨(hb n z).1, (hb n z).2.trans (by
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hC (hδmax n)) (H_nonneg q z.2))⟩)
    (fun z => JetTruncation.truncated_tendsto hs₀ hsmax hη hηmax K α γ d₀
      (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z)))
    (fun z => by
      apply squeeze_zero (fun n => (hb n z).1) (fun n => (hb n z).2)
      simpa only [mul_zero,zero_mul] using (hδlim.const_mul C).mul_const (H q z.2))
  convert hlim using 1
  funext n
  unfold relativeEntropy
  apply integral_congr_ae
  filter_upwards [] with z
  rw [periodicInitial_eq hs₀ hsmax hη hηmax]
  exact (scalarRelativeEntropy_eq (maxwellian_pos z.2) (a n z+b n z)).symm

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Scalar scales at an attained cap time -/

noncomputable section

open Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Cap

theorem dilation_radius_pos {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) : 0 < t+δ :=
  add_pos_of_nonneg_of_pos ht hδ

theorem cold_fraction_mem {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) :
    δ/(t+δ) ∈ Icc (0:ℝ) 1 :=
  ⟨div_nonneg hδ.le (dilation_radius_pos ht hδ).le,
    (div_le_one (dilation_radius_pos ht hδ)).mpr (by linarith)⟩

theorem normalized_cap_time {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) :
    t/(t+δ) = 1-δ/(t+δ) := by
  have hne := (dilation_radius_pos ht hδ).ne'
  field_simp
  ring

theorem normalized_horizon_lower {T t δ : ℝ} (hT : 0 < T) (ht : t ∈ Icc 0 T)
    (hδ : 0 < δ) :
    1/(1+δ/T) ≤ T/(t+δ) := by
  have he : 1/(1+δ/T) = T/(T+δ) := by field_simp
  rw [he]
  exact div_le_div_of_nonneg_left hT.le (dilation_radius_pos ht.1 hδ) (by linarith [ht.2])

theorem terminal_scale_tendsto_zero {T δ : ℕ → ℝ} (hT : ∀ n, 0 < T n)
    (hTlim : Tendsto T atTop (𝓝 0))
    (hratio : Tendsto (fun n => δ n/T n) atTop (𝓝 0)) :
    Tendsto δ atTop (𝓝 0) := by
  have h := hratio.mul hTlim
  simpa only [div_mul_cancel₀ _ (hT _).ne',mul_zero] using h

theorem dilation_radius_tendsto_zero {T δ t : ℕ → ℝ} (hT : ∀ n, 0 < T n)
    (ht : ∀ n, t n ∈ Icc 0 (T n)) (hδ : ∀ n, 0 < δ n)
    (hTlim : Tendsto T atTop (𝓝 0))
    (hratio : Tendsto (fun n => δ n/T n) atTop (𝓝 0)) :
    Tendsto (fun n => t n+δ n) atTop (𝓝 0) := by
  have hδlim := terminal_scale_tendsto_zero hT hTlim hratio
  apply squeeze_zero (fun n => (dilation_radius_pos (ht n).1 (hδ n)).le)
    (fun n => add_le_add (ht n).2 (le_refl (δ n)))
  simpa only [add_zero] using hTlim.add hδlim

theorem cold_fraction_subsequence {t δ : ℕ → ℝ}
    (ht : ∀ n, 0 ≤ t n) (hδ : ∀ n, 0 < δ n) :
    ∃ l ∈ Icc (0:ℝ) 1, ∃ κ : ℕ → ℕ, StrictMono κ ∧
      Tendsto (fun n => δ (κ n)/(t (κ n)+δ (κ n))) atTop (𝓝 l) :=
  isCompact_Icc.tendsto_subseq (fun n => cold_fraction_mem (ht n) (hδ n))

theorem normalized_horizon_limit_ge_one {T δ t : ℕ → ℝ} {U : ℝ}
    (hT : ∀ n, 0 < T n) (ht : ∀ n, t n ∈ Icc 0 (T n)) (hδ : ∀ n, 0 < δ n)
    (hratio : Tendsto (fun n => δ n/T n) atTop (𝓝 0))
    (hU : Tendsto (fun n => T n/(t n+δ n)) atTop (𝓝 U)) : 1 ≤ U := by
  have hden : Tendsto (fun n => 1+δ n/T n) atTop (𝓝 (1:ℝ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hratio
  have hlo : Tendsto (fun n => 1/(1+δ n/T n)) atTop (𝓝 (1:ℝ)) := by
    have h := (tendsto_const_nhds (x := (1:ℝ))).div hden one_ne_zero
    change Tendsto (fun n => 1/(1+δ n/T n)) atTop (𝓝 ((1:ℝ)/1)) at h
    simpa only [one_div_one] using h
  exact le_of_tendsto_of_tendsto' hlo hU (fun n => normalized_horizon_lower (hT n) (ht n) (hδ n))

end BoltzmannNonuniqueness.Cap

end

end

end OAI
