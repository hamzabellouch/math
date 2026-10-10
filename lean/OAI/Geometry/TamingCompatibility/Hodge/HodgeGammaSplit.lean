import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.ResolventGammaScalar
import OAI.Geometry.TamingCompatibility.Hodge.HodgeVolterraKernel
import OAI.Geometry.TamingCompatibility.Hodge.HodgeKernelGammaBounds

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

def hodgeGammaTailAction (T r : ℝ) (f : L2 A J α hs ht true) : L2 A J α hs ht true :=
  (1/120 : ℝ) • ∫ s : ℝ in Ioi (T/r^2),
    hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f

lemma hodgeGammaTailAction_bound {T r : ℝ} (hT : 0 ≤ T) (f : L2 A J α hs ht true) :
    ‖hodgeGammaTailAction A J α hs ht D hD T r f‖ ≤
      (1/120 : ℝ) * HodgeKernelBounds.gammaTail (T/r^2) * ‖f‖ := by
  have hcut : 0 ≤ T/r^2 := div_nonneg hT (sq_nonneg r)
  have hsub : Ioi (T/r^2) ⊆ Ioi (0:ℝ) := fun _ hx => hcut.trans_lt hx
  have hi := (hodgeHeatGamma_integrable A J α hs ht D hD r f).mono_set hsub
  have hw := hodgeGammaWeight_integrable.mono_set hsub
  have hh : ‖∫ s : ℝ in Ioi (T/r^2),
      hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f‖ ≤
      HodgeKernelBounds.gammaTail (T/r^2)*‖f‖ := by
    calc
      _ ≤ ∫ s : ℝ in Ioi (T/r^2),
          ‖hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ s : ℝ in Ioi (T/r^2), hodgeGammaWeight s*‖f‖ := by
        apply integral_mono_ae hi.norm (hw.mul_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsp
        have hs0 : 0 ≤ s := (hcut.trans_lt hsp).le
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hodgeGammaWeight_nonneg hs0)]
        exact mul_le_mul_of_nonneg_left (hodgeSpectralHeat_norm_le A J α hs ht D hD _ f)
          (hodgeGammaWeight_nonneg hs0)
      _ = _ := by rw [integral_mul_const]; rfl
  unfold hodgeGammaTailAction
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/120)]
  exact (mul_le_mul_of_nonneg_left hh (by norm_num)).trans_eq (by ring)

lemma hodgeGammaTailAction_rapid (N : ℕ) {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    (f : L2 A J α hs ht true) :
    ‖hodgeGammaTailAction A J α hs ht D hD T r f‖ ≤
      ((1/120 : ℝ) * HodgeKernelBounds.moment 5 (1/2) * (N.factorial : ℝ) * (2/T)^N) *
        r^(2*N)*‖f‖ := by
  apply (hodgeGammaTailAction_bound A J α hs ht D hD hT.le f).trans
  have hh := HodgeKernelBounds.gammaTail_small_scale N hT hr
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh
    (by norm_num : (0:ℝ) ≤ 1/120)) (norm_nonneg f)
  convert hb using 1; ring

lemma hodgeRegularization_gamma_split {T r : ℝ} (hT : 0 ≤ T) (hr : 0 < r)
    (f : L2 A J α hs ht true) :
    (hodgeRegularization A J α hs ht r ^ 2) f =
      (1/120 : ℝ) • (∫ s : ℝ in Ioc 0 (T/r^2),
        hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f) +
      hodgeGammaTailAction A J α hs ht D hD T r f := by
  have hi := hodgeHeatGamma_integrable A J α hs ht D hD r f
  have hcut : 0 ≤ T/r^2 := div_nonneg hT (sq_nonneg r)
  rw [hodgeRegularization_sq_eq_heat_integral A J α hs ht D hD r hr f,
    ← Ioc_union_Ioi_eq_Ioi hcut,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hi.mono_set (fun _ hx => hx.1)) (hi.mono_set (fun _ hx => hcut.trans_lt hx)),smul_add]
  rfl

lemma hodgeRegularization_gamma_test_split {T r : ℝ} (hT : 0 ≤ T) (hr : 0 < r)
    (f g : L2 A J α hs ht true) :
    ⟪(hodgeRegularization A J α hs ht r ^ 2) f,g⟫ =
      (1/120 : ℝ) * (∫ s : ℝ in Ioc 0 (T/r^2),
        hodgeGammaWeight s * ⟪hodgeSpectralHeat A J α hs ht D hD (r^2*s) f,g⟫) +
      ⟪hodgeGammaTailAction A J α hs ht D hD T r f,g⟫ := by
  rw [hodgeRegularization_gamma_split A J α hs ht D hD hT hr f,inner_add_left,real_inner_smul_left]
  congr 2
  have hi := (hodgeHeatGamma_integrable A J α hs ht D hD r f).mono_set
    (show Ioc 0 (T/r^2) ⊆ Ioi (0:ℝ) from fun _ hx => hx.1)
  rw [real_inner_comm,← integral_inner hi g]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    dsimp only
    rw [real_inner_smul_right,real_inner_comm]

end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open Set MeasureTheory

lemma polynomialMoment_integrable (q N : ℕ) :
    IntegrableOn (fun s : ℝ => Real.exp (-s)*s^q*(1+s)^N) (Ioi 0) := by
  have hm (n : ℕ) : IntegrableOn (fun s : ℝ => Real.exp (-s)*s^n) (Ioi 0) := by
    simpa only [one_mul,mul_one,mul_comm] using moment_integrable n (by norm_num : (0:ℝ)<1)
  have hb := ((hm q).add (hm (q+N))).const_mul ((2:ℝ)^(N-1))
  apply hb.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 ≤ s := hs.le
  dsimp only [Pi.add_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hh := mul_le_mul_of_nonneg_left (add_pow_le (by norm_num : (0:ℝ)≤1) hs.le N)
    (mul_nonneg (Real.exp_pos (-s)).le (pow_nonneg hs.le q))
  simpa only [Pi.add_apply,one_pow,one_mul,mul_one,pow_add,mul_add,add_mul,mul_assoc,mul_left_comm,mul_comm] using hh

lemma polynomialMoment_bound (q N : ℕ) :
    (∫ s : ℝ in Ioi 0, Real.exp (-s)*s^q*(1+s)^N) ≤
      (2:ℝ)^(N-1)*(moment q 1+moment (q+N) 1) := by
  have hm (n : ℕ) : IntegrableOn (fun s : ℝ => Real.exp (-s)*s^n) (Ioi 0) := by
    simpa only [one_mul,mul_one,mul_comm] using moment_integrable n (by norm_num : (0:ℝ)<1)
  calc
    _ ≤ ∫ s : ℝ in Ioi 0, (2:ℝ)^(N-1)*(Real.exp (-s)*s^q+Real.exp (-s)*s^(q+N)) := by
      apply integral_mono_ae (polynomialMoment_integrable q N) (((hm q).add (hm (q+N))).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hh := mul_le_mul_of_nonneg_left (add_pow_le (by norm_num : (0:ℝ)≤1) hs.le N)
        (mul_nonneg (Real.exp_pos (-s)).le (pow_nonneg hs.le q))
      simpa only [Pi.add_apply,one_pow,one_mul,mul_one,pow_add,mul_add,add_mul,mul_assoc,mul_left_comm,mul_comm] using hh
    _ = _ := by
      rw [integral_const_mul,integral_add (hm q) (hm (q+N))]
      have he (n : ℕ) : (∫ s : ℝ in Ioi 0, Real.exp (-s)*s^n) = moment n 1 := by
        simpa only [one_mul,mul_one,mul_comm] using moment_integral n (by norm_num : (0:ℝ)<1)
      rw [he,he]

variable {X : Type*} [PseudoMetricSpace X]

lemma weight_rescale (N : ℕ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (x y : X) :
    VolterraBounds.weight N (r^2) x y ≤
      (1+s)^N * VolterraBounds.weight N (r^2*s) x y := by
  unfold VolterraBounds.weight
  rw [← mul_pow,Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq_eq_abs,abs_of_pos hr]
  apply pow_le_pow_left₀ (by positivity)
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsr : Real.sqrt s ≤ 1+s := by
    have hh := sq_nonneg (Real.sqrt s-1)
    have he := Real.sq_sqrt hs.le
    nlinarith [Real.sqrt_nonneg s]
  have hb : 1 ≤ (1+s)/Real.sqrt s := (le_div_iff₀ hsqrt).mpr (by simpa using hsr)
  have ha : 0 ≤ dist x y/r := div_nonneg dist_nonneg hr.le
  have hh := mul_le_mul_of_nonneg_right hb ha
  have he : (1+s)*(1+dist x y/(r*Real.sqrt s)) =
      1+s+((1+s)/Real.sqrt s)*(dist x y/r) := by ring
  rw [he]
  nlinarith

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def gammaKernel (K : ℝ → X → X → B) (T r : ℝ) (x y : X) : B :=
  (1/120 : ℝ) • ∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s • K (r^2*s) x y

omit [CompleteSpace B] in
lemma weighted_gamma_integrand (q k N : ℕ) (hqk : q+k=5)
    {r s A : ℝ} (hr : 0 < r) (hs : 0 < s)
    (K : ℝ → X → X → B) (x y : X)
    (hK : VolterraBounds.weight N (r^2*s) x y * ‖K (r^2*s) x y‖ ≤ A/(r^2*s)^k) :
    VolterraBounds.weight N (r^2) x y * ‖hodgeGammaWeight s • K (r^2*s) x y‖ ≤
      A/r^(2*k) * (Real.exp (-s)*s^q*(1+s)^N) := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hodgeGammaWeight_nonneg hs.le)]
  have hh := mul_le_mul_of_nonneg_left hK (pow_nonneg (by linarith : (0:ℝ)≤1+s) N)
  have hb := mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_right (weight_rescale N hr hs x y) (norm_nonneg (K (r^2*s) x y))).trans
      (by simpa only [mul_assoc] using hh))
    (hodgeGammaWeight_nonneg hs.le)
  have he : hodgeGammaWeight s*((1+s)^N*(A/(r^2*s)^k)) =
      A/r^(2*k)*(Real.exp (-s)*s^q*(1+s)^N) := by
    unfold hodgeGammaWeight
    rw [← hqk,pow_add,mul_pow,← pow_mul]
    field_simp [ne_of_gt hr,ne_of_gt hs]
  calc
    _ ≤ hodgeGammaWeight s*((1+s)^N*(A/(r^2*s)^k)) := by
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hb
    _ = _ := he

omit [CompleteSpace B] in
lemma gammaKernel_bound (q k N : ℕ) (hqk : q+k=5)
    {T r A : ℝ} (hr : 0 < r) (hA : 0 ≤ A) (K : ℝ → X → X → B) (x y : X)
    (hKm : AEStronglyMeasurable (fun s : ℝ => K (r^2*s) x y) (volume.restrict (Ioc 0 (T/r^2))))
    (hK : ∀ t ∈ Ioc 0 T, VolterraBounds.weight N t x y*‖K t x y‖ ≤ A/t^k) :
    IntegrableOn (fun s : ℝ => hodgeGammaWeight s • K (r^2*s) x y) (Ioc 0 (T/r^2)) ∧
      VolterraBounds.weight N (r^2) x y*‖gammaKernel K T r x y‖ ≤
        ((1/120:ℝ)*A*(2:ℝ)^(N-1)*(moment q 1+moment (q+N) 1))/r^(2*k) := by
  let W := VolterraBounds.weight N (r^2) x y
  have hW : 0 < W := VolterraBounds.weight_pos N (sq_pos_of_pos hr) x y
  let Φ := fun s : ℝ => Real.exp (-s)*s^q*(1+s)^N
  have hΦ : IntegrableOn Φ (Ioi 0) := polynomialMoment_integrable q N
  have hsub : Ioc 0 (T/r^2) ⊆ Ioi (0:ℝ) := fun _ h => h.1
  have hΦ' := hΦ.mono_set hsub
  have hp (s : ℝ) (hsp : s ∈ Ioc 0 (T/r^2)) :
      W*‖hodgeGammaWeight s • K (r^2*s) x y‖ ≤ A/r^(2*k) * Φ s := by
    apply weighted_gamma_integrand q k N hqk hr hsp.1 K x y
    exact hK _ ⟨mul_pos (sq_pos_of_pos hr) hsp.1,by
      have hh := (le_div_iff₀ (sq_pos_of_pos hr)).mp hsp.2
      simpa only [mul_comm] using hh⟩
  have hi : IntegrableOn (fun s : ℝ => hodgeGammaWeight s • K (r^2*s) x y) (Ioc 0 (T/r^2)) := by
    apply (hΦ'.const_mul (A/r^(2*k)/W)).mono' (hodgeGammaWeight_continuous.aestronglyMeasurable.smul hKm)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hh := (le_div_iff₀ hW).mpr (show ‖hodgeGammaWeight s • K (r^2*s) x y‖*W ≤ A/r^(2*k)*Φ s by
      simpa only [mul_comm] using hp s hs)
    change ‖hodgeGammaWeight s • K (r^2*s) x y‖ ≤ (A/r^(2*k)/W)*Φ s
    simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  refine ⟨hi,?_⟩
  have hI : W*‖∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s • K (r^2*s) x y‖ ≤
      A/r^(2*k) * ((2:ℝ)^(N-1)*(moment q 1+moment (q+N) 1)) := by
    calc
      _ ≤ W*(∫ s : ℝ in Ioc 0 (T/r^2), ‖hodgeGammaWeight s • K (r^2*s) x y‖) :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hW.le
      _ = ∫ s : ℝ in Ioc 0 (T/r^2), W*‖hodgeGammaWeight s • K (r^2*s) x y‖ :=
        (integral_const_mul _ _).symm
      _ ≤ ∫ s : ℝ in Ioc 0 (T/r^2), A/r^(2*k)*Φ s := by
        apply integral_mono_ae (hi.norm.const_mul _) (hΦ'.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hp s hs
      _ = A/r^(2*k) * ∫ s : ℝ in Ioc 0 (T/r^2), Φ s := integral_const_mul _ _
      _ ≤ A/r^(2*k) * ∫ s : ℝ in Ioi 0, Φ s := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hA (pow_nonneg hr.le _))
        apply setIntegral_mono_set hΦ
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
          have hs0 : 0 ≤ s := hs.le
          dsimp [Φ]; positivity
        · exact Filter.Eventually.of_forall hsub
      _ ≤ _ := mul_le_mul_of_nonneg_left (polynomialMoment_bound q N) (div_nonneg hA (pow_nonneg hr.le _))
  unfold gammaKernel
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/120)]
  have hh := mul_le_mul_of_nonneg_left hI (by norm_num : (0:ℝ)≤1/120)
  dsimp only [W] at hh
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

end
end

end

end OAI
