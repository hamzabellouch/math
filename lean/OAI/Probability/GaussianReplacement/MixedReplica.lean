import OAI.Probability.GaussianReplacement.Gram

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace

section MixedNondegenerate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


theorem AmbientGrowth.affine_span_null {μ : Measure E} {a : ℕ} {A : ℝ}
    (hμ : AmbientGrowth μ a A) (hA : 0 ≤ A) (V : Submodule ℝ E) (s : E)
    (hmargin : Module.finrank ℝ V + 1 ≤ a) (hsupp : ∀ᵐ u ∂μ, ‖u-s‖ ≤ 2) :
    μ {u | u-s ∈ V} = 0 := by
  let C : ℝ := 3 ^ Module.finrank ℝ V * 2 ^ a * A * 2 ^ a
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb (j : ℕ) : μ {u | u-s ∈ V} ≤ ENNReal.ofReal (C * (1/2:ℝ)^j) := by
    have hj : 0 < (1/2:ℝ)^j := by positivity
    have hj1 : (1/2:ℝ)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc
      μ {u | u-s ∈ V} ≤ μ {u | ‖u-s‖ ≤ 2 ∧ Metric.infDist (u-s) (V:Set E) ≤ (1/2:ℝ)^j * 2} := by
        apply measure_mono_ae
        filter_upwards [hsupp] with u hu
        intro hv
        exact ⟨hu, by rw [Metric.infDist_zero_of_mem hv]; positivity⟩
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (((1/2:ℝ)^j)^1) :=
        hμ.radial_tube_pow hA V s 1 hmargin (by norm_num) hj hj1
      _ = _ := by rw [pow_one, ENNReal.ofReal_mul hC]
  have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal (C * (1/2:ℝ)^j)) atTop (𝓝 0) := by
    convert ENNReal.tendsto_ofReal ((tendsto_const_nhds (x:=C)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1))) using 1
    simp
  exact le_antisymm (ge_of_tendsto' hlim hb) bot_le



theorem AmbientGrowth.ae_gramSchmidt_ne_zero {μ : Measure E} [SigmaFinite μ] {a : ℕ} {A : ℝ}
    (hμ : AmbientGrowth μ a A) (hA : 0 ≤ A) (s : E)
    (hsupp : ∀ᵐ u ∂μ, ‖u-s‖ ≤ 2) (k : ℕ) (hk : k ≤ a) :
    ∀ᵐ v : Fin k → E ∂Measure.pi (fun _ => μ),
      ∀ i, gramSchmidt ℝ (fun j => v j - s) i ≠ 0 := by
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ k ih =>
    rw [ae_pi_snoc μ (measurableSet_gramSchmidt_ne_zero s (k+1))]
    filter_upwards [ih (by omega)] with v hv
    let V := Submodule.span ℝ (Set.range (fun i : Fin k => v i - s))
    have hdim : Module.finrank ℝ V ≤ k := by
      simpa [V, Set.finrank] using finrank_range_le_card (R:=ℝ) (fun i : Fin k => v i-s)
    have hnull : μ {u | u-s ∈ V} = 0 := hμ.affine_span_null hA V s (by omega) hsupp
    have ha : ∀ᵐ u ∂μ, u-s ∉ V := by
      rw [ae_iff]
      simpa only [not_not] using hnull
    filter_upwards [ha] with x hx
    intro i
    induction i using Fin.lastCases with
    | last =>
      apply norm_ne_zero_iff.mp
      rw [norm_gramSchmidt_eq_infDist, image_Iio_last]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact ne_of_gt ((V.closed_of_finiteDimensional.notMem_iff_infDist_pos
        ⟨0, V.zero_mem⟩).mp hx)
    | cast j => simpa only [gramSchmidt_castSucc, Fin.snoc_castSucc] using hv j

theorem AmbientGrowth.ae_replica_linearIndependent {μ : Measure E} [SigmaFinite μ]
    {a : ℕ} {A : ℝ} (hμ : AmbientGrowth μ a A) (hA : 0 ≤ A) (s : E)
    (hsupp : ∀ᵐ u ∂μ, ‖u-s‖ ≤ 2) (k : ℕ) (hk : k ≤ a) :
    ∀ᵐ v : Fin k → E ∂Measure.pi (fun _ => μ),
      LinearIndependent ℝ (fun j => v j-s) := by
  filter_upwards [hμ.ae_gramSchmidt_ne_zero hA s hsupp k hk] with v hv
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [det_gram_eq_prod_gramSchmidt]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hv i))

end MixedNondegenerate

section MixedReplica
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]


def mixedReplicaWeight (m r : ℕ) (s : E) {k : ℕ} (v : Fin k → E) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (‖v i-s‖⁻¹ ^ r * ‖gramSchmidt ℝ (fun j => v j-s) i‖⁻¹ ^ m)

lemma measurable_mixedReplicaWeight (m r : ℕ) (s : E) (k : ℕ) :
    Measurable (mixedReplicaWeight m r s (k:=k)) := by
  have hs : Measurable (fun v : Fin k → E => fun j => v j-s) := by fun_prop
  exact Finset.measurable_prod _ fun i _ =>
    (((measurable_pi_apply i).sub measurable_const).norm.inv.pow_const r |>.mul
      (((measurable_gramSchmidt i).comp hs).norm.inv.pow_const m)).ennreal_ofReal

omit [MeasurableSpace E] [BorelSpace E] in
lemma mixedReplicaWeight_snoc (m r : ℕ) (s : E) {k : ℕ} (v : Fin k → E) (x : E) :
    mixedReplicaWeight m r s (Fin.snoc v x) = mixedReplicaWeight m r s v *
      mixedInverse s (Submodule.span ℝ (Set.range (fun i => v i-s))) m r x := by
  unfold mixedReplicaWeight
  rw [Fin.prod_univ_castSucc]
  simp only [gramSchmidt_castSucc, Fin.snoc_castSucc]
  rw [norm_gramSchmidt_eq_infDist, image_Iio_last]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  rfl

theorem AmbientGrowth.mixed_inverse_uniform {μ : Measure E} {d n m r : ℕ} {B D : ℝ}
    (hBμ : AmbientGrowth μ (m+r) B) (hDμ : AmbientGrowth μ n D)
    (hB : 0 < B) (hD : 0 < D) (hn : m+r < n) (hnd : n ≤ d)
    (V : Submodule ℝ E) (s : E) (hmargin : Module.finrank ℝ V + (m+1) ≤ m+r)
    (hsupp : ∀ᵐ u ∂μ, ‖u-s‖ ≤ 2) :
    ∫⁻ u, mixedInverse s V m r u ∂μ ≤ momentConstant 9 d B D := by
  refine (hBμ.mixed_inverse_le hDμ hB hD (by omega) hn V s hmargin hsupp).trans
    (ENNReal.ofReal_le_ofReal ?_)
  gcongr
  exact shellConstant_exp_bound d _ n m r (by omega) (by omega) hnd (by omega) (by omega)


theorem AmbientGrowth.mixed_replica_integral {μ : Measure E} [SigmaFinite μ]
    {d n m r : ℕ} {B D : ℝ}
    (hBμ : AmbientGrowth μ (m+r) B) (hDμ : AmbientGrowth μ n D)
    (hB : 0 < B) (hD : 0 < D) (hn : m+r < n) (hnd : n ≤ d)
    (s : E) (hsupp : ∀ᵐ u ∂μ, ‖u-s‖ ≤ 2) (k : ℕ) (hk : k ≤ r) :
    ∫⁻ v : Fin k → E, mixedReplicaWeight m r s v ∂Measure.pi (fun _ => μ) ≤
      (momentConstant 9 d B D)^k := by
  induction k with
  | zero => simp [mixedReplicaWeight]
  | succ k ih =>
    have hinner (v : Fin k → E) :
        ∫⁻ x, mixedReplicaWeight m r s (Fin.snoc v x) ∂μ ≤
          mixedReplicaWeight m r s v * momentConstant 9 d B D := by
      simp_rw [mixedReplicaWeight_snoc]
      rw [lintegral_const_mul _ (measurable_mixedInverse _ _ _ _)]
      gcongr
      apply hBμ.mixed_inverse_uniform hDμ hB hD hn hnd _ s _ hsupp
      have hdim := finrank_range_le_card (R:=ℝ) (fun i : Fin k => v i-s)
      simp only [Fintype.card_fin, Set.finrank] at hdim
      omega
    calc
      _ = ∫⁻ v : Fin k → E, ∫⁻ x, mixedReplicaWeight m r s (Fin.snoc v x) ∂μ
          ∂Measure.pi (fun _ => μ) := lintegral_pi_snoc μ _ (measurable_mixedReplicaWeight m r s (k+1))
      _ ≤ ∫⁻ v : Fin k → E, mixedReplicaWeight m r s v * momentConstant 9 d B D
          ∂Measure.pi (fun _ => μ) := lintegral_mono hinner
      _ = (∫⁻ v : Fin k → E, mixedReplicaWeight m r s v ∂Measure.pi (fun _ => μ)) *
          momentConstant 9 d B D := lintegral_mul_const _ (measurable_mixedReplicaWeight m r s k)
      _ ≤ (momentConstant 9 d B D)^k * momentConstant 9 d B D :=
        mul_le_mul' (ih (by omega)) le_rfl
      _ = _ := (pow_succ _ _).symm

end MixedReplica

section FixedGaussianKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


lemma gaussian_fixed_kernel_bound {k : ℕ} (v : Fin k → E) (hv : LinearIndependent ℝ v)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1) (m : ℕ) :
    ∫⁻ X : Fin m → E, ∏ i, ∏ j, φ ⟪v i, X j⟫
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) := by
  let H : (Fin m → Fin k → ℝ) → ℝ≥0∞ := fun z => ∏ j, ∏ i, φ (z j i)
  have hH : Measurable H := by dsimp [H]; fun_prop
  have hH1 : ∫⁻ z, H z = 1 := by
    rw [volume_pi, lintegral_fin_prod (volume : Measure (Fin k → ℝ)) m
      (fun _ z => ∏ i, φ (z i)) (by intro j; fun_prop)]
    conv_lhs => arg 2; ext j; rw [volume_pi, lintegral_fin_prod (volume : Measure ℝ) k
      (fun _ z => φ z) (fun _ => hφ)]
    simp [hφ1]
  have heq (X : Fin m → E) : (∏ i, ∏ j, φ ⟪v i, X j⟫) = H (fun j i => ⟪v i, X j⟫) := by
    exact Finset.prod_comm
  simp_rw [heq]
  rw [← lintegral_map hH (by fun_prop)]
  calc
    _ ≤ ∫⁻ z, H z ∂(ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) •
        (volume : Measure (Fin m → Fin k → ℝ))) :=
      lintegral_mono' (gaussian_rows_pairings_le v hv m) (fun _ => le_rfl)
    _ = _ := by rw [lintegral_smul_measure, hH1]; simp


def rowKernel (φ : ℝ → ℝ≥0∞) {m : ℕ} (s u : E) (X : Fin m → E) : ℝ≥0∞ :=
  ∏ j, φ ⟪u-s, X j⟫

lemma measurable_rowKernel (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (m : ℕ) (s : E) :
    Measurable (fun z : E × (Fin m → E) => rowKernel φ s z.1 z.2) := by
  dsimp [rowKernel]
  fun_prop

lemma measurable_rowKernel_right (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ)
    (m : ℕ) (s u : E) : Measurable (rowKernel φ s u (m:=m)) := by
  change Measurable (fun X : Fin m → E => ∏ j, φ ⟪u-s, X j⟫)
  fun_prop

lemma measurable_rowKernel_left (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ)
    (m : ℕ) (s : E) (X : Fin m → E) : Measurable (fun u => rowKernel φ s u X) := by
  change Measurable (fun u : E => ∏ j, φ ⟪u-s, X j⟫)
  fun_prop

lemma gaussian_fresh_kernel_bound (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∫⁻ z, φ z = 1) (r : ℕ) (s u : E) (hu : u ≠ s) :
    ∫⁻ Z : Fin r → E, rowKernel φ s u Z ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal (‖u-s‖⁻¹ ^ r) := by
  have hv : LinearIndependent ℝ (fun _ : Fin 1 => u-s) :=
    linearIndependent_unique_iff.mpr (sub_ne_zero.mpr hu)
  have hh := gaussian_fixed_kernel_bound (fun _ : Fin 1 => u-s) hv φ hφ hφ1 r
  have he : gramSchmidt ℝ (fun _ : Fin 1 => u-s) 0 = u-s := gramSchmidt_bot ℝ _
  simpa only [Fin.prod_univ_one, he, rowKernel] using hh

end FixedGaussianKernel

section MixedKernelMoment
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowKernel_append (φ : ℝ → ℝ≥0∞) {m r : ℕ} (s u : E)
    (X : Fin m → E) (Z : Fin r → E) :
    rowKernel φ s u (Fin.append X Z) = rowKernel φ s u X * rowKernel φ s u Z := by
  simp only [rowKernel, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mixedReplicaWeight_factor (m r : ℕ) (s : E) {k : ℕ} (v : Fin k → E) :
    mixedReplicaWeight m r s v =
      (∏ i, ENNReal.ofReal (‖v i-s‖⁻¹ ^ r)) *
        ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun j => v j-s) i‖)⁻¹ ^ m) := by
  unfold mixedReplicaWeight
  simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ‖v _-s‖⁻¹ ^ r)]
  rw [Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_pow,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]



theorem AmbientGrowth.mixed_kernel_moment {μ : Measure E} [SigmaFinite μ]
    {d n m r q : ℕ} {B D : ℝ}
    (hBμ : AmbientGrowth μ (m+r) B) (hDμ : AmbientGrowth μ n D)
    (hB : 0 < B) (hD : 0 < D) (hr : 1 ≤ r) (hn : m+r < n) (hnd : n ≤ d)
    (hq : q ≤ r) (s : E) (hsupp : ∀ᵐ u ∂μ, ‖u-s‖ ≤ 2)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1) :
    ∫⁻ X : Fin m → E,
      (∫⁻ Z : Fin r → E, ∫⁻ u, rowKernel φ s u (Fin.append X Z) ∂μ
        ∂Measure.pi (fun _ => stdGaussian E))^q
      ∂Measure.pi (fun _ => stdGaussian E) ≤ (momentConstant 9 d B D)^q := by
  have hnull : μ {u | u=s} = 0 := by
    have hh := hBμ.affine_span_null hB.le (⊥ : Submodule ℝ E) s (by simpa using (by omega : 1 ≤ m+r)) hsupp
    simpa only [Submodule.mem_bot, sub_eq_zero] using hh
  have ha : ∀ᵐ u ∂μ, u ≠ s := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  let F : E → (Fin m → E) → ℝ≥0∞ := fun u X =>
    ENNReal.ofReal (‖u-s‖⁻¹ ^ r) * rowKernel φ s u X
  have hF : Measurable (Function.uncurry F) := by dsimp [F, rowKernel, Function.uncurry]; fun_prop
  have hFX (X : Fin m → E) : Measurable (fun u => F u X) :=
    hF.comp (measurable_id.prodMk measurable_const)
  have hfresh (X : Fin m → E) :
      ∫⁻ Z : Fin r → E, ∫⁻ u, rowKernel φ s u (Fin.append X Z) ∂μ
        ∂Measure.pi (fun _ => stdGaussian E) ≤ ∫⁻ u, F u X ∂μ := by
    simp_rw [rowKernel_append]
    rw [lintegral_lintegral_swap (by simp only [rowKernel]; fun_prop)]
    apply lintegral_mono_ae
    filter_upwards [ha] with u hu
    rw [lintegral_const_mul _ (measurable_rowKernel_right φ hφ r s u)]
    simpa only [F, mul_comm] using mul_le_mul' (le_rfl : rowKernel φ s u X ≤ rowKernel φ s u X)
      (gaussian_fresh_kernel_bound φ hφ hφ1 r s u hu)
  have hpow (X : Fin m → E) : (∫⁻ u, F u X ∂μ)^q =
      ∫⁻ v : Fin q → E, ∏ i, F (v i) X ∂Measure.pi (fun _ => μ) :=
    lintegral_pow_pi μ _ (hFX X) q
  calc
    _ ≤ ∫⁻ X : Fin m → E, (∫⁻ u, F u X ∂μ)^q
        ∂Measure.pi (fun _ => stdGaussian E) := by
      apply lintegral_mono
      intro X
      exact pow_le_pow_left' (hfresh X) q
    _ = ∫⁻ v : Fin q → E, ∫⁻ X : Fin m → E, ∏ i, F (v i) X
        ∂Measure.pi (fun _ => stdGaussian E) ∂Measure.pi (fun _ => μ) := by
      simp_rw [hpow]
      rw [lintegral_lintegral_swap (by dsimp [F, rowKernel]; fun_prop)]
    _ ≤ ∫⁻ v : Fin q → E, mixedReplicaWeight m r s v ∂Measure.pi (fun _ => μ) := by
      apply lintegral_mono_ae
      filter_upwards [hBμ.ae_replica_linearIndependent hB.le s hsupp q (by omega)] with v hv
      simp only [F, Finset.prod_mul_distrib]
      rw [lintegral_const_mul _ (by simp only [rowKernel]; fun_prop), mixedReplicaWeight_factor]
      exact mul_le_mul' le_rfl (gaussian_fixed_kernel_bound (fun i => v i-s) hv φ hφ hφ1 m)
    _ ≤ _ := hBμ.mixed_replica_integral hDμ hB hD hn hnd s hsupp q hq

end MixedKernelMoment

end CurrentProjection

end

end OAI
