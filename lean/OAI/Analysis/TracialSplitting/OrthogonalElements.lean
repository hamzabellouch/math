import OAI.Analysis.TracialSplitting.SimpleIdeals

namespace OAI

noncomputable section

universe uA uB

namespace Pureness

section

open Filter Topology

open scoped NNReal

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma rootExponent_tendsto :
    Tendsto (fun j : ℕ => ((j : ℝ≥0) + 1)⁻¹) atTop (𝓝 0) := by
  apply tendsto_inv_atTop_zero.comp
  have hn : Tendsto (fun j : ℕ => (j : ℝ≥0)) atTop atTop := tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono (fun j => le_add_of_nonneg_right (by positivity)) hn

lemma root_mul_uniform :
    TendstoUniformlyOn
      (fun j : ℕ => fun t : ℝ => t ^ ((((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) : ℝ))
      (fun t => t) atTop (Set.Icc 0 1) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
  · intro j
    exact (Real.continuous_rpow_const (by positivity)).continuousOn
  · intro t ht j k hjk
    by_cases ht0 : t = 0
    · subst t
      simp only [Real.zero_rpow (by positivity :
        (((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) ≠ (0 : ℝ)),
        Real.zero_rpow (by positivity :
        (((k : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) ≠ (0 : ℝ))]
      exact le_rfl
    · apply Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne ht.1 (Ne.symm ht0)) ht.2
      have hi : ((k : ℝ≥0) + 1)⁻¹ ≤ ((j : ℝ≥0) + 1)⁻¹ :=
        inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
      exact NNReal.coe_le_coe.mpr (add_le_add hi le_rfl)
  · exact continuousOn_id
  · intro t _
    have he : Tendsto (fun j : ℕ => ((((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) : ℝ))
        atTop (𝓝 1) := by
      have hn : Tendsto (fun j : ℕ => ((j : ℝ≥0) + 1)⁻¹ + 1) atTop (𝓝 1) :=
        by simpa using rootExponent_tendsto.add_const 1
      exact (NNReal.continuous_coe.tendsto 1).comp hn
    simpa using (tendsto_const_nhds.rpow he (Or.inr zero_lt_one) :
      Tendsto (fun j : ℕ => t ^ ((((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) : ℝ))
        atTop (𝓝 (t ^ (1 : ℝ))))

lemma normalizedRoot_mul_normalize_tendsto (h : A) (hh : 0 ≤ h) :
    Tendsto (fun j => normalizedRoot h j * normalizePositive h) atTop
      (𝓝 (normalizePositive h)) := by
  nontriviality A
  have hsub : quasispectrum ℝ (normalizePositive h) ⊆ Set.Icc 0 1 := by
    intro t ht
    refine ⟨quasispectrum_nonneg_of_nonneg _ (normalizePositive_nonneg h hh) _ ht, ?_⟩
    rw [quasispectrum_eq_spectrum_union_zero] at ht
    rcases ht with ht | ht
    · exact (le_abs_self t).trans ((spectrum.norm_le_norm_of_mem ht).trans
        (normalizePositive_norm_le h))
    · simpa only [Set.mem_singleton_iff.mp ht] using (zero_le_one : (0 : ℝ) ≤ 1)
  have ht := tendsto_cfcₙ_fun (a := normalizePositive h) (root_mul_uniform.mono hsub)
    (Eventually.of_forall fun j =>
      (Real.continuous_rpow_const (by positivity :
        (0 : ℝ) ≤ (((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0))).continuousOn)
    (Eventually.of_forall fun j => Real.zero_rpow (by positivity :
        (((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) ≠ (0 : ℝ)))
  simp only [cfcₙ_id' ℝ (normalizePositive h) (normalizePositive_nonneg h hh).isSelfAdjoint] at ht
  convert ht using 1
  ext j
  rw [← CFC.nnrpow_eq_cfcₙ_real _ _ (normalizePositive_nonneg h hh), CFC.nnrpow_add (by positivity) (by positivity),
    CFC.nnrpow_one _ (normalizePositive_nonneg h hh)]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_smul_normalizePositive (h : A) : ‖h‖ • normalizePositive h = h := by
  by_cases he : h = 0
  · simp [he]
  · simp [normalizePositive, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr he)]

lemma normalizedRoot_mul_self_tendsto (h : A) (hh : 0 ≤ h) :
    Tendsto (fun j => normalizedRoot h j * h) atTop (𝓝 h) := by
  have ht := (normalizedRoot_mul_normalize_tendsto h hh).const_smul ‖h‖
  simpa only [← mul_smul_comm, norm_smul_normalizePositive] using ht

lemma normalizedRoot_mul_hereditary_tendsto (h : A) (hh : 0 ≤ h)
    (c : A) (hc : c ∈ hereditaryCarrier h) :
    Tendsto (fun j => normalizedRoot h j * c) atTop (𝓝 c) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨d, ⟨w, rfl⟩, hd⟩ := Metric.mem_closure_iff.mp hc (ε / 4) (by positivity)
  have ht : Tendsto (fun j => normalizedRoot h j * (h * w * h)) atTop
      (𝓝 (h * w * h)) := by
    simpa only [mul_assoc] using
      ((normalizedRoot_mul_self_tendsto h hh).mul_const w).mul_const h
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp ht (ε / 2) (by positivity)
  refine ⟨J, fun j hj => ?_⟩
  have hsmall := hJ j hj
  simp only [dist_eq_norm] at hd hsmall ⊢
  have he : ‖normalizedRoot h j‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (normalizedRoot_nonneg h j)).mpr
      (normalizedRoot_le_one h hh j)
  have heq : normalizedRoot h j * c - c =
      normalizedRoot h j * (c - h * w * h) +
        (normalizedRoot h j * (h * w * h) - h * w * h) + (h * w * h - c) := by
    noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖normalizedRoot h j * (c - h * w * h)‖ +
        ‖normalizedRoot h j * (h * w * h) - h * w * h‖ + ‖h * w * h - c‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖normalizedRoot h j‖ * ‖c - h * w * h‖ +
        ‖normalizedRoot h j * (h * w * h) - h * w * h‖ + ‖h * w * h - c‖ := by
      gcongr
      exact norm_mul_le _ _
    _ < ε := by
      rw [norm_sub_rev (h * w * h) c]
      nlinarith [norm_nonneg (c - h * w * h)]

end

section

open Filter Topology

open scoped ComplexOrder ENNReal

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma trace_mul_contraction_le (τ : TracialState A) (e c : A)
    (he : 0 ≤ e) (hc : c ≤ 1) : τ.functional (e * c) ≤ τ.functional e := by
  have heq : τ.functional (e * c) =
      τ.functional (CFC.sqrt e * c * CFC.sqrt e) := by
    calc
      _ = τ.functional ((CFC.sqrt e * CFC.sqrt e) * c) := by
        rw [CFC.sqrt_mul_sqrt_self e he]
      _ = τ.functional ((CFC.sqrt e * c) * CFC.sqrt e) := by
        rw [mul_assoc, τ.tracial (CFC.sqrt e) (CFC.sqrt e * c)]
  rw [heq]
  apply τ.functional.monotone
  simpa only [(CFC.sqrt_nonneg e).star_eq, mul_one, CFC.sqrt_mul_sqrt_self e he] using
    star_left_conjugate_le_conjugate hc (CFC.sqrt e)

lemma trace_le_rank_of_mem_hereditary (τ : TracialState A) (h c : A)
    (hh : 0 ≤ h) (hc : c ∈ hereditaryCarrier h) (hc1 : c ≤ 1) :
    ENNReal.ofReal (τ.functional c).re ≤ normalizedRootRank τ h := by
  have ht : Tendsto (fun j => ENNReal.ofReal (τ.functional (normalizedRoot h j * c)).re)
      atTop (𝓝 (ENNReal.ofReal (τ.functional c).re)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Complex.continuous_re.continuousAt.tendsto.comp
        ((map_continuous τ.functional).continuousAt.tendsto.comp
          (normalizedRoot_mul_hereditary_tendsto h hh c hc)))
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro j
  calc
    _ ≤ ENNReal.ofReal (τ.functional (normalizedRoot h j)).re :=
      ENNReal.ofReal_le_ofReal (Complex.le_def.mp
        (trace_mul_contraction_le τ _ c (normalizedRoot_nonneg h j) hc1)).1
    _ ≤ normalizedRootRank τ h :=
      le_iSup (fun j => ENNReal.ofReal (τ.functional (normalizedRoot h j)).re) j

theorem hereditary_rank_domination (τ : TracialState A) (h c : A)
    (hh : 0 ≤ h) (hc : 0 ≤ c) (hcmem : c ∈ hereditaryCarrier h) :
    normalizedRootRank τ c ≤ normalizedRootRank τ h := by
  apply iSup_le
  intro j
  exact trace_le_rank_of_mem_hereditary τ h (normalizedRoot c j) hh
    (normalizedRoot_mem_hereditary hh hcmem hc j) (normalizedRoot_le_one c hc j)

theorem exists_rank_dominated_trace_transfer (hsimple : TopologicallySimple A)
    (h p : A) (hh : 0 ≤ h) (hne : h ≠ 0) (hp : 0 ≤ p) :
    ∃ c : A, 0 ≤ c ∧ c ∈ hereditaryCarrier h ∧
      (∀ τ : TracialState A, τ.functional c = τ.functional p) ∧
      (∀ τ : TracialState A, normalizedRootRank τ c ≤ normalizedRootRank τ h) := by
  obtain ⟨n, s, hs⟩ := fullness hsimple h hh hne
  let c := traceTransfer Finset.univ (CFC.sqrt h) p s
  have hc : 0 ≤ c := traceTransfer_nonneg _ _ _ _ (CFC.sqrt_nonneg h).star_eq hp
  have hcm : c ∈ hereditaryCarrier h := by
    dsimp [c]
    rw [traceTransfer_eq_sandwich]
    exact sqrt_sandwich_mem_hereditary h _ hh
  refine ⟨c, hc, hcm, ?_, fun τ => hereditary_rank_domination τ h c hh hc hcm⟩
  intro τ
  apply trace_transfer_identity τ.functional.toLinearMap.toAddMonoidHom τ.tracial
  simpa only [CFC.sqrt_mul_sqrt_self h hh] using hs

end

open Filter Topology

open scoped ComplexOrder NNReal Polynomial

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma trace_cfc_eq_of_moments (τ : TracialState A) (a b : A)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hm : ∀ n : ℕ, τ.functional (a ^ n) = τ.functional (b ^ n))
    (f : ℝ → ℝ) (hf : Continuous f) :
    τ.functional (cfc f a) = τ.functional (cfc f b) := by
  let : Algebra ℝ (A × A) := Algebra.complexToReal
  let : NormedSpace ℝ (A × A) := NormedSpace.complexToReal
  have hp : IsSelfAdjoint (a, b) := by
    show star (a, b) = (a, b)
    simp only [Prod.star_def, ha.star_eq, hb.star_eq]
  have hpoly (p : ℝ[X]) :
      τ.functional ((Polynomial.aeval (a, b) p).1) =
      τ.functional ((Polynomial.aeval (a, b) p).2) := by
    rw [Polynomial.aeval_eq_sum_range]
    simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
      Prod.pow_mk, map_sum, τ.functional.map_smul_of_tower, hm]
  have hclosed : IsClosed {z : A × A | τ.functional z.1 = τ.functional z.2} :=
    isClosed_eq ((map_continuous τ.functional).comp continuous_fst)
      ((map_continuous τ.functional).comp continuous_snd)
  have hsub : (StarAlgebra.elemental ℝ (a, b) : Set (A × A)) ⊆
      {z : A × A | τ.functional z.1 = τ.functional z.2} := by
    apply closure_minimal _ hclosed
    intro z hz
    change z ∈ (StarAlgebra.adjoin ℝ {(a, b)}).toSubalgebra at hz
    rw [StarAlgebra.adjoin_toSubalgebra, Set.star_singleton, hp.star_eq, Set.union_self,
      Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨p, rfl⟩ := hz
    exact hpoly p
  have hc := hsub (cfc_mem_elemental (p := IsSelfAdjoint) f (a, b))
  have hfst : (cfc f (a, b)).1 = cfc f a :=
    (StarAlgHom.fst ℂ A A).map_cfc f (a, b) hf.continuousOn continuous_fst hp ha
  have hsnd : (cfc f (a, b)).2 = cfc f b :=
    (StarAlgHom.snd ℂ A A).map_cfc f (a, b) hf.continuousOn continuous_snd hp hb
  change τ.functional (cfc f (a, b)).1 = τ.functional (cfc f (a, b)).2 at hc
  rwa [hfst, hsnd] at hc

omit [StarOrderedRing A] in
lemma trace_star_mul_self_pow (τ : TracialState A) (x : A) (n : ℕ) :
    τ.functional ((star x * x) ^ n) = τ.functional ((x * star x) ^ n) := by
  cases n with
  | zero => simp
  | succ n =>
    have hid : (star x * x) ^ (n + 1) = star x * (x * star x) ^ n * x := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ (star x * x) (n + 1), ih, pow_succ (x * star x) n]
        simp only [mul_assoc]
    rw [hid, mul_assoc, τ.tracial (star x) ((x * star x) ^ n * x),
      mul_assoc, ← pow_succ]

lemma trace_nnrpow_eq_of_moments (τ : TracialState A) (a b : A)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : ∀ n : ℕ, τ.functional (a ^ n) = τ.functional (b ^ n))
    (r : ℝ≥0) (hr : 0 < r) :
    τ.functional (CFC.nnrpow a r) = τ.functional (CFC.nnrpow b r) := by
  simp only [CFC.nnrpow_eq_pow, CFC.nnrpow_eq_cfcₙ_real a r ha,
    CFC.nnrpow_eq_cfcₙ_real b r hb]
  have hf0 : (0 : ℝ) ^ (r : ℝ) = 0 := Real.zero_rpow (by exact_mod_cast hr.ne')
  rw [cfcₙ_eq_cfc (hf0 := hf0), cfcₙ_eq_cfc (hf0 := hf0)]
  exact trace_cfc_eq_of_moments τ a b ha.isSelfAdjoint hb.isSelfAdjoint hm _
    (Real.continuous_rpow_const (by positivity))

theorem rank_star_mul_self (τ : TracialState A) (x : A) :
    normalizedRootRank τ (star x * x) = normalizedRootRank τ (x * star x) := by
  have hnorm : ‖star x * x‖ = ‖x * star x‖ := by
    calc
      _ = ‖x‖ * ‖x‖ := CStarRing.norm_star_mul_self (x := x)
      _ = ‖star x‖ * ‖star x‖ := by rw [norm_star]
      _ = _ := by simpa only [star_star] using (CStarRing.norm_star_mul_self (x := star x)).symm
  have hm (n : ℕ) :
      τ.functional ((normalizePositive (star x * x)) ^ n) =
      τ.functional ((normalizePositive (x * star x)) ^ n) := by
    simp only [normalizePositive, smul_pow, τ.functional.map_smul_of_tower,
      hnorm, trace_star_mul_self_pow τ x n]
  unfold normalizedRootRank
  congr 1
  funext j
  unfold normalizedRoot
  rw [trace_nnrpow_eq_of_moments τ _ _
    (normalizePositive_nonneg _ (star_mul_self_nonneg x))
    (normalizePositive_nonneg _ (mul_star_self_nonneg x)) hm _ (by positivity)]

end Pureness

open Filter Topology

namespace Pureness

variable {B : Type uB} [NonUnitalNormedRing B] [StarRing B]

def CuntzSubequiv (a b : B) : Prop :=
  a ∈ closure (Set.range fun v : B => star v * b * v)

theorem cuntzSubequiv_iff_sequence (a b : B) :
    CuntzSubequiv a b ↔
      ∃ v : ℕ → B, Tendsto (fun j => star (v j) * b * v j) atTop (𝓝 a) := by
  rw [CuntzSubequiv, mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨u, hu, hlim⟩
    choose v hv using hu
    exact ⟨v, by simpa only [hv] using hlim⟩
  · rintro ⟨v, hv⟩
    exact ⟨_, fun j => ⟨v j, rfl⟩, hv⟩

theorem cuntzSubequiv_iff_norm (a b : B) :
    CuntzSubequiv a b ↔ ∀ ε : ℝ, 0 < ε →
      ∃ v : B, ‖a - star v * b * v‖ < ε := by
  simp only [CuntzSubequiv, Metric.mem_closure_iff, Set.mem_range, dist_eq_norm]
  constructor
  · intro h ε hε
    obtain ⟨_, ⟨v, rfl⟩, hv⟩ := h ε hε
    exact ⟨v, hv⟩
  · intro h ε hε
    obtain ⟨v, hv⟩ := h ε hε
    exact ⟨_, ⟨v, rfl⟩, hv⟩

theorem cuntzSubequiv_conjugate (b v : B) : CuntzSubequiv (star v * b * v) b :=
  subset_closure ⟨v, rfl⟩

theorem zero_cuntzSubequiv (b : B) : CuntzSubequiv 0 b := by
  simpa using cuntzSubequiv_conjugate b 0

theorem cuntzSubequiv_of_tendsto {a : ℕ → B} {b c : B}
    (h : ∀ j, CuntzSubequiv (a j) b) (ha : Tendsto a atTop (𝓝 c)) :
    CuntzSubequiv c b :=
  isClosed_closure.mem_of_tendsto ha (Filter.Eventually.of_forall h)

theorem CuntzSubequiv.conjugate_left {a b : B} (h : CuntzSubequiv a b) (v : B) :
    CuntzSubequiv (star v * a * v) b := by
  obtain ⟨w, hw⟩ := (cuntzSubequiv_iff_sequence a b).mp h
  apply (cuntzSubequiv_iff_sequence _ _).mpr
  refine ⟨fun j => w j * v, ?_⟩
  have hlim : Tendsto (fun j => star v * (star (w j) * b * w j) * v)
      atTop (𝓝 (star v * a * v)) :=
    (tendsto_const_nhds.mul hw).mul tendsto_const_nhds
  simpa only [star_mul, mul_assoc] using hlim

theorem CuntzSubequiv.trans {a b c : B}
    (hab : CuntzSubequiv a b) (hbc : CuntzSubequiv b c) : CuntzSubequiv a c := by
  obtain ⟨v, hv⟩ := (cuntzSubequiv_iff_sequence a b).mp hab
  exact cuntzSubequiv_of_tendsto (fun j => hbc.conjugate_left (v j)) hv

theorem cuntzSubequiv_zero_iff (a : B) : CuntzSubequiv a 0 ↔ a = 0 := by
  simp [CuntzSubequiv, Set.range_const]

variable {A : Type uA} [NormedRing A] [StarRing A]

theorem cuntzSubequiv_refl (a : A) : CuntzSubequiv a a := by
  simpa using cuntzSubequiv_conjugate a 1

def cuntzSetoid : Setoid A where
  r a b := CuntzSubequiv a b ∧ CuntzSubequiv b a
  iseqv := {
    refl := fun a => ⟨cuntzSubequiv_refl a, cuntzSubequiv_refl a⟩
    symm := fun h => h.symm
    trans := fun h₁ h₂ => ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩ }

end Pureness

end

end OAI
