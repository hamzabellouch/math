import Mathlib
import OAI.Probability.Ballisticity.Estimates.ClippedInverse

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma convexOn_rpow_nonpos_Ici {δ p : ℝ} (hδ : 0 < δ) (hp : p ≤ 0) :
    ConvexOn ℝ (Set.Ici δ) (fun x : ℝ => x ^ p) := by
  refine ⟨convex_Ici δ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 := hδ.trans_le hx
  have hy0 := hδ.trans_le hy
  have hz : 0 < a • x + b • y :=
    hδ.trans_le ((convex_Ici δ) hx hy ha hb hab)
  have hl := (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi).2 hx0 hy0 ha hb hab
  have he := convexOn_exp.2 (Set.mem_univ (p * Real.log x))
    (Set.mem_univ (p * Real.log y)) ha hb hab
  simp only [smul_eq_mul] at hl he hz ⊢
  rw [Real.rpow_def_of_pos hz, Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hy0]
  calc
    Real.exp (Real.log (a * x + b * y) * p) ≤
      Real.exp (a * (p * Real.log x) + b * (p * Real.log y)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonpos_right hl hp]
    _ ≤ a * Real.exp (Real.log x * p) + b * Real.exp (Real.log y * p) := by
      simpa only [mul_comm p] using he

lemma inverse_jensen_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {δ B lam : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam) (hb : ∀ x, δ ≤ f x ∧ f x ≤ B) :
    (∫ x, f x ∂μ) ^ (-lam) ≤ ∫ x, (f x) ^ (-lam) ∂μ := by
  have hi : Integrable f μ :=
    (MemLp.of_bound (p := 1) hf.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hδ.le.trans (hb x).1)] using
          (hb x).2)).integrable le_rfl
  have hj : Integrable (fun x => (f x) ^ (-lam)) μ :=
    (MemLp.of_bound (p := 1) (hf.pow_const _).aestronglyMeasurable (δ ^ (-lam))
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hδ.le.trans (hb x).1) _)]
        exact Real.rpow_le_rpow_of_nonpos hδ (hb x).1 (neg_nonpos.mpr hlam))).integrable le_rfl
  exact (convexOn_rpow_nonpos_Ici hδ (neg_nonpos.mpr hlam)).map_integral_le
    (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (hδ.trans_le hx))))
    isClosed_Ici (Filter.Eventually.of_forall fun x => (hb x).1) hi hj

lemma inverse_mixture_markov {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) (π : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (F : Ω → A → ℝ) (hF : Measurable (Function.uncurry F)) (Q : Ω → ℝ)
    {δ₀ δ lam s K : ℝ} (hδ₀ : 0 < δ₀) (hlam : 0 ≤ lam) (hs : 0 < s) (hδs : δ ≤ s)
    (hb : ∀ ω a, δ₀ ≤ F ω a ∧ F ω a ≤ 1)
    (hQ : ∀ ω, (∫ a, F ω a ∂π) ≤ Q ω + δ)
    (hE : (∫ ω, ∫ a, (F ω a) ^ (-lam) ∂π ∂μ) ≤ K) :
    μ {ω | Q ω < 2 * s} ≤ ENNReal.ofReal ((3 * s) ^ lam * K) := by
  have hGi : Integrable (fun z : Ω × A => F z.1 z.2 ^ (-lam)) (μ.prod π) :=
    (MemLp.of_bound (p := 1) (hF.pow_const _).aestronglyMeasurable (δ₀ ^ (-lam))
      (Filter.Eventually.of_forall fun z => by
        change ‖F z.1 z.2 ^ (-lam)‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hδ₀.le.trans (hb z.1 z.2).1) _)]
        exact Real.rpow_le_rpow_of_nonpos hδ₀ (hb z.1 z.2).1
          (neg_nonpos.mpr hlam))).integrable le_rfl
  have hJi ω : Integrable (F ω) π :=
    (MemLp.of_bound (p := 1) (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun a => by
        change ‖F ω a‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (hδ₀.le.trans (hb ω a).1)]
        exact (hb ω a).2)).integrable le_rfl
  have hJpos ω : 0 < ∫ a, F ω a ∂π := by
    have hl := integral_mono (integrable_const δ₀) (hJi ω) (fun a => (hb ω a).1)
    have hl' : δ₀ ≤ ∫ a, F ω a ∂π := by simpa using hl
    exact hδ₀.trans_le hl'
  have hp : 0 < 3 * s := mul_pos (by norm_num) hs
  have hMeas := (hGi.integral_prod_left.const_mul ((3 * s) ^ lam)).measure_le_integral
    (Filter.Eventually.of_forall fun ω => mul_nonneg (Real.rpow_nonneg hp.le _)
      (integral_nonneg (fun a => Real.rpow_nonneg (hδ₀.le.trans (hb ω a).1) _)))
    (s := {ω | Q ω < 2 * s}) (fun ω hω => by
      have hJle : (∫ a, F ω a ∂π) ≤ 3 * s := by
        change Q ω < 2 * s at hω
        linarith [hQ ω]
      have hj := inverse_jensen_bounded π
        (hF.comp (measurable_const.prodMk measurable_id)) hδ₀ hlam (hb ω)
      have hr := Real.rpow_le_rpow_of_nonpos (hJpos ω) hJle (neg_nonpos.mpr hlam)
      calc
        1 = (3 * s) ^ lam * (3 * s) ^ (-lam) := by
          rw [← Real.rpow_add hp, add_neg_cancel, Real.rpow_zero]
        _ ≤ (3 * s) ^ lam * ∫ a, F ω a ^ (-lam) ∂π :=
          mul_le_mul_of_nonneg_left (hr.trans hj) (Real.rpow_nonneg hp.le _))
  rw [integral_const_mul] at hMeas
  exact hMeas.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hp.le _)))

theorem separated_initial_inverse_moment {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d)
    (hℓ : dot ℓ ℓ = 1) (htrans : DirectionallyTransient ν ℓ) (e : Fin d) :
    ∃ lam C : ℝ, 0 < lam ∧ lam ≤ 1 ∧ 0 < C ∧
      ∀ Bstar : ℝ, 0 < Bstar → ∀ k : ℕ, 1 ≤ k → ∃ G : ℕ,
      ∀ (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π],
        (∀ᵐ x ∂π, Pairwise fun i j => (G : ℤ) ≤ |x i e - x j e|) →
        ∀ s : ℝ, Real.exp (-Bstar) ≤ s →
        (environmentLaw ν) {ω | (∫ x, noDropProduct ℓ x ω ∂π) < 2 * s} ≤
          ENNReal.ofReal (Real.exp (C * k) * s ^ lam) := by
  classical
  obtain ⟨lam, hlam, hlam1, hmom⟩ := noDrop_real_inverse_moment ν hue ℓ hℓ htrans
  let M := max 1 (∫ ω, (noDropQuenched ℓ 0 ω).toReal ^ (-lam) ∂environmentLaw ν)
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  let C := Real.log (6 * M)
  have hC : 0 < C := Real.log_pos (by linarith)
  refine ⟨lam, C, hlam, hlam1, hC, ?_⟩
  intro Bstar hBstar k hk
  let δ := Real.exp (-Bstar)
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hBstar.le)
  have hpos : ∀ᵐ ω ∂environmentLaw ν, 0 < noDropQuenched ℓ 0 ω := by
    filter_upwards [quenched_noDrop_positive_of_directionallyTransient ν hue ℓ hℓ htrans] with ω hω
    exact hω 0
  obtain ⟨n, hn⟩ := separated_noDropProduct_inverse_bound ν ℓ hδ hlam.le hpos hmom k
  refine ⟨2 * n + 1, ?_⟩
  intro π hπ hsep s hs
  have hs0 : 0 < s := hδ.trans_le hs
  let F : Environment d → (Fin k → Lattice d) → ℝ := fun ω x => clippedNoDropProduct ℓ δ x ω
  have hF : Measurable (Function.uncurry F) := clippedNoDropProduct_measurable ℓ δ
  have hb ω x : δ ^ k ≤ F ω x ∧ F ω x ≤ 1 :=
    clippedNoDropProduct_bounds ℓ hδ.le hδ1 x ω
  have hGi : Integrable (fun z : Environment d × (Fin k → Lattice d) =>
      F z.1 z.2 ^ (-lam)) ((environmentLaw ν).prod π) := by
    apply integrable_of_nonneg_bound _ (hF.pow_const _)
    intro z
    exact ⟨Real.rpow_nonneg ((pow_pos hδ k).le.trans (hb z.1 z.2).1) _,
      Real.rpow_le_rpow_of_nonpos (pow_pos hδ k) (hb z.1 z.2).1 (neg_nonpos.mpr hlam.le)⟩
  have hE : (∫ ω, ∫ x, F ω x ^ (-lam) ∂π ∂environmentLaw ν) ≤ 2 * M ^ k := by
    rw [integral_integral_swap hGi]
    have hh := integral_mono_ae hGi.integral_prod_right (integrable_const (2 * M ^ k))
      (hsep.mono fun x hx => hn x (fun i j hij => latticeBall_disjoint_of_coordinate_gap e
        (by have h := hx hij; omega)))
    simpa using hh
  have hQ ω : (∫ x, F ω x ∂π) ≤ (∫ x, noDropProduct ℓ x ω ∂π) + δ := by
    have hI : Integrable (noDropProduct ℓ · ω) π :=
      integrable_of_nonneg_bound π (measurable_of_countable _) (fun x => noDropProduct_bounds ℓ x ω)
    have hJ : Integrable (F ω) π :=
      integrable_of_nonneg_bound π (measurable_of_countable _) (fun x =>
        ⟨(pow_pos hδ k).le.trans (hb ω x).1, (hb ω x).2⟩)
    calc
      (∫ x, F ω x ∂π) ≤ ∫ x, noDropProduct ℓ x ω + δ ∂π :=
        integral_mono hJ (hI.add (integrable_const δ)) (clippedNoDropProduct_error ℓ hδ.le hδ1 · ω)
      _ = (∫ x, noDropProduct ℓ x ω ∂π) + δ := by simp [integral_add hI (integrable_const δ)]
  have hmark := inverse_mixture_markov (environmentLaw ν) π F hF
    (fun ω => ∫ x, noDropProduct ℓ x ω ∂π) (pow_pos hδ k) hlam.le hs0 hs hb hQ hE
  apply hmark.trans (ENNReal.ofReal_le_ofReal ?_)
  have h3 : (3 : ℝ) ^ lam ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 3 by norm_num) hlam1
  have h6 : (6 : ℝ) ≤ 6 ^ k := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 6 by norm_num) hk
    simpa only [pow_one] using h
  have hexp : Real.exp (C * k) = (6 * M) ^ k := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by positivity : 0 < 6 * M)]
  rw [hexp, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hs0.le, mul_pow]
  have hsp : 0 ≤ s ^ lam := Real.rpow_nonneg hs0.le _
  calc
    3 ^ lam * s ^ lam * (2 * M ^ k) ≤ 6 * M ^ k * s ^ lam := by
      nlinarith [mul_le_mul_of_nonneg_right h3 (mul_nonneg hsp (pow_nonneg hM0 k))]
    _ ≤ 6 ^ k * M ^ k * s ^ lam := by gcongr

lemma hitKernel_apply_eq_hit {d : ℕ} {S T : Set (Lattice d)}
    (hST : Disjoint S T) (U : Set (Lattice d)) (z : State d) :
    hitKernel S T z U = quenchedKernel z (Hit S (T ∩ U)) := by
  rw [hitKernel_apply]
  exact (measure_iUnion (hitAt_pairwise_disjoint (hST.mono_right Set.inter_subset_left))
    (measurableSet_hitAt S (T ∩ U))).symm

lemma hit_concatenation {d : ℕ} {S₁ T₁ S₂ T₂ S : Set (Lattice d)}
    (h₁ : S₁ ⊆ S) (h₂ : S₂ ⊆ S) :
    (⋃ n, HitAt S₁ T₁ n ∩ FutureEvent (fun _ => Hit S₂ T₂) n) ⊆ Hit S T₂ := by
  rintro X hX
  obtain ⟨n, hn, hfuture⟩ := Set.mem_iUnion.mp hX
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hfuture
  apply Set.mem_iUnion.mpr
  refine ⟨n + m, hm.1, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · exact h₁ (hn.2 j hjn)
  · have hn : n ≤ j := by omega
    have hsub : j - n < m := by omega
    have := h₂ (hm.2 (j - n) hsub)
    simpa only [Nat.add_sub_of_le hn] using this

lemma hitKernel_comp_le {d : ℕ} (ω : Environment d) (x : Lattice d)
    {S₁ T₁ S₂ T₂ S : Set (Lattice d)}
    (hST₁ : Disjoint S₁ T₁) (hST₂ : Disjoint S₂ T₂) (hST : Disjoint S T₂)
    (h₁ : S₁ ⊆ S) (h₂ : S₂ ⊆ S) (U : Set (Lattice d)) :
    (∫⁻ y, hitKernel S₂ T₂ (ω, y) U ∂hitKernel S₁ T₁ (ω, x)) ≤
      hitKernel S T₂ (ω, x) U := by
  simp_rw [hitKernel_apply_eq_hit hST₂ U]
  rw [hitKernel_future ω x hST₁ (fun _ => Hit S₂ (T₂ ∩ U))
    (fun _ => measurableSet_hit _ _), hitKernel_apply_eq_hit hST U]
  exact measure_mono (hit_concatenation h₁ h₂)

def HeightSlab {d : ℕ} (i : Fin d) (a b : ℤ) : Set (Lattice d) :=
  {x | a ≤ x i ∧ x i < b}

def HeightLayer {d : ℕ} (i : Fin d) (b : ℤ) : Set (Lattice d) :=
  {x | x i = b}

lemma heightSlab_disjoint_layer {d : ℕ} (i : Fin d) (a b : ℤ) :
    Disjoint (HeightSlab i a b) (HeightLayer i b) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (ne_of_lt hx.2) hy

noncomputable def heightKernel {d : ℕ} (i : Fin d) (a b : ℤ) :
    Kernel (State d) (Lattice d) :=
  hitKernel (HeightSlab i a b) (HeightLayer i b)

lemma heightKernel_total_le_one {d : ℕ} (i : Fin d) (a b : ℤ) (z : State d) :
    heightKernel i a b z Set.univ ≤ 1 :=
  hitKernel_total_le_one (heightSlab_disjoint_layer i a b) z

instance heightKernel_finite {d : ℕ} (i : Fin d) (a b : ℤ) :
    IsFiniteKernel (heightKernel i a b) where
  exists_univ_le := ⟨1, ENNReal.one_lt_top, heightKernel_total_le_one i a b⟩

lemma heightKernel_supported {d : ℕ} (i : Fin d) (a b : ℤ) (z : State d) :
    ∀ᵐ y ∂heightKernel i a b z, y i = b := by
  rw [ae_iff]
  change hitKernel (HeightSlab i a b) (HeightLayer i b) z (HeightLayer i b)ᶜ = 0
  rw [hitKernel_apply_eq_hit (heightSlab_disjoint_layer i a b), Set.inter_compl_self]
  have he : Hit (HeightSlab i a b) ∅ = ∅ := by
    ext X
    simp [Hit, HitAt]
  rw [he, measure_empty]

lemma heightKernel_rows {d : ℕ} (i : Fin d) {a b : ℤ} (hab : a < b)
    (x : Lattice d) (hx : x i = a) :
    @Measurable _ _ (rowSigma (HeightSlab i a b)) _
      (fun ω : Environment d => heightKernel i a b (ω, x)) := by
  exact measurable_hitKernel_rows _ _ x ⟨by simpa only [hx] using (le_refl a), by simpa only [hx]⟩

lemma heightKernel_comp_le {d : ℕ} (i : Fin d) {a b c : ℤ}
    (hab : a ≤ b) (hbc : b ≤ c) (ω : Environment d) (x : Lattice d)
    (U : Set (Lattice d)) :
    (∫⁻ y, heightKernel i b c (ω, y) U ∂heightKernel i a b (ω, x)) ≤
      heightKernel i a c (ω, x) U := by
  exact hitKernel_comp_le ω x (heightSlab_disjoint_layer i a b)
    (heightSlab_disjoint_layer i b c) (heightSlab_disjoint_layer i a c)
    (fun _ h => ⟨h.1, h.2.trans_le hbc⟩)
    (fun _ h => ⟨hab.trans h.1, h.2⟩) U

noncomputable def normalizedMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) : Measure α := (μ Set.univ)⁻¹ • μ

lemma normalizedMeasure_probability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (hμ : μ Set.univ ≠ 0) :
    IsProbabilityMeasure (normalizedMeasure μ) := by
  constructor
  simp only [normalizedMeasure, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hμ (measure_ne_top μ Set.univ)

lemma mass_smul_normalizedMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] :
    μ Set.univ • normalizedMeasure μ = μ := by
  by_cases hμ : μ Set.univ = 0
  · have hzero : μ = 0 := Measure.measure_univ_eq_zero.mp hμ
    simp [hzero, normalizedMeasure]
  · rw [normalizedMeasure, smul_smul,
      ENNReal.mul_inv_cancel hμ (measure_ne_top μ Set.univ), one_smul]

lemma integral_normalized_comp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ≥0∞) :
    μ Set.univ * (∫⁻ x, f x ∂normalizedMeasure μ) = ∫⁻ x, f x ∂μ := by
  change μ Set.univ • (∫⁻ x, f x ∂normalizedMeasure μ) = _
  rw [← lintegral_smul_measure, mass_smul_normalizedMeasure]

lemma retained_kernel_comp_le {d : ℕ} (i : Fin d) {a b c : ℤ}
    (hab : a ≤ b) (hbc : b ≤ c) (ω : Environment d) (x : Lattice d)
    (ρ : Measure (Lattice d)) (hρ : ρ ≤ heightKernel i a b (ω, x))
    (U : Set (Lattice d)) :
    ρ Set.univ * (∫⁻ y, heightKernel i b c (ω, y) U ∂normalizedMeasure ρ) ≤
      heightKernel i a c (ω, x) U := by
  have : IsFiniteMeasure ρ := ⟨lt_of_le_of_lt (hρ Set.univ)
    (measure_lt_top (heightKernel i a b (ω, x)) Set.univ)⟩
  rw [integral_normalized_comp]
  exact (lintegral_mono' hρ le_rfl).trans (heightKernel_comp_le i hab hbc ω x U)

lemma pathCylinder_weight_locality {d : ℕ} (S : Set (Lattice d))
    (ω η : Environment d) (hωη : Set.EqOn ω η S) (x : Lattice d)
    (f : Path d) (n : ℕ) (hf : ∀ j < n, f j ∈ S) :
    quenchedKernel (ω, x) (pathCylinder f n) =
      quenchedKernel (η, x) (pathCylinder f n) := by
  by_cases hfx : f 0 = x
  · rw [quenched_pathCylinder ω x f hfx, quenched_pathCylinder η x f hfx]
    exact Finset.prod_congr rfl fun j hj => by
      simp only [edgeWeight, hωη (hf j (Finset.mem_range.mp hj))]
  · rw [quenched_pathCylinder_zero ω x f hfx, quenched_pathCylinder_zero η x f hfx]

lemma quenched_restrict_stay_congr {d : ℕ} (S : Set (Lattice d))
    (ω η : Environment d) (hωη : Set.EqOn ω η S) (x : Lattice d) :
    (quenchedKernel (ω, x)).restrict (Stay S) =
      (quenchedKernel (η, x)).restrict (Stay S) := by
  apply pathMeasure_ext
  intro f n
  rw [Measure.restrict_apply (measurableSet_pathCylinder f n),
    Measure.restrict_apply (measurableSet_pathCylinder f n)]
  by_cases hf : ∀ j ≤ n, f j ∈ S
  · have he : pathCylinder f n ∩ Stay S =
        (fun X : Path d => fun j => X (n + j)) ⁻¹' Stay S ∩ pathCylinder f n := by
      ext X
      constructor
      · rintro ⟨hX, hS⟩
        exact ⟨fun j => hS (n + j), hX⟩
      · rintro ⟨hS, hX⟩
        refine ⟨hX, fun j => ?_⟩
        by_cases hj : j ≤ n
        · simpa only [hX j hj] using hf j hj
        · have hnj : n ≤ j := by omega
          simpa only [Nat.add_sub_of_le hnj] using hS (j - n)
    rw [he]
    by_cases hfx : f 0 = x
    · rw [quenched_prefix_future ω x f hfx n (measurableSet_stay S),
        quenched_prefix_future η x f hfx n (measurableSet_stay S),
        pathCylinder_weight_locality S ω η hωη x f n (fun j hj => hf j hj.le),
        quenched_stay_congr S ω η hωη (f n)]
    · rw [measure_mono_null Set.inter_subset_right (quenched_pathCylinder_zero ω x f hfx n),
        measure_mono_null Set.inter_subset_right (quenched_pathCylinder_zero η x f hfx n)]
  · have he : pathCylinder f n ∩ Stay S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨hX, hS⟩
      exact hf fun j hj => by simpa only [← hX j hj] using hS j
    rw [he]
    simp

lemma quenched_stay_event_congr {d : ℕ} (A : Set (Path d))
    (T : Set (Lattice d)) (hA : MeasurableSet A) (hAT : A ⊆ Stay T)
    (ω η : Environment d) (hωη : Set.EqOn ω η T) (x : Lattice d) :
    quenchedKernel (ω, x) A = quenchedKernel (η, x) A := by
  have := congrArg (fun μ : Measure (Path d) => μ A)
    (quenched_restrict_stay_congr T ω η hωη x)
  simpa only [Measure.restrict_apply hA, Set.inter_eq_left.mpr hAT] using this

lemma measurable_quenched_stay_event_rows {d : ℕ} (T : Set (Lattice d))
    (x : Lattice d) (hx : x ∈ T) (A : Set (Path d))
    (hA : MeasurableSet A) (hAT : A ⊆ Stay T) :
    @Measurable _ _ (rowSigma T) _ (fun ω : Environment d => quenchedKernel (ω, x) A) := by
  apply measurable_of_row_locality _
    ((Kernel.measurable_coe _ hA).comp (measurable_id.prodMk measurable_const)) T x hx
  intro ω η h
  exact quenched_stay_event_congr A T hA hAT ω η h x

lemma annealed_event_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (x : Lattice d) (A : Set (Path d)) (hA : MeasurableSet A) :
    (∫⁻ ω, quenchedKernel (ω, x) ((fun X : Path d => fun n => X n - x) ⁻¹' A)
      ∂environmentLaw ν) = annealedLaw ν A := by
  have ht : Measurable (fun X : Path d => fun n => X n - x) := by fun_prop
  have he (ω : Environment d) :
      quenchedKernel (ω, x) ((fun X : Path d => fun n => X n - x) ⁻¹' A) =
        quenchedKernel ((fun a => ω (x + a)), 0) A := by
    have := congrArg (fun μ : Measure (Path d) => μ A) (quenched_translation ω x 0)
    rw [Measure.map_apply ht hA] at this
    simpa only [add_zero] using this
  simp_rw [he]
  have hm : Measurable (fun ω : Environment d => quenchedKernel (ω, 0) A) :=
    (Kernel.measurable_coe _ hA).comp (measurable_id.prodMk measurable_const)
  rw [← lintegral_map hm (show Measurable (fun ω : Environment d => fun a => ω (x + a)) by
    fun_prop), environment_translation, ← annealed_apply ν hA]

lemma annealed_record_suffix {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (w : List (Direction d))
    (hrecord : ∀ y ∈ wordDepartures 0 w,
      dot (realPosition y) ℓ < dot (realPosition (wordPath 0 w w.length)) ℓ)
    (A : Set (Path d)) (hA : MeasurableSet A) (hAD : A ⊆ NoDrop ℓ 0) :
    annealedLaw ν ((fun X : Path d => fun j => X (w.length + j) -
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) =
      annealedLaw ν (wordCylinder 0 w) * annealedLaw ν A := by
  let y := wordPath 0 w w.length
  let S : Set (Lattice d) := ↑(wordDepartures 0 w)
  let T : Set (Lattice d) := {z | dot (realPosition y) ℓ ≤ dot (realPosition z) ℓ}
  let B : Set (Path d) := (fun X : Path d => fun j => X j - y) ⁻¹' A
  have hB : MeasurableSet B := hA.preimage (by fun_prop)
  have hBT : B ⊆ Stay T := by
    intro X hX j
    have h := hAD hX j
    change dot (realPosition y) ℓ ≤ dot (realPosition (X j)) ℓ
    change dot (realPosition 0) ℓ ≤ dot (realPosition (X j - y)) ℓ at h
    rw [dot_realPosition_sub] at h
    have hzero : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot, realPosition]
    rw [hzero] at h
    linarith
  have hST : Disjoint S T := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact (not_le_of_gt (hrecord z hz)) hz'
  have hw (ω : Environment d) : quenchedKernel (ω, 0)
      ((fun X : Path d => fun j => X (w.length + j) - y) ⁻¹' A ∩ wordCylinder 0 w) =
      ENNReal.ofReal (wordWeight ω 0 w) * quenchedKernel (ω, y) B := by
    have hh := quenched_prefix_future ω 0 (wordPath 0 w) (by simp) w.length hB
    change quenchedKernel (ω, 0) (_ ∩ wordCylinder 0 w) =
      quenchedKernel (ω, 0) (wordCylinder 0 w) * quenchedKernel (ω, y) B at hh
    rwa [quenched_wordCylinder] at hh
  rw [annealed_apply ν ((hA.preimage (by fun_prop)).inter (measurableSet_wordCylinder 0 w))]
  change (∫⁻ ω, quenchedKernel (ω, 0)
    ((fun X : Path d => fun j => X (w.length + j) - y) ⁻¹' A ∩ wordCylinder 0 w)
    ∂environmentLaw ν) = _
  simp_rw [hw]
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (rowSigma_le S) (rowSigma_le T) (environment_indep_rows ν hST)
    ((measurable_wordWeight_on 0 w (fun _ hz => hz)).ennreal_ofReal)
    (measurable_quenched_stay_event_rows T y
      (show dot (realPosition y) ℓ ≤ dot (realPosition y) ℓ from le_rfl) B hB hBT)]
  rw [← annealed_wordCylinder, annealed_event_translation ν y A hA]

end DirectionalTransience
end
end

end OAI
