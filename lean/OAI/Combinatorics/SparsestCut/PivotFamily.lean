import OAI.Combinatorics.SparsestCut.DirectionFamily

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.PivotFamily
open UniformSparsestCut.GaussianTools UniformSparsestCut.Directions
open UniformSparsestCut.DirectionFamily UniformSparsestCut.DirectionAsymptotics
open UniformSparsestCut.DirectionInterpolation
open scoped NNReal

lemma standard_density_le_one (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one,mul_one,sub_zero]
  have hs : 1 ≤ Real.sqrt (2*Real.pi) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [Real.pi_gt_three])
  have hex : Real.exp (-x^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hi : (√(2*Real.pi))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  simpa using mul_le_mul hi hex (Real.exp_nonneg _) (by norm_num : (0:ℝ) ≤ 1)

lemma standard_small_ball {a : ℝ} (ha : 0 ≤ a) :
    (gaussianReal 0 1).real {x | |x| ≤ a} ≤ 2*a := by
  have hs : {x : ℝ | |x| ≤ a} = Icc (-a) a := by ext (x : ℝ); exact (abs_le : |x| ≤ a ↔ -a ≤ x ∧ x ≤ a)
  rw [hs,measureReal_def,gaussianReal_apply_eq_integral 0 (by norm_num)]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  calc
    _ ≤ ∫ x in Icc (-a) a, (1:ℝ) := by
      apply integral_mono (integrable_gaussianPDFReal 0 1).integrableOn (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
      exact standard_density_le_one
    _ = 2*a := by
      rw [integral_const,measureReal_def,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith : 0 ≤ a-(-a))]
      simp only [smul_eq_mul,mul_one]; ring

lemma coordinate_small_ball {m : ℕ} (j : Fin m) {a : ℝ} (ha : 0 ≤ a) :
    (stdGaussian (EuclideanSpace ℝ (Fin m))).real {x | |x j| ≤ a} ≤ 2*a := by
  have hmap : (stdGaussian (EuclideanSpace ℝ (Fin m))).map (fun x => x j) = gaussianReal 0 1 := by
    have h := gaussian_inner_law (EuclideanSpace.single j 1 : EuclideanSpace ℝ (Fin m))
    have he : (⟨‖(EuclideanSpace.single j 1 : EuclideanSpace ℝ (Fin m))‖^2, sq_nonneg _⟩ : NNReal) = 1 := by
      apply Subtype.ext
      simp
    rw [he] at h
    simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at h
    exact h
  have h := congrArg (fun μ : Measure ℝ => μ.real {x | |x| ≤ a}) hmap
  simp only [measureReal_def] at h
  rw [Measure.map_apply_of_aemeasurable (by fun_prop) (by measurability)] at h
  exact h.le.trans (standard_small_ball ha)

lemma all_coordinate_small_ball {m N S : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    (Measure.pi (fun _ : Fin S => Measure.pi (fun _ : Fin N => stdGaussian (EuclideanSpace ℝ (Fin m))))).real
      {g | ∃ s i j, |g s i j| ≤ a} ≤ (S:ℝ)*((N:ℝ)*((m:ℝ)*(2*a))) := by
  have hcol : (stdGaussian (EuclideanSpace ℝ (Fin m))).real {x | ∃ j, |x j| ≤ a} ≤ (m:ℝ)*(2*a) := by
    simpa only [Fintype.card_fin,Set.mem_ofPred_eq] using finite_union_bound (fun j : Fin m => {x : EuclideanSpace ℝ (Fin m) | |x j| ≤ a}) (fun j => coordinate_small_ball j ha)
  have hchart := real_measure_exists_le (μ := stdGaussian (EuclideanSpace ℝ (Fin m)))
    (fun _ : Fin N => {x : EuclideanSpace ℝ (Fin m) | ∃ j, |x j| ≤ a}) (fun _ => by measurability) (fun _ => hcol)
  exact real_measure_exists_le
    (fun _ : Fin S => {g : Fin N → EuclideanSpace ℝ (Fin m) | ∃ i j, |g i j| ≤ a})
    (fun _ => by measurability) (fun _ => hchart)

section ExtraSelection
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => stdGaussian E
local notation "ν" => Measure.pi (fun _ : Fin N => μ)
local notation "π" => Measure.pi (fun _ : Fin S => ν)
theorem select_on_nets_extra (hm : 0 < m) (hN : 0 < N) (hS : 0 < S)
    (V W : Finset E) (hV : ∀ v ∈ V, ‖v‖ = 1)
    {u q : ℝ} (hu : 0 ≤ u) (hq : 0 ≤ q)
    (hqprob : (N : ℝ)*(2*Real.exp (-q^2/2)) ≤ 1/4)
    {P : (Fin S → Fin N → E) → Prop} (hP : ∀ᵐ g ∂π, P g)
    (Q : Set (Fin S → Fin N → E)) {p : ℝ} (hQ : (π).real Q ≤ p)
    (hprob : (S : ℝ) * ((N : ℝ)*(2*Real.exp (-(m : ℝ)/8)) +
        (V.card : ℝ)*(W.card : ℝ)*(2*Real.exp (-(N : ℝ)*u^2/(2*(2*Real.sqrt m)^2))) +
        (V.card : ℝ)*(2*Real.exp (-(N : ℝ)*(1/8)^2/(2*(4*(m : ℝ))^2)))) +
        (V.card : ℝ)*(2*Real.exp (-(S : ℝ)/32)) + p < 1) :
    ∃ g : Fin S → Fin N → E, P g ∧ g ∉ Q ∧
      (∀ s, g s ∉ normBad) ∧
      (∀ s, ∀ v ∈ V, ∀ w ∈ W, g s ∉ fourierBad u v w) ∧
      (∀ s, ∀ v ∈ V, g s ∉ covarianceBad v) ∧
      (∀ v ∈ V, (badCount (projectionBad q v) g : ℝ) ≤ (S : ℝ)/2) := by
  classical
  let A := chartBad (N := N) V W u
  let B : Set (Fin S → Fin N → E) := {g | ∃ s, g s ∈ A}
  let C : Set (Fin S → Fin N → E) :=
    {g | ∃ v : V, (S : ℝ)/2 < (badCount (projectionBad q v) g : ℝ)}
  have hBbound := real_measure_exists_le (fun _ : Fin S => A)
    (fun _ => chartBad_measurable V W u) (fun _ => chartBad_bound hm hN V W hV hu)
  have hCbound := goodBad_bound hS V hV hq hqprob
  have hBC : (π).real ((B ∪ C) ∪ Q) < 1 :=
    ((measureReal_union_le (B ∪ C) Q).trans
      (add_le_add ((measureReal_union_le B C).trans (add_le_add hBbound hCbound)) hQ)).trans_lt hprob
  obtain ⟨g, hg0, hgP⟩ := exists_outside_with_ae hBC hP
  have hg : g ∉ B ∪ C := fun h => hg0 (Or.inl h)
  have hgQ : g ∉ Q := fun h => hg0 (Or.inr h)
  have hgB : ∀ s, g s ∉ A := by
    intro s hs; exact hg (Or.inl ⟨s, hs⟩)
  refine ⟨g, hgP, hgQ, ?_, ?_, ?_, ?_⟩
  · intro s hs; exact hgB s (Or.inl (Or.inl hs))
  · intro s v hv w hw hs; exact hgB s (Or.inl (Or.inr ⟨(⟨v,hv⟩,⟨w,hw⟩), hs⟩))
  · intro s v hv hs; exact hgB s (Or.inr ⟨⟨v,hv⟩, hs⟩)
  · intro v hv; by_contra h
    exact hg (Or.inr ⟨⟨v,hv⟩, lt_of_not_ge h⟩)

end ExtraSelection

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

lemma select_source_nets_pivot (hm : 1000000 ≤ m) (hlog : 1 ≤ Real.log m)
    (hmajor : 2*(m : ℝ)^9*Real.exp (-(m : ℝ)/8) +
      6*(m : ℝ)^3*Real.exp (-(m : ℝ)) + 2/(m:ℝ)^20 < 1)
    (V W : Finset E) (hV : ∀ v ∈ V, ‖v‖ = 1)
    (hVc : (V.card : ℝ) ≤ Real.exp (6*(m : ℝ)^2))
    (hWc : (W.card : ℝ) ≤ Real.exp (48*(m : ℝ)^2)) :
    ∃ g : Fin (m^3) → Fin (m^6) → E,
      (∀ s a b, a ≠ b → ∀ t : ℝ, g s a ≠ t • g s b) ∧
      (∀ s i j, 1/(m:ℝ)^30 < |g s i j|) ∧
      (∀ s, g s ∉ normBad) ∧
      (∀ s, ∀ v ∈ V, ∀ w ∈ W, g s ∉ fourierBad (1/(2*Real.sqrt m)) v w) ∧
      (∀ s, ∀ v ∈ V, g s ∉ covarianceBad v) ∧
      (∀ v ∈ V, (badCount (projectionBad (10*Real.sqrt (Real.log m)) v) g : ℝ) ≤
        ((m^3 : ℕ) : ℝ)/2) := by
  have hm0 : 0 < m := by omega
  have hsmall := all_coordinate_small_ball (m := m) (N := m^6) (S := m^3) (by positivity : (0:ℝ) ≤ 1/(m:ℝ)^30)
  have hp : ((m^3:ℕ):ℝ)*(((m^6:ℕ):ℝ)*((m:ℝ)*(2*(1/(m:ℝ)^30)))) = 2/(m:ℝ)^20 := by
    push_cast; field_simp
  rw [hp] at hsmall
  obtain ⟨g,hg,hQ,hrest⟩  := select_on_nets_extra (N := m^6) (S := m^3) hm0 (pow_pos hm0 _) (pow_pos hm0 _)
    V W hV (by positivity : (0:ℝ) ≤ 1/(2*Real.sqrt m))
    (by positivity : (0:ℝ) ≤ 10*Real.sqrt (Real.log m))
    (by
      simpa only [Nat.cast_pow] using (projection_failure_bound (show 2 ≤ m by omega)
        (show 0 ≤ Real.log m by linarith)))
    (GaussianNonparallel.charts_pairwise_nonparallel (show 2 ≤ m by omega))
    {g | ∃ s i j, |g s i j| ≤ 1/(m:ℝ)^30} hsmall (by
      simp only [Nat.cast_pow]
      rw [normalized_fourier_exponent hm0, normalized_covariance_exponent m hm0]
      exact (add_le_add_left (probability_majorization hm (Nat.cast_nonneg _) (Nat.cast_nonneg _) hVc hWc) _).trans_lt hmajor)
  refine ⟨g,hg,?_,hrest⟩
  intro s i j
  exact lt_of_not_ge (fun h => hQ ⟨s,i,j,h⟩)

structure PFamily (m : ℕ) extends Family m where
  pivot : ∀ s i j, 1/(m:ℝ)^30 < |g s i j|

lemma pivot_family_at_large (hm : 1000000 ≤ m) (hlog : 1 ≤ Real.log m)
    (hbias : 16*Real.exp (-(m : ℝ)/12) ≤ 1/(8*(m : ℝ)))
    (hmajor : 2*(m : ℝ)^9*Real.exp (-(m : ℝ)/8) +
      6*(m : ℝ)^3*Real.exp (-(m : ℝ)) + 2/(m:ℝ)^20 < 1) : Nonempty (PFamily m) := by
  classical
  obtain ⟨V,W,hV,hVc,hWc,hVnet,hWnet⟩ := source_nets (show 2 ≤ m by omega)
  obtain ⟨g,hpar,hpivot,hg,hfour,hcov,hgood⟩ := select_source_nets_pivot hm hlog hmajor V W hV hVc hWc
  have hm0 : 0 < m := by omega
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hn : 0 < m^6 := pow_pos hm0 _
  have hu (s : Fin (m^3)) (i : Fin (m^6)) : ‖g s i‖^2 ≤ 4*(m : ℝ) :=
    (normBounds_of_not_bad (hg s) i).2
  refine ⟨{ g := g, norms := ?_, nonparallel := hpar, covariance := ?_, fourier := ?_, good := ?_, pivot := hpivot }⟩
  · intro s i
    have h := normBounds_of_not_bad (hg s) i
    have hs := Real.sq_sqrt hm0'.le
    constructor <;> nlinarith [Real.sqrt_nonneg (m : ℝ), norm_nonneg (g s i)]
  · intro s v hv
    have hh := covariance_net_bound hn (g s) (hu s) (by positivity) V hV hVnet
      (fun v hv => net_covariance_scalar (hg s) v (hV v hv) (hcov s v hv)) v hv
    have herr := covariance_net_error (show 1000 ≤ m by omega) hbias
    have heq : 2*(4*(m : ℝ))*(1/(m : ℝ)^3) = 8*(m : ℝ)*(1/(m : ℝ)^3) := by ring
    rw [heq] at hh
    have hab := abs_le.mp (hh.trans herr)
    constructor <;> linarith
  · intro s w hw
    have hρ : 1/(m : ℝ)^3 < 1 := by
      apply (div_lt_one (by positivity)).mpr
      have hx : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 3
      norm_num at hh; linarith
    have hh := fourier_net_bound hn (g s) (hu s) (by positivity) (by positivity) hρ V W
      hVnet hWnet (fun v hv w hw => net_fourier_scalar hm0 (hg s) v w (hV v hv) (hfour s v hv w hw)) w hw
    have herr := scalar_net_error (show 1000 ≤ m by omega) hbias
    have heq : 4*(m : ℝ)+(m : ℝ) = 5*(m : ℝ) := by ring
    rw [heq] at hh
    exact hh.trans herr
  · intro v hv
    obtain ⟨v',hv',hd⟩ := hVnet v hv
    have hh := good_chart_interpolation g hg hd (projection_net_error (show 1000 ≤ m by omega) hlog)
    exact (Nat.cast_le.mpr hh).trans (hgood v' hv')

lemma pivot_majorant_tendsto :
    Tendsto (fun m : ℕ => 2*(m : ℝ)^9*Real.exp (-(m : ℝ)/8) +
      6*(m : ℝ)^3*Real.exp (-(m : ℝ)) + 2/(m:ℝ)^20) atTop (𝓝 0) := by
  have hi : Tendsto (fun m : ℕ => (m:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := (hi.pow 20).const_mul 2
  have h := selection_majorant_tendsto.add hh
  simpa [div_eq_mul_inv,inv_pow] using h

theorem pivot_directions_exist : ∀ᶠ m : ℕ in atTop, Nonempty (PFamily m) := by
  have hlog : ∀ᶠ m : ℕ in atTop, 1 ≤ Real.log m :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  have hmajor := pivot_majorant_tendsto.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [eventually_ge_atTop 1000000,hlog,eventual_bias_bound,hmajor] with m hm hl hb hp
  exact pivot_family_at_large hm hl hb.2 hp

end UniformSparsestCut.PivotFamily

end

end OAI
