import OAI.Combinatorics.SparsestCut.DirectionAsymptotics

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.DirectionFamily
open Directions DirectionInterpolation DirectionAsymptotics GaussianTools FiniteNets
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

lemma normBounds_of_not_bad {g : Fin N → E} (hg : g ∉ normBad) (i : Fin N) :
    (m : ℝ)/4 ≤ ‖g i‖^2 ∧ ‖g i‖^2 ≤ 4*(m : ℝ) := by
  constructor
  · by_contra h; exact hg ⟨i, Or.inl (lt_of_not_ge h)⟩
  · by_contra h; exact hg ⟨i, Or.inr (lt_of_not_ge h)⟩

lemma inner_empiricalSin (g : Fin N → E) (v w : E) :
    inner ℝ (empiricalSin g w - Real.exp (-‖w‖^2/2) • w) v =
      (∑ i, inner ℝ (g i) v * Real.sin (inner ℝ (g i) w))/(N : ℝ) -
      inner ℝ w v * Real.exp (-‖w‖^2/2) := by
  simp only [empiricalSin, inner_sub_left, inner_smul_left, conj_trivial,
    sum_inner, div_eq_mul_inv]
  congr 1
  · rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

lemma net_fourier_scalar (hm : 0 < m) {g : Fin N → E} (hg : g ∉ normBad)
    {u : ℝ} (v w : E) (hv : ‖v‖ = 1) (hf : g ∉ fourierBad u v w) :
    |inner ℝ (empiricalSin g w - Real.exp (-‖w‖^2/2) • w) v| ≤
      u + 16*Real.exp (-(m : ℝ)/12) := by
  have hsample (i : Fin N) : fourierSummand v w (g i) =
      inner ℝ (g i) v * Real.sin (inner ℝ (g i) w) := by
    dsimp only [fourierSummand, covarianceSummand, truncate]
    exact Set.indicator_of_mem (show g i ∈ {z : E | ‖z‖^2 ≤ 4*(m : ℝ)} from
      (normBounds_of_not_bad hg i).2) _
  have hdev : |(∑ i, fourierSummand v w (g i))/(N : ℝ) -
      ∫ z, fourierSummand v w z ∂stdGaussian E| ≤ u := le_of_not_gt hf
  simp_rw [hsample] at hdev
  rw [inner_empiricalSin]
  have hb := truncation_fourier_bias (show 1 ≤ m by omega) v w hv
  exact (abs_sub_le _ (∫ z, fourierSummand v w z ∂stdGaussian E) _).trans (add_le_add hdev hb)

lemma net_covariance_scalar {g : Fin N → E} (hg : g ∉ normBad)
    (v : E) (hv : ‖v‖ = 1) (hf : g ∉ covarianceBad v) :
    |empiricalCov g v - 1| ≤ 1/8 + 16*Real.exp (-(m : ℝ)/12) := by
  have hsample (i : Fin N) : covarianceSummand v (g i) = (inner ℝ v (g i))^2 := by
    dsimp only [fourierSummand, covarianceSummand, truncate]
    exact Set.indicator_of_mem (show g i ∈ {z : E | ‖z‖^2 ≤ 4*(m : ℝ)} from
      (normBounds_of_not_bad hg i).2) _
  have hdev : |(∑ i, covarianceSummand v (g i))/(N : ℝ) -
      ∫ z, covarianceSummand v z ∂stdGaussian E| ≤ 1/8 := le_of_not_gt hf
  simp_rw [hsample] at hdev
  exact (abs_sub_le _ (∫ z, covarianceSummand v z ∂stdGaussian E) _).trans
    (add_le_add hdev (truncation_covariance_bias v hv))

lemma source_nets (hm : 2 ≤ m) : ∃ V W : Finset E,
    (∀ v ∈ V, ‖v‖ = 1) ∧
    (V.card : ℝ) ≤ Real.exp (6*(m : ℝ)^2) ∧
    (W.card : ℝ) ≤ Real.exp (48*(m : ℝ)^2) ∧
    (∀ v : E, ‖v‖ = 1 → ∃ v' ∈ V, ‖v-v'‖ ≤ 1/(m : ℝ)^3) ∧
    (∀ w : E, ‖w‖ ≤ (m : ℝ)^42 → ∃ w' ∈ W, ‖w-w'‖ ≤ 1/(m : ℝ)^3) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hδ : (0 : ℝ) < 1/(m : ℝ)^4 := by positivity
  have hid : (m : ℝ) * (1/(m : ℝ)^4) = 1/(m : ℝ)^3 := by field_simp
  obtain ⟨V,hV,hVc,hVnet⟩ := exists_coordinate_net (K := m^4) hδ {v : E | ‖v‖ = 1} (by
    intro v hv
    change ‖v‖ = 1 at hv
    rw [hv, Nat.cast_pow]
    simp [hm0.ne'])
  obtain ⟨W,hW,hWc,hWnet⟩ := exists_coordinate_net (K := m^46) hδ {w : E | ‖w‖ ≤ (m : ℝ)^42} (by
    intro w hw
    change ‖w‖ ≤ (m : ℝ)^42 at hw
    have he : (((m^46 : ℕ) : ℝ))*(1/(m : ℝ)^4) = (m : ℝ)^42 := by push_cast; field_simp
    rwa [he])
  refine ⟨V,W,hV,?_,?_,?_,?_⟩
  · exact (Nat.cast_le.mpr hVc).trans (by simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, show (4+2 : ℝ) = 6 by norm_num] using grid_card_bound m 4 hm)
  · exact (Nat.cast_le.mpr hWc).trans (by simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, show (46+2 : ℝ) = 48 by norm_num] using grid_card_bound m 46 hm)
  · intro v hv; simpa only [hid] using hVnet v hv
  · intro w hw; simpa only [hid] using hWnet w hw

lemma select_source_nets (hm : 1000000 ≤ m) (hlog : 1 ≤ Real.log m)
    (hmajor : 2*(m : ℝ)^9*Real.exp (-(m : ℝ)/8) +
      6*(m : ℝ)^3*Real.exp (-(m : ℝ)) < 1)
    (V W : Finset E) (hV : ∀ v ∈ V, ‖v‖ = 1)
    (hVc : (V.card : ℝ) ≤ Real.exp (6*(m : ℝ)^2))
    (hWc : (W.card : ℝ) ≤ Real.exp (48*(m : ℝ)^2)) :
    ∃ g : Fin (m^3) → Fin (m^6) → E,
      (∀ s a b, a ≠ b → ∀ t : ℝ, g s a ≠ t • g s b) ∧
      (∀ s, g s ∉ normBad) ∧
      (∀ s, ∀ v ∈ V, ∀ w ∈ W, g s ∉ fourierBad (1/(2*Real.sqrt m)) v w) ∧
      (∀ s, ∀ v ∈ V, g s ∉ covarianceBad v) ∧
      (∀ v ∈ V, (badCount (projectionBad (10*Real.sqrt (Real.log m)) v) g : ℝ) ≤
        ((m^3 : ℕ) : ℝ)/2) := by
  have hm0 : 0 < m := by omega
  apply select_on_nets hm0 (pow_pos hm0 _) (pow_pos hm0 _) V W hV
    (by positivity) (by positivity)
  · simpa only [Nat.cast_pow] using projection_failure_bound (show 2 ≤ m by omega)
      (show 0 ≤ Real.log m by linarith)
  · exact GaussianNonparallel.charts_pairwise_nonparallel (show 2 ≤ m by omega)
  · simp only [Nat.cast_pow]
    rw [normalized_fourier_exponent hm0, normalized_covariance_exponent m hm0]
    exact (probability_majorization hm (Nat.cast_nonneg _) (Nat.cast_nonneg _) hVc hWc).trans_lt hmajor

lemma badCount_le_of_imp {A B : Set (Fin N → E)} (g : Fin S → Fin N → E)
    (h : ∀ s, g s ∈ A → g s ∈ B) : badCount A g ≤ badCount B g := by
  classical
  apply Finset.card_le_card
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact h s hs

lemma good_chart_interpolation {N S : ℕ} (g : Fin S → Fin N → E)
    (hg : ∀ s, g s ∉ normBad) {v v' : E} {ρ q q' : ℝ}
    (hd : ‖v-v'‖ ≤ ρ) (hq : q+2*Real.sqrt m*ρ ≤ q') :
    badCount (projectionBad q' v) g ≤ badCount (projectionBad q v') g := by
  apply badCount_le_of_imp g
  intro s hs
  by_contra hn
  obtain ⟨i,hi⟩ := hs
  have hp : |inner ℝ v' (g s i)| ≤ q := by
    by_contra h; exact hn ⟨i,lt_of_not_ge h⟩
  have hgn : ‖g s i‖ ≤ 2*Real.sqrt m := by
    have := (normBounds_of_not_bad (hg s) i).2
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m), Real.sqrt_nonneg (m : ℝ), norm_nonneg (g s i)]
  have hh := (projection_interpolate hgn (by positivity) hd hp).trans hq
  exact not_lt_of_ge hh hi

structure Family (m : ℕ) where
  g : Fin (m^3) → Fin (m^6) → EuclideanSpace ℝ (Fin m)
  norms : ∀ s i, Real.sqrt m/2 ≤ ‖g s i‖ ∧ ‖g s i‖ ≤ 2*Real.sqrt m
  nonparallel : ∀ s a b, a ≠ b → ∀ t : ℝ, g s a ≠ t • g s b
  covariance : ∀ s v, ‖v‖ = 1 → 1/2 ≤ empiricalCov (g s) v ∧ empiricalCov (g s) v ≤ 2
  fourier : ∀ s w, ‖w‖ ≤ (m : ℝ)^42 →
    ‖empiricalSin (g s) w - Real.exp (-‖w‖^2/2) • w‖ ≤ 2/Real.sqrt m
  good : ∀ v, ‖v‖ = 1 →
    (badCount (projectionBad (11*Real.sqrt (Real.log m)) v) g : ℝ) ≤ ((m^3 : ℕ) : ℝ)/2

lemma family_at_large (hm : 1000000 ≤ m) (hlog : 1 ≤ Real.log m)
    (hbias : 16*Real.exp (-(m : ℝ)/12) ≤ 1/(8*(m : ℝ)))
    (hmajor : 2*(m : ℝ)^9*Real.exp (-(m : ℝ)/8) +
      6*(m : ℝ)^3*Real.exp (-(m : ℝ)) < 1) : Nonempty (Family m) := by
  classical
  obtain ⟨V,W,hV,hVc,hWc,hVnet,hWnet⟩ := source_nets (show 2 ≤ m by omega)
  obtain ⟨g,hpar,hg,hfour,hcov,hgood⟩ := select_source_nets hm hlog hmajor V W hV hVc hWc
  have hm0 : 0 < m := by omega
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hn : 0 < m^6 := pow_pos hm0 _
  have hu (s : Fin (m^3)) (i : Fin (m^6)) : ‖g s i‖^2 ≤ 4*(m : ℝ) :=
    (normBounds_of_not_bad (hg s) i).2
  refine ⟨{ g := g, norms := ?_, nonparallel := hpar, covariance := ?_, fourier := ?_, good := ?_ }⟩
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

theorem directions_exist : ∀ᶠ m : ℕ in atTop, Nonempty (Family m) := by
  have hlog : ∀ᶠ m : ℕ in atTop, 1 ≤ Real.log m :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 1000000, hlog, eventual_bias_bound,
    eventual_selection_majorant] with m hm hl hb hp
  exact family_at_large hm hl hb.2 hp

end UniformSparsestCut.DirectionFamily

end

end OAI
