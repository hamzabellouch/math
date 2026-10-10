import OAI.Analysis.SignedDisk.LocalCancellation3

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

namespace DiskScales

lemma norm_geometric_rpow_lt {p : ℝ} (hp : 0 < p) : (1/2 : ℝ)^p < 1 :=
  Real.rpow_lt_one (by norm_num) (by norm_num) hp

lemma raw_endpoint_tail_scaled {A t δ M : ℝ} (hA : 0 ≤ A) (ht : 0 < t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM0 : 0 ≤ M)
    (hM : M ≤ A*δ^(-(1/50 : ℝ))) :
    (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ ^ 2 *
      (ENNReal.ofReal (156*δ/δ^(1/5 : ℝ))*ENNReal.ofReal M*ENNReal.ofReal M) +
    (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ *
      ((ENNReal.ofReal (6*Real.pi)*ENNReal.ofReal (2*(200*δ/(δ^(1/5 : ℝ))^2)))*ENNReal.ofReal M) +
    ENNReal.ofReal (24*Real.pi*δ)*ENNReal.ofReal M/ENNReal.ofReal (t*δ^(1/10 : ℝ)) ≤
    ENNReal.ofReal (156*(A/t)^2*δ^(14/25 : ℝ)+2424*Real.pi*(A/t)*δ^(9/25 : ℝ)) := by
  calc
    _ ≤ ENNReal.ofReal (156*(A/t)^2*δ^(14/25 : ℝ)+2400*Real.pi*(A/t)*δ^(9/25 : ℝ)) +
          ENNReal.ofReal (24*Real.pi*(A/t)*δ^(9/25 : ℝ)) :=
      add_le_add (shell_tail_scaled hA ht hδ hδ1 hM0 hM)
        (endpoint_tail_scaled hA ht hδ hδ1 hM)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

lemma geometric_tail_sum {A t d : ℝ} (hA : 0 ≤ A) (ht : 0 < t) (hd : 0 ≤ d) :
    (∑' n : ℕ, ENNReal.ofReal
      (156*(A/t)^2*(width d n)^(14/25 : ℝ)+2424*Real.pi*(A/t)*(width d n)^(9/25 : ℝ))) =
    ENNReal.ofReal (156*(A/t)^2*d^(14/25 : ℝ)/(1-(1/2 : ℝ)^(14/25 : ℝ))+
      2424*Real.pi*(A/t)*d^(9/25 : ℝ)/(1-(1/2 : ℝ)^(9/25 : ℝ))) := by
  have h1 := (summable_width_rpow hd (by norm_num : (0 : ℝ) < 14/25)).mul_left (156*(A/t)^2)
  have h2 := (summable_width_rpow hd (by norm_num : (0 : ℝ) < 9/25)).mul_left (2424*Real.pi*(A/t))
  have hn (n : ℕ) : 0 ≤ width d n := mul_nonneg hd (pow_nonneg (by norm_num) n)
  have hc1 : 0 ≤ 156*(A/t)^2 := by positivity
  have hc2 : 0 ≤ 2424*Real.pi*(A/t) := by positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => add_nonneg
    (mul_nonneg hc1 (Real.rpow_nonneg (hn n) _))
    (mul_nonneg hc2 (Real.rpow_nonneg (hn n) _))) (h1.add h2),
    Summable.tsum_add h1 h2, tsum_mul_left, tsum_mul_left,
    tsum_width_rpow hd (by norm_num : (0 : ℝ) < 14/25),
    tsum_width_rpow hd (by norm_num : (0 : ℝ) < 9/25)]
  congr 1
  ring

/-- After the initial-width choice d=A/t, the failure exponents are strictly
larger than one, rather than the nonintegrable weak-(1,1) exponent. -/
lemma starting_width_tail {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    156*(A/t)^2*(A/t)^(14/25 : ℝ)/(1-(1/2 : ℝ)^(14/25 : ℝ))+
      2424*Real.pi*(A/t)*(A/t)^(9/25 : ℝ)/(1-(1/2 : ℝ)^(9/25 : ℝ)) =
    (156/(1-(1/2 : ℝ)^(14/25 : ℝ)))*(A/t)^(64/25 : ℝ)+
      (2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ)))*(A/t)^(34/25 : ℝ) := by
  have hq : 0 < A/t := div_pos hA ht
  have he1 : (A/t)^2*(A/t)^(14/25 : ℝ) = (A/t)^(64/25 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hq]
    norm_num
  have he2 : (A/t)*(A/t)^(9/25 : ℝ) = (A/t)^(34/25 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one (A/t)]
    rw [← Real.rpow_add hq]
    norm_num
  calc
    _ = (156/(1-(1/2 : ℝ)^(14/25 : ℝ)))*((A/t)^2*(A/t)^(14/25 : ℝ))+
      (2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ)))*((A/t)*(A/t)^(9/25 : ℝ)) := by ring
    _ = _ := by rw [he1,he2]

lemma size_start_identity {Cs A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    (1+216*Cs)/(A/t)^(1/100 : ℝ)*A+
      (16+4538*Cs)*t*(A/t)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) =
    t*((1+216*Cs)*(A/t)^(99/100 : ℝ)+
      (16+4538*Cs)*(A/t)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) := by
  have hq : 0 < A/t := div_pos hA ht
  have he : (A/t)/(A/t)^(1/100 : ℝ) = (A/t)^(99/100 : ℝ) := by
    have hh := Real.rpow_sub hq (1 : ℝ) (1/100 : ℝ)
    norm_num at hh
    exact hh.symm
  have hAt : t*(A/t) = A := by field_simp
  calc
    _ = t*((1+216*Cs)*((A/t)/(A/t)^(1/100 : ℝ))+
      (16+4538*Cs)*(A/t)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) := by
        rw [mul_add]
        congr 1
        · calc
            _ = (1+216*Cs)/(A/t)^(1/100 : ℝ)*(t*(A/t)) := by rw [hAt]
            _ = _ := by ring
        · ring
    _ = _ := by rw [he]

/-- One fixed small-width cutoff enforces geometry and the strict endpoint
size threshold at every smaller positive width. -/
lemma exists_size_parameters (Cs : ℝ) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1/4 ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ d₀ → δ ≤ (δ^(1/5 : ℝ))^2/1600) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
        (1+216*Cs)*δ^(99/100 : ℝ)+
          (16+4538*Cs)*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) ≤ 1) := by
  obtain ⟨d,hd,hdq,hgeom⟩ := exists_admissible_width
  have ht : Tendsto (fun δ : ℝ => (1+216*Cs)*δ^(99/100 : ℝ)+
      (16+4538*Cs)*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) (𝓝 0) (𝓝 0) := by
    have h1 := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 99/100)).tendsto 0
    have h2 := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1/10)).tendsto 0
    simpa using (h1.const_mul (1+216*Cs)).add ((h2.const_mul (16+4538*Cs)).div_const _)
  obtain ⟨l,u,hu,hs⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  let d₀ := min d (u/2)
  have hd0 : 0 < d₀ := lt_min hd (by linarith [hu.2])
  refine ⟨d₀,hd0,(min_le_left _ _).trans hdq,fun δ hδ hδd => hgeom δ hδ (hδd.trans (min_le_left _ _)), ?_⟩
  intro δ hδ hδd
  apply le_of_lt
  apply hs
  exact ⟨lt_trans hu.1 hδ, lt_of_le_of_lt hδd ((min_le_right _ _).trans_lt (by linarith [hu.2]))⟩

def sizeTailConstant : ℝ :=
  156/(1-(1/2 : ℝ)^(14/25 : ℝ))+2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ))

lemma sizeTailConstant_pos : 0 < sizeTailConstant := by
  have h1 : 0 < 1-(1/2 : ℝ)^(14/25 : ℝ) := sub_pos.mpr (norm_geometric_rpow_lt (by norm_num))
  have h2 : 0 < 1-(1/2 : ℝ)^(9/25 : ℝ) := sub_pos.mpr (norm_geometric_rpow_lt (by norm_num))
  unfold sizeTailConstant
  positivity

lemma collapse_size_tail {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    (156/(1-(1/2 : ℝ)^(14/25 : ℝ)))*q^(64/25 : ℝ)+
      (2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ)))*q^(34/25 : ℝ) ≤
      sizeTailConstant*q^(34/25 : ℝ) := by
  have hc : 0 ≤ 156/(1-(1/2 : ℝ)^(14/25 : ℝ)) :=
    div_nonneg (by norm_num) (sub_nonneg.mpr ((norm_geometric_rpow_lt (by norm_num)).le))
  have he := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hq hq1 (by norm_num : (34/25 : ℝ) ≤ 64/25)) hc
  unfold sizeTailConstant
  nlinarith

end DiskScales

namespace LocalCancellation
open DiskKernels DiskMoments DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

/-- The uniform integrable superlevel tail, with both forced band endpoints.
The only decomposition assumption is equality of the specified densities on
each observation disk. No direction positivity is needed for this size bound. -/
theorem size_tail {Cs : ℝ} (hCs : 0 ≤ Cs) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ {ι : Type*} [Fintype ι] (b : ι → ErrorPiece Cs),
      0 < errorPrice b (1/100) → ∀ t : ℝ, L*errorPrice b (1/100) ≤ t →
      ∀ g : ℂ → ℝ, ContDiff ℝ 1 g →
      ∃ E : Set ℂ, MeasurableSet E ∧
        volume E ≤ ENNReal.ofReal (sizeTailConstant*(errorPrice b (1/100)/t)^(34/25 : ℝ)) ∧
        ∀ x ∉ E,
          (∀ᵐ y, y ∈ Metric.ball x 3 → ∑ j, (b j).density y = gradient g y) →
          ∀ r, EndpointRadius g x r → ‖∫ y in Metric.ball x r, gradient g y‖ ≤ t := by
  obtain ⟨d₀,hd0,hdq,hgeom,hsmall⟩ := exists_size_parameters Cs
  have hL : 1 ≤ (1 : ℝ)/d₀ := (le_div_iff₀ hd0).mpr (by linarith)
  refine ⟨1/d₀,hL,?_⟩
  intro ι _ b hA t ht g hg
  let A := errorPrice b (1/100)
  have hAt : A ≤ t := (le_mul_of_one_le_left hA.le hL).trans ht
  have ht0 : 0 < t := lt_of_lt_of_le hA hAt
  have hqd : A/t ≤ d₀ := by
    apply (div_le_iff₀ ht0).mpr
    have hh : A/d₀ ≤ t := by simpa only [A,one_div, div_eq_mul_inv, mul_comm, mul_one] using ht
    have hh' := (div_le_iff₀ hd0).mp hh
    linarith
  have hq0 : 0 < A/t := div_pos hA ht0
  have hq1 : A/t ≤ 1 := by linarith
  have hqq : A/t ≤ 1/4 := hqd.trans hdq
  obtain ⟨E,hE,hEv,hEst⟩ := size_endpoint_raw b hCs hq0 hqq
    (fun δ hδ hδq => hgeom δ hδ (hδq.trans hqd)) ht0 hAt hg
  refine ⟨E,hE,?_,?_⟩
  · apply hEv.trans
    calc
      _ ≤ ∑' n : ℕ, ENNReal.ofReal
          (156*(A/t)^2*(width (A/t) n)^(14/25 : ℝ)+
            2424*Real.pi*(A/t)*(width (A/t) n)^(9/25 : ℝ)) := by
        apply ENNReal.tsum_le_tsum
        intro n
        have hw0 : 0 < width (A/t) n := width_pos hq0 n
        have hw1 : width (A/t) n ≤ 1 := (width_le hq0.le n).trans hq1
        apply raw_endpoint_tail_scaled hA.le ht0 hw0 hw1 (coarseMass_nonneg b _ _)
        have hh := coarseMass_bound b (by norm_num : (0 : ℝ) ≤ 1/100) hw0
        norm_num at hh
        rw [Real.rpow_neg hw0.le]
        exact hh
      _ = ENNReal.ofReal
          ((156/(1-(1/2 : ℝ)^(14/25 : ℝ)))*(A/t)^(64/25 : ℝ)+
            (2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ)))*(A/t)^(34/25 : ℝ)) := by
        rw [geometric_tail_sum hA.le ht0 hq0.le, starting_width_tail hA ht0]
      _ ≤ ENNReal.ofReal (sizeTailConstant*(A/t)^(34/25 : ℝ)) :=
        ENNReal.ofReal_le_ofReal (collapse_size_tail hq0 hq1)
  · intro x hx hh r hr
    apply (hEst x hx hh r hr).trans
    rw [size_start_identity hA ht0]
    exact (mul_le_mul_of_nonneg_left (hsmall _ hq0 hqd) ht0.le).trans_eq (mul_one t)

end LocalCancellation

namespace DyadicMajorant

section
variable {X : Type*} [MeasurableSpace X]

/-- A Borel price built from exceptions, rather than a measurability-dependent
selection of maximizing radii. -/
def price (t : ℝ) (E : ℕ → Set X) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal t + ∑' n : ℕ, (E n).indicator (fun _ => ENNReal.ofReal (t*2^(n+1))) x

lemma measurable_price (t : ℝ) {E : ℕ → Set X} (hE : ∀ n, MeasurableSet (E n)) :
    Measurable (price t E) := by
  unfold price
  have hs : Measurable (fun x => ∑' n : ℕ, (E n).indicator (fun _ => ENNReal.ofReal (t*2^(n+1))) x) := Measurable.tsum (fun n =>
    (measurable_const : Measurable (fun _ : X => ENNReal.ofReal (t*2^(n+1)))).indicator (hE n))
  exact measurable_const.add hs

omit [MeasurableSpace X] in
lemma majorizes {t v : ℝ} (ht : 0 < t) {E : ℕ → Set X} {x : X}
    (hv : ∀ n : ℕ, x ∉ E n → v ≤ t*2^n) :
    ENNReal.ofReal v ≤ price t E x := by
  by_cases hvt : v ≤ t
  · exact (ENNReal.ofReal_le_ofReal hvt).trans le_self_add
  · have he : ∃ n : ℕ, v ≤ t*2^n := by
      obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (v/t) (by norm_num : (1 : ℝ) < 2)
      exact ⟨n, le_of_lt ((div_lt_iff₀ ht).mp hn |> fun h => by simpa only [mul_comm] using h)⟩
    let n := Nat.find he
    have hn : v ≤ t*2^n := Nat.find_spec he
    have hn0 : n ≠ 0 := by
      intro hz
      have : v ≤ t := by simpa only [hz, pow_zero, mul_one] using hn
      exact hvt this
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hjn : j < n := by omega
    have hmem : x ∈ E j := by
      by_contra h
      exact Nat.find_min he hjn (hv j h)
    have hp : ENNReal.ofReal (t*2^(j+1)) ≤ price t E x := by
      have hs := ENNReal.le_tsum j (f := fun n : ℕ => (E n).indicator (fun _ => ENNReal.ofReal (t*2^(n+1))) x)
      rw [indicator_of_mem hmem] at hs
      exact hs.trans le_add_self
    apply le_trans (ENNReal.ofReal_le_ofReal hn)
    simpa only [hj, Nat.succ_eq_add_one] using hp

lemma lintegral_price (μ : Measure X) {Q : Set X}
    (t : ℝ) {E : ℕ → Set X} (hE : ∀ n, MeasurableSet (E n)) :
    (∫⁻ x in Q, price t E x ∂μ) ≤
      ENNReal.ofReal t*μ Q + ∑' n : ℕ, ENNReal.ofReal (t*2^(n+1))*μ (E n) := by
  simp only [price]
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ,
    lintegral_tsum (fun n => (measurable_const.indicator (hE n)).aemeasurable)]
  apply add_le_add le_rfl
  apply ENNReal.tsum_le_tsum
  intro n
  rw [lintegral_indicator (hE n), lintegral_const, Measure.restrict_apply_univ,
    Measure.restrict_apply (hE n)]
  exact mul_le_mul_right (measure_mono inter_subset_left) _

end

lemma weighted_geometric_sum {t K c : ℝ} (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hc1 : 2*c < 1) :
    (∑' n : ℕ, ENNReal.ofReal (t*2^(n+1))*ENNReal.ofReal (K*c^n)) =
      ENNReal.ofReal (2*t*K/(1-2*c)) := by
  have he (n : ℕ) : ENNReal.ofReal (t*2^(n+1))*ENNReal.ofReal (K*c^n) =
      ENNReal.ofReal (2*t*K*(2*c)^n) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_pow, pow_succ]
    ring
  simp_rw [he]
  have hc' : ‖2*c‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hc1
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    ((summable_geometric_of_norm_lt_one hc').mul_left (2*t*K)),
    tsum_mul_left, tsum_geometric_of_norm_lt_one hc']
  rfl

variable {X : Type*} [MeasurableSpace X]

lemma lintegral_price_geometric (μ : Measure X) {Q : Set X} {q t K c : ℝ}
    (hq : 0 ≤ q) (hQ : μ Q ≤ ENNReal.ofReal q) (ht : 0 ≤ t)
    (hK : 0 ≤ K) (hc : 0 ≤ c) (hc1 : 2*c < 1)
    {E : ℕ → Set X} (hE : ∀ n, MeasurableSet (E n))
    (hEv : ∀ n : ℕ, μ (E n) ≤ ENNReal.ofReal (K*c^n)) :
    (∫⁻ x in Q, price t E x ∂μ) ≤
      ENNReal.ofReal (t*(q+2*K/(1-2*c))) := by
  apply (lintegral_price μ t hE).trans
  calc
    _ ≤ ENNReal.ofReal t*ENNReal.ofReal q+
        ∑' n : ℕ, ENNReal.ofReal (t*2^(n+1))*ENNReal.ofReal (K*c^n) :=
      add_le_add (mul_le_mul_right hQ _) (ENNReal.tsum_le_tsum fun n => mul_le_mul_right (hEv n) _)
    _ = ENNReal.ofReal (t*q)+ENNReal.ofReal (2*t*K/(1-2*c)) := by
      rw [← ENNReal.ofReal_mul ht, weighted_geometric_sum ht hK hc hc1]
    _ = _ := by
      rw [← ENNReal.ofReal_add (mul_nonneg ht hq) (by positivity [sub_pos.mpr hc1])]
      congr 1
      ring

end DyadicMajorant

namespace LocalCancellation
open DiskScales DiskMoments

lemma errorPrice_zero {ι : Type*} [Fintype ι] {Cs α : ℝ} (b : ι → ErrorPiece Cs)
    (hA : errorPrice b α = 0) : ∀ j, (b j).density =ᵐ[volume] 0 := by
  intro j
  have hterm : (b j).size^α*(b j).mass ≤ errorPrice b α :=
    Finset.single_le_sum (fun k _ => mul_nonneg (Real.rpow_nonneg (b k).size_pos.le _) (b k).mass_nonneg) (Finset.mem_univ j)
  have hm : (b j).mass = 0 := by
    have hp := Real.rpow_pos_of_pos (b j).size_pos α
    rw [hA] at hterm
    nlinarith [(b j).mass_nonneg]
  have hz := (integral_eq_zero_iff_of_nonneg (fun y => norm_nonneg ((b j).density y)) (b j).integrable.norm).mp hm
  filter_upwards [hz] with y hy
  exact norm_eq_zero.mp hy

lemma dyadic_ratio {A L : ℝ} (hA : 0 < A) (hL : 1 ≤ L) (n : ℕ) :
    A/(L*A*2^n) ≤ (1/2 : ℝ)^n := by
  have hLA : 0 < L*A := mul_pos (by linarith) hA
  have hn : 0 < (2 : ℝ)^n := by positivity
  calc
    _ ≤ (L*A)/(L*A*2^n) := div_le_div_of_nonneg_right (le_mul_of_one_le_left hA.le hL) (mul_nonneg hLA.le hn.le)
    _ = (1/2 : ℝ)^n := by rw [div_pow]; field_simp; simp

/-- A simultaneous Borel integrable price for every admissible disk gradient.
The constant is independent of the number of pieces. -/
theorem size_majorant {Cs : ℝ} (hCs : 0 ≤ Cs) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] (b : ι → ErrorPiece Cs)
      (g : ℂ → ℝ), ContDiff ℝ 1 g → ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
      ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
        (∫⁻ x in Q, F x) ≤ ENNReal.ofReal (C*errorPrice b (1/100)) ∧
        ∀ x, (∀ᵐ y, y ∈ Metric.ball x 3 → ∑ j, (b j).density y = gradient g y) →
          ∀ r, EndpointRadius g x r →
            ENNReal.ofReal ‖∫ y in Metric.ball x r, gradient g y‖ ≤ F x := by
  obtain ⟨L,hL,hsize⟩ := size_tail hCs
  let c : ℝ := (1/2 : ℝ)^(34/25 : ℝ)
  have hc : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hc1 : 2*c < 1 := by
    have hh := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1/2)
      (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 34/25)
    norm_num at hh
    linarith
  let C := L*(1+2*sizeTailConstant/(1-2*c))
  have hC : 0 < C := mul_pos (by linarith) (by
    have := sizeTailConstant_pos
    have := sub_pos.mpr hc1
    positivity)
  refine ⟨C,hC,?_⟩
  intro ι _ b g hg Q hQ
  let A := errorPrice b (1/100)
  by_cases hAz : A = 0
  · refine ⟨0,measurable_const,?_,?_⟩
    · simp only [Pi.zero_apply, lintegral_zero, A, hAz, mul_zero, ENNReal.ofReal_zero, le_refl]
    · intro x hh r hr
      have hz := errorPrice_zero b hAz
      have hs : (∑ j, ∫ y in Metric.ball x r, (b j).density y) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        exact integral_eq_zero_of_ae ((ae_restrict_of_ae (hz j)))
      have he := ball_pairing_decomposition b x (by linarith [hr.1.2] : r ≤ 3) hh
      rw [← he,hs,norm_zero,ENNReal.ofReal_zero]
      exact le_refl _
  · have hA : 0 < A := lt_of_le_of_ne (errorPrice_nonneg b _) (Ne.symm hAz)
    have ht : 0 < L*A := mul_pos (by linarith) hA
    have hts (n : ℕ) : L*A ≤ L*A*2^n := le_mul_of_one_le_right ht.le (one_le_pow₀ (by norm_num))
    choose E hE hEv hbound using fun n : ℕ => hsize b hA (L*A*2^n) (hts n) g hg
    refine ⟨DyadicMajorant.price (L*A) E, DyadicMajorant.measurable_price _ hE,?_,?_⟩
    · have htail (n : ℕ) : volume (E n) ≤ ENNReal.ofReal (sizeTailConstant*c^n) := by
        apply (hEv n).trans
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ sizeTailConstant_pos.le
        calc
          _ ≤ ((1/2 : ℝ)^n)^(34/25 : ℝ) := Real.rpow_le_rpow (by positivity) (dyadic_ratio hA hL n) (by norm_num)
          _ = c^n := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm (n : ℝ),
              Real.rpow_mul (by norm_num), Real.rpow_natCast]
      have hi := DyadicMajorant.lintegral_price_geometric volume (by norm_num : (0 : ℝ) ≤ 1) hQ ht.le
        sizeTailConstant_pos.le hc hc1 hE htail
      convert hi using 1
      congr 1
      dsimp [C,A]
      ring
    · intro x hh r hr
      apply DyadicMajorant.majorizes ht
      intro n hn
      exact hbound n x hn hh r hr

end LocalCancellation

end SignedDisk

end

end OAI
