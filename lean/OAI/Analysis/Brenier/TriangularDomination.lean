import OAI.Analysis.Brenier.Midpoint
import OAI.Analysis.Brenier.TriangularSampling

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358.TriangularDomination

/-- A weighted change of variables that only needs an upper change-of-variables bound. -/
def WeightedDomination {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (F : A → B) (J : A → ℝ≥0∞) : Prop :=
  ∀ w : B → ℝ≥0∞, Measurable w →
    (∫⁻ a, J a * w (F a) ∂μ) ≤ ∫⁻ b, w b ∂ν

/-- A measure-preserving coordinate change has unit weight. -/
theorem weightedDomination_of_measurePreserving
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {F : A → B}
    (hF : MeasurePreserving F μ ν) :
    WeightedDomination μ ν F (fun _ => 1) := by
  intro w hw
  simpa using (hF.lintegral_comp hw).le

/-- Weighted domination composes, multiplying the two Jacobian weights. This also
allows measure-preserving coordinate identifications to be inserted on either side. -/
theorem WeightedDomination.comp
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure A} {ν : Measure B} {ρ : Measure C}
    {F : A → B} {G : B → C} {J : A → ℝ≥0∞} {K : B → ℝ≥0∞}
    (hF : WeightedDomination μ ν F J) (hG : WeightedDomination ν ρ G K)
    (hGmeas : Measurable G) (hK : Measurable K) :
    WeightedDomination μ ρ (G ∘ F) (fun a => J a * K (F a)) := by
  intro w hw
  calc
    _ = ∫⁻ a, J a * (K (F a) * w (G (F a))) ∂μ := by
      simp_rw [Function.comp_apply, mul_assoc]
    _ ≤ ∫⁻ b, K b * w (G b) ∂ν := hF _ (hK.mul (hw.comp hGmeas))
    _ ≤ ∫⁻ c, w c ∂ρ := hG w hw

/-- One genuine induction step for triangular changes of variables. The last output
coordinate may depend on every preceding input coordinate, but the preceding output
coordinates do not depend on the last input coordinate. No joint differentiability is
needed: measurable weights and the two lower-dimensional integral bounds suffice. -/
theorem WeightedDomination.triangular_ae
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure A} {ν : Measure B} {ρ : Measure C} {σ : Measure D}
    [SFinite ρ] [SFinite σ]
    {F : A → B} {G : A → C → D}
    {J : A → ℝ≥0∞} {j : A → C → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable (fun p : A × C => G p.1 p.2))
    (hJ : Measurable J) (hj : Measurable (fun p : A × C => j p.1 p.2))
    (hbase : WeightedDomination μ ν F J)
    (hfiber : ∀ᵐ a ∂μ, WeightedDomination ρ σ (G a) (j a)) :
    WeightedDomination (μ.prod ρ) (ν.prod σ)
      (fun p : A × C => (F p.1, G p.1 p.2))
      (fun p : A × C => J p.1 * j p.1 p.2) := by
  intro w hw
  have hmap : Measurable (fun p : A × C => (F p.1, G p.1 p.2)) :=
    (hF.comp measurable_fst).prodMk hG
  have hweight : Measurable (fun p : A × C => J p.1 * j p.1 p.2) :=
    (hJ.comp measurable_fst).mul hj
  have htotal : Measurable (fun p : A × C =>
      (J p.1 * j p.1 p.2) * w (F p.1, G p.1 p.2)) :=
    hweight.mul (hw.comp hmap)
  change (∫⁻ p : A × C, (J p.1 * j p.1 p.2) * w (F p.1, G p.1 p.2) ∂μ.prod ρ) ≤ _
  rw [lintegral_prod _ htotal.aemeasurable,
    lintegral_prod _ hw.aemeasurable]
  calc
    _ = ∫⁻ a, J a * (∫⁻ c, j a c * w (F a, G a c) ∂ρ) ∂μ := by
      apply lintegral_congr
      intro a
      have hj' : Measurable (j a) := hj.comp (measurable_const.prodMk measurable_id)
      have hG' : Measurable (G a) := hG.comp (measurable_const.prodMk measurable_id)
      simp only [mul_assoc]
      exact lintegral_const_mul _ (hj'.mul (hw.comp (measurable_const.prodMk hG')))
    _ ≤ ∫⁻ a, J a * (∫⁻ d, w (F a, d) ∂σ) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hfiber] with a ha
      exact mul_le_mul_right (ha _
        (hw.comp (measurable_const.prodMk measurable_id))) (J a)
    _ ≤ ∫⁻ b, ∫⁻ d, w (b, d) ∂σ ∂ν :=
      hbase _ hw.lintegral_prod_right'

/-- Everywhere fiber bounds specialize the almost-everywhere product theorem. -/
theorem WeightedDomination.triangular
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure A} {ν : Measure B} {ρ : Measure C} {σ : Measure D}
    [SFinite ρ] [SFinite σ]
    {F : A → B} {G : A → C → D}
    {J : A → ℝ≥0∞} {j : A → C → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable (fun p : A × C => G p.1 p.2))
    (hJ : Measurable J) (hj : Measurable (fun p : A × C => j p.1 p.2))
    (hbase : WeightedDomination μ ν F J)
    (hfiber : ∀ a, WeightedDomination ρ σ (G a) (j a)) :
    WeightedDomination (μ.prod ρ) (ν.prod σ)
      (fun p : A × C => (F p.1, G p.1 p.2))
      (fun p : A × C => J p.1 * j p.1 p.2) := by
  exact hbase.triangular_ae hF hG hJ hj (Filter.Eventually.of_forall hfiber)

/-- A pointwise smaller weight preserves the integral domination. -/
theorem WeightedDomination.mono_weight
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {F : A → B} {J K : A → ℝ≥0∞}
    (h : WeightedDomination μ ν F J) (hK : K ≤ᵐ[μ] J) :
    WeightedDomination μ ν F K := by
  intro w hw
  apply le_trans _ (h w hw)
  apply lintegral_mono_ae
  filter_upwards [hK] with a ha
  exact mul_le_mul_left ha (w (F a))

/-- Integral domination gives the expected domination of weighted image measures. -/
theorem WeightedDomination.map_withDensity_le
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {F : A → B} {J : A → ℝ≥0∞}
    (h : WeightedDomination μ ν F J) (hF : Measurable F) :
    Measure.map F (μ.withDensity J) ≤ ν := by
  apply Measure.le_iff.mpr
  intro s hs
  have htest := h (s.indicator (fun _ => 1)) (measurable_const.indicator hs)
  have heq : (fun a => J a * s.indicator (fun _ => (1 : ℝ≥0∞)) (F a)) =
      (F ⁻¹' s).indicator J := by
    funext a
    by_cases ha : F a ∈ s <;> simp [ha]
  rw [heq, lintegral_indicator (hs.preimage hF), lintegral_indicator hs] at htest
  rw [Measure.map_apply hF hs, withDensity_apply _ (hs.preimage hF)]
  simpa using htest

/-- A uniform lower Jacobian bound gives the unweighted pushforward bound. -/
theorem WeightedDomination.smul_map_le
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {F : A → B} {J : A → ℝ≥0∞}
    (h : WeightedDomination μ ν F J) (hF : Measurable F)
    {c : ℝ≥0∞} (hc : ∀ᵐ a ∂μ, c ≤ J a) :
    c • Measure.map F μ ≤ ν := by
  have h' := (h.mono_weight hc).map_withDensity_le hF
  simpa [withDensity_const, Measure.map_smul _ hF.aemeasurable] using h'

/-- The product arithmetic-geometric-mean bound needed for diagonal derivatives of
midpoints of triangular maps. Zero derivatives are allowed. -/
theorem sqrt_prod_mul_prod_le_prod_midpoint
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    Real.sqrt ((∏ i ∈ s, a i) * ∏ i ∈ s, b i) ≤
      ∏ i ∈ s, (a i + b i) / 2 := by
  have hsq : (∏ i ∈ s, a i) * (∏ i ∈ s, b i) ≤
      (∏ i ∈ s, (a i + b i) / 2) ^ 2 := by
    have h := Finset.prod_le_prod₀
      (fun i hi => mul_nonneg (ha i hi) (hb i hi))
      (fun i hi => (show a i * b i ≤ ((a i + b i) / 2) ^ 2 by
        nlinarith [sq_nonneg (a i - b i)]))
    simpa only [Finset.prod_mul_distrib, Finset.prod_pow] using h
  have hnonneg : 0 ≤ ∏ i ∈ s, (a i + b i) / 2 :=
    Finset.prod_nonneg (fun i hi => div_nonneg (add_nonneg (ha i hi) (hb i hi)) (by norm_num))
  have hab : 0 ≤ (∏ i ∈ s, a i) * ∏ i ∈ s, b i :=
    mul_nonneg (Finset.prod_nonneg ha) (Finset.prod_nonneg hb)
  have hsqrt := Real.sq_sqrt hab
  have hsqrt0 := Real.sqrt_nonneg ((∏ i ∈ s, a i) * ∏ i ∈ s, b i)
  nlinarith

end Problem358.TriangularDomination

end

/-! The measurable geometric Jacobian weight for two finite triangular samplers.
The weight is defined globally, but its identification with the geometric mean
of diagonal products only uses positivity on valid sampling parameters. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open Problem358.TriangularRecursion

namespace Problem358.TriangularDensity

/-- Product of the geometric means of the paired longitudinal derivatives. -/
def geometricWeight (q r dq dr : ConditionalFamily) :
    (n : ℕ) → Coordinates n → ℝ≥0∞
  | 0, _ => 1
  | n + 1, u => geometricWeight q r dq dr n (Fin.init u) *
      ENNReal.ofReal (Real.sqrt
        (dq n (sample q n (Fin.init u)) (u (Fin.last n)) *
         dr n (sample r n (Fin.init u)) (u (Fin.last n))))

@[simp] theorem geometricWeight_zero (q r dq dr : ConditionalFamily)
    (u : Coordinates 0) : geometricWeight q r dq dr 0 u = 1 := rfl

@[simp] theorem geometricWeight_snoc (q r dq dr : ConditionalFamily) (n : ℕ)
    (s : Coordinates n) (t : ℝ) :
    geometricWeight q r dq dr (n + 1) (Fin.snoc s t) =
      geometricWeight q r dq dr n s * ENNReal.ofReal (Real.sqrt
        (dq n (sample q n s) t * dr n (sample r n s) t)) := by
  simp only [geometricWeight, Fin.init_snoc, Fin.snoc_last]

/-- Measurability requires no sign conditions or information above the cutoff. -/
theorem measurable_geometricWeight_of_le (q r dq dr : ConditionalFamily) (N : ℕ)
    (hQ : ∀ n, n ≤ N → Measurable (sample q n))
    (hR : ∀ n, n ≤ N → Measurable (sample r n))
    (hD : ∀ n, n < N → Measurable (fun p : Coordinates n × ℝ => dq n p.1 p.2))
    (hE : ∀ n, n < N → Measurable (fun p : Coordinates n × ℝ => dr n p.1 p.2)) :
    ∀ n, n ≤ N → Measurable (geometricWeight q r dq dr n) := by
  intro n
  induction n with
  | zero => intro _; exact measurable_const
  | succ n ih =>
      intro hn
      have hnle : n ≤ N := by omega
      have hnlt : n < N := by omega
      have hi : Measurable (fun u : Coordinates (n + 1) => Fin.init u) := by
        apply Measurable.of_eval
        intro i
        exact measurable_pi_apply i.castSucc
      have hd := (hD n hnlt).comp
        (((hQ n hnle).comp hi).prodMk (measurable_pi_apply (Fin.last n)))
      have he := (hE n hnlt).comp
        (((hR n hnle).comp hi).prodMk (measurable_pi_apply (Fin.last n)))
      exact ((ih hnle).comp hi).mul ((hd.mul he).sqrt.ennreal_ofReal)

/-- On the open parameter cube, the geometric weight is exactly the geometric
mean of both diagonal derivative products. This is deliberately not claimed
outside the cube, where the supplied derivative fields need not be positive. -/
theorem geometricWeight_eq_ofReal_sqrt_diagonalProduct
    (q r dq dr : ConditionalFamily) (N : ℕ)
    (hD : ∀ n, n < N → ∀ u, InUnitCube u → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dq n (sample q n u) t)
    (hE : ∀ n, n < N → ∀ u, InUnitCube u → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dr n (sample r n u) t) :
    ∀ n, n ≤ N → ∀ u, InUnitCube u →
      geometricWeight q r dq dr n u = ENNReal.ofReal (Real.sqrt
        (diagonalProduct q dq n u * diagonalProduct r dr n u)) := by
  intro n
  induction n with
  | zero =>
      intro hn u hu
      simp only [geometricWeight, diagonalProduct, mul_one, Real.sqrt_one, ENNReal.ofReal_one]
  | succ n ih =>
      intro hn u hu
      have hnle : n ≤ N := by omega
      have hp : 0 ≤ diagonalProduct q dq n (Fin.init u) *
          diagonalProduct r dr n (Fin.init u) :=
        (mul_pos (diagonalProduct_pos_of_le q dq N hD n hnle _ hu.init)
          (diagonalProduct_pos_of_le r dr N hE n hnle _ hu.init)).le
      rw [geometricWeight, ih hnle _ hu.init]
      rw [diagonalProduct, diagonalProduct]
      have hreorder :
          (diagonalProduct q dq n (Fin.init u) *
            dq n (sample q n (Fin.init u)) (u (Fin.last n))) *
          (diagonalProduct r dr n (Fin.init u) *
            dr n (sample r n (Fin.init u)) (u (Fin.last n))) =
          (diagonalProduct q dq n (Fin.init u) *
            diagonalProduct r dr n (Fin.init u)) *
          (dq n (sample q n (Fin.init u)) (u (Fin.last n)) *
            dr n (sample r n (Fin.init u)) (u (Fin.last n))) := by ring
      rw [hreorder, Real.sqrt_mul hp, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

/-- Constant terminal products turn the Jacobian into a constant almost
certainly, exactly the normalization needed by midpoint measure domination. -/
theorem geometricWeight_ae_eq_constant
    (q r dq dr : ConditionalFamily) (N : ℕ) (A B : ℝ)
    (hD : ∀ n, n < N → ∀ u, InUnitCube u → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dq n (sample q n u) t)
    (hE : ∀ n, n < N → ∀ u, InUnitCube u → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dr n (sample r n u) t)
    (hA : ∀ u, InUnitCube u → diagonalProduct q dq N u = A)
    (hB : ∀ u, InUnitCube u → diagonalProduct r dr N u = B) :
    ∀ᵐ u ∂(Measure.pi fun _ : Fin N =>
      (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)),
      geometricWeight q r dq dr N u = ENNReal.ofReal (Real.sqrt (A * B)) := by
  filter_upwards [ae_inUnitCube N] with u hu
  rw [geometricWeight_eq_ofReal_sqrt_diagonalProduct q r dq dr N hD hE N
    (le_refl N) u hu, hA u hu, hB u hu]

end Problem358.TriangularDensity

end

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem358.TriangularDomination

/-- Weighted substitution for every finite dimension from measurable triangular
recursion and almost-everywhere one-dimensional fiber substitution. The maps and
weights are supplied explicitly; no quantile existence is assumed implicitly. -/
theorem weightedDomination_triangular_recursion
    (η : Measure ℝ) [SigmaFinite η]
    (F : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ))
    (G : (n : ℕ) → ((Fin n → ℝ) × ℝ) → ℝ)
    (J : (n : ℕ) → (Fin n → ℝ) → ℝ≥0∞)
    (j : (n : ℕ) → ((Fin n → ℝ) × ℝ) → ℝ≥0∞)
    (hF : ∀ n, Measurable (F n)) (hG : ∀ n, Measurable (G n))
    (hJ : ∀ n, Measurable (J n)) (hj : ∀ n, Measurable (j n))
    (hzero : ∀ s, J 0 s = 1)
    (hrecursion : ∀ n s t,
      F (n + 1) (Fin.snoc s t) = Fin.snoc (F n s) (G n (s, t)))
    (hweight : ∀ n s t,
      J (n + 1) (Fin.snoc s t) = J n s * j n (s, t))
    (hfiber : ∀ n, ∀ᵐ s ∂(Measure.pi fun _ : Fin n => η),
      WeightedDomination η volume (fun t => G n (s, t)) (fun t => j n (s, t))) :
    ∀ n, WeightedDomination (Measure.pi fun _ : Fin n => η)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) (F n) (J n) := by
  intro n
  induction n with
  | zero =>
    intro w hw
    have hmap : F 0 = id := by
      funext s
      exact Subsingleton.elim _ _
    have hmeasure : (Measure.pi fun _ : Fin 0 => η) =
        (Measure.pi fun _ : Fin 0 => (volume : Measure ℝ)) := by
      congr 1
      funext i
      exact Fin.elim0 i
    simp only [hzero, one_mul, hmap, id_eq, hmeasure, le_refl]
  | succ n ih =>
    intro w hw
    have hsource := measurePreserving_finSnoc n η
    have htarget := measurePreserving_finSnoc n (volume : Measure ℝ)
    have hdom := ih.triangular_ae
      (G := fun s t => G n (s, t)) (j := fun s t => j n (s, t))
      (hF n) (hG n) (hJ n) (hj n) (hfiber n)
    have hw' : Measurable (fun p : (Fin n → ℝ) × ℝ => w (Fin.snoc p.1 p.2)) :=
      hw.comp htarget.measurable
    have hbound := hdom _ hw'
    have hsourceIntegral := hsource.lintegral_comp
      ((hJ (n + 1)).mul (hw.comp (hF (n + 1))))
    have htargetIntegral := htarget.lintegral_comp hw
    change (∫⁻ p : (Fin n → ℝ) × ℝ,
      J (n + 1) (Fin.snoc p.1 p.2) * w (F (n + 1) (Fin.snoc p.1 p.2))
        ∂(Measure.pi fun _ : Fin n => η).prod η) = _ at hsourceIntegral
    simp_rw [hweight, hrecursion] at hsourceIntegral
    exact hsourceIntegral.symm.trans_le (hbound.trans_eq htargetIntegral)

/-- Finite-cutoff version: no maps, derivatives, or substitution bounds beyond
the requested ambient dimension need to satisfy any hypotheses. -/
theorem weightedDomination_triangular_recursion_of_le
    (N : ℕ)
    (η : Measure ℝ) [SigmaFinite η]
    (F : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ))
    (G : (n : ℕ) → ((Fin n → ℝ) × ℝ) → ℝ)
    (J : (n : ℕ) → (Fin n → ℝ) → ℝ≥0∞)
    (j : (n : ℕ) → ((Fin n → ℝ) × ℝ) → ℝ≥0∞)
    (hF : ∀ n, n ≤ N → Measurable (F n))
    (hG : ∀ n, n < N → Measurable (G n))
    (hJ : ∀ n, n ≤ N → Measurable (J n))
    (hj : ∀ n, n < N → Measurable (j n))
    (hzero : ∀ s, J 0 s = 1)
    (hrecursion : ∀ n, n < N → ∀ s t,
      F (n + 1) (Fin.snoc s t) = Fin.snoc (F n s) (G n (s, t)))
    (hweight : ∀ n, n < N → ∀ s t,
      J (n + 1) (Fin.snoc s t) = J n s * j n (s, t))
    (hfiber : ∀ n, n < N → ∀ᵐ s ∂(Measure.pi fun _ : Fin n => η),
      WeightedDomination η volume (fun t => G n (s, t)) (fun t => j n (s, t))) :
    ∀ n, n ≤ N → WeightedDomination (Measure.pi fun _ : Fin n => η)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) (F n) (J n) := by
  intro n
  induction n with
  | zero =>
    intro _ w hw
    have hmap : F 0 = id := by
      funext s
      exact Subsingleton.elim _ _
    have hmeasure : (Measure.pi fun _ : Fin 0 => η) =
        (Measure.pi fun _ : Fin 0 => (volume : Measure ℝ)) := by
      congr 1
      funext i
      exact Fin.elim0 i
    simp only [hzero, one_mul, hmap, id_eq, hmeasure, le_refl]
  | succ n ih =>
    intro hn w hw
    have hnlt : n < N := by omega
    have hnle : n ≤ N := by omega
    have ih := ih hnle
    have hsource := measurePreserving_finSnoc n η
    have htarget := measurePreserving_finSnoc n (volume : Measure ℝ)
    have hdom := ih.triangular_ae
      (G := fun s t => G n (s, t)) (j := fun s t => j n (s, t))
      (hF n hnle) (hG n hnlt) (hJ n hnle) (hj n hnlt) (hfiber n hnlt)
    have hw' : Measurable (fun p : (Fin n → ℝ) × ℝ => w (Fin.snoc p.1 p.2)) :=
      hw.comp htarget.measurable
    have hbound := hdom _ hw'
    have hsourceIntegral := hsource.lintegral_comp
      ((hJ (n + 1) hn).mul (hw.comp (hF (n + 1) hn)))
    have htargetIntegral := htarget.lintegral_comp hw
    change (∫⁻ p : (Fin n → ℝ) × ℝ,
      J (n + 1) (Fin.snoc p.1 p.2) * w (F (n + 1) (Fin.snoc p.1 p.2))
        ∂(Measure.pi fun _ : Fin n => η).prod η) = _ at hsourceIntegral
    simp_rw [hweight n hnlt, hrecursion n hnlt] at hsourceIntegral
    exact hsourceIntegral.symm.trans_le (hbound.trans_eq htargetIntegral)

end Problem358.TriangularDomination

end

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Problem358.TriangularDomination

/-- Extend a weighted triangular change of variables by one midpoint coordinate.
The fiber functions need derivatives only in their last variable, not in parameters. -/
theorem WeightedDomination.midpoint_fiber
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B}
    {F : A → B} {J : A → ℝ≥0∞}
    {s : Set ℝ} {X Z X' Z' : A → ℝ → ℝ}
    (hs : MeasurableSet s) (hconv : Convex ℝ s)
    (hF : Measurable F) (hJ : Measurable J)
    (hX : Measurable (fun p : A × ℝ => X p.1 p.2))
    (hZ : Measurable (fun p : A × ℝ => Z p.1 p.2))
    (hX' : Measurable (fun p : A × ℝ => X' p.1 p.2))
    (hZ' : Measurable (fun p : A × ℝ => Z' p.1 p.2))
    (hderivX : ∀ a t, t ∈ s → HasDerivWithinAt (X a) (X' a t) s t)
    (hderivZ : ∀ a t, t ∈ s → HasDerivWithinAt (Z a) (Z' a t) s t)
    (hposX : ∀ a t, t ∈ s → 0 < X' a t)
    (hposZ : ∀ a t, t ∈ s → 0 < Z' a t)
    (hbase : WeightedDomination μ ν F J) :
    WeightedDomination (μ.prod (volume.restrict s)) (ν.prod volume)
      (fun p : A × ℝ => (F p.1, (X p.1 p.2 + Z p.1 p.2) / 2))
      (fun p : A × ℝ => J p.1 *
        ENNReal.ofReal (Real.sqrt (X' p.1 p.2 * Z' p.1 p.2))) := by
  refine WeightedDomination.triangular
    (ρ := volume.restrict s) (σ := volume)
    (G := fun a t => (X a t + Z a t) / 2)
    (j := fun a t => ENNReal.ofReal (Real.sqrt (X' a t * Z' a t)))
    hF ?_ hJ ?_ hbase ?_
  · exact (hX.add hZ).div_const 2
  · exact ((hX'.mul hZ').sqrt).ennreal_ofReal
  · intro a w _
    exact lintegral_midpoint_geometric_jacobian_le hs hconv
      (hderivX a) (hderivZ a) (hposX a) (hposZ a) w

/-- The preceding induction step in the measure-domination form used by midpoint
couplings, once the product weight has a uniform lower bound. -/
theorem WeightedDomination.midpoint_fiber_smul_map_le
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B}
    {F : A → B} {J : A → ℝ≥0∞}
    {s : Set ℝ} {X Z X' Z' : A → ℝ → ℝ}
    (hs : MeasurableSet s) (hconv : Convex ℝ s)
    (hF : Measurable F) (hJ : Measurable J)
    (hX : Measurable (fun p : A × ℝ => X p.1 p.2))
    (hZ : Measurable (fun p : A × ℝ => Z p.1 p.2))
    (hX' : Measurable (fun p : A × ℝ => X' p.1 p.2))
    (hZ' : Measurable (fun p : A × ℝ => Z' p.1 p.2))
    (hderivX : ∀ a t, t ∈ s → HasDerivWithinAt (X a) (X' a t) s t)
    (hderivZ : ∀ a t, t ∈ s → HasDerivWithinAt (Z a) (Z' a t) s t)
    (hposX : ∀ a t, t ∈ s → 0 < X' a t)
    (hposZ : ∀ a t, t ∈ s → 0 < Z' a t)
    (hbase : WeightedDomination μ ν F J)
    {c : ℝ≥0∞}
    (hc : ∀ᵐ p : A × ℝ ∂μ.prod (volume.restrict s),
      c ≤ J p.1 * ENNReal.ofReal (Real.sqrt (X' p.1 p.2 * Z' p.1 p.2))) :
    c • Measure.map
      (fun p : A × ℝ => (F p.1, (X p.1 p.2 + Z p.1 p.2) / 2))
      (μ.prod (volume.restrict s)) ≤ ν.prod volume := by
  apply (hbase.midpoint_fiber hs hconv hF hJ hX hZ hX' hZ'
    hderivX hderivZ hposX hposZ).smul_map_le _ hc
  exact (hF.comp measurable_fst).prodMk ((hX.add hZ).div_const 2)

end Problem358.TriangularDomination

namespace Problem358.TriangularRecursion

open TriangularDensity TriangularDomination

/-- Measurability of the midpoint needs only the two samplers at the depth in
question, not any conditional functions after that depth. -/
theorem measurable_midpoint_of_samples (q r : ConditionalFamily) (n : ℕ)
    (hq : Measurable (sample q n)) (hr : Measurable (sample r n)) :
    Measurable (midpoint q r n) := by
  apply Measurable.of_eval
  intro i
  exact (((measurable_pi_apply i).comp hq).add
    ((measurable_pi_apply i).comp hr)).div_const 2

/-- Specialization of finite triangular substitution to the canonical paired
samplers. Regularity is needed only on sampled open-unit-cube prefixes. The
recursive weight is the product of geometric means of longitudinal derivatives. -/
theorem weightedDomination_midpoint_of_weight
    (q r dq dr : ConditionalFamily) (N : ℕ)
    (hq : ∀ n, n < N → Measurable (fun p : (Fin n → ℝ) × ℝ => q n p.1 p.2))
    (hr : ∀ n, n < N → Measurable (fun p : (Fin n → ℝ) × ℝ => r n p.1 p.2))
    (hdq : ∀ n, n < N → Measurable (fun p : (Fin n → ℝ) × ℝ => dq n p.1 p.2))
    (hdr : ∀ n, n < N → Measurable (fun p : (Fin n → ℝ) × ℝ => dr n p.1 p.2))
    (hsq : ∀ n, n ≤ N → Measurable (sample q n))
    (hsr : ∀ n, n ≤ N → Measurable (sample r n))
    (hderivq : ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (q n (sample q n s)) (dq n (sample q n s) t) t)
    (hderivr : ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (r n (sample r n s)) (dr n (sample r n s) t) t)
    (hposq : ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dq n (sample q n s) t)
    (hposr : ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dr n (sample r n s) t)
    (J : (n : ℕ) → (Fin n → ℝ) → ℝ≥0∞)
    (hJ : ∀ n, n ≤ N → Measurable (J n))
    (hzero : ∀ s, J 0 s = 1)
    (hweight : ∀ n, n < N → ∀ s t,
      J (n + 1) (Fin.snoc s t) = J n s * ENNReal.ofReal
        (Real.sqrt (dq n (sample q n s) t * dr n (sample r n s) t))) :
    WeightedDomination
      (Measure.pi fun _ : Fin N => volume.restrict (Ioo (0 : ℝ) 1))
      (Measure.pi fun _ : Fin N => (volume : Measure ℝ)) (midpoint q r N) (J N) := by
  apply weightedDomination_triangular_recursion_of_le N
    (volume.restrict (Ioo (0 : ℝ) 1)) (midpoint q r)
    (fun n p => midpointFiber q r n p.1 p.2) J
    (fun n p => ENNReal.ofReal (Real.sqrt
      (dq n (sample q n p.1) p.2 * dr n (sample r n p.1) p.2)))
    (fun n hn => measurable_midpoint_of_samples q r n (hsq n hn) (hsr n hn))
    ?_ hJ ?_ hzero (fun n _ s t => midpoint_snoc q r n s t) hweight ?_ N le_rfl
  · intro n hn
    exact (((hq n hn).comp (((hsq n hn.le).comp measurable_fst).prodMk
      measurable_snd)).add
      ((hr n hn).comp (((hsr n hn.le).comp measurable_fst).prodMk
      measurable_snd))).div_const 2
  · intro n hn
    exact ((((hdq n hn).comp (((hsq n hn.le).comp measurable_fst).prodMk
      measurable_snd)).mul
      ((hdr n hn).comp (((hsr n hn.le).comp measurable_fst).prodMk
      measurable_snd))).sqrt).ennreal_ofReal
  · intro n hn
    filter_upwards [TriangularDensity.ae_inUnitCube n] with s hs
    intro w _
    exact lintegral_midpoint_geometric_jacobian_le measurableSet_Ioo (convex_Ioo 0 1)
      (fun t ht => (hderivq n hn s hs t ht).hasDerivWithinAt)
      (fun t ht => (hderivr n hn s hs t ht).hasDerivWithinAt)
      (hposq n hn s hs) (hposr n hn s hs) w

/-- Canonical finite-dimensional midpoint domination. The only quantitative
input is the two constant terminal diagonal products; all weighted substitution
and measurable-Jacobian conditions are discharged from the scalar data. -/
theorem midpoint_smul_map_le_of_diagonalProducts
    (q r dq dr : ConditionalFamily) (N : ℕ) (A B : ℝ)
    (hq : ∀ n, n < N → Measurable (fun p : (Fin n → ℝ) × ℝ => q n p.1 p.2))
    (hr : ∀ n, n < N → Measurable (fun p : (Fin n → ℝ) × ℝ => r n p.1 p.2))
    (hdq : ∀ n, n < N → Measurable (fun p : (Fin n → ℝ) × ℝ => dq n p.1 p.2))
    (hdr : ∀ n, n < N → Measurable (fun p : (Fin n → ℝ) × ℝ => dr n p.1 p.2))
    (hsq : ∀ n, n ≤ N → Measurable (sample q n))
    (hsr : ∀ n, n ≤ N → Measurable (sample r n))
    (hderivq : ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (q n (sample q n s)) (dq n (sample q n s) t) t)
    (hderivr : ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (r n (sample r n s)) (dr n (sample r n s) t) t)
    (hposq : ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dq n (sample q n s) t)
    (hposr : ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dr n (sample r n s) t)
    (hA : ∀ s, InUnitCube s → diagonalProduct q dq N s = A)
    (hB : ∀ s, InUnitCube s → diagonalProduct r dr N s = B) :
    ENNReal.ofReal (Real.sqrt (A * B)) •
      Measure.map (midpoint q r N)
        (Measure.pi fun _ : Fin N => volume.restrict (Ioo (0 : ℝ) 1)) ≤
      Measure.pi fun _ : Fin N => (volume : Measure ℝ) := by
  have hdom := weightedDomination_midpoint_of_weight q r dq dr N
    hq hr hdq hdr hsq hsr hderivq hderivr hposq hposr
    (geometricWeight q r dq dr)
    (measurable_geometricWeight_of_le q r dq dr N hsq hsr hdq hdr)
    (geometricWeight_zero q r dq dr)
    (fun n _ s t => geometricWeight_snoc q r dq dr n s t)
  apply hdom.smul_map_le
    (measurable_midpoint_of_samples q r N (hsq N le_rfl) (hsr N le_rfl))
  filter_upwards [geometricWeight_ae_eq_constant q r dq dr N A B hposq hposr hA hB]
    with s hs
  exact hs.ge

end Problem358.TriangularRecursion

end

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open Problem358.TriangularRecursion

namespace Problem358.TriangularDensity

/-- The derivative dictated by successive conditional section densities.
It is defined on all prefixes, including invalid prefixes of density zero. -/
def densityRatio (q : ConditionalFamily) (p : (n : ℕ) → Coordinates n → ℝ) :
    ConditionalFamily :=
  fun n x t => p n x / p (n + 1) (Fin.snoc x (q n x t))

/-- The ratio derivative field is jointly measurable using only the finite
collection of section densities involved in the sampler. -/
theorem measurable_densityRatio_of_le
    (q : ConditionalFamily) (p : (n : ℕ) → Coordinates n → ℝ) (N : ℕ)
    (hq : ∀ n, n < N → Measurable (fun z : Coordinates n × ℝ => q n z.1 z.2))
    (hp : ∀ n, n ≤ N → Measurable (p n)) :
    ∀ n, n < N → Measurable (fun z : Coordinates n × ℝ =>
      densityRatio q p n z.1 z.2) := by
  intro n hn
  apply ((hp n hn.le).comp measurable_fst).div
  apply (hp (n + 1) (Nat.succ_le_iff.mpr hn)).comp
  exact (measurePreserving_finSnoc n (volume : Measure ℝ)).measurable.comp
    (measurable_fst.prodMk (hq n hn))

/-- Positivity of section densities propagates to the conditional derivative
at every valid sampled prefix. -/
theorem densityRatio_pos_on_sampled_prefixes
    (q : ConditionalFamily) (D : (n : ℕ) → Set (Coordinates n))
    (p : (n : ℕ) → Coordinates n → ℝ) (N : ℕ)
    (hzero : (fun i => Fin.elim0 i) ∈ D 0)
    (hstep : ∀ n, n < N → ∀ x, x ∈ D n → ∀ t ∈ Ioo (0 : ℝ) 1,
      Fin.snoc x (q n x t) ∈ D (n + 1))
    (hp : ∀ n, n ≤ N → ∀ x, x ∈ D n → 0 < p n x) :
    ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < densityRatio q p n (sample q n s) t := by
  intro n hn s hs t ht
  have hx := sample_mem_domains_of_le q D N hzero hstep n hn.le s hs
  exact div_pos (hp n hn.le _ hx)
    (hp (n + 1) (Nat.succ_le_iff.mpr hn) _ (hstep n hn _ hx t ht))

/-- Exact telescoping of the measurable ratio field, with the terminal density
one on every valid terminal prefix. -/
theorem diagonalProduct_densityRatio_eq_initial
    (q : ConditionalFamily) (D : (n : ℕ) → Set (Coordinates n))
    (p : (n : ℕ) → Coordinates n → ℝ) (N : ℕ)
    (hzero : (fun i => Fin.elim0 i) ∈ D 0)
    (hstep : ∀ n, n < N → ∀ x, x ∈ D n → ∀ t ∈ Ioo (0 : ℝ) 1,
      Fin.snoc x (q n x t) ∈ D (n + 1))
    (hp : ∀ n, n ≤ N → ∀ x, x ∈ D n → 0 < p n x)
    (hterminal : ∀ x ∈ D N, p N x = 1) :
    ∀ s, InUnitCube s → diagonalProduct q (densityRatio q p) N s =
      p 0 (fun i => Fin.elim0 i) := by
  exact diagonalProduct_eq_initial_density q (densityRatio q p) D p N hzero hstep
    (fun n hn x hx => (hp n hn x hx).ne') (fun _ _ _ _ _ _ => rfl) hterminal

/-- For two geometric section-density families, positive conditional quantile
derivatives and terminal density one imply the full midpoint domination.
No independently measurable derivative field or Jacobian identity is required. -/
theorem midpoint_smul_map_le_of_density_ratios
    (q r : ConditionalFamily) (D E : (n : ℕ) → Set (Coordinates n))
    (p v : (n : ℕ) → Coordinates n → ℝ) (N : ℕ)
    (hq : ∀ n, n < N → Measurable (fun z : Coordinates n × ℝ => q n z.1 z.2))
    (hr : ∀ n, n < N → Measurable (fun z : Coordinates n × ℝ => r n z.1 z.2))
    (hp : ∀ n, n ≤ N → Measurable (p n))
    (hv : ∀ n, n ≤ N → Measurable (v n))
    (hsq : ∀ n, n ≤ N → Measurable (sample q n))
    (hsr : ∀ n, n ≤ N → Measurable (sample r n))
    (hDzero : (fun i => Fin.elim0 i) ∈ D 0)
    (hEzero : (fun i => Fin.elim0 i) ∈ E 0)
    (hDstep : ∀ n, n < N → ∀ x, x ∈ D n → ∀ t ∈ Ioo (0 : ℝ) 1,
      Fin.snoc x (q n x t) ∈ D (n + 1))
    (hEstep : ∀ n, n < N → ∀ x, x ∈ E n → ∀ t ∈ Ioo (0 : ℝ) 1,
      Fin.snoc x (r n x t) ∈ E (n + 1))
    (hppos : ∀ n, n ≤ N → ∀ x, x ∈ D n → 0 < p n x)
    (hvpos : ∀ n, n ≤ N → ∀ x, x ∈ E n → 0 < v n x)
    (hpterminal : ∀ x ∈ D N, p N x = 1)
    (hvterminal : ∀ x ∈ E N, v N x = 1)
    (hderivq : ∀ n, n < N → ∀ x, x ∈ D n → ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (q n x) (p n x / p (n + 1) (Fin.snoc x (q n x t))) t)
    (hderivr : ∀ n, n < N → ∀ x, x ∈ E n → ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (r n x) (v n x / v (n + 1) (Fin.snoc x (r n x t))) t) :
    ENNReal.ofReal (Real.sqrt
      (p 0 (fun i => Fin.elim0 i) * v 0 (fun i => Fin.elim0 i))) •
      Measure.map (midpoint q r N)
        (Measure.pi fun _ : Fin N => volume.restrict (Ioo (0 : ℝ) 1)) ≤
      Measure.pi fun _ : Fin N => (volume : Measure ℝ) := by
  apply midpoint_smul_map_le_of_diagonalProducts q r (densityRatio q p) (densityRatio r v)
    N (p 0 (fun i => Fin.elim0 i)) (v 0 (fun i => Fin.elim0 i)) hq hr
    (measurable_densityRatio_of_le q p N hq hp)
    (measurable_densityRatio_of_le r v N hr hv) hsq hsr
    ?_ ?_
    (densityRatio_pos_on_sampled_prefixes q D p N hDzero hDstep hppos)
    (densityRatio_pos_on_sampled_prefixes r E v N hEzero hEstep hvpos)
    (diagonalProduct_densityRatio_eq_initial q D p N hDzero hDstep hppos hpterminal)
    (diagonalProduct_densityRatio_eq_initial r E v N hEzero hEstep hvpos hvterminal)
  · intro n hn s hs t ht
    exact hderivq n hn _ (sample_mem_domains_of_le q D N hDzero hDstep n hn.le s hs) t ht
  · intro n hn s hs t ht
    exact hderivr n hn _ (sample_mem_domains_of_le r E N hEzero hEstep n hn.le s hs) t ht

end Problem358.TriangularDensity

end

end OAI
