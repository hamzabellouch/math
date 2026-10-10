import OAI.NumberTheory.DirichletL.Descent.MarkBounds

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InversePrincipalEnergy
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open SecondPassArithmetic FirstPassCubeLabels IdealMobiusDivisorSum
open InverseMoment
local notation "Eis" => ActualEisensteinCubic.O

section
variable {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in

theorem zero_norm_le (F : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1)
    (m c d : Eis) (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 ≤ Y)
    (K : Finset ι → Finset ι → Finset Eis)
    (hzero : ∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : Eis) ∈ K G E) :
    ‖truncatedSecondZero p hg F Ψ m c d H W Y K‖ ≤
      Y * ‖paperRadialFourier W 0‖ * ∑ G ∈ F.powerset, ‖H G‖ ^ 2 := by
  apply (truncatedSecondZero_norm_le p hg hinj F Ψ m c d H W Y K hzero).trans
  rw [abs_of_nonneg hY]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hY (norm_nonneg _))
  exact Finset.sum_le_sum (fun G _ => pow_le_pow_left₀ (norm_nonneg _)
    (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d H G) 2)

def supportIdeal (G : Finset ι) : Ideal Eis := ∏ i ∈ G, Ideal.span {p i}

omit [DecidableEq ι] in
lemma supportIdeal_ne_zero (G : Finset ι) : supportIdeal p G ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (Ideal.span {p i}))

omit [DecidableEq ι] in
lemma supportIdeal_norm_pos (G : Finset ι) : 0 < (Ideal.absNorm (supportIdeal p G) : ℝ) := by
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (supportIdeal_ne_zero p G))

include hinj in

theorem mask_card_le_divisors (G : Finset ι) :
    G.powerset.card ≤ (idealDivisors (supportIdeal p G)).card := by
  apply Finset.card_le_card_of_injOn (supportIdeal p)
  · intro E hE
    apply (mem_idealDivisors (supportIdeal_ne_zero p G)).mpr
    exact Finset.prod_dvd_prod_of_subset E G (fun i => Ideal.span {p i}) (Finset.mem_powerset.mp hE)
  · intro E _ D _ h
    exact FirstCauchyArithmetic.family_product_injective (fun i => Ideal.span {p i}) hinj h

def principalFrequency (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ((Y : ℂ) / (‖eisEmbedding (∏ i ∈ (∅ : Finset ι) ∪ ∅, p i)‖ : ℂ)) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * primeProductNorm p ((∅ : Finset ι) ∪ ∅))) *
    secondGaussTerm p hp hg hinj Ψ Ψ m r c d e k H₁ H₂ ∅ ∅

theorem principalFrequency_eq (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    principalFrequency p hg hinj hp Ψ m r c d e k H₁ H₂ W Y =
      (Y : ℂ) * paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 / ‖eisEmbedding e‖ ^ 2) *
        (star (H₁ ∅) * H₂ ∅) := by
  simp only [principalFrequency, Finset.union_empty, Finset.prod_empty, map_one, norm_one,
    Complex.ofReal_one, div_one, primeProductNorm, one_pow, mul_one,
    secondGaussTerm_empty (p := p) (hp := hp) (hg := hg) (hinj := hinj)]

theorem principalFrequency_eq_secondFrequencyKernel_empty
    (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    principalFrequency p hg hinj hp Ψ m r c d e k H₁ H₂ W Y =
      secondFrequencyKernel p hp hg hinj ∅ Ψ Ψ m r c d e k H₁ H₂ W Y := by
  simp only [secondFrequencyKernel, Finset.powerset_empty, Finset.sum_singleton,
    Finset.disjoint_empty_left, ite_true, principalFrequency]

def restorationTerm (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (G : Finset ι) (E : G.powerset) (k : Eis) : ℂ :=
  secondSourceCommonCoefficient p hg Ψ m c d G E.val *
    principalFrequency p hg hinj hp Ψ m
      (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
      (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y

theorem restorationTerm_eq_principal_kernel (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ)
    (m c d : Eis) (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (G : Finset ι) (E : G.powerset) (k : Eis) :
    restorationTerm p hg hinj hp Ψ m c d H W Y G E k =
      secondSourceCommonCoefficient p hg Ψ m c d G E.val *
        secondFrequencyKernel p hp hg hinj ∅ Ψ Ψ m
          (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
          (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y := by
  rw [restorationTerm, principalFrequency_eq_secondFrequencyKernel_empty]

theorem restorationTerm_eq (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (G : Finset ι) (E : G.powerset) (k : Eis) :
    restorationTerm p hg hinj hp Ψ m c d H W Y G E k =
      (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2 : ℝ) *
      (‖H G‖ ^ 2 : ℝ) * (UniqueFactorizationMonoid.moebius (supportIdeal p E.val) : ℂ) *
      ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ) : ℝ) : ℂ) *
      paperRadialFourier W ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k‖ ^ 2) := by
  rw [restorationTerm, principalFrequency_eq]
  simp only [Finset.union_empty, secondSourceCommonCoefficient, primeSubsetGenerator_norm_sq]
  have hh : star (H G) * H G = (‖H G‖ ^ 2 : ℝ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hh]
  simp only [supportIdeal, Complex.ofReal_div]
  have harg : Y * ‖eisEmbedding k‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E.val, Ideal.span {p i}) : ℝ) =
      (Y / (Ideal.absNorm (∏ i ∈ E.val, Ideal.span {p i}) : ℝ)) * ‖eisEmbedding k‖ ^ 2 := by ring
  rw [harg]
  ring

theorem restorationTerm_mask_norm_le (hp : ∀ i, p i ≠ 0)
    (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (G : Finset ι) (E : G.powerset) (k : Eis) (θ : ℂ) (hθ : ‖θ‖ ≤ 1) :
    ‖θ * restorationTerm p hg hinj hp Ψ m c d H W Y G E k‖ ≤
      ‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) *
        ‖paperRadialFourier W ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k‖ ^ 2)‖ := by
  have ht := div_pos hY (supportIdeal_norm_pos p E.val)
  have ha : ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
      ((secondInputCoefficient_norm_le p hg Ψ m c d G).trans (hΨ _)) 2
  have hμ := QuadraticInitialBound.norm_ideal_moebius_le_one (supportIdeal p E.val)
  rw [restorationTerm_eq]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_norm, abs_of_pos ht]
  calc
    _ ≤ 1 * (1 * ‖H G‖ ^ 2 * 1 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) *
        ‖paperRadialFourier W ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k‖ ^ 2)‖) := by gcongr
    _ = _ := by ring

theorem restorationTerm_mask_summable_norm (hp : ∀ i, p i ≠ 0)
    (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (G : Finset ι) (E : G.powerset) (θ : Eis → ℂ)
    (hθ : ∀ k : {k : Eis // k ≠ 0}, ‖θ k.val‖ ≤ 1) :
    Summable (fun k : {k : Eis // k ≠ 0} =>
      ‖θ k.val * restorationTerm p hg hinj hp Ψ m c d H W Y G E k.val‖) := by
  have ht := div_pos hY (supportIdeal_norm_pos p E.val)
  have hs := (paperRadialFourier_lattice_summable_norm W _ ht).subtype (fun k : Eis => k ≠ 0)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => restorationTerm_mask_norm_le p hg hinj hp Ψ hΨ m c d H W Y hY G E k.val (θ k.val) (hθ k))
    (hs.mul_left (‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ))))

theorem restoration_divisor_abs_le (hp : ∀ i, p i ≠ 0)
    (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (G : Finset ι) (E : G.powerset) (θ : Eis → ℂ)
    (hθ : ∀ k : {k : Eis // k ≠ 0}, ‖θ k.val‖ ≤ 1) :
    (∑' k : {k : Eis // k ≠ 0},
      ‖θ k.val * restorationTerm p hg hinj hp Ψ m c d H W Y G E k.val‖) ≤
        QuadraticInitialBound.pvControl W * ‖H G‖ ^ 2 := by
  have ht := div_pos hY (supportIdeal_norm_pos p E.val)
  have hs := (paperRadialFourier_lattice_summable_norm W _ ht).subtype (fun k : Eis => k ≠ 0)
  have hb : (∑' k : {k : Eis // k ≠ 0},
      ‖θ k.val * restorationTerm p hg hinj hp Ψ m c d H W Y G E k.val‖) ≤
      ∑' k : {k : Eis // k ≠ 0}, ‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) *
        ‖paperRadialFourier W ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k.val‖ ^ 2)‖ :=
    Summable.tsum_le_tsum
      (fun k : {k : Eis // k ≠ 0} => restorationTerm_mask_norm_le p hg hinj hp Ψ hΨ m c d H W Y hY G E k.val (θ k.val) (hθ k))
      (restorationTerm_mask_summable_norm p hg hinj hp Ψ hΨ m c d H W Y hY G E θ hθ)
      (hs.mul_left (‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ))))
  apply hb.trans
  calc
    _ = (‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ))) *
        (∑' k : {k : Eis // k ≠ 0}, ‖paperRadialFourier W
          ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k.val‖ ^ 2)‖) :=
      tsum_mul_left
    _ = ‖H G‖ ^ 2 * ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) *
        (∑' k : {k : Eis // k ≠ 0}, ‖paperRadialFourier W
          ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k.val‖ ^ 2)‖)) := mul_assoc _ _ _
    _ ≤ ‖H G‖ ^ 2 * QuadraticInitialBound.pvControl W :=
      mul_le_mul_of_nonneg_left (QuadraticInitialBound.pv_lattice_bound W _ ht) (sq_nonneg ‖H G‖)
    _ = _ := mul_comm _ _

def principalRestoration (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (θ : Finset ι → Finset ι → Eis → ℂ) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E : G.powerset, ∑' k : {k : Eis // k ≠ 0},
    θ G E.val k.val * restorationTerm p hg hinj hp Ψ m c d H W Y G E k.val

theorem principalRestoration_abs_le (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (θ : Finset ι → Finset ι → Eis → ℂ)
    (hθ : ∀ G ∈ F.powerset, ∀ E : G.powerset, ∀ k : {k : Eis // k ≠ 0}, ‖θ G E.val k.val‖ ≤ 1) :
    (∑ G ∈ F.powerset, ∑ E : G.powerset, ∑' k : {k : Eis // k ≠ 0},
      ‖θ G E.val k.val * restorationTerm p hg hinj hp Ψ m c d H W Y G E k.val‖) ≤
      QuadraticInitialBound.pvControl W *
        ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro G hG
  calc
    _ ≤ ∑ E : G.powerset, QuadraticInitialBound.pvControl W * ‖H G‖ ^ 2 :=
      Finset.sum_le_sum (fun E _ => restoration_divisor_abs_le p hg hinj hp Ψ hΨ m c d H W Y hY G E
        (θ G E.val) (hθ G hG E))
    _ = (G.powerset.card : ℝ) * (QuadraticInitialBound.pvControl W * ‖H G‖ ^ 2) := by simp
    _ ≤ ((idealDivisors (supportIdeal p G)).card : ℝ) *
        (QuadraticInitialBound.pvControl W * ‖H G‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast mask_card_le_divisors p hinj G)
        (mul_nonneg (QuadraticInitialBound.pvControl_nonneg W) (sq_nonneg _))
    _ = _ := by ring

theorem principalRestoration_norm_le (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (θ : Finset ι → Finset ι → Eis → ℂ)
    (hθ : ∀ G ∈ F.powerset, ∀ E : G.powerset, ∀ k : {k : Eis // k ≠ 0}, ‖θ G E.val k.val‖ ≤ 1) :
    ‖principalRestoration p hg hinj hp F Ψ m c d H W Y θ‖ ≤
      QuadraticInitialBound.pvControl W *
        ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
  apply (norm_sum_le _ _).trans
  apply le_trans _ (principalRestoration_abs_le p hg hinj hp F Ψ hΨ m c d H W Y hY θ hθ)
  apply Finset.sum_le_sum
  intro G hG
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro E _
  exact norm_tsum_le_tsum_norm (restorationTerm_mask_summable_norm p hg hinj hp Ψ hΨ m c d H W Y hY G E
    (θ G E.val) (hθ G hG E))

def markedRadial {σ : Type*} [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (V : 𝓢(ℝ, ℂ)) (X : ℝ) (G : Finset ι) : ℂ :=
  primeMark slots lists a (A ∪ G) * V (primeProductNorm p G / X)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma markedRadial_support {σ : Type*} [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (V : 𝓢(ℝ, ℂ)) (X M : ℝ) (hX : 0 < X)
    (hV : ∀ t, V t ≠ 0 → t ≤ Real.exp M) (G : Finset ι)
    (hG : markedRadial p slots lists a A V X G ≠ 0) :
    primeProductNorm p G ≤ X * Real.exp M := by
  have hv : V (primeProductNorm p G / X) ≠ 0 := by
    intro hz
    exact hG (by simp [markedRadial, hz])
  simpa only [mul_comm] using (div_le_iff₀ hX).mp (hV _ hv)

include hinj in

theorem radial_mass_from_pointwise (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (H : Finset ι → ℂ) (U ε D : ℝ)
    (hU : 0 < U) (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (hs : ∀ G, H G ≠ 0 → primeProductNorm p G ≤ U)
    (hb : ∀ G, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 ≤
      D * (primeProductNorm p G) ^ ε) :
    (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2) ≤
      128 * D * U ^ (1 + ε) := by
  let T := boundedPrimeSupports p F U
  have he : (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2) =
      ∑ G ∈ T, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro G hG hn
    have hz : H G = 0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hG, hs G hh⟩)
    simp [hz]
  rw [he]
  calc
    _ ≤ ∑ G ∈ T, D * U ^ ε := by
      apply Finset.sum_le_sum
      intro G hG
      exact (hb G).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (primeProductNorm_pos p hp G).le (Finset.mem_filter.mp hG).2 hε) hD)
    _ = (T.card : ℝ) * (D * U ^ ε) := by simp
    _ ≤ (128 * U) * (D * U ^ ε) := mul_le_mul_of_nonneg_right
      (boundedPrimeSupports_card_positive p hp hinj F U hU) (by positivity)
    _ = 128 * D * U ^ (1 + ε) := by rw [Real.rpow_add hU, Real.rpow_one]; ring

omit [DecidableEq ι] in
lemma mass_le_divisor_mass (F : Finset ι) (H : Finset ι → ℂ) :
    (∑ G ∈ F.powerset, ‖H G‖ ^ 2) ≤
      ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro G _
  have ho : (1 : Ideal Eis) ∈ idealDivisors (supportIdeal p G) :=
    (mem_idealDivisors (supportIdeal_ne_zero p G)).mpr (one_dvd _)
  have hc : (1 : ℝ) ≤ ((idealDivisors (supportIdeal p G)).card : ℝ) := by
    exact_mod_cast Finset.one_le_card.mpr ⟨1, ho⟩
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (sq_nonneg ‖H G‖)

end

theorem marked_radial_divisor_mass (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A F : Finset ι) (V : 𝓢(ℝ, ℂ)) (X M : ℝ), 0 < X →
      (∀ t, V t ≠ 0 → t ≤ Real.exp M) →
      (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) *
        ‖markedRadial p slots lists a A V X G‖ ^ 2) ≤
        C * (4 : ℝ)^A.card * (SchwartzMap.seminorm ℝ 0 0 V)^2 *
          (X * Real.exp M)^(1 + ε) := by
  obtain ⟨Cm, hCm, hm⟩ := finite_primeMark_extracted_bound (ε / 4) (by positivity)
  obtain ⟨Cd, hCd, hd⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  refine ⟨128 * Cd * Cm ^ 2, by positivity, ?_⟩
  intro ι σ _ _ p hp _ hinj hcop slots lists a hslots ha A F V X M hX hV
  have hpoint (G : Finset ι) :
      ((idealDivisors (supportIdeal p G)).card : ℝ) *
        ‖markedRadial p slots lists a A V X G‖ ^ 2 ≤
      (Cd * ((2 : ℝ)^A.card * Cm * SchwartzMap.seminorm ℝ 0 0 V)^2) *
        (primeProductNorm p G)^ε := by
    have hn := primeProductNorm_pos p hp G
    have hmark := hm p hp hcop slots lists a hslots ha A G
    have hv := V.norm_le_seminorm ℝ (primeProductNorm p G / X)
    have hdiv := hd (supportIdeal p G) (supportIdeal_ne_zero p G)
    rw [show (Ideal.absNorm (supportIdeal p G) : ℝ) = primeProductNorm p G from
      (primeProductNorm_eq_ideal_norm p G).symm] at hdiv
    have hpow : (primeProductNorm p G) ^ (ε / 2) * ((primeProductNorm p G) ^ (ε / 4))^2 =
        (primeProductNorm p G)^ε := by
      rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_add hn]
      congr 1
      ring
    calc
      _ ≤ (Cd * (primeProductNorm p G)^(ε/2)) *
          (((2 : ℝ)^A.card * Cm * (primeProductNorm p G)^(ε/4)) *
            SchwartzMap.seminorm ℝ 0 0 V)^2 := by
        apply mul_le_mul hdiv _ (sq_nonneg _) (by positivity)
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [markedRadial, norm_mul]
        exact mul_le_mul hmark hv (norm_nonneg _) (by positivity)
      _ = (Cd * ((2 : ℝ)^A.card * Cm * SchwartzMap.seminorm ℝ 0 0 V)^2) *
          ((primeProductNorm p G)^(ε/2) * ((primeProductNorm p G)^(ε/4))^2) := by ring
      _ = _ := by rw [hpow]
  have hb := radial_mass_from_pointwise p hinj hp F (markedRadial p slots lists a A V X)
    (X * Real.exp M) ε (Cd * ((2 : ℝ)^A.card * Cm * SchwartzMap.seminorm ℝ 0 0 V)^2)
    (by positivity) hε.le (by positivity)
    (markedRadial_support p slots lists a A V X M hX hV) hpoint
  have h4 : ((2 : ℝ)^A.card)^2 = (4 : ℝ)^A.card := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  convert hb using 1 ; (rw [mul_pow, mul_pow, h4]; ring)

lemma radial_support_of_annular (V : 𝓢(ℝ, ℂ)) (a M : ℝ)
    (hV : tsupport V ⊆ Set.Icc a (Real.exp M)) :
    ∀ t, V t ≠ 0 → t ≤ Real.exp M := by
  intro t ht
  exact (hV (subset_closure ht)).2

def outsideCutoff {ι : Type*} [DecidableEq ι]
    (K : Finset ι → Finset ι → Finset Eis) (G E : Finset ι) (k : Eis) : ℂ :=
  if k ∈ K G E then 0 else 1

lemma outsideCutoff_norm_le_one {ι : Type*} [DecidableEq ι]
    (K : Finset ι → Finset ι → Finset Eis) (G E : Finset ι) (k : Eis) :
    ‖outsideCutoff K G E k‖ ≤ 1 := by
  unfold outsideCutoff
  split_ifs <;> norm_num

lemma outsideCutoff_mul_norm_le_one {ι : Type*} [DecidableEq ι]
    (K : Finset ι → Finset ι → Finset Eis) (G E : Finset ι) (k : Eis)
    (θ : ℂ) (hθ : ‖θ‖ ≤ 1) : ‖outsideCutoff K G E k * θ‖ ≤ 1 := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul (outsideCutoff_norm_le_one K G E k) hθ
    (norm_nonneg _) zero_le_one

theorem uniform_row_control :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(ℝ, ℂ),
      ‖paperRadialFourier W 0‖ + QuadraticInitialBound.pvControl W ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 0
  refine ⟨s ∪ QuadraticInitialBound.pvSeminorms,
    C + QuadraticInitialBound.pvConstant, add_pos hC QuadraticInitialBound.pvConstant_pos, ?_⟩
  intro W
  have h₁ := Seminorm.le_def.mp (Finset.sup_mono (f := schwartzSeminormFamily ℝ ℝ ℂ)
    (Finset.subset_union_left (s₁ := s) (s₂ := QuadraticInitialBound.pvSeminorms))) W
  have h₂ := Seminorm.le_def.mp (Finset.sup_mono (f := schwartzSeminormFamily ℝ ℝ ℂ)
    (Finset.subset_union_right (s₁ := s) (s₂ := QuadraticInitialBound.pvSeminorms))) W
  have hz : ‖paperRadialFourier W 0‖ ≤ C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    simpa only [pow_zero, one_mul] using hb W 0 le_rfl
  calc
    _ ≤ C * (s ∪ QuadraticInitialBound.pvSeminorms).sup (schwartzSeminormFamily ℝ ℝ ℂ) W +
        QuadraticInitialBound.pvConstant *
          (s ∪ QuadraticInitialBound.pvSeminorms).sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
      add_le_add (hz.trans (mul_le_mul_of_nonneg_left h₁ hC.le))
        (mul_le_mul_of_nonneg_left h₂ QuadraticInitialBound.pvConstant_pos.le)
    _ = _ := by ring

section
variable {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem principal_energy_le (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 1 ≤ Y)
    (K : Finset ι → Finset ι → Finset Eis)
    (hzero : ∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : Eis) ∈ K G E)
    (θ : Finset ι → Finset ι → Eis → ℂ)
    (hθ : ∀ G ∈ F.powerset, ∀ E : G.powerset, ∀ k : {k : Eis // k ≠ 0}, ‖θ G E.val k.val‖ ≤ 1) :
    ‖truncatedSecondZero p hg F Ψ m c d H W Y K‖ +
        ‖principalRestoration p hg hinj hp F Ψ m c d H W Y θ‖ ≤
      Y * (‖paperRadialFourier W 0‖ + QuadraticInitialBound.pvControl W) *
        ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hd : 0 ≤ ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 :=
    Finset.sum_nonneg (fun G _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  calc
    _ ≤ Y * ‖paperRadialFourier W 0‖ * ∑ G ∈ F.powerset, ‖H G‖ ^ 2 +
        QuadraticInitialBound.pvControl W *
          ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 :=
      add_le_add (zero_norm_le p hg hinj F Ψ hΨ m c d H W Y hY0.le K hzero)
        (principalRestoration_norm_le p hg hinj hp F Ψ hΨ m c d H W Y hY0 θ hθ)
    _ ≤ Y * ‖paperRadialFourier W 0‖ *
          (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2) +
        Y * QuadraticInitialBound.pvControl W *
          (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (mass_le_divisor_mass p F H) (mul_nonneg hY0.le (norm_nonneg _))
      · exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_left (QuadraticInitialBound.pvControl_nonneg W) hY) hd
    _ = _ := by ring

end

theorem marked_principal_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A F : Finset ι) (Ψ : Eis →* ℂ), (∀ z, ‖Ψ z‖ ≤ 1) →
      ∀ (m c d : Eis) (V W : 𝓢(ℝ, ℂ)) (X M Y : ℝ), 0 < X → 1 ≤ Y →
      (∀ t, V t ≠ 0 → t ≤ Real.exp M) →
      ∀ K : Finset ι → Finset ι → Finset Eis,
      (∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : Eis) ∈ K G E) →
      ∀ θ : Finset ι → Finset ι → Eis → ℂ,
      (∀ G ∈ F.powerset, ∀ E : G.powerset, ∀ k : {k : Eis // k ≠ 0}, ‖θ G E.val k.val‖ ≤ 1) →
      ‖truncatedSecondZero p hg F Ψ m c d (markedRadial p slots lists a A V X) W Y K‖ +
        ‖principalRestoration p hg hinj hp F Ψ m c d (markedRadial p slots lists a A V X) W Y θ‖ ≤
      C * (4 : ℝ)^A.card *
        (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 V)^2) *
        Y * (X * Real.exp M)^(1 + ε) := by
  obtain ⟨s, Cr, hCr, hr⟩ := uniform_row_control
  obtain ⟨Cm, hCm, hm⟩ := marked_radial_divisor_mass ε hε
  refine ⟨s, Cr * Cm, mul_pos hCr hCm, ?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots lists a hslots ha A F Ψ hΨ m c d V W X M Y hX hY hV K hzero θ hθ
  apply (principal_energy_le p hg hinj hp F Ψ hΨ m c d
    (markedRadial p slots lists a A V X) W Y hY K hzero θ hθ).trans
  have hb := hm p hp hinj hcop slots lists a hslots ha A F V X M hX hV
  calc
    _ ≤ Y * (Cr * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
        (Cm * (4 : ℝ)^A.card * (SchwartzMap.seminorm ℝ 0 0 V)^2 *
          (X * Real.exp M)^(1 + ε)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hr W) (le_trans zero_le_one hY)) hb
        (Finset.sum_nonneg (fun G _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
        (mul_nonneg (le_trans zero_le_one hY) (mul_nonneg hCr.le (apply_nonneg _ _)))
    _ = _ := by ring

end SevenEighths.InversePrincipalEnergy

end

end OAI
