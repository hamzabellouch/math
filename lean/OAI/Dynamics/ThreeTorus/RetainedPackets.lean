import OAI.Dynamics.ThreeTorus.Cutoffs
import OAI.Dynamics.ThreeTorus.NeutralSupport

namespace OAI

/-! Literal retained passage vectors, spectral identities, regularity, old marginals, and quantitative cutoff losses. -/

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

lemma integral_passageChart {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H)
    (f : TripleTorus → ℝ) :
    (∫ x, f (passageChart H x) ∂tripleVolume) = ∫ x, f x ∂tripleVolume := by
  let e : TripleTorus ≃ᵐ TripleTorus :=
    { toEquiv := passageChart H
      measurable_toFun := (measurePreserving_passageChart hH).measurable
      measurable_invFun := passageChart_inverse_measurable hH }
  exact (measurePreserving_passageChart hH).integral_comp e.measurableEmbedding f

/-- A complete quantitative form of the physical transport estimate (2.9).
The sole right-hand quantity is the actual summed Fourier-mass error. -/
lemma physical_retainedPassage_error_le {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A)
    (S : Finset ℤ) (χ W : ℤ → UnitAddCircle → ℝ) (hχc : ∀ j, Continuous (χ j))
    (ψ : UnitAddCircle → ℝ) (hψc : Continuous ψ) (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1)
    (hχ : ∀ j a, 0 ≤ χ j a ∧ χ j a ≤ 1)
    (hW : ∀ j a, W j a ≠ 0 → j ∈ S ∧ χ j a = 1)
    (hE : ∀ j, Integrable (fun a => |‖exactPassageCoeff m H A j a‖^2-W j a|)
      AddCircle.haarAddCircle)
    (hp : ∀ᵐ a ∂AddCircle.haarAddCircle,
      Summable (fun j => |‖exactPassageCoeff m H A j a‖^2-W j a|))
    (hs : Summable (fun j => ∫ a, |‖exactPassageCoeff m H A j a‖^2-W j a|
      ∂AddCircle.haarAddCircle)) :
    (∫ x : TripleTorus,
      ‖(ψ x.2.2:ℂ)*packet m A x-retainedPassage m H A S χ ψ (passageChart H x)‖^2
        ∂tripleVolume) ≤
      ∑' j : ℤ, ∫ a, |‖exactPassageCoeff m H A j a‖^2-W j a| ∂AddCircle.haarAddCircle := by
  have he := integral_passageChart hH.measurable (fun x : TripleTorus =>
    ‖(ψ x.2.1:ℂ)*packet m A ((passageChart H).symm x)-retainedPassage m H A S χ ψ x‖^2)
  simp only [Equiv.symm_apply_apply] at he
  change (∫ x : TripleTorus,
      ‖(ψ x.2.2:ℂ)*packet m A x-retainedPassage m H A S χ ψ (passageChart H x)‖^2
        ∂tripleVolume) = _ at he
  rw [he,integrated_retainedPassage_error hH hA S χ hχc ψ hψc]
  let E : UnitAddCircle → UnitAddCircle → ℝ := fun a θ =>
    ‖passageFourierInput m H A a θ-
      ∑ j ∈ S, (χ j a:ℂ)*exactPassageCoeff m H A j a*fourier j θ‖^2
  have hEc : Continuous E.uncurry := by
    apply Continuous.pow
    apply Continuous.norm
    apply (continuous_passageFourierInput hH hA).sub
    apply continuous_finsetSum
    intro j _hj
    exact (((Complex.continuous_ofReal.comp (hχc j)).comp continuous_fst).mul
      ((continuous_exactPassageCoeff hH hA j).comp continuous_fst)).mul
      ((fourier j).continuous.comp continuous_snd)
  have hIc : Continuous (fun a => ∫ θ, E a θ ∂AddCircle.haarAddCircle) := by
    simpa only [setIntegral_univ] using
      continuous_parametric_integral_of_continuous (μ := AddCircle.haarAddCircle) hEc isCompact_univ
  have hIi : Integrable (fun a => ∫ θ, E a θ ∂AddCircle.haarAddCircle) AddCircle.haarAddCircle :=
    hIc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ a, ∫ θ, E a θ ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun a => mul_nonneg (sq_nonneg _)
          (integral_nonneg (fun _ => sq_nonneg _)))
      · exact hIi
      · filter_upwards [] with a
        exact mul_le_of_le_one_left (integral_nonneg (fun _ => sq_nonneg _))
          (by nlinarith [(hψ a).1,(hψ a).2])
    _ ≤ _ := integrated_Fourier_cutoff_le_mass_error
      (fun a => (continuous_passageFourierInput hH hA).comp (continuous_const.prodMk continuous_id)) S χ W hχ hW hE hp hs

lemma pointwise_array_mass_error_summable {c : ℤ → UnitAddCircle → ℂ}
    {W : ℝ → UnitAddCircle → ℝ} (hc : HasCompactSupport W.uncurry)
    (hcs : ∀ a, Summable (fun j => ‖c j a‖^2)) {n : ℕ} (hn : 0 < n) (a : UnitAddCircle) :
    Summable (fun j : ℤ => |‖c j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a|) := by
  obtain ⟨S,hS⟩ := compact_lattice_support hc hn 0
  have hw : Summable (fun j : ℤ => |(n:ℝ)⁻¹*W ((j:ℝ)/n) a|) := by
    apply summable_of_ne_finset_zero (s := S)
    intro j hj
    have hz : W ((j:ℝ)/n) a = 0 := by simpa using hS j hj a
    simp [hz]
  refine Summable.of_nonneg_of_le (f := fun j => ‖c j a‖^2+|(n:ℝ)⁻¹*W ((j:ℝ)/n) a|)
    (fun _ => abs_nonneg _) (fun j => ?_) ((hcs a).add hw)
  have hh := abs_sub_le (‖c j a‖^2) 0 ((n:ℝ)⁻¹*W ((j:ℝ)/n) a)
  have he : |‖c j a‖^2| = ‖c j a‖^2 := abs_of_nonneg (sq_nonneg _)
  simpa only [sub_zero,zero_sub,abs_neg,he] using hh

/-- The actual physical packet cutoff error tends to zero once the unrounded
stationary mass theorem is applied. All summability hypotheses are derived. -/
lemma physical_retainedPassage_tendsto
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {W : ℝ → UnitAddCircle → ℝ}
    (hH : ∀ n, Continuous (H n)) (hA : Continuous A)
    (hWc : Continuous W.uncurry) (hWk : HasCompactSupport W.uncurry)
    (S : ℕ → Finset ℤ) (χ : ℕ → ℤ → UnitAddCircle → ℝ)
    (hχc : ∀ n j, Continuous (χ n j)) (hχ : ∀ n j a, 0 ≤ χ n j a ∧ χ n j a ≤ 1)
    (ψ : UnitAddCircle → ℝ) (hψc : Continuous ψ) (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1)
    (hW : ∀ (n : ℕ), 0 < n → ∀ (j : ℤ) (a : UnitAddCircle), W ((j:ℝ)/n) a ≠ 0 → j ∈ S n ∧ χ n j a = 1)
    (ht : Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a|
        ∂AddCircle.haarAddCircle) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x : TripleTorus,
      ‖(ψ x.2.2:ℂ)*packet m A x-
        retainedPassage m (H n) A (S n) (χ n) ψ (passageChart (H n) x)‖^2
        ∂tripleVolume) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))) _ ht
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hEc (j : ℤ) : Continuous (fun a =>
      |‖exactPassageCoeff m (H n) A j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a|) := by
    exact (((continuous_exactPassageCoeff (hH n) hA j).norm.pow 2).sub
      (continuous_const.mul (hWc.comp (continuous_const.prodMk continuous_id)))).abs
  apply physical_retainedPassage_error_le (hH n) hA (S n) (χ n)
    (fun j a => (n:ℝ)⁻¹*W ((j:ℝ)/n) a) (hχc n) ψ hψc hψ (hχ n)
  · intro j a ha
    exact hW n hn j a (fun hz => ha (by simp [hz]))
  · intro j
    exact (hEc j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · apply Filter.Eventually.of_forall
    intro a
    exact pointwise_array_mass_error_summable hWk
      (fun a => continuous_fourier_summable
        ((continuous_passageFourierInput (hH n) hA).comp (continuous_const.prodMk continuous_id))) hn a
  · simpa only [sub_zero] using integrated_array_mass_error_summable hWc hWk
      (continuous_exactPassageCoeff (hH n) hA) (exactPassageCoeff_summable (hH n) hA) hn 0

/-- Physical transport for the actual signed packet. The summed stationary
mass error is proved, not an input to this statement. -/
lemma exact_physical_retainedPassage_tendsto
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv P = V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0))
    {χ : ℝ → UnitAddCircle → ℝ} (hχc : Continuous χ.uncurry)
    (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (ψ : UnitAddCircle → ℝ) (hψc : Continuous ψ) (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
      (A₀ a) s ≠ 0 → χ s a = 1)
    (S : ℕ → Finset ℤ)
    (hS : ∀ n, 0 < n → ∀ j ∉ S n, ∀ a, χ ((j:ℝ)/n) a = 0) :
    Tendsto (fun n => ∫ x : TripleTorus,
      ‖(ψ x.2.2:ℂ)*packet m A x-
        retainedPassage m (H n) A (S n) (fun j => χ ((j:ℝ)/n)) ψ
          (passageChart (H n) x)‖^2 ∂tripleVolume) atTop (𝓝 0) := by
  have hbranch := scaled_speed_good_branch hm hR hV hd
  have hW := stationaryWeight_signed_compact_continuous (contDiff_const.mul hV) hAc
    (fun a => (hsupp a).trans Ioc_subset_Icc_self) hR hbranch.1 hbranch.2
  apply physical_retainedPassage_tendsto
    (W := fun s a => stationaryWeight (Icc (l-R) (u+R))
      (fun x => (m:ℝ)*V x) (A₀ a) s) hHc hAcont hW.1 hW.2 S
    (fun n j => χ ((j:ℝ)/n))
    (fun _ _ => hχc.comp (continuous_const.prodMk continuous_id))
    (fun _ _ _ => hχ _ _) ψ hψc hψ
  · intro n hn j a hw
    have he := hχW ((j:ℝ)/n) a hw
    refine ⟨?_,he⟩
    by_contra hj
    have hz := hS n hn j hj a
    linarith
  · exact exactPassageCoeff_summed hm hH hA hA₀ hAc hAd hsupp hlo huo hlu hR
      hP hV hPV hd hHc hAcont hδt

end ThreeTorus

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology
namespace ThreeTorus

lemma stationaryWeight_cylinder_support {C : Set ℝ} {V : ℝ → ℝ} {m : ℤ}
    {A : UnitAddCircle → ℝ → ℂ} :
    support (fun p : ℝ × UnitAddCircle => stationaryWeight C (fun x => (m:ℝ)*V x) (A p.2) p.1) ⊆
      stationaryImage m V (tsupport (fun p : ℝ × UnitAddCircle => A p.2 p.1)) := by
  intro p hp
  have hs : p.1 ∈ (fun x => (m:ℝ)*V x) '' C := by
    by_contra hn
    exact hp (by simp [stationaryWeight,branchDensity,hn])
  have hu := invFunOn_pos hs
  have hA : A p.2 (invFunOn (fun x => (m:ℝ)*V x) C p.1) ≠ 0 := by
    intro hz
    exact hp (by simp [stationaryWeight,branchDensity,hs,hz])
  refine ⟨(invFunOn (fun x => (m:ℝ)*V x) C p.1,p.2),?_,Prod.ext hu.2 rfl⟩
  exact subset_tsupport _ hA

lemma lifted_amplitude_compactSupport {A : UnitAddCircle → ℝ → ℂ} {l u : ℝ}
    (hA : ∀ a, support (A a) ⊆ Icc l u) :
    HasCompactSupport (fun p : ℝ × UnitAddCircle => A p.2 p.1) ∧
      tsupport (fun p : ℝ × UnitAddCircle => A p.2 p.1) ⊆ Icc l u ×ˢ univ := by
  have hs : tsupport (fun p : ℝ × UnitAddCircle => A p.2 p.1) ⊆ Icc l u ×ˢ univ := by
    apply closure_minimal _ (isClosed_Icc.prod isClosed_univ)
    intro p hp
    exact ⟨hA p.2 hp,mem_univ _⟩
  exact ⟨(isCompact_Icc.prod isCompact_univ).of_isClosed_subset isClosed_closure hs,hs⟩

/-- The output amplitudes from different colors are exactly disjoint at each
shared angular index; asymptotic orthogonality is not used here. -/
lemma retained_amplitude_disjoint {χ ξ : ℝ × UnitAddCircle → ℝ}
    (hd : Disjoint (tsupport χ) (tsupport ξ)) (s : ℝ)
    (F G : UnitAddCircle × UnitAddCircle → ℂ) :
    Disjoint (tsupport (fun p : UnitAddCircle × UnitAddCircle => (χ (s,p.1):ℂ)*F p))
      (tsupport (fun p : UnitAddCircle × UnitAddCircle => (ξ (s,p.1):ℂ)*G p)) := by
  have hs (η : ℝ × UnitAddCircle → ℝ) (B : UnitAddCircle × UnitAddCircle → ℂ) :
      tsupport (fun p : UnitAddCircle × UnitAddCircle => (η (s,p.1):ℂ)*B p) ⊆
        (fun p : UnitAddCircle × UnitAddCircle => (s,p.1)) ⁻¹' tsupport η := by
    apply closure_minimal _ ((isClosed_tsupport η).preimage (continuous_const.prodMk continuous_fst))
    intro p hp
    exact subset_tsupport η (fun hz => hp (by simp [hz]))
  exact (hd.preimage _).mono (hs χ F) (hs ξ G)

lemma norm_spare_character (m : ℤ) (C : UnitAddCircle → ℂ) (a b : UnitAddCircle) :
    ‖C a * fourier m b‖ = ‖C a‖ := by
  rw [norm_mul,show ‖fourier m b‖ = 1 from Circle.norm_coe _,mul_one]

/-- The source's finite stationary-image support selection, including the
zero-frequency exclusion and exact disjointness of the cutoffs. -/
lemma colored_stationary_cutoffs {ι : Type*} [Finite ι]
    (m : ι → ℤ) (V : ℝ → ℝ) (I : Set ℝ)
    (K U : ι → Set (ℝ × UnitAddCircle))
    (hm : ∀ i, m i ≠ 0) (hV : Continuous V) (hi : InjOn V I)
    (hK : ∀ i, IsCompact (K i)) (hKI : ∀ i, K i ⊆ I ×ˢ univ)
    (hzero : ∀ x ∈ I, V x ≠ 0)
    (hsep : ∀ i j, ∀ x ∈ I, ∀ y ∈ I, (m i:ℝ)*V x = (m j:ℝ)*V y → m i = m j)
    (hdisj : ∀ i j, i ≠ j → m i = m j → Disjoint (K i) (K j))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, stationaryImage (m i) V (K i) ⊆ U i) :
    ∃ χ : ι → ℝ × UnitAddCircle → ℝ,
      (∀ i, CylinderSmooth (χ i) ∧ HasCompactSupport (χ i) ∧ tsupport (χ i) ⊆ U i ∧
        (∀ p, 0 ≤ χ i p ∧ χ i p ≤ 1) ∧ (∀ a, χ i (0,a) = 0) ∧
        ∀ p ∈ stationaryImage (m i) V (K i), χ i =ᶠ[𝓝 p] 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) := by
  let E i := stationaryImage (m i) V (K i)
  let O i := U i ∩ {p : ℝ × UnitAddCircle | p.1 ≠ 0}
  have hO i : IsOpen (O i) := (hU i).inter (isOpen_ne_fun continuous_fst continuous_const)
  have hEO i : E i ⊆ O i := by
    intro p hp
    refine ⟨hKU i hp,?_⟩
    obtain ⟨q,hq,rfl⟩ := hp
    exact mul_ne_zero (by exact_mod_cast hm i) (hzero _ (hKI i hq).1)
  have hEd : Pairwise (Disjoint on E) := by
    intro i j hij
    by_cases he : m i = m j
    · change Disjoint (stationaryImage (m i) V (K i)) (stationaryImage (m j) V (K j))
      rw [he]
      exact stationaryImage_disjoint_same (hm j) hi (hKI i) (hKI j) (hdisj i j hij he)
    · apply stationaryImage_disjoint_distinct
      intro p hp q hq hh
      exact he (hsep i j p.1 (hKI i hp).1 q.1 (hKI j hq).1 hh)
  obtain ⟨χ,hχ,hχd⟩ := finite_disjoint_cylinder_cutoffs E O
    (fun i => stationaryImage_compact hV (hK i)) hO hEO hEd
  refine ⟨χ,fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1.trans inter_subset_left,
    (hχ i).2.2.2.1,?_,(hχ i).2.2.2.2⟩,hχd⟩
  intro a
  by_contra ha
  exact ((hχ i).2.2.1 (subset_tsupport (χ i) ha)).2 rfl

lemma simultaneous_retained_indices {ι : Type*} (χ : ι → ℝ × UnitAddCircle → ℝ)
    (hc : ∀ i, HasCompactSupport (χ i)) (hz : ∀ i a, χ i (0,a) = 0) :
    ∃ S : ℕ → ι → Finset ℤ, (∀ n i, (0:ℤ) ∉ S n i) ∧
      ∀ n, 0 < n → ∀ i j, j ∉ S n i → ∀ a, χ i ((j:ℝ)/n,a) = 0 := by
  classical
  have hex (n : ℕ) (i : ι) : ∃ S : Finset ℤ, (0:ℤ) ∉ S ∧
      (0 < n → ∀ j ∉ S, ∀ a, χ i ((j:ℝ)/n,a) = 0) := by
    by_cases hn : 0 < n
    · obtain ⟨S,hS,hS'⟩ := cylinder_cutoff_finite_indices (hc i) (hz i) n hn
      exact ⟨S,hS,fun _ => hS'⟩
    · exact ⟨∅,Finset.notMem_empty _,fun h => (hn h).elim⟩
  choose S hS hS' using hex
  exact ⟨S,hS,fun n hn i => hS' n i hn⟩

/-- Simultaneous physical transport with constructed, disjoint cylinder cutoffs.
The limit is a consequence of the signed stationary-phase theorem for the
actual Fourier coefficients, not an assumption on an auxiliary array. -/
theorem colored_physical_passage {ι : Type*} [Finite ι]
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    {A₀ : ι → UnitAddCircle → ℝ → ℂ}
    {P V : ℝ → ℝ} {m : ι → ℤ} {δ : ℕ → ℝ}
    {H : ℕ → UnitAddCircle → UnitAddCircle} {o l u R : ℝ}
    (hm : ∀ i, m i ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ i a x, x ∈ Ioc o (o+1) → A i ((x : UnitAddCircle),a) = A₀ i a x)
    (hA₀ : ∀ i a, ContDiff ℝ 2 (A₀ i a)) (hAc : ∀ i, Continuous (A₀ i).uncurry)
    (hAd : ∀ i, Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ i p.1) p.2))
    (hsupp : ∀ i a, Function.support (A₀ i a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv P = V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hHc : ∀ n, Continuous (H n)) (hAcont : ∀ i, Continuous (A i)) (hδt : Tendsto δ atTop (𝓝 0))
    (hzero : ∀ x ∈ Icc l u, V x ≠ 0)
    (hsep : ∀ i j, ∀ x ∈ Icc l u, ∀ y ∈ Icc l u,
      (m i:ℝ)*V x = (m j:ℝ)*V y → m i = m j)
    (hdisj : ∀ i j, i ≠ j → m i = m j →
      Disjoint (tsupport (fun p : ℝ × UnitAddCircle => A₀ i p.2 p.1))
        (tsupport (fun p : ℝ × UnitAddCircle => A₀ j p.2 p.1)))
    (U : ι → Set (ℝ × UnitAddCircle)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, stationaryImage (m i) V
      (tsupport (fun p : ℝ × UnitAddCircle => A₀ i p.2 p.1)) ⊆ U i)
    (ψ : UnitAddCircle → ℝ) (hψc : Continuous ψ) (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) :
    ∃ (χ : ι → ℝ × UnitAddCircle → ℝ) (S : ℕ → ι → Finset ℤ),
      (∀ i, CylinderSmooth (χ i) ∧ HasCompactSupport (χ i) ∧ tsupport (χ i) ⊆ U i ∧
        (∀ p, 0 ≤ χ i p ∧ χ i p ≤ 1)) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      (∀ n i, (0:ℤ) ∉ S n i) ∧
      (∀ n, 0 < n → ∀ i j, j ∉ S n i → ∀ a, χ i ((j:ℝ)/n,a) = 0) ∧
      ∀ i, Tendsto (fun n => ∫ x : TripleTorus,
        ‖(ψ x.2.2:ℂ)*packet (m i) (A i) x-
          retainedPassage (m i) (H n) (A i) (S n i)
            (fun j a => χ i ((j:ℝ)/n,a)) ψ (passageChart (H n) x)‖^2
              ∂tripleVolume) atTop (𝓝 0) := by
  let K i := tsupport (fun p : ℝ × UnitAddCircle => A₀ i p.2 p.1)
  have hK i := lifted_amplitude_compactSupport
    (fun a => (hsupp i a).trans Ioc_subset_Icc_self)
  have hi : InjOn V (Icc l u) := by
    apply (strictMonoOn_of_deriv_pos (convex_Icc _ _) hV.continuous.continuousOn _).injOn
    intro x hx
    have hx' := interior_subset hx
    exact hd x ⟨by linarith [hx'.1],by linarith [hx'.2]⟩
  obtain ⟨χ,hχ,hχd⟩ := colored_stationary_cutoffs m V (Icc l u) K U hm hV.continuous hi
    (fun i => (hK i).1) (fun i => (hK i).2) hzero hsep hdisj hU hKU
  obtain ⟨S,hS,hS'⟩ := simultaneous_retained_indices χ (fun i => (hχ i).2.1)
    (fun i => (hχ i).2.2.2.2.1)
  refine ⟨χ,S,fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1,(hχ i).2.2.2.1⟩,
    hχd,hS,hS',?_⟩
  intro i
  exact exact_physical_retainedPassage_tendsto (χ := fun s a => χ i (s,a)) (hm i) hH (hA i) (hA₀ i) (hAc i)
    (hAd i) (hsupp i) hlo huo hlu hR hP hV hPV hd hHc (hAcont i) hδt
    (hχ i).1.continuous (fun s a => (hχ i).2.2.2.1 (s,a)) ψ hψc hψ
    (fun s a hw => ((hχ i).2.2.2.2.2 (s,a)
      (stationaryWeight_cylinder_support hw)).self_of_nhds)
    (fun n => S n i) (fun n hn j hj a => hS' n hn i j hj a)

end ThreeTorus

noncomputable section
open Set Function Filter
open scoped Topology
namespace ThreeTorus

/-- The second support separation in the manuscript uses cutoffs in frequency
alone, as opposed to the first passage's frequency/slow-coordinate cutoffs. -/
theorem finite_disjoint_frequency_cutoffs {ι : Type*} [Finite ι]
    (K U : ι → Set ℝ) (hK : ∀ i, IsCompact (K i)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, K i ⊆ U i) (hdisj : Pairwise (Disjoint on K)) :
    ∃ χ : ι → ℝ → ℝ,
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        tsupport (χ i) ⊆ U i ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        ∀ s ∈ K i, χ i =ᶠ[𝓝 s] 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) := by
  have hd : Pairwise (fun i j => Disjoint (𝓝ˢ (K i)) (𝓝ˢ (K j))) :=
    fun i j hij => disjoint_nhdsSet_nhdsSet (hK i).isClosed (hK j).isClosed (hdisj hij)
  obtain ⟨O,hO,hOd⟩ := hd.exists_mem_filter_of_disjoint
  have hv i : K i ⊆ interior (O i) ∩ U i :=
    subset_inter (subset_interior_iff_mem_nhdsSet.mpr (hO i)) (hKU i)
  choose χ hχ using fun i => compact_smooth_cutoff (hK i)
    (isOpen_interior.inter (hU i)) (hv i)
  refine ⟨χ,fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1.trans inter_subset_right,
    (hχ i).2.2.2⟩,?_⟩
  intro i j hij
  exact (hOd hij).mono ((hχ i).2.2.1.trans (inter_subset_left.trans interior_subset))
    ((hχ j).2.2.1.trans (inter_subset_left.trans interior_subset))

lemma compactSupport_frequency_cylinder {χ : ℝ → ℝ} (hc : HasCompactSupport χ) :
    HasCompactSupport (fun p : ℝ × UnitAddCircle => χ p.1) := by
  apply (hc.prod isCompact_univ).of_isClosed_subset isClosed_closure
  apply closure_minimal _ ((isClosed_tsupport χ).prod isClosed_univ)
  intro p hp
  exact ⟨subset_tsupport χ hp,mem_univ _⟩

/-- Sampling disjoint frequency supports gives exactly disjoint finite index
sets. There is no asymptotic assertion in this exact separation conclusion. -/
theorem disjoint_frequency_indices {ι : Type*}
    (χ : ι → ℝ → ℝ) (hc : ∀ i, HasCompactSupport (χ i)) (hz : ∀ i, χ i 0 = 0)
    (hd : Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j)))) :
    ∃ S : ℕ → ι → Finset ℤ,
      (∀ n i, (0:ℤ) ∉ S n i) ∧
      (∀ n, Pairwise (fun i j => Disjoint (S n i) (S n j))) ∧
      ∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ χ i ((j:ℝ)/n) ≠ 0 := by
  classical
  have hex (n : ℕ) (i : ι) : ∃ S : Finset ℤ,
      (∀ j ∈ S, χ i ((j:ℝ)/n) ≠ 0) ∧
      (0 < n → ∀ (j : ℤ), χ i ((j:ℝ)/n) ≠ 0 → j ∈ S) := by
    by_cases hn : 0 < n
    · obtain ⟨S,_hS,hS'⟩ := cylinder_cutoff_finite_indices
        (compactSupport_frequency_cylinder (hc i)) (fun _ => hz i) n hn
      refine ⟨S.filter (fun j => χ i ((j:ℝ)/n) ≠ 0),?_,?_⟩
      · intro j hj
        exact (Finset.mem_filter.mp hj).2
      · intro _ j hj
        apply Finset.mem_filter.mpr
        exact ⟨by by_contra hh; exact hj (hS' j hh 0),hj⟩
    · exact ⟨∅,by simp,fun hh => (hn hh).elim⟩
  choose S hS hS' using hex
  refine ⟨S,?_,?_,?_⟩
  · intro n i hi
    exact hS n i 0 hi (by simp [hz])
  · intro n i j hij
    rw [Finset.disjoint_left]
    intro k hi hj
    exact Set.disjoint_left.mp (hd hij) (subset_tsupport (χ i) (hS n i k hi))
      (subset_tsupport (χ j) (hS n j k hj))
  · intro n hn i j
    exact ⟨hS n i j,hS' n i hn j⟩

/-- Compact slow-coordinate supports at equal old index stay disjoint under
strictly monotone stationary maps. Distinct indices use the separated ranges. -/
lemma frequency_images_disjoint {ι : Type*} (m : ι → ℤ) (V : ℝ → ℝ)
    (I : Set ℝ) (K : ι → Set ℝ) (hm : ∀ i, m i ≠ 0) (hi : InjOn V I)
    (hKI : ∀ i, K i ⊆ I)
    (hsep : ∀ i j, ∀ x ∈ I, ∀ y ∈ I, (m i:ℝ)*V x = (m j:ℝ)*V y → m i = m j)
    (hdisj : ∀ i j, i ≠ j → m i = m j → Disjoint (K i) (K j)) :
    Pairwise (fun i j => Disjoint ((fun x => (m i:ℝ)*V x) '' K i)
      ((fun x => (m j:ℝ)*V x) '' K j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨x,hx,hxz⟩ := hz
  obtain ⟨y,hy,hyz⟩ := hz'
  have he : (m i:ℝ)*V x = (m j:ℝ)*V y := hxz.trans hyz.symm
  have he' : m i = m j := hsep i j x (hKI i hx) y (hKI j hy) he
  rw [he'] at he
  have hm' : (m j:ℝ) ≠ 0 := by exact_mod_cast hm j
  have hxy := hi (hKI i hx) (hKI j hy) (mul_left_cancel₀ hm' he)
  exact Set.disjoint_left.mp (hdisj i j hij he') hx (hxy ▸ hy)

/-- Full exact producer for the second passage's cutoff and index geometry. -/
theorem second_separation_cutoffs {ι : Type*} [Finite ι]
    (m : ι → ℤ) (V : ℝ → ℝ) (I : Set ℝ) (K U : ι → Set ℝ)
    (hm : ∀ i, m i ≠ 0) (hV : Continuous V) (hi : InjOn V I)
    (hK : ∀ i, IsCompact (K i)) (hKI : ∀ i, K i ⊆ I)
    (hzero : ∀ x ∈ I, V x ≠ 0)
    (hsep : ∀ i j, ∀ x ∈ I, ∀ y ∈ I, (m i:ℝ)*V x = (m j:ℝ)*V y → m i = m j)
    (hdisj : ∀ i j, i ≠ j → m i = m j → Disjoint (K i) (K j))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, (fun x => (m i:ℝ)*V x) '' K i ⊆ U i) :
    ∃ (χ : ι → ℝ → ℝ) (S : ℕ → ι → Finset ℤ),
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        tsupport (χ i) ⊆ U i ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        ∀ s ∈ (fun x => (m i:ℝ)*V x) '' K i, χ i =ᶠ[𝓝 s] 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      (∀ n i, (0:ℤ) ∉ S n i) ∧
      (∀ n, Pairwise (fun i j => Disjoint (S n i) (S n j))) ∧
      ∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ χ i ((j:ℝ)/n) ≠ 0 := by
  let E i := (fun x => (m i:ℝ)*V x) '' K i
  have hE i : IsCompact (E i) := (hK i).image (continuous_const.mul hV)
  let O i := U i ∩ {x : ℝ | x ≠ 0}
  have hO i : IsOpen (O i) := (hU i).inter isOpen_compl_singleton
  have hEO i : E i ⊆ O i := by
    intro z hz
    refine ⟨hKU i hz,?_⟩
    obtain ⟨x,hx,rfl⟩ := hz
    exact mul_ne_zero (by exact_mod_cast hm i) (hzero _ (hKI i hx))
  obtain ⟨χ,hχ,hχd⟩ := finite_disjoint_frequency_cutoffs E O hE hO hEO
    (frequency_images_disjoint m V I K hm hi hKI hsep hdisj)
  have hz i : χ i 0 = 0 := by
    by_contra h
    exact ((hχ i).2.2.1 (subset_tsupport (χ i) h)).2 rfl
  obtain ⟨S,hS,hSd,hS'⟩ := disjoint_frequency_indices χ (fun i => (hχ i).2.1) hz hχd
  exact ⟨χ,S,fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1.trans inter_subset_left,
    (hχ i).2.2.2⟩,hχd,hS,hSd,hS'⟩

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace ThreeTorus
namespace CompactParameter

/-- Compact-parameter differentiation, used by the exact passage near epsilon=0. -/
lemma hasFDerivAt_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (hF : ContDiff ℝ 1 F) (a b : ℝ) (x : E) :
    HasFDerivAt (fun y => ∫ t in a..b, F (y,t))
      (∫ t in a..b, (fderiv ℝ F (x,t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  let D : E × ℝ → E →L[ℝ] G := fun p =>
    (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD : Continuous D := hF.continuous_fderiv (by norm_num) |>.clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hD.continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := fun y t => F (y,t)) (F' := fun y t => D (y,t))
    (bound := fun _ => C) (Metric.closedBall_mem_nhds x (by norm_num : (0:ℝ)<1)) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_
  · exact Eventually.of_forall (fun y => (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro y hy
    exact hC (y,t) ⟨hy,uIoc_subset_uIcc ht⟩
  · exact Eventually.of_forall (fun t y _ => by
      simpa [D,Function.comp_def] using ((hF.differentiable one_ne_zero ((ContinuousLinearMap.inl ℝ E ℝ) y+(0,t))).hasFDerivAt).comp y
        ((ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt.add_const (0,t)))

/-- Smooth parameter integration over a fixed compact interval. -/
lemma contDiff_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (n : ℕ) {F : E × ℝ → G} (hF : ContDiff ℝ n F) (a b : ℝ) :
    ContDiff ℝ n (fun y => ∫ t in a..b, F (y,t)) := by
  induction n generalizing G with
  | zero =>
    apply contDiff_zero.mpr
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (show Continuous (Function.uncurry (fun y t => F (y,t))) from hF.continuous) a b
  | succ n ih =>
    let D : E × ℝ → E →L[ℝ] G := fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hD : ContDiff ℝ n D := (hF.fderiv_right (by simp)).clm_comp contDiff_const
    have hder (x : E) := hasFDerivAt_compact_integral (hF.of_le (by exact_mod_cast Nat.succ_pos n)) a b x
    rw [show ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 by simp, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hder x).differentiableAt, ?_, ?_⟩
    · simp
    · have heq : fderiv ℝ (fun y => ∫ t in a..b, F (y,t)) =
          fun y => ∫ t in a..b, D (y,t) := by
        funext y
        exact (hder y).fderiv
      rw [heq]
      exact ih hD

lemma smooth_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (a b : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ t in a..b, F (y,t)) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_compact_integral n (hF.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))) a b

end CompactParameter

/-- Smoothness of a Fourier coefficient in an arbitrary finite-dimensional
parameter, obtained from a compact interval integral of the literal lift. -/
lemma smooth_fourierCoeff_param {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → UnitAddCircle → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × ℝ => f p.1 (p.2 : UnitAddCircle))) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => fourierCoeff (f x) j) := by
  have hchar : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × ℝ => (fourier (-j) (p.2 : UnitAddCircle) : ℂ)) := by
    simp only [fourier_coe_apply, Complex.ofReal_one, div_one]
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd)).cexp
  have h := CompactParameter.smooth_compact_integral (hchar.mul hf) 0 1
  have he (x : E) : fourierCoeff (f x) j =
      ∫ t in (0:ℝ)..1, (fourier (-j) (t : UnitAddCircle) : ℂ) * f x t := by
    simpa only [one_div_one,one_smul,zero_add,smul_eq_mul] using
      fourierCoeff_eq_intervalIntegral (f x) j 0
  simpa only [he] using h

lemma smooth_fourier_lift (m : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => (fourier m (x : UnitAddCircle) : ℂ)) := by
  simp only [fourier_coe_apply,Complex.ofReal_one,div_one]
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

/-- Smoothness of the exact old-amplitude coefficients; no stationary-phase
approximation replaces these coefficients. -/
lemma smooth_exactPassageCoeff {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {Hl : ℝ → ℝ} {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hHl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Hl)
    (hH : ∀ t : ℝ, H (t : UnitAddCircle) = (Hl t : UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A (p.1,p.2))) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun a : ℝ => exactPassageCoeff m H A j a) := by
  apply smooth_fourierCoeff_param
  change ContDiff ℝ _ (fun p : ℝ × ℝ => A (p.2,p.1)*fourier m (H p.2))
  simp_rw [hH]
  exact (hA.comp (contDiff_snd.prodMk contDiff_fst)).mul ((smooth_fourier_lift m).comp (hHl.comp contDiff_snd))

/-- The new amplitudes retained by the passage lie in the same smooth packet
class needed for its next use. -/
lemma smooth_retained_amplitude {m j : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {Hl : ℝ → ℝ} {A : UnitAddCircle × UnitAddCircle → ℂ}
    {χ : ℝ × UnitAddCircle → ℝ} {ψ : UnitAddCircle → ℝ} (s : ℝ)
    (hHl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Hl)
    (hH : ∀ t : ℝ, H (t : UnitAddCircle) = (Hl t : UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (hχ : CylinderSmooth χ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a : ℝ => ψ a)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ =>
      (χ (s,p.1):ℂ)*(ψ p.1:ℂ)*exactPassageCoeff m H A j p.1*fourier m (p.2:UnitAddCircle)) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => χ (s,(p.1:UnitAddCircle))) :=
    hχ.comp (contDiff_const.prodMk contDiff_fst)
  exact (((Complex.ofRealCLM.contDiff.comp hc).mul (Complex.ofRealCLM.contDiff.comp (hψ.comp contDiff_fst))).mul
    ((smooth_exactPassageCoeff hHl hH hA j).comp contDiff_fst)).mul
      ((smooth_fourier_lift m).comp contDiff_snd)

end ThreeTorus

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology ENNReal
namespace ThreeTorus

/-- A nonnegative integrable density identity proved with signed vector
measures is the identical ordinary measure identity. -/
lemma positive_density_map_of_vectorMeasure
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} {q : X → ℝ} {p : Y → ℝ}
    (hf : Measurable f) (hq : Integrable q μ) (hp : Integrable p ν)
    (hq0 : ∀ x, 0 ≤ q x) (hp0 : ∀ y, 0 ≤ p y)
    (he : (μ.withDensityᵥ q).map f = ν.withDensityᵥ p) :
    (μ.withDensity (fun x => ENNReal.ofReal (q x))).map f =
      ν.withDensity (fun y => ENNReal.ofReal (p y)) := by
  ext s hs
  rw [Measure.map_apply hf hs,withDensity_apply _ (hf hs),withDensity_apply _ hs]
  rw [← ofReal_integral_eq_lintegral_ofReal hq.integrableOn (Eventually.of_forall hq0),
    ← ofReal_integral_eq_lintegral_ofReal hp.integrableOn (Eventually.of_forall hp0)]
  congr 1
  have h := congrArg (fun v : VectorMeasure Y ℝ => v s) he
  simpa only [VectorMeasure.map_apply _ hf hs,withDensityᵥ_apply hq (hf hs),
    withDensityᵥ_apply hp hs] using h

lemma branchDensity_nonneg {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : ∀ t, 0 ≤ q t) (y : ℝ) : 0 ≤ branchDensity I J g D q y := by
  classical
  simp only [branchDensity,Set.indicator_apply]
  split_ifs
  · exact div_nonneg (hq _) (abs_nonneg _)
  · rfl

lemma unfoldedModeDensity_nonneg {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : ∀ t, 0 ≤ q t) {n : ℝ} (hn : 0 ≤ n) (j t : ℝ) :
    0 ≤ unfoldedModeDensity I J g D q n j t := by
  unfold unfoldedModeDensity scaledBranchKernel
  exact mul_nonneg (inv_nonneg.mpr (abs_nonneg _))
    (branchDensity_nonneg (fun a => mul_nonneg hn (hq a)) _)

lemma foldCircleDensity_nonneg {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) (z : UnitAddCircle) :
    0 ≤ foldCircleDensity q z := by
  unfold foldCircleDensity periodizedReal
  exact tsum_nonneg (fun k => hq _)

/-- The literal new amplitude at a retained angular mode. -/
def retainedAmplitude (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ)
    (p : UnitAddCircle × UnitAddCircle) : ℂ :=
  (ψ p.1:ℂ)*(χ ((j:ℝ)/n) p.1:ℂ)*exactPassageCoeff m (H n) A j p.1*fourier m p.2

lemma retainedPassage_eq_sum_packets (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S : Finset ℤ) (n : ℕ) (x : TripleTorus) :
    retainedPassage m (H n) A S (fun j => χ ((j:ℝ)/n)) ψ x =
      ∑ j ∈ S, packet j (retainedAmplitude ψ χ m H A n j) x := rfl

lemma retainedAmplitude_norm_sq (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ)
    (p : UnitAddCircle × UnitAddCircle) :
    ‖retainedAmplitude ψ χ m H A n j p‖^2 =
      retainedCircleWeight ψ χ (fun n j => exactPassageCoeff m (H n) A j) n j p.1 := by
  simp only [retainedAmplitude,norm_mul,show ‖fourier m p.2‖ = 1 from Circle.norm_coe _,
    mul_one,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,retainedCircleWeight]

lemma retainedAmplitude_modulus (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) (a b : UnitAddCircle) :
    ‖retainedAmplitude ψ χ m H A n j (a,b)‖ =
      ‖retainedAmplitude ψ χ m H A n j (a,0)‖ := by
  simp only [retainedAmplitude,norm_mul,show ‖fourier m b‖ = 1 from Circle.norm_coe _,
    show ‖fourier m (0:UnitAddCircle)‖ = 1 from Circle.norm_coe _]

-- The same elementary identity used in the supplied whitening proof.
lemma map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {ζ : X → Y} {w : Y → ℝ≥0∞}
    (hζ : Measurable ζ) (hw : Measurable w) :
    (μ.withDensity (w ∘ ζ)).map ζ = (μ.map ζ).withDensity w := by
  ext s hs
  rw [Measure.map_apply hζ hs, withDensity_apply _ (hζ hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hζ hs), ← lintegral_indicator hs,
    lintegral_map (hw.indicator hs) hζ]
  apply lintegral_congr
  intro x
  rfl

/-- If a coefficient's modulus is independent of its spare coordinate, its
literal packet spectral measure is the single-coordinate weighted image. -/
lemma packetSpectralMeasure_of_modulus
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) {j : ℤ}
    {B : UnitAddCircle × UnitAddCircle → ℂ} {q : UnitAddCircle → ℝ}
    (hq : Measurable q) (hB : ∀ p, ‖B p‖^2 = q p.1) :
    packetSpectralMeasure φ j B =
      (AddCircle.haarAddCircle.withDensity (fun a => ENNReal.ofReal (q a))).map
        (fun a => j • φ a) := by
  unfold packetSpectralMeasure
  have he : (fun p : UnitAddCircle × UnitAddCircle => ENNReal.ofReal (‖B p‖^2)) =
      (fun a => ENNReal.ofReal (q a)) ∘ Prod.fst := funext (fun p => congrArg _ (hB p))
  rw [he]
  change Measure.map ((fun a => j • φ a) ∘ Prod.fst) _ = _
  rw [← Measure.map_map (show Measurable (fun a => j • φ a) from hφ.const_smul j) measurable_fst,
    map_withDensity_comp slowVolume measurable_fst hq.ennreal_ofReal]
  simp only [slowVolume,Measure.map_fst_prod,measure_univ,one_smul]

lemma retainedCircleWeight_nonneg (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (c : ℕ → ℤ → UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) (a : UnitAddCircle) :
    0 ≤ retainedCircleWeight ψ χ c n j a := by unfold retainedCircleWeight; positivity

lemma circleDensityLift_nonneg {q : UnitAddCircle → ℝ} (hq : ∀ a, 0 ≤ q a)
    (o x : ℝ) : 0 ≤ circleDensityLift o q x := by
  classical
  simp only [circleDensityLift,Set.indicator_apply]
  split_ifs
  · exact hq _
  · rfl

/-- The folded branch is the ordinary (positive) spectral density, not just
an identity of signed integrals. -/
lemma positive_foldedModeDensity_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqm : Measurable q₀)
    (hq0 : ∀ a, 0 ≤ q a) (hq00 : ∀ x, 0 ≤ q₀ x)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n j : ℝ} (hn : 0 < n) (hjn : j ≠ 0) :
    (AddCircle.haarAddCircle.withDensity (fun a => ENNReal.ofReal (q a))).map
        (fun a => (((j+(j/n)*J a)/n : ℝ) : UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensity
        (fun z => ENNReal.ofReal
          (foldCircleDensity (unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀ n j) z)) := by
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hD : ∀ x ∈ I, HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hmi := measurable_unfoldedModeDensity hJ hIo hinj hd hqm n j
  have hii := integrable_unfoldedModeDensity hIo.measurableSet
    (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet hD hinj
    (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hqi hn hjn
  exact positive_density_map_of_vectorMeasure
    (AddCircle.measurable_mk'.comp ((measurable_const.add (hj.const_mul _)).div_const n))
    hq (integrable_foldCircleDensity hmi hii) hq0
    (foldCircleDensity_nonneg (unfoldedModeDensity_nonneg hq00 hn.le j))
    (foldedModeDensity_pushforward hq hqm hq₀ hq₀s hqs hj hJ hJe hIo hinj hd hn hjn)

lemma passage_speed_mode (J : UnitAddCircle → ℝ) (n : ℝ) (j : ℤ) (a : UnitAddCircle) :
    j • (((1+J a/n)/n : ℝ) : UnitAddCircle) =
      ((((j:ℝ)+((j:ℝ)/n)*J a)/n : ℝ) : UnitAddCircle) := by
  rw [← AddCircle.coe_zsmul]
  congr 1
  simp only [zsmul_eq_mul]
  ring

/-- Any coefficient with the actual retained modulus has the displayed
nonnegative folded density under the actual new twist. -/
lemma packetSpectralMeasure_new_speed {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    {B : UnitAddCircle × UnitAddCircle → ℂ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqmeas : Measurable q) (hqm : Measurable q₀)
    (hB : ∀ p, ‖B p‖^2 = q p.1) (hq00 : ∀ x, 0 ≤ q₀ x)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n : ℝ} {j : ℤ} (hn : 0 < n) (hjn : j ≠ 0) :
    packetSpectralMeasure (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) j B =
      AddCircle.haarAddCircle.withDensity
        (fun z => ENNReal.ofReal
          (foldCircleDensity (unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀ n j) z)) := by
  have hσ : Measurable (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp ((measurable_const.add (hj.div_const n)).div_const n)
  rw [packetSpectralMeasure_of_modulus hσ hqmeas hB]
  simp_rw [passage_speed_mode]
  exact positive_foldedModeDensity_pushforward hq hqm
    (fun a => (hB (a,0)) ▸ sq_nonneg _) hq00 hq₀ hq₀s hqs hj hJ hJe hIo hinj hd hn
    (by exact_mod_cast hjn)

/-- Density identity for the literal retained coefficient used by the passage.
The only support hypothesis is that the cutoff lies on the chosen good branch. -/
lemma retainedAmplitude_spectralDensity
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle} {A : UnitAddCircle × UnitAddCircle → ℂ}
    {J : UnitAddCircle → ℝ} {J₀ : ℝ → ℝ} {o : ℝ} {I : Set ℝ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry)
    (hH : ∀ n, Continuous (H n)) (hA : Continuous A)
    (hψs : ∀ x ∈ Ioc o (o+1), ψ (x:UnitAddCircle) ≠ 0 → x ∈ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n : ℕ} {j : ℤ} (hn : 0 < n) (hjn : j ≠ 0) :
    packetSpectralMeasure (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) j
      (retainedAmplitude ψ χ m H A n j) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
          (circleDensityLift o (retainedCircleWeight ψ χ
            (fun n j => exactPassageCoeff m (H n) A j) n j)) n j) z)) := by
  let C n j := exactPassageCoeff m (H n) A j
  let q := retainedCircleWeight ψ χ C n j
  have hC n j : Continuous (C n j) := continuous_exactPassageCoeff (hH n) hA j
  have hq : Continuous q :=
    ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
      ((hC n j).norm.pow 2)
  have hqs : support (circleDensityLift o q) ⊆ Ioc o (o+1) ∩ I := by
    intro x hx
    have hxI : x ∈ Ioc o (o+1) := by
      by_contra hh
      exact hx (by simp [circleDensityLift,hh])
    refine ⟨hxI,hψs x hxI ?_⟩
    intro hz
    exact hx (by simp [circleDensityLift,hxI,q,retainedCircleWeight,hz])
  exact packetSpectralMeasure_new_speed
    (retainedCircleWeight_integrable hψ hχ hC n j) hq.measurable
    (measurable_circleDensityLift hq.measurable o)
    (retainedAmplitude_norm_sq ψ χ m H A n j)
    (circleDensityLift_nonneg (retainedCircleWeight_nonneg ψ χ C n j) o)
    (fun _ hx => by simp only [circleDensityLift,indicator_of_mem hx]; rfl)
    (hqs.trans inter_subset_left) (hqs.trans inter_subset_right)
    hj hJ hJe hIo hinj hd (by exact_mod_cast hn) hjn

lemma packet_twisted_pair_zero {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) (hB : Continuous B)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ) {m k : ℤ}
    (hdisj : m = k → Disjoint (support A) (support B)) (n : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*packet k B (twistIter φ n x)
      ∂tripleVolume) = 0 := by
  let B' : UnitAddCircle × UnitAddCircle → ℂ := fun p => fourier n (k • φ p.1)*B p
  have hb' : Continuous B' :=
    ((fourier n).continuous.comp ((hφ.comp continuous_fst).const_smul k)).mul hB
  have he (x : TripleTorus) : packet k B (twistIter φ n x) = packet k B' x := by
    rw [packet_twistIter]
    dsimp [packet,B']
    ring
  simp_rw [he]
  rw [integral_packet_pair hA hb']
  split_ifs with hmk
  · apply integral_eq_zero_of_ae
    filter_upwards [] with p
    by_cases ha : A p = 0
    · simp [ha]
    · have hb : B p = 0 := by
        by_contra hh
        exact Set.disjoint_left.mp (hdisj hmk) ha hh
      simp [B',hb]
  · rfl

/-- The spectral measure of a smooth disjoint packet list is the sum of the
literal packet pushforwards, demonstrated by every bilateral Fourier moment. -/
lemma disjoint_packet_list_correlation {ι : Type*} [Fintype ι]
    (m : ι → ℤ) (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (hA : ∀ i, Continuous (A i)) {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ)
    (hd : ∀ i j, i ≠ j → m i = m j → Disjoint (support (A i)) (support (A j)))
    (n : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (∑ i, packet (m i) (A i) x)*
        (∑ i, packet (m i) (A i) (twistIter φ n x)) ∂tripleVolume) =
      ∑ i, ∫ z, fourier n z ∂packetSpectralMeasure φ (m i) (A i) := by
  classical
  have ht : Continuous (twistIter φ n) :=
    (continuous_fst.add ((hφ.comp (continuous_fst.comp continuous_snd)).const_smul n)).prodMk
      continuous_snd
  have hc (i j : ι) : Continuous (fun x : TripleTorus =>
      starRingEnd ℂ (packet (m i) (A i) x)*packet (m j) (A j) (twistIter φ n x)) :=
    (Complex.continuous_conj.comp (continuous_packet (hA i))).mul
      ((continuous_packet (hA j)).comp ht)
  have hi (i j : ι) : Integrable (fun x : TripleTorus =>
      starRingEnd ℂ (packet (m i) (A i) x)*packet (m j) (A j) (twistIter φ n x)) tripleVolume :=
    (hc i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [map_sum,Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j),Finset.sum_eq_single i]
  · exact (packet_spectral_moment hφ (hA i) (m i) n).symm
  · intro j _ hji
    exact packet_twisted_pair_zero (hA i) (hA j) hφ (hd i j hji.symm) n
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end ThreeTorus
end
end
end
end
end
end

section

/-! Exact spectral identity for the literal retained packet vector. This closes
 the interface between the previously proved coefficient-density estimates and
 the actual Koopman correlations, without an abstract density hypothesis. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma foldCircleDensity_add_ae {q r : ℝ → ℝ} (hq : Measurable q) (hr : Measurable r)
    (hqi : Integrable q) (hri : Integrable r) :
    foldCircleDensity (fun x => q x+r x) =ᵐ[AddCircle.haarAddCircle]
      fun z => foldCircleDensity q z+foldCircleDensity r z := by
  apply (integrable_foldCircleDensity (hq.add hr) (hqi.add hri)).ae_eq_of_withDensityᵥ_eq
    ((integrable_foldCircleDensity hq hqi).add (integrable_foldCircleDensity hr hri))
  rw [← foldCircleDensity_pushforward (hq.add hr) (hqi.add hri),
    withDensityᵥ_add hqi hri,
    withDensityᵥ_add (integrable_foldCircleDensity hq hqi) (integrable_foldCircleDensity hr hri)]
  have he := map_add (VectorMeasure.mapGm (fun x : ℝ => (x:UnitAddCircle)))
    (volume.withDensityᵥ q) (volume.withDensityᵥ r)
  change (volume.withDensityᵥ q+volume.withDensityᵥ r).map _ =
    (volume.withDensityᵥ q).map _+(volume.withDensityᵥ r).map _ at he
  rw [he,foldCircleDensity_pushforward hq hqi,foldCircleDensity_pushforward hr hri]

lemma foldCircleDensity_finsetSum_ae {ι : Type*} (S : Finset ι) (q : ι → ℝ → ℝ)
    (hq : ∀ i ∈ S, Measurable (q i)) (hqi : ∀ i ∈ S, Integrable (q i)) :
    foldCircleDensity (fun x => ∑ i ∈ S, q i x) =ᵐ[AddCircle.haarAddCircle]
      fun z => ∑ i ∈ S, foldCircleDensity (q i) z := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    filter_upwards [] with z
    simp [foldCircleDensity,periodizedReal,AddCircle.liftIoc,Set.domRestrict]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    have hh := foldCircleDensity_add_ae (hq i (Finset.mem_insert_self i S))
      (Finset.measurable_sum S (fun j hj => hq j (Finset.mem_insert_of_mem hj)))
      (hqi i (Finset.mem_insert_self i S))
      (integrable_finsetSum S (fun j hj => hqi j (Finset.mem_insert_of_mem hj)))
    have ht := ih (fun j hj => hq j (Finset.mem_insert_of_mem hj))
      (fun j hj => hqi j (Finset.mem_insert_of_mem hj))
    filter_upwards [hh,ht] with z hz ht
    rw [hz,ht]

lemma moment_withDensity_real {p : UnitAddCircle → ℝ} (hp : Measurable p)
    (hp0 : ∀ z, 0 ≤ p z) (v : UnitAddCircle → ℂ) :
    (∫ z, v z ∂AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (p z))) =
      ∫ z, (p z:ℂ)*v z ∂AddCircle.haarAddCircle := by
  rw [integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
    (by filter_upwards [] with z; finiteness)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (hp0 z),Complex.real_smul]

lemma continuous_retainedAmplitude
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle} {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry)
    (hH : ∀ n, Continuous (H n)) (hA : Continuous A) (n : ℕ) (j : ℤ) :
    Continuous (retainedAmplitude ψ χ m H A n j) := by
  unfold retainedAmplitude
  exact ((((Complex.continuous_ofReal.comp hψ).comp continuous_fst).mul
    (Complex.continuous_ofReal.comp (hχ.comp (continuous_const.prodMk continuous_fst)))).mul
    ((continuous_exactPassageCoeff (hH n) hA j).comp continuous_fst)).mul
      ((fourier m).continuous.comp continuous_snd)

/-- All bilateral Koopman moments of the actual finite retained vector are
exactly those of its explicit nonnegative folded coefficient density. -/
theorem retainedPassage_spectral_moment
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle} {A : UnitAddCircle × UnitAddCircle → ℂ}
    {J : UnitAddCircle → ℝ} {J₀ : ℝ → ℝ} {I : Set ℝ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry)
    (hH : ∀ n, Continuous (H n)) (hA : Continuous A)
    (hψs : ∀ x ∈ Ioc (0:ℝ) 1, ψ (x:UnitAddCircle) ≠ 0 → x ∈ I)
    (hj : Continuous J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n : ℕ} {S : Finset ℤ} (hn : 0 < n) (hS : ∀ j ∈ S, j ≠ 0) (k : ℤ) :
    let φ := fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)
    let f := retainedPassage m (H n) A S (fun j => χ ((j:ℝ)/n)) ψ
    (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter φ k x) ∂tripleVolume) =
      ∫ z, (exactRetainedPacketDensity I J₀ ψ χ m H A S n z:ℂ)*fourier k z
        ∂AddCircle.haarAddCircle := by
  classical
  dsimp only
  let φ := fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)
  let B := retainedAmplitude ψ χ m H A n
  let q := fun j : ℤ => unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
    (circleDensityLift 0 (retainedCircleWeight ψ χ
      (fun n j => exactPassageCoeff m (H n) A j) n j)) n j
  have hφ : Continuous φ :=
    (AddCircle.continuous_mk' 1).comp ((continuous_const.add (hj.div_const n)).div_const n)
  have hB j : Continuous (B j) := continuous_retainedAmplitude hψ hχ hH hA n j
  have hreg j (hjS : j ∈ S) := retained_unfolded_regular hJ hIo hinj hd hψ hχ
    (fun n j => continuous_exactPassageCoeff (m := m) (hH n) hA j) 0 hn (hS j hjS)
  have hqm j (hjS : j ∈ S) : Measurable (q j) := (hreg j hjS).1
  have hqi j (hjS : j ∈ S) : Integrable (q j) := (hreg j hjS).2
  have hq0 j : ∀ t, 0 ≤ q j t :=
    unfoldedModeDensity_nonneg (circleDensityLift_nonneg
      (retainedCircleWeight_nonneg ψ χ _ n j) 0) (Nat.cast_nonneg n) j
  have hds j (hjS : j ∈ S) : packetSpectralMeasure φ j (B j) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (foldCircleDensity (q j) z)) :=
    retainedAmplitude_spectralDensity hψ hχ hH hA (by simpa using hψs) hj.measurable
      hJ hJe hIo hinj hd hn (hS j hjS)
  have hfold := foldCircleDensity_finsetSum_ae S q hqm hqi
  have hint j (hjS : j ∈ S) : Integrable
      (fun z => (foldCircleDensity (q j) z:ℂ)*fourier k z) AddCircle.haarAddCircle :=
    (integrable_foldCircleDensity (hqm j hjS) (hqi j hjS)).ofReal.mul_bdd
      (fourier k).continuous.aestronglyMeasurable
      (ae_of_all _ (fun z => le_of_eq (Circle.norm_coe _)))
  have hc := disjoint_packet_list_correlation (fun j : S => (j:ℤ))
    (fun j : S => B j) (fun j => hB j) hφ
    (fun i j hij he => (hij (Subtype.ext he)).elim) k
  have hsum (x : TripleTorus) : (∑ j : S, packet (j:ℤ) (B j) x) =
      ∑ j ∈ S, packet j (B j) x := Finset.sum_coe_sort S (fun j => packet j (B j) x)
  simp_rw [hsum] at hc
  rw [Finset.sum_coe_sort S (fun j => ∫ z, fourier k z ∂packetSpectralMeasure φ j (B j))] at hc
  simp only [retainedPassage_eq_sum_packets]
  change (∫ x : TripleTorus, starRingEnd ℂ (∑ j ∈ S, packet j (B j) x)*
      (∑ j ∈ S, packet j (B j) (twistIter φ k x)) ∂tripleVolume) = _
  rw [hc]
  calc
    _ = ∑ j ∈ S, ∫ z, (foldCircleDensity (q j) z:ℂ)*fourier k z
        ∂AddCircle.haarAddCircle := by
      apply Finset.sum_congr rfl
      intro j hjS
      rw [hds j hjS]
      exact moment_withDensity_real (measurable_foldCircleDensity (hqm j hjS))
        (foldCircleDensity_nonneg (hq0 j)) (fourier k)
    _ = ∫ z, (∑ j ∈ S, (foldCircleDensity (q j) z:ℂ))*fourier k z
        ∂AddCircle.haarAddCircle := by
      simp_rw [Finset.sum_mul]
      exact (integral_finsetSum _ hint).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hfold] with z hz
      change (∑ j ∈ S, (foldCircleDensity (q j) z:ℂ))*fourier k z =
        (foldCircleDensity (fun t => ∑ j ∈ S, q j t) z:ℂ)*fourier k z
      rw [hz,Complex.ofReal_sum]

end ThreeTorus
end
end

section

/-! Smoothness at the edge of the good arc is essential: the actual retained
spectral densities must be valid smooth inputs to the next stage. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma support_branchDensity_subset {J q : ℝ → ℝ} {I : Set ℝ} :
    support (branchDensity I J (invFunOn J I) (deriv J) q) ⊆ J '' tsupport q := by
  intro y hy
  have hyI : y ∈ J '' I := by
    by_contra hh
    exact hy (by simp [branchDensity,hh])
  have hx := invFunOn_pos hyI
  refine ⟨invFunOn J I y,subset_tsupport q ?_,hx.2⟩
  intro hq
  exact hy (by simp [branchDensity,hyI,hq])

lemma branchDensity_compact {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : Continuous J) (hq : HasCompactSupport q) :
    HasCompactSupport (branchDensity I J (invFunOn J I) (deriv J) q) := by
  apply HasCompactSupport.intro (hq.image hJ)
  intro y hy
  exact notMem_support.mp (fun hh => hy (support_branchDensity_subset hh))

lemma branchDensity_smooth {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q)
    (hs : tsupport q ⊆ I) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let g := invFunOn J I
  have hM : IsCompact (J '' tsupport q) := hc.image hJ.continuous
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ J '' tsupport q
  · obtain ⟨x,hx,rfl⟩ := hy
    have hxI := hs hx
    have hyI : J x ∈ J '' I := mem_image_of_mem J hxI
    have hg := contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)
    have hge : g (J x) = x := hinj (invFunOn_pos hyI).1 hxI (invFunOn_pos hyI).2
    have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => |deriv J (g y)|) (J x) :=
      (contDiffAt_abs (by simpa only [hge] using hd x hxI)).comp (J x)
        (hD.contDiffAt.comp (J x) hg)
    have hquot := (hq.contDiffAt.comp (J x) hg).div hden
      (by simpa only [hge] using abs_ne_zero.mpr (hd x hxI))
    apply hquot.congr_of_eventuallyEq
    filter_upwards [(isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hyI] with z hz
    simp only [branchDensity,indicator_of_mem hz,g]
    rfl
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hy] with z hz
    exact notMem_support.mp (fun hh => hz (support_branchDensity_subset hh))

lemma unfoldedModeDensity_smooth {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q)
    (hs : tsupport q ⊆ I) (n j : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j) := by
  have hmul : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => n*q x) := contDiff_const.mul hq
  have hcs : HasCompactSupport (fun x => n*q x) := hc.mul_left
  have hs' : tsupport (fun x => n*q x) ⊆ I := tsupport_mul_subset_right.trans hs
  have hh := branchDensity_smooth hJ hIo hinj hd hmul hcs hs' 
  unfold unfoldedModeDensity scaledBranchKernel
  exact contDiff_const.mul (hh.comp ((contDiff_const.mul contDiff_id).sub contDiff_const |>.div_const _))

lemma unfoldedModeDensity_compact {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport q) {n j : ℝ} (hn : n ≠ 0) (hj : j ≠ 0) :
    HasCompactSupport (unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j) := by
  have hh := branchDensity_compact (I := I) hJ (hc.mul_left (f := fun _ => n))
  let e : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ n hn).trans (Homeomorph.addRight (-j))
  let e' : ℝ ≃ₜ ℝ := e.trans (Homeomorph.mulRight₀ (n/j) (div_ne_zero hn hj))
  have he (t : ℝ) : e' t = (n*t-j)/(j/n) := by
    dsimp [e',e]
    field_simp
    ring
  have hc' := hh.comp_homeomorph e'
  have heq : unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j =
      fun t => |j/n|⁻¹ * branchDensity I J (invFunOn J I) (deriv J) (fun x => n*q x) (e' t) := by
    funext t
    rw [he]
    rfl
  rw [heq]
  exact hc'.mul_left

lemma periodizedReal_eq_periodize {q : ℝ → ℝ} (hc : HasCompactSupport q) :
    periodizedReal q = periodize q := by
  funext x
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R+|x|+1)
  have hs : support (fun k : ℤ => q (x+k)) ⊆ (Finset.Icc (-(N:ℤ)) N : Set ℤ) := by
    intro k hk
    have hr := hR (x+k) (subset_tsupport q hk)
    have hh : |(k:ℝ)| < N := by
      have ha := abs_sub_le (x+(k:ℝ)) 0 x
      simp only [sub_zero,zero_sub,abs_neg,add_sub_cancel_left,Real.norm_eq_abs] at hr ha
      linarith
    have hab := abs_lt.mp hh
    simp only [Finset.mem_coe,Finset.mem_Icc]
    constructor
    · exact_mod_cast (by linarith : -(N:ℝ) ≤ (k:ℝ))
    · exact_mod_cast (by linarith : (k:ℝ) ≤ (N:ℝ))
  exact tsum_eq_finsum ((Finset.finite_toSet _).subset hs)

lemma foldCircleDensity_smooth_lift {q : ℝ → ℝ}
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => foldCircleDensity q (x:UnitAddCircle)) := by
  have he : (fun x : ℝ => foldCircleDensity q (x:UnitAddCircle)) = periodize q := by
    funext x
    rw [foldCircleDensity_coe_all]
    exact congrFun (periodizedReal_eq_periodize hc) x
  rw [he]
  exact contDiff_periodize hq hc

/-- The literal real lift of a retained coefficient weight. The smooth cutoff
is taken before the final passage integer, as in the source. -/
def realRetainedWeight (ψ₀ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) (x : ℝ) : ℝ :=
  ψ₀ x^2*χ ((j:ℝ)/n) x^2*‖exactPassageCoeff m (H n) A j x‖^2

lemma realRetainedWeight_support (ψ₀ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) :
    tsupport (realRetainedWeight ψ₀ χ m H A n j) ⊆ tsupport ψ₀ := by
  apply closure_mono
  intro x hx hz
  exact hx (by simp [realRetainedWeight,hz])

lemma realRetainedWeight_compact {ψ₀ : ℝ → ℝ} (hc : HasCompactSupport ψ₀)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) :
    HasCompactSupport (realRetainedWeight ψ₀ χ m H A n j) :=
  hc.of_isClosed_subset isClosed_closure (realRetainedWeight_support ψ₀ χ m H A n j)

lemma realRetainedWeight_smooth {ψ₀ : ℝ → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀)
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (n : ℕ) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (realRetainedWeight ψ₀ χ m H A n j) := by
  have hχ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => χ ((j:ℝ)/n) x) := hχ.comp (contDiff_const.prodMk contDiff_id)
  exact ((hψ.pow 2).mul (hχ'.pow 2)).mul
    ((smooth_exactPassageCoeff (hHl n) (hH n) hA j).norm_sq (𝕜 := ℂ))

lemma retainedWeight_lift_eq {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1)) :
    circleDensityLift 0 (retainedCircleWeight ψ χ
      (fun n j => exactPassageCoeff m (H n) A j) n j) =
      realRetainedWeight ψ₀ χ m H A n j := by
  apply circleDensityLift_eq
  · intro x hx
    simp only [retainedCircleWeight,realRetainedWeight,he x hx]
  · exact (subset_tsupport _).trans ((realRetainedWeight_support ψ₀ χ m H A n j).trans hs)

/-- Actual retained densities are smooth at all branch edges, including their
zero set. This supplies the next passage's regularity; it is not an assumption
that the density is already smooth. -/
theorem exactRetainedPacketDensity_smooth_lift
    {I : Set ℝ} {J : ℝ → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {m : ℤ}
    {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {S : Finset ℤ} {n : ℕ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hc : HasCompactSupport ψ₀)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1) ∩ I)
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (hn : 0 < n) (hS : ∀ j ∈ S, j ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => exactRetainedPacketDensity I J ψ χ m H A S n x) := by
  unfold exactRetainedPacketDensity
  simp_rw [retainedWeight_lift_eq χ m H A n _ he (hs.trans inter_subset_left)]
  apply foldCircleDensity_smooth_lift
  · apply ContDiff.sum
    intro j hj
    exact unfoldedModeDensity_smooth hJ hIo hinj hd
      (realRetainedWeight_smooth hψ hχ hHl hH hA n j)
      (realRetainedWeight_compact hc χ m H A n j)
      ((realRetainedWeight_support ψ₀ χ m H A n j).trans (hs.trans inter_subset_right)) n j
  · have hh (j : ℤ) (hj : j ∈ S) : HasCompactSupport
        (unfoldedModeDensity I J (invFunOn J I) (deriv J)
          (realRetainedWeight ψ₀ χ m H A n j) n j) :=
      unfoldedModeDensity_compact hJ.continuous
        (realRetainedWeight_compact hc χ m H A n j)
        (by exact_mod_cast hn.ne') (by exact_mod_cast hS j hj)
    convert HasCompactSupport.finset_sum hh using 1
    first | rfl | (funext time; simp only [Finset.sum_apply])

lemma continuous_of_continuous_lift {Y : Type*} [TopologicalSpace Y]
    {f : UnitAddCircle → Y} (hf : Continuous (fun x : ℝ => f (x:UnitAddCircle))) :
    Continuous f :=
  isQuotientMap_quotient_mk'.continuous_iff.mpr hf

end ThreeTorus
end
end

section

/-! Identification of the reference stationary marginal with the actual old
packet spectrum. In particular integer carrier speeds do not change it. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma positive_circle_branch_fold
    {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqm : Measurable q₀)
    (hq0 : ∀ a, 0 ≤ q a) (hq00 : ∀ x, 0 ≤ q₀ x)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x:UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0) :
    (AddCircle.haarAddCircle.withDensity (fun a => ENNReal.ofReal (q a))).map
        (fun a => (J a:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀) z)) := by
  let w := branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hD : ∀ x ∈ I, HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hIm := (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet
  have hwi : Integrable w := integrable_branchDensity hIo.measurableSet hIm hD hinj
    (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hqi.integrableOn
  have hwm : Measurable w := measurable_branchDensity_smooth hJ hIo hinj hd hqm
  have hmap := circle_branch_pushforward hq hq₀ hq₀s hqs hj hJ.continuous.measurable hJe
    hIo.measurableSet hIm hD hinj (fun _ hx => hinj.leftInvOn_invFunOn hx) hd
  apply positive_density_map_of_vectorMeasure (AddCircle.measurable_mk'.comp hj) hq
    (integrable_foldCircleDensity hwm hwi) hq0
    (foldCircleDensity_nonneg (branchDensity_nonneg hq00))
  rw [← foldCircleDensity_pushforward hwm hwi,← hmap]
  exact (vectorMeasure_map_comp _ hj AddCircle.measurable_mk').symm

lemma stationaryWeight_change_branch {A : ℝ → ℂ} {J : ℝ → ℝ} {C I : Set ℝ}
    (hIC : I ⊆ C) (hi : InjOn J C) (hs : support A ⊆ I) :
    stationaryWeight C J A = stationaryWeight I J A := by
  have h := stationaryWeight_family_of_branch (Ω := Unit) hIC hi (fun _ => hs)
  funext s
  have hh := congrFun h (s,())
  exact hh

/-- The density of a literal old angular packet, not an abstract probability
model. The integer speed carrier vanishes on the temporal circle. -/
theorem oldPacket_spectralDensity_of_modulus
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : ℝ → ℂ}
    {v : UnitAddCircle → ℝ} {V : ℝ → ℝ} {m c : ℤ} {o : ℝ} {C I : Set ℝ}
    (hA : Continuous A) (hA₀ : Continuous A₀)
    (hmod : ∀ u a, ‖A (u,a)‖ = ‖A (u,0)‖)
    (hAe : ∀ x ∈ Ioc o (o+1), A ((x:UnitAddCircle),0) = A₀ x)
    (has : support A₀ ⊆ Ioc o (o+1)) (hAs : support A₀ ⊆ I)
    (hv : Measurable v) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVe : ∀ x ∈ I, v (x:UnitAddCircle) = V x)
    (hIo : IsOpen I) (hIC : I ⊆ C) (hinj : InjOn (fun x => (m:ℝ)*V x) C)
    (hd : ∀ x ∈ I, deriv (fun x => (m:ℝ)*V x) x ≠ 0) :
    packetSpectralMeasure (fun a => ((v a-c:ℝ):UnitAddCircle)) m A =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (stationaryWeight C (fun x => (m:ℝ)*V x) A₀) z)) := by
  have hqc : Continuous (fun u : UnitAddCircle => ‖A (u,0)‖^2) :=
    ((hA.comp (continuous_id.prodMk continuous_const)).norm.pow 2)
  have hps := packetSpectralMeasure_of_modulus
    (φ := fun a => (((v a-(c:ℝ)) : ℝ):UnitAddCircle)) (j := m) (B := A)
    (q := fun u => ‖A (u,0)‖^2)
    (AddCircle.measurable_mk'.comp (hv.sub measurable_const)) hqc.measurable
    (fun p => by rw [hmod])
  rw [hps]
  have hmode (a : UnitAddCircle) : m • ((v a-c:ℝ):UnitAddCircle) = ((m:ℝ)*v a:UnitAddCircle) := by
    rw [← AddCircle.coe_zsmul]
    simp only [zsmul_eq_mul]
    rw [mul_sub]
    have he : ((m:ℝ)*(c:ℝ):UnitAddCircle) = 0 := by
      rw [← Int.cast_mul]
      exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨m*c,by simp⟩
    rw [AddCircle.coe_sub,he,sub_zero]
  simp_rw [hmode]
  rw [stationaryWeight_change_branch hIC hinj hAs]
  apply positive_circle_branch_fold (q₀ := fun x => ‖A₀ x‖^2)
    (hqc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hA₀.norm.pow 2).measurable) (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
    (fun x hx => by rw [hAe x hx])
    (by intro x hx; apply has; intro hz; apply hx; simp [hz])
    (by intro x hx; apply hAs; intro hz; apply hx; simp [hz])
    (hv.const_mul (m:ℝ)) (contDiff_const.mul hV) (fun x hx => by rw [hVe x hx])
    hIo (hinj.mono hIC) hd

end ThreeTorus
end
end

section

/-! Actual old densities for amplitudes depending on both slow coordinates. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators ENNReal
namespace ThreeTorus

lemma map_fst_withDensity_marginal
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {q : X × Y → ℝ≥0∞} (hq : Measurable q) :
    ((μ.prod ν).withDensity q).map Prod.fst =
      μ.withDensity (fun x => ∫⁻ y, q (x,y) ∂ν) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs,withDensity_apply _ (measurable_fst hs),
    withDensity_apply _ hs,← lintegral_indicator (measurable_fst hs),
    ← lintegral_indicator hs,lintegral_prod _ (hq.indicator (measurable_fst hs)).aemeasurable]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx]
    apply lintegral_congr
    intro y
    exact Set.indicator_of_mem (show (x,y) ∈ Prod.fst ⁻¹' s from hx) q
  · simp only [Set.indicator_of_notMem hx]
    have hz (y : Y) : ((Prod.fst ⁻¹' s).indicator q) (x,y) = 0 :=
      Set.indicator_of_notMem (show (x,y) ∉ Prod.fst ⁻¹' s from hx) q
    simp only [hz,lintegral_zero]

lemma continuous_slowMarginal {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) :
    Continuous (fun u => ∫ a, ‖A (u,a)‖^2 ∂AddCircle.haarAddCircle) := by
  have hc : Continuous (uncurry (fun (u a : UnitAddCircle) => ‖A (u,a)‖^2)) := hA.norm.pow 2
  simpa only [setIntegral_univ] using
    continuous_parametric_integral_of_continuous (X := UnitAddCircle) (Y := UnitAddCircle)
      (μ := AddCircle.haarAddCircle) hc isCompact_univ

lemma packetSpectralMeasure_marginal {φ : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {m : ℤ}
    (hφ : Measurable φ) (hA : Continuous A) :
    packetSpectralMeasure φ m A =
      (AddCircle.haarAddCircle.withDensity (fun u => ENNReal.ofReal
        (∫ a, ‖A (u,a)‖^2 ∂AddCircle.haarAddCircle))).map (fun u => m • φ u) := by
  unfold packetSpectralMeasure slowVolume
  change Measure.map ((fun u => m • φ u) ∘ Prod.fst) _ = _
  rw [← Measure.map_map (show Measurable (fun u => m • φ u) from hφ.const_smul m) measurable_fst,
    map_fst_withDensity_marginal (q := fun p => ENNReal.ofReal (‖A p‖^2))
      (by simpa only [Pi.pow_apply] using (hA.norm.pow 2).measurable.ennreal_ofReal)]
  congr 2
  funext u
  exact (ofReal_integral_eq_lintegral_ofReal
    (((hA.comp (continuous_const.prodMk continuous_id)).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (ae_of_all _ (fun a => sq_nonneg _))).symm

lemma branchDensity_integral {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (I : Set ℝ) (J g D : ℝ → ℝ) (q : ℝ × Ω → ℝ) (s : ℝ) :
    branchDensity I J g D (fun u => ∫ a, q (u,a) ∂ν) s =
      ∫ a, branchDensity I J g D (fun u => q (u,a)) s ∂ν := by
  classical
  unfold branchDensity
  by_cases hs : s ∈ J '' I
  · simp only [Set.indicator_of_mem hs,integral_div]
  · simp only [Set.indicator_of_notMem hs,integral_zero]

/-- An arbitrary smooth/continuous old packet has the stationary marginal as
its temporal density. Spare-coordinate independence is not required. -/
theorem oldPacket_spectralDensity
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {v : UnitAddCircle → ℝ} {V : ℝ → ℝ} {m c : ℤ} {o : ℝ} {C I : Set ℝ}
    (hA : Continuous A) (hA₀ : Continuous A₀.uncurry)
    (hAe : ∀ a x, x ∈ Ioc o (o+1) → A ((x:UnitAddCircle),a) = A₀ a x)
    (has : ∀ a, support (A₀ a) ⊆ Ioc o (o+1)) (hAs : ∀ a, support (A₀ a) ⊆ I)
    (hv : Measurable v) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVe : ∀ x ∈ I, v (x:UnitAddCircle) = V x)
    (hIo : IsOpen I) (hIC : I ⊆ C) (hinj : InjOn (fun x => (m:ℝ)*V x) C)
    (hd : ∀ x ∈ I, deriv (fun x => (m:ℝ)*V x) x ≠ 0) :
    packetSpectralMeasure (fun a => ((v a-c:ℝ):UnitAddCircle)) m A =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (fun s => ∫ a, stationaryWeight C (fun x => (m:ℝ)*V x)
          (A₀ a) s ∂AddCircle.haarAddCircle) z)) := by
  let q : UnitAddCircle → ℝ := fun u => ∫ a, ‖A (u,a)‖^2 ∂AddCircle.haarAddCircle
  let q₀ : ℝ → ℝ := fun x => ∫ a, ‖A₀ a x‖^2 ∂AddCircle.haarAddCircle
  have hqc : Continuous q := continuous_slowMarginal hA
  have hq₀c : Continuous q₀ := by
    have hc : Continuous (uncurry (fun (x : ℝ) (a : UnitAddCircle) => ‖A₀ a x‖^2)) :=
      (hA₀.comp continuous_swap).norm.pow 2
    simpa only [q₀,setIntegral_univ] using
      continuous_parametric_integral_of_continuous (X := ℝ) (Y := UnitAddCircle)
        (μ := AddCircle.haarAddCircle) hc isCompact_univ
  have hs (K : Set ℝ) (hK : ∀ a, support (A₀ a) ⊆ K) : support q₀ ⊆ K := by
    intro x hx
    by_contra hnot
    apply hx
    have hz (a : UnitAddCircle) : A₀ a x = 0 := by
      by_contra hn
      exact hnot (hK a hn)
    simp only [q₀,hz,norm_zero,zero_pow (by decide : 2 ≠ 0),integral_zero]
  have hmap := packetSpectralMeasure_marginal (m := m) (A := A)
    (φ := fun a => (((v a-(c:ℝ)) : ℝ):UnitAddCircle))
    (AddCircle.measurable_mk'.comp (hv.sub measurable_const)) hA
  rw [hmap]
  have hmode (a : UnitAddCircle) : m • ((v a-c:ℝ):UnitAddCircle) =
      (((m:ℝ)*v a:ℝ):UnitAddCircle) := by
    rw [← AddCircle.coe_zsmul]
    simp only [zsmul_eq_mul]
    rw [mul_sub]
    have he : ((m:ℝ)*(c:ℝ):UnitAddCircle) = 0 := by
      rw [← Int.cast_mul]
      exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨m*c,by simp⟩
    rw [AddCircle.coe_sub,he,sub_zero]
  simp_rw [hmode]
  have hb : branchDensity I (fun x => (m:ℝ)*V x)
      (invFunOn (fun x => (m:ℝ)*V x) I) (deriv (fun x => (m:ℝ)*V x)) q₀ =
      fun s => ∫ a, stationaryWeight C (fun x => (m:ℝ)*V x) (A₀ a) s
        ∂AddCircle.haarAddCircle := by
    funext s
    rw [show q₀ = fun x => ∫ a, ‖A₀ a x‖^2 ∂AddCircle.haarAddCircle from rfl,
      branchDensity_integral (q := fun p : ℝ × UnitAddCircle => ‖A₀ p.2 p.1‖^2)]
    apply integral_congr_ae
    filter_upwards [] with a
    exact congrFun (stationaryWeight_change_branch hIC hinj (hAs a)).symm s
  rw [← hb]
  exact positive_circle_branch_fold
    (hqc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hq₀c.measurable (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun x hx => integral_congr_ae (ae_of_all _ (fun a => by dsimp only; rw [hAe a x hx])))
    (hs _ has) (hs _ hAs) (hv.const_mul (m:ℝ)) (contDiff_const.mul hV)
    (fun x hx => by rw [hVe x hx]) hIo (hinj.mono hIC) hd

end ThreeTorus
end
end

section

/-! The unchanged old spectral marginal, as a signed pushforward, for applying
L¹ contraction to physical cutoffs. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators ENNReal
namespace ThreeTorus

lemma signed_circle_branch_fold
    {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqm : Measurable q₀)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x:UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0) :
    Integrable (foldCircleDensity (branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀))
      AddCircle.haarAddCircle ∧
    (AddCircle.haarAddCircle.withDensityᵥ q).map (fun a => (J a:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensityᵥ
        (foldCircleDensity (branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀)) := by
  let w := branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hD : ∀ x ∈ I, HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hIm := (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet
  have hwi : Integrable w := integrable_branchDensity hIo.measurableSet hIm hD hinj
    (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hqi.integrableOn
  have hwm : Measurable w := measurable_branchDensity_smooth hJ hIo hinj hd hqm
  have hmap := circle_branch_pushforward hq hq₀ hq₀s hqs hj hJ.continuous.measurable hJe
    hIo.measurableSet hIm hD hinj (fun _ hx => hinj.leftInvOn_invFunOn hx) hd
  refine ⟨integrable_foldCircleDensity hwm hwi,?_⟩
  rw [← foldCircleDensity_pushforward hwm hwi,← hmap]
  exact (vectorMeasure_map_comp _ hj AddCircle.measurable_mk').symm

theorem oldStationaryMarginal_map
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {v : UnitAddCircle → ℝ} {V : ℝ → ℝ} {m : ℤ} {o : ℝ} {C I : Set ℝ}
    (hA : Continuous A) (hA₀ : Continuous A₀.uncurry)
    (hAe : ∀ a x, x ∈ Ioc o (o+1) → A ((x:UnitAddCircle),a) = A₀ a x)
    (has : ∀ a, support (A₀ a) ⊆ Ioc o (o+1)) (hAs : ∀ a, support (A₀ a) ⊆ I)
    (hv : Measurable v) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVe : ∀ x ∈ I, v (x:UnitAddCircle) = V x)
    (hIo : IsOpen I) (hIC : I ⊆ C) (hinj : InjOn (fun x => (m:ℝ)*V x) C)
    (hd : ∀ x ∈ I, deriv (fun x => (m:ℝ)*V x) x ≠ 0) :
    let p := foldCircleDensity (fun s => ∫ a, stationaryWeight C (fun x => (m:ℝ)*V x)
      (A₀ a) s ∂AddCircle.haarAddCircle)
    Integrable p AddCircle.haarAddCircle ∧
      (AddCircle.haarAddCircle.withDensityᵥ (fun u => ∫ a, ‖A (u,a)‖^2
        ∂AddCircle.haarAddCircle)).map (fun u => (((m:ℝ)*v u : ℝ):UnitAddCircle)) =
          AddCircle.haarAddCircle.withDensityᵥ p := by
  dsimp only
  let q : UnitAddCircle → ℝ := fun u => ∫ a, ‖A (u,a)‖^2 ∂AddCircle.haarAddCircle
  let q₀ : ℝ → ℝ := fun x => ∫ a, ‖A₀ a x‖^2 ∂AddCircle.haarAddCircle
  have hqc : Continuous q := continuous_slowMarginal hA
  have hq₀c : Continuous q₀ := by
    have hc : Continuous (uncurry (fun (x : ℝ) (a : UnitAddCircle) => ‖A₀ a x‖^2)) :=
      (hA₀.comp continuous_swap).norm.pow 2
    simpa only [q₀,setIntegral_univ] using
      continuous_parametric_integral_of_continuous (X := ℝ) (Y := UnitAddCircle)
        (μ := AddCircle.haarAddCircle) hc isCompact_univ
  have hs (K : Set ℝ) (hK : ∀ a, support (A₀ a) ⊆ K) : support q₀ ⊆ K := by
    intro x hx
    by_contra hnot
    apply hx
    have hz (a : UnitAddCircle) : A₀ a x = 0 := by
      by_contra hn
      exact hnot (hK a hn)
    simp only [q₀,hz,norm_zero,zero_pow (by decide : 2 ≠ 0),integral_zero]
  have hb : branchDensity I (fun x => (m:ℝ)*V x)
      (invFunOn (fun x => (m:ℝ)*V x) I) (deriv (fun x => (m:ℝ)*V x)) q₀ =
      fun s => ∫ a, stationaryWeight C (fun x => (m:ℝ)*V x) (A₀ a) s
        ∂AddCircle.haarAddCircle := by
    funext s
    rw [show q₀ = fun x => ∫ a, ‖A₀ a x‖^2 ∂AddCircle.haarAddCircle from rfl,
      branchDensity_integral (q := fun p : ℝ × UnitAddCircle => ‖A₀ p.2 p.1‖^2)]
    apply integral_congr_ae
    filter_upwards [] with a
    exact congrFun (stationaryWeight_change_branch hIC hinj (hAs a)).symm s
  rw [← hb]
  exact signed_circle_branch_fold
    (hqc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hq₀c.measurable
    (fun x hx => integral_congr_ae (ae_of_all _ (fun a => by dsimp only; rw [hAe a x hx])))
    (hs _ has) (hs _ hAs) (hv.const_mul (m:ℝ)) (contDiff_const.mul hV)
    (fun x hx => by rw [hVe x hx]) hIo (hinj.mono hIC) hd

end ThreeTorus
end
end

section

/-! The neutral passage's old cutoff reference differs from the actual old
packet density by at most its physical missing mass. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma cutoff_slowMarginal_l1
    {A : UnitAddCircle × UnitAddCircle → ℂ} {ψ : UnitAddCircle → ℝ}
    (hA : Continuous A) (hψc : Continuous ψ) (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1)
    {B : ℝ} (_hB : 0 ≤ B) (hAb : ∀ p, ‖A p‖^2 ≤ B) :
    (∫ u, |(∫ a, ‖A (u,a)‖^2 ∂AddCircle.haarAddCircle)-
      (∫ a, ‖(ψ a:ℂ)*A (u,a)‖^2 ∂AddCircle.haarAddCircle)| ∂AddCircle.haarAddCircle) ≤
      B*(∫ a, (1-ψ a^2) ∂AddCircle.haarAddCircle) := by
  let D := B*(∫ a, (1-ψ a^2) ∂AddCircle.haarAddCircle)
  have hd : ∀ u, |(∫ a, ‖A (u,a)‖^2 ∂AddCircle.haarAddCircle)-
      (∫ a, ‖(ψ a:ℂ)*A (u,a)‖^2 ∂AddCircle.haarAddCircle)| ≤ D := by
    intro u
    have ha : Continuous (fun a => ‖A (u,a)‖^2) :=
      (hA.comp (continuous_const.prodMk continuous_id)).norm.pow 2
    have hap : Continuous (fun a => ‖(ψ a:ℂ)*A (u,a)‖^2) :=
      ((Complex.continuous_ofReal.comp hψc).mul
        (hA.comp (continuous_const.prodMk continuous_id))).norm.pow 2
    have hc : Continuous (fun a => ‖A (u,a)‖^2-‖(ψ a:ℂ)*A (u,a)‖^2) := ha.sub hap
    have he (a : UnitAddCircle) : ‖A (u,a)‖^2-‖(ψ a:ℂ)*A (u,a)‖^2 =
        (1-ψ a^2)*‖A (u,a)‖^2 := by
      simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      ring
    have hz (a : UnitAddCircle) : 0 ≤ ‖A (u,a)‖^2-‖(ψ a:ℂ)*A (u,a)‖^2 := by
      rw [he]
      exact mul_nonneg (by nlinarith [(hψ a).1,(hψ a).2]) (sq_nonneg _)
    rw [← integral_sub (ha.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hap.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      abs_of_nonneg (integral_nonneg hz)]
    have hbound : Continuous (fun a => B*(1-ψ a^2)) :=
      continuous_const.mul (continuous_const.sub (hψc.pow 2))
    calc
      _ ≤ ∫ a, B*(1-ψ a^2) ∂AddCircle.haarAddCircle := by
        apply integral_mono (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          (hbound.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        intro a
        dsimp only
        rw [he,mul_comm B]
        exact mul_le_mul_of_nonneg_left (hAb _) (by nlinarith [(hψ a).1,(hψ a).2])
      _ = D := by rw [integral_const_mul]
  calc
    _ ≤ ∫ _ : UnitAddCircle, D ∂AddCircle.haarAddCircle := by
      exact integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _)) (integrable_const D)
        (ae_of_all _ hd)
    _ = _ := by simp [D]

/-- The reference in the neutral Riemann estimate is genuinely the cutoff
old spectrum. Its loss is bounded independently of slope, residue modulus or
passage integer. -/
theorem oldStationaryMarginal_cutoff_l1
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {v : UnitAddCircle → ℝ} {V : ℝ → ℝ} {m : ℤ} {o : ℝ} {C I : Set ℝ}
    (hA : Continuous A) (hA₀ : Continuous A₀.uncurry)
    (hAe : ∀ a x, x ∈ Ioc o (o+1) → A ((x:UnitAddCircle),a) = A₀ a x)
    (has : ∀ a, support (A₀ a) ⊆ Ioc o (o+1)) (hAs : ∀ a, support (A₀ a) ⊆ I)
    (hv : Measurable v) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVe : ∀ x ∈ I, v (x:UnitAddCircle) = V x)
    (hIo : IsOpen I) (hIC : I ⊆ C) (hinj : InjOn (fun x => (m:ℝ)*V x) C)
    (hd : ∀ x ∈ I, deriv (fun x => (m:ℝ)*V x) x ≠ 0)
    {ψ : UnitAddCircle → ℝ} (hψc : Continuous ψ) (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hAb : ∀ p, ‖A p‖^2 ≤ B) :
    let p := foldCircleDensity (fun s => ∫ a, stationaryWeight C (fun x => (m:ℝ)*V x)
      (A₀ a) s ∂AddCircle.haarAddCircle)
    let pψ := foldCircleDensity (fun s => ∫ a, stationaryWeight C (fun x => (m:ℝ)*V x)
      (fun x => (ψ a:ℂ)*A₀ a x) s ∂AddCircle.haarAddCircle)
    (∫ z, |pψ z-p z| ∂AddCircle.haarAddCircle) ≤
      B*(∫ a, (1-ψ a^2) ∂AddCircle.haarAddCircle) := by
  dsimp only
  let Aψ : UnitAddCircle × UnitAddCircle → ℂ := fun p => (ψ p.2:ℂ)*A p
  let A₀ψ : UnitAddCircle → ℝ → ℂ := fun a x => (ψ a:ℂ)*A₀ a x
  have hAψ : Continuous Aψ := ((Complex.continuous_ofReal.comp hψc).comp continuous_snd).mul hA
  have hA₀ψ : Continuous A₀ψ.uncurry :=
    ((Complex.continuous_ofReal.comp hψc).comp continuous_fst).mul hA₀
  have hs (K : Set ℝ) (hK : ∀ a, support (A₀ a) ⊆ K) : ∀ a, support (A₀ψ a) ⊆ K := by
    intro a x hx
    exact hK a (right_ne_zero_of_mul hx)
  have he : ∀ a x, x ∈ Ioc o (o+1) → Aψ ((x:UnitAddCircle),a) = A₀ψ a x := by
    intro a x hx
    dsimp only [Aψ,A₀ψ]
    rw [hAe a x hx]
  obtain ⟨hpi,hmap⟩ := oldStationaryMarginal_map hA hA₀ hAe has hAs hv hV hVe hIo hIC hinj hd
  obtain ⟨hψi,hψmap⟩ := oldStationaryMarginal_map hAψ hA₀ψ he (hs _ has) (hs _ hAs)
    hv hV hVe hIo hIC hinj hd
  have hq := continuous_slowMarginal hA
  have hqψ := continuous_slowMarginal hAψ
  have hb := l1_pushforward_difference
    (hqψ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hψi hpi
    (AddCircle.measurable_mk'.comp (hv.const_mul (m:ℝ))) hψmap hmap
  refine hb.trans ?_
  simp only [Aψ,abs_sub_comm]
  exact cutoff_slowMarginal_l1 hA hψc hψ hB hAb

end ThreeTorus
end
end

section

/-! Quantitative physical and spectral conclusions for the same actual packet.
This is the analytic (not yet geometric finite-stage) transmission boundary. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators FourierTransform
namespace ThreeTorus

lemma sq_norm_sub_le_two (x y z : ℂ) :
    ‖x-z‖^2 ≤ 2*‖x-y‖^2+2*‖y-z‖^2 := by
  have hh : ‖x-z‖ ≤ ‖x-y‖+‖y-z‖ := by
    convert norm_add_le (x-y) (y-z) using 1
    congr 1
    ring
  have h0 := norm_nonneg (x-z)
  have h1 := norm_nonneg (x-y)
  have h2 := norm_nonneg (y-z)
  nlinarith [sq_nonneg (‖x-y‖-‖y-z‖)]

lemma continuous_passageChart {H : UnitAddCircle → UnitAddCircle} (hH : Continuous H) :
    Continuous (passageChart H) := by
  change Continuous (fun x : TripleTorus => (x.2.1,x.2.2,x.1+(-H x.2.1)))
  exact continuous_snd.fst.prodMk (continuous_snd.snd.prodMk
    (continuous_fst.add (hH.comp continuous_snd.fst).neg))

lemma continuous_retainedPassage {ψ : UnitAddCircle → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {m : ℤ}
    {H : ℕ → UnitAddCircle → UnitAddCircle} {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry)
    (hH : ∀ n, Continuous (H n)) (hA : Continuous A) (n : ℕ) (S : Finset ℤ) :
    Continuous (retainedPassage m (H n) A S (fun j => χ ((j:ℝ)/n)) ψ) := by
  change Continuous (fun x => ∑ j ∈ S, packet j (retainedAmplitude ψ χ m H A n j) x)
  exact continuous_finsetSum _ (fun j _ => continuous_packet
    (continuous_retainedAmplitude hψ hχ hH hA n j))

lemma cutoff_packet_error_eq {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hmod : ∀ u a, ‖A (u,a)‖ = ‖A (u,0)‖) (ψ : UnitAddCircle → ℝ) (m : ℤ) :
    (∫ x : TripleTorus, ‖packet m A x-(ψ x.2.2:ℂ)*packet m A x‖^2 ∂tripleVolume) =
      (∫ u, ‖A (u,0)‖^2 ∂AddCircle.haarAddCircle)*
      (∫ a, (1-ψ a)^2 ∂AddCircle.haarAddCircle) := by
  have he (x : TripleTorus) : ‖packet m A x-(ψ x.2.2:ℂ)*packet m A x‖^2 =
      ‖A (x.2.1,0)‖^2*(1-ψ x.2.2)^2 := by
    rw [show packet m A x-(ψ x.2.2:ℂ)*packet m A x =
      (1-(ψ x.2.2:ℂ))*packet m A x by ring]
    simp only [packet,norm_mul,fourier_apply,Circle.norm_coe,mul_one]
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      mul_pow,sq_abs,hmod]
    ring
  simp_rw [he]
  change (∫ x : UnitAddCircle × (UnitAddCircle × UnitAddCircle),
    ‖A (x.2.1,0)‖^2*(1-ψ x.2.2)^2 ∂AddCircle.haarAddCircle.prod slowVolume) = _
  rw [integral_fun_snd (μ := AddCircle.haarAddCircle) (ν := slowVolume)
    (fun p : UnitAddCircle × UnitAddCircle => ‖A (p.1,0)‖^2*(1-ψ p.2)^2)]
  simpa only [probReal_univ,one_smul] using
    (integral_prod_mul (μ := AddCircle.haarAddCircle) (ν := AddCircle.haarAddCircle)
      (fun u => ‖A (u,0)‖^2) (fun a => (1-ψ a)^2))

lemma cutoff_packet_error_le {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hmod : ∀ u a, ‖A (u,a)‖ = ‖A (u,0)‖) {δ : ℝ}
    (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8) (m : ℤ) :
    (∫ x : TripleTorus,
      ‖packet m A x-(neutralCircleCutoff c x.2.2:ℂ)*packet m A x‖^2 ∂tripleVolume) ≤
      (∫ u, ‖A (u,0)‖^2 ∂AddCircle.haarAddCircle)*(4*δ) := by
  rw [cutoff_packet_error_eq hmod]
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg (fun _ => sq_nonneg _))
  have hc := continuous_neutralCircleCutoff c
  have hi : Integrable (fun a => (1-neutralCircleCutoff c a^2)) AddCircle.haarAddCircle :=
    (continuous_const.sub (hc.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ a, (1-neutralCircleCutoff c a^2) ∂AddCircle.haarAddCircle := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun _ => sq_nonneg _)) hi
      exact ae_of_all _ (fun a => by
        have h := neutralCircleCutoff_bounds c hδ a
        nlinarith)
    _ ≤ _ := neutralCircleCutoff_error c hδ hδ'

/-- Removing the good-arc cutoff adds no assumed physical approximation.
Its missing mass is explicitly paid. -/
lemma uncut_retainedPassage_error_le
    {A : UnitAddCircle × UnitAddCircle → ℂ} {m : ℤ}
    {H : ℕ → UnitAddCircle → UnitAddCircle} {χ : ℝ → UnitAddCircle → ℝ}
    (hA : Continuous A) (hH : ∀ n, Continuous (H n)) (hχ : Continuous χ.uncurry)
    (hmod : ∀ u a, ‖A (u,a)‖ = ‖A (u,0)‖) {δ : ℝ}
    (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8) (n : ℕ) (S : Finset ℤ) :
    (∫ x : TripleTorus,
      ‖packet m A x-retainedPassage m (H n) A S (fun j => χ ((j:ℝ)/n))
        (neutralCircleCutoff c) (passageChart (H n) x)‖^2 ∂tripleVolume) ≤
      8*δ*(∫ u, ‖A (u,0)‖^2 ∂AddCircle.haarAddCircle)+
      2*(∫ x : TripleTorus,
      ‖(neutralCircleCutoff c x.2.2:ℂ)*packet m A x-
        retainedPassage m (H n) A S (fun j => χ ((j:ℝ)/n))
          (neutralCircleCutoff c) (passageChart (H n) x)‖^2 ∂tripleVolume) := by
  let f := packet m A
  let g := fun x : TripleTorus => (neutralCircleCutoff c x.2.2:ℂ)*f x
  let h := fun x : TripleTorus => retainedPassage m (H n) A S (fun j => χ ((j:ℝ)/n))
    (neutralCircleCutoff c) (passageChart (H n) x)
  have hf : Continuous f := continuous_packet hA
  have hg : Continuous g := (Complex.continuous_ofReal.comp
    ((continuous_neutralCircleCutoff c).comp continuous_snd.snd)).mul hf
  have hh : Continuous h :=
    (continuous_retainedPassage (continuous_neutralCircleCutoff c) hχ hH hA n S).comp
      (continuous_passageChart (hH n))
  have hi (v w : TripleTorus → ℂ) (hv : Continuous v) (hw : Continuous w) :
      Integrable (fun x => ‖v x-w x‖^2) tripleVolume :=
    ((hv.sub hw).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfg := hi f g hf hg
  have hgh := hi g h hg hh
  calc
    _ ≤ ∫ x, (2*‖f x-g x‖^2+2*‖g x-h x‖^2) ∂tripleVolume := by
      apply integral_mono (hi f h hf hh) ((hfg.const_mul 2).add (hgh.const_mul 2))
      intro x
      exact sq_norm_sub_le_two (f x) (g x) (h x)
    _ = 2*(∫ x, ‖f x-g x‖^2 ∂tripleVolume)+2*(∫ x, ‖g x-h x‖^2 ∂tripleVolume) := by
      rw [integral_add (hfg.const_mul 2) (hgh.const_mul 2),integral_const_mul,integral_const_mul]
    _ ≤ _ := by
      have hh := cutoff_packet_error_le hmod c hδ hδ' m
      change (∫ x, ‖f x-g x‖^2 ∂tripleVolume) ≤ _ at hh
      dsimp only [g,h]
      nlinarith

/-- A single actual quantile passage simultaneously satisfies the physical,
spectral, smoothness and all bilateral-moment conclusions. The passage integer
remains arbitrarily large after the law, cutoffs and amplitudes are fixed. -/
theorem exact_quantile_passage
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {Δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+Δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hΔt : Tendsto Δ atTop (𝓝 0))
    (hmod : ∀ a x, ‖A₀ a x‖ = ‖A₀ 0 x‖)
    (hmodA : ∀ u a, ‖A (u,a)‖ = ‖A (u,0)‖)
    (hAs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hρm : ∫ y, ρ y = 1)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, |ρ y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (ρ y : ℂ)) v = 0)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {χ : ℝ → UnitAddCircle → ℝ}
    (hχs : CylinderSmooth χ.uncurry)
    (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry) (hzχ : ∀ a, χ 0 a = 0)
    (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
    {g : UnitAddCircle → ℝ} (hg : Continuous g) {ε : ℝ}
    (hideal : ∀ s ∈ support (stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ 0)),
      ∀ y, |foldCircleDensity (scaledDensity ρ s) y-g y| ≤ ε)
    {η : ℝ} (hη : 0 < η) :
    let w := stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ 0)
    ∃ S : ℕ → Finset ℤ,
      (∀ n, 0 < n → ∀ j ∈ S n, j ≠ 0) ∧
      (∀ n, 0 < n → ∀ j ∉ S n, ∀ a, χ ((j:ℝ)/n) a = 0) ∧
      ∀ᶠ n : ℕ in atTop,
        let ψ := neutralCircleCutoff c
        let J := quantileCircleJitter ρ c
        let φ := fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)
        let f := retainedPassage m (H n) A (S n) (fun j => χ ((j:ℝ)/n)) ψ
        let p := exactRetainedPacketDensity (Ioo δ (1-δ)) (lawJitter ρ c) ψ χ m H A (S n) n
        (∫ x : TripleTorus, ‖packet m A x-f (passageChart (H n) x)‖^2 ∂tripleVolume) <
          8*δ*(∫ u, ‖A (u,0)‖^2 ∂AddCircle.haarAddCircle)+η ∧
        (∫ z, |p z-foldCircleDensity w z*g ((n:ℤ) • z)| ∂AddCircle.haarAddCircle) <
          (∫ s, w s)*(4*δ+ε)+η ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p x) ∧
        (∀ k : ℤ, (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter φ k x) ∂tripleVolume) =
          ∫ z, (p z:ℂ)*fourier k z ∂AddCircle.haarAddCircle) ∧
        (∀ j u a, ‖retainedAmplitude ψ χ m H A n j (u,a)‖ =
          ‖retainedAmplitude ψ χ m H A n j (u,0)‖) := by
  dsimp only
  obtain ⟨S,hSN,hST,hsp⟩ := exact_quantile_circle_spectral_estimate hm hH hA hA₀ hAc hAd hAr
    hsupp hlo huo hlu hR hPr hV hPV hdV h0 hHc hAcont hΔt hmod
    hρ hi hp hρm hC hb hF c hδ hδ' hχc hcχ hzχ hχ hχW hg hideal hη
  refine ⟨S,hSN,hST,?_⟩
  have hψc := continuous_neutralCircleCutoff c
  have hph := exact_physical_retainedPassage_tendsto hm hH hA hA₀ hAc hAd hsupp
    hlo huo hlu hR hPr hV hPV hdV hHc hAcont hΔt hχc hχ
    (neutralCircleCutoff c) hψc (neutralCircleCutoff_bounds c hδ) hχW S hST
  have hJs := lawJitter_smooth c hρ hi hp hρm
  have hJinj := lawJitter_injOn c hρ.continuous hi hp hρm hδ
  have hJd : ∀ x ∈ Ioo δ (1-δ), deriv (lawJitter ρ c) x ≠ 0 := by
    intro x hx
    obtain ⟨hd,hdp⟩ := lawJitter_deriv_pos c hρ hi hp hρm hδ hx
    rw [hd.deriv]
    exact hdp.ne'
  have hψs : tsupport c.ψ ⊆ Ioc (0:ℝ) (0+1) ∩ Ioo δ (1-δ) := by
    intro x hx
    have hh := c.ψ_support hx
    exact ⟨⟨by linarith [hh.1],by linarith [hh.2]⟩,hh⟩
  have heψ : ∀ x ∈ Ioc (0:ℝ) (0+1), neutralCircleCutoff c (x:UnitAddCircle) = c.ψ x := by
    intro x hx
    exact lawPsi_eq c hδ ⟨hx.1.le,by simpa using hx.2⟩
  have hψsupport : ∀ x ∈ Ioc (0:ℝ) 1,
      neutralCircleCutoff c (x:UnitAddCircle) ≠ 0 → x ∈ Ioo δ (1-δ) := by
    intro x hx hn
    rw [heψ x (by simpa using hx)] at hn
    exact (hψs (subset_tsupport c.ψ hn)).2
  have hHl : ∀ n : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (n:ℝ)*(Pr x+Δ n*x)) :=
    fun _ => contDiff_const.mul (hPr.add (contDiff_const.mul contDiff_id))
  filter_upwards [hsp,hph.eventually (eventually_lt_nhds (half_pos hη)),
    eventually_gt_atTop (0:ℕ)] with n hnsp hnph hn
  refine ⟨?_,hnsp,?_,?_,?_⟩
  · have hh := uncut_retainedPassage_error_le (m := m) hAcont hHc hχc hmodA c hδ hδ' n (S n)
    exact hh.trans_lt (by linarith)
  · exact exactRetainedPacketDensity_smooth_lift hJs isOpen_Ioo hJinj hJd
      c.ψ_smooth c.ψ_compact heψ hψs hχs hHl hH hAs hn (hSN n hn)
  · intro k
    exact retainedPassage_spectral_moment hψc hχc hHc hAcont hψsupport
      (continuous_quantileCircleJitter c hρ hi hp hρm) hJs
      (fun x _ => quantileCircleJitter_coe ρ c x) isOpen_Ioo hJinj hJd hn (hSN n hn) k
  · exact fun _ _ _ => retainedAmplitude_modulus _ _ _ _ _ _ _ _ _

end ThreeTorus
end
end

section

/-! Quantitative good-arc cutoff losses for genuine two-coordinate amplitudes.
This does not presume spare-coordinate independence. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma continuous_stationaryWeight_parameter {Ω : Type*} [TopologicalSpace Ω]
    {A : Ω → ℝ → ℂ} (hA : Continuous A.uncurry) (C : Set ℝ) (J : ℝ → ℝ) (s : ℝ) :
    Continuous (fun a => stationaryWeight C J (A a) s) := by
  classical
  unfold stationaryWeight branchDensity
  by_cases hs : s ∈ J '' C
  · simp only [Set.indicator_of_mem hs]
    exact ((hA.comp (continuous_id.prodMk continuous_const)).norm.pow 2).div_const _
  · simp only [Set.indicator_of_notMem hs]
    exact continuous_const

lemma stationaryCutoffLift_marginal {A : UnitAddCircle → ℝ → ℂ}
    {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ} {o : ℝ}
    (heψ : ∀ x ∈ Ioc o (o+1), ψ₀ x = ψ (x:UnitAddCircle))
    (hsψ : support ψ₀ ⊆ Ioc o (o+1)) (C : Set ℝ) (J : ℝ → ℝ) (s : ℝ) :
    (∫ a : ℝ, stationaryCutoffLift C J
      (fun p : ℝ × ℝ => A (p.2:UnitAddCircle) p.1) ψ₀ (a,s)) =
      ∫ a, stationaryWeight C J (fun x => (ψ a:ℂ)*A a x) s ∂AddCircle.haarAddCircle := by
  let q : UnitAddCircle → ℝ := fun a => ψ a^2*stationaryWeight C J (A a) s
  have he : circleDensityLift o q = fun a => stationaryCutoffLift C J
      (fun p : ℝ × ℝ => A (p.2:UnitAddCircle) p.1) ψ₀ (a,s) := by
    apply circleDensityLift_eq
    · intro x hx
      simp only [q,stationaryCutoffLift,heψ x hx]
    · intro x hx
      apply hsψ
      intro hz
      exact hx (by simp [stationaryCutoffLift,hz])
  rw [← he,circle_integral_lift]
  apply integral_congr_ae
  filter_upwards [] with a
  rw [stationaryWeight_mul]
  simp [q,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma packet_cutoff_error_uniform {A : UnitAddCircle × UnitAddCircle → ℂ}
    {ψ : UnitAddCircle → ℝ} (hψc : Continuous ψ) (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hAb : ∀ p, ‖A p‖^2 ≤ B) (m : ℤ) :
    (∫ x : TripleTorus, ‖packet m A x-(ψ x.2.2:ℂ)*packet m A x‖^2 ∂tripleVolume) ≤
      B*(∫ a, (1-ψ a^2) ∂AddCircle.haarAddCircle) := by
  have hc : Continuous (fun x : TripleTorus => B*(1-ψ x.2.2^2)) :=
    continuous_const.mul (continuous_const.sub ((hψc.comp continuous_snd.snd).pow 2))
  have hi := hc.integrable_of_hasCompactSupport (μ := tripleVolume)
    (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ x : TripleTorus, B*(1-ψ x.2.2^2) ∂tripleVolume := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun _ => sq_nonneg _)) hi
      filter_upwards [] with x
      have he : ‖packet m A x-(ψ x.2.2:ℂ)*packet m A x‖^2 =
          ‖A (x.2.1,x.2.2)‖^2*(1-ψ x.2.2)^2 := by
        rw [show packet m A x-(ψ x.2.2:ℂ)*packet m A x =
          (1-(ψ x.2.2:ℂ))*packet m A x by ring]
        simp only [packet,norm_mul,fourier_apply,Circle.norm_coe,mul_one]
        rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
          mul_pow,sq_abs]
        ring
      rw [he]
      have h := hψ x.2.2
      calc
        _ ≤ B*(1-ψ x.2.2)^2 := mul_le_mul_of_nonneg_right (hAb _) (sq_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) hB
    _ = _ := by
      change (∫ x : UnitAddCircle × (UnitAddCircle × UnitAddCircle),
        B*(1-ψ x.2.2^2) ∂AddCircle.haarAddCircle.prod slowVolume) = _
      rw [integral_fun_snd (μ := AddCircle.haarAddCircle (T := (1:ℝ))) (ν := slowVolume)
        (fun p : UnitAddCircle × UnitAddCircle => B*(1-ψ p.2^2))]
      simp only [probReal_univ,one_smul]
      change (∫ x : UnitAddCircle × UnitAddCircle, B*(1-ψ x.2^2)
        ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) = _
      rw [integral_fun_snd (μ := AddCircle.haarAddCircle (T := (1:ℝ)))
        (ν := AddCircle.haarAddCircle) (fun a : UnitAddCircle => B*(1-ψ a^2))]
      simp only [probReal_univ,one_smul,integral_const_mul]

lemma packet_neutral_cutoff_error {A : UnitAddCircle × UnitAddCircle → ℂ}
    {B : ℝ} (hB : 0 ≤ B) (hAb : ∀ p, ‖A p‖^2 ≤ B) {δ : ℝ}
    (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8) (m : ℤ) :
    (∫ x : TripleTorus, ‖packet m A x-(neutralCircleCutoff c x.2.2:ℂ)*packet m A x‖^2
      ∂tripleVolume) ≤ B*(4*δ) :=
  (packet_cutoff_error_uniform (continuous_neutralCircleCutoff c)
    (neutralCircleCutoff_bounds c hδ) hB hAb m).trans
      (mul_le_mul_of_nonneg_left (neutralCircleCutoff_error c hδ hδ') hB)

lemma uncut_retainedPassage_uniform_error
    {A : UnitAddCircle × UnitAddCircle → ℂ} {m : ℤ}
    {H : ℕ → UnitAddCircle → UnitAddCircle} {χ : ℝ → UnitAddCircle → ℝ}
    (hA : Continuous A) (hH : ∀ n, Continuous (H n)) (hχ : Continuous χ.uncurry)
    {B : ℝ} (hB : 0 ≤ B) (hAb : ∀ p, ‖A p‖^2 ≤ B) {δ : ℝ}
    (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8) (n : ℕ) (S : Finset ℤ) :
    (∫ x : TripleTorus,
      ‖packet m A x-retainedPassage m (H n) A S (fun j => χ ((j:ℝ)/n))
        (neutralCircleCutoff c) (passageChart (H n) x)‖^2 ∂tripleVolume) ≤
      8*δ*B+2*(∫ x : TripleTorus,
      ‖(neutralCircleCutoff c x.2.2:ℂ)*packet m A x-
        retainedPassage m (H n) A S (fun j => χ ((j:ℝ)/n))
          (neutralCircleCutoff c) (passageChart (H n) x)‖^2 ∂tripleVolume) := by
  let f := packet m A
  let g := fun x : TripleTorus => (neutralCircleCutoff c x.2.2:ℂ)*f x
  let h := fun x : TripleTorus => retainedPassage m (H n) A S (fun j => χ ((j:ℝ)/n))
    (neutralCircleCutoff c) (passageChart (H n) x)
  have hf : Continuous f := continuous_packet hA
  have hg : Continuous g := (Complex.continuous_ofReal.comp
    ((continuous_neutralCircleCutoff c).comp continuous_snd.snd)).mul hf
  have hh : Continuous h :=
    (continuous_retainedPassage (continuous_neutralCircleCutoff c) hχ hH hA n S).comp
      (continuous_passageChart (hH n))
  have hi (v w : TripleTorus → ℂ) (hv : Continuous v) (hw : Continuous w) :
      Integrable (fun x => ‖v x-w x‖^2) tripleVolume :=
    ((hv.sub hw).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfg := hi f g hf hg
  have hgh := hi g h hg hh
  calc
    _ ≤ ∫ x, (2*‖f x-g x‖^2+2*‖g x-h x‖^2) ∂tripleVolume := by
      apply integral_mono (hi f h hf hh) ((hfg.const_mul 2).add (hgh.const_mul 2))
      intro x
      exact sq_norm_sub_le_two (f x) (g x) (h x)
    _ = 2*(∫ x, ‖f x-g x‖^2 ∂tripleVolume)+2*(∫ x, ‖g x-h x‖^2 ∂tripleVolume) := by
      rw [integral_add (hfg.const_mul 2) (hgh.const_mul 2),integral_const_mul,integral_const_mul]
    _ ≤ _ := by
      have hh := packet_neutral_cutoff_error hB hAb c hδ hδ' m
      change (∫ x, ‖f x-g x‖^2 ∂tripleVolume) ≤ _ at hh
      dsimp only [g,h]
      nlinarith

end ThreeTorus
end
end

section

/-! The actual neutral refresh: a single retained vector simultaneously
approximates the old physical packet and its old temporal spectrum. The
amplitude may depend on both slow coordinates. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

theorem exact_neutral_passage
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {Δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+Δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hΔt : Tendsto Δ atTop (𝓝 0))
    (hAs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    {v : UnitAddCircle → ℝ} (hv : Measurable v) (hVe : ∀ x : ℝ, v (x:UnitAddCircle) = V x)
    {B : ℝ} (hB : 0 ≤ B) (hAb : ∀ p, ‖A p‖^2 ≤ B)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {χ : ℝ → UnitAddCircle → ℝ}
    (hχs : CylinderSmooth χ.uncurry)
    (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry) (hzχ : ∀ a, χ 0 a = 0)
    (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1) :
    let pold := foldCircleDensity (fun s => ∫ a, stationaryWeight (Icc (l-R) (u+R))
      (fun x => (m:ℝ)*V x) (A₀ a) s ∂AddCircle.haarAddCircle)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ β : ℝ,
      ∃ S : ℕ → Finset ℤ,
        (∀ n, 0 < n → ∀ j ∈ S n, j ≠ 0) ∧
        (∀ n, 0 < n → ∀ j ∉ S n, ∀ a, χ ((j:ℝ)/n) a = 0) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
          let ψ := neutralCircleCutoff c
          let J := neutralJitter c L β
          let φ := fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)
          let f := retainedPassage m (H n) A (S n) (fun j => χ ((j:ℝ)/n)) ψ
          let p := exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal c L β)
            ψ χ m H A (S n) n
          (∫ x : TripleTorus, ‖packet m A x-f (passageChart (H n) x)‖^2 ∂tripleVolume) <
            8*δ*B+η ∧
          (∫ z, |p z-pold z| ∂AddCircle.haarAddCircle) < C/L+4*δ*B+η ∧
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p x) ∧
          (∀ k : ℤ, (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter φ k x) ∂tripleVolume) =
            ∫ z, (p z:ℂ)*fourier k z ∂AddCircle.haarAddCircle) ∧
          (∀ j u a, ‖retainedAmplitude ψ χ m H A n j (u,a)‖ =
            ‖retainedAmplitude ψ χ m H A n j (u,0)‖) := by
  dsimp only
  let ψ := neutralCircleCutoff c
  let W := fun s a => stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s
  let pold := foldCircleDensity (fun s => ∫ a, W s a ∂AddCircle.haarAddCircle)
  let pcut := foldCircleDensity (fun s => ∫ a, stationaryWeight (Icc (l-R) (u+R))
    (fun x => (m:ℝ)*V x) (fun x => (ψ a:ℂ)*A₀ a x) s ∂AddCircle.haarAddCircle)
  let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
    (fun p : ℝ × ℝ => A₀ (p.2:UnitAddCircle) p.1) c.ψ
  have hψc := continuous_neutralCircleCutoff c
  have hψs : tsupport c.ψ ⊆ Ioc (0:ℝ) (0+1) ∩ Ioo δ (1-δ) := by
    intro x hx
    have hh := c.ψ_support hx
    exact ⟨⟨by linarith [hh.1],by linarith [hh.2]⟩,hh⟩
  have heψ : ∀ x ∈ Ioc (0:ℝ) (0+1), c.ψ x = ψ (x:UnitAddCircle) := by
    intro x hx
    exact (lawPsi_eq c hδ ⟨hx.1.le,by simpa using hx.2⟩).symm
  have hψsupport : ∀ x ∈ Ioc (0:ℝ) 1, ψ (x:UnitAddCircle) ≠ 0 → x ∈ Ioo δ (1-δ) := by
    intro x hx hn
    rw [← heψ x (by simpa using hx)] at hn
    exact (hψs (subset_tsupport c.ψ hn)).2
  have hcut : (∫ z, |pcut z-pold z| ∂AddCircle.haarAddCircle) ≤ B*(4*δ) := by
    have hs₁ : ∀ a, support (A₀ a) ⊆ Ioc o (o+1) := by
      intro a x hx
      have hh := hsupp a hx
      exact ⟨lt_of_le_of_lt hlo hh.1,hh.2.trans huo⟩
    have hs₂ : ∀ a, support (A₀ a) ⊆ Ioo (l-R) (u+R) := by
      intro a x hx
      have hh := hsupp a hx
      exact ⟨by linarith [hh.1],by linarith [hh.2]⟩
    have hb := oldStationaryMarginal_cutoff_l1 hAcont hAc hA hs₁ hs₂ hv hV
      (fun x _ => hVe x) isOpen_Ioo Ioo_subset_Icc_self
      (scaled_speed_good_branch hm hR hV hdV).1 (scaled_speed_good_branch hm hR hV hdV).2
      hψc (neutralCircleCutoff_bounds c hδ) hB hAb
    exact hb.trans (mul_le_mul_of_nonneg_left (neutralCircleCutoff_error c hδ hδ') hB)
  have hmarg : (fun s => ∫ a, F (a,s)) = fun s => ∫ a,
      stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
        (fun x => (ψ a:ℂ)*A₀ a x) s ∂AddCircle.haarAddCircle := by
    funext s
    exact stationaryCutoffLift_marginal heψ
      (fun x hx => (hψs (subset_tsupport c.ψ hx)).1) _ _ s
  obtain ⟨C,hC,hsp⟩ := exact_neutral_circle_spectral_estimate hm hH hA hA₀ hAc hAd hAr
    hsupp hlo huo hlu hR hPr hV hPV hdV h0 hHc hAcont hΔt isOpen_Ioo
    c.ψ_smooth c.ψ_compact hψs heψ hψc hχc hcχ hzχ
    (neutralCircleCutoff_bounds c hδ) hχ hχW (Q := 1) (by decide) 0
  refine ⟨C,hC,?_⟩
  intro L hL β
  have hJs := neutralJitterReal_smooth c L β
  have hJc := continuous_neutralJitter c L β
  have heJ : ∀ a ∈ Ioo δ (1-δ), neutralJitterReal c L β a = L*a+β :=
    fun a ha => neutralJitterReal_affine c hδ L β ⟨ha.1.le,ha.2.le⟩
  have hJinj : InjOn (neutralJitterReal c L β) (Ioo δ (1-δ)) := by
    intro a ha b hb hab
    rw [heJ a ha,heJ b hb] at hab
    nlinarith
  have hJd : ∀ a ∈ Ioo δ (1-δ), deriv (neutralJitterReal c L β) a ≠ 0 := by
    intro a ha
    rw [neutralJitterReal_deriv c hδ L β ha]
    exact hL.ne'
  obtain ⟨S,hSN,hST,ht⟩ := hsp L hL β (neutralJitterReal c L β) (neutralJitter c L β)
    heJ hJs hJc.measurable (fun x _ => neutralJitter_coe c L β x)
  simp only [Nat.cast_one,mul_one,zero_add,inv_one,one_mul] at hSN hST ht
  refine ⟨S,hSN,hST,?_⟩
  intro η hη
  have hph := exact_physical_retainedPassage_tendsto hm hH hA hA₀ hAc hAd hsupp
    hlo huo hlu hR hPr hV hPV hdV hHc hAcont hΔt hχc hχ
    ψ hψc (neutralCircleCutoff_bounds c hδ) hχW S hST
  have hpi (n : ℕ) (hn : 0 < n) := exactRetainedPacketDensity_integrable (m := m) hJs isOpen_Ioo hJinj hJd
    hψc hχc hHc hAcont hn (hSN n hn)
  have hpcuti : Integrable pcut AddCircle.haarAddCircle := by
    have hreg := exact_cutoff_weight_regular hm hR hV hdV hAr
      (fun a => (hsupp a).trans Ioc_subset_Icc_self) c.ψ_smooth c.ψ_compact h0
    have hi := compact_slice_integral_regular
      ((hreg.1.comp (contDiff_snd.prodMk contDiff_fst)).continuous)
      (hreg.2.1.comp_homeomorph (Homeomorph.prodComm ℝ ℝ))
    dsimp only [pcut]
    rw [← hmarg]
    exact integrable_foldCircleDensity hi.1.measurable hi.2
  have hpoldi : Integrable pold AddCircle.haarAddCircle := by
    have hs₁ : ∀ a, support (A₀ a) ⊆ Ioc o (o+1) := fun a x hx =>
      ⟨lt_of_le_of_lt hlo (hsupp a hx).1,(hsupp a hx).2.trans huo⟩
    have hs₂ : ∀ a, support (A₀ a) ⊆ Ioo (l-R) (u+R) := by
      intro a x hx
      have hh := hsupp a hx
      exact ⟨by linarith [hh.1],by linarith [hh.2]⟩
    exact (oldStationaryMarginal_map hAcont hAc hA hs₁ hs₂ hv hV
      (fun x _ => hVe x) isOpen_Ioo Ioo_subset_Icc_self
      (scaled_speed_good_branch hm hR hV hdV).1 (scaled_speed_good_branch hm hR hV hdV).2).1
  have hspec := ht (η/2) (half_pos hη)
  change ∀ᶠ n : ℕ in atTop, (∫ z, |exactRetainedPacketDensity (Ioo δ (1-δ))
    (neutralJitterReal c L β) ψ χ m H A (S n) n z-foldCircleDensity (fun s => ∫ a, F (a,s)) z|
      ∂AddCircle.haarAddCircle) < C/L+η/2 at hspec
  rw [hmarg] at hspec
  have hHl : ∀ n : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (n:ℝ)*(Pr x+Δ n*x)) :=
    fun _ => contDiff_const.mul (hPr.add (contDiff_const.mul contDiff_id))
  filter_upwards [hspec,hph.eventually (eventually_lt_nhds (half_pos hη)),
    eventually_gt_atTop (0:ℕ)] with n hnsp hnph hn
  refine ⟨?_,?_,?_,?_,?_⟩
  · have hh := uncut_retainedPassage_uniform_error (m := m) hAcont hHc hχc hB hAb c hδ hδ' n (S n)
    exact hh.trans_lt (by linarith)
  · exact (integral_abs_sub_triangle (hpi n hn) hpcuti hpoldi).trans_lt (by linarith)
  · exact exactRetainedPacketDensity_smooth_lift hJs isOpen_Ioo hJinj hJd
      c.ψ_smooth c.ψ_compact (fun x hx => (heψ x hx).symm) hψs hχs hHl hH hAs hn (hSN n hn)
  · intro k
    exact retainedPassage_spectral_moment hψc hχc hHc hAcont hψsupport hJc hJs
      (fun x _ => neutralJitter_coe c L β x) isOpen_Ioo hJinj hJd hn (hSN n hn) k
  · exact fun _ _ _ => retainedAmplitude_modulus _ _ _ _ _ _ _ _ _

end ThreeTorus
end
end

end OAI
