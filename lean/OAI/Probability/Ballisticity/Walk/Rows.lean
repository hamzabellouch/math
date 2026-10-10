import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace TailDecorrelation

variable {I A D : Type*} [MeasurableSpace A] [MeasurableSpace D]

@[instance_reducible] def rows (S : Set I) : MeasurableSpace (I → A) :=
  ⨆ i : S, (inferInstance : MeasurableSpace A).comap (fun ω => ω i.1)

lemma rows_mono {S T : Set I} (h : S ⊆ T) :
    rows (A := A) S ≤ rows T := by
  apply iSup_le
  intro i
  exact le_iSup_of_le ⟨i.1, h i.2⟩ le_rfl

lemma rows_le (S : Set I) : rows (A := A) S ≤ (inferInstance : MeasurableSpace (I → A)) := by
  apply iSup_le
  intro i
  exact (show Measurable (fun ω : I → A => ω i.1) from
    measurable_pi_apply i.1).comap_le

lemma rows_univ : rows (A := A) (Set.univ : Set I) = (inferInstance : MeasurableSpace (I → A)) := by
  apply le_antisymm (rows_le Set.univ)
  change (⨆ i : I, _) ≤ _
  exact iSup_le fun i => le_iSup_of_le ⟨i, Set.mem_univ i⟩ le_rfl

@[instance_reducible] def dataRows (S : Set I) : MeasurableSpace (D × (I → A)) :=
  (inferInstance : MeasurableSpace D).comap Prod.fst ⊔
    (rows S).comap Prod.snd

lemma dataRows_mono {S T : Set I} (h : S ⊆ T) :
    dataRows (D := D) (A := A) S ≤ dataRows T := by
  exact sup_le_sup le_rfl (MeasurableSpace.comap_mono (rows_mono h))

lemma dataRows_le (S : Set I) : dataRows (D := D) (A := A) S ≤ (inferInstance : MeasurableSpace (D × (I → A))) := by
  exact sup_le_sup le_rfl (MeasurableSpace.comap_mono (rows_le S))

lemma dataRows_univ :
    dataRows (D := D) (A := A) (Set.univ : Set I) = (inferInstance : MeasurableSpace (D × (I → A))) := by
  simp only [dataRows, rows_univ]
  rfl

lemma rows_eq_iSup_two (S : Set I) :
    rows (A := A) S =
      ⨆ i ∈ S, (inferInstance : MeasurableSpace A).comap (fun ω : I → A => ω i) := by
  simp only [rows, iSup_subtype]

lemma independent_rows (ν : Measure A) [IsProbabilityMeasure ν]
    {S T : Set I} (hST : Disjoint S T) :
    Indep (rows S) (rows T) (Measure.infinitePi (fun _ : I => ν)) := by
  rw [rows_eq_iSup_two, rows_eq_iSup_two]
  exact indep_iSup_of_disjoint (fun i =>
    (show Measurable (fun ω : I → A => ω i) from measurable_pi_apply i).comap_le)
    (iIndepFun_infinitePi (P := fun _ : I => ν)
      (X := fun _ a => a) (fun _ => measurable_id)).iIndep hST

lemma independent_row_functions (ν : Measure A) [IsProbabilityMeasure ν]
    {S T : Set I} (hST : Disjoint S T)
    {f g : (I → A) → ℝ}
    (hf : @Measurable _ _ (rows S) _ f)
    (hg : @Measurable _ _ (rows T) _ g) :
    IndepFun f g (Measure.infinitePi (fun _ : I => ν)) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  exact (Indep_iff _ _ _).mp (independent_rows ν hST) _ _ (hf hs) (hg ht)

lemma row_function_integral_mul (ν : Measure A) [IsProbabilityMeasure ν]
    {S T : Set I} (hST : Disjoint S T)
    {f g : (I → A) → ℝ}
    (hf : @Measurable _ _ (rows S) _ f)
    (hg : @Measurable _ _ (rows T) _ g) :
    (∫ ω, f ω * g ω ∂Measure.infinitePi (fun _ : I => ν)) =
      (∫ ω, f ω ∂Measure.infinitePi (fun _ : I => ν)) *
        ∫ ω, g ω ∂Measure.infinitePi (fun _ : I => ν) := by
  exact (independent_row_functions ν hST hf hg).integral_mul_eq_mul_integral
    ((hf.mono (rows_le S) le_rfl).aestronglyMeasurable)
    ((hg.mono (rows_le T) le_rfl).aestronglyMeasurable)

lemma dataRows_section {S : Set I} {f : D × (I → A) → ℝ}
    (hf : @Measurable _ _ (dataRows S) _ f) (d : D) :
    @Measurable _ _ (rows S) _ (fun ω => f (d, ω)) := by
  apply hf.comp
  let : MeasurableSpace (I → A) := rows S
  exact measurable_const.prodMk measurable_id

variable [Encodable I]

def prefixRows (n : ℕ) : Set I := {i | Encodable.encode i < n}

lemma prefixRows_finite (n : ℕ) : (prefixRows (I := I) n).Finite := by
  exact (Set.finite_Iio n).preimage Encodable.encode_injective.injOn

lemma prefixRows_mono : Monotone (prefixRows (I := I)) := by
  intro n m h i hi
  exact lt_of_lt_of_le hi h

lemma iUnion_prefixRows : (⋃ n, prefixRows (I := I) n) = Set.univ := by
  ext i
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨Encodable.encode i + 1, Nat.lt_succ_self _⟩

noncomputable def dataFiltration : Filtration ℕ (inferInstance : MeasurableSpace (D × (I → A))) where
  seq n := dataRows (prefixRows n)
  mono' := fun _ _ h => dataRows_mono (prefixRows_mono h)
  le' n := dataRows_le (prefixRows n)

lemma iSup_dataFiltration :
    (⨆ n, dataFiltration (D := D) (A := A) (I := I) n) = (inferInstance : MeasurableSpace (D × (I → A))) := by
  apply le_antisymm (iSup_le fun n => (dataFiltration (D := D) (A := A) (I := I)).le n)
  change (inferInstance : MeasurableSpace D).comap Prod.fst ⊔
    (inferInstance : MeasurableSpace (I → A)).comap Prod.snd ≤ _
  apply sup_le
  · exact le_iSup_of_le 0 le_sup_left
  · change (⨆ i : I, (inferInstance : MeasurableSpace A).comap (fun ω => ω i)).comap
      (Prod.snd : D × (I → A) → I → A) ≤ _
    rw [MeasurableSpace.comap_iSup]
    apply iSup_le
    intro i
    apply le_iSup_of_le (Encodable.encode i + 1)
    apply le_trans _ le_sup_right
    exact MeasurableSpace.comap_mono (le_iSup_of_le
      (⟨i, Nat.lt_succ_self _⟩ : prefixRows (Encodable.encode i + 1)) le_rfl)

section LikelihoodApproximation

variable {μ : Measure (D × (I → A))} [IsFiniteMeasure μ]

lemma likelihood_approximation {f : D × (I → A) → ℝ}
    (hf : Integrable f μ) (hm : StronglyMeasurable f) :
    Tendsto (fun n => eLpNorm
      (μ[f | dataFiltration (D := D) (A := A) (I := I) n] - f) 1 μ)
      atTop (𝓝 0) := by
  apply hf.tendsto_eLpNorm_condExp (ℱ := dataFiltration (D := D) (A := A) (I := I))
  rw [iSup_dataFiltration]
  exact hm

lemma bounded_likelihood_approximation {f : D × (I → A) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hf : StronglyMeasurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) :
    ∃ g : ℕ → D × (I → A) → ℝ,
      (∀ n, @Measurable _ _ (dataRows (prefixRows n)) _ (g n)) ∧
      (∀ n x, 0 ≤ g n x ∧ g n x ≤ B) ∧
      (∀ n, (∫ x, g n x ∂μ) = ∫ x, f x ∂μ) ∧
      Tendsto (fun n => ∫ x, |g n x - f x| ∂μ) atTop (𝓝 0) := by
  let F := dataFiltration (D := D) (A := A) (I := I)
  let u : ℕ → D × (I → A) → ℝ := fun n => μ[f | F n]
  let g : ℕ → D × (I → A) → ℝ := fun n x => max 0 (min B (u n x))
  have hu (n : ℕ) : @Measurable _ _ (dataRows (prefixRows n)) _ (u n) :=
    stronglyMeasurable_condExp.measurable
  have hg (n : ℕ) : @Measurable _ _ (dataRows (prefixRows n)) _ (g n) :=
    measurable_const.max (measurable_const.min (hu n))
  have hgf (n : ℕ) : g n =ᵐ[μ] u n := by
    have h0 : 0 ≤ᵐ[μ] u n := condExp_nonneg (Eventually.of_forall hf0)
    have h1 : ∀ᵐ x ∂μ, u n x ≤ B :=
      condExp_le_nonneg_const hB (Eventually.of_forall hfB)
    filter_upwards [h0, h1] with x hx0 hx1
    change 0 ≤ u n x at hx0
    simp only [g, min_eq_right hx1, max_eq_right hx0]
  have hfi : Integrable f μ := (integrable_const B).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hfB x)
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro n x
    exact ⟨le_max_left _ _, max_le hB (min_le_left _ _)⟩
  · intro n
    rw [integral_congr_ae (hgf n)]
    exact integral_condExp (F.le n)
  · have ht := ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp
      (likelihood_approximation (μ := μ) hfi hf)
    simp only [ENNReal.toReal_zero] at ht
    apply ht.congr
    intro n
    change (eLpNorm (u n - f) 1 μ).toReal = _
    rw [eLpNorm_one_eq_lintegral_enorm (integrable_condExp.sub hfi).aestronglyMeasurable,
      ← integral_norm_eq_lintegral_enorm (integrable_condExp.sub hfi).aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hgf n] with x hx
    simp only [Pi.sub_apply, Real.norm_eq_abs, hx]
    rfl

end LikelihoodApproximation

section BoundedEscape

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

lemma integrable_bounded_nonneg {f : Ω → ℝ} {B : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) :
    Integrable f μ := by
  exact (integrable_const B).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hfB x)

lemma eventually_integral_le_of_pointwise_eventually
    {F : ℕ → Ω → ℝ} {G : Ω → ℝ} {K : ℝ}
    (hF : ∀ n, Measurable (F n)) (hG : Integrable G μ)
    (hF0 : ∀ n x, 0 ≤ F n x) (hFK : ∀ n x, F n x ≤ K)
    (hG0 : ∀ x, 0 ≤ G x)
    (hevent : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, F n x ≤ G x) :
    ∀ ε > 0, ∀ᶠ n in atTop, (∫ x, F n x ∂μ) ≤ (∫ x, G x ∂μ) + ε := by
  let E : ℕ → Ω → ℝ := fun n x => max 0 (F n x - G x)
  have hEmeas (n : ℕ) : AEStronglyMeasurable (E n) μ :=
    (aemeasurable_const.max ((hF n).aemeasurable.sub hG.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hEbound (n : ℕ) (x : Ω) : ‖E n x‖ ≤ K := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact max_le (le_trans (hF0 n x) (hFK n x)) (by linarith [hFK n x, hG0 x])
  have hEi (n : ℕ) : Integrable (E n) μ :=
    (integrable_const K).mono' (hEmeas n) (Eventually.of_forall (hEbound n))
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => E n x) atTop (𝓝 0) := by
    filter_upwards [hevent] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hx] with n hn
    exact (max_eq_left (sub_nonpos.mpr hn)).symm
  have ht : Tendsto (fun n => ∫ x, E n x ∂μ) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (fun _ => K) hEmeas (integrable_const K)
      (fun n => Eventually.of_forall (hEbound n)) hlim
  intro ε hε
  filter_upwards [ht.eventually_lt_const hε] with n hn
  calc
    (∫ x, F n x ∂μ) ≤ ∫ x, G x + E n x ∂μ := by
      apply integral_mono (integrable_bounded_nonneg (hF n) (hF0 n) (hFK n)) (hG.add (hEi n))
      intro x
      have := le_max_right 0 (F n x - G x)
      dsimp [E]
      linarith
    _ = (∫ x, G x ∂μ) + ∫ x, E n x ∂μ := integral_add hG (hEi n)
    _ ≤ _ := by linarith

end BoundedEscape

section BoundedIndependence

variable (δ : Measure D) (ν : Measure A) [IsProbabilityMeasure δ] [IsProbabilityMeasure ν]

omit [Encodable I] in
lemma bounded_escape_product
    {S : Set I} {g : D × (I → A) → ℝ} {B K C : ℝ}
    (hB : 0 ≤ B) (_ : 0 ≤ K) (hC : 0 ≤ C)
    (hg : @Measurable _ _ (dataRows S) _ g)
    (hg0 : ∀ x, 0 ≤ g x) (hgB : ∀ x, g x ≤ B)
    (W : ℕ → D × (I → A) → ℝ) (T : ℕ → D → Set I)
    (hW : ∀ n, Measurable (W n))
    (hW0 : ∀ n x, 0 ≤ W n x) (hWK : ∀ n x, W n x ≤ K)
    (hWr : ∀ n d, @Measurable _ _ (rows (T n d)) _ (fun ω => W n (d, ω)))
    (hWC : ∀ n d, (∫ ω, W n (d, ω) ∂Measure.infinitePi (fun _ : I => ν)) ≤ C)
    (hescape : ∀ᵐ d ∂δ, ∀ᶠ n in atTop, Disjoint S (T n d)) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      (∫ x, g x * W n x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) ≤
        C * (∫ x, g x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) + ε := by
  let P := Measure.infinitePi (fun _ : I => ν)
  have hgm : Measurable g := hg.mono (dataRows_le S) le_rfl
  have hgi : Integrable g (δ.prod P) := integrable_bounded_nonneg hgm hg0 hgB
  have hprod0 (n : ℕ) (x : D × (I → A)) : 0 ≤ g x * W n x :=
    mul_nonneg (hg0 x) (hW0 n x)
  have hprodK (n : ℕ) (x : D × (I → A)) : g x * W n x ≤ B * K :=
    mul_le_mul (hgB x) (hWK n x) (hW0 n x) hB
  have hprod (n : ℕ) : Integrable (fun x => g x * W n x) (δ.prod P) :=
    integrable_bounded_nonneg (hgm.mul (hW n)) (hprod0 n) (hprodK n)
  let F : ℕ → D → ℝ := fun n d => ∫ ω, g (d, ω) * W n (d, ω) ∂P
  let G : D → ℝ := fun d => C * ∫ ω, g (d, ω) ∂P
  have hFm (n : ℕ) : Measurable (F n) :=
    (hgm.mul (hW n)).stronglyMeasurable.integral_prod_right.measurable
  have hGi : Integrable G δ := hgi.integral_prod_left.const_mul C
  have hG0 (d : D) : 0 ≤ G d :=
    mul_nonneg hC (integral_nonneg fun ω => hg0 (d, ω))
  have hF0 (n : ℕ) (d : D) : 0 ≤ F n d := integral_nonneg fun ω => hprod0 n (d, ω)
  have hFK (n : ℕ) (d : D) : F n d ≤ B * K := by
    calc
      F n d ≤ ∫ _ : I → A, B * K ∂P := by
        exact integral_mono
          (integrable_bounded_nonneg (μ := P)
            ((hgm.mul (hW n)).comp (measurable_const.prodMk measurable_id))
            (fun ω => hprod0 n (d, ω)) (fun ω => hprodK n (d, ω)))
          (integrable_const _) (fun ω => hprodK n (d, ω))
      _ = B * K := by simp [P]
  have hevent : ∀ᵐ d ∂δ, ∀ᶠ n in atTop, F n d ≤ G d := by
    filter_upwards [hescape] with d hd
    filter_upwards [hd] with n hn
    change (∫ ω, g (d, ω) * W n (d, ω) ∂P) ≤ _
    rw [row_function_integral_mul ν hn (dataRows_section hg d) (hWr n d)]
    change (∫ ω, g (d, ω) ∂P) * (∫ ω, W n (d, ω) ∂P) ≤
      C * (∫ ω, g (d, ω) ∂P)
    exact (mul_le_mul_of_nonneg_left (hWC n d) (integral_nonneg fun ω => hg0 (d, ω))).trans_eq
      (mul_comm _ _)
  intro ε hε
  filter_upwards [eventually_integral_le_of_pointwise_eventually hFm hGi hF0 hFK hG0 hevent ε hε] with n hn
  rw [integral_prod _ (hprod n)]
  rw [show (∫ d, G d ∂δ) = C * ∫ x, g x ∂δ.prod P by
    dsimp [G]
    rw [integral_const_mul, ← integral_prod _ hgi]] at hn
  exact hn

def EscapingLocalApproximation (Z : ℕ → D × (I → A) → ℝ) (K : ℝ) : Prop :=
  ∀ η > 0, ∃ (W : ℕ → D × (I → A) → ℝ) (T : ℕ → D → Set I),
    (∀ n, Measurable (W n)) ∧
    (∀ n x, 0 ≤ W n x ∧ W n x ≤ K) ∧
    (∀ n d, @Measurable _ _ (rows (T n d)) _ (fun ω => W n (d, ω))) ∧
    (∀ n d, (∫ ω, |Z n (d, ω) - W n (d, ω)| ∂Measure.infinitePi (fun _ : I => ν)) ≤ η) ∧
    (∀ S : Set I, S.Finite → ∀ᵐ d ∂δ, ∀ᶠ n in atTop, Disjoint S (T n d))

lemma bounded_product_approximation_pointwise {f g z w B K : ℝ}
    (hg0 : 0 ≤ g) (hgB : g ≤ B) (hz0 : 0 ≤ z) (hzK : z ≤ K) :
    f * z ≤ g * w + K * |f - g| + B * |z - w| := by
  have h1 := mul_le_mul_of_nonneg_right (le_abs_self (f - g)) hz0
  have h2 := mul_le_mul_of_nonneg_left hzK (abs_nonneg (f - g))
  have h3 := mul_le_mul_of_nonneg_left (le_abs_self (z - w)) hg0
  have h4 := mul_le_mul_of_nonneg_right hgB (abs_nonneg (z - w))
  nlinarith

lemma bounded_decorrelation
    {f : D × (I → A) → ℝ} {Z : ℕ → D × (I → A) → ℝ} {B K C : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B)
    (hZ : ∀ n, Measurable (Z n))
    (hZ0 : ∀ n x, 0 ≤ Z n x) (hZK : ∀ n x, Z n x ≤ K)
    (hZC : ∀ n d, (∫ ω, Z n (d, ω) ∂Measure.infinitePi (fun _ : I => ν)) ≤ C)
    (hloc : EscapingLocalApproximation δ ν Z K) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      (∫ x, f x * Z n x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) ≤
        C * (∫ x, f x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) + ε := by
  let P := Measure.infinitePi (fun _ : I => ν)
  let μ := δ.prod P
  have hfi : Integrable f μ := integrable_bounded_nonneg hf hf0 hfB
  have hfintB : (∫ x, f x ∂μ) ≤ B := by
    calc
      (∫ x, f x ∂μ) ≤ ∫ _ : D × (I → A), B ∂μ := integral_mono hfi (integrable_const B) hfB
      _ = B := by simp [μ, P]
  obtain ⟨g, hgr, hgb, hgint, hgconv⟩ :=
    bounded_likelihood_approximation (μ := μ) hB hf.stronglyMeasurable hf0 hfB
  intro ε hε
  let η := ε / (2 * (K + 2 * B + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨W, T, hWm, hWb, hWr, hWerr, hWesc⟩ := hloc η hη
  obtain ⟨j, hj⟩ := (hgconv.eventually_lt_const hη).exists
  let g₀ := g j
  have hg₀m : Measurable g₀ := (hgr j).mono (dataRows_le _) le_rfl
  have hg₀i : Integrable g₀ μ :=
    integrable_bounded_nonneg hg₀m (fun x => (hgb j x).1) (fun x => (hgb j x).2)
  have hW0 (n : ℕ) (x : D × (I → A)) : 0 ≤ W n x := (hWb n x).1
  have hWK (n : ℕ) (x : D × (I → A)) : W n x ≤ K := (hWb n x).2
  have hZi (n : ℕ) : Integrable (Z n) μ := integrable_bounded_nonneg (hZ n) (hZ0 n) (hZK n)
  have hWi (n : ℕ) : Integrable (W n) μ := integrable_bounded_nonneg (hWm n) (hW0 n) (hWK n)
  have hZsi (n : ℕ) (d : D) : Integrable (fun ω => Z n (d, ω)) P :=
    integrable_bounded_nonneg ((hZ n).comp (measurable_const.prodMk measurable_id))
      (fun ω => hZ0 n (d, ω)) (fun ω => hZK n (d, ω))
  have hWsi (n : ℕ) (d : D) : Integrable (fun ω => W n (d, ω)) P :=
    integrable_bounded_nonneg ((hWm n).comp (measurable_const.prodMk measurable_id))
      (fun ω => hW0 n (d, ω)) (fun ω => hWK n (d, ω))
  have hWmean (n : ℕ) (d : D) : (∫ ω, W n (d, ω) ∂P) ≤ C + η := by
    calc
      (∫ ω, W n (d, ω) ∂P) ≤ ∫ ω, Z n (d, ω) + |Z n (d, ω) - W n (d, ω)| ∂P := by
        apply integral_mono (hWsi n d) ((hZsi n d).add ((hZsi n d).sub (hWsi n d)).abs)
        intro ω
        have := neg_abs_le (Z n (d, ω) - W n (d, ω))
        change W n (d, ω) ≤ Z n (d, ω) + |Z n (d, ω) - W n (d, ω)|
        linarith
      _ = (∫ ω, Z n (d, ω) ∂P) + ∫ ω, |Z n (d, ω) - W n (d, ω)| ∂P :=
        integral_add (hZsi n d) ((hZsi n d).sub (hWsi n d)).abs
      _ ≤ C + η := add_le_add (hZC n d) (hWerr n d)
  have herri (n : ℕ) : Integrable (fun x => |Z n x - W n x|) μ :=
    ((hZi n).sub (hWi n)).abs
  have hWerrμ (n : ℕ) : (∫ x, |Z n x - W n x| ∂μ) ≤ η := by
    change (∫ x, |Z n x - W n x| ∂δ.prod P) ≤ η
    rw [integral_prod _ (herri n)]
    calc
      (∫ d, ∫ ω, |Z n (d, ω) - W n (d, ω)| ∂P ∂δ) ≤ ∫ _ : D, η ∂δ :=
        integral_mono ((hZi n).sub (hWi n)).abs.integral_prod_left (integrable_const η) (hWerr n)
      _ = η := by simp
  have hprod (n : ℕ) : Integrable (fun x => f x * Z n x) μ :=
    integrable_bounded_nonneg (hf.mul (hZ n)) (fun x => mul_nonneg (hf0 x) (hZ0 n x))
      (fun x => mul_le_mul (hfB x) (hZK n x) (hZ0 n x) hB)
  have hgprod (n : ℕ) : Integrable (fun x => g₀ x * W n x) μ :=
    integrable_bounded_nonneg (hg₀m.mul (hWm n)) (fun x => mul_nonneg (hgb j x).1 (hW0 n x))
      (fun x => mul_le_mul (hgb j x).2 (hWK n x) (hW0 n x) hB)
  have hgf : (∫ x, |f x - g₀ x| ∂μ) < η := by
    simpa only [abs_sub_comm] using hj
  have hevent := bounded_escape_product δ ν hB hK (add_nonneg hC hη.le)
    (hgr j) (fun x => (hgb j x).1) (fun x => (hgb j x).2)
    W T hWm hW0 hWK hWr hWmean (hWesc _ (prefixRows_finite j)) η hη
  filter_upwards [hevent] with n hn
  have hfgi : Integrable (fun x => |f x - g₀ x|) μ := (hfi.sub hg₀i).abs
  have hsum : Integrable (fun x => g₀ x * W n x + K * |f x - g₀ x|) μ :=
    (hgprod n).add (hfgi.const_mul K)
  have hi : (∫ x, f x * Z n x ∂μ) ≤
      (∫ x, g₀ x * W n x ∂μ) + K * (∫ x, |f x - g₀ x| ∂μ) +
        B * (∫ x, |Z n x - W n x| ∂μ) := by
    have ht := integral_mono (hprod n) (hsum.add ((herri n).const_mul B))
      (fun x => bounded_product_approximation_pointwise (hgb j x).1 (hgb j x).2 (hZ0 n x) (hZK n x))
    change (∫ x, f x * Z n x ∂μ) ≤
      ∫ x, (g₀ x * W n x + K * |f x - g₀ x|) + B * |Z n x - W n x| ∂μ at ht
    rwa [integral_add hsum ((herri n).const_mul B),
      integral_add (hgprod n) (hfgi.const_mul K),
      integral_const_mul, integral_const_mul] at ht
  have hn' : (∫ x, g₀ x * W n x ∂μ) ≤ (C + η) * (∫ x, f x ∂μ) + η := by
    change (∫ x, g j x * W n x ∂μ) ≤ (C + η) * (∫ x, g j x ∂μ) + η at hn
    rw [hgint j] at hn
    exact hn
  have heq : (K + 2 * B + 1) * η = ε / 2 := by
    dsimp [η]
    have hden : K + 2 * B + 1 ≠ 0 := by positivity
    field_simp
  have h1 := mul_le_mul_of_nonneg_left hgf.le hK
  have h2 := mul_le_mul_of_nonneg_left (hWerrμ n) hB
  have h3 := mul_le_mul_of_nonneg_left hfintB hη.le
  change (∫ x, f x * Z n x ∂μ) ≤ C * (∫ x, f x ∂μ) + ε
  nlinarith

end BoundedIndependence

end TailDecorrelation

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

end

end OAI
