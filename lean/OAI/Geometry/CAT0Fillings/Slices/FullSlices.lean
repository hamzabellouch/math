import Mathlib
import OAI.Geometry.CAT0Fillings.Slices.Limits
import OAI.Geometry.CAT0Fillings.Slices.NormalBudget

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma NormalApprox.eq_zero_of_cost_zero {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hz : h.cost = 0) : T = 0 := by
  apply h.current.eq_zero_of_mass_eq_zero
  apply le_antisymm _ (mass_nonneg _)
  simpa only [hz,Nat.cast_zero] using h.mass_le_cost

omit [Nonempty X] in
lemma superlevelSlice_zero [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    (hz : T = 0) {u : X → ℝ} (hu : Continuous u) (t : ℝ) :
    superlevelSlice hT hB u t = 0 := by
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.measurable
  have hBz : boundarySucc T = 0 := by rw [hz]; exact boundarySucc_zero k
  unfold superlevelSlice
  rw [restrictCurrent_zero_of_eq_zero hT hz hE, restrictCurrent_zero_of_eq_zero hB hBz hE]
  change (0 : Functional X k) - boundarySucc (fun _ _ => 0) = 0
  rw [boundarySucc_zero]
  ext b π
  simp

lemma normalSlice_zero {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hz : T = 0) {u : X → ℝ} (hu : Continuous u) (t : ℝ) :
    normalSlice h u t = 0 := by
  classical
  unfold normalSlice
  split_ifs
  · exact superlevelSlice_zero h.normal.1 h.normal.2 hz hu t
  · rfl

lemma normalSlice_eq_zero_outside {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) {u : X → ℝ} {R : ℝ} (hR : ∀ x, |u x| ≤ R) {t : ℝ}
    (ht : t ∉ Icc (-R) R) : normalSlice h u t = 0 := by
  classical
  unfold normalSlice
  split_ifs
  · exact superlevelSlice_eq_zero_outside h.normal.1 h.normal.2 hR ht
  · rfl

omit [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma NormalApprox.cost_congr [BorelSpace X] [CompactSpace X] [Nonempty X]
    {k : ℕ} {T U : Functional X k}
    (hT : NormalApprox k T) (hU : NormalApprox k U) (he : T = U) : hT.cost = hU.cost := by
  subst U
  rfl

lemma superlevelSlice_total_coarea_bound {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ G : ℝ → ℝ, Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∫ t, G t) ≤ (K:ℝ) * (mass T + mass (boundarySucc T)) ∧
      ∀ᵐ t : ℝ, IsIntegral k (superlevelSlice hT.1 hT.2.2.1 u t) ∧
        mass (superlevelSlice hT.1 hT.2.2.1 u t) ≤ G t ∧
        mass (boundary (superlevelSlice hT.1 hT.2.2.1 u t)) ≤ G t := by
  cases k with
  | zero =>
    obtain ⟨G,hG,hG0,hGI,hS⟩ := superlevelSlice_coarea_bound hT hX hK
    refine ⟨G,hG,hG0,hGI.trans ?_,?_⟩
    · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mass_nonneg _)) K.coe_nonneg
    · filter_upwards [hS] with t ht
      exact ⟨⟨ht.1,ht.2.1⟩,ht.2.2,by simpa only [boundary,mass_zero] using hG0 t⟩
  | succ k =>
    obtain ⟨G,H,hG,hH,hG0,hH0,hGI,hHI,hS⟩ := superlevelSlice_normal_coarea_bound hT hX hK
    refine ⟨fun t => G t + H t,hG.add hH,fun t => add_nonneg (hG0 t) (hH0 t),?_,?_⟩
    · rw [integral_add hG hH,mul_add]
      exact add_le_add hGI hHI
    · filter_upwards [hS] with t ht
      exact ⟨ht.1,ht.2.1.trans (le_add_of_nonneg_right (hH0 t)),
        ht.2.2.trans (le_add_of_nonneg_left (hG0 t))⟩

lemma normalSlice_cost_upper {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ g : ℝ → ℝ, Integrable g ∧ (∀ t, 0 ≤ g t) ∧
      (∫ t, g t) ≤ 2 * K * h.cost ∧
      ∀ᵐ t : ℝ, ((normalSlice_approx h u t).cost : ℝ) ≤ g t + 2 := by
  classical
  obtain ⟨Ts,hTs,hM,hN,hlim⟩ := h.cost_spec
  obtain ⟨ψ,hψ,μs,νs,μ,ν,hμs,hμ,hνs,hν,hμlim,hνlim⟩ :=
    exists_joint_weak_controlling_subsequence (fun j => (hTs j).1)
      (fun j => (hTs j).2.2.1) h.cost h.cost hM hN hlim (boundarySucc_weak_limit hlim)
  have hweak := ae_superlevelSlice_weak_tendsto (fun j => (hTs (ψ j)).1) h.normal.1
    (fun j => (hTs (ψ j)).2.2.1) h.normal.2 μs νs μ ν hμs hμ hνs hν hμlim hνlim
    (fun b π => (hlim b π).comp hψ.tendsto_atTop) (boundedLip_of_lipschitz hK)
  choose G hG hG0 hGI hS using fun j => superlevelSlice_total_coarea_bound (hTs (ψ j)) hX hK
  have hGI' j : (∫ t, G j t) ≤ 2 * (K:ℝ) * h.cost := by
    calc (∫ t, G j t) ≤ K * (mass (Ts (ψ j)) + mass (boundarySucc (Ts (ψ j)))) := hGI j
      _ ≤ K * ((h.cost:ℝ) + h.cost) := mul_le_mul_of_nonneg_left (add_le_add (hM (ψ j)) (hN (ψ j))) K.coe_nonneg
      _ = _ := by ring
  obtain ⟨g,hg,hg0,hgI,hfat⟩ := exists_integrable_subsequence_bound volume hG
    (fun j => Eventually.of_forall (hG0 j)) (2 * (K:ℝ) * h.cost) hGI'
  refine ⟨g,hg,hg0,?_,?_⟩
  · simpa only [max_eq_left (show 0 ≤ 2 * (K:ℝ) * h.cost by positivity)] using hgI
  · filter_upwards [hweak,ae_all_iff.mpr hS,hfat,ae_normalSlice_eq h hX hK] with t ht hs hf he
    obtain ⟨χ,hχ,hχG⟩ := hf
    have hA : NormalApproxAt k (Nat.ceil (g t + 1)) (normalSlice h u t) := by
      refine ⟨fun j => superlevelSlice (hTs (ψ (χ j))).1 (hTs (ψ (χ j))).2.2.1 u t,
        fun j => (hs (χ j)).1,?_,?_,?_⟩
      · intro j
        exact ((hs (χ j)).2.1.trans (hχG j).le).trans (Nat.le_ceil _)
      · intro j
        exact ((hs (χ j)).2.2.trans (hχG j).le).trans (Nat.le_ceil _)
      · intro b π
        rw [he]
        exact (ht b π).comp hχ.tendsto_atTop
    have hc := (normalSlice_approx h u t).cost_le hA
    calc ((normalSlice_approx h u t).cost : ℝ) ≤ Nat.ceil (g t + 1) := by exact_mod_cast hc
      _ ≤ g t + 2 := by have hh := Nat.ceil_lt_add_one (show 0 ≤ g t + 1 by linarith [hg0 t]); linarith

lemma measurable_normalSlice_cost {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) {u : X → ℝ} (hu : BoundedLip u) :
    Measurable (fun t : ℝ => (normalSlice_approx h u t).cost) := by
  apply measurable_normalApprox_cost (normalSlice h u) (normalSlice_approx h u)
  intro b π
  have hm : Measurable (fun p : ℝ × Unit => normalSlice h u p.1 b π) :=
    measurable_normalSlice_family (fun _ : Unit => T) (fun _ => h)
      (fun _ _ => measurable_const) hu b π
  change Measurable ((fun p : ℝ × Unit => normalSlice h u p.1 b π) ∘ (fun t : ℝ => (t,())))
  exact hm.comp (measurable_id.prodMk measurable_const)

theorem normalSlice_cost_integrable {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    {R : ℝ} (hR : ∀ x, |u x| ≤ R) :
    Integrable (fun t : ℝ => ((normalSlice_approx h u t).cost : ℝ)) ∧
      (∫ t : ℝ, ((normalSlice_approx h u t).cost : ℝ)) ≤
        (2 * K + 2 * volume.real (Icc (-R) R)) * h.cost := by
  classical
  let f : ℝ → ℝ := fun t => (normalSlice_approx h u t).cost
  have hfm : Measurable f := (show Measurable (fun n : ℕ => (n:ℝ)) from measurable_from_nat).comp
    (measurable_normalSlice_cost h (boundedLip_of_lipschitz hK))
  have hf0 t : 0 ≤ f t := Nat.cast_nonneg _
  by_cases hz : h.cost = 0
  · have hfz : f = 0 := by
      funext t
      have he := normalSlice_zero h (h.eq_zero_of_cost_zero hz) hK.continuous t
      have hc := (normalSlice_approx h u t).cost_congr (normalApprox_zero k) he
      rw [(normalApprox_zero k).cost_zero] at hc
      change ((normalSlice_approx h u t).cost : ℝ) = 0
      simp only [hc,Nat.cast_zero]
    change Integrable f ∧ (∫ t, f t) ≤ _
    rw [hfz,hz]
    simp
  have hC : (1:ℝ) ≤ h.cost := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
  obtain ⟨g,hg,hg0,hgI,hbound⟩ := normalSlice_cost_upper h hX hK
  let e : ℝ → ℝ := (Icc (-R) R).indicator (fun _ => 2 * (h.cost:ℝ))
  have he : Integrable e := by
    apply (integrable_indicator_iff isClosed_Icc.measurableSet).mpr
    exact integrableOn_const measure_Icc_lt_top.ne
  have hG : Integrable (g + e) := hg.add he
  have hle : ∀ᵐ t : ℝ, f t ≤ (g + e) t := by
    filter_upwards [hbound] with t ht
    by_cases htR : t ∈ Icc (-R) R
    · simp only [Pi.add_apply,e,indicator_of_mem htR]
      exact ht.trans (by linarith)
    · have hz' := normalSlice_eq_zero_outside h hR htR
      have hc := (normalSlice_approx h u t).cost_congr (normalApprox_zero k) hz'
      rw [(normalApprox_zero k).cost_zero] at hc
      simp only [f,hc,Nat.cast_zero,Pi.add_apply,e,indicator_of_notMem htR,add_zero]
      exact hg0 t
  have hf : Integrable f := hG.mono' hfm.aestronglyMeasurable (hle.mono fun t ht => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hf0 t)] using ht)
  refine ⟨hf,(integral_mono_ae hf hG hle).trans ?_⟩
  simp only [Pi.add_apply]
  rw [integral_add hg he]
  have heI : (∫ t, e t) = 2 * (h.cost:ℝ) * volume.real (Icc (-R) R) := by
    dsimp only [e]
    rw [integral_indicator isClosed_Icc.measurableSet]
    simp only [setIntegral_const,smul_eq_mul]
    ring
  rw [heI]
  nlinarith [hgI]

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

noncomputable def fullSlice : {k : ℕ} → {T : Functional X k} →
    NormalApprox k T → (Fin k → X → ℝ) → Euc k → Functional X 0
  | 0, T, _, _, _ => T
  | k+1, _, h, π, z => fullSlice (normalSlice_approx h (π 0) ((Prism.split k z).1))
      (Fin.tail π) ((Prism.split k z).2)

lemma fullSlice_approx : {k : ℕ} → {T : Functional X k} →
    (h : NormalApprox k T) → (π : Fin k → X → ℝ) → (z : Euc k) →
    NormalApprox 0 (fullSlice h π z)
  | 0, _, h, _, _ => h
  | k+1, _, h, π, z => fullSlice_approx (normalSlice_approx h (π 0) ((Prism.split k z).1))
      (Fin.tail π) ((Prism.split k z).2)

lemma fullSlice_integral {k : ℕ} {T : Functional X k} (h : NormalApprox k T)
    (π : Fin k → X → ℝ) (z : Euc k) : IsIntegral 0 (fullSlice h π z) :=
  (fullSlice_approx h π z).integral_zero

lemma measurable_fullSlice_family {k : ℕ} {A : Type*} [MeasurableSpace A]
    (T : A → Functional X k) (h : ∀ a, NormalApprox k (T a))
    (hm : ∀ b π, Measurable (fun a => T a b π))
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    (b : X → ℝ) (σ : Fin 0 → X → ℝ) :
    Measurable (fun p : A × Euc k => fullSlice (h p.1) π p.2 b σ) := by
  induction k generalizing A with
  | zero => exact (hm b σ).comp measurable_fst
  | succ k ih =>
    let S : ℝ × A → Functional X k := fun p => normalSlice (h p.2) (π 0) p.1
    have hS (p : ℝ × A) : NormalApprox k (S p) := normalSlice_approx (h p.2) (π 0) p.1
    have hSm b σ : Measurable (fun p : ℝ × A => S p b σ) :=
      measurable_normalSlice_family T h hm (hπ 0) b σ
    have hall : Measurable (fun p : (ℝ × A) × Euc k => fullSlice (hS p.1) (Fin.tail π) p.2 b σ) :=
      ih S hS hSm (Fin.tail π) (fun i => hπ i.succ)
    have hsplit : Measurable (fun p : A × Euc (k+1) => Prism.split k p.2) :=
      (Prism.split k).continuous.measurable.comp measurable_snd
    have hchange : Measurable (fun p : A × Euc (k+1) => (((Prism.split k p.2).1,p.1),(Prism.split k p.2).2)) :=
      (hsplit.fst.prodMk measurable_fst).prodMk hsplit.snd
    exact hall.comp hchange

lemma measurable_fullSlice {k : ℕ} {T : Functional X k} (h : NormalApprox k T)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    (b : X → ℝ) (σ : Fin 0 → X → ℝ) :
    Measurable (fun z => fullSlice h π z b σ) := by
  have hm : Measurable (fun p : Unit × Euc k => fullSlice h π p.2 b σ) :=
    measurable_fullSlice_family (fun _ : Unit => T) (fun _ => h) (fun _ _ => measurable_const) π hπ b σ
  change Measurable ((fun p : Unit × Euc k => fullSlice h π p.2 b σ) ∘ (fun z => ((),z)))
  exact hm.comp (measurable_const.prodMk measurable_id)

lemma measurable_fullSlice_cost {k : ℕ} {T : Functional X k} (h : NormalApprox k T)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i)) :
    Measurable (fun z => (fullSlice_approx h π z).cost) :=
  measurable_normalApprox_cost (fullSlice h π) (fullSlice_approx h π) (measurable_fullSlice h π hπ)

theorem fullSlice_cost_integrable {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hK : ∀ i, LipschitzWith K (π i))
    {R : ℝ} (hR : ∀ i x, |π i x| ≤ R) :
    Integrable (fun z : Euc k => ((fullSlice_approx h π z).cost : ℝ)) ∧
      (∫ z : Euc k, ((fullSlice_approx h π z).cost : ℝ)) ≤
        (2 * K + 2 * volume.real (Icc (-R) R))^k * h.cost := by
  induction k with
  | zero =>
    change Integrable (fun _ : Euc 0 => (h.cost:ℝ)) ∧ _
    rw [volume_euclideanSpace_eq_dirac]
    simp only [integral_dirac,pow_zero,one_mul]
    exact ⟨integrable_const _,le_rfl⟩
  | succ k ih =>
    let B : ℝ := 2 * K + 2 * volume.real (Icc (-R) R)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    let f : Euc (k+1) → ℝ := fun z => (fullSlice_approx h π z).cost
    let F : ℝ × Euc k → ℝ := fun p => (fullSlice_approx (normalSlice_approx h (π 0) p.1) (Fin.tail π) p.2).cost
    let c : ℝ → ℝ := fun t => (normalSlice_approx h (π 0) t).cost
    have he : F = f ∘ (Prism.split k).symm := by
      funext p
      rfl
    have hfm : Measurable f := measurable_from_nat.comp
      (measurable_fullSlice_cost h π (fun i => boundedLip_of_lipschitz (hK i)))
    have hFm : Measurable F := by rw [he]; exact hfm.comp (Prism.split k).symm.continuous.measurable
    have hF0 p : 0 ≤ F p := Nat.cast_nonneg _
    have ht (t : ℝ) : Integrable (fun z => F (t,z)) ∧
        (∫ z, F (t,z)) ≤ B^k * c t :=
      ih (normalSlice_approx h (π 0) t) (Fin.tail π) (fun i => hK i.succ) (fun i x => hR i.succ x)
    have hc : Integrable c ∧ (∫ t, c t) ≤ B * h.cost := normalSlice_cost_integrable h hX (hK 0) (hR 0)
    have hinnerM : AEStronglyMeasurable (fun t => ∫ z, F (t,z)) volume :=
      hFm.aestronglyMeasurable.integral_prod_right'
    have hinner0 t : 0 ≤ ∫ z, F (t,z) := integral_nonneg (fun z => hF0 (t,z))
    have hinner : Integrable (fun t => ∫ z, F (t,z)) :=
      (hc.1.const_mul (B^k)).mono' hinnerM (Eventually.of_forall fun t => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (hinner0 t)] using (ht t).2)
    have hFi : Integrable F (volume.prod volume) := by
      apply (integrable_prod_iff hFm.aestronglyMeasurable).mpr
      refine ⟨Eventually.of_forall fun t => (ht t).1,?_⟩
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hF0 _)] using hinner
    have hfi : Integrable f := by
      apply ((Prism.split_symm_measurePreserving k).integrable_comp_emb
        (Prism.split k).symm.toHomeomorph.measurableEmbedding).mp
      simpa only [←he,Measure.volume_eq_prod] using hFi
    refine ⟨hfi,?_⟩
    change (∫ z, f z) ≤ B^(k+1) * h.cost
    rw [Prism.integral_split]
    change (∫ p, (f ∘ (Prism.split k).symm) p ∂volume.prod volume) ≤ _
    rw [←he,integral_prod _ hFi]
    calc (∫ t, ∫ z, F (t,z)) ≤ ∫ t, B^k * c t :=
        integral_mono hinner (hc.1.const_mul _) (fun t => (ht t).2)
      _ = B^k * ∫ t, c t := integral_const_mul _ _
      _ ≤ B^k * (B * h.cost) := mul_le_mul_of_nonneg_left hc.2 (pow_nonneg hB _)
      _ = _ := by rw [pow_succ]; ring

lemma fullSlice_eval_integrable {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {b : X → ℝ} (hb : BoundedLip b) (σ : Fin 0 → X → ℝ) :
    Integrable (fun z : Euc k => fullSlice h π z b σ) := by
  classical
  choose K hK using fun i => (hπ i).1
  let K' : ℝ≥0 := Finset.univ.sup K
  have hK' i : LipschitzWith K' (π i) := (hK i).weaken (Finset.le_sup (Finset.mem_univ i))
  choose R hR using fun i => (hπ i).2
  let R' : ℝ := max 0 (∑ i, |R i|)
  have hR' i x : |π i x| ≤ R' := by
    apply (hR i x).trans
    exact (le_abs_self _).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (R j)) (Finset.mem_univ i)).trans (le_max_right _ _))
  have hcost := (fullSlice_cost_integrable h hX π hK' hR').1
  obtain ⟨B₀,hB₀⟩ := hb.2
  let B : ℝ≥0 := ⟨max B₀ 0,le_max_right _ _⟩
  have hB x : |b x| ≤ B := (hB₀ x).trans (le_max_left _ _)
  apply (hcost.const_mul (B:ℝ)).mono' (measurable_fullSlice h π hπ b σ).aestronglyMeasurable
  filter_upwards [] with z
  have hd := (fullSlice_integral h π z).1.mass_bound_uniform (π := σ) hb (fun _ => (1:ℝ≥0))
    (fun i => Fin.elim0 i) hB
  simp only [Fin.prod_univ_zero,one_mul] at hd
  simpa only [Real.norm_eq_abs] using hd.trans
    (mul_le_mul_of_nonneg_left (fullSlice_approx h π z).mass_le_cost B.coe_nonneg)

lemma normalSlice_integral {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    Integrable (fun t : ℝ => normalSlice h u t b π) ∧
      T b (Matrix.vecCons u π) = ∫ t : ℝ, normalSlice h u t b π := by
  have hcopy := h
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := hcopy
  have ha := superlevelSlice_integral_of_bounded_weak_limit hTs h.normal.1 h.normal.2
    (C:ℝ≥0) (C:ℝ≥0) hM hN hlim hX hK hab
  have he : (fun t : ℝ => superlevelSlice h.normal.1 h.normal.2 u t b π) =ᵐ[volume]
      (fun t => normalSlice h u t b π) := by
    filter_upwards [ae_normalSlice_eq h hX hK] with t ht
    rw [ht]
  exact ⟨ha.1.congr he,ha.2.trans (integral_congr_ae he)⟩

theorem fullSlice_action_integral {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {b : X → ℝ} (hb : BoundedLip b) :
    T b π = ∫ z : Euc k, fullSlice h π z b (fun j => Fin.elim0 j) := by
  induction k with
  | zero =>
    have hp : π = fun j => Fin.elim0 j := by funext j; exact Fin.elim0 j
    simp only [fullSlice,volume_euclideanSpace_eq_dirac,integral_dirac,hp]
  | succ k ih =>
    have he : π = Matrix.vecCons (π 0) (Fin.tail π) := by ext i x; exact Fin.cases rfl (fun _ => rfl) i
    have ht : T b π = ∫ t : ℝ, normalSlice h (π 0) t b (Fin.tail π) := by
      conv_lhs => rw [he]
      exact (normalSlice_integral h hX (hπ 0).1.choose_spec ⟨hb,fun i => (hπ i.succ).1⟩).2
    rw [ht,Prism.integral_split]
    have hFi : Integrable (fun p : ℝ × Euc k =>
        fullSlice h π ((Prism.split k).symm p) b (fun j => Fin.elim0 j)) :=
      ((Prism.split_symm_measurePreserving k).integrable_comp_emb
        (Prism.split k).symm.toHomeomorph.measurableEmbedding).mpr
          (fullSlice_eval_integrable h hX π hπ hb _)
    rw [Measure.volume_eq_prod,integral_prod _ (by simpa only [Measure.volume_eq_prod] using hFi)]
    apply integral_congr_ae
    filter_upwards [] with t
    exact ih (normalSlice_approx h (π 0) t) (Fin.tail π) (fun i => hπ i.succ)

end CAT0Fillings.Slicing
end

end OAI
