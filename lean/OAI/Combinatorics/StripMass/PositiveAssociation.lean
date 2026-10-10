import Mathlib
import OAI.Combinatorics.StripMass.LaguerreTails

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory Filter
lemma association_sampled {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (q : SimpleFunc ℝ ℝ) {I : Set ℝ}
    (hqI : ∀ x, q x ∈ I) (h f g : (ι → ℝ) → ℝ)
    (hh : ∀ x ∈ coordinateBox ι I, 0 ≤ h x)
    (hf : ∀ x ∈ coordinateBox ι I, 0 ≤ f x)
    (hg : ∀ x ∈ coordinateBox ι I, 0 ≤ g x)
    (hfm : MonotoneOn f (coordinateBox ι I))
    (hgm : MonotoneOn g (coordinateBox ι I))
    (hhm : ∀ x ∈ coordinateBox ι I, ∀ y ∈ coordinateBox ι I,
      h x * h y ≤ h (x ⊓ y) * h (x ⊔ y)) :
    (∫ x, h (fun i => q (x i)) * f (fun i => q (x i)) ∂Measure.pi (fun _ : ι => μ)) *
      (∫ x, h (fun i => q (x i)) * g (fun i => q (x i)) ∂Measure.pi (fun _ : ι => μ)) ≤
    (∫ x, h (fun i => q (x i)) ∂Measure.pi (fun _ : ι => μ)) *
      (∫ x, h (fun i => q (x i)) * (f (fun i => q (x i)) * g (fun i => q (x i)))
        ∂Measure.pi (fun _ : ι => μ)) := by
  classical
  let A := ↥q.range
  let Q : ℝ → A := fun x => ⟨q x, q.mem_range_self x⟩
  let e : (ι → A) → (ι → ℝ) := fun x i => x i
  have hQ : Measurable Q := q.measurable.subtype_mk
  let ν : Measure A := μ.map Q
  have heI (x : ι → A) : e x ∈ coordinateBox ι I := by
    intro i
    obtain ⟨z, hz⟩ := SimpleFunc.mem_range.mp (x i).property
    change (x i).val ∈ I
    rw [← hz]
    exact hqI z
  have hint (k : (ι → ℝ) → ℝ) :
      (∫ x, k (fun i => q (x i)) ∂Measure.pi (fun _ : ι => μ)) =
        ∫ x : ι → A, k (e x) ∂Measure.pi (fun _ : ι => ν) := by
    rw [← Measure.pi_map_pi (fun _ : ι => hQ.aemeasurable)]
    symm
    apply integral_map (Measurable.of_eval (fun i => hQ.comp (measurable_pi_apply i))).aemeasurable
    exact (measurable_of_countable _).aestronglyMeasurable
  rw [hint (fun x => h x * f x), hint (fun x => h x * g x), hint h,
    hint (fun x => h x * (f x * g x))]
  apply association_finite_product (fun _ : ι => ν) (fun x => h (e x)) (fun x => f (e x))
    (fun x => g (e x)) (fun x => hh _ (heI x)) (fun x => hf _ (heI x)) (fun x => hg _ (heI x))
  · intro x y hxy
    exact hfm (heI x) (heI y) (fun i => hxy i)
  · intro x y hxy
    exact hgm (heI x) (heI y) (fun i => hxy i)
  · intro x y
    exact hhm _ (heI x) _ (heI y)

lemma measurable_sampled {ι : Type*} [Fintype ι]
    (q : SimpleFunc ℝ ℝ) (k : (ι → ℝ) → ℝ) :
    Measurable (fun x : ι → ℝ => k (fun i => q (x i))) := by
  let Q : ℝ → ↥q.range := fun x => ⟨q x, q.mem_range_self x⟩
  have hQ : Measurable Q := q.measurable.subtype_mk
  exact (measurable_of_countable (fun x : ι → ↥q.range => k (fun i => x i))).comp
    (Measurable.of_eval (fun i => hQ.comp (measurable_pi_apply i)))

 

lemma integral_tendsto_quantization {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsFiniteMeasure μ] {I : Set ℝ} (hIc : IsCompact I)
    {y₀ : ℝ} (h₀ : y₀ ∈ I) (hμI : ∀ᵐ x ∂μ, x ∈ I)
    (k : (ι → ℝ) → ℝ) (hk : ContinuousOn k (coordinateBox ι I)) :
    Tendsto (fun n => ∫ x : ι → ℝ,
      k (fun i => SimpleFunc.approxOn id measurable_id I y₀ h₀ n (x i))
        ∂Measure.pi (fun _ : ι => μ)) atTop
      (nhds (∫ x, k x ∂Measure.pi (fun _ : ι => μ))) := by
  let q : ℕ → SimpleFunc ℝ ℝ := SimpleFunc.approxOn id measurable_id I y₀ h₀
  have hqI (n : ℕ) (x : ι → ℝ) : (fun i => q n (x i)) ∈ coordinateBox ι I :=
    fun i => SimpleFunc.approxOn_mem measurable_id h₀ n (x i)
  have hB : IsCompact (coordinateBox ι I) := isCompact_pi_infinite fun _ => hIc
  obtain ⟨b, hb⟩ := hB.exists_bound_of_continuousOn hk
  have hμB : ∀ᵐ x ∂Measure.pi (fun _ : ι => μ), x ∈ coordinateBox ι I :=
    ae_all_iff.mpr (fun i => (Measure.quasiMeasurePreserving_eval (fun _ : ι => μ) i).ae hμI)
  apply tendsto_integral_of_dominated_convergence (fun _ => b)
    (fun n => (measurable_sampled (q n) k).aestronglyMeasurable) (integrable_const b)
    (fun n => Eventually.of_forall (fun x => hb _ (hqI n x)))
  filter_upwards [hμB] with x hx
  apply (hk x hx).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_pi_nhds.mpr (fun i => ?_), Eventually.of_forall (fun n => hqI n x)⟩
  exact SimpleFunc.tendsto_approxOn measurable_id h₀ (subset_closure (hx i))

 

lemma association_compact_product {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsFiniteMeasure μ] {I : Set ℝ} (hIc : IsCompact I)
    {y₀ : ℝ} (h₀ : y₀ ∈ I) (hμI : ∀ᵐ x ∂μ, x ∈ I)
    (h f g : (ι → ℝ) → ℝ)
    (hhc : ContinuousOn h (coordinateBox ι I))
    (hfc : ContinuousOn f (coordinateBox ι I))
    (hgc : ContinuousOn g (coordinateBox ι I))
    (hh : ∀ x ∈ coordinateBox ι I, 0 ≤ h x)
    (hf : ∀ x ∈ coordinateBox ι I, 0 ≤ f x)
    (hg : ∀ x ∈ coordinateBox ι I, 0 ≤ g x)
    (hfm : MonotoneOn f (coordinateBox ι I))
    (hgm : MonotoneOn g (coordinateBox ι I))
    (hhm : ∀ x ∈ coordinateBox ι I, ∀ y ∈ coordinateBox ι I,
      h x * h y ≤ h (x ⊓ y) * h (x ⊔ y)) :
    (∫ x, h x * f x ∂Measure.pi (fun _ : ι => μ)) *
      (∫ x, h x * g x ∂Measure.pi (fun _ : ι => μ)) ≤
    (∫ x, h x ∂Measure.pi (fun _ : ι => μ)) *
      (∫ x, h x * (f x * g x) ∂Measure.pi (fun _ : ι => μ)) := by
  apply le_of_tendsto_of_tendsto
    ((integral_tendsto_quantization μ hIc h₀ hμI _ (hhc.mul hfc)).mul
      (integral_tendsto_quantization μ hIc h₀ hμI _ (hhc.mul hgc)))
    ((integral_tendsto_quantization μ hIc h₀ hμI h hhc).mul
      (integral_tendsto_quantization μ hIc h₀ hμI _ (hhc.mul (hfc.mul hgc))))
  exact Eventually.of_forall (fun n => association_sampled μ
    (SimpleFunc.approxOn id measurable_id I y₀ h₀ n)
    (SimpleFunc.approxOn_mem measurable_id h₀ n) h f g hh hf hg hfm hgm hhm)

 

def orderedProductDensity (N : ℕ) (w : Fin N → ℝ → ℝ) (x : Fin N → ℝ) : ℝ :=
  (∏ i, w i (x i)) * ∏ i, ∏ j ∈ Finset.Ioi i, orderedPairKernel (x i) (x j)

lemma orderedProductDensity_nonneg {N : ℕ} {I : Set ℝ}
    (hI : I ⊆ Ioi 0) (w : Fin N → ℝ → ℝ) (hw : ∀ i x, x ∈ I → 0 ≤ w i x)
    {x : Fin N → ℝ} (hx : x ∈ coordinateBox (Fin N) I) :
    0 ≤ orderedProductDensity N w x := by
  unfold orderedProductDensity
  exact mul_nonneg (Finset.prod_nonneg (fun i _ => hw i _ (hx i)))
    (Finset.prod_nonneg (fun i _ => Finset.prod_nonneg (fun j _ =>
      orderedPairKernel_nonneg (hI (hx i)).le (hI (hx j)).le)))

lemma continuousOn_orderedProductDensity {N : ℕ} {I : Set ℝ}
    (hI : I ⊆ Ioi 0) (w : Fin N → ℝ → ℝ) (hw : ∀ i, ContinuousOn (w i) I) :
    ContinuousOn (orderedProductDensity N w) (coordinateBox (Fin N) I) := by
  unfold orderedProductDensity
  apply ContinuousOn.mul
  · apply continuousOn_finsetProd
    intro i _
    exact (hw i).comp (continuous_apply i).continuousOn (fun x hx => hx i)
  · apply continuousOn_finsetProd
    intro i _
    apply continuousOn_finsetProd
    intro j _
    unfold orderedPairKernel
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      exact ne_of_gt (add_pos (hI (hx j)) (hI (hx i)))

lemma orderedProductDensity_logSupermodular {N : ℕ} {I : Set ℝ}
    (hI : I ⊆ Ioi 0) (w : Fin N → ℝ → ℝ) (hw : ∀ i x, x ∈ I → 0 ≤ w i x)
    {x y : Fin N → ℝ} (hx : x ∈ coordinateBox (Fin N) I) (hy : y ∈ coordinateBox (Fin N) I) :
    orderedProductDensity N w x * orderedProductDensity N w y ≤
      orderedProductDensity N w (x ⊓ y) * orderedProductDensity N w (x ⊔ y) := by
  have hp :
      (∏ i, ∏ j ∈ Finset.Ioi i, orderedPairKernel (x i) (x j)) *
        (∏ i, ∏ j ∈ Finset.Ioi i, orderedPairKernel (y i) (y j)) ≤
      (∏ i, ∏ j ∈ Finset.Ioi i, orderedPairKernel ((x ⊓ y) i) ((x ⊓ y) j)) *
        (∏ i, ∏ j ∈ Finset.Ioi i, orderedPairKernel ((x ⊔ y) i) ((x ⊔ y) j)) := by
    simp only [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro i _
      exact Finset.prod_nonneg fun j _ => mul_nonneg
        (orderedPairKernel_nonneg (hI (hx i)).le (hI (hx j)).le)
        (orderedPairKernel_nonneg (hI (hy i)).le (hI (hy j)).le)
    · intro i _
      apply Finset.prod_le_prod₀
      · intro j _
        exact mul_nonneg
          (orderedPairKernel_nonneg (hI (hx i)).le (hI (hx j)).le)
          (orderedPairKernel_nonneg (hI (hy i)).le (hI (hy j)).le)
      · intro j _
        exact orderedPairKernel_logSupermodular
          (hI (hx i)) (hI (hy i)) (hI (hx j)) (hI (hy j))
  unfold orderedProductDensity
  rw [mul_mul_mul_comm, mul_mul_mul_comm (∏ i, w i ((x ⊓ y) i)),
    ← product_coordinate_modular]
  exact mul_le_mul_of_nonneg_left hp (mul_nonneg
    (Finset.prod_nonneg (fun i _ => hw i _ (hx i)))
    (Finset.prod_nonneg (fun i _ => hw i _ (hy i))))

lemma orderedProductDensity_eq {N : ℕ} (w : Fin N → ℝ → ℝ)
    {x : Fin N → ℝ} (hx : StrictMono x) :
    orderedProductDensity N w x =
      (∏ i, w i (x i)) * ∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (x i) (x j) := by
  unfold orderedProductDensity
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j hj
  exact orderedPairKernel_eq (hx (Finset.mem_Ioi.mp hj)).le

lemma orderedProductDensity_eq_zero {N : ℕ} (w : Fin N → ℝ → ℝ)
    {x : Fin N → ℝ} (hx : ¬ StrictMono x) : orderedProductDensity N w x = 0 := by
  classical
  unfold StrictMono at hx
  push Not at hx
  obtain ⟨i, j, hij, hji⟩ := hx
  have hz : (∏ i, ∏ j ∈ Finset.Ioi i, orderedPairKernel (x i) (x j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i)
      (Finset.prod_eq_zero (Finset.mem_Ioi.mpr hij) (orderedPairKernel_eq_zero hji))
  simp [orderedProductDensity, hz]

 

theorem ordered_density_association_compact {N : ℕ} {l u : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) (w : Fin N → ℝ → ℝ)
    (hwc : ∀ i, ContinuousOn (w i) (Icc l u))
    (hw : ∀ i x, x ∈ Icc l u → 0 ≤ w i x)
    (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Icc l u)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Icc l u)))
    (hf : ∀ x ∈ coordinateBox (Fin N) (Icc l u), 0 ≤ f x)
    (hg : ∀ x ∈ coordinateBox (Fin N) (Icc l u), 0 ≤ g x)
    (hfm : MonotoneOn f (coordinateBox (Fin N) (Icc l u)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Icc l u))) :
    (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x * f x) *
      (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x * g x) ≤
    (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x) *
      (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x * (f x * g x)) := by
  have hI : Icc l u ⊆ Ioi (0 : ℝ) := fun _ hx => hl.trans_le hx.1
  have hb : coordinateBox (Fin N) (Icc l u) = Set.univ.pi (fun _ : Fin N => Icc l u) := by
    ext x
    simp [coordinateBox, Pi.le_def, forall_and]
  have h := association_compact_product (volume.restrict (Icc l u)) isCompact_Icc
    (left_mem_Icc.mpr hlu) (ae_restrict_mem measurableSet_Icc) (orderedProductDensity N w) f g
    (continuousOn_orderedProductDensity hI w hwc) hfc hgc
    (fun _ hx => orderedProductDensity_nonneg hI w hw hx) hf hg hfm hgm
    (fun _ hx _ hy => orderedProductDensity_logSupermodular hI w hw hx hy)
  simpa only [hb, volume_pi, Measure.restrict_pi_pi] using h

 

lemma weighted_covariance_shift {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (h f g : α → ℝ) (hh : Integrable h μ) (hf : Integrable (fun x => h x * f x) μ)
    (hg : Integrable (fun x => h x * g x) μ)
    (hfg : Integrable (fun x => h x * (f x * g x)) μ) (b c : ℝ) :
    (∫ x, h x * (f x + b) ∂μ) * (∫ x, h x * (g x + c) ∂μ) -
        (∫ x, h x ∂μ) * (∫ x, h x * ((f x + b) * (g x + c)) ∂μ) =
      (∫ x, h x * f x ∂μ) * (∫ x, h x * g x ∂μ) -
        (∫ x, h x ∂μ) * (∫ x, h x * (f x * g x) ∂μ) := by
  have hf' : (∫ x, h x * (f x + b) ∂μ) = (∫ x, h x * f x ∂μ) + b * ∫ x, h x ∂μ := by
    simp_rw [mul_add]
    rw [integral_add hf (hh.mul_const b), integral_mul_const, mul_comm _ b]
  have hg' : (∫ x, h x * (g x + c) ∂μ) = (∫ x, h x * g x ∂μ) + c * ∫ x, h x ∂μ := by
    simp_rw [mul_add]
    rw [integral_add hg (hh.mul_const c), integral_mul_const, mul_comm _ c]
  have hfg' : (∫ x, h x * ((f x + b) * (g x + c)) ∂μ) =
      (∫ x, h x * (f x * g x) ∂μ) + c * (∫ x, h x * f x ∂μ) +
        b * (∫ x, h x * g x ∂μ) + b * c * (∫ x, h x ∂μ) := by
    simp_rw [show ∀ x, h x * ((f x + b) * (g x + c)) =
      h x * (f x * g x) + c * (h x * f x) + b * (h x * g x) + (b * c) * h x by
        intro x; ring]
    have hi₁ : Integrable (fun x => h x * (f x * g x) + c * (h x * f x)) μ :=
      hfg.add (hf.const_mul c)
    have hi₂ : Integrable (fun x => h x * (f x * g x) + c * (h x * f x) + b * (h x * g x)) μ :=
      hi₁.add (hg.const_mul b)
    rw [integral_add hi₂ (hh.const_mul (b * c)),
      integral_add hi₁ (hg.const_mul b), integral_add hfg (hf.const_mul c)]
    simp only [integral_const_mul]
  rw [hf', hg', hfg']
  ring

 

theorem ordered_density_covariance_compact {N : ℕ} {l u : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) (w : Fin N → ℝ → ℝ)
    (hwc : ∀ i, ContinuousOn (w i) (Icc l u))
    (hw : ∀ i x, x ∈ Icc l u → 0 ≤ w i x)
    (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Icc l u)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Icc l u)))
    (hfm : MonotoneOn f (coordinateBox (Fin N) (Icc l u)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Icc l u))) :
    (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x * f x) *
      (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x * g x) ≤
    (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x) *
      (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x * (f x * g x)) := by
  have hB : IsCompact (coordinateBox (Fin N) (Icc l u)) := isCompact_pi_infinite fun _ => isCompact_Icc
  obtain ⟨b, hb⟩ := hB.exists_bound_of_continuousOn hfc
  obtain ⟨c, hc⟩ := hB.exists_bound_of_continuousOn hgc
  have hh : ContinuousOn (orderedProductDensity N w) (coordinateBox (Fin N) (Icc l u)) :=
    continuousOn_orderedProductDensity (fun _ hx => hl.trans_le hx.1) w hwc
  have h := ordered_density_association_compact hl hlu w hwc hw
    (fun x => f x + b) (fun x => g x + c) (hfc.add continuousOn_const) (hgc.add continuousOn_const)
    (fun x hx => by have h := (abs_le.mp (hb x hx)).1; linarith)
    (fun x hx => by have h := (abs_le.mp (hc x hx)).1; linarith)
    (fun x hx y hy hxy => add_le_add (hfm hx hy hxy) le_rfl)
    (fun x hx y hy hxy => add_le_add (hgm hx hy hxy) le_rfl)
  have he := weighted_covariance_shift (volume.restrict (coordinateBox (Fin N) (Icc l u)))
    (orderedProductDensity N w) f g (hh.integrableOn_compact hB)
    ((hh.mul hfc).integrableOn_compact hB) ((hh.mul hgc).integrableOn_compact hB)
    ((hh.mul (hfc.mul hgc)).integrableOn_compact hB) b c
  linarith

 

theorem ordered_density_reverse_covariance_compact {N : ℕ} {l u : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) (w : Fin N → ℝ → ℝ)
    (hwc : ∀ i, ContinuousOn (w i) (Icc l u))
    (hw : ∀ i x, x ∈ Icc l u → 0 ≤ w i x)
    (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Icc l u)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Icc l u)))
    (hfm : AntitoneOn f (coordinateBox (Fin N) (Icc l u)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Icc l u))) :
    (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x * (f x * g x)) *
      (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x) ≤
    (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x * f x) *
      (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x * g x) := by
  have h := ordered_density_covariance_compact hl hlu w hwc hw (fun x => -f x) g
    hfc.neg hgc (fun x hx y hy hxy => neg_le_neg (hfm hx hy hxy)) hgm
  simp only [neg_mul, mul_neg, integral_neg, neg_le_neg_iff] at h
  nlinarith



 
def orderedChamber (N : ℕ) (I : Set ℝ) : Set (Fin N → ℝ) :=
  {x | StrictMono x ∧ ∀ i, x i ∈ I}

def rawProductDensity (N : ℕ) (w : Fin N → ℝ → ℝ) (x : Fin N → ℝ) : ℝ :=
  (∏ i, w i (x i)) * ∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (x i) (x j)

lemma isOpen_strictMono_coordinates (N : ℕ) : IsOpen {x : Fin N → ℝ | StrictMono x} := by
  have heq : {x : Fin N → ℝ | StrictMono x} =
      ⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : i < j), {x | x i < x j} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, StrictMono]
  rw [heq]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ => isOpen_lt (continuous_apply i) (continuous_apply j)

lemma coordinateBox_eq_pi {ι : Type*} (I : Set ℝ) :
    coordinateBox ι I = Set.univ.pi (fun _ : ι => I) := by
  ext x
  simp [coordinateBox]

lemma measurableSet_coordinateBox {ι : Type*} [Countable ι] {I : Set ℝ}
    (hI : MeasurableSet I) : MeasurableSet (coordinateBox ι I) := by
  have he : coordinateBox ι I = ⋂ i : ι, (fun x : ι → ℝ => x i) ⁻¹' I := by
    ext x
    simp [coordinateBox]
  rw [he]
  exact MeasurableSet.iInter fun i : ι => hI.preimage (measurable_pi_apply i)

lemma orderedProductDensity_indicator (N : ℕ) (w : Fin N → ℝ → ℝ) :
    orderedProductDensity N w = {x : Fin N → ℝ | StrictMono x}.indicator (rawProductDensity N w) := by
  classical
  funext x
  by_cases hx : StrictMono x
  · simp only [Set.indicator_of_mem (show x ∈ {x : Fin N → ℝ | StrictMono x} from hx)]
    exact orderedProductDensity_eq w hx
  · simp only [Set.indicator_of_notMem (show x ∉ {x : Fin N → ℝ | StrictMono x} from hx)]
    exact orderedProductDensity_eq_zero w hx

lemma orderedProductDensity_mul_indicator (N : ℕ) (w : Fin N → ℝ → ℝ)
    (f : (Fin N → ℝ) → ℝ) :
    (fun x => orderedProductDensity N w x * f x) =
      {x : Fin N → ℝ | StrictMono x}.indicator (fun x => rawProductDensity N w x * f x) := by
  rw [orderedProductDensity_indicator]
  funext x
  by_cases hx : StrictMono x <;> simp [hx]

lemma orderedChamber_eq_inter (N : ℕ) (I : Set ℝ) :
    orderedChamber N I = {x : Fin N → ℝ | StrictMono x} ∩ coordinateBox (Fin N) I := rfl

lemma integral_orderedProductDensity_mul {N : ℕ} (I : Set ℝ) (w : Fin N → ℝ → ℝ)
    (f : (Fin N → ℝ) → ℝ) :
    (∫ x in coordinateBox (Fin N) I, orderedProductDensity N w x * f x) =
      ∫ x in orderedChamber N I, rawProductDensity N w x * f x := by
  rw [orderedProductDensity_mul_indicator, setIntegral_indicator (isOpen_strictMono_coordinates N).measurableSet,
    orderedChamber_eq_inter, inter_comm]

lemma integrable_orderedProductDensity_mul_iff {N : ℕ} (I : Set ℝ) (w : Fin N → ℝ → ℝ)
    (f : (Fin N → ℝ) → ℝ) :
    IntegrableOn (fun x => orderedProductDensity N w x * f x) (coordinateBox (Fin N) I) ↔
      IntegrableOn (fun x => rawProductDensity N w x * f x) (orderedChamber N I) := by
  rw [orderedProductDensity_mul_indicator,
    integrableOn_indicator_iff (isOpen_strictMono_coordinates N).measurableSet]
  rfl

lemma integral_orderedProductDensity {N : ℕ} (I : Set ℝ) (w : Fin N → ℝ → ℝ) :
    (∫ x in coordinateBox (Fin N) I, orderedProductDensity N w x) =
      ∫ x in orderedChamber N I, rawProductDensity N w x := by
  simpa using integral_orderedProductDensity_mul I w (fun _ => 1)

lemma integrable_orderedProductDensity_iff {N : ℕ} (I : Set ℝ) (w : Fin N → ℝ → ℝ) :
    IntegrableOn (orderedProductDensity N w) (coordinateBox (Fin N) I) ↔
      IntegrableOn (rawProductDensity N w) (orderedChamber N I) := by
  simpa using integrable_orderedProductDensity_mul_iff I w (fun _ => 1)

lemma coordinateBox_mono {ι : Type*} {I J : Set ℝ} (hIJ : I ⊆ J) :
    coordinateBox ι I ⊆ coordinateBox ι J := fun _ hx i => hIJ (hx i)

lemma coordinateBox_iUnion_of_monotone {ι : Type*} [Fintype ι] {s : ℕ → Set ℝ}
    (hs : Monotone s) :
    (⋃ n, coordinateBox ι (s n)) = coordinateBox ι (⋃ n, s n) := by
  simp only [coordinateBox_eq_pi]
  exact Set.iUnion_pi_of_monotone (Set.toFinite Set.univ) (fun _ _ => hs)

 

end
end CriticalStrip

end OAI
