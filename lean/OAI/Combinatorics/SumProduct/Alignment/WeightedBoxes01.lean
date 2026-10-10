import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.WordPlan01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
end

section
 

noncomputable section
namespace ConstructedWordPlan.GlobalWordPlan
open AlignmentScales RationalPivotPlan
variable {n : ℕ} (D : Pivot n) {G X : Type*} [Group G] [MulAction G X]

def jump (L : Fin D.pairs → G) (q₀ : ℕ) : ℕ → Path D → Scale n → G
  | _, [], _ => 1
  | j, o::p, b => jump L q₀ (j+1) p (update b D.index (tailAt D.tail j) o.1) *
      FreeGroup.lift (letter D.index D.tail D.owner D.added L q₀ b) o.2

 

lemma exactRun_snd (L : Fin D.pairs → G) (q₀ j : ℕ) (p : Path D) (b : Scale n) (x : X) :
    (exactRun D.index D.tail D.owner D.added L q₀ j p b x).2 = jump D L q₀ j p b • x := by
  induction p generalizing j b x with
  | nil => simp [exactRun,jump]
  | cons o p ih => simp only [exactRun,jump,ih,mul_smul]

end ConstructedWordPlan.GlobalWordPlan
end
 
end

section
 

 
open scoped BigOperators ENNReal
open MvPolynomial

namespace WeightedBoxes

variable {σ : Type*}

 
def StrictDegree (w : σ → ℕ) (j : ℕ) (p : MvPolynomial σ ℝ) : Prop :=
  ∀ m, p.coeff m ≠ 0 → Finsupp.weight w m < j

 
noncomputable def coeffNorm (p : MvPolynomial σ ℝ) : ℝ :=
  ∑ m ∈ p.support, |p.coeff m|

lemma coeffNorm_nonneg (p : MvPolynomial σ ℝ) : 0 ≤ coeffNorm p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma monomial_bound (w : σ → ℕ) (m : σ →₀ ℕ) (u : σ → ℝ) (E : ℝ)
    (hu : ∀ i, |u i| ≤ E ^ w i) :
    |m.prod (fun i n => u i ^ n)| ≤ E ^ Finsupp.weight w m := by
  classical
  simp only [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  rw [Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀
  · intro i _; exact abs_nonneg _
  · intro i _
    rw [abs_pow, Nat.mul_comm, pow_mul]
    exact pow_le_pow_left₀ (abs_nonneg _) (hu i) _

lemma eval_bound (w : σ → ℕ) (p : MvPolynomial σ ℝ) (j : ℕ)
    (hp : StrictDegree w j p) (u : σ → ℝ) (E : ℝ)
    (hE : 1 ≤ E) (hu : ∀ i, |u i| ≤ E ^ w i) :
    |eval u p| ≤ coeffNorm p * E ^ (j - 1) := by
  classical
  rw [eval_eq]
  change |∑ m ∈ p.support, p.coeff m * m.prod (fun i n => u i ^ n)| ≤ _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  dsimp [coeffNorm]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro m hm
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (monomial_bound w m u E hu).trans
  exact pow_le_pow_right₀ hE (Nat.le_sub_one_of_lt (hp m (mem_support_iff.mp hm)))

 
theorem uniform_displacement_bound [Fintype σ] (w : σ → ℕ)
    (p : σ → MvPolynomial σ ℝ) (hp : ∀ i, StrictDegree w (w i) (p i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : ℝ), 1 ≤ E → ∀ u : σ → ℝ,
      (∀ i, |u i| ≤ E ^ w i) → ∀ i, |eval u (p i)| ≤ C * E ^ (w i - 1) := by
  refine ⟨∑ i, coeffNorm (p i), Finset.sum_nonneg (fun _ _ => coeffNorm_nonneg _), ?_⟩
  intro E hE u hu i
  apply (eval_bound w (p i) (w i) (hp i) u E hE hu).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) _)
  exact Finset.single_le_sum (fun j _ => coeffNorm_nonneg (p j)) (Finset.mem_univ i)

open MeasureTheory MeasureTheory.Measure

 
def LowerDependency (w : σ → ℕ) (d : (σ → ℝ) → σ → ℝ) : Prop :=
  ∀ i u v, (∀ j, w j < w i → u j = v j) → d u i = d v i

 

theorem measurePreserving_triangular [Fintype σ] (w : σ → ℕ)
    (d : (σ → ℝ) → σ → ℝ) (hd : Measurable d) (hdep : LowerDependency w d)
    (s : ℕ) (hw : ∀ i, w i ≤ s) :
    MeasurePreserving (fun u => u + d u) volume volume := by
  induction s generalizing σ with
  | zero =>
    have he : d = fun _ => d 0 := by
      funext u i
      apply hdep i u 0
      intro j hj
      have := hw i
      omega
    rw [he]
    exact measurePreserving_add_right volume (d 0)
  | succ s ih =>
    classical
    let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : σ => ℝ) (fun i => w i ≤ s)
    let low := {i : σ // w i ≤ s}
    let high := {i : σ // ¬w i ≤ s}
    let ext (u : low → ℝ) : σ → ℝ := e.symm (u, 0)
    let dl (u : low → ℝ) (i : low) : ℝ := d (ext u) i
    let dh (u : low → ℝ) (i : high) : ℝ := d (ext u) i
    have hmext : Measurable ext := e.symm.measurable.comp (measurable_id.prodMk measurable_const)
    have hmdl : Measurable dl := Measurable.of_eval (fun i =>
      (measurable_pi_apply i.val).comp (hd.comp hmext))
    have hmdh : Measurable dh := Measurable.of_eval (fun i =>
      (measurable_pi_apply i.val).comp (hd.comp hmext))
    have hdlext (u : σ → ℝ) : d (ext (e u).1) = d u := by
      funext i
      apply hdep i
      intro j hj
      have hjl : w j ≤ s := by have := hw i; omega
      simp [ext, e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hjl]
    have hdepl : LowerDependency (fun i : low => w i) dl := by
      intro i u v huv
      apply hdep i
      intro j hj
      have hjl : w j ≤ s := by have := i.property; omega
      simpa [ext, e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hjl]
        using huv ⟨j, hjl⟩ hj
    have hl := ih (fun i : low => w i) dl hmdl hdepl (fun i => i.property)
    have hp : MeasurePreserving
        (fun p : (low → ℝ) × (high → ℝ) => (p.1 + dl p.1, p.2 + dh p.1))
        (volume.prod volume) (volume.prod volume) := by
      apply hl.skew_product (g := fun x y => y + dh x)
        (measurable_snd.add (hmdh.comp measurable_fst))
      exact Filter.Eventually.of_forall fun u => map_add_right_eq_self volume (dh u)
    have he := volume_preserving_piEquivPiSubtypeProd (fun _ : σ => ℝ) (fun i => w i ≤ s)
    have ht := he.symm.comp (hp.comp he)
    convert! ht using 1
    funext u
    apply e.injective
    simp only [Function.comp_apply]
    change e (u + d u) = e (e.symm ((e u).1 + dl (e u).1, (e u).2 + dh (e u).1))
    rw [MeasurableEquiv.apply_symm_apply]
    apply Prod.ext
    · funext i
      change u i + d u i = u i + d (ext (e u).1) i
      rw [hdlext]
    · funext i
      change u i + d u i = u i + d (ext (e u).1) i
      rw [hdlext]

lemma polynomial_lowerDependency (w : σ → ℕ) (p : σ → MvPolynomial σ ℝ)
    (hp : ∀ i, StrictDegree w (w i) (p i)) :
    LowerDependency w (fun u i => eval u (p i)) := by
  intro i u v huv
  apply eval₂_congr
  intro j m hj hm
  apply huv j
  have hh := Finsupp.weight_sub_single_add (w := w) (Finsupp.mem_support_iff.mp hj)
  have hd := hp i m hm
  omega

 

theorem measurePreserving_polynomialShear [Fintype σ] (w : σ → ℕ)
    (p : σ → MvPolynomial σ ℝ) (hp : ∀ i, StrictDegree w (w i) (p i)) :
    MeasurePreserving (fun u i => u i + eval u (p i)) volume volume := by
  classical
  apply measurePreserving_triangular w (fun u i => eval u (p i))
    (Measurable.of_eval (fun i => (p i).continuous_eval.measurable))
    (polynomial_lowerDependency w p hp) (Finset.univ.sup w)
  exact fun i => Finset.le_sup (f := w) (Finset.mem_univ i)

section Boxes
open Set
open scoped symmDiff

variable [Fintype σ]

 
def rect (r : σ → ℝ) : Set (σ → ℝ) := Set.Icc (-r) r

omit [Fintype σ] in
lemma mem_rect_iff {r u : σ → ℝ} : u ∈ rect r ↔ ∀ i, |u i| ≤ r i := by
  simp only [rect, Set.mem_Icc, Pi.le_def, Pi.neg_apply, abs_le]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

lemma measurableSet_rect (r : σ → ℝ) : MeasurableSet (rect r) := measurableSet_Icc

lemma rect_volume (r : σ → ℝ) (hr : ∀ i, 0 ≤ r i) :
    volume.real (rect r) = ∏ i, (2 * r i) := by
  rw [Measure.real, rect, Real.volume_Icc_pi_toReal (fun i => by have := hr i; simpa using this)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Pi.neg_apply]
  ring

lemma rect_finite (r : σ → ℝ) : volume (rect r) ≠ ∞ :=
  isCompact_Icc.measure_ne_top

lemma rect_volume_pos (r : σ → ℝ) (hr : ∀ i, 0 < r i) :
    0 < volume.real (rect r) := by
  rw [rect_volume r (fun i => (hr i).le)]
  exact Finset.prod_pos fun i _ => mul_pos (by norm_num) (hr i)

lemma rect_smul_volume (r : σ → ℝ) (hr : ∀ i, 0 ≤ r i) (a : ℝ) (ha : 0 ≤ a) :
    volume.real (rect (fun i => a * r i)) = a ^ Fintype.card σ * volume.real (rect r) := by
  rw [rect_volume _ (fun i => mul_nonneg ha (hr i)), rect_volume r hr]
  simp_rw [mul_left_comm 2 a]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

 

lemma symmDiff_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A B C : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAC : A ⊆ C) (hBC : B ⊆ C) (hC : μ C ≠ ∞) (heq : μ.real A = μ.real B) :
    μ.real (A ∆ B) ≤ 2 * (μ.real C - μ.real A) := by
  have hAf := measure_ne_top_of_subset hAC hC
  have hBf := measure_ne_top_of_subset hBC hC
  rw [measureReal_symmDiff_eq hA hB hAf hBf]
  have h₁ := measureReal_sdiff_add_inter (μ := μ) (s := A) hB hAf
  have h₂ := measureReal_sdiff_add_inter (μ := μ) (s := B) hA hBf
  have h₃ := measureReal_union_add_inter (μ := μ) (s := A) hB hAf hBf
  have h₄ := measureReal_mono (μ := μ) (Set.union_subset hAC hBC) hC
  rw [Set.inter_comm B A] at h₂
  linarith

 

lemma preimage_symmDiff_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {T : α → α} (hT : MeasurePreserving T μ μ) {A C : Set α}
    (hA : MeasurableSet A) (hC : MeasurableSet C) (hAC : A ⊆ C)
    (hTC : MapsTo T A C) (hCf : μ C ≠ ∞) :
    μ.real (A ∆ (T ⁻¹' A)) ≤ 2 * (μ.real C - μ.real A) := by
  have hpmA := hT.measure_preimage hA.nullMeasurableSet
  have hpmC := hT.measure_preimage hC.nullMeasurableSet
  have hpC : μ (T ⁻¹' C) ≠ ∞ := by rwa [hpmC]
  have heq : μ.real A = μ.real (T ⁻¹' A) := by simp only [Measure.real, hpmA]
  have h := symmDiff_bound μ hA (hA.preimage hT.measurable) hTC
    (Set.preimage_mono hAC) hpC heq
  change (μ (A ∆ (T ⁻¹' A))).toReal ≤
    2 * ((μ (T ⁻¹' C)).toReal - (μ A).toReal) at h
  rw [hpmC] at h
  exact h

 
def weightedBox (w : σ → ℕ) (E : ℝ) : Set (σ → ℝ) := rect (fun i => E ^ w i)

 
noncomputable def boundaryError (w : σ → ℕ) (T : (σ → ℝ) → σ → ℝ) (E : ℝ) : ℝ :=
  volume.real (weightedBox w E ∆ (T ⁻¹' weightedBox w E)) /
    volume.real (weightedBox w E)

lemma boundaryError_nonneg (w : σ → ℕ) (T : (σ → ℝ) → σ → ℝ) (E : ℝ) :
    0 ≤ boundaryError w T E := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

 
theorem boundaryError_bound (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : σ → MvPolynomial σ ℝ) (hp : ∀ i, StrictDegree w (w i) (p i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, 1 ≤ E →
      boundaryError w (fun u i => u i + eval u (p i)) E ≤
        2 * ((1 + C / E) ^ Fintype.card σ - 1) := by
  obtain ⟨C, hC, hCb⟩ := uniform_displacement_bound w p hp
  refine ⟨C, hC, ?_⟩
  intro E hE
  have hEpos : 0 < E := by linarith
  have hf : 1 ≤ 1 + C / E := le_add_of_nonneg_right (div_nonneg hC hEpos.le)
  let r : σ → ℝ := fun i => E ^ w i
  have hr : ∀ i, 0 < r i := fun i => pow_pos hEpos _
  have hBC : rect r ⊆ rect (fun i => (1 + C / E) * r i) := by
    intro u hu
    rw [mem_rect_iff] at hu ⊢
    intro i
    exact (hu i).trans (le_mul_of_one_le_left (hr i).le hf)
  have hTC : MapsTo (fun u i => u i + eval u (p i)) (rect r)
      (rect (fun i => (1 + C / E) * r i)) := by
    intro u hu
    rw [mem_rect_iff] at hu ⊢
    intro i
    have hepow : E ^ (w i - 1) = E ^ w i / E := by
      apply (eq_div_iff (ne_of_gt hEpos)).2
      rw [← pow_succ, Nat.sub_add_cancel (hw i)]
    calc
      |u i + eval u (p i)| ≤ |u i| + |eval u (p i)| := abs_add_le _ _
      _ ≤ r i + C * E ^ (w i - 1) := add_le_add (hu i) (hCb E hE u hu i)
      _ = (1 + C / E) * r i := by dsimp [r]; rw [hepow]; ring
  have hb := preimage_symmDiff_bound volume (measurePreserving_polynomialShear w p hp)
    (measurableSet_rect r) (measurableSet_rect _) hBC hTC (rect_finite _)
  rw [rect_smul_volume r (fun i => (hr i).le) _ (by positivity)] at hb
  unfold boundaryError weightedBox
  change volume.real (rect r ∆ ((fun u i => u i + eval u (p i)) ⁻¹' rect r)) /
    volume.real (rect r) ≤ _
  rw [div_le_iff₀ (rect_volume_pos r hr)]
  nlinarith [hb]

 

theorem boundaryError_tendsto (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : σ → MvPolynomial σ ℝ) (hp : ∀ i, StrictDegree w (w i) (p i)) :
    Filter.Tendsto (boundaryError w (fun u i => u i + eval u (p i)))
      Filter.atTop (nhds 0) := by
  obtain ⟨C, _, hC⟩ := boundaryError_bound w hw p hp
  have ht : Filter.Tendsto (fun E : ℝ => 2 * ((1 + C / E) ^ Fintype.card σ - 1))
      Filter.atTop (nhds 0) := by
    have hdiv : Filter.Tendsto (fun E : ℝ => C / E) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop Filter.tendsto_id
    convert (tendsto_const_nhds.mul (((tendsto_const_nhds.add hdiv).pow
      (Fintype.card σ)).sub tendsto_const_nhds)) using 1
    simp
  apply squeeze_zero' (Filter.Eventually.of_forall (boundaryError_nonneg w _)) _ ht
  exact (Filter.eventually_ge_atTop (1 : ℝ)).mono hC

 
noncomputable def normalizedRestriction {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (B : Set α) : Measure α := (μ B)⁻¹ • μ.restrict B

lemma normalizedRestriction_real {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (B : Set α) {A : Set α} (hA : MeasurableSet A) :
    (normalizedRestriction μ B).real A = μ.real (A ∩ B) / μ.real B := by
  rw [normalizedRestriction, measureReal_ennreal_smul_apply,
    measureReal_restrict_apply hA, ENNReal.toReal_inv]
  simp only [Measure.real]
  ring

 
theorem normalizedRestriction_variation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {T : α → α} (hT : MeasurePreserving T μ μ)
    {B : Set α} (hB : MeasurableSet B) (hBf : μ B ≠ ∞)
    {A : Set α} (hA : MeasurableSet A) :
    |((normalizedRestriction μ B).map T).real A - (normalizedRestriction μ B).real A| ≤
      μ.real (B ∆ (T ⁻¹' B)) / μ.real B := by
  rw [map_measureReal_apply hT.measurable hA,
    normalizedRestriction_real μ B (hA.preimage hT.measurable),
    normalizedRestriction_real μ B hA, ← sub_div, abs_div,
    abs_of_nonneg (measureReal_nonneg (μ := μ) (s := B))]
  apply div_le_div_of_nonneg_right _ (measureReal_nonneg (μ := μ) (s := B))
  have hpB : μ (T ⁻¹' B) ≠ ∞ := by
    rw [hT.measure_preimage hB.nullMeasurableSet]; exact hBf
  have hpAB := hT.measure_preimage (hA.inter hB).nullMeasurableSet
  have hb : μ.real (A ∩ B) = μ.real ((T ⁻¹' A) ∩ (T ⁻¹' B)) := by
    change (μ (A ∩ B)).toReal = (μ (T ⁻¹' (A ∩ B))).toReal
    rw [hpAB]
  rw [hb]
  apply (abs_measureReal_sub_le_measureReal_symmDiff'
    ((hA.preimage hT.measurable).inter hB).nullMeasurableSet
    ((hA.preimage hT.measurable).inter (hB.preimage hT.measurable)).nullMeasurableSet
    (measure_ne_top_of_subset Set.inter_subset_right hBf)
    (measure_ne_top_of_subset Set.inter_subset_right hpB)).trans
  apply measureReal_mono
  · rw [← Set.inter_symmDiff_distrib_left]
    exact Set.inter_subset_right
  · exact measure_ne_top_of_subset Set.symmDiff_subset_union (measure_union_lt_top hBf.lt_top hpB.lt_top).ne

 

theorem weightedBoxLaw_invariance (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : σ → MvPolynomial σ ℝ) (hp : ∀ i, StrictDegree w (w i) (p i)) :
    ∃ ε : ℝ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∀ E : ℝ, ∀ A : Set (σ → ℝ), MeasurableSet A →
        |((normalizedRestriction volume (weightedBox w E)).map
          (fun u i => u i + eval u (p i))).real A -
          (normalizedRestriction volume (weightedBox w E)).real A| ≤ ε E := by
  refine ⟨boundaryError w (fun u i => u i + eval u (p i)),
    boundaryError_tendsto w hw p hp, ?_⟩
  intro E A hA
  exact normalizedRestriction_variation volume (measurePreserving_polynomialShear w p hp)
    (measurableSet_rect _) (rect_finite _) hA

end Boxes

end WeightedBoxes

end
end

end OAI
