import OAI.Geometry.Immersion.ClosedSurface.MeanSupport
import OAI.Geometry.Immersion.ClosedSurface.GridCover

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set Function WeightedEstimates
attribute [local instance] Classical.propDecidable


lemma cutoff_weighted_bounds : ∃ C : ℕ → ℝ, (∀ m, 1 ≤ C m) ∧
    ∀ (h : ℝ), 0 < h → ∀ (a : Index) (m : ℕ),
      WeightedBound univ h m (C m) (cutoff h a) := by
  obtain ⟨c,hc,hbound⟩ := cutoff_derivative_bounds
  let C (m : ℕ) := 1 + ∑ j ∈ Finset.range (m+1), c j
  have hC (m : ℕ) : 1 ≤ C m := by
    have hs : 0 ≤ ∑ j ∈ Finset.range (m+1), c j := Finset.sum_nonneg (fun j _ => hc j)
    dsimp [C]; linarith
  refine ⟨C,hC,fun h hh a m j hj x _ => ?_⟩
  rw [iteratedFDerivWithin_univ]
  have hmul := mul_le_mul_of_nonneg_left (hbound h hh a j x) (pow_nonneg hh.le j)
  have hle : c j ≤ C m := by
    have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (m+1)) => hc i)
      (show j ∈ Finset.range (m+1) by simp; omega)
    dsimp [C]; linarith
  apply le_trans _ hle
  convert hmul using 1
  field_simp



lemma weighted_sum_bounded_overlap {h C : ℝ} (hh : 0 < h) (hC : 0 ≤ C)
    {m : ℕ} (s : Finset Index) (f : Index → Base → ℝ)
    (hf : ∀ a ∈ s, ContDiff ℝ ∞ (f a))
    (hsupp : ∀ a ∈ s, tsupport (f a) ⊆ tsupport (cutoff h a))
    (hb : ∀ a ∈ s, WeightedBound univ h m C (f a)) :
    WeightedBound univ h m (36*C) (fun x => ∑ a ∈ s, f a x) := by
  intro j hj x _
  rw [iteratedFDerivWithin_univ, iteratedFDeriv_sum (fun a ha =>
    (hf a ha).of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)))]
  let t := s.filter (fun a => x ∈ tsupport (cutoff h a))
  have ht : t ⊆ s := Finset.filter_subset _ _
  have hz (a : Index) (ha : a ∈ s) (hat : a ∉ t) :
      iteratedFDeriv ℝ j (f a) x = 0 := by
    apply notMem_support.mp
    intro hmem
    have hx := hsupp a ha (support_iteratedFDeriv_subset j hmem)
    exact hat (Finset.mem_filter.mpr ⟨ha,hx⟩)
  have he : (∑ a ∈ t, iteratedFDeriv ℝ j (f a) x) =
      ∑ a ∈ s, iteratedFDeriv ℝ j (f a) x :=
    Finset.sum_subset ht (fun a ha hat => hz a ha hat)
  simp only [Finset.sum_apply]
  rw [← he]
  calc
    _ ≤ h^j * ∑ a ∈ t, ‖iteratedFDeriv ℝ j (f a) x‖ := by
      gcongr; exact norm_sum_le _ _
    _ = ∑ a ∈ t, h^j * ‖iteratedFDeriv ℝ j (f a) x‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ _a ∈ t, C := Finset.sum_le_sum (fun a ha => by
      simpa only [iteratedFDerivWithin_univ] using hb a (ht ha) j hj x (mem_univ x))
    _ = (t.card : ℝ)*C := by simp
    _ ≤ 36*C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast active_cutoff_count hh s x

def squareSum (s : Finset Index) (h : ℝ) (x : Base) : ℝ :=
  ∑ a ∈ s, (cutoff h a x)^2

def normalizedCutoff (s : Finset Index) (h : ℝ) (a : Index) (x : Base) : ℝ :=
  cutoff h a x / Real.sqrt (squareSum s h x)

lemma squareSum_smooth (s : Finset Index) (h : ℝ) : ContDiff ℝ ∞ (squareSum s h) :=
  ContDiff.sum (fun a _ => (cutoff_smooth h a).pow 2)

lemma squareSum_nonneg (s : Finset Index) (h : ℝ) (x : Base) : 0 ≤ squareSum s h x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma squareSum_ge_one {s : Finset Index} {h : ℝ} (hh : 0 < h) {x : Base}
    (hcover : ∃ a ∈ s, x ∈ cell h 1 a) : 1 ≤ squareSum s h x := by
  obtain ⟨a,ha,hax⟩ := hcover
  have hb := Finset.single_le_sum (fun b (_ : b ∈ s) => sq_nonneg (cutoff h b x)) ha
  simpa [squareSum,cutoff_one_on_cell hh a hax] using hb

lemma normalizedCutoff_tsupport (s : Finset Index) (h : ℝ) (a : Index) :
    tsupport (normalizedCutoff s h a) ⊆ tsupport (cutoff h a) := by
  apply closure_mono
  intro x hx
  exact fun hz => hx (by simp [normalizedCutoff,hz])

lemma normalizedCutoff_squares {s : Finset Index} {h : ℝ} {x : Base}
    (hp : 0 < squareSum s h x) : ∑ a ∈ s, (normalizedCutoff s h a x)^2 = 1 := by
  calc
    _ = squareSum s h x / (Real.sqrt (squareSum s h x))^2 := by
      simp only [normalizedCutoff,div_pow,Finset.sum_div,squareSum]
    _ = 1 := by rw [Real.sq_sqrt hp.le,div_self hp.ne']

lemma squareSum_weighted_bounds : ∃ D : ℕ → ℝ, (∀ m, 1 ≤ D m) ∧
    ∀ (h : ℝ), 0 < h → ∀ (s : Finset Index) (m : ℕ),
      WeightedBound univ h m (D m) (squareSum s h) := by
  obtain ⟨C,hC,hbound⟩ := cutoff_weighted_bounds
  let D (m : ℕ) := 1 + 36 * (2^m * C m * C m)
  have hD (m : ℕ) : 1 ≤ D m := by
    have hc0 : 0 ≤ C m := zero_le_one.trans (hC m)
    have hp : 0 ≤ 36 * (2^m * C m * C m) := by positivity
    dsimp [D]; linarith
  refine ⟨D,hD,fun h hh s m => ?_⟩
  have hc0 : 0 ≤ C m := zero_le_one.trans (hC m)
  have hb : WeightedBound univ h m (36 * (2^m * C m * C m))
      (fun x => ∑ a ∈ s, cutoff h a x * cutoff h a x) :=
    weighted_sum_bounded_overlap hh (by positivity) s _
      (fun a _ => (cutoff_smooth h a).mul (cutoff_smooth h a))
      (fun a _ => tsupport_mul_subset_left)
      (fun a _ => (hbound h hh a m).real_mul uniqueDiffOn_univ hh.le hc0 hc0
        (cutoff_smooth h a).contDiffOn (cutoff_smooth h a).contDiffOn (hbound h hh a m))
  exact (hb.mono_const (by dsimp [D]; linarith)).congr (fun x _ => by simp [squareSum,pow_two])

end ClosedSurfaceR4.PhaseGrid

namespace ClosedSurfaceR4.PhaseGrid
open Set Function WeightedEstimates

lemma inverse_sqrt_smooth : ContDiffOn ℝ ∞ (fun r : ℝ => (Real.sqrt r)⁻¹) (Ioi 0) := by
  apply (contDiffOn_id.sqrt (fun r hr => ne_of_gt hr)).inv
  intro r hr
  exact (Real.sqrt_pos.2 hr).ne'

lemma normalizedCutoff_smooth {U : Set Base} {s : Finset Index} {h : ℝ}
    (hh : 0 < h) (hcover : ∀ x ∈ U, ∃ a ∈ s, x ∈ cell h 1 a) (a : Index) :
    ContDiffOn ℝ ∞ (normalizedCutoff s h a) U := by
  have hm : MapsTo (squareSum s h) U (Ioi 0) :=
    fun x hx => zero_lt_one.trans_le (squareSum_ge_one hh (hcover x hx))
  have hi := inverse_sqrt_smooth.comp (squareSum_smooth s h).contDiffOn hm
  change ContDiffOn ℝ ∞ (fun x => cutoff h a x / Real.sqrt (squareSum s h x)) U
  simpa only [div_eq_mul_inv,Function.comp_apply] using (cutoff_smooth h a).contDiffOn.mul hi




theorem normalizedCutoff_weighted_bounds : ∃ C : ℕ → ℝ, (∀ m, 1 ≤ C m) ∧
    ∀ (h : ℝ), 0 < h → ∀ (s : Finset Index) (U : Set Base), IsOpen U →
      (∀ x ∈ U, ∃ a ∈ s, x ∈ cell h 1 a) → ∀ (a : Index) (m : ℕ),
      WeightedBound U h m (C m) (normalizedCutoff s h a) := by
  obtain ⟨c,hc,hcb⟩ := cutoff_weighted_bounds
  obtain ⟨d,hd,hdb⟩ := squareSum_weighted_bounds
  have hcoeff (m : ℕ) : ∃ e : ℝ, 1 ≤ e ∧ ∀ j ≤ m, ∀ r ∈ Icc (1:ℝ) (d m),
      ‖iteratedFDerivWithin ℝ j (fun r : ℝ => (Real.sqrt r)⁻¹) (Ioi 0) r‖ ≤ e :=
    compact_coefficient_bound isOpen_Ioi.uniqueDiffOn isCompact_Icc
      (fun r hr => zero_lt_one.trans_le hr.1) inverse_sqrt_smooth m
  choose e he heb using hcoeff
  let C (m : ℕ) := 1 + 2^m * c m * ((m.factorial : ℝ) * e m * (d m)^m)
  have hc0 (m : ℕ) : 0 ≤ c m := zero_le_one.trans (hc m)
  have hd0 (m : ℕ) : 0 ≤ d m := zero_le_one.trans (hd m)
  have he0 (m : ℕ) : 0 ≤ e m := zero_le_one.trans (he m)
  have hC (m : ℕ) : 1 ≤ C m := by
    have hcm := hc0 m
    have hdm := hd0 m
    have hem := he0 m
    have hnonneg : 0 ≤ 2^m * c m * ((m.factorial : ℝ) * e m * (d m)^m) := by positivity
    dsimp [C]; linarith
  refine ⟨C,hC,fun h hh s U hU hcover a m => ?_⟩
  have hb := (hdb h hh s m).restrict_open hU
  have hmap : MapsTo (squareSum s h) U (Icc 1 (d m)) := by
    intro x hx
    refine ⟨squareSum_ge_one hh (hcover x hx),?_⟩
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hb.norm_le hx)
  have hpos : MapsTo (squareSum s h) U (Ioi 0) := fun x hx =>
    zero_lt_one.trans_le (hmap hx).1
  have hs : ContDiffOn ℝ ∞ (squareSum s h) U := (squareSum_smooth s h).contDiffOn
  have hi : ContDiffOn ℝ ∞ (fun x => (Real.sqrt (squareSum s h x))⁻¹) U :=
    inverse_sqrt_smooth.comp hs hpos
  have hbi := hb.comp hU.uniqueDiffOn isOpen_Ioi.uniqueDiffOn hh (hd m) (he0 m)
    hs inverse_sqrt_smooth hpos (fun j hj x hx => heb m j hj _ (hmap hx))
  have hcm := hc0 m
  have hdm := hd0 m
  have hem := he0 m
  have hp := ((hcb h hh a m).restrict_open hU).real_mul hU.uniqueDiffOn hh.le
    (hc0 m) (by positivity) (cutoff_smooth h a).contDiffOn hi hbi
  have hp' := hp.mono_const (show 2^m*c m*((m.factorial:ℝ)*e m*(d m)^m) ≤ C m by
    dsimp [C]; linarith)
  exact hp'.congr (fun x _ => by simp only [normalizedCutoff,div_eq_mul_inv])



theorem normalizedCutoff_polynomial_derivatives : ∃ C : ℕ → ℝ, (∀ j, 1 ≤ C j) ∧
    ∀ (z : ℝ), 0 < z → ∀ (s : Finset Index) (U : Set Base), IsOpen U →
      (∀ x ∈ U, ∃ a ∈ s, x ∈ cell (z^6) 1 a) → ∀ (a : Index) (j : ℕ) (x : Base),
      x ∈ U → ‖iteratedFDeriv ℝ j (normalizedCutoff s (z^6) a) x‖ ≤ C j / z^(6*j) := by
  obtain ⟨C,hC,hb⟩ := normalizedCutoff_weighted_bounds
  refine ⟨C,hC,fun z hz s U hU hcover a j x hx => ?_⟩
  have hp := (hb (z^6) (pow_pos hz _) s U hU hcover a j).deriv_le (pow_pos hz _) le_rfl hx
  simpa only [iteratedFDerivWithin_of_isOpen j hU hx,← pow_mul] using hp

end ClosedSurfaceR4.PhaseGrid

end

end OAI
