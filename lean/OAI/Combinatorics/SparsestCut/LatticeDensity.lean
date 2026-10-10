import OAI.Combinatorics.SparsestCut.ProductSlice

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.LatticeDensity

lemma cell_bound {h h' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ t, HasDerivAt h (h' t) t) (hi : IntervalIntegrable h' volume a b) :
    (b-a)*h a ≤ (∫ t in a..b, h t)+(b-a)*(∫ t in a..b, |h' t|) := by
  have hc : Continuous h := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hh : ∀ t ∈ Icc a b, h a ≤ h t+∫ x in a..b, |h' x| := by
    intro t ht
    have hid : IntervalIntegrable h' volume a t := hi.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2)
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hid
    have hm : (∫ x in a..t, |h' x|) ≤ ∫ x in a..b, |h' x| := by
      apply intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      · filter_upwards with x using abs_nonneg (h' x)
      · exact hi.abs
    have hn := intervalIntegral.abs_integral_le_integral_abs (f := h') (μ := volume) ht.1
    rw [he] at hn
    have habs : h a-h t ≤ |h t-h a| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith
  have h := intervalIntegral.integral_mono_on (μ := volume) hab intervalIntegrable_const
    ((hc.intervalIntegrable a b).add intervalIntegrable_const) hh
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add (hc.intervalIntegrable a b) intervalIntegrable_const,
    intervalIntegral.integral_const] at h
  simpa only [smul_eq_mul] using h

lemma lattice_intervals_disjoint {τ : ℝ} (hτ : 0 < τ) :
    ∀ k l : ℤ, k ≠ l → Disjoint (Ioc ((k:ℝ)*τ) (((k:ℝ)+1)*τ))
      (Ioc ((l:ℝ)*τ) (((l:ℝ)+1)*τ)) := by
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have hkl' : (k:ℝ)+1 ≤ l := by exact_mod_cast (Int.add_one_le_iff.mpr h)
    have hz := mul_le_mul_of_nonneg_right hkl' hτ.le
    linarith [hx.2, hy.1]
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have hkl' : (l:ℝ)+1 ≤ k := by exact_mod_cast (Int.add_one_le_iff.mpr h)
    have hz := mul_le_mul_of_nonneg_right hkl' hτ.le
    linarith [hy.2, hx.1]

lemma lattice_bound {h h' : ℝ → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hd : ∀ t, HasDerivAt h (h' t) t) (hh : ∀ t, 0 ≤ h t)
    (hi : Integrable h) (hi' : Integrable h') (s : Finset ℤ) :
    τ*(∑ k ∈ s, h ((k:ℝ)*τ)) ≤ (∫ t, h t)+τ*(∫ t, |h' t|) := by
  let U := ⋃ k ∈ s, Ioc ((k:ℝ)*τ) (((k:ℝ)+1)*τ)
  have hle (k : ℤ) : (k:ℝ)*τ ≤ ((k:ℝ)+1)*τ := by linarith
  have hs (f : ℝ → ℝ) (hf : Integrable f) :
      (∑ k ∈ s, ∫ t in ((k:ℝ)*τ)..(((k:ℝ)+1)*τ), f t) = ∫ t in U, f t := by
    simp_rw [intervalIntegral.integral_of_le (hle _)]
    exact (integral_biUnion_finset s (fun _ _ => measurableSet_Ioc)
      (fun k _ l _ hkl => lattice_intervals_disjoint hτ k l hkl)
      (fun _ _ => hf.integrableOn)).symm
  have he (k : ℤ) : (((k:ℝ)+1)*τ-(k:ℝ)*τ) = τ := by ring
  have hb (k : ℤ) : τ*h ((k:ℝ)*τ) ≤
      (∫ t in ((k:ℝ)*τ)..(((k:ℝ)+1)*τ), h t)+
        τ*(∫ t in ((k:ℝ)*τ)..(((k:ℝ)+1)*τ), |h' t|) := by
    simpa only [he] using cell_bound (a := (k:ℝ)*τ) (b := ((k:ℝ)+1)*τ)
      (by linarith) hd hi'.intervalIntegrable
  calc
    _ = ∑ k ∈ s, τ*h ((k:ℝ)*τ) := Finset.mul_sum ..
    _ ≤ ∑ k ∈ s, ((∫ t in ((k:ℝ)*τ)..(((k:ℝ)+1)*τ), h t)+
        τ*(∫ t in ((k:ℝ)*τ)..(((k:ℝ)+1)*τ), |h' t|)) := Finset.sum_le_sum (fun k _ => hb k)
    _ = (∫ t in U, h t)+τ*(∫ t in U, |h' t|) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs h hi, hs (fun t => |h' t|) hi'.abs]
    _ ≤ _ := add_le_add
      (integral_mono_measure Measure.restrict_le_self (by filter_upwards with t using hh t) hi)
      (mul_le_mul_of_nonneg_left
        (integral_mono_measure Measure.restrict_le_self (by filter_upwards with t using abs_nonneg (h' t)) hi'.abs) hτ.le)

end UniformSparsestCut.LatticeDensity

namespace UniformSparsestCut.LatticeDensity
open MeasureTheory Set
open scoped BigOperators

lemma affine_integral (f : ℝ → ℝ) (c a : ℝ) :
    (∫ t, f (c-t/a)) = |a| *(∫ t, f t) := by
  rw [Measure.integral_comp_div (fun x => f (c-x)),smul_eq_mul,integral_sub_left_eq_self]

lemma affine_integrable {f : ℝ → ℝ} (hf : Integrable f) (c : ℝ) {a : ℝ} (ha : a ≠ 0) :
    Integrable (fun t => f (c-t/a)) :=
  ((integrable_comp_sub_left f c).mpr hf).comp_div ha

lemma affine_lattice_bound {φ φ' : ℝ → ℝ} (hd : ∀ t, HasDerivAt φ (φ' t) t)
    (hn : ∀ t, 0 ≤ φ t) (hi : Integrable φ) (hi' : Integrable φ')
    (h1 : ∫ t, φ t=1) {τ a : ℝ} (hτ : 0 < τ) (ha : a ≠ 0) (c : ℝ) (s : Finset ℤ) :
    τ/|a| *(∑ k ∈ s, φ (c-(k:ℝ)*τ/a)) ≤ 1+τ/|a| *(∫ t, |φ' t|) := by
  let h : ℝ → ℝ := fun t => φ (c-t/a)/|a|
  let h' : ℝ → ℝ := fun t => -(φ' (c-t/a)/a)/|a|
  have ha' : 0 < |a| := abs_pos.mpr ha
  have hD (t : ℝ) : HasDerivAt h (h' t) t := by
    convert! ((hd (c-t/a)).comp t (((hasDerivAt_id t).div_const a).const_sub c)).div_const |a| using 1
    dsimp [h']
    ring
  have hint : (∫ t, h t)=1 := by
    dsimp [h]
    rw [integral_div,affine_integral,h1,mul_one,div_self ha'.ne']
  have h'int : (∫ t, |h' t|)=(∫ t, |φ' t|)/|a| := by
    dsimp [h']
    simp only [abs_div,abs_neg,abs_abs]
    rw [integral_div,integral_div,affine_integral (fun t => |φ' t|)]
    field_simp
  have hb := lattice_bound hτ hD (fun t => div_nonneg (hn _) (abs_nonneg _))
    ((affine_integrable hi c ha).div_const _) (((affine_integrable hi' c ha).div_const a).neg.div_const _) s
  rw [hint,h'int] at hb
  dsimp [h] at hb
  rw [← Finset.sum_div] at hb
  convert hb using 1 <;> ring

end UniformSparsestCut.LatticeDensity

end

end OAI
