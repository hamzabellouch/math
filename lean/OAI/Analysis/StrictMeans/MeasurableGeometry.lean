import OAI.Analysis.StrictMeans.CriticalPotential

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma isClosed_exists_mem_compact {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {R : Set (P × X)} (hR : IsClosed R) :
    IsClosed {p : P | ∃ x ∈ K, (p,x) ∈ R} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : IsClosed {q : P × K | (q.1,(q.2:X)) ∈ R} :=
    hR.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hh := isClosedMap_fst_of_compactSpace _ hc
  convert hh using 1
  ext p
  simp only [mem_ofPred_eq, mem_image, Prod.exists, Subtype.exists, exists_and_right,
    exists_eq_right]
  constructor <;> rintro ⟨x,hx,hr⟩ <;> exact ⟨x,hx,hr⟩

lemma measurableSet_exists_of_closed_sigmaCompact {P X : Type*}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace X] [SigmaCompactSpace X]
    {R : Set (P × X)} (hR : IsClosed R) :
    MeasurableSet {p : P | ∃ x : X, (p,x) ∈ R} := by
  have he : {p : P | ∃ x : X, (p,x) ∈ R} =
      ⋃ n : ℕ, {p : P | ∃ x ∈ compactCovering X n, (p,x) ∈ R} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨n,hn⟩ := (iUnion_eq_univ_iff.mp (iUnion_compactCovering X)) x
      exact ⟨n,x,hn,hx⟩
    · rintro ⟨n,x,_,hx⟩
      exact ⟨x,hx⟩
  rw [he]
  exact MeasurableSet.iUnion (fun n =>
    (isClosed_exists_mem_compact (isCompact_compactCovering X n) hR).measurableSet)

lemma measurableSet_compact_positive_sublevels {P X : Type*}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X] [WeaklyLocallyCompactSpace X]
    {g : P × X → ℝ} (hg : Continuous g) :
    MeasurableSet {p : P | ∀ r : ℝ, 0 < r → IsCompact {x : X | g (p,x) ≤ r}} := by
  let K : CompactExhaustion X := CompactExhaustion.choice X
  let C (n m : ℕ) : Set P := {p | ∀ x : X, x ∉ K m → (n:ℝ)+1 ≤ g (p,x)}
  have hC (n m : ℕ) : IsClosed (C n m) := by
    change IsClosed {p | ∀ x : X, x ∉ K m → (n:ℝ)+1 ≤ g (p,x)}
    simp only [ofPred_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun _ =>
      isClosed_le continuous_const (hg.comp (continuous_id.prodMk continuous_const))))
  have he : {p : P | ∀ r : ℝ, 0 < r → IsCompact {x : X | g (p,x) ≤ r}} =
      ⋂ n : ℕ, ⋃ m : ℕ, C n m := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · intro hp n
      obtain ⟨m, hm⟩ := K.exists_superset_of_isCompact (hp ((n:ℝ)+1) (by positivity))
      refine ⟨m, ?_⟩
      intro x hx
      exact le_of_lt (lt_of_not_ge (fun hh => hx (hm hh)))
    · intro hp r hr
      obtain ⟨n,hn⟩ := exists_nat_gt r
      obtain ⟨m,hm⟩ := hp n
      have hs : {x : X | g (p,x) ≤ r} ⊆ K m := by
        intro x hx
        by_contra hxK
        have hh := hm x hxK
        exact (not_le_of_gt (lt_trans hn (by linarith : (n:ℝ)<(n:ℝ)+1))) (hh.trans hx)
      exact IsCompact.of_isClosed_subset (K.isCompact m)
        (isClosed_le (hg.comp (continuous_const.prodMk continuous_id)) continuous_const) hs
  rw [he]
  exact MeasurableSet.iInter (fun n => MeasurableSet.iUnion (fun m => (hC n m).measurableSet))

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma reciprocalFunction_deriv (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    deriv (reciprocalFunction f) z =
      -deriv (deriv (halfPlaneFunction f)) z / (deriv (halfPlaneFunction f) z) ^ 2 := by
  have h := (((halfPlaneFunction_differentiableOn f).deriv isOpen_halfPlane).differentiableAt
    (isOpen_halfPlane.mem_nhds hz)).hasDerivAt
  change deriv (fun z => (deriv (halfPlaneFunction f) z)⁻¹) z = _
  exact (h.inv (halfPlaneFunction_deriv_ne_zero f hz)).deriv

lemma logarithmicDerivative_eq_reciprocal (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    logarithmicDerivative (halfPlaneFunction f) z =
      I * z.im * (deriv (reciprocalFunction f) z / reciprocalFunction f z) := by
  rw [reciprocalFunction_deriv f hz]
  unfold logarithmicDerivative reciprocalFunction
  field_simp [halfPlaneFunction_deriv_ne_zero f hz]

lemma continuous_logarithmicDerivative :
    Continuous (fun p : DiskFamily × HalfPlaneSet => logarithmicDerivative (halfPlaneFunction p.1) p.2) := by
  have he : (fun p : DiskFamily × HalfPlaneSet => logarithmicDerivative (halfPlaneFunction p.1) p.2) =
      (fun p => I * (p.2.val.im : ℂ) * (deriv (reciprocalFunction p.1) p.2 / reciprocalFunction p.1 p.2)) := by
    funext p
    exact logarithmicDerivative_eq_reciprocal _ p.2.property
  rw [he]
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_im.comp (continuous_subtype_val.comp continuous_snd)))).mul
    (continuous_reciprocalFunction_deriv.div continuous_reciprocalFunction
      (fun p => reciprocalFunction_ne_zero _ p.2.property))

lemma continuous_jacobianExpression (k : ℝ) :
    Continuous (fun p : DiskFamily × HalfPlaneSet => jacobianExpression k (halfPlaneFunction p.1) p.2) := by
  unfold jacobianExpression
  exact ((continuous_const.add ((Complex.continuous_re.comp continuous_logarithmicDerivative).const_mul _)).add
    (continuous_logarithmicDerivative.norm.pow 2)).div_const _

lemma reciprocalFunction_rebase (f : DiskFamily) (z : UpperHalfPlane) {w : ℂ} (hw : 0 < w.im) :
    reciprocalFunction (rebase f z) w =
      reciprocalFunction f (affineAt z w) / reciprocalFunction f z :=
  halfPlaneQ_rebase f z ⟨w, hw⟩

lemma reciprocalFunction_rebase_deriv (f : DiskFamily) (z w : UpperHalfPlane) :
    deriv (reciprocalFunction (rebase f z)) w =
      (deriv (reciprocalFunction f) (affineAt z w) * z.im) / reciprocalFunction f z := by
  have hf := ((reciprocalFunction_differentiableOn f).differentiableAt
    (isOpen_halfPlane.mem_nhds (affineAt_mapsTo z w.im_pos))).hasDerivAt
  have hh := (hf.comp (w : ℂ) (affineAt_hasDerivAt z w)).div_const (reciprocalFunction f z)
  have he : reciprocalFunction (rebase f z) =ᶠ[𝓝 (w : ℂ)]
      fun u => reciprocalFunction f (affineAt z u) / reciprocalFunction f z :=
    Filter.eventually_of_mem (isOpen_halfPlane.mem_nhds w.im_pos)
      (fun u hu => reciprocalFunction_rebase f z hu)
  exact (hh.congr_of_eventuallyEq he).deriv

lemma logarithmicDerivative_rebase (f : DiskFamily) (z w : UpperHalfPlane) :
    logarithmicDerivative (halfPlaneFunction (rebase f z)) w =
      logarithmicDerivative (halfPlaneFunction f) (affineAt z w) := by
  rw [logarithmicDerivative_eq_reciprocal _ w.im_pos,
    logarithmicDerivative_eq_reciprocal _ (affineAt_mapsTo z w.im_pos),
    reciprocalFunction_rebase_deriv, reciprocalFunction_rebase f z w.im_pos]
  simp only [affineAt, add_im, ofReal_im, mul_im, ofReal_re, zero_mul, zero_add]
  field_simp [reciprocalFunction_ne_zero f z.im_pos,
    reciprocalFunction_ne_zero f (affineAt_mapsTo z w.im_pos)]
  push_cast
  ring

lemma jacobianExpression_rebase (k : ℝ) (f : DiskFamily) (z w : UpperHalfPlane) :
    jacobianExpression k (halfPlaneFunction (rebase f z)) w =
      jacobianExpression k (halfPlaneFunction f) (affineAt z w) := by
  simp only [jacobianExpression, logarithmicDerivative_rebase]

lemma jacobianExpression_rebase_I (k : ℝ) (f : DiskFamily) (z : UpperHalfPlane) :
    jacobianExpression k (halfPlaneFunction (rebase f z)) I =
      jacobianExpression k (halfPlaneFunction f) z := by
  simpa using jacobianExpression_rebase k f z UpperHalfPlane.I

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def reciprocalPotential (k : ℝ) (p : DiskFamily × ℂ) (z : UpperHalfPlane) : ℝ :=
  ‖halfPlaneFunction p.1 z-p.2‖ / z.im ^ k

lemma continuous_reciprocalPotential (k : ℝ) :
    Continuous (fun p : (DiskFamily × ℂ) × UpperHalfPlane => reciprocalPotential k p.1 p.2) := by
  exact ((continuous_halfPlaneFunction.comp
    ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).sub
      (continuous_snd.comp continuous_fst)).norm.div
    ((UpperHalfPlane.continuous_im.comp continuous_snd).rpow_const (fun p => Or.inl p.2.im_ne_zero))
    (fun p => (Real.rpow_pos_of_pos p.2.im_pos _).ne')

lemma reciprocalPotential_sublevel_image (k : ℝ) (p : DiskFamily × ℂ) {r : ℝ} (hr : 0 < r) :
    UpperHalfPlane.coe '' {z : UpperHalfPlane | reciprocalPotential k p z ≤ r} =
      potentialSuperlevel k (halfPlaneFunction p.1) p.2 (1/r) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    refine ⟨w.im_pos, ?_⟩
    change ‖halfPlaneFunction p.1 w - p.2‖ / w.im^k ≤ r at hw
    rw [le_div_iff₀ (one_div_pos.mpr hr)]
    have hh := (div_le_iff₀ (Real.rpow_pos_of_pos w.im_pos k)).mp hw
    simpa only [one_div, div_eq_mul_inv, mul_assoc, one_mul] using
      (div_le_iff₀ hr).mpr (by simpa only [mul_comm, UpperHalfPlane.coe_im] using hh)
  · intro hz
    refine ⟨⟨z,hz.1⟩, ?_, rfl⟩
    change ‖halfPlaneFunction p.1 z-p.2‖/z.im^k ≤ r
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hz.1 k)]
    have hh := hz.2
    simpa only [one_div, div_eq_mul_inv, inv_inv, one_mul, mul_one, mul_comm] using hh

lemma compactPotential_iff (k : ℝ) (p : DiskFamily × ℂ) :
    (∀ h : ℝ, 0 < h → IsCompact (potentialSuperlevel k (halfPlaneFunction p.1) p.2 h)) ↔
    (∀ r : ℝ, 0 < r → IsCompact {z : UpperHalfPlane | reciprocalPotential k p z ≤ r}) := by
  constructor
  · intro hp r hr
    apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
    rw [reciprocalPotential_sublevel_image k p hr]
    exact hp _ (one_div_pos.mpr hr)
  · intro hp h hh
    have he := reciprocalPotential_sublevel_image k p (one_div_pos.mpr hh)
    rw [one_div_one_div] at he
    rw [← he]
    exact (hp _ (one_div_pos.mpr hh)).image UpperHalfPlane.continuous_coe

def GoodPair (k : ℝ) (p : DiskFamily × ℂ) : Prop :=
  (∀ h : ℝ, 0 < h → IsCompact (potentialSuperlevel k (halfPlaneFunction p.1) p.2 h)) ∧
  (∀ z : UpperHalfPlane, criticalMap k (halfPlaneFunction p.1) z = p.2 →
    jacobianExpression k (halfPlaneFunction p.1) z ≠ 0) ∧
  (∀ z w : UpperHalfPlane, criticalMap k (halfPlaneFunction p.1) z = p.2 →
    criticalMap k (halfPlaneFunction p.1) w = p.2 →
    criticalHeight k (halfPlaneFunction p.1) z = criticalHeight k (halfPlaneFunction p.1) w → z = w)

lemma continuous_jacobianExpression_upper (k : ℝ) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => jacobianExpression k (halfPlaneFunction p.1) p.2) := by
  have hc : Continuous (fun p : DiskFamily × UpperHalfPlane =>
      (p.1, (⟨(p.2:ℂ),p.2.im_pos⟩ : HalfPlaneSet))) :=
    continuous_fst.prodMk ((UpperHalfPlane.continuous_coe.comp continuous_snd).subtype_mk _)
  have hh := (continuous_jacobianExpression k).comp hc
  exact hh

lemma measurableSet_regular_pairs (k : ℝ) :
    MeasurableSet {p : DiskFamily × ℂ | ∀ z : UpperHalfPlane,
      criticalMap k (halfPlaneFunction p.1) z = p.2 →
        jacobianExpression k (halfPlaneFunction p.1) z ≠ 0} := by
  have hm : Continuous (fun q : (DiskFamily × ℂ) × UpperHalfPlane => (q.1.1,q.2)) :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have hG := (continuous_criticalMap k).comp hm
  have hJ := (continuous_jacobianExpression_upper k).comp hm
  have he := measurableSet_exists_of_closed_sigmaCompact
    ((isClosed_eq hG (continuous_snd.comp continuous_fst)).inter (isClosed_eq hJ (continuous_const (y := (0 : ℝ)))))
  convert he.compl using 1
  ext p
  simp

lemma measurableSet_untied_pairs (k : ℝ) :
    MeasurableSet {p : DiskFamily × ℂ | ∀ z w : UpperHalfPlane,
      criticalMap k (halfPlaneFunction p.1) z = p.2 →
      criticalMap k (halfPlaneFunction p.1) w = p.2 →
      criticalHeight k (halfPlaneFunction p.1) z = criticalHeight k (halfPlaneFunction p.1) w → z = w} := by
  let R (n : ℕ) : Set ((DiskFamily × ℂ) × (UpperHalfPlane × UpperHalfPlane)) :=
    {q | criticalMap k (halfPlaneFunction q.1.1) q.2.1 = q.1.2 ∧
      criticalMap k (halfPlaneFunction q.1.1) q.2.2 = q.1.2 ∧
      criticalHeight k (halfPlaneFunction q.1.1) q.2.1 = criticalHeight k (halfPlaneFunction q.1.1) q.2.2 ∧
      1/((n:ℝ)+1) ≤ dist (q.2.1 : ℂ) (q.2.2 : ℂ)}
  have hR (n : ℕ) : IsClosed (R n) := by
    exact (isClosed_eq ((continuous_criticalMap k).comp
      ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd)))
        (continuous_snd.comp continuous_fst)).inter <|
      (isClosed_eq ((continuous_criticalMap k).comp
        ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd)))
          (continuous_snd.comp continuous_fst)).inter <|
      (isClosed_eq ((continuous_criticalHeight k).comp
        ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd)))
        ((continuous_criticalHeight k).comp
          ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd)))).inter <|
      isClosed_le continuous_const
        ((UpperHalfPlane.continuous_coe.comp (continuous_fst.comp continuous_snd)).dist
          (UpperHalfPlane.continuous_coe.comp (continuous_snd.comp continuous_snd)))
  have he : {p : DiskFamily × ℂ | ∀ z w : UpperHalfPlane,
      criticalMap k (halfPlaneFunction p.1) z = p.2 →
      criticalMap k (halfPlaneFunction p.1) w = p.2 →
      criticalHeight k (halfPlaneFunction p.1) z = criticalHeight k (halfPlaneFunction p.1) w → z = w} =
      (⋃ n : ℕ, {p : DiskFamily × ℂ | ∃ x : UpperHalfPlane × UpperHalfPlane, (p,x) ∈ R n})ᶜ := by
    ext p
    simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion]
    constructor
    · intro hp
      rintro ⟨n,⟨z,w⟩,hz,hw,hv,hd⟩
      have := hp z w hz hw hv
      subst w
      have h0 := one_div_pos.mpr (by positivity : (0:ℝ)<(n:ℝ)+1)
      rw [dist_self] at hd
      linarith
    · intro hp z w hz hw hv
      by_contra hne
      have hd : 0 < dist (z:ℂ) (w:ℂ) := dist_pos.mpr (fun he => hne (UpperHalfPlane.ext he))
      obtain ⟨n,hn⟩ := exists_nat_gt (1 / dist (z:ℂ) (w:ℂ))
      apply hp
      refine ⟨n,(z,w),hz,hw,hv,?_⟩
      apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
      have hh := (div_lt_iff₀ hd).mp hn
      nlinarith
  rw [he]
  exact (MeasurableSet.iUnion (fun n => measurableSet_exists_of_closed_sigmaCompact (hR n))).compl

lemma measurableSet_goodPairs (k : ℝ) : MeasurableSet {p : DiskFamily × ℂ | GoodPair k p} := by
  have hc : MeasurableSet {p : DiskFamily × ℂ |
      ∀ h : ℝ, 0 < h → IsCompact (potentialSuperlevel k (halfPlaneFunction p.1) p.2 h)} := by
    simp only [compactPotential_iff]
    exact measurableSet_compact_positive_sublevels (continuous_reciprocalPotential k)
  exact hc.inter ((measurableSet_regular_pairs k).inter (measurableSet_untied_pairs k))

end
end StrictInverseFirstPower

end

end OAI
