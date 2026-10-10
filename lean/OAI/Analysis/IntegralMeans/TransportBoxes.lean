import OAI.Analysis.IntegralMeans.GoodPairs

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun

def displacementWindow (N : ℝ) (z w : ℂ) : Prop :=
  z.im ≤ N*w.im ∧ w.im ≤ N*z.im ∧ |w.re-z.re| ≤ N*z.im

def transportWindow (k N : ℝ) : Set (DiskClass × halfPlane) :=
  {q | q ∈ pairingDomain k ∧
    displacementWindow N q.2 (criticalPair (classFun q.1) k q.2)}

lemma measurableSet_transportWindow {k : ℝ} (hk : 0 < k) (N : ℝ) :
    MeasurableSet (transportWindow k N) := by
  have hr := measurable_criticalPair hk
  have hz : Measurable (fun q : pairingDomain k => (q.val.2 : ℂ)) :=
    measurable_subtype_coe.comp (measurable_subtype_coe.snd)
  have hm : MeasurableSet {q : pairingDomain k |
      displacementWindow N q.val.2 (criticalPair (classFun q.val.1) k q.val.2)} :=
    (measurableSet_le (Complex.measurable_im.comp hz)
      (measurable_const.mul (Complex.measurable_im.comp hr))).inter
    ((measurableSet_le (Complex.measurable_im.comp hr)
      (measurable_const.mul (Complex.measurable_im.comp hz))).inter
    (measurableSet_le (((Complex.measurable_re.comp hr).sub (Complex.measurable_re.comp hz)).abs)
      (measurable_const.mul (Complex.measurable_im.comp hz))))
  have h := (measurableSet_pairingDomain hk.le).subtype_image hm
  convert h using 1
  ext q
  simp only [transportWindow,mem_ofPred_eq,mem_image,Subtype.exists,exists_prop]
  aesop

lemma displacementWindow_affine (N : ℝ) {t : ℂ} (ht : t ∈ halfPlane) (z w : ℂ) :
    displacementWindow N (affine t z) (affine t w) ↔ displacementWindow N z w := by
  have him (v : ℂ) : (affine t v).im = t.im*v.im := by simp [affine]
  have hre : (affine t w).re-(affine t z).re = t.im*(w.re-z.re) := by simp [affine]; ring
  simp only [displacementWindow,him,hre,abs_mul,abs_of_pos (show 0<t.im from ht)]
  simp only [show N*(t.im*w.im) = t.im*(N*w.im) from by ring,
    show N*(t.im*z.im) = t.im*(N*z.im) from by ring,
    mul_le_mul_iff_right₀ (show 0<t.im from ht)]

lemma transportWindow_root (g : DiskClass) {k : ℝ} (hk : 0 < k) (N : ℝ) (z : halfPlane) :
    (rerootClass g z,halfOne) ∈ transportWindow k N ↔ (g,z) ∈ transportWindow k N := by
  have hJ := class_normalizedJacobian_root g hk z
  have hG := class_goodPair_root g hk z
  change (0 < normalizedJacobian (classFun (rerootClass g z)) k Complex.I ∧
    GoodPair (classFun (rerootClass g z)) k (criticalMap (classFun (rerootClass g z)) k Complex.I)) ∧ _ ↔
    (0 < normalizedJacobian (classFun g) k z ∧ GoodPair (classFun g) k (criticalMap (classFun g) k z)) ∧ _
  rw [hJ,hG]
  apply and_congr_right
  intro h
  have he := class_criticalPair_reroot g hk z halfOne (by simpa only [halfOne,affine_I] using h.1)
    (by simpa only [halfOne,affine_I] using h.2)
  simp only [halfOne,affine_I] at he
  change displacementWindow N Complex.I (criticalPair (classFun (rerootClass g z)) k Complex.I) ↔
    displacementWindow N z (criticalPair (classFun g) k z)
  rw [← displacementWindow_affine N z.property Complex.I,affine_I,he]

lemma displacementWindow_mono {N M : ℝ} (hNM : N ≤ M) {z w : ℂ}
    (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) (h : displacementWindow N z w) :
    displacementWindow M z w :=
  ⟨h.1.trans (mul_le_mul_of_nonneg_right hNM hw.le),
    h.2.1.trans (mul_le_mul_of_nonneg_right hNM hz.le),
    h.2.2.trans (mul_le_mul_of_nonneg_right hNM hz.le)⟩

lemma exists_displacementWindow {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    ∃ n : ℕ, displacementWindow (n+1) z w := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max (z.im/w.im) (max (w.im/z.im) (|w.re-z.re|/z.im)))
  refine ⟨n,?_,?_,?_⟩
  · exact (div_le_iff₀ hw).mp ((le_max_left _ _).trans (by exact_mod_cast hn.le.trans (le_add_of_nonneg_right zero_le_one)))
  · exact (div_le_iff₀ hz).mp (((le_max_left _ _).trans (le_max_right _ _)).trans (by exact_mod_cast hn.le.trans (le_add_of_nonneg_right zero_le_one)))
  · exact (div_le_iff₀ hz).mp (((le_max_right _ _).trans (le_max_right _ _)).trans (by exact_mod_cast hn.le.trans (le_add_of_nonneg_right zero_le_one)))

lemma transportWindow_mono {k : ℝ} (hk : 0 < k) {N M : ℝ} (hNM : N ≤ M) :
    transportWindow k N ⊆ transportWindow k M := by
  rintro ⟨g,z⟩ ⟨hp,hw⟩
  exact ⟨hp,displacementWindow_mono hNM z.property
    (criticalPair_spec (classFun_schlicht g).1 hk z.property hp.1 hp.2).1 hw⟩

lemma iUnion_transportWindow {k : ℝ} (hk : 0 < k) :
    (⋃ n : ℕ, transportWindow k (n+1)) = pairingDomain k := by
  ext q
  constructor
  · rintro ⟨_,⟨n,rfl⟩,hq⟩
    exact hq.1
  · intro hq
    obtain ⟨n,hn⟩ := exists_displacementWindow q.2.property
      (criticalPair_spec (classFun_schlicht q.1).1 hk q.2.property hq.1 hq.2).1
    exact mem_iUnion.mpr ⟨n,hq,hn⟩

def transportSlice (g : DiskClass) (k N : ℝ) : Set ℂ :=
  {z | z ∈ halfPlane ∧ 0 < normalizedJacobian (classFun g) k z ∧
    GoodPair (classFun g) k (criticalMap (classFun g) k z) ∧
    displacementWindow N z (criticalPair (classFun g) k z)}

lemma transportSlice_iff (g : DiskClass) (k N : ℝ) (z : halfPlane) :
    z.val ∈ transportSlice g k N ↔ (g,z) ∈ transportWindow k N := by
  simp only [transportSlice,transportWindow,pairingDomain,mem_ofPred_eq,z.property,true_and,and_assoc]

lemma measurableSet_transportSlice (g : DiskClass) {k : ℝ} (hk : 0 < k) (N : ℝ) :
    MeasurableSet (transportSlice g k N) := by
  apply measurableSet_halfPlane_pred
  have hm : Measurable (fun z : halfPlane => (g,z)) := measurable_const.prodMk measurable_id
  have h := (measurableSet_transportWindow hk N).preimage hm
  convert h using 1
  ext z
  exact and_assoc.symm

def transportBox (R a b : ℝ) : Set ℂ := {z | |z.re| ≤ R ∧ a ≤ z.im ∧ z.im ≤ b}

lemma measurableSet_transportBox (R a b : ℝ) : MeasurableSet (transportBox R a b) :=
  (measurableSet_le Complex.measurable_re.abs measurable_const).inter
    ((measurableSet_le measurable_const Complex.measurable_im).inter
      (measurableSet_le Complex.measurable_im measurable_const))

lemma pair_mem_enlargedBox {N R Y : ℝ} (hN : 1 ≤ N) {z w : ℂ}
    (hz : z ∈ transportBox R 1 Y) (hw : displacementWindow N z w) :
    w ∈ transportBox (R+N*Y) (1/N) (N*Y) := by
  have hn : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hab : |w.re| ≤ |z.re|+|w.re-z.re| := by
    calc |w.re| = |z.re+(w.re-z.re)| := by congr 1; ring
         _ ≤ |z.re|+|w.re-z.re| := abs_add_le _ _
  refine ⟨hab.trans (add_le_add hz.1 (hw.2.2.trans (mul_le_mul_of_nonneg_left hz.2.2 hn.le))),?_,
    hw.2.1.trans (mul_le_mul_of_nonneg_left hz.2.2 hn.le)⟩
  rw [div_le_iff₀ hn]
  nlinarith [hw.1,hz.2.1]

lemma fiberSum_mul_indicator.{u_1, u_2} {X : Type u_1} {Y : Type u_2} (f : X → Y) (s t : Set X)
    (u : X → ℝ≥0∞) (y : Y) :
    fiberSum f s (fun x => u x * t.indicator 1 x) y = fiberSum f (s ∩ t) u y := by
  classical
  rw [fiberSum,fiberSum,tsum_subtype {x | x ∈ s ∧ f x = y} (fun x => u x * t.indicator 1 x),
    tsum_subtype {x | x ∈ s ∩ t ∧ f x = y} u]
  apply tsum_congr
  intro x
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> by_cases hy : f x = y <;>
    simp [hs,ht,hy]

lemma transport_box (g : DiskClass) {β k N R Y : ℝ} (hk : 0 < k)
    (hb : β-1 = 4*(k-1)) (hN : 1 ≤ N) :
    (∫⁻ z in halfPlane, transportDensity g β z * ENNReal.ofReal (normalizedJacobian (classFun g) k z) *
      (transportSlice g k N ∩ transportBox R 1 Y).indicator 1 z) ≤
    ∫⁻ z in halfPlane, transportDensity g β z * ENNReal.ofReal (-normalizedJacobian (classFun g) k z) *
      (transportBox (R+N*Y) (1/N) (N*Y)).indicator 1 z := by
  let S := transportSlice g k N ∩ transportBox R 1 Y
  let T := transportBox (R+N*Y) (1/N) (N*Y)
  have hs : MeasurableSet S := (measurableSet_transportSlice g hk N).inter (measurableSet_transportBox R 1 Y)
  have ht : MeasurableSet T := measurableSet_transportBox _ _ _
  have hp := transport_area g β k 1 (by norm_num) (measurable_const.indicator hs : Measurable (S.indicator (1 : ℂ → ℝ≥0∞)))
  have hn := transport_area g β k (-1) (by norm_num) (measurable_const.indicator ht : Measurable (T.indicator (1 : ℂ → ℝ≥0∞)))
  simp only [one_mul] at hp
  simp only [neg_one_mul] at hn
  apply le_trans hp.le
  apply le_trans ?_ hn.symm.le
  apply lintegral_mono
  intro ξ
  apply le_trans (fiberSum_mul_indicator (criticalMap (classFun g) k) (jacobianRegion g k 1) S (targetDensity g β) ξ).le
  apply le_trans ?_ (fiberSum_mul_indicator (criticalMap (classFun g) k) (jacobianRegion g k (-1)) T (targetDensity g β) ξ).symm.le
  apply fiberSum_mono_injective (criticalPair (classFun g) k) ξ
  · intro z hz hG
    have hsz := hz.2.1
    have hpair := criticalPair_spec (classFun_schlicht g).1 hk hsz.1 hsz.2.1 hsz.2.2.1
    exact ⟨⟨⟨hpair.1,by simpa only [neg_one_mul] using neg_pos.mpr hpair.2.2.1⟩,
      pair_mem_enlargedBox hN hz.2.2 hsz.2.2.2⟩,hpair.2.1.trans hG⟩
  · apply (criticalPair_injective (classFun_schlicht g).1 hk).mono
    intro z hz
    exact ⟨hz.1.2.1.1,hz.1.2.1.2.1,hz.1.2.1.2.2.1⟩
  · intro z hz _
    exact targetDensity_le_pair g hk hb hz.2.1.1 hz.2.1.2.1 hz.2.1.2.2.1

lemma measurableSet_exceptionSlice (g : DiskClass) {k : ℝ} (hk : 0 < k) :
    MeasurableSet {z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)} := by
  apply measurableSet_halfPlane_pred
  have hm : Measurable (fun z : halfPlane => (g,criticalMap (classFun g) k z)) :=
    (continuous_const.prodMk ((continuous_class_criticalMap k).comp
      (show Continuous (fun z : halfPlane => (g,z)) from continuous_const.prodMk continuous_id))).measurable
  exact ((measurableSet_class_goodPairs hk.le).preimage hm).compl

lemma exceptional_transport_zero (g : DiskClass) {β k : ℝ} (hk : 0 < k)
    (hg : ∀ᵐ ξ : ℂ, GoodPair (classFun g) k ξ) :
    (∫⁻ z in halfPlane, transportDensity g β z * ENNReal.ofReal (normalizedJacobian (classFun g) k z) *
      {z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)}.indicator 1 z) = 0 := by
  have hs := measurableSet_exceptionSlice g hk
  have he := transport_area g β k 1 (by norm_num)
    (measurable_const.indicator hs : Measurable ({z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)}.indicator (1 : ℂ → ℝ≥0∞)))
  simp only [one_mul] at he
  refine he.trans ?_
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hg] with ξ hξ
  unfold fiberSum
  apply ENNReal.tsum_eq_zero.mpr
  intro z
  have hn : z.val ∉ {z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)} := by
    rintro ⟨_,hbad⟩
    exact hbad (z.property.2.symm ▸ hξ)
  exact (congrArg (targetDensity g β z * ·) (indicator_of_notMem (f := (1 : ℂ → ℝ≥0∞)) hn)).trans (mul_zero _)

end Brennan

end

end OAI
