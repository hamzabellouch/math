import Mathlib
import OAI.Probability.Perceptron.Variational.HeatGrid

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open Filter Set Metric MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma equicontinuous_of_convex_nonneg_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ℕ → E → ℝ) (f : E → ℝ)
    (hcv : ∀ n, ConvexOn ℝ Set.univ (F n)) (h0 : ∀ n x, 0 ≤ F n x)
    (ht : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) : Equicontinuous F := by
  let G : E → ℝ := fun x => sSup (Set.range (fun n => F n x))
  have hb (x : E) : BddAbove (Set.range (fun n => F n x)) := (ht x).bddAbove_range
  have hle (n : ℕ) (x : E) : F n x ≤ G x := le_csSup (hb x) ⟨n,rfl⟩
  have hG : ConvexOn ℝ Set.univ G := by
    refine ⟨convex_univ,?_⟩
    intro x _ y _ a b ha hb' hab
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨n,rfl⟩
    exact ((hcv n).2 trivial trivial ha hb' hab).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hle n x) ha)
        (mul_le_mul_of_nonneg_left (hle n y) hb'))
  have hGc : Continuous G := continuousOn_univ.mp (hG.continuousOn isOpen_univ)
  intro x
  have hn : {y : E | G y < G x+1} ∈ 𝓝 x :=
    (hGc.continuousAt).preimage_mem_nhds (Iio_mem_nhds (by linarith))
  obtain ⟨r,hr,hrG⟩ := Metric.mem_nhds_iff.mp hn
  let K : ℝ≥0 := (2*(G x+1)/(r/2)).toNNReal
  have hLip (n : ℕ) : LipschitzOnWith K (F n) (ball x (r-r/2)) := by
    apply ((hcv n).subset (Set.subset_univ _) (convex_ball _ _)).lipschitzOnWith_of_abs_le
      (half_pos hr)
    intro y hy
    rw [abs_of_nonneg (h0 n y)]
    exact (hle n y).trans (hrG hy).le
  apply Metric.equicontinuousAt_of_continuity_modulus (fun y => (K:ℝ)*dist x y)
    (by
      have hc : Continuous (fun y : E => (K:ℝ)*dist x y) := by fun_prop
      simpa only [dist_self,mul_zero] using hc.tendsto x) F
  filter_upwards [ball_mem_nhds x (by linarith : 0 < r-r/2)] with y hy n
  have hx : x ∈ ball x (r-r/2) := by rw [mem_ball,dist_self]; linarith
  exact (hLip n).dist_le_mul x hx y hy

lemma tendstoUniformlyOn_of_convex_nonneg_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ℕ → E → ℝ) (f : E → ℝ)
    (hcv : ∀ n, ConvexOn ℝ Set.univ (F n)) (h0 : ∀ n x, 0 ≤ F n x)
    (ht : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    {K : Set E} (hK : IsCompact K) : TendstoUniformlyOn F f atTop K := by
  have he := equicontinuous_of_convex_nonneg_tendsto F f hcv h0 ht
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have he' : Equicontinuous (fun n (x : K) => F n x) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ,hδ,hd⟩ := Metric.equicontinuousAt_iff.mp (he (x:E)) ε hε
    exact ⟨δ,hδ,fun y hy n => hd (y:E) hy n⟩
  have hp : Tendsto (fun n (x : K) => F n x) atTop (𝓝 (fun x : K => f x)) :=
    tendsto_pi_nhds.mpr (fun x => ht x)
  have hu := (he'.tendsto_uniformFun_iff_pi atTop (fun x : K => f x)).mpr hp
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp hu)

lemma finiteAmplitudeSphereValue_uniform {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) {K : Set (Fin (k+1) → ℝ)}
    (hK : IsCompact K) : TendstoUniformlyOn (fun n => finiteAmplitudeSphereValue n k w)
      (finiteAmplitudeSphereDual w (fun i => (hw i).le) hw1) atTop K :=
  tendstoUniformlyOn_of_convex_nonneg_tendsto _ _ (finiteAmplitudeSphereValue_convex w hw hw1)
    (finiteAmplitudeSphereValue_nonneg w hw hw1) (finiteAmplitudeSphereValue_tendsto w hw hw1) hK

def fieldAmplitudes (k : ℕ) (h : Fin (k+1) → ℝ) (i : Fin (k+1)) : ℝ :=
  if _hi : i.val < k then stepFieldIncrement k h i.val else Real.sqrt (2*h 0)

lemma fieldAmplitudes_last (k : ℕ) (h : Fin (k+1) → ℝ) :
    fieldAmplitudes k h (Fin.last k)=Real.sqrt (2*h 0) := by
  simp [fieldAmplitudes]

lemma fieldAmplitudes_increment (k : ℕ) (h : Fin (k+1) → ℝ) :
    finiteAmplitudeIncrement k (fieldAmplitudes k h)=stepFieldIncrement k h := by
  funext j
  by_cases hj : j < k
  · simp [finiteAmplitudeIncrement,fieldAmplitudes,hj]
  · simp [finiteAmplitudeIncrement,stepFieldIncrement,hj]

lemma fieldAmplitudes_continuous (k : ℕ) : Continuous (fieldAmplitudes k) := by
  apply continuous_pi
  intro i
  unfold fieldAmplitudes
  split_ifs
  · unfold stepFieldIncrement
    split_ifs
    fun_prop
  · fun_prop

lemma amplitudeCovarianceLevels_fieldAmplitudes (k : ℕ) (h : Fin (k+1) → ℝ)
    (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    amplitudeCovarianceLevels k (finiteAmplitudeIncrement k (fieldAmplitudes k h))
      (fieldAmplitudes k h (Fin.last k))=h := by
  rw [fieldAmplitudes_increment,fieldAmplitudes_last]
  funext i
  induction i using Fin.induction with
  | zero =>
    have hr := amplitudeCovarianceLevels_root k (stepFieldIncrement k h) (Real.sqrt (2*h 0))
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hh0)] at hr
    linarith
  | succ i ih =>
    have hi := amplitudeCovarianceLevels_increment k (stepFieldIncrement k h) (Real.sqrt (2*h 0)) i
    rw [stepFieldIncrement_sq k h hh i,ih] at hi
    linarith

lemma finiteAmplitudeSphereDual_fieldAmplitudes {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    finiteAmplitudeSphereDual w hw hw1 (fieldAmplitudes k h)=
      sInf (finiteSphericalDualValues w h hw hw1)+h (Fin.last k) := by
  unfold finiteAmplitudeSphereDual amplitudeSphereDual
  rw [amplitudeCovarianceLevels_fieldAmplitudes k h hh hh0]

lemma finiteAmplitudeSphereValue_fieldAmplitudes (n k : ℕ) (w h : Fin (k+1) → ℝ)
    (hh0 : 0 ≤ h 0) :
    finiteAmplitudeSphereValue n k w (fieldAmplitudes k h)=finiteSphericalFieldValue n k w h+h (Fin.last k) := by
  unfold finiteAmplitudeSphereValue
  rw [fieldAmplitudes_increment,fieldAmplitudes_last,amplitudeSphereValue_eq]
  have hv : (⟨(Real.sqrt (2*h 0))^2,sq_nonneg _⟩ : ℝ≥0)=Real.toNNReal (2*h 0) := by
    apply NNReal.coe_injective
    change (Real.sqrt (2*h 0))^2=(Real.toNNReal (2*h 0) : ℝ)
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hh0),
      Real.coe_toNNReal _ (mul_nonneg (by norm_num) hh0)]
  rw [hv,finiteSphericalFieldValue,sub_add_cancel]

theorem finiteSphericalFieldValue_compact_uniform {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) {K : Set (Fin (k+1) → ℝ)}
    (hK : IsCompact K) (hfield : ∀ h ∈ K, Monotone h ∧ 0 ≤ h 0) :
    TendstoUniformlyOn (fun n h => finiteSphericalFieldValue n k w h)
      (fun h => sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)) atTop K := by
  have hu := finiteAmplitudeSphereValue_uniform w hw hw1 (hK.image (fieldAmplitudes_continuous k))
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  filter_upwards [hu ε hε] with n hn h hh
  have ht := hn (fieldAmplitudes k h) ⟨h,hh,rfl⟩
  rw [finiteAmplitudeSphereValue_fieldAmplitudes n k w h (hfield h hh).2,
    finiteAmplitudeSphereDual_fieldAmplitudes w h (fun i => (hw i).le) hw1
      (hfield h hh).1 (hfield h hh).2,dist_add_right] at ht
  exact ht

end SphericalPerceptronFreeEnergy

end

end OAI
