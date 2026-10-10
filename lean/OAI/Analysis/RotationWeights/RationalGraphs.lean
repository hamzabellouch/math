import OAI.Analysis.RotationWeights.OrbitBounds

namespace OAI

noncomputable section

universe uι uX uY

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CircleModel
open MeasureTheory Set
open scoped ENNReal

def upperExceptional (q : ℕ → ℕ) (r : ℕ → ℝ) : Set CircleX :=
  ⋃ i, {x | 1-r i ≤ Xi q i x}
def lowerExceptional (q : ℕ → ℕ) (r : ℕ → ℝ) : Set CircleX :=
  ⋃ i, {x | Xi q i x < r i}
lemma measurableSet_upperExceptional (q : ℕ → ℕ) (r : ℕ → ℝ) : MeasurableSet (upperExceptional q r) :=
  MeasurableSet.iUnion (fun i => measurableSet_le measurable_const (measurable_Xi q i))
lemma measurableSet_lowerExceptional (q : ℕ → ℕ) (r : ℕ → ℝ) : MeasurableSet (lowerExceptional q r) :=
  MeasurableSet.iUnion (fun i => measurableSet_lt (measurable_Xi q i) measurable_const)
lemma measure_Xi_upper {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (i : ℕ) (r : ℝ) :
    volume {x : CircleX | 1-r ≤ Xi q i x} ≤ ENNReal.ofReal r := by
  change volume ((fun x : CircleX => q i • x) ⁻¹' (repr ⁻¹' Ici (1-r))) ≤ _
  rw [(measurePreserving_XiMap hq i).measure_preimage (measurable_repr measurableSet_Ici).nullMeasurableSet]
  exact measure_repr_upper
lemma measure_Xi_lower {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (i : ℕ) (r : ℝ) :
    volume {x : CircleX | Xi q i x < r} ≤ ENNReal.ofReal r := by
  change volume ((fun x : CircleX => q i • x) ⁻¹' (repr ⁻¹' Iio r)) ≤ _
  rw [(measurePreserving_XiMap hq i).measure_preimage (measurable_repr measurableSet_Iio).nullMeasurableSet]
  exact measure_repr_lower
lemma measure_upperExceptional {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (r : ℕ → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hs : Summable r) :
    volume.real (upperExceptional q r) ≤ ∑' i, r i := by
  have hh : volume (upperExceptional q r) ≤ ENNReal.ofReal (∑' i, r i) := by
    calc
      _ ≤ ∑' i, volume {x : CircleX | 1-r i ≤ Xi q i x} := measure_iUnion_le _
      _ ≤ ∑' i, ENNReal.ofReal (r i) := ENNReal.tsum_le_tsum (fun i => measure_Xi_upper hq i (r i))
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg hr hs).symm
  exact ENNReal.toReal_le_of_le_ofReal (tsum_nonneg hr) hh
lemma measure_lowerExceptional {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (r : ℕ → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hs : Summable r) :
    volume.real (lowerExceptional q r) ≤ ∑' i, r i := by
  have hh : volume (lowerExceptional q r) ≤ ENNReal.ofReal (∑' i, r i) := by
    calc
      _ ≤ ∑' i, volume {x : CircleX | Xi q i x < r i} := measure_iUnion_le _
      _ ≤ ∑' i, ENNReal.ofReal (r i) := ENNReal.tsum_le_tsum (fun i => measure_Xi_lower hq i (r i))
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg hr hs).symm
  exact ENNReal.toReal_le_of_le_ofReal (tsum_nonneg hr) hh
end CircleModel

namespace CircleSampling

section
open CircleModel Set MeasureTheory Filter
open scoped ENNReal Topology BigOperators

lemma graphTolerance_pos (j : ℕ) : 0 < gridTolerance j (scaleState j).1 := by
  unfold gridTolerance
  have := (scaleState j).2.qpos (scaleState j).1.d le_rfl
  positivity
lemma oldGraphBad_bound (j : ℕ) :
    volume.real (oldGraphBad j) ≤ 1/(10*((j:ℝ)+1)^2) := by
  have htol := (graphTolerance_pos j).le
  have hq : 0 < ((scaleState j).1.q (scaleState j).1.d:ℝ) := Nat.cast_pos.mpr ((scaleState j).2.qpos _ le_rfl)
  calc
    _ ≤ ∑ i : Fin (blockEnd j), volume.real {x : CircleX | 1-(modelFrequency i:ℝ)*gridTolerance j (scaleState j).1 ≤ CircleModel.Xi modelFrequency i x} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : Fin (blockEnd j), (modelFrequency i:ℝ)*gridTolerance j (scaleState j).1 := by
      apply Finset.sum_le_sum
      intro i _
      exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (Nat.cast_nonneg _) htol)
        (CircleModel.measure_Xi_upper (fun i => (frequency_pos (i+1)).ne') i _)
    _ ≤ ∑ _i : Fin (blockEnd j), ((scaleState j).1.q (scaleState j).1.d:ℝ)*gridTolerance j (scaleState j).1 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ htol
      have hf := frequency_strictMono.monotone (show i.val+1 ≤ blockEnd j by omega)
      rw [frequency_eq_state (j:=j) le_rfl] at hf
      exact_mod_cast hf
    _ = (blockEnd j:ℝ)*(((scaleState j).1.q (scaleState j).1.d:ℝ)*gridTolerance j (scaleState j).1) := by simp
    _ ≤ _ := by
      unfold gridTolerance blockEnd
      have hd : 0 ≤ ((scaleState j).1.d:ℝ) := Nat.cast_nonneg _
      have hj : 0 < (j:ℝ)+1 := by positivity
      field_simp
      nlinarith [sq_pos_of_pos hj]

lemma measure_iUnion_le_ofReal_tsum {ι : Type uι} {X : Type uX} [Countable ι] [MeasurableSpace X]
    (μ : Measure X) (A : ι → Set X) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hs : Summable b) (h : ∀ i, μ (A i) ≤ ENNReal.ofReal (b i)) :
    μ (⋃ i, A i) ≤ ENNReal.ofReal (∑' i, b i) := by
  calc
    _ ≤ ∑' i, μ (A i) := measure_iUnion_le _
    _ ≤ ∑' i, ENNReal.ofReal (b i) := ENNReal.tsum_le_tsum h
    _ = _ := (ENNReal.ofReal_tsum_of_nonneg hb hs).symm
lemma tailGraphBad_subset (j : ℕ) : tailGraphBad j ⊆
    ⋃ s : ℕ, ⋃ k : Fin (blockLength (j+1+s)),
      {x | 1-sampleBound j*coordinatePhase (blocks.equiv ⟨j+1+s,k⟩) ≤ CircleModel.Xi modelFrequency (blocks.equiv ⟨j+1+s,k⟩) x} := by
  rintro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  obtain ⟨⟨b,k⟩,he⟩ := blocks.equiv.surjective i.val
  have hi' : i.val < blockEnd (b+1) := by
    rw [←he]
    change blockEnd b+k.val < blockEnd b+blockLength b
    exact Nat.add_lt_add_left k.isLt _
  have hb : j+1 ≤ b := by
    by_contra! hb
    have := blockEnd_strictMono.monotone (show b+1 ≤ j+1 by omega)
    omega
  have heq : j+1+(b-(j+1))=b := by omega
  apply mem_iUnion.mpr
  refine ⟨b-(j+1),?_⟩
  rw [heq]
  exact mem_iUnion.mpr ⟨k,by simpa only [he] using hi⟩
lemma tailGraphBad_bound (j : ℕ) :
    volume.real (tailGraphBad j) ≤ 4*sampleBound j/(polynomialWindow (j+1):ℝ) := by
  have hQ := (sampleBound_pos j).le
  have hq : ∀ i, modelFrequency i ≠ 0 := fun i => (frequency_pos (i+1)).ne'
  have hs : Summable (fun s => 2*sampleBound j/(polynomialWindow (j+1+s):ℝ)) := by
    simpa only [div_eq_mul_inv,one_mul] using (summable_window_inverse (j+1)).mul_left (2*sampleBound j)
  have hblock (s : ℕ) : volume (⋃ k : Fin (blockLength (j+1+s)),
      {x : CircleX | 1-sampleBound j*coordinatePhase (blocks.equiv ⟨j+1+s,k⟩) ≤ CircleModel.Xi modelFrequency (blocks.equiv ⟨j+1+s,k⟩) x}) ≤
      ENNReal.ofReal (2*sampleBound j/(polynomialWindow (j+1+s):ℝ)) := by
    apply (measure_iUnion_le_ofReal_tsum volume _ _ (fun k => mul_nonneg (sampleBound_pos j).le (coordinatePhase_pos _).le)
      (Summable.of_finite) (fun k => CircleModel.measure_Xi_upper hq _ _)).trans
    apply ENNReal.ofReal_le_ofReal
    rw [tsum_fintype,←Finset.mul_sum]
    calc
      _ ≤ sampleBound j*(2/(polynomialWindow (j+1+s):ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_phase_block _) (sampleBound_pos j).le
      _ = _ := by ring
  have hm : volume (tailGraphBad j) ≤ ENNReal.ofReal (∑' s, 2*sampleBound j/(polynomialWindow (j+1+s):ℝ)) :=
    (measure_mono (tailGraphBad_subset j)).trans (measure_iUnion_le_ofReal_tsum volume _ _ (fun _ => by positivity) hs hblock)
  apply (ENNReal.toReal_le_of_le_ofReal (tsum_nonneg (fun _ => by positivity)) hm).trans
  simp_rw [div_eq_mul_inv]
  rw [tsum_mul_left]
  calc
    _ ≤ 2*sampleBound j*(2/(polynomialWindow (j+1):ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [one_div] using tsum_window_inverse (j+1)
    _ = _ := by ring

lemma sampleBound_div_window (j : ℕ) : sampleBound j/(polynomialWindow (j+1):ℝ) ≤ 1/(blockLength j:ℝ) := by
  have hm : 0 < (blockLength j:ℝ) := Nat.cast_pos.mpr (scaleStep j).mpos
  have hm1 : 1 ≤ (blockLength j:ℝ) := by exact_mod_cast (scaleStep j).mpos
  have hm20 : (20:ℝ) ≤ blockLength j := by exact_mod_cast (show 20 ≤ blockLength j from (by have := blockLength_ge j; omega))
  have hk : (blockLength j:ℝ)^((3:ℝ)/4*blockLength j) ≤ (polynomialWindow (j+1):ℝ) := Nat.le_ceil _
  calc
    _ ≤ sampleBound j/((blockLength j:ℝ)^((3:ℝ)/4*blockLength j)) :=
      div_le_div_of_nonneg_left (sampleBound_pos j).le (Real.rpow_pos_of_pos hm _) hk
    _ = (blockLength j:ℝ)^(-(1:ℝ)/20*blockLength j) := by
      rw [sampleBound,←Real.rpow_sub hm]
      congr 1
      ring
    _ ≤ (blockLength j:ℝ)^(-(1:ℝ)) := Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
    _ = _ := by rw [Real.rpow_neg_one,one_div]
lemma graphBad_bound (j : ℕ) : volume.real (graphBad j) ≤ 1/(10*((j:ℝ)+1)^2)+4/(blockLength j:ℝ) := by
  calc
    _ ≤ volume.real (oldGraphBad j)+volume.real (tailGraphBad j) := measureReal_union_le _ _
    _ ≤ 1/(10*((j:ℝ)+1)^2)+4*sampleBound j/(polynomialWindow (j+1):ℝ) := add_le_add (oldGraphBad_bound j) (tailGraphBad_bound j)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (sampleBound_div_window j) (by norm_num : (0:ℝ) ≤ 4)
      apply add_le_add le_rfl
      simpa only [div_eq_mul_inv,mul_one,one_mul,mul_assoc] using h
lemma graphBad_tendsto : Tendsto (fun j => volume.real (graphBad j)) atTop (𝓝 0) := by
  have ha : Tendsto (fun j : ℕ => 1/(10*((j:ℝ)+1)^2)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).pow 2
    convert h.div_const 10 using 1
    · ext j
      field_simp
    · norm_num
  have hb : Tendsto (fun j => 4/(blockLength j:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,one_mul,mul_zero,Function.comp_def] using ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp blockLength_strictMono.tendsto_atTop).const_mul 4
  exact squeeze_zero (fun _ => measureReal_nonneg) graphBad_bound (by simpa using ha.add hb)
end
open Set
lemma frequency_dvd_of_le {a b : ℕ} (h : a ≤ b) : frequency a ∣ frequency b := by
  induction b, h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ b h ih => exact ih.trans (frequency_dvd b)
lemma circle_nat_zero (a : ℕ) : ((a:ℝ):CircleX)=0 := by
  rw [←mul_one (a:ℝ),←nsmul_eq_mul,AddCircle.coe_nsmul,AddCircle.coe_period,nsmul_zero]
lemma rational_annihilated {N P : ℕ} (hN : 0 < N) (hNP : N ∣ P) (a : ℕ) :
    P • (((a:ℝ)/(N:ℝ):ℝ):CircleX)=0 := by
  obtain ⟨c,rfl⟩ := hNP
  rw [←AddCircle.coe_nsmul,nsmul_eq_mul]
  have he : ((N*c:ℕ):ℝ)*((a:ℝ)/(N:ℝ))=((c*a:ℕ):ℝ) := by
    push_cast
    field_simp
  rw [he,circle_nat_zero]
lemma rational_grid_lift {N P : ℕ} (hN : 0 < N) (hP : 0 < P) (hNP : N ∣ P)
    (a : Fin N) : ∃ t : Fin P, ((t.val:ℝ)/(P:ℝ):ℝ) = (a.val:ℝ)/(N:ℝ) := by
  obtain ⟨c,rfl⟩ := hNP
  have hc : 0 < c := Nat.pos_of_mul_pos_left hP
  refine ⟨⟨a.val*c,Nat.mul_lt_mul_of_pos_right a.isLt hc⟩,?_⟩
  dsimp
  push_cast
  field_simp
lemma rational_stage_index (D j : ℕ) (a : Fin (frequency (D+1))) (hj : D+1 ≤ blockEnd j) :
    ∃ t : Fin ((scaleState j).1.q (scaleState j).1.d),
      gridPoint (scaleState j).1 t=(((a.val:ℝ)/(frequency (D+1):ℝ):ℝ):CircleX) := by
  have hq : frequency (blockEnd j)=(scaleState j).1.q (scaleState j).1.d := frequency_eq_state (j:=j) le_rfl
  have hdiv := frequency_dvd_of_le hj
  rw [hq] at hdiv
  obtain ⟨t,ht⟩ := rational_grid_lift (frequency_pos (D+1)) ((scaleState j).2.qpos _ le_rfl) hdiv a
  exact ⟨t,congrArg (fun x : ℝ => (x:CircleX)) ht⟩
lemma rational_tail_period (D : ℕ) (a : Fin (frequency (D+1))) (i : ℕ) (hi : D ≤ i) :
    modelFrequency i • (((a.val:ℝ)/(frequency (D+1):ℝ):ℝ):CircleX)=0 :=
  rational_annihilated (frequency_pos (D+1)) (frequency_dvd_of_le (Nat.add_le_add_right hi 1)) _
end CircleSampling

open MeasureTheory Set
namespace CircleSampling

section

lemma integral_norm_le_sqrt {X : Type uX} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ Real.sqrt (∫ x, (f x)^2 ∂μ) := by
  have hh := integral_mul_norm_le_Lp_mul_Lq
    (show Real.HolderConjugate 2 2 by norm_num [Real.holderConjugate_iff])
    (by simpa using hf) (show MemLp (fun _ : X => (1:ℝ)) (ENNReal.ofReal 2) μ from memLp_const 1)
  simpa [Real.rpow_two,Real.sqrt_eq_rpow,Real.norm_eq_abs,sq_abs] using hh

lemma setIntegral_norm_le_sqrt {X : Type uX} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {f : X → ℝ} (hf : MemLp f 2 μ) (A : Set X) (hA : MeasurableSet A) :
    (∫ x in A, ‖f x‖ ∂μ) ≤ Real.sqrt (∫ x, (f x)^2 ∂μ)*Real.sqrt (μ.real A) := by
  have hi := (memLp_const (1:ℝ) (μ:=μ) (p:=2)).indicator hA
  have hh := integral_mul_norm_le_Lp_mul_Lq
    (show Real.HolderConjugate 2 2 by norm_num [Real.holderConjugate_iff])
    (by simpa using hf) (by simpa using hi)
  have he (x : X) : ‖f x‖*‖A.indicator (fun _ => (1:ℝ)) x‖ = A.indicator (fun x => ‖f x‖) x := by
    by_cases hx : x∈A <;> simp [hx]
  have he2 (x : X) : ‖A.indicator (fun _ => (1:ℝ)) x‖^(2:ℝ) = A.indicator (fun _ => (1:ℝ)) x := by
    by_cases hx : x∈A <;> simp [hx]
  have hl : (∫ x, ‖f x‖*‖A.indicator (fun _ => (1:ℝ)) x‖ ∂μ) = ∫ x in A, ‖f x‖ ∂μ := by
    simp_rw [he]
    exact integral_indicator hA
  have hr : (∫ x, ‖A.indicator (fun _ => (1:ℝ)) x‖^(2:ℝ) ∂μ) = μ.real A := by
    simp_rw [he2]
    rw [integral_indicator hA]
    simp
  rw [hl,hr] at hh
  simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs,Real.sqrt_eq_rpow,one_div] using hh

lemma setIntegral_nonneg_le_sqrt {X : Type uX} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {f : X → ℝ} (hf : MemLp f 2 μ) (hn : ∀ x,0≤f x)
    (A : Set X) (hA : MeasurableSet A) :
    (∫ x in A, f x ∂μ) ≤ Real.sqrt (∫ x, (f x)^2 ∂μ)*Real.sqrt (μ.real A) := by
  simpa only [Real.norm_of_nonneg (hn _)] using setIntegral_norm_le_sqrt μ hf A hA

lemma integral_sq_le_of_error {X : Type uX} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf : MemLp f 2 μ) {ε : ℝ}
    (hε : 0≤ε) (he : (∫ x,(f x-1)^2 ∂μ) ≤ ε^2) :
    (∫ x,(f x)^2 ∂μ) ≤ (1+ε)^2 := by
  have hg : MemLp (fun x => f x-1) 2 μ := hf.sub (memLp_const 1)
  have hin : Integrable f μ := hf.integrable (by norm_num)
  have hgs := hg.integrable_sq
  have hL := integral_norm_le_sqrt μ hg
  have herr : (∫ x,f x-1 ∂μ) ≤ ε := by
    calc
      _ ≤ ∫ x,‖f x-1‖ ∂μ := integral_mono (hg.integrable (by norm_num)) (hg.norm.integrable (by norm_num)) (fun _ => le_abs_self _)
      _ ≤ Real.sqrt (∫ x,(f x-1)^2 ∂μ) := hL
      _ ≤ ε := (Real.sqrt_le_left hε).mpr he
  have hid : (∫ x,(f x)^2 ∂μ) = (∫ x,(f x-1)^2 ∂μ)+2*(∫ x,f x-1 ∂μ)+1 := by
    have hp (x : X) : (f x)^2=(f x-1)^2+2*(f x-1)+1 := by ring
    simp_rw [hp]
    have hmid : Integrable (fun x => (f x-1)^2+2*(f x-1)) μ := hgs.add ((hg.integrable (by norm_num)).const_mul 2)
    rw [integral_add hmid (integrable_const 1)]
    rw [integral_add hgs ((hg.integrable (by norm_num)).const_mul 2),integral_const_mul]
    simp
  rw [hid]
  nlinarith

open MeasureTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction
variable {X : Type uX} [MeasurableSpace X]

lemma weightedMeasure_le_sqrt (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : MemLp f 2 μ) (hn : ∀ x, 0 ≤ f x) {C : ℝ}
    (hC : 0 ≤ C) (hb : (∫ x, (f x)^2 ∂μ) ≤ C^2)
    (A : Set X) (hA : MeasurableSet A) :
    (weightedMeasure μ f).real A ≤ C*Real.sqrt (μ.real A) := by
  rw [weightedMeasure_real_apply μ (hf.integrable (by norm_num)) hn hA]
  exact (setIntegral_nonneg_le_sqrt μ hf hn A hA).trans
    (mul_le_mul_of_nonneg_right ((Real.sqrt_le_left hC).mpr hb) (Real.sqrt_nonneg _))

lemma finiteMeasure_sqrt_uc {Y : Type uY} [MeasurableSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] (ν : ℕ → Measure Y) [∀ j, IsFiniteMeasure (ν j)]
    (T : Y → X) (_hT : Measurable T) {C : ℝ} (hC : 0 < C)
    (hb : ∀ j A, MeasurableSet A → (ν j).real (T ⁻¹' A) ≤ C*Real.sqrt (μ.real A)) :
    ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
      ∀ A : Set X, μ A < δ → ∀ j, ν j (T ⁻¹' A) ≤ ε := by
  intro ε hε
  by_cases htop : ε=⊤
  · exact ⟨1,by norm_num,fun _ _ _ => htop.symm ▸ le_top⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε htop
  refine ⟨ENNReal.ofReal ((ε.toReal/C)^2), ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos (div_pos he hC)), ?_⟩
  intro A hA j
  let B := toMeasurable μ A
  have hB : MeasurableSet B := measurableSet_toMeasurable μ A
  have hμ : μ B=μ A := measure_toMeasurable A
  have hBr : μ.real B ≤ (ε.toReal/C)^2 := by
    apply (ENNReal.toReal_le_of_le_ofReal (sq_nonneg _))
    rw [hμ]
    exact hA.le
  apply le_trans (measure_mono (preimage_mono (subset_toMeasurable μ A)))
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) htop).mp
  calc
    _ ≤ C*Real.sqrt (μ.real B) := hb j B hB
    _ ≤ C*(ε.toReal/C) := mul_le_mul_of_nonneg_left ((Real.sqrt_le_left (div_pos he hC).le).mpr hBr) hC.le
    _ = ε.toReal := mul_div_cancel₀ _ hC.ne'

lemma weightedMeasure_l1_test [TopologicalSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf : MemLp f 2 μ) (hm : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (φ : X →ᵇ ℝ) :
    |(∫ x, φ x ∂weightedMeasure μ f)-(∫ x, φ x ∂μ)| ≤
      ‖φ‖*Real.sqrt (∫ x, (f x-1)^2 ∂μ) := by
  have hfi := hf.integrable (by norm_num)
  have hfg : Integrable (fun x => f x*φ x) μ := hfi.mul_bdd φ.continuous.aestronglyMeasurable (ae_of_all _ φ.norm_coe_le_norm)
  have hg : MemLp (fun x => f x-1) 2 μ := hf.sub (memLp_const 1)
  rw [weightedMeasure_integral μ hm hn φ, ←integral_sub hfg (φ.integrable μ)]
  have he : (fun x => f x*φ x-φ x) = (fun x => (f x-1)*φ x) := by ext x; ring
  rw [he]
  calc
    _ ≤ ∫ x, ‖(f x-1)*φ x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖φ‖*‖f x-1‖ ∂μ := by
      apply integral_mono ((hfg.sub (φ.integrable μ)).congr (ae_of_all _ (fun x => by dsimp; ring))).norm
        ((hg.norm.integrable (by norm_num)).const_mul ‖φ‖)
      intro x
      dsimp only
      rw [norm_mul,mul_comm]
      exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm x) (norm_nonneg _)
    _ = ‖φ‖*(∫ x, ‖f x-1‖ ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_norm_le_sqrt μ hg) (norm_nonneg _)

lemma weightedMeasure_test_restrict [TopologicalSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Integrable f μ) (_hm : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (A : Set X) (hA : MeasurableSet A) (φ : X →ᵇ ℝ) :
    |(∫ x, φ x ∂(weightedMeasure μ f).restrict Aᶜ)-(∫ x, φ x ∂weightedMeasure μ f)| ≤
      ‖φ‖*(weightedMeasure μ f).real A := by
  have := weightedMeasure_finite μ hf hn
  have hi : Integrable φ (weightedMeasure μ f) := φ.integrable _
  have he := integral_add_compl hA hi
  have hsub : (∫ x, φ x ∂(weightedMeasure μ f).restrict Aᶜ)-(∫ x, φ x ∂weightedMeasure μ f) =
      -(∫ x in A, φ x ∂weightedMeasure μ f) := by linarith [he]
  rw [hsub,abs_neg]
  calc
    _ ≤ ∫ x in A, ‖φ x‖ ∂weightedMeasure μ f := norm_integral_le_integral_norm _
    _ ≤ ∫ _x in A, ‖φ‖ ∂weightedMeasure μ f := integral_mono hi.restrict.norm (integrable_const _) φ.norm_coe_le_norm
    _ = _ := by simp [mul_comm]
end

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

lemma tendsto_integral_graph_error {X : Type uX} [PseudoMetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : ℕ → FiniteMeasure (X×X)) (T : C(X,X)) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0)) {M : ℝ} (hM : 0≤M)
    (hmass : ∀ j, (ν j : Measure (X×X)).real univ≤M)
    (hsupport : ∀ j, ∀ᵐ z ∂(ν j : Measure (X×X)), dist z.2 (T z.1)≤r j)
    (φ : (X×X) →ᵇ ℝ) :
    Tendsto (fun j => ∫ z, φ z-φ (z.1,T z.1) ∂(ν j : Measure (X×X))) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he : 0<ε/(M+1) := div_pos hε (by linarith)
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous φ.continuous) (ε/(M+1)) he
  obtain ⟨N,hN⟩ := (eventually_atTop.mp (hr.eventually_lt_const hδ))
  refine ⟨N,fun n hn => ?_⟩
  have hb : ∀ᵐ z ∂(ν n : Measure (X×X)), ‖φ z-φ (z.1,T z.1)‖≤ε/(M+1) := by
    filter_upwards [hsupport n] with z hz
    have hd : dist z (z.1,T z.1)<δ := by
      simpa only [Prod.dist_eq,dist_self, max_eq_right (dist_nonneg)] using hz.trans_lt (hN n hn)
    simpa only [dist_eq_norm] using (hclose hd).le
  calc
    _ = ‖∫ z, φ z-φ (z.1,T z.1) ∂(ν n : Measure (X×X))‖ := dist_zero_right _
    _ ≤ (ε/(M+1))*(ν n : Measure (X×X)).real univ := norm_integral_le_of_norm_le_const hb
    _ ≤ (ε/(M+1))*M := mul_le_mul_of_nonneg_left (hmass n) he.le
    _ < ε := by
      have hh : (ε/(M+1))*(M+1)=ε := div_mul_cancel₀ _ (by linarith)
      nlinarith

lemma tendsto_graph_of_fst {X : Type uX} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : ℕ → FiniteMeasure (X×X)) (μ : FiniteMeasure X) (T : C(X,X)) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0)) {M : ℝ} (hM : 0≤M)
    (hmass : ∀ j, (ν j : Measure (X×X)).real univ≤M)
    (hsupport : ∀ j, ∀ᵐ z ∂(ν j : Measure (X×X)), dist z.2 (T z.1)≤r j)
    (hfst : Tendsto (fun j => (ν j).map Prod.fst) atTop (𝓝 μ)) :
    Tendsto ν atTop (𝓝 (μ.map (fun x => (x,T x)))) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro φ
  let ψ : X →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨fun x => φ (x,T x),by fun_prop⟩
  have hf := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hfst ψ
  have hcomp : ∀ j, (∫ x, ψ x ∂((ν j).map Prod.fst : Measure X))=
      ∫ z, φ (z.1,T z.1) ∂(ν j : Measure (X×X)) := by
    intro j
    exact integral_map measurable_fst.aemeasurable ψ.continuous.measurable.aestronglyMeasurable
  have htgt : (∫ z, φ z ∂(μ.map (fun x => (x,T x)) : Measure (X×X)))=∫ x, ψ x ∂(μ : Measure X) := by
    exact integral_map (by fun_prop) φ.continuous.measurable.aestronglyMeasurable
  simp_rw [hcomp] at hf
  rw [htgt]
  have hd := tendsto_integral_graph_error ν T r hr hM hmass hsupport φ
  have hi2 (j : ℕ) : Integrable (fun z : X×X => φ (z.1,T z.1)) (ν j : Measure (X×X)) :=
    (show Continuous (fun z : X×X => φ (z.1,T z.1)) by fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hid (j : ℕ) : (∫ z,φ z-φ (z.1,T z.1) ∂(ν j : Measure (X×X)))+
      (∫ z,φ (z.1,T z.1) ∂(ν j : Measure (X×X)))=∫ z,φ z ∂(ν j : Measure (X×X)) := by
    rw [integral_sub (φ.integrable _) (hi2 j)]
    ring
  simpa only [hid,zero_add] using hd.add hf
end CircleSampling

end

end OAI
