import OAI.Geometry.QuadricBundles.LineFactors

namespace OAI

namespace QuadricCounterexample
open Set MvPolynomial Matrix
noncomputable section

structure EqualizerData where
  divisor : StandardChart → BasePolynomial
  lift : StandardChart → BasePolynomial
  reduced : ∀ i, Squarefree (divisor i)
  nonzero : ∀ i, divisor i ≠ 0
  divisor_change : ∀ i j z, z ∈ coordinateOverlap i j →
    baseEval (divisor i) z = (firstFactor i j z*secondFactor i j z)^3*
      baseEval (divisor j) (coordinateChange i j z)
  lift_change : ∀ i j z, z ∈ coordinateOverlap i j → baseEval (divisor i) z=0 →
    secondFactor i j z^24*baseEval (lift j) (coordinateChange i j z)=
      baseEval (lift i) z*firstFactor i j z^24
  lift_unit : ∀ i z, baseEval (divisor i) z=0 → baseEval (lift i) z ≠ 0

namespace EqualizerData
variable (D : EqualizerData)

def topFactor (i j : StandardChart) (z : BaseCoordinates) : ℂ := firstFactor i j z^24
def quotientFactor (i j : StandardChart) (z : BaseCoordinates) : ℂ := secondFactor i j z^24
def bottomFactor (i j : StandardChart) (z : BaseCoordinates) : ℂ :=
  (firstFactor i j z)⁻¹^3*secondFactor i j z^21

def numerator (i j : StandardChart) (z : BaseCoordinates) : ℂ :=
  quotientFactor i j z*baseEval (D.lift j) (coordinateChange i j z)-
    baseEval (D.lift i) z*topFactor i j z

lemma topFactor_regular (i j : StandardChart) (U : Set BaseCoordinates) :
    UniformlyRegularOn U (topFactor i j) := (firstFactor_regular i j U).pow 24
lemma quotientFactor_regular (i j : StandardChart) (U : Set BaseCoordinates) :
    UniformlyRegularOn U (quotientFactor i j) := (secondFactor_regular i j U).pow 24
lemma bottomFactor_regular (i j : StandardChart) :
    UniformlyRegularOn (coordinateOverlap i j) (bottomFactor i j) :=
  (((firstFactor_regular i j _).inv fun _ hz ↦ firstFactor_ne_zero hz).pow 3).mul
    ((secondFactor_regular i j _).pow 21)

lemma numerator_regular (i j : StandardChart) :
    UniformlyRegularOn (coordinateOverlap i j) (D.numerator i j) := by
  have h := (uniformlyRegular_polynomial univ (D.lift j)).comp
    (coordinateChange_fst_regular i j) (coordinateChange_snd_regular i j)
    (fun _ _ ↦ mem_univ _)
  exact ((quotientFactor_regular i j _).mul h).sub
    ((uniformlyRegular_polynomial _ (D.lift i)).mul (topFactor_regular i j _))

lemma exists_low (i j : StandardChart) :
    ∃ k : BaseCoordinates → ℂ, UniformlyRegularOn (coordinateOverlap i j) k ∧
      ∀ z ∈ coordinateOverlap i j, baseEval (D.divisor i) z*k z=D.numerator i j z := by
  apply exists_uniformlyRegular_division (overlapPolynomial i j) (D.divisor i) (D.reduced i)
    (D.numerator i j) (D.numerator_regular i j)
  intro z hz hd
  exact sub_eq_zero.mpr (D.lift_change i j z hz hd)

def low (i j : StandardChart) : BaseCoordinates → ℂ := (D.exists_low i j).choose
lemma low_regular (i j : StandardChart) :
    UniformlyRegularOn (coordinateOverlap i j) (D.low i j) := (D.exists_low i j).choose_spec.1
lemma low_spec (i j : StandardChart) {z : BaseCoordinates} (hz : z ∈ coordinateOverlap i j) :
    baseEval (D.divisor i) z*D.low i j z=D.numerator i j z := (D.exists_low i j).choose_spec.2 z hz

lemma divisor_factor (i j : StandardChart) {z : BaseCoordinates}
    (hz : z ∈ coordinateOverlap i j) :
    baseEval (D.divisor i) z*bottomFactor i j z=
      quotientFactor i j z*baseEval (D.divisor j) (coordinateChange i j z) := by
  rw [D.divisor_change i j z hz]
  unfold bottomFactor quotientFactor
  have hn := firstFactor_ne_zero hz
  field_simp

lemma topFactor_mul (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z ∈ coordinateOverlap i j) (hk : z ∈ coordinateOverlap i k) :
    topFactor i j z*topFactor j k (coordinateChange i j z)=topFactor i k z := by
  unfold topFactor
  rw [← mul_pow,firstFactor_mul i j k hj hk]
lemma quotientFactor_mul (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z ∈ coordinateOverlap i j) (hk : z ∈ coordinateOverlap i k) :
    quotientFactor i j z*quotientFactor j k (coordinateChange i j z)=quotientFactor i k z := by
  unfold quotientFactor
  rw [← mul_pow,secondFactor_mul i j k hj hk]
lemma bottomFactor_mul (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z ∈ coordinateOverlap i j) (hk : z ∈ coordinateOverlap i k) :
    bottomFactor i j z*bottomFactor j k (coordinateChange i j z)=bottomFactor i k z := by
  unfold bottomFactor
  rw [← firstFactor_mul i j k hj hk,← secondFactor_mul i j k hj hk]
  simp only [_root_.mul_inv_rev,mul_pow]
  ring

lemma numerator_mul (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z ∈ coordinateOverlap i j) (hk : z ∈ coordinateOverlap i k) :
    baseEval (D.divisor i) z *
      (D.low i j z*topFactor j k (coordinateChange i j z)+
        bottomFactor i j z*D.low j k (coordinateChange i j z))=
      baseEval (D.divisor i) z*D.low i k z := by
  have hjk := coordinateOverlap_third i j k hj hk
  calc
    _ = (baseEval (D.divisor i) z*D.low i j z)*topFactor j k (coordinateChange i j z)+
      (baseEval (D.divisor i) z*bottomFactor i j z)*D.low j k (coordinateChange i j z) := by ring
    _ = D.numerator i j z*topFactor j k (coordinateChange i j z)+
      quotientFactor i j z*(baseEval (D.divisor j) (coordinateChange i j z)*
        D.low j k (coordinateChange i j z)) := by rw [D.low_spec i j hj,D.divisor_factor i j hj]; ring
    _ = D.numerator i j z*topFactor j k (coordinateChange i j z)+
      quotientFactor i j z*D.numerator j k (coordinateChange i j z) := by rw [D.low_spec j k hjk]
    _ = D.numerator i k z := by
      unfold numerator
      rw [coordinateChange_comp i j k hj]
      rw [← topFactor_mul i j k hj hk,← quotientFactor_mul i j k hj hk]
      ring
    _ = _ := (D.low_spec i k hk).symm

lemma low_mul (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z ∈ coordinateOverlap i j) (hk : z ∈ coordinateOverlap i k) :
    D.low i j z*topFactor j k (coordinateChange i j z)+
      bottomFactor i j z*D.low j k (coordinateChange i j z)=D.low i k z := by
  let U := coordinateOverlap i j ∩ coordinateOverlap i k
  have hU : IsOpen U := (coordinateOverlap_open i j).inter (coordinateOverlap_open i k)
  have h0 := (coordinateChange_fst_regular i j).mono (show U ⊆ coordinateOverlap i j from inter_subset_left)
  have h1 := (coordinateChange_snd_regular i j).mono (show U ⊆ coordinateOverlap i j from inter_subset_left)
  have ha := (topFactor_regular j k univ).comp h0 h1 (fun _ _ ↦ mem_univ _)
  have hl := (D.low_regular j k).comp h0 h1 (fun _ hw ↦ coordinateOverlap_third i j k hw.1 hw.2)
  have hf := (((D.low_regular i j).mono inter_subset_left).mul ha).add
    (((bottomFactor_regular i j).mono inter_subset_left).mul hl)
  have hg := (D.low_regular i k).mono (show U ⊆ coordinateOverlap i k from inter_subset_right)
  exact continuous_cancel_polynomial hU (hf.regular.analyticOnNhd hU).continuousOn
    (hg.regular.analyticOnNhd hU).continuousOn (D.nonzero i)
    (fun w hw ↦ D.numerator_mul i j k hw.1 hw.2) ⟨hj,hk⟩

@[simp] lemma topFactor_self (i : StandardChart) (z : BaseCoordinates) : topFactor i i z=1 := by
  simp [topFactor,firstFactor,scalarFactor]
@[simp] lemma quotientFactor_self (i : StandardChart) (z : BaseCoordinates) : quotientFactor i i z=1 := by
  simp [quotientFactor,secondFactor,scalarFactor]
@[simp] lemma bottomFactor_self (i : StandardChart) (z : BaseCoordinates) : bottomFactor i i z=1 := by
  simp [bottomFactor,firstFactor,secondFactor,scalarFactor]
@[simp] lemma coordinateOverlap_self (i : StandardChart) : coordinateOverlap i i=univ := by
  ext z; simp [coordinateOverlap_iff]

lemma low_self (i : StandardChart) (z : BaseCoordinates) : D.low i i z=0 := by
  have hr := D.low_regular i i
  rw [coordinateOverlap_self] at hr
  apply continuous_cancel_polynomial isOpen_univ
    (hr.regular.analyticOnNhd isOpen_univ).continuousOn continuousOn_const (D.nonzero i) _ (mem_univ z)
  intro w _
  have h := D.low_spec i i (z := w) (by simp)
  simpa [numerator] using h

def coordinateTransition (i j : StandardChart) (z : BaseCoordinates) : TwoMatrix :=
  !![topFactor i j z,0;D.low i j z,bottomFactor i j z]

lemma coordinateTransition_self (i : StandardChart) (z : BaseCoordinates) :
    D.coordinateTransition i i z=1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [coordinateTransition,D.low_self]

lemma coordinateTransition_mul (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z ∈ coordinateOverlap i j) (hk : z ∈ coordinateOverlap i k) :
    D.coordinateTransition i j z*D.coordinateTransition j k (coordinateChange i j z)=
      D.coordinateTransition i k z := by
  ext a b; fin_cases a <;> fin_cases b
  · simpa [coordinateTransition,Matrix.mul_apply,Fin.sum_univ_two] using topFactor_mul i j k hj hk
  · simp [coordinateTransition,Matrix.mul_apply,Fin.sum_univ_two]
  · simpa [coordinateTransition,Matrix.mul_apply,Fin.sum_univ_two] using D.low_mul i j k hj hk
  · simpa [coordinateTransition,Matrix.mul_apply,Fin.sum_univ_two] using bottomFactor_mul i j k hj hk

lemma coordinateTransition_regular (i j : StandardChart) (a b : Fin 2) :
    UniformlyRegularOn (coordinateOverlap i j) (fun z ↦ D.coordinateTransition i j z a b) := by
  fin_cases a <;> fin_cases b
  · exact topFactor_regular i j _
  · exact uniformlyRegular_const _ 0
  · exact D.low_regular i j
  · exact bottomFactor_regular i j

end EqualizerData
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix
noncomputable section

def standardChartNat (n : ℕ) : StandardChart :=
  if n=0 then (0,0) else if n=1 then (0,1) else if n=2 then (1,0) else (1,1)
def standardEquationNat (n : ℕ) : BasePolynomial := if n<4 then 1 else 0

lemma standardChartNat_surj (i : StandardChart) : ∃ n : ℕ, n<4 ∧ standardChartNat n=i := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j
  · exact ⟨0,by norm_num,by simp [standardChartNat]⟩
  · exact ⟨1,by norm_num,by simp [standardChartNat]⟩
  · exact ⟨2,by norm_num,by simp [standardChartNat]⟩
  · exact ⟨3,by norm_num,by simp [standardChartNat]⟩

lemma principalChart_one (i : StandardChart) : principalChart i 1=range (affineQuadric i) := by
  ext x; simp [principalChart]

lemma standardCharts_cover (x : QuadricSurface) :
    ∃ n, x ∈ principalChart (standardChartNat n) (standardEquationNat n) := by
  obtain ⟨i,z,hz⟩ := affineQuadric_cover x
  obtain ⟨n,hn,hi⟩ := standardChartNat_surj i
  refine ⟨n,?_⟩
  rw [standardEquationNat,ite_eq_left hn,principalChart_one,hi]
  exact ⟨z,hz⟩

namespace EqualizerData
variable (D : EqualizerData)

def globalTransition (i j : StandardChart) (x : QuadricSurface) : TwoMatrix :=
  D.coordinateTransition i j (coordQuadric i x)

lemma globalTransition_self (i : StandardChart) (x : QuadricSurface) :
    D.globalTransition i i x=1 := D.coordinateTransition_self i (coordQuadric i x)

lemma coord_mem_overlap (i j : StandardChart) {x : QuadricSurface}
    (hi : x ∈ range (affineQuadric i)) (hj : x ∈ range (affineQuadric j)) :
    coordQuadric i x ∈ coordinateOverlap i j := by
  rw [← affineQuadric_mem_range,affineQuadric_coord hi]
  exact hj

lemma globalTransition_mul (i j k : StandardChart) {x : QuadricSurface}
    (hi : x ∈ range (affineQuadric i)) (hj : x ∈ range (affineQuadric j))
    (hk : x ∈ range (affineQuadric k)) :
    D.globalTransition i j x*D.globalTransition j k x=D.globalTransition i k x := by
  have hc : coordinateChange i j (coordQuadric i x)=coordQuadric j x := by
    rw [← coordinateChange_coord,affineQuadric_coord hi]
  simpa only [globalTransition,hc] using
    D.coordinateTransition_mul i j k (coord_mem_overlap i j hi hj) (coord_mem_overlap i k hi hk)

def bundle : AlgebraicRankTwoBundle where
  numberOfCharts := 4
  chart := standardChartNat
  equation := standardEquationNat
  finiteCover := fun i hi ↦ by simp [standardEquationNat,not_lt.mpr hi]
  covers := standardCharts_cover
  transition := fun i j ↦ D.globalTransition (standardChartNat i) (standardChartNat j)
  transition_self := fun i x _ ↦ D.globalTransition_self _ x
  transition_mul := fun i j k x hi hj hk ↦ D.globalTransition_mul _ _ _ hi.1 hj.1 hk.1
  transition_regular := by
    intro i j a b
    have hr := (D.coordinateTransition_regular (standardChartNat i) (standardChartNat j) a b).mono
      (show {z | baseEval (standardEquationNat i) z ≠ 0 ∧
        affineQuadric (standardChartNat i) z ∈ principalChart (standardChartNat j) (standardEquationNat j)}
        ⊆ coordinateOverlap (standardChartNat i) (standardChartNat j) from
          fun z hz ↦ (affineQuadric_mem_range _ _ z).mp hz.2.1)
    simpa only [globalTransition,coordQuadric_affine] using hr.regular

def inclusionMatrix (i : StandardChart) (z : BaseCoordinates) : TwoMatrix :=
  !![1,0;baseEval (D.lift i) z,baseEval (D.divisor i) z]

lemma inclusionMatrix_change (i j : StandardChart) {z : BaseCoordinates}
    (hz : z ∈ coordinateOverlap i j) :
    D.inclusionMatrix i z*D.coordinateTransition i j z=
      !![topFactor i j z,0;0,quotientFactor i j z]*
        D.inclusionMatrix j (coordinateChange i j z) := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [inclusionMatrix,coordinateTransition,Matrix.mul_apply,Fin.sum_univ_two]
  · have h := D.low_spec i j hz
    unfold numerator at h
    linear_combination h
  · exact D.divisor_factor i j hz

lemma second_projection_surjective (i : StandardChart) (z : BaseCoordinates) :
    Function.Surjective (fun v : FiberCoordinates ↦ baseEval (D.lift i) z*v 0+
      baseEval (D.divisor i) z*v 1) := by
  intro w
  by_cases hd : baseEval (D.divisor i) z=0
  · have hh := D.lift_unit i z hd
    refine ⟨![w/baseEval (D.lift i) z,0],?_⟩
    dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    field_simp; simp
  · refine ⟨![0,w/baseEval (D.divisor i) z],?_⟩
    dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    field_simp; simp

lemma inclusionMatrix_det (i : StandardChart) (z : BaseCoordinates) :
    (D.inclusionMatrix i z).det=baseEval (D.divisor i) z := by
  simp [inclusionMatrix,Matrix.det_fin_two]

end EqualizerData
end
end QuadricCounterexample

end OAI
