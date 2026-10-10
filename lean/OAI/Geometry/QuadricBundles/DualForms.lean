import OAI.Geometry.QuadricBundles.HomogeneousClassification

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology Metric
noncomputable section

@[simp] lemma affineP1_one (i : Fin 2) : affineP1 i 1 = (1 : ℂ) := by
  fin_cases i <;> simp [affineP1, reciprocalP1]

lemma projective_usc_of_affine_usc {u : ProjectiveLine → ℝ}
    (hu : ∀ i : Fin 2, UpperSemicontinuous (fun z ↦ u (affineP1 i z))) :
    UpperSemicontinuous u := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro t
  have he : u ⁻¹' Set.Iio t = ⋃ i : Fin 2, affineP1 i '' ((u ∘ affineP1 i) ⁻¹' Set.Iio t) := by
    ext x
    simp only [Set.mem_preimage,Set.mem_Iio,Set.mem_iUnion,Set.mem_image]
    constructor
    · intro hx
      obtain ⟨i,z,rfl⟩ := affineP1_cover x
      exact ⟨i,z,hx,rfl⟩
    · rintro ⟨i,z,hz,rfl⟩
      exact hz
  rw [he]
  exact isOpen_iUnion fun i ↦ (affineP1_isOpenEmbedding i).isOpenMap _
    ((hu i).isOpen_preimage _)

theorem projective_subharmonic_const {u : ProjectiveLine → ℝ}
    (hu : ∀ i : Fin 2, DiskSubharmonicOn Set.univ (fun z ↦ u (affineP1 i z))) :
    ∀ x y, u x = u y := by
  have husc : UpperSemicontinuous u := projective_usc_of_affine_usc
    (fun i ↦ upperSemicontinuousOn_univ_iff.mp (hu i).1)
  obtain ⟨p,_,hp⟩ := UpperSemicontinuousOn.exists_isMaxOn (Set.univ_nonempty : (Set.univ : Set ProjectiveLine).Nonempty)
    isCompact_univ (husc.upperSemicontinuousOn Set.univ)
  obtain ⟨i,z,hz⟩ := affineP1_cover p
  have hmax (q : ProjectiveLine) : u q ≤ u p := hp (Set.mem_univ q)
  have hi := (hu i).eq_const_of_max isOpen_univ isPreconnected_univ (Set.mem_univ z)
    (fun y _ ↦ by rw [hz]; exact hmax (affineP1 i y))
  have hone : u (1 : ℂ) = u p := by simpa only [affineP1_one,hz] using hi 1 (Set.mem_univ 1)
  have hall (j : Fin 2) (w : ℂ) : u (affineP1 j w) = u p := by
    have hj := (hu j).eq_const_of_max isOpen_univ isPreconnected_univ (Set.mem_univ (1 : ℂ))
      (fun y _ ↦ by rw [affineP1_one,hone]; exact hmax (affineP1 j y))
    simpa only [affineP1_one,hone] using hj w (Set.mem_univ w)
  intro x y
  obtain ⟨i,z,rfl⟩ := affineP1_cover x
  obtain ⟨j,w,rfl⟩ := affineP1_cover y
  exact (hall i z).trans (hall j w).symm

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric Matrix
noncomputable section
open scoped ComplexOrder

structure EqualizerData.PshDualForm (D : EqualizerData) where
  value : StandardChart → BaseCoordinates × FiberCoordinates → ℝ
  quadratic : ∀ i z, ∃ H : TwoMatrix, H.PosSemidef ∧ ∀ v,
    value i (z,v)=(star v ⬝ᵥ H.mulVec v).re
  psh : ∀ i, DiskPshOn Set.univ (value i)
  compatible : ∀ i j z, z ∈ coordinateOverlap i j → ∀ v,
    value i (z,v)=value j (coordinateChange i j z,(D.coordinateTransition i j z).transpose.mulVec v)

lemma coordinateOverlap_of_affine_eq {i j : StandardChart} {z w : BaseCoordinates}
    (h : affineQuadric i z=affineQuadric j w) : z ∈ coordinateOverlap i j := by
  rw [← affineQuadric_mem_range,h]
  exact ⟨w,rfl⟩

lemma coordinateChange_of_affine_eq {i j : StandardChart} {z w : BaseCoordinates}
    (h : affineQuadric i z=affineQuadric j w) : coordinateChange i j z=w := by
  rw [← coordinateChange_coord,h,coordQuadric_affine]

lemma exists_projective_gluing (f : Fin 2 → ℂ → ℝ)
    (h : ∀ i j z w, affineP1 i z=affineP1 j w → f i z=f j w) :
    ∃ u : ProjectiveLine → ℝ, ∀ i z, u (affineP1 i z)=f i z := by
  choose i z hz using affineP1_cover
  refine ⟨fun x ↦ f (i x) (z x),fun j w ↦ ?_⟩
  exact h _ _ _ _ (hz (affineP1 j w))

namespace EqualizerData.PshDualForm
variable {D : EqualizerData} (Q : D.PshDualForm)

def firstNorm (i : StandardChart) (p : BaseCoordinates × ℂ) : ℝ :=
  Q.value i (p.1,![p.2,0])
def secondNorm (i : StandardChart) (p : BaseCoordinates × ℂ) : ℝ :=
  Q.value i (p.1,![baseEval (D.lift i) p.1*p.2,baseEval (D.divisor i) p.1*p.2])

lemma firstNorm_change (i j : StandardChart) {z : BaseCoordinates}
    (hz : z ∈ coordinateOverlap i j) (c : ℂ) :
    Q.firstNorm i (z,c)=Q.firstNorm j (coordinateChange i j z,topFactor i j z*c) := by
  have h := Q.compatible i j z hz ![c,0]
  simpa [firstNorm,EqualizerData.coordinateTransition,Matrix.transpose_apply,
    Matrix.mulVec, dotProduct,Fin.sum_univ_two] using h

lemma secondNorm_change (i j : StandardChart) {z : BaseCoordinates}
    (hz : z ∈ coordinateOverlap i j) (c : ℂ) :
    Q.secondNorm i (z,c)=Q.secondNorm j
      (coordinateChange i j z,EqualizerData.quotientFactor i j z*c) := by
  have h := Q.compatible i j z hz
    ![baseEval (D.lift i) z*c,baseEval (D.divisor i) z*c]
  unfold secondNorm
  rw [h]
  congr 2
  have h1 := D.low_spec i j hz
  have h2 := D.divisor_factor i j hz
  ext k
  fin_cases k <;> norm_num [EqualizerData.coordinateTransition,Matrix.transpose_apply,
    Matrix.mulVec, dotProduct,Fin.sum_univ_two]
  · unfold EqualizerData.numerator at h1
    linear_combination c*h1
  · linear_combination c*h2

lemma firstNorm_same_ruling (i j k : Fin 2) (z y w c : ℂ)
    (h : affineP1 j y=affineP1 k w) :
    Q.firstNorm (i,j) ((z,y),c)=Q.firstNorm (i,k) ((z,w),c) := by
  have he : affineQuadric (i,j) (z,y)=affineQuadric (i,k) (z,w) := Prod.ext rfl h
  rw [Q.firstNorm_change (i,j) (i,k) (coordinateOverlap_of_affine_eq he),
    coordinateChange_of_affine_eq he]
  simp [EqualizerData.topFactor,firstFactor,scalarFactor]

lemma secondNorm_same_ruling (i j k : Fin 2) (z y w c : ℂ)
    (h : affineP1 j y=affineP1 k w) :
    Q.secondNorm (j,i) ((y,z),c)=Q.secondNorm (k,i) ((w,z),c) := by
  have he : affineQuadric (j,i) (y,z)=affineQuadric (k,i) (w,z) := Prod.ext h rfl
  rw [Q.secondNorm_change (j,i) (k,i) (coordinateOverlap_of_affine_eq he),
    coordinateChange_of_affine_eq he]
  simp [EqualizerData.quotientFactor,secondFactor,scalarFactor]

lemma nonneg (i : StandardChart) (z : BaseCoordinates) (v : FiberCoordinates) :
    0 ≤ Q.value i (z,v) := by
  obtain ⟨H,hH,h⟩ := Q.quadratic i z
  rw [h]
  exact (hH.dotProduct_mulVec_nonneg v).1

lemma scalar (i : StandardChart) (z : BaseCoordinates) (c : ℂ) (v : FiberCoordinates) :
    Q.value i (z,c • v)=‖c‖^2*Q.value i (z,v) := by
  obtain ⟨H,_,h⟩ := Q.quadratic i z
  rw [h,h]
  simp only [star_smul,mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    ← mul_assoc,Complex.star_def]
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

lemma firstNorm_psh (i : StandardChart) : DiskPshOn Set.univ (Q.firstNorm i) := by
  apply (Q.psh i).comp _ (mapsTo_univ _ _)
  apply DifferentiableOn.prodMk (by fun_prop)
  apply differentiableOn_pi.mpr
  intro k
  fin_cases k <;> dsimp <;> fun_prop

lemma secondNorm_psh (i : StandardChart) : DiskPshOn Set.univ (Q.secondNorm i) := by
  have hh : Differentiable ℂ (baseEval (D.lift i)) :=
    fun z ↦ (analytic_baseEval _ z (mem_univ _)).differentiableAt
  have hd : Differentiable ℂ (baseEval (D.divisor i)) :=
    fun z ↦ (analytic_baseEval _ z (mem_univ _)).differentiableAt
  apply (Q.psh i).comp _ (mapsTo_univ _ _)
  apply DifferentiableOn.prodMk (by fun_prop)
  apply differentiableOn_pi.mpr
  intro k
  fin_cases k <;> dsimp <;> fun_prop

lemma firstNorm_ruling_const (i j k : Fin 2) (z y w c : ℂ) :
    Q.firstNorm (i,j) ((z,y),c)=Q.firstNorm (i,k) ((z,w),c) := by
  obtain ⟨u,hu⟩ := exists_projective_gluing (fun j y ↦ Q.firstNorm (i,j) ((z,y),c))
    (fun j k y w h ↦ Q.firstNorm_same_ruling i j k z y w c h)
  have hp : ∀ j : Fin 2, DiskSubharmonicOn Set.univ (fun y ↦ u (affineP1 j y)) := by
    intro j
    simpa only [hu,Function.comp_def] using
      (Q.firstNorm_psh (i,j)).2 Set.univ isOpen_univ (fun y : ℂ ↦ ((z,y),c))
        (by fun_prop) (mapsTo_univ _ _)
  simpa only [hu] using projective_subharmonic_const hp (affineP1 j y) (affineP1 k w)

lemma secondNorm_ruling_const (i j k : Fin 2) (z y w c : ℂ) :
    Q.secondNorm (j,i) ((y,z),c)=Q.secondNorm (k,i) ((w,z),c) := by
  obtain ⟨u,hu⟩ := exists_projective_gluing (fun j y ↦ Q.secondNorm (j,i) ((y,z),c))
    (fun j k y w h ↦ Q.secondNorm_same_ruling i j k z y w c h)
  have hp : ∀ j : Fin 2, DiskSubharmonicOn Set.univ (fun y ↦ u (affineP1 j y)) := by
    intro j
    simpa only [hu,Function.comp_def] using
      (Q.secondNorm_psh (j,i)).2 Set.univ isOpen_univ (fun y : ℂ ↦ ((y,z),c))
        (by fun_prop) (mapsTo_univ _ _)
  simpa only [hu] using projective_subharmonic_const hp (affineP1 j y) (affineP1 k w)

end EqualizerData.PshDualForm

structure PshLine24 where
  value : Fin 2 → ℂ × ℂ → ℝ
  nonneg : ∀ i z c, 0 ≤ value i (z,c)
  scalar : ∀ i z c d, value i (z,c*d)=‖c‖^2*value i (z,d)
  psh : ∀ i, DiskPshOn Set.univ (value i)
  change : ∀ i j z, i=j ∨ z≠0 → ∀ c,
    value i (z,c)=value j (scalarCoordinateChange i j z,scalarFactor i j z^24*c)

def otherIndex (i : Fin 2) : Fin 2 := if i=0 then 1 else 0

def homogeneousCoordinate (i : Fin 2) (v : FiberCoordinates) : ℂ :=
  v (otherIndex i)/v i

lemma homogeneousCoordinate_smul (i : Fin 2) {v : FiberCoordinates} (hv : v i≠0)
    {c : ℂ} (hc : c≠0) : homogeneousCoordinate i (c • v)=homogeneousCoordinate i v := by
  simp only [homogeneousCoordinate,Pi.smul_apply,smul_eq_mul]
  field_simp

lemma homogeneousRepresentative (i : Fin 2) {v : FiberCoordinates} (hv : v i≠0) :
    v=v i • affineRepresentative i (homogeneousCoordinate i v) := by
  fin_cases i <;> dsimp at hv <;> ext k <;> fin_cases k <;>
    simp [affineRepresentative,homogeneousCoordinate,otherIndex,Pi.smul_apply,smul_eq_mul] <;>
    field_simp

lemma homogeneousCoordinate_overlap (i j : Fin 2) {v : FiberCoordinates}
    (_hi : v i≠0) (hj : v j≠0) : i=j ∨ homogeneousCoordinate i v≠0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [homogeneousCoordinate,otherIndex]

lemma homogeneousCoordinate_change (i j : Fin 2) {v : FiberCoordinates}
    (_hi : v i≠0) (_hj : v j≠0) :
    scalarCoordinateChange i j (homogeneousCoordinate i v)=homogeneousCoordinate j v := by
  fin_cases i <;> fin_cases j <;>
    simp [scalarCoordinateChange,homogeneousCoordinate,otherIndex]

lemma homogeneousCoordinate_factor (i j : Fin 2) {v : FiberCoordinates}
    (hi : v i≠0) (_hj : v j≠0) :
    scalarFactor i j (homogeneousCoordinate i v)*v i=v j := by
  fin_cases i <;> fin_cases j <;> dsimp at hi <;>
    simp [scalarFactor,homogeneousCoordinate,otherIndex] <;> field_simp

namespace PshLine24
variable (L : PshLine24)

lemma zero (i : Fin 2) (z : ℂ) : L.value i (z,0)=0 := by
  simpa using L.scalar i z 0 0

lemma coordinate_independent (i j : Fin 2) {v : FiberCoordinates}
    (hi : v i≠0) (hj : v j≠0) :
    L.value i (homogeneousCoordinate i v,(v i)^24)=
      L.value j (homogeneousCoordinate j v,(v j)^24) := by
  rw [L.change _ _ _ (homogeneousCoordinate_overlap i j hi hj),
    homogeneousCoordinate_change i j hi hj,← mul_pow,homogeneousCoordinate_factor i j hi hj]

def homogeneousNorm (v : FiberCoordinates) : ℝ :=
  if v 0=0 then L.value 1 (homogeneousCoordinate 1 v,(v 1)^24)
  else L.value 0 (homogeneousCoordinate 0 v,(v 0)^24)

lemma homogeneousNorm_chart (i : Fin 2) {v : FiberCoordinates} (hi : v i≠0) :
    L.homogeneousNorm v=L.value i (homogeneousCoordinate i v,(v i)^24) := by
  fin_cases i
  · change v 0≠0 at hi
    simp [homogeneousNorm,hi]
  · by_cases h : v 0=0
    · simp [homogeneousNorm,h]
    · simp only [homogeneousNorm,h,↓reduceIte]
      exact L.coordinate_independent 0 1 h hi

@[simp] lemma homogeneousNorm_zero : L.homogeneousNorm 0=0 := by
  simp [homogeneousNorm,L.zero]

lemma homogeneousNorm_nonneg (v : FiberCoordinates) : 0 ≤ L.homogeneousNorm v := by
  unfold homogeneousNorm
  split_ifs <;> exact L.nonneg _ _ _

lemma homogeneousNorm_scalar (c : ℂ) (v : FiberCoordinates) :
    L.homogeneousNorm (c • v)=‖c‖^48*L.homogeneousNorm v := by
  by_cases hc : c=0
  · subst c; simp
  by_cases hv : v=0
  · subst v; simp
  obtain ⟨i,hi⟩ : ∃ i, v i≠0 := by simpa only [not_forall,Pi.zero_apply] using funext_iff.not.mp hv
  have hci : (c • v) i≠0 := mul_ne_zero hc hi
  rw [L.homogeneousNorm_chart i hci,L.homogeneousNorm_chart i hi,
    homogeneousCoordinate_smul i hi hc]
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,L.scalar,norm_pow,← pow_mul]

lemma value_weighted_chart (i : Fin 2) {v : FiberCoordinates} (hi : v i≠0) (t : ℂ) :
    L.value i (homogeneousCoordinate i v,t*(v i)^24)=‖t‖^2*L.homogeneousNorm v := by
  rw [L.scalar,L.homogeneousNorm_chart i hi]

lemma weightedChart_differentiableAt {E : Type u1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → FiberCoordinates} {t : E → ℂ} {x : E} (i : Fin 2)
    (hf : DifferentiableAt ℂ f x) (ht : DifferentiableAt ℂ t x) (hi : f x i≠0) :
    DifferentiableAt ℂ (fun y ↦ (homogeneousCoordinate i (f y),t y*(f y i)^24)) x := by
  change DifferentiableAt ℂ (fun y ↦ (f y (otherIndex i)/f y i,t y*(f y i)^24)) x
  have hfi (j : Fin 2) : DifferentiableAt ℂ (fun y ↦ f y j) x := (differentiableAt_pi.mp hf) j
  simpa only [div_eq_mul_inv,Pi.mul_apply,Pi.inv_apply,Pi.pow_apply] using
    ((hfi (otherIndex i)).mul ((hfi i).inv hi)).prodMk (ht.mul ((hfi i).pow 24))

lemma weightedNorm_usc {E : Type u2} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {f : E → FiberCoordinates} {t : E → ℂ}
    (hf : ∀ x ∈ U, DifferentiableAt ℂ f x) (ht : ∀ x ∈ U, DifferentiableAt ℂ t x)
    (hn : ∀ x ∈ U, f x≠0) :
    UpperSemicontinuousOn (fun x ↦ ‖t x‖^2*L.homogeneousNorm (f x)) U := by
  intro x hx
  obtain ⟨i,hi⟩ : ∃ i, f x i≠0 := by
    simpa only [not_forall,Pi.zero_apply] using funext_iff.not.mp (hn x hx)
  have hc := (weightedChart_differentiableAt i (hf x hx) (ht x hx) hi).continuousAt
  have hu : UpperSemicontinuousAt (fun y ↦ L.value i
      (homogeneousCoordinate i (f y),t y*(f y i)^24)) x :=
    UpperSemicontinuousAt.comp (upperSemicontinuousOn_univ_iff.mp (L.psh i).1 _) hc
  apply (hu.upperSemicontinuousWithinAt U).congr_of_eventuallyEq hx
  have he : ∀ᶠ y in 𝓝 x, f y i≠0 := ((continuous_apply i).continuousAt.comp (hf x hx).continuousAt).eventually_ne hi
  filter_upwards [nhdsWithin_le_nhds he] with y hy
  exact L.value_weighted_chart i hy (t y)

lemma homogeneousNorm_usc : UpperSemicontinuousOn L.homogeneousNorm ({0}ᶜ : Set FiberCoordinates) := by
  have h := L.weightedNorm_usc (E := FiberCoordinates) (U := ({0}ᶜ : Set FiberCoordinates))
    (f := id) (t := fun _ ↦ (1 : ℂ)) (fun _ _ ↦ differentiableAt_id)
    (fun _ _ ↦ differentiableAt_const _) (fun _ hv ↦ hv)
  simpa only [id_eq,norm_one,one_pow,one_mul] using h

lemma homogeneousNorm_disk (U : Set ℂ) (hU : IsOpen U)
    (f : ℂ → FiberCoordinates) (t : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) (ht : AnalyticOnNhd ℂ t U)
    (hn : ∀ z ∈ U, f z≠0) :
    LocalDiskSubmeanOn U (fun z ↦ ‖t z‖^2*L.homogeneousNorm (f z)) := by
  refine ⟨L.weightedNorm_usc (fun z hz ↦ (hf z hz).differentiableAt)
    (fun z hz ↦ (ht z hz).differentiableAt) hn,?_⟩
  intro x hx
  obtain ⟨i,hi⟩ : ∃ i, f x i≠0 := by
    simpa only [not_forall,Pi.zero_apply] using funext_iff.not.mp (hn x hx)
  have he : ∀ᶠ y in 𝓝 x, f y i≠0 := ((continuous_apply i).continuousAt.comp (hf x hx).continuousAt).eventually_ne hi
  obtain ⟨R,hR,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (hU.mem_nhds hx) he)
  have hB : closedBall x (R/2) ⊆ ball x R :=
    closedBall_subset_ball (by linarith)
  have hd : DifferentiableOn ℂ
      (fun z ↦ (homogeneousCoordinate i (f z),t z*(f z i)^24)) (ball x R) := by
    intro z hz
    exact (weightedChart_differentiableAt i
      (hf z (hball (ball_subset_closedBall hz)).1).differentiableAt
      (ht z (hball (ball_subset_closedBall hz)).1).differentiableAt
      (hball (ball_subset_closedBall hz)).2).differentiableWithinAt
  have hs := (L.psh i).2 (ball x R) isOpen_ball _ hd (mapsTo_univ _ _)
  obtain ⟨hint,hmean⟩ := hs.2 x (mem_ball_self hR) (R/2) (by linarith) hB
  have hAE : (fun z ↦ L.value i (homogeneousCoordinate i (f z),t z*(f z i)^24))
      =ᵐ[MeasureTheory.volume.restrict (ball x (R/2))]
      (fun z ↦ ‖t z‖^2*L.homogeneousNorm (f z)) :=
    (MeasureTheory.ae_restrict_mem measurableSet_ball).mono (fun z hz ↦
      L.value_weighted_chart i (hball (ball_subset_closedBall (hB (ball_subset_closedBall hz)))).2 (t z))
  refine ⟨R/2,by linarith,fun z hz ↦ (hball (ball_subset_closedBall (hB hz))).1,
    hint.congr hAE,?_⟩
  change (MeasureTheory.volume (ball x (R/2))).toReal *
    L.value i (homogeneousCoordinate i (f x),t x*(f x i)^24) ≤
      ∫ z in ball x (R/2), L.value i (homogeneousCoordinate i (f z),t z*(f z i)^24) at hmean
  rwa [MeasureTheory.integral_congr_ae hAE,L.value_weighted_chart i hi] at hmean

lemma homogeneousMetric : HomogeneousLocalPshMetric24 L.homogeneousNorm :=
  ⟨L.homogeneousNorm_nonneg,L.homogeneousNorm_scalar,L.homogeneousNorm_usc,L.homogeneousNorm_disk⟩

end PshLine24

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric Matrix
noncomputable section
namespace EqualizerData.PshDualForm
variable {D : EqualizerData} (Q : D.PshDualForm)

lemma firstNorm_scalar (i : StandardChart) (z : BaseCoordinates) (c d : ℂ) :
    Q.firstNorm i (z,c*d)=‖c‖^2*Q.firstNorm i (z,d) := by
  unfold firstNorm
  rw [← Q.scalar]
  congr 2
  ext k
  fin_cases k <;> simp [Pi.smul_apply,smul_eq_mul]

lemma secondNorm_scalar (i : StandardChart) (z : BaseCoordinates) (c d : ℂ) :
    Q.secondNorm i (z,c*d)=‖c‖^2*Q.secondNorm i (z,d) := by
  unfold secondNorm
  rw [← Q.scalar]
  congr 2
  ext k
  fin_cases k <;> simp [Pi.smul_apply,smul_eq_mul,mul_left_comm]

def firstLine : PshLine24 where
  value i p := Q.firstNorm (i,0) ((p.1,0),p.2)
  nonneg i z c := Q.nonneg _ _ _
  scalar i z c d := Q.firstNorm_scalar _ _ c d
  psh i := (Q.firstNorm_psh (i,0)).comp (by fun_prop) (mapsTo_univ _ _)
  change i j z hz c := by
    have ho : (z,0) ∈ coordinateOverlap (i,0) (j,0) :=
      (coordinateOverlap_iff _ _ _).mpr ⟨hz,Or.inl rfl⟩
    simpa [EqualizerData.topFactor,firstFactor,coordinateChange,scalarCoordinateChange] using
      Q.firstNorm_change (i,0) (j,0) ho c

def secondLine : PshLine24 where
  value i p := Q.secondNorm (0,i) ((0,p.1),p.2)
  nonneg i z c := Q.nonneg _ _ _
  scalar i z c d := Q.secondNorm_scalar _ _ c d
  psh i := (Q.secondNorm_psh (0,i)).comp (by fun_prop) (mapsTo_univ _ _)
  change i j z hz c := by
    have ho : (0,z) ∈ coordinateOverlap (0,i) (0,j) :=
      (coordinateOverlap_iff _ _ _).mpr ⟨Or.inl rfl,hz⟩
    simpa [EqualizerData.quotientFactor,secondFactor,coordinateChange,scalarCoordinateChange] using
      Q.secondNorm_change (0,i) (0,j) ho c

lemma firstLine_value (i j : Fin 2) (z w c : ℂ) :
    Q.firstLine.value i (z,c)=Q.firstNorm (i,j) ((z,w),c) :=
  Q.firstNorm_ruling_const i 0 j z 0 w c

lemma secondLine_value (i j : Fin 2) (z w c : ℂ) :
    Q.secondLine.value j (w,c)=Q.secondNorm (i,j) ((z,w),c) :=
  Q.secondNorm_ruling_const j 0 i w 0 z c

end EqualizerData.PshDualForm

lemma matrixBranchDenominator_homogeneous (M : TwoMatrix) (i j : Fin 2)
    {v : FiberCoordinates} (hi : v i≠0) :
    matrixBranchDenominator M (i,j)
      (homogeneousCoordinate i v,homogeneousCoordinate j (M*ᵥv))*v i=(M*ᵥv) j := by
  have h := congrFun (congrArg (M.mulVec) (homogeneousRepresentative i hi)) j
  simpa only [mulVec_smul,Pi.smul_apply,smul_eq_mul,matrixBranchDenominator,
    mulVec,dotProduct,Fin.sum_univ_two,mul_comm,mul_left_comm,mul_assoc,mul_add] using h.symm

lemma matrixGraphValue_homogeneous (M : TwoMatrix) (i j : Fin 2)
    {v : FiberCoordinates} (hi : v i≠0) (hj : (M*ᵥv) j≠0) :
    matrixGraphValue M (i,j)
      (homogeneousCoordinate i v,homogeneousCoordinate j (M*ᵥv))=0 := by
  apply (matrixGraphValue_zero_iff _ _ _).mpr
  have h' := homogeneousRepresentative j hj
  have hd := matrixBranchDenominator_homogeneous M i j hi
  apply (smul_right_injective _ hi)
  dsimp only
  rw [← mulVec_smul,← homogeneousRepresentative i hi,smul_smul,mul_comm,hd,← h']

namespace EqualizerData.PshDualForm
variable {T : GraphScalars} (Q : T.equalizerData.PshDualForm)

lemma graph_identifies_homogeneous (k : Fin 3) {v : FiberCoordinates}
    (hv : v≠0) (hw : T.matrices k*ᵥv≠0) :
    Q.firstLine.homogeneousNorm v=Q.secondLine.homogeneousNorm (T.matrices k*ᵥv) := by
  obtain ⟨i,hi⟩ : ∃ i, v i≠0 := by simpa only [not_forall,Pi.zero_apply] using funext_iff.not.mp hv
  obtain ⟨j,hj⟩ : ∃ j, (T.matrices k*ᵥv) j≠0 := by
    simpa only [not_forall,Pi.zero_apply] using funext_iff.not.mp hw
  let z : BaseCoordinates := (homogeneousCoordinate i v,homogeneousCoordinate j (T.matrices k*ᵥv))
  have hg : matrixGraphValue (T.matrices k) (i,j) z=0 := matrixGraphValue_homogeneous _ _ _ hi hj
  have hd : baseEval (T.divisorPolynomial (i,j)) z=0 := by
    simp only [GraphScalars.divisorPolynomial,baseEval_mul,baseEval_matrixGraphPolynomial]
    fin_cases k
    · exact mul_eq_zero_of_left (mul_eq_zero_of_left hg _) _
    · exact mul_eq_zero_of_left (mul_eq_zero_of_right _ hg) _
    · exact mul_eq_zero_of_right _ hg
  have hb := T.chartLift_branch k (i,j) z hg
  have hn := matrixBranchDenominator_homogeneous (T.matrices k) i j hi
  have hcoef : baseEval (T.chartLift (i,j)) z*((T.matrices k*ᵥv) j)^24=(v i)^24 := by
    rw [← hn,mul_pow,← mul_assoc,hb,one_mul]
  rw [Q.firstLine.homogeneousNorm_chart i hi,Q.secondLine.homogeneousNorm_chart j hj,
    Q.firstLine_value i j _ z.2,Q.secondLine_value i j z.1]
  change Q.value (i,j) (z,![v i^24,0])=
    Q.value (i,j) (z,![baseEval (T.chartLift (i,j)) z*((T.matrices k*ᵥv) j)^24,
      baseEval (T.divisorPolynomial (i,j)) z*((T.matrices k*ᵥv) j)^24])
  rw [hcoef,hd,zero_mul]

end EqualizerData.PshDualForm
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section

@[simp] lemma source_matrices_zero : sourceGraphScalars.matrices 0=1 := rfl
@[simp] lemma source_matrices_one : sourceGraphScalars.matrices 1=source_A := rfl
@[simp] lemma source_matrices_two : sourceGraphScalars.matrices 2=source_B := rfl

namespace EqualizerData.PshDualForm
variable (Q : sourceGraphScalars.equalizerData.PshDualForm)

lemma source_lines_identical (v : FiberCoordinates) :
    Q.firstLine.homogeneousNorm v=Q.secondLine.homogeneousNorm v := by
  by_cases hv : v=0
  · simp [hv]
  simpa using Q.graph_identifies_homogeneous 0 hv (by simpa using hv)

lemma source_first_homogeneous_zero : ∀ v, Q.firstLine.homogeneousNorm v=0 := by
  apply source_invariant_local_homogeneous_metric_zero Q.firstLine.homogeneousMetric
  · intro v
    by_cases hv : v=0
    · simp [hv]
    have hw : sourceGraphScalars.matrices 1*ᵥv≠0 :=
      (smul_ne_zero_iff_ne source_A_gl).mpr hv
    change Q.firstLine.homogeneousNorm (source_A*ᵥv)=Q.firstLine.homogeneousNorm v
    rw [Q.source_lines_identical]
    exact (Q.graph_identifies_homogeneous 1 hv hw).symm
  · intro v
    by_cases hv : v=0
    · simp [hv]
    have hw : sourceGraphScalars.matrices 2*ᵥv≠0 :=
      (smul_ne_zero_iff_ne source_B_gl).mpr hv
    change Q.firstLine.homogeneousNorm (source_B*ᵥv)=Q.firstLine.homogeneousNorm v
    rw [Q.source_lines_identical]
    exact (Q.graph_identifies_homogeneous 2 hv hw).symm

lemma source_second_homogeneous_zero (v : FiberCoordinates) :
    Q.secondLine.homogeneousNorm v=0 := by
  rw [← Q.source_lines_identical,Q.source_first_homogeneous_zero]

end EqualizerData.PshDualForm

@[simp] lemma homogeneousCoordinate_affineRepresentative (i : Fin 2) (z : ℂ) :
    homogeneousCoordinate i (affineRepresentative i z)=z := by
  fin_cases i <;> simp [homogeneousCoordinate,affineRepresentative,otherIndex]

lemma PshLine24.value_zero_of_homogeneous_zero (L : PshLine24)
    (h : ∀ v, L.homogeneousNorm v=0) (i : Fin 2) (z c : ℂ) : L.value i (z,c)=0 := by
  have hv : affineRepresentative i z i≠0 := by simp
  have hval := h (affineRepresentative i z)
  rw [L.homogeneousNorm_chart i hv] at hval
  simp only [homogeneousCoordinate_affineRepresentative,affineRepresentative_index,one_pow] at hval
  have hs := L.scalar i z c 1
  simpa only [mul_one,hval,mul_zero] using hs

namespace EqualizerData.PshDualForm
variable (Q : sourceGraphScalars.equalizerData.PshDualForm)

lemma source_firstNorm_zero (i : StandardChart) (z : BaseCoordinates) (c : ℂ) :
    Q.firstNorm i (z,c)=0 := by
  rw [← Q.firstLine_value i.1 i.2 z.1 z.2 c]
  exact Q.firstLine.value_zero_of_homogeneous_zero Q.source_first_homogeneous_zero _ _ _

lemma source_secondNorm_zero (i : StandardChart) (z : BaseCoordinates) (c : ℂ) :
    Q.secondNorm i (z,c)=0 := by
  rw [← Q.secondLine_value i.1 i.2 z.1 z.2 c]
  exact Q.secondLine.value_zero_of_homogeneous_zero Q.source_second_homogeneous_zero _ _ _

lemma source_value_zero_off_divisor (i : StandardChart) (z : BaseCoordinates)
    (hd : baseEval (sourceGraphScalars.divisorPolynomial i) z≠0) (v : FiberCoordinates) :
    Q.value i (z,v)=0 := by
  obtain ⟨H,hH,h⟩ := Q.quadratic i z
  have hker (u : FiberCoordinates) (hu : Q.value i (z,u)=0) : H*ᵥu=0 := by
    apply hH.dotProduct_mulVec_zero_iff.mp
    rw [h] at hu
    exact Complex.ext hu (hH.dotProduct_mulVec_nonneg u).2.symm
  let d := baseEval (sourceGraphScalars.divisorPolynomial i) z
  let a := baseEval (sourceGraphScalars.chartLift i) z
  have hk1 : H*ᵥ![1,0]=0 := hker _ (Q.source_firstNorm_zero i z 1)
  have hk2 : H*ᵥ![a,d]=0 := hker _ (by
      simpa [secondNorm,GraphScalars.equalizerData,a,d]
        using Q.source_secondNorm_zero i z 1)
  have hv : v=(v 0-a*v 1/d) • ![1,0]+(v 1/d) • ![a,d] := by
    ext k
    fin_cases k
    · simp [smul_eq_mul,Pi.add_apply]
      field_simp [d,hd]
      ring
    · simp [smul_eq_mul,Pi.add_apply]
      field_simp [d,hd]
  have hvH : H*ᵥv=0 := by
    rw [hv,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,hk1,hk2,smul_zero,smul_zero,add_zero]
  rw [h,hvH,dotProduct_zero,Complex.zero_re]

end EqualizerData.PshDualForm

lemma DiskPshOn.eq_zero_of_off_polynomial {q : BaseCoordinates → ℝ}
    (hq : DiskPshOn Set.univ q) (hn : ∀ z, 0 ≤ q z)
    {p : BasePolynomial} (hp : p≠0) (hz : ∀ z, baseEval p z≠0 → q z=0) : ∀ z, q z=0 := by
  obtain ⟨w,hw⟩ := (dense_polynomial_nonzero hp).nonempty
  intro z
  let γ : ℂ → BaseCoordinates := fun t ↦ z+t • (w-z)
  have hγ : AnalyticOnNhd ℂ γ Set.univ := by
    intro t _
    dsimp [γ]
    fun_prop
  have hr : AnalyticOnNhd ℂ (baseEval p ∘ γ) Set.univ :=
    (analytic_baseEval p).comp hγ (mapsTo_univ _ _)
  have he : ¬ Set.EqOn (baseEval p ∘ γ) 0 Set.univ := by
    intro he
    have h := he (x := (1 : ℂ)) (mem_univ _)
    have hγ1 : γ 1=w := by simp [γ]
    exact hw (by simpa only [Function.comp_apply,hγ1,Pi.zero_apply] using h)
  have hne := (hr.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left he
  have hae : ∀ᵐ t ∂volume, (baseEval p ∘ γ) t≠0 := by
    have h := ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℂ)) MeasurableSet.univ hne
    change ∀ᵐ t ∂volume.restrict (univ : Set ℂ), (baseEval p ∘ γ) t≠0 at h
    simpa only [Measure.restrict_univ] using h
  have hqae : (q ∘ γ)=ᵐ[volume] (fun _ ↦ 0) := hae.mono fun t ht ↦ hz (γ t) ht
  have hs := hq.2 Set.univ isOpen_univ γ hγ.differentiableOn (mapsTo_univ _ _)
  have hm := (hs.2 0 (mem_univ _) 1 (by norm_num) (subset_univ _)).2
  rw [integral_congr_ae (ae_restrict_of_ae hqae),integral_zero] at hm
  have hvol : 0 < (volume (ball (0 : ℂ) 1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume (0 : ℂ) (by norm_num : (0 : ℝ) < 1)))
      (measure_ne_top_of_subset ball_subset_closedBall (isCompact_closedBall (0 : ℂ) 1).measure_ne_top)
  have hγ0 : γ 0=z := by simp [γ]
  simp only [Function.comp_apply,hγ0] at hm
  exact le_antisymm (by nlinarith [hn z]) (hn z)

namespace EqualizerData.PshDualForm
variable (Q : sourceGraphScalars.equalizerData.PshDualForm)

theorem source_value_zero (i : StandardChart) (z : BaseCoordinates) (v : FiberCoordinates) :
    Q.value i (z,v)=0 := by
  have hp : DiskPshOn Set.univ (fun w ↦ Q.value i (w,v)) :=
    (Q.psh i).comp (by fun_prop) (mapsTo_univ _ _)
  exact hp.eq_zero_of_off_polynomial (fun w ↦ Q.nonneg i w v)
    (sourceGraphScalars.divisorPolynomial_nonzero i)
    (fun w hw ↦ Q.source_value_zero_off_divisor i w hw v) z

end EqualizerData.PshDualForm
end
end QuadricCounterexample

end

end OAI
