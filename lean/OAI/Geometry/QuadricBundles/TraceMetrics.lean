import OAI.Geometry.QuadricBundles.Compactness

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise
noncomputable section

def standardChartIndex (i : StandardChart) : ℕ := (standardChartNat_surj i).choose
lemma standardChartIndex_lt (i : StandardChart) : standardChartIndex i<4 :=
  (standardChartNat_surj i).choose_spec.1
@[simp] lemma standardChartNat_index (i : StandardChart) :
    standardChartNat (standardChartIndex i)=i := (standardChartNat_surj i).choose_spec.2

lemma EqualizerData.twist_coordinateDomain (D : EqualizerData) (m : ℕ) (hm : 0 < m)
    (i : StandardChart) :
    (powerPullbackTwist D.bundle m hm).coordinateDomain (standardChartIndex i)=univ := by
  ext z
  simp [AlgebraicRankTwoBundle.coordinateDomain,powerPullbackTwist,EqualizerData.bundle,
    standardEquationNat,standardChartIndex_lt,baseEval_pullback]

lemma EqualizerData.twist_chart (D : EqualizerData) (m : ℕ) (hm : 0 < m)
    (i : StandardChart) :
    (powerPullbackTwist D.bundle m hm).chart (standardChartIndex i)=i :=
  standardChartNat_index i

lemma EqualizerData.twist_domain (D : EqualizerData) (m : ℕ) (hm : 0 < m)
    (i : StandardChart) :
    (powerPullbackTwist D.bundle m hm).domain (standardChartIndex i)=range (affineQuadric i) := by
  ext x
  simp [AlgebraicRankTwoBundle.domain,powerPullbackTwist,EqualizerData.bundle,
    standardEquationNat,standardChartIndex_lt,principalChart,baseEval_pullback]

lemma SmoothHermitianMetric.chart_psh {V : AlgebraicRankTwoBundle}
    (h : SmoothHermitianMetric V) (hp : h.StrictlyGriffithsPositive) (i : ℕ)
    (hi : V.coordinateDomain i=univ) :
    DiskPshOn univ (fun p : BaseCoordinates × FiberCoordinates ↦
      quadraticValue (h.dualMatrix i p.1) p.2) := by
  have hh := chern_positive_dual_norm_psh isOpen_univ
    (H := h.dualMatrix i) (by simpa only [hi] using (h.smooth i).of_le (by exact WithTop.coe_le_coe.mpr le_top))
    (by simpa only [hi] using h.positive i)
    (by simpa only [hi,mixedHessian,wirtingerDerivative,metricMixedHessian,
      holomorphicMetricDerivative] using hp i)
  rw [univ_prod_univ] at hh
  convert hh using 1
  rfl

lemma continuous_matrix_of_quadratic {X : Type u1} [TopologicalSpace X]
    {n : Type u2} [Fintype n] [DecidableEq n] {H : X → Matrix n n ℂ}
    (hh : ∀ x, (H x).IsHermitian)
    (hc : ∀ v, Continuous (fun x ↦ quadraticValue (H x) v)) : Continuous H := by
  have he : H=fun x ↦ matrixFromQuadratic (quadraticValue (H x)) := by
    funext x; exact (matrixFromQuadratic_value (hh x)).symm
  rw [he]
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  change Continuous (fun x ↦ Complex.equivRealProdCLM.symm
    ((quadraticValue (H x) (Pi.single i 1+Pi.single j 1)-quadraticValue (H x) (Pi.single i 1)-
      quadraticValue (H x) (Pi.single j 1))/2,
     (quadraticValue (H x) (Pi.single i 1)+quadraticValue (H x) (Pi.single j 1)-
       quadraticValue (H x) (Pi.single i 1+Complex.I • Pi.single j 1))/2))
  exact Complex.equivRealProdCLM.symm.continuous.comp
    ((((hc _).sub (hc _) |>.sub (hc _)).div_const 2).prodMk
      (((hc _).add (hc _) |>.sub (hc _)).div_const 2))

section Trace
variable (m : ℕ) [NeZero m]
local instance : Fintype (rootsOfUnity m ℂ) := Fintype.ofFinite _

def matrixRootTrace (H : BaseCoordinates → TwoMatrix) (z : BaseCoordinates) : TwoMatrix :=
  ((m : ℝ)⁻¹ ^ 2) • ∑ ζ : rootsOfUnity m ℂ, ∑ η : rootsOfUnity m ℂ,
    H ((ζ.val : ℂ)*chosenRoot m z.1,(η.val : ℂ)*chosenRoot m z.2)

lemma matrixRootTrace_quadratic (H : BaseCoordinates → TwoMatrix) (z : BaseCoordinates)
    (v : FiberCoordinates) :
    quadraticValue (matrixRootTrace m H z) v =
      doubleRootTrace m (fun p : ℂ × (ℂ × FiberCoordinates) ↦
        quadraticValue (H (p.1,p.2.1)) p.2.2) (z.1,(z.2,v)) := by
  rw [doubleRootTrace_formula]
  change (quadraticValueCLM v) (((m : ℝ)⁻¹ ^ 2) • ∑ ζ : rootsOfUnity m ℂ,
    ∑ η : rootsOfUnity m ℂ, H ((ζ.val : ℂ)*chosenRoot m z.1,(η.val : ℂ)*chosenRoot m z.2)) = _
  simp only [map_smul,map_sum,smul_eq_mul]
  rfl

lemma matrixRootTrace_posDef {H : BaseCoordinates → TwoMatrix}
    (hH : ∀ z, (H z).PosDef) (z : BaseCoordinates) : (matrixRootTrace m H z).PosDef := by
  unfold matrixRootTrace
  apply Matrix.PosDef.smul
  · apply Matrix.posDef_sum (Finset.univ_nonempty)
    intro ζ _
    exact Matrix.posDef_sum (Finset.univ_nonempty) (fun η _ ↦ hH _)
  · exact pow_pos (inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m)))) _

lemma continuous_matrixRootTrace {H : BaseCoordinates → TwoMatrix}
    (hc : Continuous H) (hh : ∀ z, (H z).IsHermitian) :
    Continuous (matrixRootTrace m H) := by
  apply continuous_matrix_of_quadratic
  · intro z
    unfold matrixRootTrace
    exact (IsSelfAdjoint.all ((m : ℝ)⁻¹ ^ 2)).smul
      (isSelfAdjoint_sum _ fun _ _ ↦ isSelfAdjoint_sum _ fun _ _ ↦ hh _)
  · intro v
    have hq : Continuous (fun p : ℂ × (ℂ × FiberCoordinates) ↦
        quadraticValue (H (p.1,p.2.1)) p.2.2) := by
      unfold quadraticValue
      fun_prop
    have htrace := continuousOn_doubleRootTrace m isOpen_univ
      (U := univ) (by simpa only [preimage_univ] using hq.continuousOn)
    have ht : Continuous (fun z : BaseCoordinates ↦
      doubleRootTrace m (fun p : ℂ × (ℂ × FiberCoordinates) ↦
        quadraticValue (H (p.1,p.2.1)) p.2.2) (z.1,(z.2,v))) :=
      continuousOn_univ.mp htrace |>.comp (by fun_prop)
    exact ht.congr (fun z ↦ (matrixRootTrace_quadratic m H z v).symm)

lemma matrixRootTrace_psh {H : BaseCoordinates → TwoMatrix}
    (hc : Continuous H) (hpos : ∀ z, (H z).PosDef)
    (hp : DiskPshOn univ (fun p : BaseCoordinates × FiberCoordinates ↦
      quadraticValue (H p.1) p.2)) :
    DiskPshOn univ (fun p : BaseCoordinates × FiberCoordinates ↦
      quadraticValue (matrixRootTrace m H p.1) p.2) := by
  let F := fun p : ℂ × (ℂ × FiberCoordinates) ↦ quadraticValue (H (p.1,p.2.1)) p.2.2
  have hF : Continuous F := by unfold F quadraticValue; fun_prop
  have hFp : DiskPshOn univ F := hp.comp
    (by fun_prop : DifferentiableOn ℂ (fun p : ℂ × (ℂ × FiberCoordinates) ↦ ((p.1,p.2.1),p.2.2)) univ)
    (fun _ _ ↦ mem_univ _)
  have ht := doubleRootTrace_psh m isOpen_univ (U := univ)
    (by simpa only [preimage_univ] using hF.continuousOn)
    (fun p _ ↦ quadraticValue_nonneg (hpos _).posSemidef _)
    (by simpa only [preimage_univ] using hFp)
  have ha := ht.comp
    (by fun_prop : DifferentiableOn ℂ (fun p : BaseCoordinates × FiberCoordinates ↦ (p.1.1,(p.1.2,p.2))) univ)
    (fun _ _ ↦ mem_univ _)
  convert ha using 1
  funext p
  exact matrixRootTrace_quadratic m H p.1 p.2

lemma matrixRootTrace_anyRoot (H : BaseCoordinates → TwoMatrix)
    (x : BaseCoordinates) :
    matrixRootTrace m H (x.1^m,x.2^m) =
      ((m : ℝ)⁻¹ ^ 2) • ∑ ζ : rootsOfUnity m ℂ, ∑ η : rootsOfUnity m ℂ,
        H ((ζ.val : ℂ)*x.1,(η.val : ℂ)*x.2) := by
  obtain ⟨a,ha⟩ := same_power_orbit m (chosenRoot_pow m (x.1^m))
  obtain ⟨b,hb⟩ := same_power_orbit m (chosenRoot_pow m (x.2^m))
  unfold matrixRootTrace
  rw [ha,hb]
  congr 1
  have he := Equiv.sum_comp ((Equiv.mulRight a).prodCongr (Equiv.mulRight b))
    (fun p : rootsOfUnity m ℂ × rootsOfUnity m ℂ ↦
      H ((p.1.val : ℂ)*x.1,(p.2.val : ℂ)*x.2))
  simp only [Fintype.sum_prod_type] at he
  change (∑ ζ : rootsOfUnity m ℂ, ∑ η : rootsOfUnity m ℂ,
    H ((((ζ*a).val : ℂ))*x.1,(((η*b).val : ℂ))*x.2)) = _ at he
  simpa only [Subgroup.coe_mul,Units.val_mul,mul_assoc] using he

omit [NeZero m] in
lemma root_pow (ζ : rootsOfUnity m ℂ) (x : ℂ) : ((ζ.val : ℂ)*x)^m=x^m := by
  rw [mul_pow,(mem_rootsOfUnity' m ζ.val).mp ζ.property,one_mul]

lemma root_norm (ζ : rootsOfUnity m ℂ) (x : ℂ) : ‖(ζ.val : ℂ)*x‖=‖x‖ := by
  rw [norm_mul,Complex.norm_eq_one_of_mem_rootsOfUnity ζ.property,one_mul]

def rootSwitchEquiv (i j : Fin 2) : Equiv.Perm (rootsOfUnity m ℂ) :=
  if i=j then Equiv.refl _ else Equiv.inv _

omit [NeZero m] in
lemma scalarCoordinateChange_root (i j : Fin 2) (ζ : rootsOfUnity m ℂ) (x : ℂ) :
    scalarCoordinateChange i j ((ζ.val : ℂ)*x) =
      ((rootSwitchEquiv m i j ζ).val : ℂ)*scalarCoordinateChange i j x := by
  by_cases hij : i=j <;>
    simp [scalarCoordinateChange,rootSwitchEquiv,hij,_root_.mul_inv_rev,mul_comm]

omit [NeZero m] in
lemma coordinateChange_pow (i j : StandardChart) (x : BaseCoordinates) :
    coordinateChange i j (x.1^m,x.2^m) =
      ((coordinateChange i j x).1^m,(coordinateChange i j x).2^m) := by
  ext <;> simp only [coordinateChange,scalarCoordinateChange] <;> split_ifs <;> simp

lemma coordinateOverlap_pow (i j : StandardChart) (x : BaseCoordinates) :
    (x.1^m,x.2^m) ∈ coordinateOverlap i j ↔ x ∈ coordinateOverlap i j := by
  simp only [coordinateOverlap_iff,ne_eq,pow_eq_zero_iff (NeZero.ne m)]

lemma polarizationTransition_affine (i j : StandardChart) (x : BaseCoordinates) :
    polarizationTransition i j (affineQuadric i x)=firstFactor i j x*secondFactor i j x := by
  simp only [polarizationTransition,hyperplaneTransition,affineQuadric,coordP1_affine,
    firstFactor,secondFactor,scalarFactor]

lemma polarizationTransition_root_norm (i j : StandardChart) (x : BaseCoordinates)
    (ζ η : rootsOfUnity m ℂ) :
    ‖polarizationTransition i j (affineQuadric i ((ζ.val : ℂ)*x.1,(η.val : ℂ)*x.2))‖ =
      ‖polarizationTransition i j (affineQuadric i x)‖ := by
  simp only [polarizationTransition_affine,norm_mul,firstFactor,secondFactor,scalarFactor]
  split_ifs <;> simp only [root_norm]

lemma matrixRootTrace_change (H : BaseCoordinates → TwoMatrix) (i j : StandardChart)
    (x : BaseCoordinates) :
    matrixRootTrace m H (coordinateChange i j (x.1^m,x.2^m)) =
      ((m : ℝ)⁻¹ ^ 2) • ∑ ζ : rootsOfUnity m ℂ, ∑ η : rootsOfUnity m ℂ,
        H (coordinateChange i j ((ζ.val : ℂ)*x.1,(η.val : ℂ)*x.2)) := by
  rw [coordinateChange_pow,matrixRootTrace_anyRoot]
  congr 1
  have he := Equiv.sum_comp ((rootSwitchEquiv m i.1 j.1).prodCongr
      (rootSwitchEquiv m i.2 j.2))
    (fun p : rootsOfUnity m ℂ × rootsOfUnity m ℂ ↦
      H ((p.1.val : ℂ)*(coordinateChange i j x).1,
        (p.2.val : ℂ)*(coordinateChange i j x).2))
  simpa only [Fintype.sum_prod_type,Equiv.prodCongr_apply,Prod.map,coordinateChange,
    scalarCoordinateChange_root] using he.symm

lemma quadraticValue_congruence (A H : TwoMatrix) (v : FiberCoordinates) :
    quadraticValue (A.conjTranspose*H*A) v=quadraticValue H (A.mulVec v) := by
  simp only [quadraticValue,star_mulVec,dotProduct_mulVec,vecMul_vecMul]

lemma quadraticValue_scalar (H : TwoMatrix) (c : ℂ) (v : FiberCoordinates) :
    quadraticValue H (c • v)=‖c‖^2*quadraticValue H v := by
  simp only [quadraticValue,star_smul,mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    ← mul_assoc,Complex.star_def]
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

lemma quadraticValue_sum_smul (H : rootsOfUnity m ℂ → rootsOfUnity m ℂ → TwoMatrix)
    (v : FiberCoordinates) :
    quadraticValue (((m : ℝ)⁻¹^2) • ∑ ζ, ∑ η, H ζ η) v =
      ((m : ℝ)⁻¹^2)*∑ ζ, ∑ η, quadraticValue (H ζ η) v := by
  change (quadraticValueCLM v) _ = _
  simp only [map_smul,map_sum,smul_eq_mul]
  rfl

omit [NeZero m] in
lemma SmoothHermitianMetric.twist_quadratic_change {D : EqualizerData} {hm : 0 < m}
    (h : SmoothHermitianMetric (powerPullbackTwist D.bundle m hm))
    (i j : StandardChart) {x : BaseCoordinates} (hx : x ∈ coordinateOverlap i j)
    (v : FiberCoordinates) :
    quadraticValue (h.dualMatrix (standardChartIndex i) x) v =
      ‖polarizationTransition i j (affineQuadric i x)‖^2*
        quadraticValue (h.dualMatrix (standardChartIndex j) (coordinateChange i j x))
          ((D.coordinateTransition i j (x.1^m,x.2^m)).transpose.mulVec v) := by
  have hi : affineQuadric i x ∈ (powerPullbackTwist D.bundle m hm).domain (standardChartIndex i) := by
    rw [D.twist_domain]; exact ⟨x,rfl⟩
  have hj : affineQuadric i x ∈ (powerPullbackTwist D.bundle m hm).domain (standardChartIndex j) := by
    rw [D.twist_domain]; exact (affineQuadric_mem_range _ _ _).mpr hx
  have he := h.compatible (standardChartIndex j) (standardChartIndex i) (affineQuadric i x) hj hi
  simp only [D.twist_chart,coordQuadric_affine,coordinateChange_coord] at he
  rw [he,quadraticValue_congruence]
  change quadraticValue (h.dualMatrix (standardChartIndex j) (coordinateChange i j x))
    (((polarizationTransition _ _ _ • D.globalTransition _ _ (powerQuadric m (affineQuadric i x))).transpose).mulVec v)=_
  simp only [EqualizerData.bundle,standardChartNat_index,powerQuadric_affine hm,
    EqualizerData.globalTransition,coordQuadric_affine,Matrix.transpose_smul,smul_mulVec]
  exact quadraticValue_scalar _ _ _

lemma SmoothHermitianMetric.trace_quadratic_change {D : EqualizerData} {hm : 0 < m}
    (h : SmoothHermitianMetric (powerPullbackTwist D.bundle m hm))
    (i j : StandardChart) {x : BaseCoordinates} (hx : x ∈ coordinateOverlap i j)
    (v : FiberCoordinates) :
    quadraticValue (matrixRootTrace m (h.dualMatrix (standardChartIndex i)) (x.1^m,x.2^m)) v =
      ‖polarizationTransition i j (affineQuadric i x)‖^2*
        quadraticValue (matrixRootTrace m (h.dualMatrix (standardChartIndex j))
          (coordinateChange i j (x.1^m,x.2^m)))
          ((D.coordinateTransition i j (x.1^m,x.2^m)).transpose.mulVec v) := by
  rw [matrixRootTrace_anyRoot,matrixRootTrace_change,quadraticValue_sum_smul,
    quadraticValue_sum_smul]
  have hs : ∀ ζ η : rootsOfUnity m ℂ,
      quadraticValue (h.dualMatrix (standardChartIndex i) ((ζ.val : ℂ)*x.1,(η.val : ℂ)*x.2)) v =
        ‖polarizationTransition i j (affineQuadric i x)‖^2*
          quadraticValue (h.dualMatrix (standardChartIndex j)
            (coordinateChange i j ((ζ.val : ℂ)*x.1,(η.val : ℂ)*x.2)))
            ((D.coordinateTransition i j (x.1^m,x.2^m)).transpose.mulVec v) := by
    intro ζ η
    have hr : ((ζ.val : ℂ)*x.1,(η.val : ℂ)*x.2) ∈ coordinateOverlap i j := by
      rw [← coordinateOverlap_pow m]
      simpa only [root_pow] using (coordinateOverlap_pow m i j x).mpr hx
    simpa only [root_pow,polarizationTransition_root_norm] using h.twist_quadratic_change m i j hr v
  simp_rw [hs,← Finset.mul_sum]
  ring

omit [NeZero m] in
lemma polarizationTransition_power (i j : StandardChart) (x : BaseCoordinates) :
    polarizationTransition i j (affineQuadric i (x.1^m,x.2^m)) =
      polarizationTransition i j (affineQuadric i x)^m := by
  simp only [polarizationTransition_affine,firstFactor,secondFactor,scalarFactor]
  split_ifs <;> simp [mul_pow]

def traceScalar (i j : StandardChart) (z : BaseCoordinates) : ℝ :=
  ‖polarizationTransition i j (affineQuadric i z)‖ ^ (2/(m : ℝ))

lemma traceScalar_power (i j : StandardChart) (x : BaseCoordinates) :
    traceScalar m i j (x.1^m,x.2^m) =
      ‖polarizationTransition i j (affineQuadric i x)‖^2 := by
  unfold traceScalar
  rw [polarizationTransition_power,norm_pow]
  have he : (2/(m : ℝ))=(m : ℝ)⁻¹*(2 : ℕ) := by simp only [Nat.cast_ofNat]; ring
  rw [he,Real.rpow_mul_natCast (by positivity),Real.pow_rpow_inv_natCast (norm_nonneg _) (NeZero.ne m)]

lemma SmoothHermitianMetric.trace_change {D : EqualizerData} {hm : 0 < m}
    (h : SmoothHermitianMetric (powerPullbackTwist D.bundle m hm))
    (i j : StandardChart) {z : BaseCoordinates} (hz : z ∈ coordinateOverlap i j)
    (v : FiberCoordinates) :
    quadraticValue (matrixRootTrace m (h.dualMatrix (standardChartIndex i)) z) v =
      traceScalar m i j z *
        quadraticValue (matrixRootTrace m (h.dualMatrix (standardChartIndex j))
          (coordinateChange i j z))
          ((D.coordinateTransition i j z).transpose.mulVec v) := by
  let x : BaseCoordinates := (chosenRoot m z.1,chosenRoot m z.2)
  have hx : (x.1^m,x.2^m)=z := Prod.ext (chosenRoot_pow m _) (chosenRoot_pow m _)
  have hr : x ∈ coordinateOverlap i j := (coordinateOverlap_pow m i j x).mp (hx ▸ hz)
  have he := h.trace_quadratic_change m i j hr v
  rw [← traceScalar_power m i j x,hx] at he
  exact he
end Trace
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise
noncomputable section

structure TwistedPshForm (D : EqualizerData) (m : ℕ) where
  matrix : StandardChart → BaseCoordinates → TwoMatrix
  continuous : ∀ i, Continuous (matrix i)
  positive : ∀ i z, (matrix i z).PosDef
  psh : ∀ i, DiskPshOn univ (fun p : BaseCoordinates × FiberCoordinates ↦
    quadraticValue (matrix i p.1) p.2)
  compatible : ∀ i j z, z ∈ coordinateOverlap i j → ∀ v,
    quadraticValue (matrix i z) v = traceScalar m i j z *
      quadraticValue (matrix j (coordinateChange i j z))
        ((D.coordinateTransition i j z).transpose.mulVec v)

namespace TwistedPshForm
variable {D : EqualizerData} {m : ℕ}
def value (P : TwistedPshForm D m) (i : StandardChart)
    (p : BaseCoordinates × FiberCoordinates) : ℝ := quadraticValue (P.matrix i p.1) p.2

lemma value_continuous (P : TwistedPshForm D m) (i : StandardChart) : Continuous (P.value i) := by
  unfold value quadraticValue
  have hc := P.continuous i
  fun_prop

lemma value_nonneg (P : TwistedPshForm D m) (i : StandardChart)
    (z : BaseCoordinates) (v : FiberCoordinates) : 0 ≤ P.value i (z,v) :=
  quadraticValue_nonneg (P.positive i z).posSemidef v

lemma value_scalar (P : TwistedPshForm D m) (i : StandardChart)
    (z : BaseCoordinates) (c : ℂ) (v : FiberCoordinates) :
    P.value i (z,c • v)=‖c‖^2*P.value i (z,v) := quadraticValue_scalar _ _ _

def rescale (P : TwistedPshForm D m) (c : ℝ) (hc : 0<c) : TwistedPshForm D m where
  matrix i z := c • P.matrix i z
  continuous i := by
    have hi := P.continuous i
    fun_prop
  positive i z := (P.positive i z).smul hc
  psh i := by
    have he (p : BaseCoordinates × FiberCoordinates) :
        quadraticValue (c • P.matrix i p.1) p.2 = c*P.value i p := by
      change (quadraticValueCLM p.2) (c • P.matrix i p.1)=_
      rw [map_smul]; rfl
    simp_rw [he]
    exact (P.psh i).const_mul_of_continuous (P.value_continuous i).continuousOn hc.le
  compatible i j z hz v := by
    have he (H : TwoMatrix) (w : FiberCoordinates) :
        quadraticValue (c • H) w = c*quadraticValue H w := by
      change (quadraticValueCLM w) (c • H)=_
      rw [map_smul]; rfl
    rw [he,he,P.compatible i j z hz v]
    ring

@[simp] lemma value_rescale (P : TwistedPshForm D m) (c : ℝ) (hc : 0<c)
    (i : StandardChart) (p : BaseCoordinates × FiberCoordinates) :
    (P.rescale c hc).value i p=c*P.value i p := by
  change (quadraticValueCLM p.2) (c • P.matrix i p.1)=_
  rw [map_smul]; rfl

lemma quadratic_bound_of_unit_ball {H : TwoMatrix} {C : ℝ}
    (h : ∀ v : FiberCoordinates, ‖v‖≤1 → quadraticValue H v≤C) (v : FiberCoordinates) :
    quadraticValue H v ≤ C*‖v‖^2 := by
  by_cases hv : v=0
  · subst v; simp [quadraticValue]
  have hn : ‖v‖≠0 := norm_ne_zero_iff.mpr hv
  have hn' : (‖v‖ : ℂ)≠0 := by exact_mod_cast hn
  let w := (‖v‖ : ℂ)⁻¹ •v
  have hw : ‖w‖≤1 := by
    dsimp [w]
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ hn]
  have he : (‖v‖:ℂ) • w=v := by
    dsimp [w]
    ext k
    change (‖v‖:ℂ) * ((‖v‖:ℂ)⁻¹ * v k)=v k
    rw [← mul_assoc,mul_inv_cancel₀ hn',one_mul]
  calc
    quadraticValue H v = quadraticValue H ((‖v‖:ℂ) • w) := congrArg _ he.symm
    _ = ‖v‖^2*quadraticValue H w := by
      rw [quadraticValue_scalar,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    _ ≤ ‖v‖^2*C := mul_le_mul_of_nonneg_left (h w hw) (sq_nonneg _)
    _ = C*‖v‖^2 := mul_comm _ _

lemma exists_normalized (P : TwistedPshForm D m) :
    ∃ Q : TwistedPshForm D m,
      (∀ i z, ‖z‖≤1 → ∀ v, Q.value i (z,v)≤‖v‖^2) ∧
      ∃ i z v, ‖z‖≤1 ∧ ‖v‖≤1 ∧ Q.value i (z,v)=1 := by
  let K : Set (StandardChart × (BaseCoordinates × FiberCoordinates)) :=
    univ ×ˢ (closedBall 0 1 ×ˢ closedBall 0 1)
  have hK : IsCompact K := isCompact_univ.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hKn : K.Nonempty := ⟨((0,0),(0,0)),by simp [K]⟩
  have hf : Continuous (fun p : StandardChart × (BaseCoordinates × FiberCoordinates) ↦ P.value p.1 p.2) :=
    continuous_prod_of_discrete_left.mpr P.value_continuous
  obtain ⟨p,hp,hmax⟩ := hK.exists_isMaxOn hKn hf.continuousOn
  let C := P.value p.1 p.2
  let e : FiberCoordinates := Pi.single 0 1
  have he : e≠0 := by intro he; have ht := congrFun he 0; simp [e] at ht
  have hen : ‖e‖≤1 := (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    (fun k ↦ by by_cases hk : k=0 <;> simp [e,hk])
  have h0 : 0<P.value (0,0) (0,e) :=
    (Complex.lt_def.mp ((P.positive (0,0) 0).dotProduct_mulVec_pos he)).1
  have hC : 0<C := h0.trans_le (hmax (show ((0,0),(0,e))∈K by
    exact ⟨mem_univ _,by simp,by simpa only [mem_closedBall,dist_zero_right] using hen⟩))
  have hC' : C≠0 := ne_of_gt hC
  refine ⟨P.rescale C⁻¹ (inv_pos.mpr hC),?_,p.1,p.2.1,p.2.2,?_,?_,?_⟩
  · intro i z hz v
    change quadraticValue ((P.rescale C⁻¹ (inv_pos.mpr hC)).matrix i z) v≤‖v‖^2
    suffices hh : ∀ w : FiberCoordinates, ‖w‖≤1 →
        quadraticValue ((P.rescale C⁻¹ (inv_pos.mpr hC)).matrix i z) w≤1 by
      simpa only [one_mul] using quadratic_bound_of_unit_ball hh v
    intro w hw
    change (P.rescale C⁻¹ (inv_pos.mpr hC)).value i (z,w)≤1
    rw [value_rescale]
    have ht : P.value i (z,w)≤C := hmax (show (i,(z,w))∈K by
      exact ⟨mem_univ _,by simpa using hz,by simpa using hw⟩)
    exact (inv_mul_le_iff₀ hC).mpr (by simpa using ht)
  · simpa only [K,mem_prod,mem_univ,mem_closedBall,dist_zero_right,true_and] using hp.2.1
  · simpa only [K,mem_prod,mem_univ,mem_closedBall,dist_zero_right,true_and] using hp.2.2
  · rw [value_rescale]; exact inv_mul_cancel₀ hC'
end TwistedPshForm

def SmoothHermitianMetric.tracedForm {D : EqualizerData} {m : ℕ} (hm : 0 < m)
    (h : SmoothHermitianMetric (powerPullbackTwist D.bundle m hm)) (hp : h.StrictlyGriffithsPositive) :
    TwistedPshForm D m := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  have hc (i : StandardChart) : Continuous (h.dualMatrix (standardChartIndex i)) :=
    continuousOn_univ.mp (D.twist_coordinateDomain m hm i ▸ (h.smooth _).continuousOn)
  have hpos (i : StandardChart) (z : BaseCoordinates) :
      (h.dualMatrix (standardChartIndex i) z).PosDef := h.positive _ z
        (by rw [D.twist_coordinateDomain]; exact mem_univ _)
  exact {
    matrix i := matrixRootTrace m (h.dualMatrix (standardChartIndex i))
    continuous i := continuous_matrixRootTrace m (hc i) (fun z ↦ (hpos i z).isHermitian)
    positive i z := matrixRootTrace_posDef m (hpos i) z
    psh i := matrixRootTrace_psh m (hc i) (hpos i)
      (h.chart_psh hp _ (D.twist_coordinateDomain m hm i))
    compatible i j z hz v := h.trace_change m i j hz v }
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise
noncomputable section

lemma norm_transpose_mulVec_le (A : TwoMatrix) (v : FiberCoordinates) :
    ‖A.transpose.mulVec v‖ ≤ 2*‖A‖*‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hA (j : Fin 2) : ‖A j i‖≤‖A‖ := (norm_le_pi_norm (A j) i).trans (norm_le_pi_norm A j)
  have hv (j : Fin 2) : ‖v j‖≤‖v‖ := norm_le_pi_norm v j
  simp only [Matrix.mulVec, dotProduct,Fin.sum_univ_two,Matrix.transpose_apply]
  calc
    ‖A 0 i*v 0+A 1 i*v 1‖ ≤ ‖A 0 i*v 0‖+‖A 1 i*v 1‖ := norm_add_le _ _
    _ ≤ ‖A‖*‖v‖+‖A‖*‖v‖ := by
      simp only [norm_mul]
      exact add_le_add (mul_le_mul (hA 0) (hv 0) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (hA 1) (hv 1) (norm_nonneg _) (norm_nonneg _))
    _ = 2*‖A‖*‖v‖ := by ring

lemma traceScalar_le (m : ℕ) (hm : 0 < m) (i j : StandardChart) (z : BaseCoordinates) :
    traceScalar m i j z ≤ 1+‖polarizationTransition i j (affineQuadric i z)‖^2 := by
  unfold traceScalar
  have hm' : (1:ℝ)≤ m := by exact_mod_cast hm
  by_cases hg : 1≤‖polarizationTransition i j (affineQuadric i z)‖
  · have he : 2/(m:ℝ)≤2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    have hh := Real.rpow_le_rpow_of_exponent_le hg he
    rw [Real.rpow_two] at hh
    linarith
  · exact (Real.rpow_le_one (norm_nonneg _) (le_of_not_ge hg) (by positivity)).trans
      (by nlinarith [sq_nonneg ‖polarizationTransition i j (affineQuadric i z)‖])

lemma EqualizerData.coordinateTransition_continuousOn (D : EqualizerData) (i j : StandardChart) :
    ContinuousOn (D.coordinateTransition i j) (coordinateOverlap i j) := by
  apply continuousOn_pi.mpr; intro a
  apply continuousOn_pi.mpr; intro b
  exact ((D.coordinateTransition_regular i j a b).regular.analyticOnNhd
    (coordinateOverlap_open i j)).continuousOn

def switchRegion (R : ℝ) (i j : StandardChart) : Set BaseCoordinates :=
  closedBall 0 R ∩ {z | (i.1=j.1 ∨ 1≤‖z.1‖) ∧ (i.2=j.2 ∨ 1≤‖z.2‖)}

lemma switchRegion_compact (R : ℝ) (i j : StandardChart) : IsCompact (switchRegion R i j) := by
  have hc1 : IsClosed {z : BaseCoordinates | 1≤‖z.1‖} :=
    isClosed_le continuous_const (by fun_prop)
  have hc2 : IsClosed {z : BaseCoordinates | 1≤‖z.2‖} :=
    isClosed_le continuous_const (by fun_prop)
  have h1 : IsClosed {z : BaseCoordinates | i.1=j.1 ∨ 1≤‖z.1‖} := by
    by_cases h : i.1=j.1
    · simp [h]
    · simpa [h] using hc1
  have h2 : IsClosed {z : BaseCoordinates | i.2=j.2 ∨ 1≤‖z.2‖} := by
    by_cases h : i.2=j.2
    · simp [h]
    · simpa [h] using hc2
  exact (isCompact_closedBall _ _).inter_right (h1.inter h2)

lemma switchRegion_subset (R : ℝ) (i j : StandardChart) :
    switchRegion R i j ⊆ coordinateOverlap i j := by
  intro z hz
  apply (coordinateOverlap_iff i j z).mpr
  exact ⟨hz.2.1.imp_right (fun h ↦ norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one h)),
    hz.2.2.imp_right (fun h ↦ norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one h))⟩

lemma exists_unit_coordinateChange (i : StandardChart) (z : BaseCoordinates) (R : ℝ) (hR : ‖z‖≤R) :
    ∃ j, z∈switchRegion R i j ∧ ‖coordinateChange i j z‖≤1 := by
  have hs (a : Fin 2) (w : ℂ) :
      ∃ b : Fin 2, (a=b ∨ 1≤‖w‖) ∧ ‖scalarCoordinateChange a b w‖≤1 := by
    by_cases hw : ‖w‖≤1
    · exact ⟨a,Or.inl rfl,by simpa only [scalarCoordinateChange_self] using hw⟩
    · have ha : a≠1-a := by fin_cases a <;> decide
      refine ⟨1-a,Or.inr (le_of_not_ge hw),?_⟩
      simp only [scalarCoordinateChange,ite_eq_right ha,norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_not_ge hw)
  obtain ⟨j₁,h₁,b₁⟩ := hs i.1 z.1
  obtain ⟨j₂,h₂,b₂⟩ := hs i.2 z.2
  refine ⟨(j₁,j₂),⟨by simpa only [mem_closedBall,dist_zero_right] using hR,h₁,h₂⟩,?_⟩
  exact max_le b₁ b₂

lemma TwistedPshForm.local_bound (D : EqualizerData) (i : StandardChart) (R : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ m, 0 < m → ∀ P : TwistedPshForm D m,
      (∀ j z, ‖z‖≤1 → ∀ v, P.value j (z,v)≤‖v‖^2) →
      ∀ z, ‖z‖≤R → ∀ v, P.value i (z,v)≤C*‖v‖^2 := by
  let F (j : StandardChart) (z : BaseCoordinates) : ℝ :=
    (1+‖polarizationTransition i j (affineQuadric i z)‖^2)*(2*‖D.coordinateTransition i j z‖)^2
  have hc (j : StandardChart) : ContinuousOn (F j) (switchRegion R i j) := by
    have hT := (D.coordinateTransition_continuousOn i j).mono (switchRegion_subset R i j)
    have hg : Continuous (fun z ↦ polarizationTransition i j (affineQuadric i z)) := by
      simp_rw [polarizationTransition_polynomial]
      exact continuousOn_univ.mp (analytic_baseEval _).continuousOn
    exact (continuousOn_const.add (hg.norm.continuousOn.pow 2)).mul
      ((continuousOn_const.mul hT.norm).pow 2)
  choose B hB using fun j ↦ (switchRegion_compact R i j).exists_bound_of_continuousOn (hc j)
  let C : ℝ := ∑ j : StandardChart, |B j|
  have hC : 0≤C := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  refine ⟨C,hC,?_⟩
  intro m hm P hP z hz v
  obtain ⟨j,hzj,hsmall⟩ := exists_unit_coordinateChange i z R hz
  have hcov := P.compatible i j z (switchRegion_subset R i j hzj) v
  have hq := hP j (coordinateChange i j z) hsmall ((D.coordinateTransition i j z).transpose.mulVec v)
  have hs : 0≤traceScalar m i j z := Real.rpow_nonneg (norm_nonneg _) _
  have hbound : F j z≤C := calc
    F j z ≤ ‖F j z‖ := le_abs_self _
    _ ≤ B j := hB j z hzj
    _ ≤ |B j| := le_abs_self _
    _ ≤ C := by
      change |B j|≤ ∑ k : StandardChart, |B k|
      exact Finset.single_le_sum (fun k _ ↦ abs_nonneg (B k)) (Finset.mem_univ j)
  calc
    P.value i (z,v) = traceScalar m i j z *
      P.value j (coordinateChange i j z,(D.coordinateTransition i j z).transpose.mulVec v) := hcov
    _ ≤ traceScalar m i j z * ‖(D.coordinateTransition i j z).transpose.mulVec v‖^2 :=
      mul_le_mul_of_nonneg_left hq hs
    _ ≤ (1+‖polarizationTransition i j (affineQuadric i z)‖^2) *
      (2*‖D.coordinateTransition i j z‖*‖v‖)^2 := by
      apply mul_le_mul (traceScalar_le m hm i j z) _ (sq_nonneg _) (by positivity)
      exact sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr (norm_transpose_mulVec_le _ _)
    _ = F j z*‖v‖^2 := by dsimp [F]; ring
    _ ≤ C*‖v‖^2 := mul_le_mul_of_nonneg_right hbound (sq_nonneg _)
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise
noncomputable section

lemma norm_matrix_of_quadratic_bound {H : TwoMatrix} (hH : H.PosSemidef) {C : ℝ}
    (hC : 0≤C) (hb : ∀ v : FiberCoordinates, quadraticValue H v≤C*‖v‖^2) : ‖H‖≤4*C := by
  have hnon (v : FiberCoordinates) : 0≤quadraticValue H v := quadraticValue_nonneg hH v
  have he (i : Fin 2) : ‖(Pi.single i 1 : FiberCoordinates)‖=1 := by rw [Pi.norm_single,norm_one]
  have hsingle (i : Fin 2) : quadraticValue H (Pi.single i 1)≤C := by simpa only [he,one_pow,mul_one] using hb (Pi.single i 1)
  have hsmall (v : FiberCoordinates) (hv : ‖v‖≤2) : quadraticValue H v≤4*C := by
    have hn := sq_le_sq₀ (norm_nonneg v) (by norm_num : (0:ℝ)≤2) |>.mpr hv
    have hh := mul_le_mul_of_nonneg_left hn hC
    exact (hb v).trans (by nlinarith)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have hsum := hsmall (Pi.single i 1+Pi.single j 1) (by
    calc ‖(Pi.single i 1 : FiberCoordinates)+Pi.single j 1‖ ≤ ‖(Pi.single i 1 : FiberCoordinates)‖+‖(Pi.single j 1 : FiberCoordinates)‖ := norm_add_le _ _
         _ = 2 := by rw [he,he]; norm_num)
  have hisum := hsmall (Pi.single i 1+Complex.I •Pi.single j 1) (by
    calc ‖(Pi.single i 1 : FiberCoordinates)+Complex.I •Pi.single j 1‖ ≤ ‖(Pi.single i 1 : FiberCoordinates)‖+‖Complex.I •(Pi.single j 1 : FiberCoordinates)‖ := norm_add_le _ _
         _ = 2 := by rw [norm_smul,Complex.norm_I,he,he]; norm_num)
  have hid := congrFun (congrFun (matrixFromQuadratic_value hH.isHermitian) i) j
  have hre : |(H i j).re|≤2*C := by
    rw [← hid]
    change |(quadraticValue H (Pi.single i 1+Pi.single j 1)-quadraticValue H (Pi.single i 1)-quadraticValue H (Pi.single j 1))/2|≤2*C
    apply abs_le.mpr
    constructor <;> nlinarith [hnon (Pi.single i 1+Pi.single j 1),hnon (Pi.single i 1),hnon (Pi.single j 1),hsingle i,hsingle j]
  have him : |(H i j).im|≤2*C := by
    rw [← hid]
    change |(quadraticValue H (Pi.single i 1)+quadraticValue H (Pi.single j 1)-quadraticValue H (Pi.single i 1+Complex.I •Pi.single j 1))/2|≤2*C
    apply abs_le.mpr
    constructor <;> nlinarith [hnon (Pi.single i 1+Complex.I •Pi.single j 1),hnon (Pi.single i 1),hnon (Pi.single j 1),hsingle i,hsingle j]
  exact (Complex.norm_le_abs_re_add_abs_im (H i j)).trans (by linarith)

lemma norm_coefficients_of_quadratic_bound {H : TwoMatrix} (hH : H.PosSemidef) {C : ℝ}
    (hC : 0≤C) (hb : ∀ v : FiberCoordinates, quadraticValue H v≤C*‖v‖^2) :
    ‖matrixToCoefficients H‖≤8*C := by
  have hM := norm_matrix_of_quadratic_bound hH hC hb
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤8*C)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    ∑ ij : Fin 2 × Fin 2, ‖matrixToCoefficients H ij‖^2 ≤ ∑ _ij : Fin 2 × Fin 2, (4*C)^2 := by
      apply Finset.sum_le_sum
      intro ij _
      change ‖H ij.1 ij.2‖^2≤(4*C)^2
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      exact (norm_le_pi_norm (H ij.1) ij.2).trans ((norm_le_pi_norm H ij.1).trans hM)
    _ = (8*C)^2 := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul]; norm_num; ring

end
end QuadricCounterexample

end

end OAI
