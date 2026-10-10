import OAI.Analysis.NumericalRange.OptimalExtremal

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_191 u_192 u_193 u_194 u_195 u_196 u_197 u_198 u_199 u_200 u_201 u_202 u_203 u_204 u_205 u_206 u_207 u_208 u_209 u_210 u_211 u_212 u_213 u_214

open MeasureTheory
open scoped ENNReal

section
variable {T : Type u_193} {H : Type u_194} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def dilationField (S : C(T, H →L[ℂ] H)) (x : H) : C(T,H) :=
  ⟨fun t => S t x, by fun_prop⟩

def dilationLM (S : C(T, H →L[ℂ] H)) : H →ₗ[ℂ] Lp H 2 μ where
  toFun x := ContinuousMap.toLp 2 μ ℂ (dilationField S x)
  map_add' x y := by
    rw [← map_add]; congr 1
    ext t
    exact map_add (S t) x y
  map_smul' c x := by
    rw [RingHom.id_apply, ← map_smul]; congr 1
    ext t
    exact map_smul (S t) c x

lemma dilationLM_coe
    {T : Type u_193} {H : Type u_194} [TopologicalSpace T] [CompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] {μ : MeasureTheory.Measure T}
    [MeasureTheory.IsFiniteMeasure μ] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : C(T,H →L[ℂ] H)) (x : H) :
    dilationLM (μ := μ) S x =ᵐ[μ] fun t => S t x :=
  ContinuousMap.coeFn_toLp (μ := μ) (dilationField S x)

lemma dilationLM_inner (S : C(T,H →L[ℂ] H)) (x y : H) :
    inner ℂ (dilationLM (μ := μ) S x) (dilationLM (μ := μ) S y) =
      inner ℂ x ((∫ t, (S t).adjoint * S t ∂μ) y) := by
  rw [L2.inner_def]
  have hcont : Continuous (fun t => (S t).adjoint * S t) := by fun_prop
  have hi : Integrable (fun t => (S t).adjoint * S t) μ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ t, inner ℂ (S t x) (S t y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [dilationLM_coe (μ := μ) S x, dilationLM_coe (μ := μ) S y]
        with t hx hy
      rw [hx,hy]
    _ = ∫ t, inner ℂ x (((S t).adjoint * S t) y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right]
    _ = _ := by
      have hiy : Integrable (fun t => ((S t).adjoint * S t) y) μ :=
        (ContinuousLinearMap.apply ℂ H y).integrable_comp hi
      rw [integral_inner hiy, ← ContinuousLinearMap.integral_apply hi]

def positiveDilation (S : C(T,H →L[ℂ] H))
    (hmass : (∫ t, (S t).adjoint * S t ∂μ) = 1) : H →ₗᵢ[ℂ] Lp H 2 μ :=
  (dilationLM S).isometryOfInner fun x y => by
    rw [dilationLM_inner (μ := μ) S x y, hmass]
    rfl

section MatrixDensity
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker
variable {n : Type u_195} {m : Type u_196} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def baseAmplification : Matrix n n ℂ →L[ℂ]
    (EuclideanSpace ℂ (n × m) →L[ℂ] EuclideanSpace ℂ (n × m)) :=
  (show Matrix n n ℂ →ₗ[ℂ]
    (EuclideanSpace ℂ (n × m) →L[ℂ] EuclideanSpace ℂ (n × m)) from
    { toFun := fun A => Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix m m ℂ))
      map_add' := fun A B => by simp [Matrix.add_kronecker]
      map_smul' := fun c A => by simp [Matrix.smul_kronecker] }).toContinuousLinearMap

lemma baseAmplification_mul (A B : Matrix n n ℂ) :
    baseAmplification (m := m) (A*B) = baseAmplification A * baseAmplification B := by
  change Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) ((A*B) ⊗ₖ (1 : Matrix m m ℂ)) =
    Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix m m ℂ)) * Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (B ⊗ₖ 1)
  rw [← map_mul, ← Matrix.mul_kronecker_mul, one_mul]

lemma baseAmplification_star (A : Matrix n n ℂ) :
    baseAmplification (m := m) Aᴴ = (baseAmplification A).adjoint := by
  change Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (Aᴴ ⊗ₖ (1 : Matrix m m ℂ)) =
    star (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix m m ℂ)))
  have he := map_star (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ))
    (A ⊗ₖ (1 : Matrix m m ℂ))
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one] using he

@[simp] lemma baseAmplification_one :
    baseAmplification (n := n) (m := m) (1 : Matrix n n ℂ) = 1 := by
  change Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) ((1 : Matrix n n ℂ) ⊗ₖ (1 : Matrix m m ℂ)) = 1
  rw [Matrix.one_kronecker_one, map_one]

def densityRootField (L : C(T,Matrix n n ℂ)) (hL : ∀ t, 0 ≤ L t) :
    C(T,EuclideanSpace ℂ (n × m) →L[ℂ] EuclideanSpace ℂ (n × m)) :=
  ⟨fun t => baseAmplification (CFC.sqrt (L t)),
    baseAmplification.continuous.comp
      (CFC.continuousOn_sqrt.comp_continuous L.continuous hL)⟩

lemma densityRootField_sq
    {T : Type u_193} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T] {n : Type u_195} {m : Type u_196} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (L : C(T,Matrix n n ℂ)) (hL : ∀ t, 0 ≤ L t) (t : T) :
    (densityRootField (m := m) L hL t).adjoint * densityRootField L hL t =
      baseAmplification (L t) := by
  change (baseAmplification (n := n) (m := m) (CFC.sqrt (L t))).adjoint *
    baseAmplification (n := n) (m := m) (CFC.sqrt (L t)) = baseAmplification (n := n) (m := m) (L t)
  rw [← baseAmplification_star, ← baseAmplification_mul]
  have hs : (CFC.sqrt (L t))ᴴ = CFC.sqrt (L t) :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (L t))).isHermitian.eq
  rw [hs, CFC.sqrt_mul_sqrt_self (L t) (hL t)]

lemma densityRootField_mass (L : C(T,Matrix n n ℂ)) (hL : ∀ t, 0 ≤ L t)
    (hmass : (∫ t, L t ∂μ) = 1) :
    (∫ t, (densityRootField (m := m) L hL t).adjoint * densityRootField L hL t ∂μ) = 1 := by
  simp_rw [densityRootField_sq]
  have hi : Integrable (fun t => L t) μ :=
    L.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have : CompleteSpace (EuclideanSpace ℂ (n × m)) := inferInstance
  have : CompleteSpace (EuclideanSpace ℂ (n × m) →L[ℂ] EuclideanSpace ℂ (n × m)) :=
    ContinuousLinearMap.instCompleteSpace
  rw [(baseAmplification (n := n) (m := m)).integral_comp_comm hi,
    hmass, baseAmplification_one]

def matrixPositiveDilation (L : C(T,Matrix n n ℂ)) (hL : ∀ t, 0 ≤ L t)
    (hmass : (∫ t, L t ∂μ) = 1) :
    EuclideanSpace ℂ (n × m) →ₗᵢ[ℂ] Lp (EuclideanSpace ℂ (n × m)) 2 μ :=
  positiveDilation (densityRootField L hL) (densityRootField_mass L hL hmass)

end MatrixDensity

theorem positiveDilation_compression (S B : C(T,H →L[ℂ] H))
    (hmass : (∫ t, (S t).adjoint * S t ∂μ) = 1) (hB : ∀ t, ‖B t‖ ≤ 1) :
    let V := (positiveDilation S hmass).toContinuousLinearMap
    V.adjoint.comp ((pointwiseL2L (fun t => B t) B.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hB)).comp V) =
        ∫ t, (S t).adjoint * B t * S t ∂μ := by
  dsimp only
  let V := (positiveDilation S hmass).toContinuousLinearMap
  let M := pointwiseL2L (μ := μ) (fun t => B t) B.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hB)
  have hi : Integrable (fun t => (S t).adjoint * B t * S t) μ :=
    (show Continuous (fun t => (S t).adjoint * B t * S t) by fun_prop
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x (V.adjoint (M (V y))) =
    inner ℂ x ((∫ t, (S t).adjoint * B t * S t ∂μ) y)
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  calc
    _ = ∫ t, inner ℂ (S t x) (B t (S t y)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [dilationLM_coe (μ := μ) S x, dilationLM_coe (μ := μ) S y,
        pointwiseL2_ae (fun t => B t) B.continuous.aestronglyMeasurable
          (Filter.Eventually.of_forall hB) (V y)] with t hx hy hM
      change inner ℂ ((dilationLM S x) t) ((pointwiseL2 (fun t => B t) B.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hB) (V y)) t) = _
      rw [hx, hM]
      change inner ℂ (S t x) (B t ((dilationLM S y) t)) = _
      rw [hy]
    _ = ∫ t, inner ℂ x (((S t).adjoint * B t * S t) y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right]
    _ = _ := by
      have hiy : Integrable (fun t => ((S t).adjoint * B t * S t) y) μ :=
        (ContinuousLinearMap.apply ℂ H y).integrable_comp hi
      rw [integral_inner hiy, ← ContinuousLinearMap.integral_apply hi]

end

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker

section
variable {n : Type u_197} {m : Type u_198} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def coefficientMatrixHom : Matrix m m ℂ →⋆ₐ[ℂ] Matrix (n × m) (n × m) ℂ where
  toFun B := (1 : Matrix n n ℂ) ⊗ₖ B
  map_zero' := Matrix.kronecker_zero _
  map_add' A B := Matrix.kronecker_add _ A B
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, one_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul,
      Matrix.one_kronecker_one]
  map_star' B := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one]

lemma coefficientMatrixHom_norm (B : Matrix m m ℂ) :
    ‖coefficientMatrixHom (n := n) B‖ ≤ ‖B‖ :=
  NonUnitalStarAlgHom.norm_apply_le (coefficientMatrixHom (n := n)) B

def coefficientAmplification : Matrix m m ℂ →L[ℂ]
    (EuclideanSpace ℂ (n × m) →L[ℂ] EuclideanSpace ℂ (n × m)) :=
  ((Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.comp
    coefficientMatrixHom.toAlgHom.toLinearMap).toContinuousLinearMap

lemma coefficientAmplification_norm (B : Matrix m m ℂ) :
    ‖coefficientAmplification (n := n) B‖ ≤ ‖B‖ :=
  coefficientMatrixHom_norm B

lemma coefficientAmplification_star (B : Matrix m m ℂ) :
    coefficientAmplification (n := n) Bᴴ = (coefficientAmplification B).adjoint := by
  change Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) ((1 : Matrix n n ℂ) ⊗ₖ Bᴴ) =
    star (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) ((1 : Matrix n n ℂ) ⊗ₖ B))
  have he := map_star (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ))
    ((1 : Matrix n n ℂ) ⊗ₖ B)
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one] using he

end

section
open MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker
variable {T : Type u_199} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]
  {n : Type u_200} {m : Type u_201} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def coefficientMultiplierField (F : C(T,Matrix m m ℂ)) :
    C(T,EuclideanSpace ℂ (n × m) →L[ℂ] EuclideanSpace ℂ (n × m)) :=
  ⟨fun t => coefficientAmplification (F t), coefficientAmplification.continuous.comp F.continuous⟩

lemma coefficientMultiplierField_norm
    {T : Type u_199} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T] {n : Type u_200} {m : Type u_201} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (F : C(T,Matrix m m ℂ)) (hF : ∀ t, ‖F t‖ ≤ 1)
    (t : T) : ‖coefficientMultiplierField (n := n) F t‖ ≤ 1 :=
  (coefficientAmplification_norm (n := n) (F t)).trans (hF t)

lemma densityRootField_compression
    {T : Type u_199} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T] {n : Type u_200} {m : Type u_201} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (L : C(T,Matrix n n ℂ)) (hL : ∀ t, 0 ≤ L t)
    (F : C(T,Matrix m m ℂ)) (t : T) :
    (densityRootField (m := m) L hL t).adjoint * coefficientMultiplierField F t *
      densityRootField L hL t =
        Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (L t ⊗ₖ F t) := by
  change (baseAmplification (n := n) (m := m) (CFC.sqrt (L t))).adjoint *
    coefficientAmplification (n := n) (F t) *
    baseAmplification (n := n) (m := m) (CFC.sqrt (L t)) = _
  rw [← baseAmplification_star]
  change Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) ((CFC.sqrt (L t))ᴴ ⊗ₖ (1 : Matrix m m ℂ)) *
    Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) ((1 : Matrix n n ℂ) ⊗ₖ F t) *
    Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (CFC.sqrt (L t) ⊗ₖ (1 : Matrix m m ℂ)) = _
  rw [← map_mul, ← map_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one, Matrix.one_mul]
  have hs : (CFC.sqrt (L t))ᴴ = CFC.sqrt (L t) :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (L t))).isHermitian.eq
  rw [hs, CFC.sqrt_mul_sqrt_self (L t) (hL t)]

theorem matrixPositiveDilation_compression (L : C(T,Matrix n n ℂ))
    (hL : ∀ t, 0 ≤ L t) (hmass : (∫ t, L t ∂μ) = 1)
    (F : C(T,Matrix m m ℂ)) (hF : ∀ t, ‖F t‖ ≤ 1) :
    let V := (matrixPositiveDilation (m := m) L hL hmass).toContinuousLinearMap
    let B := coefficientMultiplierField (n := n) F
    V.adjoint.comp ((pointwiseL2L (fun t => B t) B.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (coefficientMultiplierField_norm F hF))).comp V) =
        ∫ t, Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (L t ⊗ₖ F t) ∂μ := by
  have he := positiveDilation_compression (μ := μ) (densityRootField (m := m) L hL)
    (coefficientMultiplierField (n := n) F) (densityRootField_mass L hL hmass)
    (coefficientMultiplierField_norm F hF)
  simpa only [densityRootField_compression, matrixPositiveDilation] using he

end

section
variable {H : Type u_202} {K : Type u_203} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem isometric_multiplier_saturation (V : H →ₗᵢ[ℂ] K) (M : K →L[ℂ] K)
    (hM : ‖M‖ ≤ 1) {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (he : V.toContinuousLinearMap.adjoint (M (V x)) = y) :
    M (V x) = V y ∧ M.adjoint (V y) = V x := by
  have hMy : M (V x) = V y := by
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℂ)
    · calc ‖M (V x)‖ ≤ ‖M‖ * ‖V x‖ := M.le_opNorm _
           _ ≤ ‖V y‖ := by rw [V.norm_map, V.norm_map, hx, hy, mul_one]; exact hM
    · change RCLike.re (inner ℂ (M (V x)) (V.toContinuousLinearMap y)) = _
      rw [← ContinuousLinearMap.adjoint_inner_left, he, inner_self_eq_norm_sq_to_K]
      simp [V.norm_map, hy]
  refine ⟨hMy, ?_⟩
  apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℂ)
  · calc ‖M.adjoint (V y)‖ ≤ ‖M.adjoint‖ * ‖V y‖ := M.adjoint.le_opNorm _
         _ ≤ ‖V x‖ := by
           rw [ContinuousLinearMap.adjoint.norm_map, V.norm_map, V.norm_map, hx, hy, mul_one]
           exact hM
  · rw [ContinuousLinearMap.adjoint_inner_left, hMy, inner_self_eq_norm_sq_to_K]
    simp [V.norm_map, hx, hy]

end

section
open MeasureTheory
variable {T : Type u_204} {H : Type u_205} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positiveDilation_saturation (S B : C(T,H →L[ℂ] H))
    (hmass : (∫ t, (S t).adjoint * S t ∂μ) = 1) (hB : ∀ t, ‖B t‖ ≤ 1)
    {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (he : (∫ t, (S t).adjoint * B t * S t ∂μ) x = y) :
    ∀ᵐ t ∂μ, B t (S t x) = S t y ∧ (B t).adjoint (S t y) = S t x := by
  let hBn : ∀ᵐ t ∂μ, ‖B t‖ ≤ 1 := Filter.Eventually.of_forall hB
  let M := pointwiseL2L (fun t => B t) B.continuous.aestronglyMeasurable hBn
  let V := positiveDilation S hmass
  have hcomp := positiveDilation_compression (μ := μ) S B hmass hB
  have hv : V.toContinuousLinearMap.adjoint (M (V x)) = y := by
    have hh := congrArg (fun f : H →L[ℂ] H => f x) hcomp
    exact hh.trans he
  obtain ⟨hforward,hback⟩ := isometric_multiplier_saturation V M
    (pointwiseL2L_norm _ _ _) hx hy hv
  have hC : Continuous (fun t => (B t).adjoint) := by fun_prop
  have hCn : ∀ᵐ t ∂μ, ‖(B t).adjoint‖ ≤ 1 := by
    filter_upwards [] with t
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hB t
  have hadj := pointwiseL2L_adjoint (fun t => B t) B.continuous.aestronglyMeasurable hBn
    (fun t => (B t).adjoint) hC.aestronglyMeasurable hCn (Filter.Eventually.of_forall fun _ => rfl)
  have hback' : pointwiseL2L (fun t => (B t).adjoint) hC.aestronglyMeasurable hCn (V y) = V x := by
    rw [← hadj]
    exact hback
  have hfae : M (V x) =ᵐ[μ] V y := by rw [hforward]
  have hbae : pointwiseL2L (fun t => (B t).adjoint) hC.aestronglyMeasurable hCn (V y) =ᵐ[μ] V x := by rw [hback']
  filter_upwards [hfae, hbae, dilationLM_coe (μ := μ) S x,
    dilationLM_coe (μ := μ) S y,
    pointwiseL2_ae (fun t => B t) B.continuous.aestronglyMeasurable hBn (V x),
    pointwiseL2_ae (fun t => (B t).adjoint) hC.aestronglyMeasurable hCn (V y)]
    with t hf hb hxt hyt hmt hmat
  change (V x) t = S t x at hxt
  change (V y) t = S t y at hyt
  change (M (V x)) t = B t ((V x) t) at hmt
  change (pointwiseL2L (fun t => (B t).adjoint) hC.aestronglyMeasurable hCn (V y)) t =
    (B t).adjoint ((V y) t) at hmat
  exact ⟨by rwa [hmt, hxt, hyt] at hf, by rwa [hmat, hyt, hxt] at hb⟩
end

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
section
variable {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def weightedDensity (L : Matrix n n ℂ) (X Y : Matrix n m ℂ) : Matrix m m ℂ :=
  (Xᴴ * L * Y)ᵀ

lemma weightedDensity_star
    {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (L : Matrix n n ℂ) (X Y : Matrix n m ℂ) :
    (weightedDensity L X Y)ᴴ = weightedDensity Lᴴ Y X := by
  simp only [weightedDensity, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma weightedDensity_pos
    {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {L : Matrix n n ℂ} (hL : L.PosSemidef) (X : Matrix n m ℂ) :
    (weightedDensity L X X).PosSemidef :=
  (hL.conjTranspose_mul_mul_same X).transpose

lemma weightedDensity_block_pos {L : Matrix n n ℂ} (hL : L.PosSemidef)
    (X Y : Matrix n m ℂ) :
    (Matrix.fromBlocks (weightedDensity L X X) (weightedDensity L X Y)ᴴ
      (weightedDensity L X Y) (weightedDensity L Y Y)).PosSemidef := by
  have hp := (hL.conjTranspose_mul_mul_same (Matrix.fromCols X Y)).transpose
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, Matrix.fromBlocks_transpose] at hp
  rw [weightedDensity_star, hL.isHermitian.eq]
  exact hp

lemma weightedDensity_of_sqrt
    {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {L S : Matrix n n ℂ} (hS : Sᴴ*S = L)
    (X Y : Matrix n m ℂ) :
    weightedDensity L X Y = weightedDensity 1 (S*X) (S*Y) := by
  simp only [weightedDensity, Matrix.conjTranspose_mul, Matrix.mul_one]
  rw [← hS]
  congr 1
  simp only [Matrix.mul_assoc]

lemma weightedDensity_right
    {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (L : Matrix n n ℂ) (X Y : Matrix n m ℂ)
    (F : Matrix m m ℂ) :
    weightedDensity L X (Y*Fᵀ) = F*weightedDensity L X Y := by
  simp only [weightedDensity, ← Matrix.mul_assoc, Matrix.transpose_mul,
    Matrix.transpose_transpose]

lemma weightedDensity_left
    {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (L : Matrix n n ℂ) (X Y : Matrix n m ℂ)
    (F : Matrix m m ℂ) :
    weightedDensity L (X*Fᵀ) Y = weightedDensity L X Y * Fᴴ := by
  simp only [weightedDensity, Matrix.conjTranspose_mul, Matrix.transpose_mul,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, Matrix.transpose_transpose, Matrix.mul_assoc]

lemma weightedDensity_ordered_products (X Y : Matrix n m ℂ) (F : Matrix m m ℂ)
    (hY : Y = X*Fᵀ) (hX : X = Y*(Fᴴ)ᵀ) :
    weightedDensity 1 X X = Fᴴ*weightedDensity 1 X Y ∧
    weightedDensity 1 X Y = F*weightedDensity 1 X X ∧
    weightedDensity 1 Y Y = weightedDensity 1 X Y*Fᴴ := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = weightedDensity 1 X (Y*(Fᴴ)ᵀ) := congrArg (weightedDensity 1 X) hX
      _ = _ := weightedDensity_right 1 X Y Fᴴ
  · calc
      _ = weightedDensity 1 X (X*Fᵀ) := congrArg (weightedDensity 1 X) hY
      _ = _ := weightedDensity_right 1 X X F
  · calc
      _ = weightedDensity 1 (X*Fᵀ) Y := congrArg (fun Z => weightedDensity 1 Z Y) hY
      _ = _ := weightedDensity_left 1 X Y F

def weightedDensityCLM (X Y : Matrix n m ℂ) : Matrix n n ℂ →L[ℂ] Matrix m m ℂ :=
  (show Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ from
    { toFun := fun L => weightedDensity L X Y
      map_add' := fun L M => by simp [weightedDensity,Matrix.mul_add,Matrix.add_mul]
      map_smul' := fun c L => by simp [weightedDensity] }).toContinuousLinearMap

lemma integral_weightedDensity {T : Type u_208} [MeasurableSpace T] {μ : Measure T}
    {L : T → Matrix n n ℂ} (hL : Integrable L μ) (X Y : Matrix n m ℂ) :
    (∫ t, weightedDensity (L t) X Y ∂μ) = weightedDensity (∫ t, L t ∂μ) X Y :=
  (weightedDensityCLM X Y).integral_comp_comm hL

lemma weightedDensity_mean {T : Type u_209} [MeasurableSpace T] {μ : Measure T}
    {L : T → Matrix n n ℂ} (hL : Integrable L μ) (hmass : ∫ t, L t ∂μ = 1)
    (X Y : Matrix n m ℂ) :
    (∫ t, weightedDensity (L t) X Y ∂μ) = (Xᴴ*Y)ᵀ := by
  rw [integral_weightedDensity hL, hmass, weightedDensity, Matrix.mul_one]

lemma weightedDensity_mean_zero {T : Type u_210} [MeasurableSpace T] {μ : Measure T}
    {L : T → Matrix n n ℂ} (hL : Integrable L μ) (hmass : ∫ t, L t ∂μ = 1)
    {X Y : Matrix n m ℂ} (hXY : Xᴴ*Y = 0) :
    (∫ t, weightedDensity (L t) X Y ∂μ) = 0 := by
  rw [weightedDensity_mean hL hmass, hXY, Matrix.transpose_zero]

lemma trace_weightedDensity_one
    {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (X : Matrix n m ℂ) :
    (weightedDensity 1 X X).trace = (‖vectorize X‖ ^ 2 : ℝ) := by
  simp only [weightedDensity, Matrix.mul_one, Matrix.trace, Matrix.diag_apply, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, vectorize]
  rw [Finset.sum_comm]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (starRingEnd ℂ) (X j i) * X j i = (‖X j i‖ : ℂ)^2
  rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]
  simp

lemma continuous_weightedDensity
    {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {T : Type u_211} [TopologicalSpace T]
    {L : T → Matrix n n ℂ} (hL : Continuous L) (X Y : Matrix n m ℂ) :
    Continuous (fun t => weightedDensity (L t) X Y) :=
  (weightedDensityCLM X Y).continuous.comp hL

lemma inner_vectorize
    {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (X Y : Matrix n m ℂ) :
    inner ℂ (vectorize X) (vectorize Y) = (Xᴴ*Y).trace := by
  simp only [vectorize, PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_prod_type,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change Y j i * (starRingEnd ℂ) (X j i) = (starRingEnd ℂ) (X j i) * Y j i
  exact mul_comm _ _

theorem weightedDensity_testing {L : Matrix n n ℂ} (hL : L.IsHermitian)
    (X Y : Matrix n m ℂ) (u : Matrix m m ℂ) :
    ((weightedDensity L X Y)ᴴ*u).trace =
      inner ℂ (vectorize Y) (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ)
        (L ⊗ₖ u) (vectorize X)) := by
  rw [weightedDensity_star, hL.eq, kronecker_vectorize, inner_vectorize]
  simp only [weightedDensity, Matrix.mul_assoc]
  calc
    _ = ((Yᴴ * (L * X)) * uᵀ).trace := by
      simpa only [Matrix.transpose_transpose] using
        Matrix.trace_transpose_mul (Yᴴ * (L * X)) uᵀ
    _ = _ := by simp only [Matrix.mul_assoc]

end

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
variable {T : Type u_212} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]
  {n : Type u_213} {m : Type u_214} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

lemma vectorize_injective
    {n : Type u_213} {m : Type u_214} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] :
    Function.Injective (vectorize (n := n) (m := m)) := by
  intro X Y h
  ext i j
  exact congrArg (fun v : EuclideanSpace ℂ (n × m) => v (i,j)) h

theorem actual_density_ordered (L : C(T,Matrix n n ℂ)) (hL : ∀ t, 0 ≤ L t)
    (hmass : (∫ t, L t ∂μ) = 1)
    (F : C(T,Matrix m m ℂ)) (hF : ∀ t, ‖F t‖ ≤ 1)
    {X Y : Matrix n m ℂ} (hx : ‖vectorize X‖ = 1) (hy : ‖vectorize Y‖ = 1)
    (he : (∫ t, Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (L t ⊗ₖ F t) ∂μ)
      (vectorize X) = vectorize Y) :
    ∀ᵐ t ∂μ,
      weightedDensity (L t) X X = (F t)ᴴ * weightedDensity (L t) X Y ∧
      weightedDensity (L t) X Y = F t * weightedDensity (L t) X X ∧
      weightedDensity (L t) Y Y = weightedDensity (L t) X Y * (F t)ᴴ := by
  have he' : (∫ t, (densityRootField (m := m) L hL t).adjoint *
      coefficientMultiplierField (n := n) F t * densityRootField (m := m) L hL t ∂μ)
      (vectorize X) = vectorize Y := by
    simpa only [densityRootField_compression] using he
  have ha := positiveDilation_saturation (μ := μ) (densityRootField (m := m) L hL)
    (coefficientMultiplierField (n := n) F) (densityRootField_mass L hL hmass)
    (coefficientMultiplierField_norm F hF) hx hy he'
  filter_upwards [ha] with t ht
  let S : Matrix n n ℂ := CFC.sqrt (L t)
  have hs : Sᴴ*S = L t := by
    have hh : Sᴴ = S := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (L t))).isHermitian.eq
    rw [hh]
    exact CFC.sqrt_mul_sqrt_self (L t) (hL t)
  have hroot (Z : Matrix n m ℂ) : densityRootField (m := m) L hL t (vectorize Z) =
      vectorize (S*Z) := by
    change Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (S ⊗ₖ (1 : Matrix m m ℂ)) (vectorize Z) = _
    rw [kronecker_vectorize]
    simp only [Matrix.transpose_one, Matrix.mul_one]
  have hcoeff (B : Matrix m m ℂ) (Z : Matrix n m ℂ) :
      coefficientAmplification (n := n) B (vectorize Z) = vectorize (Z*Bᵀ) := by
    change Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) ((1 : Matrix n n ℂ) ⊗ₖ B) (vectorize Z) = _
    rw [kronecker_vectorize, Matrix.one_mul]
  have hY : S*Y = (S*X)*(F t)ᵀ := by
    apply vectorize_injective
    have hh := ht.1
    change coefficientAmplification (n := n) (F t) (densityRootField L hL t (vectorize X)) =
      densityRootField L hL t (vectorize Y) at hh
    rw [hroot, hroot, hcoeff] at hh
    exact hh.symm
  have hX : S*X = (S*Y)*((F t)ᴴ)ᵀ := by
    apply vectorize_injective
    have hh := ht.2
    change (coefficientAmplification (n := n) (F t)).adjoint
      (densityRootField L hL t (vectorize Y)) = densityRootField L hL t (vectorize X) at hh
    rw [← coefficientAmplification_star, hroot, hroot, hcoeff] at hh
    exact hh.symm
  simpa only [← weightedDensity_of_sqrt hs] using
    weightedDensity_ordered_products (S*X) (S*Y) (F t) hY hX

theorem actual_density_means
    {T : Type u_212} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T] {μ : MeasureTheory.Measure T}
    [MeasureTheory.IsFiniteMeasure μ] {n : Type u_213} {m : Type u_214} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (L : C(T,Matrix n n ℂ))
    (hmass : (∫ t, L t ∂μ) = 1) {X Y : Matrix n m ℂ}
    (hx : ‖vectorize X‖ = 1) (hXY : Xᴴ*Y = 0) :
    (∫ t, weightedDensity (L t) X Y ∂μ) = 0 ∧
    (∫ t, weightedDensity (L t) X X ∂μ).trace = 1 := by
  have hi : Integrable (fun t => L t) μ :=
    L.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨weightedDensity_mean_zero hi hmass hXY, ?_⟩
  rw [integral_weightedDensity hi, hmass, trace_weightedDensity_one, hx]
  norm_num


end CompleteCrouzeix

end

end OAI
