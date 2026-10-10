import OAI.Analysis.RotationWeights.Decomposable

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uA uB uE uX

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

section

lemma fiberShiftL2_indicator (n : ℤ) (s : Set CircleX) (hs : MeasurableSet s) :
    fiberShiftL2 n * indicatorV2 AddCircle.haarAddCircle s hs =
      indicatorV2 AddCircle.haarAddCircle s hs * fiberShiftL2 n := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [fiberShiftL2_coe n (indicatorV2 AddCircle.haarAddCircle s hs f),
    indicatorV2_coe AddCircle.haarAddCircle s hs f,
    indicatorV2_coe AddCircle.haarAddCircle s hs (fiberShiftL2 n f),
    fiberShiftL2_coe n f] with x h1 h2 h3 h4
  change (fiberShiftL2 n (indicatorV2 AddCircle.haarAddCircle s hs f)) x =
    (indicatorV2 AddCircle.haarAddCircle s hs (fiberShiftL2 n f)) x
  rw [h1,h2,h3]
  by_cases hx : x∈s
  · simp only [Set.indicator_of_mem hx,h4]
  · simp only [Set.indicator_of_notMem hx,map_zero]

lemma continuousPi_indicator (θ : CircleX) (g : C(CircleX,ℂ))
    (s : Set CircleX) (hs : MeasurableSet s) :
    continuousPi θ g * indicatorV2 AddCircle.haarAddCircle s hs =
      indicatorV2 AddCircle.haarAddCircle s hs * continuousPi θ g := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousPi_coe θ g (indicatorV2 AddCircle.haarAddCircle s hs f),
    indicatorV2_coe AddCircle.haarAddCircle s hs f,
    indicatorV2_coe AddCircle.haarAddCircle s hs (continuousPi θ g f),
    continuousPi_coe θ g f] with x h1 h2 h3 h4
  change (continuousPi θ g (indicatorV2 AddCircle.haarAddCircle s hs f)) x =
    (indicatorV2 AddCircle.haarAddCircle s hs (continuousPi θ g f)) x
  rw [h1,h2,h3]
  by_cases hx : x∈s
  · simp only [Set.indicator_of_mem hx,h4]
  · simp only [Set.indicator_of_notMem hx,map_zero]

def circleJ (θ : CircleX) (n : ℤ) : CircleFiberOperator :=
  shiftedL2 AddCircle.haarAddCircle (fun x ↦ x+n•θ)
    (measurePreserving_add_right AddCircle.haarAddCircle (n•θ))
    (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap

lemma circleJ_coe (θ : CircleX) (n : ℤ) (f : CircleFiberL2) :
    circleJ θ n f =ᵐ[AddCircle.haarAddCircle] fun x ↦ fiberShift n (f (x+n•θ)) :=
  shiftedL2_coe _ _ _ _ _

lemma fiberShiftL2_circleJ (θ : CircleX) (n : ℤ) :
    fiberShiftL2 1 * circleJ θ n = circleJ θ n * fiberShiftL2 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [fiberShiftL2_coe 1 (circleJ θ n f),circleJ_coe θ n f,
    circleJ_coe θ n (fiberShiftL2 1 f),
    (measurePreserving_add_right AddCircle.haarAddCircle (n•θ)).quasiMeasurePreserving.ae
      (fiberShiftL2_coe 1 f)] with x h1 h2 h3 h4
  change (fiberShiftL2 1 (circleJ θ n f)) x = (circleJ θ n (fiberShiftL2 1 f)) x
  rw [h1,h2,h3,h4]
  change (fiberShift 1 * fiberShift n) (f (x+n•θ)) =
    (fiberShift n * fiberShift 1) (f (x+n•θ))
  rw [← fiberShift_add,← fiberShift_add,add_comm (1:ℤ) n]

lemma continuousPiField_covariance (θ : CircleX) (n : ℤ) (g : C(CircleX,ℂ)) (x : CircleX)
    (u : FiberHilbert) :
    continuousPiField θ g x (fiberShift n u) =
      fiberShift n (continuousPiField θ g (x+n•θ) u) := by
  ext k
  simp only [continuousPiField_apply,fiberShift_apply]
  have he : x+(k:ℤ)•θ = (x+n•θ)+(k-n)•θ := by rw [sub_zsmul]; abel
  rw [he]

lemma continuousPi_circleJ (θ : CircleX) (n : ℤ) (g : C(CircleX,ℂ)) :
    continuousPi θ g * circleJ θ n = circleJ θ n * continuousPi θ g := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousPi_coe θ g (circleJ θ n f),circleJ_coe θ n f,
    circleJ_coe θ n (continuousPi θ g f),
    (measurePreserving_add_right AddCircle.haarAddCircle (n•θ)).quasiMeasurePreserving.ae
      (continuousPi_coe θ g f)] with x h1 h2 h3 h4
  change (continuousPi θ g (circleJ θ n f)) x = (circleJ θ n (continuousPi θ g f)) x
  rw [h1,h2,h3,h4]
  exact continuousPiField_covariance θ n g x _

lemma doubleCentralizer_commute {A : Type uA} {B : Type uB} [Monoid A] [Monoid B]
    (φ : A ≃* B) (u v p : A) (hp : p ∈ Set.centralizer (Set.centralizer ({u,v} : Set A)))
    (b : B) (hu : φ u * b = b * φ u) (hv : φ v * b = b * φ v) :
    φ p * b = b * φ p := by
  have hb : φ.symm b ∈ Set.centralizer ({u,v} : Set A) := by
    intro a ha
    rcases (Set.mem_insert_iff.mp ha) with rfl | ha
    · apply φ.injective
      simpa using hu
    · have he : a=v := Set.mem_singleton_iff.mp ha
      subst a
      apply φ.injective
      simpa using hv
  have he := hp (φ.symm b) hb
  have he' := congrArg φ he.symm
  simpa only [map_mul,φ.apply_symm_apply] using he'

lemma regular_doubleCentralizer_indicators (θ : ℝ) (p : RegularOperator)
    (hp : p ∈ Set.centralizer (Set.centralizer
      ({(regularU : RegularOperator),(regularV (rotationScalar θ) : RegularOperator)} : Set RegularOperator)))
    (s : Set CircleX) (hs : MeasurableSet s) :
    circleFiberBasis.repr.symm.conjStarAlgEquiv p * indicatorV2 AddCircle.haarAddCircle s hs =
      indicatorV2 AddCircle.haarAddCircle s hs * circleFiberBasis.repr.symm.conjStarAlgEquiv p := by
  apply doubleCentralizer_commute circleFiberBasis.repr.symm.conjStarAlgEquiv.toMulEquiv
    regularU (regularV (rotationScalar θ)) p hp
  · change circleFiberBasis.repr.symm.conjStarAlgEquiv (regularU : RegularOperator) * _ =
      _ * circleFiberBasis.repr.symm.conjStarAlgEquiv (regularU : RegularOperator)
    rw [circleFiberBasis_conj_U]
    exact fiberShiftL2_indicator 1 s hs
  · change circleFiberBasis.repr.symm.conjStarAlgEquiv (regularV (rotationScalar θ) : RegularOperator) * _ =
      _ * circleFiberBasis.repr.symm.conjStarAlgEquiv (regularV (rotationScalar θ) : RegularOperator)
    rw [circleFiberBasis_conj_V]
    exact continuousPi_indicator (θ : CircleX) (fourier 1) s hs


lemma regular_doubleCentralizer_circleJ (θ : ℝ) (p : RegularOperator)
    (hp : p ∈ Set.centralizer (Set.centralizer
      ({(regularU : RegularOperator),(regularV (rotationScalar θ) : RegularOperator)} : Set RegularOperator)))
    (n : ℤ) :
    circleFiberBasis.repr.symm.conjStarAlgEquiv p * circleJ (θ : CircleX) n =
      circleJ (θ : CircleX) n * circleFiberBasis.repr.symm.conjStarAlgEquiv p := by
  apply doubleCentralizer_commute circleFiberBasis.repr.symm.conjStarAlgEquiv.toMulEquiv
    regularU (regularV (rotationScalar θ)) p hp
  · change circleFiberBasis.repr.symm.conjStarAlgEquiv (regularU : RegularOperator) * _ =
      _ * circleFiberBasis.repr.symm.conjStarAlgEquiv (regularU : RegularOperator)
    rw [circleFiberBasis_conj_U]
    exact fiberShiftL2_circleJ (θ : CircleX) n
  · change circleFiberBasis.repr.symm.conjStarAlgEquiv (regularV (rotationScalar θ) : RegularOperator) * _ =
      _ * circleFiberBasis.repr.symm.conjStarAlgEquiv (regularV (rotationScalar θ) : RegularOperator)
    rw [circleFiberBasis_conj_V]
    exact continuousPi_circleJ (θ : CircleX) n (fourier 1)
end

open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
section
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma invariant_eigenvector_zero (P Q D : E →L[ℂ] E)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hInv : (1-Q)*D*P=0) (e : E) (c : ℂ) (hc : c≠0)
    (hDe : (star D) e = c•e) (hQe : Q e=0) : P e=0 := by
  have hStar : P * star D * (1-Q)=0 := by
    have h := congrArg star hInv
    simpa only [star_mul,star_sub,star_one,hP.isSelfAdjoint.star_eq,
      hQ.isSelfAdjoint.star_eq,star_zero,mul_assoc] using h
  have h := congrArg (fun A : E →L[ℂ] E ↦ A e) hStar
  change P ((star D) (e-Q e))=0 at h
  rw [hQe,sub_zero,hDe,map_smul] at h
  exact (smul_eq_zero.mp h).resolve_left hc

omit [CompleteSpace E] in
lemma invariant_eigenvector_one (P Q D : E →L[ℂ] E)
    (hInv : (1-Q)*D*P=0) (e : E) (c : ℂ) (hc : c≠0)
    (hDe : D e=c•e) (hPe : P e=e) : Q e=e := by
  have h := congrArg (fun A : E →L[ℂ] E ↦ A e) hInv
  change (1-Q) (D (P e))=0 at h
  rw [hPe,hDe,map_smul] at h
  have he := (smul_eq_zero.mp h).resolve_left hc
  change e-Q e=0 at he
  exact (sub_eq_zero.mp he).symm

lemma projection_diagonal_norm_sq (P : E →L[ℂ] E) (hP : IsStarProjection P) (e : E) :
    (inner ℂ e (P e)).re = ‖P e‖^2 := by
  have h := ContinuousLinearMap.adjoint_inner_right P e (P e)
  have hid : P (P e)=P e := congrArg (fun A : E →L[ℂ] E ↦ A e) hP.isIdempotentElem.eq
  change inner ℂ e ((star P) (P e)) = inner ℂ (P e) (P e) at h
  rw [hP.isSelfAdjoint.star_eq,hid] at h
  rw [h]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (P e)

lemma projection_diagonal_strict (P : E →L[ℂ] E) (hP : IsStarProjection P) (e : E)
    (he : ‖e‖=1) (hz : P e≠0) (ho : P e≠e) :
    0 < (inner ℂ e (P e)).re ∧ (inner ℂ e (P e)).re < 1 := by
  have hp := projection_diagonal_norm_sq P hP e
  have hq := projection_diagonal_norm_sq (1-P) hP.one_sub e
  have hqn : (1-P) e ≠ 0 := by
    change e-P e ≠ 0
    intro h
    exact ho (sub_eq_zero.mp h).symm
  have hqpos : 0 < ‖(1-P) e‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hqn)
  have hpn : 0 < ‖P e‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hqeq : (inner ℂ e ((1-P) e)).re = 1-(inner ℂ e (P e)).re := by
    change (inner ℂ e (e-P e)).re = _
    rw [inner_sub_right,Complex.sub_re]
    have hee : (inner ℂ e e).re = ‖e‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) e
    rw [hee,he,one_pow]
  rw [hqeq] at hq
  exact ⟨by linarith,by linarith⟩

end

open MeasureTheory Filter Set
section
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

lemma ergodic_ae_ne_of_preimage_zero (σ : X → X) (hσ : Ergodic σ μ)
    (f : X → E) (hf : AEMeasurable f μ) (e : E)
    (hinv : ∀ᵐ x ∂μ, f (σ x)=e → f x=e)
    (hne : ¬∀ᵐ x ∂μ, f x=e) : ∀ᵐ x ∂μ, f x≠e := by
  have hs : NullMeasurableSet {x | f x=e} μ := hf.nullMeasurableSet_preimage (measurableSet_singleton e)
  have hle : σ ⁻¹' {x | f x=e} ≤ᵐ[μ] {x | f x=e} := hinv
  rcases hσ.ae_empty_or_univ_of_preimage_ae_le hs hle with h | h
  · filter_upwards [h] with x hx
    intro he
    exact Eq.mp hx he
  · apply False.elim
    apply hne
    filter_upwards [h] with x hx
    exact hx.mpr (Set.mem_univ x)

lemma ergodic_ae_ne_of_zero_preimage (σ : X → X) (hσ : Ergodic σ μ)
    (f : X → E) (hf : AEMeasurable f μ) (e : E)
    (hinv : ∀ᵐ x ∂μ, f x=e → f (σ x)=e)
    (hne : ¬∀ᵐ x ∂μ, f x=e) : ∀ᵐ x ∂μ, f x≠e := by
  have hs : NullMeasurableSet {x | f x=e} μ := hf.nullMeasurableSet_preimage (measurableSet_singleton e)
  have hle : {x | f x=e} ≤ᵐ[μ] σ ⁻¹' {x | f x=e} := hinv
  rcases hσ.ae_empty_or_univ_of_ae_le_preimage hs hle with h | h
  · filter_upwards [h] with x hx
    intro he
    exact Eq.mp hx he
  · apply False.elim
    apply hne
    filter_upwards [h] with x hx
    exact hx.mpr (Set.mem_univ x)
end

section

lemma covariant_field_zero (θ : CircleX) (P : CircleX → FiberOperator)
    (hcov : ∀ n : ℤ, ∀ᵐ x ∂AddCircle.haarAddCircle,
      P x * (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap =
        (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap * P (x+n•θ))
    (hz : ∀ᵐ x ∂AddCircle.haarAddCircle, P x (lp.single 2 0 1)=0) :
    ∀ᵐ x ∂AddCircle.haarAddCircle, P x=0 := by
  have hb : ∀ n : ℤ, ∀ᵐ x ∂AddCircle.haarAddCircle, P x (lp.single 2 n 1)=0 := by
    intro n
    filter_upwards [hcov n,
      (measurePreserving_add_right AddCircle.haarAddCircle (n•θ)).quasiMeasurePreserving.ae hz]
      with x hc he
    have h := congrArg (fun A : FiberOperator ↦ A (lp.single 2 0 1)) hc
    change P x (fiberShift n (lp.single 2 0 1)) = fiberShift n (P (x+n•θ) (lp.single 2 0 1)) at h
    simpa only [fiberShift_single,add_zero,he,map_zero] using h
  filter_upwards [ae_all_iff.mpr hb] with x hx
  apply lp.ext_continuousLinearMap (by norm_num)
  intro n
  apply ContinuousLinearMap.ext
  intro c
  change P x (lp.single 2 n c)=0
  have he : (lp.single 2 n c : FiberHilbert) = c • (lp.single 2 n (1:ℂ) : FiberHilbert) := by
    ext k
    by_cases hk : k=n
    · subst k
      simp
    · simp [lp.single_apply,hk]
  rw [he,map_smul,hx n,smul_zero]

lemma covariant_field_one (θ : CircleX) (P : CircleX → FiberOperator)
    (hcov : ∀ n : ℤ, ∀ᵐ x ∂AddCircle.haarAddCircle,
      P x * (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap =
        (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap * P (x+n•θ))
    (hz : ∀ᵐ x ∂AddCircle.haarAddCircle, P x (lp.single 2 0 1)=lp.single 2 0 1) :
    ∀ᵐ x ∂AddCircle.haarAddCircle, P x=1 := by
  have hc : ∀ n : ℤ, ∀ᵐ x ∂AddCircle.haarAddCircle,
      (1-P x) * (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap =
        (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap * (1-P (x+n•θ)) := by
    intro n
    filter_upwards [hcov n] with x hx
    simp only [sub_mul,mul_sub,one_mul,mul_one,hx]
  have hz' : ∀ᵐ x ∂AddCircle.haarAddCircle, (1-P x) (lp.single 2 0 1)=0 := by
    filter_upwards [hz] with x hx
    change lp.single 2 0 1-P x (lp.single 2 0 1)=0
    rw [hx,sub_self]
  filter_upwards [covariant_field_zero θ (fun x ↦ 1-P x) hc hz'] with x hx
  exact (sub_eq_zero.mp hx).symm

lemma decomposable_eq_zero {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ) (P : X → (E →L[ℂ] E))
    (hP : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x=P x (f x))
    (hz : ∀ᵐ x ∂μ, P x=0) : A=0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [hP f,hz,Lp.coeFn_zero E 2 μ] with x h1 h2 h3
  change (A f) x = (0 : Lp E 2 μ) x
  rw [h1,h2]
  simpa using h3.symm

lemma decomposable_eq_one {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ) (P : X → (E →L[ℂ] E))
    (hP : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x=P x (f x))
    (hz : ∀ᵐ x ∂μ, P x=1) : A=1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [hP f,hz] with x h1 h2
  change (A f) x = f x
  rw [h1,h2,one_apply_eq_self]

end

lemma invariant_covariant_diagonal_strict
    (θ : CircleX) (hθ : Ergodic (fun x : CircleX ↦ x+θ) AddCircle.haarAddCircle)
    (A : CircleFiberOperator) (P : CircleX → FiberOperator)
    (hP : ∀ f : CircleFiberL2, ∀ᵐ x ∂AddCircle.haarAddCircle, (A f) x=P x (f x))
    (hproj : ∀ᵐ x ∂AddCircle.haarAddCircle, IsStarProjection (P x))
    (hcov : ∀ n : ℤ, ∀ᵐ x ∂AddCircle.haarAddCircle,
      P x * (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap =
        (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap * P (x+n•θ))
    (D : CircleX → FiberOperator) (c : CircleX → ℂ)
    (hc : ∀ᵐ x ∂AddCircle.haarAddCircle, c x≠0)
    (heigen : ∀ᵐ x ∂AddCircle.haarAddCircle,
      D x (lp.single 2 0 1)=c x • lp.single 2 0 1 ∧
      (star (D x)) (lp.single 2 0 1)=c x • lp.single 2 0 1)
    (hinv : ∀ᵐ x ∂AddCircle.haarAddCircle, (1-P (x+θ))*D x*P x=0)
    (hA0 : A≠0) (hA1 : A≠1) :
    ∀ᵐ x ∂AddCircle.haarAddCircle,
      0 < (inner ℂ (lp.single 2 0 1) (P x (lp.single 2 0 1))).re ∧
      (inner ℂ (lp.single 2 0 1) (P x (lp.single 2 0 1))).re < 1 := by
  let : MeasurableSpace FiberHilbert := borel FiberHilbert
  let : BorelSpace FiberHilbert := ⟨rfl⟩
  let e : FiberHilbert := lp.single 2 0 1
  have hm : AEMeasurable (fun x ↦ P x e) AddCircle.haarAddCircle := by
    apply (Lp.aestronglyMeasurable (A (Lp.const 2 AddCircle.haarAddCircle e))).aemeasurable.congr
    exact decomposable_const AddCircle.haarAddCircle A P hP e
  have hz : ¬∀ᵐ x ∂AddCircle.haarAddCircle, P x e=0 := by
    intro h
    exact hA0 (decomposable_eq_zero AddCircle.haarAddCircle A P hP (covariant_field_zero θ P hcov h))
  have ho : ¬∀ᵐ x ∂AddCircle.haarAddCircle, P x e=e := by
    intro h
    exact hA1 (decomposable_eq_one AddCircle.haarAddCircle A P hP (covariant_field_one θ P hcov h))
  have hrz : ∀ᵐ x ∂AddCircle.haarAddCircle, P (x+θ) e=0 → P x e=0 := by
    filter_upwards [hproj,hθ.toMeasurePreserving.quasiMeasurePreserving.ae hproj,hc,heigen,hinv]
      with x hp hq hcx hex hix
    intro h
    exact invariant_eigenvector_zero (P x) (P (x+θ)) (D x) hp hq hix e (c x) hcx hex.2 h
  have hro : ∀ᵐ x ∂AddCircle.haarAddCircle, P x e=e → P (x+θ) e=e := by
    filter_upwards [hc,heigen,hinv] with x hcx hex hix
    intro h
    exact invariant_eigenvector_one (P x) (P (x+θ)) (D x) hix e (c x) hcx hex.1 h
  filter_upwards [hproj,
    ergodic_ae_ne_of_preimage_zero (fun x : CircleX ↦ x+θ) hθ (fun x ↦ P x e) hm 0 hrz hz,
    ergodic_ae_ne_of_zero_preimage (fun x : CircleX ↦ x+θ) hθ (fun x ↦ P x e) hm e hro ho]
    with x hp hx0 hx1
  exact projection_diagonal_strict (P x) hp e (by simp [e]) hx0 hx1


end ContinuousCircleWeight

end

end OAI
