import Mathlib

namespace OAI

namespace HigherDimensionalBallPacking
open scoped ContDiff

abbrev Phase (n : ℕ) := Fin n → ℂ

noncomputable def capacity {n : ℕ} (z : Phase n) : ℝ :=
  Real.pi * ∑ j, Complex.normSq (z j)

def closedBall (n : ℕ) (r : ℝ) : Set (Phase n) := {z | capacity z ≤ r}

def openBall (n : ℕ) (r : ℝ) : Set (Phase n) := {z | capacity z < r}

noncomputable def standardForm {n : ℕ} (u v : Phase n) : ℝ :=
  ∑ j, ((u j).re * (v j).im - (u j).im * (v j).re)

def SymplecticOn {n : ℕ} (U : Set (Phase n)) (f : Phase n → Phase n) : Prop :=
  IsOpen U ∧ ContDiffOn ℝ ∞ f U ∧
    Topology.IsEmbedding (fun x : U => f x) ∧
    ∀ x ∈ U, ∀ u v : Phase n,
      standardForm (fderiv ℝ f x u) (fderiv ℝ f x v) = standardForm u v

def HasPacking (n k : ℕ) (R : ℝ) (r : Fin k → ℝ) : Prop :=
  ∃ (U : Fin k → Set (Phase n)) (f : Fin k → Phase n → Phase n),
    (∀ i, closedBall n (r i) ⊆ U i ∧ SymplecticOn (U i) (f i) ∧
      Set.MapsTo (f i) (closedBall n (r i)) (openBall n R)) ∧
    (∀ i j, i ≠ j →
      Disjoint (f i '' closedBall n (r i)) (f j '' closedBall n (r j)))

def PackingInequalities (n k : ℕ) (R : ℝ) (r : Fin k → ℝ) : Prop :=
  (∑ i, r i ^ n) < R ^ n ∧ ∀ i j, i ≠ j → r i + r j < R

noncomputable section
open scoped Topology
open Set Function Filter

namespace Rigidity

abbrev End (n : ℕ) := Phase n →L[ℝ] Phase n

def standardJ (n : ℕ) : End n :=
  (ContinuousLinearMap.lsmul ℝ ℂ) Complex.I

@[simp] theorem standardJ_apply (n : ℕ) (v : Phase n) (i : Fin n) :
    standardJ n v i = Complex.I * v i := rfl

@[simp] theorem standardJ_sq (n : ℕ) (v : Phase n) :
    standardJ n (standardJ n v) = -v := by
  funext i
  simp only [standardJ_apply, ← mul_assoc, Complex.I_mul_I, neg_one_mul, Pi.neg_apply]

@[simp] theorem standardForm_J_J {n : ℕ} (v w : Phase n) :
    standardForm (standardJ n v) (standardJ n w) = standardForm v w := by
  unfold standardForm
  apply Finset.sum_congr rfl
  intro i _
  simp [standardJ_apply, Complex.mul_re, Complex.mul_im]
  ring

@[simp] theorem standardForm_J_self {n : ℕ} (v : Phase n) :
    standardForm v (standardJ n v) = ∑ i, Complex.normSq (v i) := by
  unfold standardForm
  apply Finset.sum_congr rfl
  intro i _
  simp [standardJ_apply, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]

theorem standardForm_J_pos {n : ℕ} {v : Phase n} (hv : v ≠ 0) :
    0 < standardForm v (standardJ n v) := by
  rw [standardForm_J_self]
  have hi : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hi
  have hpos : 0 < Complex.normSq (v i) := Complex.normSq_pos.mpr hi
  exact hpos.trans_le (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j))
    (Finset.mem_univ i))

def Compatible {n : ℕ} (J : End n) : Prop :=
  (∀ v, J (J v) = -v) ∧
  (∀ v w, standardForm (J v) (J w) = standardForm v w) ∧
  (∀ v, v ≠ 0 → 0 < standardForm v (J v))

theorem compatible_standardJ (n : ℕ) : Compatible (standardJ n) :=
  ⟨standardJ_sq n, standardForm_J_J, fun _ hv => standardForm_J_pos hv⟩

def conjugateJ {n : ℕ} (e : Phase n ≃L[ℝ] Phase n) : End n :=
  e.toContinuousLinearMap.comp ((standardJ n).comp e.symm.toContinuousLinearMap)

@[simp] theorem conjugateJ_apply {n : ℕ} (e : Phase n ≃L[ℝ] Phase n) (v : Phase n) :
    conjugateJ e v = e (standardJ n (e.symm v)) := rfl

theorem compatible_conjugateJ {n : ℕ} (e : Phase n ≃L[ℝ] Phase n)
    (he : ∀ v w, standardForm (e v) (e w) = standardForm v w) :
    Compatible (conjugateJ e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    simp
  · intro v w
    simp only [conjugateJ_apply, he, standardForm_J_J]
    simpa using (he (e.symm v) (e.symm w)).symm
  · intro v hv
    have hv' : e.symm v ≠ 0 := by
      intro h
      apply hv
      simpa using congrArg e h
    have h := he (e.symm v) (standardJ n (e.symm v))
    rw [e.apply_symm_apply] at h
    change 0 < standardForm v (e (standardJ n (e.symm v)))
    rw [h]
    exact standardForm_J_pos hv'

theorem symplectic_linear_injective {n : ℕ} {A : End n}
    (hA : ∀ v w, standardForm (A v) (A w) = standardForm v w) :
    Injective A := by
  apply (injective_iff_map_eq_zero A).mpr
  intro v hv
  by_contra hne
  have hp := standardForm_J_pos hne
  have he := hA v (standardJ n v)
  rw [hv, show standardForm (0 : Phase n) (A (standardJ n v)) = 0 by
    simp [standardForm]] at he
  exact (ne_of_gt hp) he.symm

theorem symplectic_linear_invertible {n : ℕ} {A : End n}
    (hA : ∀ v w, standardForm (A v) (A w) = standardForm v w) : A.IsInvertible := by
  have hi := symplectic_linear_injective hA
  have hs := (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs), rfl⟩

theorem symplecticOn_fderiv_invertible {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) {x : Phase n} (hx : x ∈ U) :
    (fderiv ℝ f x).IsInvertible :=
  symplectic_linear_invertible (h.2.2.2 x hx)

theorem symplecticOn_injOn {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) : InjOn f U := by
  intro x hx y hy hxy
  exact congrArg Subtype.val (h.2.2.1.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy)

theorem symplecticOn_open_image {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) : IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x,hx,rfl⟩
  have hs := h.2.1.contDiffAt (h.1.mem_nhds hx)
  obtain ⟨e,he⟩ := symplecticOn_fderiv_invertible h hx
  have hd : HasStrictFDerivAt f (e : End n) x := by
    rw [he]
    exact hs.hasStrictFDerivAt (by simp)
  have hi := Filter.image_mem_map (m := f) (h.1.mem_nhds hx)
  rwa [hd.map_nhds_eq_of_equiv] at hi

theorem symplecticOn_inverse_smooth {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) :
    ContDiffOn ℝ ∞ (invFunOn f U) (f '' U) := by
  rintro y ⟨x,hx,rfl⟩
  apply ContDiffAt.contDiffWithinAt
  have hs := h.2.1.contDiffAt (h.1.mem_nhds hx)
  obtain ⟨e,he⟩ := symplecticOn_fderiv_invertible h hx
  have hd : HasFDerivAt f (e : End n) x := by
    rw [he]
    exact hs.differentiableAt (by simp) |>.hasFDerivAt
  let q := hs.toOpenPartialHomeomorph f hd (by simp)
  have hqx : x ∈ q.source := hs.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hqy : f x ∈ q.target := hs.image_mem_toOpenPartialHomeomorph_target hd (by simp)
  have hqg : q.symm (f x) = x := q.left_inv hqx
  have hqs : ContDiffAt ℝ ∞ q.symm (f x) := hs.to_localInverse hd (by simp)
  have hUevent : ∀ᶠ z in 𝓝 (f x), q.symm z ∈ U :=
    hqs.continuousAt.eventually (h.1.mem_nhds (by rw [hqg]; exact hx))
  apply hqs.congr_of_eventuallyEq
  filter_upwards [q.open_target.mem_nhds hqy, hUevent] with z hz hUz
  have hj := (symplecticOn_injOn h).leftInvOn_invFunOn hUz
  have hqz : f (q.symm z) = z := q.right_inv hz
  rwa [hqz] at hj

def imageJ {n : ℕ} (U : Set (Phase n)) (f : Phase n → Phase n) (y : Phase n) : End n :=
  let D := fderiv ℝ f (invFunOn f U y)
  D.comp ((standardJ n).comp D.inverse)

@[simp] theorem imageJ_at_image {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) {x : Phase n} (hx : x ∈ U) :
    imageJ U f (f x) = (fderiv ℝ f x).comp
      ((standardJ n).comp (fderiv ℝ f x).inverse) := by
  unfold imageJ
  rw [(symplecticOn_injOn h).leftInvOn_invFunOn hx]

theorem imageJ_compatible {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) {y : Phase n} (hy : y ∈ f '' U) :
    Compatible (imageJ U f y) := by
  obtain ⟨x,hx,rfl⟩ := hy
  rw [imageJ_at_image h hx]
  obtain ⟨e,he⟩ := symplecticOn_fderiv_invertible h hx
  rw [←he]
  have heω : ∀ v w, standardForm (e v) (e w) = standardForm v w := by
    intro v w
    change standardForm ((e : End n) v) ((e : End n) w) = _
    rw [he]
    exact h.2.2.2 x hx v w
  convert compatible_conjugateJ e heω using 1
  simp [conjugateJ]

theorem imageJ_smooth {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) :
    ContDiffOn ℝ ∞ (imageJ U f) (f '' U) := by
  intro y hy
  apply ContDiffAt.contDiffWithinAt
  have hg := (symplecticOn_inverse_smooth h).contDiffAt
    ((symplecticOn_open_image h).mem_nhds hy)
  have hx : invFunOn f U y ∈ U := invFunOn_mem hy
  have hf := h.2.1.contDiffAt (h.1.mem_nhds hx)
  have hD : ContDiffAt ℝ ∞ (fun z => fderiv ℝ f (invFunOn f U z)) y :=
    (hf.fderiv_right (by simp)).comp y hg
  have hI := (symplecticOn_fderiv_invertible h hx).contDiffAt_map_inverse.comp y hD
  exact hD.clm_comp (contDiffAt_const.clm_comp hI)

theorem imageJ_intertwines {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) {x : Phase n} (hx : x ∈ U)
    (v : Phase n) :
    imageJ U f (f x) (fderiv ℝ f x v) = fderiv ℝ f x (standardJ n v) := by
  rw [imageJ_at_image h hx]
  obtain ⟨e,he⟩ := symplecticOn_fderiv_invertible h hx
  rw [←he]
  simp

theorem symplecticOn_inverse_fderiv {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) {y : Phase n} (hy : y ∈ f '' U) :
    fderiv ℝ (invFunOn f U) y = (fderiv ℝ f (invFunOn f U y)).inverse := by
  let g := invFunOn f U
  have hx : g y ∈ U := invFunOn_mem hy
  have hg := (symplecticOn_inverse_smooth h).contDiffAt
    ((symplecticOn_open_image h).mem_nhds hy)
  have hf := h.2.1.contDiffAt (h.1.mem_nhds hx)
  have hc : f ∘ g =ᶠ[𝓝 y] id := by
    filter_upwards [(symplecticOn_open_image h).mem_nhds hy] with z hz
    exact invFunOn_eq hz
  have hcomp : (fderiv ℝ f (g y)).comp (fderiv ℝ g y) = ContinuousLinearMap.id ℝ (Phase n) := by
    rw [←fderiv_comp y (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp))]
    rw [hc.fderiv_eq, fderiv_id]
  obtain ⟨e,he⟩ := symplecticOn_fderiv_invertible h hx
  change fderiv ℝ g y = _
  rw [←he]
  rw [←he] at hcomp
  simp only [ContinuousLinearMap.inverse_equiv]
  apply ContinuousLinearMap.ext
  intro v
  apply e.injective
  have hv := congrArg (fun A : End n => A v) hcomp
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using hv

def PseudoHolomorphicAt {n : ℕ} (J : Phase n → End n) (u : ℂ → Phase n) (z : ℂ) : Prop :=
  DifferentiableAt ℝ u z ∧ ∀ w : ℂ,
    fderiv ℝ u z (Complex.I * w) = J (u z) (fderiv ℝ u z w)

theorem complex_differentiable_of_CR {n : ℕ} {u : ℂ → Phase n} {z : ℂ}
    (hu : DifferentiableAt ℝ u z)
    (hCR : ∀ w : ℂ, fderiv ℝ u z (Complex.I * w) = standardJ n (fderiv ℝ u z w)) :
    DifferentiableAt ℂ u z := by
  let A := fderiv ℝ u z
  let L : ℂ →L[ℂ] Phase n := (ContinuousLinearMap.id ℂ ℂ).smulRight (A 1)
  have hL : L.restrictScalars ℝ = A := by
    ext w i
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      simpa only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_one, mul_one]
        using (Complex.re_add_im w).symm
    have hI : A Complex.I = standardJ n (A 1) := by
      simpa only [mul_one] using hCR 1
    have hAw : A w = w.re • A 1 + w.im • standardJ n (A 1) := by
      conv_lhs => rw [hw]
      simp only [map_add, map_smul, hI]
    rw [hAw]
    change w * A 1 i = _
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, standardJ_apply]
    rw [←mul_assoc, ←add_mul]
    congr 1
    exact (Complex.re_add_im w).symm
  exact (hasFDerivAt_of_restrictScalars ℝ hu.hasFDerivAt hL).differentiableAt

theorem inverse_chart_holomorphic {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (h : SymplecticOn U f) {u : ℂ → Phase n} {z : ℂ}
    (hu : PseudoHolomorphicAt (imageJ U f) u z) (hz : u z ∈ f '' U) :
    DifferentiableAt ℂ (invFunOn f U ∘ u) z := by
  let g := invFunOn f U
  have hg := ((symplecticOn_inverse_smooth h).contDiffAt
    ((symplecticOn_open_image h).mem_nhds hz)).differentiableAt (by simp)
  apply complex_differentiable_of_CR (hg.comp z hu.1)
  intro w
  rw [fderiv_comp z hg hu.1]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hu.2]
  rw [symplecticOn_inverse_fderiv h hz]
  change (fderiv ℝ f (g (u z))).inverse
    ((fderiv ℝ f (g (u z))) (standardJ n
      ((fderiv ℝ f (g (u z))).inverse (fderiv ℝ u z w)))) = _
  obtain ⟨e,he⟩ := symplecticOn_fderiv_invertible h (invFunOn_mem hz)
  rw [←he]
  simp

end Rigidity
end
end HigherDimensionalBallPacking

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity

def stdDot (n : ℕ) : Phase n →L[ℝ] Phase n →L[ℝ] ℝ :=
  ∑ i, ((ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (Complex.reCLM.comp (ContinuousLinearMap.proj i))
    (Complex.reCLM.comp (ContinuousLinearMap.proj i)) +
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (Complex.imCLM.comp (ContinuousLinearMap.proj i))
    (Complex.imCLM.comp (ContinuousLinearMap.proj i)))

@[simp] theorem stdDot_apply {n : ℕ} (v w : Phase n) :
    stdDot n v w = ∑ i, ((v i).re * (w i).re + (v i).im * (w i).im) := by
  simp [stdDot]

theorem stdDot_symm {n : ℕ} (v w : Phase n) : stdDot n v w = stdDot n w v := by
  simp only [stdDot_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem standardForm_J_right {n : ℕ} (v w : Phase n) :
    standardForm v (standardJ n w) = stdDot n v w := by
  simp [standardForm, stdDot_apply, standardJ_apply, Complex.mul_re, Complex.mul_im]

theorem stdDot_pos {n : ℕ} {v : Phase n} (hv : v ≠ 0) : 0 < stdDot n v v := by
  rw [← standardForm_J_right]
  exact standardForm_J_pos hv

theorem stdDot_nonneg {n : ℕ} (v : Phase n) : 0 ≤ stdDot n v v := by
  by_cases hv : v = 0
  · subst v
    simp
  · exact (stdDot_pos hv).le

theorem standardForm_skew {n : ℕ} (v w : Phase n) :
    standardForm v w = -standardForm w v := by
  unfold standardForm
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem standardForm_neg_right {n : ℕ} (v w : Phase n) :
    standardForm v (-w) = -standardForm v w := by
  unfold standardForm
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.neg_apply, Complex.neg_re, Complex.neg_im]
  ring

theorem compatible_metric_symm {n : ℕ} {J : End n} (hJ : Compatible J)
    (v w : Phase n) : standardForm v (J w) = standardForm w (J v) := by
  calc
    standardForm v (J w) = standardForm (J v) (J (J w)) := (hJ.2.1 v (J w)).symm
    _ = -standardForm (J v) w := by rw [hJ.1, standardForm_neg_right]
    _ = standardForm w (J v) := by rw [standardForm_skew, neg_neg]

theorem compatible_of_sq_symmetric_positive {n : ℕ} {J : End n}
    (hJsq : ∀ v, J (J v) = -v)
    (hsym : ∀ v w, standardForm v (J w) = standardForm w (J v))
    (hpos : ∀ v, v ≠ 0 → 0 < standardForm v (J v)) : Compatible J := by
  refine ⟨hJsq, ?_, hpos⟩
  intro v w
  rw [hsym, hJsq, standardForm_neg_right, standardForm_skew, neg_neg]

def relativeOperator {n : ℕ} (J : End n) : End n := -(standardJ n).comp J

@[simp] theorem relativeOperator_apply {n : ℕ} (J : End n) (v : Phase n) :
    relativeOperator J v = -standardJ n (J v) := rfl

@[simp] theorem standardJ_relativeOperator {n : ℕ} (J : End n) (v : Phase n) :
    standardJ n (relativeOperator J v) = J v := by simp

@[simp] theorem relativeOperator_J_relativeOperator {n : ℕ} {J : End n}
    (hJ : Compatible J) (v : Phase n) :
    relativeOperator J (standardJ n (relativeOperator J v)) = standardJ n v := by
  rw [standardJ_relativeOperator, relativeOperator_apply, hJ.1]
  simp

@[simp] theorem stdDot_relativeOperator {n : ℕ} (J : End n) (v w : Phase n) :
    stdDot n v (relativeOperator J w) = standardForm v (J w) := by
  rw [←standardForm_J_right, standardJ_relativeOperator]

theorem relativeOperator_selfadjoint {n : ℕ} {J : End n} (hJ : Compatible J)
    (v w : Phase n) :
    stdDot n (relativeOperator J v) w = stdDot n v (relativeOperator J w) := by
  rw [stdDot_symm, stdDot_relativeOperator, stdDot_relativeOperator]
  exact compatible_metric_symm hJ w v

theorem relativeOperator_positive {n : ℕ} {J : End n} (hJ : Compatible J)
    {v : Phase n} (hv : v ≠ 0) : 0 < stdDot n v (relativeOperator J v) := by
  rw [stdDot_relativeOperator]
  exact hJ.2.2 v hv

def cayleyP {n : ℕ} (J : End n) (a b : ℝ) : End n :=
  a • relativeOperator J + b • ContinuousLinearMap.id ℝ (Phase n)

@[simp] theorem cayleyP_apply {n : ℕ} (J : End n) (a b : ℝ) (v : Phase n) :
    cayleyP J a b v = a • relativeOperator J v + b • v := rfl

theorem cayleyP_invertible {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : (cayleyP J b a).IsInvertible := by
  have hi : Injective (cayleyP J b a) := by
    apply (injective_iff_map_eq_zero (cayleyP J b a)).mpr
    intro v hv
    by_contra hne
    have hp := stdDot_pos hne
    have hA := relativeOperator_positive hJ hne
    have he : stdDot n v (cayleyP J b a v) =
        b * stdDot n v (relativeOperator J v) + a * stdDot n v v := by
      simp only [cayleyP_apply, map_add, map_smul, smul_eq_mul]
    rw [hv] at he
    simp only [map_zero] at he
    have hn := mul_nonneg hb hA.le
    have hh := mul_pos ha hp
    linarith
  have hs := (LinearMap.injective_iff_surjective (f := (cayleyP J b a).toLinearMap)).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective (cayleyP J b a)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs), rfl⟩

theorem cayleyP_commute {n : ℕ} (J : End n) (a b : ℝ) (v : Phase n) :
    cayleyP J b a (cayleyP J a b v) = cayleyP J a b (cayleyP J b a v) := by
  simp only [cayleyP_apply, map_add, map_smul]
  module

theorem cayleyP_J_identity {n : ℕ} {J : End n} (hJ : Compatible J)
    (a b : ℝ) (v : Phase n) :
    cayleyP J a b (standardJ n (cayleyP J a b v)) =
      cayleyP J b a (standardJ n (cayleyP J b a v)) := by
  simp only [cayleyP_apply, map_add, map_smul, relativeOperator_J_relativeOperator hJ]
  module

theorem cayleyP_stdDot_identity {n : ℕ} {J : End n} (hJ : Compatible J)
    (a b : ℝ) (v w : Phase n) :
    stdDot n (cayleyP J b a v) (cayleyP J a b w) =
      stdDot n (cayleyP J a b v) (cayleyP J b a w) := by
  simp only [cayleyP_apply, map_add, map_smul,
    add_apply, smul_apply, smul_eq_mul]
  rw [relativeOperator_selfadjoint hJ v w]
  ring

theorem cayleyP_stdDot_positive {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) {v : Phase n} (hv : v ≠ 0) :
    0 < stdDot n (cayleyP J b a v) (cayleyP J a b v) := by
  have he : stdDot n (cayleyP J b a v) (cayleyP J a b v) =
      a * b * (stdDot n (relativeOperator J v) (relativeOperator J v) + stdDot n v v) +
      (a ^ 2 + b ^ 2) * stdDot n v (relativeOperator J v) := by
    simp only [cayleyP_apply, map_add, map_smul,
      add_apply, smul_apply, smul_eq_mul]
    rw [relativeOperator_selfadjoint hJ v v]
    ring
  rw [he]
  have hfirst : 0 ≤ a * b *
      (stdDot n (relativeOperator J v) (relativeOperator J v) + stdDot n v v) :=
    mul_nonneg (mul_nonneg ha.le hb) (add_nonneg (stdDot_nonneg _) (stdDot_nonneg _))
  have hcoeff : 0 < a ^ 2 + b ^ 2 := by nlinarith [sq_pos_of_pos ha, sq_nonneg b]
  exact add_pos_of_nonneg_of_pos hfirst (mul_pos hcoeff (relativeOperator_positive hJ hv))

def cayleyOperator {n : ℕ} (J : End n) (a b : ℝ) : End n :=
  (cayleyP J a b).comp (cayleyP J b a).inverse

theorem cayleyOperator_on_denominator {n : ℕ} {J : End n} {a b : ℝ}
    (hQ : (cayleyP J b a).IsInvertible) (v : Phase n) :
    cayleyOperator J a b (cayleyP J b a v) = cayleyP J a b v := by
  obtain ⟨e,he⟩ := hQ
  simp only [cayleyOperator, ←he, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

theorem denominator_cayleyOperator {n : ℕ} {J : End n} {a b : ℝ}
    (hQ : (cayleyP J b a).IsInvertible) (v : Phase n) :
    cayleyP J b a (cayleyOperator J a b v) = cayleyP J a b v := by
  change cayleyP J b a (cayleyP J a b ((cayleyP J b a).inverse v)) = _
  rw [cayleyP_commute]
  obtain ⟨e,he⟩ := hQ
  simp [←he]

theorem cayleyOperator_selfadjoint {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (hQ : (cayleyP J b a).IsInvertible) (v w : Phase n) :
    stdDot n (cayleyOperator J a b v) w = stdDot n v (cayleyOperator J a b w) := by
  obtain ⟨e,he⟩ := hQ
  obtain ⟨x,rfl⟩ := e.surjective v
  obtain ⟨y,rfl⟩ := e.surjective w
  change stdDot n (cayleyOperator J a b ((e : End n) x)) ((e : End n) y) =
    stdDot n ((e : End n) x) (cayleyOperator J a b ((e : End n) y))
  rw [he, cayleyOperator_on_denominator ⟨e,he⟩,
    cayleyOperator_on_denominator ⟨e,he⟩]
  exact (cayleyP_stdDot_identity hJ a b x y).symm

theorem cayleyOperator_positive {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) {v : Phase n} (hv : v ≠ 0) :
    0 < stdDot n v (cayleyOperator J a b v) := by
  obtain ⟨e,he⟩ := cayleyP_invertible hJ ha hb
  obtain ⟨x,rfl⟩ := e.surjective v
  have hx : x ≠ 0 := by simpa using hv
  change 0 < stdDot n ((e : End n) x) (cayleyOperator J a b ((e : End n) x))
  rw [he, cayleyOperator_on_denominator ⟨e,he⟩]
  exact cayleyP_stdDot_positive hJ ha hb hx

theorem cayleyOperator_J_identity {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (hQ : (cayleyP J b a).IsInvertible) (v : Phase n) :
    cayleyOperator J a b (standardJ n (cayleyOperator J a b v)) = standardJ n v := by
  obtain ⟨e,he⟩ := hQ
  obtain ⟨x,rfl⟩ := e.surjective v
  apply e.injective
  change (e : End n) (cayleyOperator J a b (standardJ n (cayleyOperator J a b ((e : End n) x)))) =
    (e : End n) (standardJ n ((e : End n) x))
  rw [he, denominator_cayleyOperator ⟨e,he⟩, cayleyOperator_on_denominator ⟨e,he⟩]
  exact cayleyP_J_identity hJ a b x

def interpolateJ {n : ℕ} (J : End n) (t : ℝ) : End n :=
  (standardJ n).comp (cayleyOperator J (1 + t) (1 - t))

theorem compatible_interpolateJ {n : ℕ} {J : End n} (hJ : Compatible J)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : Compatible (interpolateJ J t) := by
  have ha : 0 < 1 + t := by linarith [ht.1]
  have hb : 0 ≤ 1 - t := by linarith [ht.2]
  have hQ := cayleyP_invertible hJ ha hb
  apply compatible_of_sq_symmetric_positive
  · intro v
    change standardJ n (cayleyOperator J (1+t) (1-t)
      (standardJ n (cayleyOperator J (1+t) (1-t) v))) = -v
    rw [cayleyOperator_J_identity hJ hQ, standardJ_sq]
  · intro v w
    change standardForm v (standardJ n (cayleyOperator J (1+t) (1-t) w)) =
      standardForm w (standardJ n (cayleyOperator J (1+t) (1-t) v))
    rw [standardForm_J_right, standardForm_J_right,
      ←cayleyOperator_selfadjoint hJ hQ, stdDot_symm]
  · intro v hv
    change 0 < standardForm v (standardJ n (cayleyOperator J (1+t) (1-t) v))
    rw [standardForm_J_right]
    exact cayleyOperator_positive hJ ha hb hv

@[simp] theorem interpolateJ_zero {n : ℕ} {J : End n} (hJ : Compatible J) :
    interpolateJ J 0 = standardJ n := by
  have hQ := cayleyP_invertible hJ (a := 1) (b := 1) (by norm_num) (by norm_num)
  obtain ⟨e,he⟩ := hQ
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator J (1+0) (1-0) ((e : End n) x)) = standardJ n ((e : End n) x)
  simp only [add_zero, sub_zero, he, cayleyOperator_on_denominator ⟨e,he⟩]

@[simp] theorem interpolateJ_one {n : ℕ} {J : End n} (hJ : Compatible J) :
    interpolateJ J 1 = J := by
  have hQ := cayleyP_invertible hJ (a := 2) (b := 0) (by norm_num) (by norm_num)
  obtain ⟨e,he⟩ := hQ
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator J (1+1) (1-1) ((e : End n) x)) = J ((e : End n) x)
  norm_num only [he, show (1:ℝ)+1=2 by norm_num, sub_self,
    cayleyOperator_on_denominator ⟨e,he⟩]
  simp

theorem contDiffAt_interpolateJ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {J : E → End n} {t : E → ℝ} {x : E}
    (hJs : ContDiffAt ℝ ∞ J x) (hts : ContDiffAt ℝ ∞ t x)
    (hJ : Compatible (J x)) (ht : t x ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun y => interpolateJ (J y) (t y)) x := by
  have hA : ContDiffAt ℝ ∞ (fun y => relativeOperator (J y)) x :=
    (contDiffAt_const.clm_comp hJs).neg
  have ha : ContDiffAt ℝ ∞ (fun y => 1 + t y) x := contDiffAt_const.add hts
  have hb : ContDiffAt ℝ ∞ (fun y => 1 - t y) x := contDiffAt_const.sub hts
  have hP : ContDiffAt ℝ ∞ (fun y => cayleyP (J y) (1+t y) (1-t y)) x :=
    (ha.smul hA).add (hb.smul contDiffAt_const)
  have hQ : ContDiffAt ℝ ∞ (fun y => cayleyP (J y) (1-t y) (1+t y)) x :=
    (hb.smul hA).add (ha.smul contDiffAt_const)
  have hQi := cayleyP_invertible hJ (show 0 < 1 + t x by linarith [ht.1])
    (show 0 ≤ 1 - t x by linarith [ht.2])
  have hI : ContDiffAt ℝ ∞ (fun y => (cayleyP (J y) (1-t y) (1+t y)).inverse) x :=
    ContDiffAt.comp x (g := ContinuousLinearMap.inverse)
      (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (n := ∞) hQi) hQ
  exact contDiffAt_const.clm_comp (hP.clm_comp hI)

end HigherDimensionalBallPacking.Rigidity

end

end OAI
