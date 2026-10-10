import OAI.Analysis.SignedDisk.SignedRuns1

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace DiskMoments
lemma signedAverage_hasCompactSupport {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (fun x => signedAverage g x t) := by
  have he : RadiusEnvelope.envelope (fun s x => signedAverage g x s) t t =
      fun x => signedAverage g x t := by
    funext x
    obtain ⟨s,hs,he,_⟩ := RadiusEnvelope.attains (u := fun s x => signedAverage g x s) (a := t) (b := t) le_rfl x (signedAverage_radius_continuousOn hg x ht)
    have hst : s = t := le_antisymm hs.2 hs.1
    simpa only [hst] using he
  rw [← he]
  exact run_envelope_hasCompactSupport hg hc ht le_rfl
end DiskMoments

namespace SignedRuns
open DiskMoments ActualLabels

def Regular (f : ℂ → ℂ) : Prop := HasCompactSupport f ∧ ∃ L : ℝ≥0, LipschitzWith L f

lemma regular_zero : Regular (fun _ : ℂ => (0:ℂ)) :=
  ⟨HasCompactSupport.zero,0,LipschitzWith.const 0⟩

lemma regular_add {f g : ℂ → ℂ} (hf : Regular f) (hg : Regular g) :
    Regular (fun x => f x+g x) := by
  obtain ⟨hfC,L,hfL⟩ := hf
  obtain ⟨hgC,K,hgL⟩ := hg
  exact ⟨hfC.add hgC,L+K,hfL.add hgL⟩

lemma regular_scalar {f : ℂ → ℝ} (hc : HasCompactSupport f) {L : ℝ≥0}
    (hf : LipschitzWith L f) (n : Label) : Regular (fun x => f x • (n:ℂ)) := by
  refine ⟨hc.smul_right,L,?_⟩
  rw [lipschitzWith_iff_norm_sub_le] at hf ⊢
  intro x y
  simpa only [← sub_smul,norm_smul,label_unit,mul_one] using hf x y

lemma regular_listSum {α : Type*} (l : List α) (f : α → ℂ → ℂ)
    (hf : ∀ a ∈ l, Regular (f a)) : Regular (fun x => (l.map fun a => f a x).sum) := by
  induction l with
  | nil => exact regular_zero
  | cons a l ih =>
    exact regular_add (hf a (by simp)) (ih (fun b hb => hf b (by simp [hb])))

lemma runTerm_regular {g : ℂ → ℝ} {r : ℕ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (a : Run) (ha : a.first ≤ a.last) :
    Regular (fun x => (runEnvelope g r a.first a.last x-signedAverage g x (r a.first)) • (a.dir:ℂ)) := by
  have hab : r a.last ≤ 2*r a.first := by
    have := radius_antitone r hr hstep ha
    linarith [hr a.first]
  obtain ⟨L,hL⟩ := run_envelope_lipschitz hg hgc (hr a.last) hab
  obtain ⟨K,hK⟩ := hg.lipschitzWith_of_hasCompactSupport hgc one_ne_zero
  apply regular_scalar
    ((run_envelope_hasCompactSupport hg hgc (hr a.last) hab).sub (signedAverage_hasCompactSupport hg hgc (hr a.first)))
    (hL.sub (signedAverage_lipschitz hK (hr a.first)))

/-- Every exact history potential is compactly supported and Lipschitz, as
needed for signed weighted integration by parts. -/
theorem potential_regular {g : ℂ → ℝ} {r : ℕ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (p : List Label) : Regular (fun x => potential g r x p) := by
  cases p with
  | nil => exact regular_zero
  | cons n p =>
    simp_rw [potential_eq_runs]
    exact regular_listSum (runs (n::p)) _ (fun a ha =>
      runTerm_regular hg hgc hr hstep a (runs_bounds n p a ha).1)

open Complex

def divergence (V : ℂ → ℂ) (x : ℂ) : ℝ :=
  fderiv ℝ (fun y => (V y).re) x 1+fderiv ℝ (fun y => (V y).im) x I

lemma inner_coordinates (z w : ℂ) :
    inner ℝ z w = inner ℝ z (1:ℂ)*w.re+inner ℝ z I*w.im := by
  conv_lhs => rw [← Complex.re_add_im w]
  rw [inner_add_right]
  have hre : (w.re:ℂ) = w.re • (1:ℂ) := by simp
  have him : (w.im:ℂ)*I = w.im • I := by rw [Complex.real_smul]
  rw [hre,him,real_inner_smul_right,real_inner_smul_right]
  ring

lemma gradient_aestronglyMeasurable (f : ℂ → ℝ) : AEStronglyMeasurable (gradient f) :=
  ((InnerProductSpace.toDual ℝ ℂ).symm.continuous.measurable.comp
    (measurable_fderiv ℝ f)).aestronglyMeasurable

lemma gradient_norm_le {f : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : ℂ) :
    ‖gradient f x‖ ≤ (L:ℝ) := by
  simpa only [gradient,(InnerProductSpace.toDual ℝ ℂ).symm.norm_map] using
    (norm_fderiv_le_of_lipschitz ℝ hf : ‖fderiv ℝ f x‖ ≤ (L:ℝ))

lemma integrable_fderiv_apply {f : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hc : HasCompactSupport f) (v : ℂ) : Integrable (fun x => fderiv ℝ f x v) := by
  have hi := (innerSL ℝ v).integrable_comp (SignedDisk.LipschitzWith.integrable_gradient (μ := volume) hf hc)
  apply hi.congr
  filter_upwards with x
  change inner ℝ v (gradient f x) = _
  rw [real_inner_comm,gradient,InnerProductSpace.toDual_symm_apply]

lemma integrable_gradient_mul {f g : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hg : Integrable g) (v : ℂ) : Integrable (fun x => inner ℝ (gradient f x) v*g x) := by
  apply hg.bdd_mul ((gradient_aestronglyMeasurable f).inner aestronglyMeasurable_const)
  filter_upwards with x
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (gradient_norm_le hf x) (norm_nonneg v))

lemma regular_integrable (V : ℂ → ℂ) (hV : Regular V) : Integrable V := by
  obtain ⟨hc,L,hL⟩ := hV
  exact hL.continuous.integrable_of_hasCompactSupport hc

lemma weighted_divergence_integrable {w : ℂ → ℝ} {K : ℝ≥0} (hw : LipschitzWith K w)
    (hb : ∀ x, ‖w x‖ ≤ 1) {V : ℂ → ℂ} (hV : Regular V) :
    Integrable (fun x => w x*divergence V x) := by
  obtain ⟨hc,L,hL⟩ := hV
  have hr := integrable_fderiv_apply (Complex.reCLM.lipschitzWith.comp hL)
    (hc.comp_left (map_zero Complex.reCLM)) (1:ℂ)
  have hi := integrable_fderiv_apply (Complex.imCLM.lipschitzWith.comp hL)
    (hc.comp_left (map_zero Complex.imCLM)) I
  exact (hr.add hi).bdd_mul hw.continuous.aestronglyMeasurable (ae_of_all _ hb)

lemma potential_flux_integrable {w : ℂ → ℝ} {K : ℝ≥0} (hw : LipschitzWith K w)
    {V : ℂ → ℂ} (hV : Regular V) :
    Integrable (fun x => inner ℝ (gradient w x) (V x)) := by
  have hi := regular_integrable V hV
  apply (hi.norm.const_mul (K:ℝ)).mono'
    ((gradient_aestronglyMeasurable w).inner hi.aestronglyMeasurable)
  filter_upwards with x
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (gradient_norm_le hw x) (norm_nonneg _))

/-- Weighted vector integration by parts for the actual class of compact
Lipschitz path potentials and bounded Lipschitz spatial history weights. -/
theorem vector_weighted_ibp {w : ℂ → ℝ} {K : ℝ≥0} (hw : LipschitzWith K w)
    (hb : ∀ x, ‖w x‖ ≤ 1) {V : ℂ → ℂ} (hV : Regular V) :
    (∫ x, w x*divergence V x) = -∫ x, inner ℝ (gradient w x) (V x) := by
  obtain ⟨hc,L,hL⟩ := hV
  have hrL := Complex.reCLM.lipschitzWith.comp hL
  have hiL := Complex.imCLM.lipschitzWith.comp hL
  have hrC := hc.comp_left (map_zero Complex.reCLM)
  have hiC := hc.comp_left (map_zero Complex.imCLM)
  have hr := (integrable_fderiv_apply hrL hrC (1:ℂ)).bdd_mul
    hw.continuous.aestronglyMeasurable (ae_of_all _ hb)
  have hi := (integrable_fderiv_apply hiL hiC I).bdd_mul
    hw.continuous.aestronglyMeasurable (ae_of_all _ hb)
  have hrr := integrable_gradient_mul hw (hrL.continuous.integrable_of_hasCompactSupport hrC) (1:ℂ)
  have hir := integrable_gradient_mul hw (hiL.continuous.integrable_of_hasCompactSupport hiC) I
  change (∫ x, w x*(fderiv ℝ (Complex.reCLM ∘ V) x 1+fderiv ℝ (Complex.imCLM ∘ V) x I)) = _
  simp only [mul_add]
  rw [integral_add hr hi,SignedDisk.LipschitzWith.integral_mul_fderiv_eq_neg hw hrL hrC (1:ℂ),
    SignedDisk.LipschitzWith.integral_mul_fderiv_eq_neg hw hiL hiC I,← neg_add,← integral_add hrr hir]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  exact (inner_coordinates _ _).symm

open ActualLabels FiniteLabels SignedAssembly Finset DiskMoments

lemma leafSum_add (f g : List Label → ℝ) (d : ℕ) (p : List Label) :
    leafSum (fun q => f q+g q) d p = leafSum f d p+leafSum g d p := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih => simp only [leafSum,ih,sum_add_distrib]

lemma leafSum_mul_const (f : List Label → ℝ) (c : ℝ) (d : ℕ) (p : List Label) :
    leafSum (fun q => f q*c) d p = leafSum f d p*c := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih => simp only [leafSum,ih,sum_mul]

lemma leafSum_const_mul (f : List Label → ℝ) (c : ℝ) (d : ℕ) (p : List Label) :
    leafSum (fun q => c*f q) d p = c*leafSum f d p := by
  simpa only [mul_comm] using leafSum_mul_const f c d p

lemma leafSum_neg (f : List Label → ℝ) (d : ℕ) (p : List Label) :
    leafSum (fun q => -(f q)) d p = -leafSum f d p := by
  simpa only [neg_one_mul] using leafSum_const_mul f (-1) d p

lemma leafSum_mono (f g : List Label → ℝ) (d : ℕ) (p : List Label)
    (hle : ∀ q, q.length = p.length+d → f q ≤ g q) : leafSum f d p ≤ leafSum g d p := by
  induction d generalizing p with
  | zero => exact hle p (by simp)
  | succ d ih =>
    apply sum_le_sum
    intro n _
    apply ih
    intro q hq
    apply hle q
    simp only [List.length_cons] at hq
    omega

lemma leafSum_congr (f g : List Label → ℝ) (d : ℕ) (p : List Label)
    (he : ∀ q, q.length = p.length+d → f q = g q) : leafSum f d p = leafSum g d p :=
  le_antisymm (leafSum_mono f g d p (fun q hq => (he q hq).le))
    (leafSum_mono g f d p (fun q hq => (he q hq).ge))

lemma leafSum_weight (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ) (d : ℕ) (p : List Label) :
    leafSum (weight h r old x) d p = weight h r old x p := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih =>
    simp only [leafSum,ih,weight,← mul_sum,(observation h r p.length x (p.headD old)).total,mul_one]

lemma leafSum_integrable (f : List Label → ℂ → ℝ) (hf : ∀ q, Integrable (f q))
    (d : ℕ) (p : List Label) : Integrable (fun x => leafSum (fun q => f q x) d p) := by
  induction d generalizing p with
  | zero => exact hf p
  | succ d ih => exact integrable_finsetSum _ (fun n _ => ih (n::p))

lemma integral_leafSum (f : List Label → ℂ → ℝ) (hf : ∀ q, Integrable (f q))
    (d : ℕ) (p : List Label) :
    (∫ x, leafSum (fun q => f q x) d p) = leafSum (fun q => ∫ x, f q x) d p := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih =>
    simp only [leafSum]
    rw [integral_finsetSum _ (fun n _ => leafSum_integrable f hf d (n::p))]
    exact sum_congr rfl (fun n _ => ih (n::p))

theorem history_weighted_ibp (g : ℂ → ℝ) (h : ℂ → ℂ) (r : ℕ → ℝ)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (old : Label) (m : ℕ) :
    (∫ x, leafSum (fun q => weight h r old x q*divergence (fun y => potential g r y q) x) m []) =
      -∫ x, leafSum (fun q => inner ℝ (gradient (fun y => weight h r old y q) x) (potential g r x q)) m [] := by
  have hreg (q : List Label) := potential_regular hg hc hr hstep q
  have hint (q : List Label) : Integrable (fun x => weight h r old x q*divergence (fun y => potential g r y q) x) := by
    obtain ⟨K,hK⟩ := weight_lipschitz h r hr old q
    apply weighted_divergence_integrable hK _ (hreg q)
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (weight_nonneg h r old x q)]
    exact weight_le_one h r old x q
  have hflux (q : List Label) : Integrable (fun x => inner ℝ (gradient (fun y => weight h r old y q) x) (potential g r x q)) := by
    obtain ⟨K,hK⟩ := weight_lipschitz h r hr old q
    exact potential_flux_integrable hK (hreg q)
  rw [integral_leafSum _ hint,integral_leafSum _ hflux,← leafSum_neg]
  apply leafSum_congr
  intro q _
  obtain ⟨K,hK⟩ := weight_lipschitz h r hr old q
  apply vector_weighted_ibp hK _ (hreg q)
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (weight_nonneg h r old x q)]
  exact weight_le_one h r old x q

/-- Averaging preserves the complete signed run-master inequality; finite
history weights sum to one at every observation point. -/
theorem expected_run_master (g : ℂ → ℝ) (h : ℂ → ℂ) (r : ℕ → ℝ)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (old : Label) (m : ℕ) (x : ℂ)
    (hd : ∀ i j, i ≤ j → DifferentiableAt ℝ (runEnvelope g r i j) x) :
    ‖gradient (runEnvelope g r 0 m) x‖ ≤
      12*leafSum (fun q => weight h r old x q*((runs q).map fun a => coneContribution a.dir
        (gradient (runEnvelope g r a.first a.last) x)).sum) (m+1) [] := by
  have hh := leafSum_mono
    (fun q => weight h r old x q*‖gradient (runEnvelope g r 0 m) x‖)
    (fun q => weight h r old x q*(12*((runs q).map fun a => coneContribution a.dir
        (gradient (runEnvelope g r a.first a.last) x)).sum)) (m+1) [] (by
      intro q hq
      cases q with
      | nil => simp at hq
      | cons n p =>
        have hp : p.length = m := by simpa using hq
        apply mul_le_mul_of_nonneg_left _ (weight_nonneg h r old x (n::p))
        simpa only [hp] using run_master hg hc hr hstep n p x hd)
  rw [leafSum_mul_const,leafSum_weight,weight,one_mul] at hh
  have he : (fun q => weight h r old x q*(12*((runs q).map fun a => coneContribution a.dir
        (gradient (runEnvelope g r a.first a.last) x)).sum)) =
      (fun q => 12*(weight h r old x q*((runs q).map fun a => coneContribution a.dir
        (gradient (runEnvelope g r a.first a.last) x)).sum)) := by funext q; ring
  rw [he,leafSum_const_mul] at hh
  exact hh

open DiskMoments ActualLabels Complex

lemma divergence_add {U V : ℂ → ℂ} {x : ℂ}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x) :
    divergence (fun y => U y+V y) x = divergence U x+divergence V x := by
  have hUr : DifferentiableAt ℝ (fun y => (U y).re) x := Complex.reCLM.differentiableAt.comp x hU
  have hVr : DifferentiableAt ℝ (fun y => (V y).re) x := Complex.reCLM.differentiableAt.comp x hV
  have hUi : DifferentiableAt ℝ (fun y => (U y).im) x := Complex.imCLM.differentiableAt.comp x hU
  have hVi : DifferentiableAt ℝ (fun y => (V y).im) x := Complex.imCLM.differentiableAt.comp x hV
  simp only [divergence,Complex.add_re,Complex.add_im]
  rw [fderiv_fun_add hUr hVr,fderiv_fun_add hUi hVi]
  simp only [_root_.add_apply]
  ring

lemma divergence_scalar {f : ℂ → ℝ} {x : ℂ} (hf : DifferentiableAt ℝ f x) (n : ℂ) :
    divergence (fun y => f y • n) x = inner ℝ n (gradient f x) := by
  simp only [divergence,Complex.real_smul,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
  rw [fderiv_mul_const hf n.re,fderiv_mul_const hf n.im]
  simp only [_root_.smul_apply,smul_eq_mul]
  rw [real_inner_comm,inner_coordinates]
  simp only [gradient,InnerProductSpace.toDual_symm_apply]
  ring

lemma listSum_diff {α : Type*} (l : List α) (V : α → ℂ → ℂ) {x : ℂ}
    (hd : ∀ a ∈ l, DifferentiableAt ℝ (V a) x) :
    DifferentiableAt ℝ (fun y => (l.map fun a => V a y).sum) x := by
  induction l with
  | nil => exact differentiableAt_const 0
  | cons a l ih =>
    exact (hd a (by simp)).add (ih (fun a ha => hd a (by simp [ha])))

lemma divergence_listSum {α : Type*} (l : List α) (V : α → ℂ → ℂ) {x : ℂ}
    (hd : ∀ a ∈ l, DifferentiableAt ℝ (V a) x) :
    divergence (fun y => (l.map fun a => V a y).sum) x = (l.map fun a => divergence (V a) x).sum := by
  induction l with
  | nil => simp [divergence]
  | cons a l ih =>
    have hs := listSum_diff l V (fun b hb => hd b (by simp [hb]))
    simp only [List.map_cons,List.sum_cons]
    rw [divergence_add (hd a (by simp)) hs,ih (fun b hb => hd b (by simp [hb]))]

lemma average_diff {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (x : ℂ) {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ (fun y => signedAverage g y t) x := by
  obtain ⟨K,hK⟩ := hg.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  exact (hasFDerivAt_signedAverage hg (fun y => norm_fderiv_le_of_lipschitz ℝ hK) x ht).differentiableAt

/-- The divergence of the exact path potential is the complete signed sum
of run gradients, with precisely the starting-baseline gradients removed. -/
lemma potential_divergence {g : ℂ → ℝ} {r : ℕ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (hr : ∀ k, 0 < r k) (p : List Label) (x : ℂ)
    (hd : ∀ i j, i ≤ j → DifferentiableAt ℝ (runEnvelope g r i j) x) :
    divergence (fun y => potential g r y p) x =
      ((runs p).map fun a => inner ℝ (a.dir:ℂ)
        (gradient (runEnvelope g r a.first a.last) x-gradient (fun y => signedAverage g y (r a.first)) x)).sum := by
  cases p with
  | nil => simp [potential,runs,divergence]
  | cons n p =>
    simp_rw [potential_eq_runs]
    have hd' (a : Run) (ha : a ∈ runs (n::p)) :
        DifferentiableAt ℝ (fun y => runEnvelope g r a.first a.last y-signedAverage g y (r a.first)) x :=
      (hd a.first a.last (runs_bounds n p a ha).1).sub (average_diff hg hgc x (hr a.first))
    rw [divergence_listSum _ _ (fun a ha => (hd' a ha).smul_const (a.dir:ℂ))]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a ha
    rw [divergence_scalar (hd' a ha)]
    congr 1
    simp only [gradient]
    rw [fderiv_fun_sub (hd a.first a.last (runs_bounds n p a ha).1) (average_diff hg hgc x (hr a.first)),map_sub]

open DiskMoments ActualLabels Finset ConeCoordinates

lemma radius_in_run_bin (r : ℕ → ℝ) (hstep : ∀ k, 2*r (k+1) = r k)
    {i j : ℕ} (hij : i ≤ j) {t : ℝ} (ht : t ∈ Icc (r j) (2*r i)) :
    ∃ k ∈ Set.Icc i j, t ∈ Icc (r k) (2*r k) := by
  obtain ⟨l,hl,htl⟩ := radius_in_bin (fun k => r (i+k))
    (fun k => by simpa [Nat.add_assoc] using hstep (i+k)) (j-i)
    (by simpa only [Nat.add_sub_of_le hij,Nat.add_zero] using ht)
  exact ⟨i+l,⟨by omega,by omega⟩,htl⟩

lemma attaining_endpoint {g : ℂ → ℝ} {r : ℕ → ℝ}
    (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    {i j k : ℕ} (hik : i ≤ k) (hkj : k ≤ j) {x : ℂ} {t : ℝ}
    (ht : t ∈ Icc (r k) (2*r k))
    (hmax : ∀ s ∈ Icc (r j) (2*r i), signedAverage g x s ≤ signedAverage g x t) :
    PhysicalEndpointRadius g (r k) x t := by
  refine ⟨ht,Or.inr (Or.inr ?_)⟩
  intro s hs
  apply hmax
  constructor
  · exact (radius_antitone r hr hstep hkj).trans hs.1
  · have := radius_antitone r hr hstep hik
    linarith [hs.2]

lemma attaining_interior {g : ℂ → ℝ} {r : ℕ → ℝ}
    (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    {i j k : ℕ} (hik : i < k) (hkj : k < j) {x : ℂ} {t : ℝ}
    (ht : t ∈ Icc (r k) (2*r k))
    (hmax : ∀ s ∈ Icc (r j) (2*r i), signedAverage g x s ≤ signedAverage g x t) :
    PhysicalNeighborhoodRadius g (r k) x t := by
  refine ⟨ht,?_⟩
  intro s _ hs
  apply hmax
  have hs' := abs_le.mp hs
  have hlow := radius_antitone r hr hstep (show k+1 ≤ j by omega)
  have hhigh := radius_antitone r hr hstep (show i+1 ≤ k by omega)
  constructor <;> linarith [hstep k,hstep i,hr k,ht.1,ht.2]

def unfavorable (n : Label) (z : ℂ) : ℝ :=
  max 0 (-inner ℝ (axis n 1) z)+max 0 (-inner ℝ (axis n (-1)) z)

lemma unfavorable_nonneg (n : Label) (z : ℂ) : 0 ≤ unfavorable n z :=
  add_nonneg (le_max_left _ _) (le_max_left _ _)

lemma unfavorable_le_norm (n : Label) (z : ℂ) : unfavorable n z ≤ 2*‖z‖ := by
  have h (s : ℝ) (hs : s^2 = 1) : max 0 (-inner ℝ (axis n s) z) ≤ ‖z‖ := by
    apply max_le (norm_nonneg _)
    have hh := abs_real_inner_le_norm (axis (n:ℂ) s) z
    rw [axis_norm (label_unit n) hs,one_mul] at hh
    exact (neg_le_abs _).trans hh
  have hp := h 1 (by norm_num)
  have hm := h (-1) (by norm_num)
  unfold unfavorable
  linarith

/-- The exact unfavorable run term is charged either to one interior bin or
one of its two end bins; padding by nonnegative costs permits summing runs. -/
lemma run_unfavorable_bound {g : ℂ → ℝ} {r : ℕ → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (H : ℕ → Label → ℝ) (J : ℕ → ℝ) (hH : ∀ k n, 0 ≤ H k n) (hJ : ∀ k, 0 ≤ J k)
    (x : ℂ) (n : Label) {i j : ℕ} (hij : i ≤ j)
    (hd : DifferentiableAt ℝ (runEnvelope g r i j) x)
    (hinterior : ∀ k t, PhysicalNeighborhoodRadius g (r k) x t →
      unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H k n)
    (hend : ∀ k t, PhysicalEndpointRadius g (r k) x t →
      ‖gradient (fun y => signedAverage g y t) x‖ ≤ J k) :
    unfavorable n (gradient (runEnvelope g r i j) x) ≤
      (∑ k ∈ Icc i j, H k n)+2*(J i+J j) := by
  obtain ⟨t,ht,he,hm⟩ := runEnvelope_attains g r hg hr hstep hij x
  rw [run_gradient_touching hg hc hr hd ht he]
  obtain ⟨k,hk,hkt⟩ := radius_in_run_bin r hstep hij ht
  have hs : 0 ≤ ∑ k ∈ Icc i j, H k n := sum_nonneg (fun _ _ => hH _ _)
  by_cases hki : k = i
  · subst k
    have hb := (unfavorable_le_norm n _).trans (mul_le_mul_of_nonneg_left
      (hend i t (attaining_endpoint hr hstep le_rfl hij hkt hm)) (by norm_num : (0:ℝ) ≤ 2))
    linarith [hJ j]
  by_cases hkj : k = j
  · subst k
    have hb := (unfavorable_le_norm n _).trans (mul_le_mul_of_nonneg_left
      (hend j t (attaining_endpoint hr hstep hij le_rfl hkt hm)) (by norm_num : (0:ℝ) ≤ 2))
    linarith [hJ i]
  have hik := hk.1
  have hkj' := hk.2
  have hb := hinterior k t (attaining_interior hr hstep (by omega) (by omega) hkt hm)
  have hsum : H k n ≤ ∑ l ∈ Icc i j, H l n := single_le_sum (fun l _ => hH l n) (Finset.mem_Icc.mpr hk)
  linarith [hJ i,hJ j]
end SignedRuns

end SignedDisk

end

end OAI
