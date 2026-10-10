import Mathlib
import OAI.Computability.MinUncut.Analysis.FreshCorrelation

namespace OAI

noncomputable section
open scoped BigOperators
variable {m n : ℕ}
namespace MinUncut.Average

lemma weighted_sqrt_mul_sqrt {T : Type*} [Fintype T] (w a b : T → ℝ)
    (hw : ∀ t, 0 ≤ w t) (ha : ∀ t, 0 ≤ a t) (hb : ∀ t, 0 ≤ b t) :
    (∑ t, w t * (Real.sqrt (a t) * Real.sqrt (b t))) ≤
      Real.sqrt (∑ t, w t*a t) * Real.sqrt (∑ t, w t*b t) := by
  have he t : w t * (Real.sqrt (a t) * Real.sqrt (b t)) =
      Real.sqrt (w t*a t) * Real.sqrt (w t*b t) := by
    rw [Real.sqrt_mul (hw t), Real.sqrt_mul (hw t)]
    calc
      _ = (Real.sqrt (w t))^2 * (Real.sqrt (a t) * Real.sqrt (b t)) := by rw [Real.sq_sqrt (hw t)]
      _ = _ := by ring
  simp_rw [he]
  exact Real.sum_sqrt_mul_sqrt_le _ (fun t => mul_nonneg (hw t) (ha t))
    (fun t => mul_nonneg (hw t) (hb t))

lemma weighted_sqrt {T : Type*} [Fintype T] (w a : T → ℝ)
    (hw : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t=1) (ha : ∀ t, 0 ≤ a t) :
    (∑ t, w t * Real.sqrt (a t)) ≤ Real.sqrt (∑ t, w t*a t) := by
  simpa only [Real.sqrt_one, mul_one, hw1] using
    weighted_sqrt_mul_sqrt w a (fun _ => 1) hw ha (fun _ => by norm_num)

lemma expect_sqrt_mul_sqrt {T : Type*} [Fintype T] (a b : T → ℝ)
    (ha : ∀ t, 0 ≤ a t) (hb : ∀ t, 0 ≤ b t) :
    (𝔼 t, Real.sqrt (a t)*Real.sqrt (b t)) ≤
      Real.sqrt (𝔼 t, a t)*Real.sqrt (𝔼 t, b t) := by
  have h := weighted_sqrt_mul_sqrt (fun _ : T => (Fintype.card T:ℝ)⁻¹) a b
    (fun _ => by positivity) ha hb
  simpa only [← Finset.mul_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv,
    mul_comm (Fintype.card T:ℝ)⁻¹, ← Finset.sum_mul] using h
end MinUncut.Average

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable

lemma faceCorrelation_sum_le {T : Type*} (S : Finset T) (v : T → Point m n → ℝ) :
    faceCorrelation (fun x => ∑ t ∈ S, v t x) ≤ ∑ t ∈ S, faceCorrelation (v t) := by
  apply faceCorrelation_le
  intro z
  simp_rw [Finset.sum_mul, Finset.expect_sum_comm]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun t _ => code_correlation_le (v t) z))

lemma faceCorrelation_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (u : Ω → Point m n → ℝ) (hm : ∀ x, Measurable (fun t => u t x))
    (hi : ∀ x, Integrable (fun t => u t x) μ) :
    Integrable (fun t => faceCorrelation (u t)) μ := by
  have hh : Integrable (fun t => 𝔼 x, |u t x|) μ := by
    simp only [Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun x _ => (hi x).abs)).div_const _
  exact hh.mono' (faceCorrelation_measurable_field u hm).aestronglyMeasurable
    (ae_of_all _ (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (faceCorrelation_nonneg _)]
      exact faceCorrelation_le_l1 _))

variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

def classField (f : FoldedProof A) (σ η : ℝ)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (a : Option (PairClass m))
    (B : FaceArray A m n) (c : Point m n → ℝ) (x : Point m n) : ℝ :=
  selectedProject (classSelection x a J) (fun B c => gradient f B σ η c x) B c

lemma classField_memLp (f : FoldedProof A) (σ η : ℝ)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (a : Option (PairClass m))
    (B : FaceArray A m n) (x : Point m n) :
    MemLp (fun c => classField f σ η J a B c x) 2 (γpi (Point m n)) :=
  memLp_selectedProject _ _ _

lemma classField_measurable (f : FoldedProof A) (σ η : ℝ)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (a : Option (PairClass m))
    (B : FaceArray A m n) (x : Point m n) :
    Measurable (fun c => classField f σ η J a B c x) :=
  (selectedProject_continuous _ _ _).measurable

lemma classField_correlation_integrable (f : FoldedProof A) (σ η : ℝ)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (a : Option (PairClass m))
    (B : FaceArray A m n) :
    Integrable (fun c => faceCorrelation (classField f σ η J a B c)) (γpi (Point m n)) :=
  faceCorrelation_integrable _ (classField_measurable f σ η J a B)
    (fun x => (classField_memLp f σ η J a B x).integrable (by norm_num))

lemma lowGradient_class_partition (D s : ℕ) (f : FoldedProof A) (σ η : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ) (x : Point m n) :
    lowGradient D s f σ η B c x =
      ∑ a : Option (PairClass m), classField f σ η (rectangle D s) a B c x :=
  classSelection_partition x _ _

lemma lowGradient_classes_correlation (D s : ℕ) (f : FoldedProof A) (σ η : ℝ) :
    averagedCorrelation (lowGradient (m := m) (n := n) D s f σ η) ≤
      ∑ a : Option (PairClass m), averagedCorrelation (classField (n := n) f σ η (rectangle D s) a) := by
  have hp (B : FaceArray A m n) (c : Point m n → ℝ) :
      faceCorrelation (lowGradient D s f σ η B c) ≤
        ∑ a : Option (PairClass m), faceCorrelation (classField f σ η (rectangle D s) a B c) := by
    conv_lhs => arg 1; ext x; rw [lowGradient_class_partition]
    exact faceCorrelation_sum_le _ _
  unfold averagedCorrelation
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro B _
  calc
    _ ≤ ∫ c, (∑ a : Option (PairClass m), faceCorrelation (classField f σ η (rectangle D s) a B c)) ∂γpi (Point m n) :=
      integral_mono (lowGradient_correlation_integrable D s f σ η B)
        (integrable_finsetSum _ (fun a _ => classField_correlation_integrable f σ η (rectangle D s) a B)) (hp B)
    _ = _ := integral_finsetSum _ (fun a _ => classField_correlation_integrable f σ η (rectangle D s) a B)
end MinUncut.Inner

namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory GaussianHermite
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [Nonempty W] [Fintype ι]

def jointL1 (u : (R → W) → (ι → ℝ) → ℝ) : ℝ :=
  𝔼 B, ∫ c, |u B c| ∂γpi ι

lemma jointL1_le_sqrt (u : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) : jointL1 u ≤ Real.sqrt (jointEnergy u) := by
  have hi (B : R → W) : (∫ c, |u B c| ∂γpi ι) ≤ Real.sqrt (∫ c, (u B c)^2 ∂γpi ι) := by
    simpa using integral_norm_mul_le_sqrt (hu B) (memLp_const (1:ℝ) (p := 2) (μ := γpi ι))
  exact (Finset.expect_le_expect (fun B _ => hi B)).trans
    (expect_sqrt_le _ (fun B => integral_nonneg (fun c => sq_nonneg _)))
end MinUncut.RowNoise

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma averagedEnergy_eq_expect_joint
    (u : FaceArray A m n → (Point m n → ℝ) → Point m n → ℝ)
    (hu : ∀ B x, MemLp (fun c => u B c x) 2 (γpi (Point m n))) :
    averagedEnergy u = 𝔼 x, jointEnergy (fun B c => u B c x) := by
  rw [averagedEnergy_eq_jointEnergy u hu]
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Point, Fintype.card_fin]
  ring

lemma retainedClass_localized (x : Point m n) {k : ℕ} (Y : PointedBox x k)
    (a : Option (PairClass m)) (J : Finset (Finset (Row m n) × (Point m n → ℕ))) :
    retainedClass x Y a J=localizedSelection x Y (classSelection x a J) := rfl

lemma class_localization_energy (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (hn : 2 ≤ n) {k s D : ℕ} (hk : k ≤ n-1)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j ∈ J, (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ D) (a : Option (PairClass m)) :
    (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, jointEnergy (fun B c =>
      classField f σ η J a B c x-
      selectedProject (retainedClass x Y a J) (fun B c => gradient f B σ η c x) B c)) ≤
      ((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))*σ⁻¹^2 := by
  have : NeZero n := ⟨by omega⟩
  have hnR : 0 ≤ (n:ℝ)-1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let δ : ℝ := ((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))
  have hd : 0 ≤ δ := by dsimp [δ]; positivity
  have hx (x : Point m n) :
      (𝔼 Y : PointedBox x k, jointEnergy (fun B c => classField f σ η J a B c x-
        selectedProject (retainedClass x Y a J) (fun B c => gradient f B σ η c x) B c)) ≤
      δ*jointEnergy (fun B c => gradient f B σ η c x) := by
    have hh := localization_energy_loss (W := Forms A) x (by simpa using hk)
      (classSelection x a J) (fun j hj => hJ j (Finset.mem_filter.mp hj).1)
      (fun B c => gradient f B σ η c x)
    change (𝔼 Y : PointedBox x k, jointEnergy (fun B c => classField f σ η J a B c x-
        selectedProject (retainedClass x Y a J) (fun B c => gradient f B σ η c x) B c)) ≤
      ((s+D:ℕ):ℝ)*((k:ℝ)/(Fintype.card (Fin n)-1))*
        jointEnergy (selectedProject (classSelection x a J) (fun B c => gradient f B σ η c x)) at hh
    simp only [Fintype.card_fin] at hh
    exact hh.trans
      (mul_le_mul_of_nonneg_left
        (selectedProject_energy_le (classSelection x a J) _ (fun B => gradient_memLp f B hσ η x)) hd)
  calc
    _ ≤ 𝔼 x : Point m n, δ*jointEnergy (fun B c => gradient f B σ η c x) :=
      Finset.expect_le_expect (fun x _ => hx x)
    _ = δ*averagedEnergy (fun B c => gradient f B σ η c) := by
      rw [← Finset.mul_expect, averagedEnergy_eq_expect_joint _ (fun B x => gradient_memLp f B hσ η x)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (averagedEnergy_gradient_le f (by omega) hσ η) hd

lemma class_localization_l1 (f : FoldedProof A) {σ : ℝ} (hσ : 0<σ) (η : ℝ)
    (hn : 2 ≤ n) {k s D : ℕ} (hk : k ≤ n-1)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j ∈ J, (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ D) (a : Option (PairClass m)) :
    (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, jointL1 (fun B c =>
      classField f σ η J a B c x-
      selectedProject (retainedClass x Y a J) (fun B c => gradient f B σ η c x) B c)) ≤
      σ⁻¹*Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) := by
  have : NeZero n := ⟨by omega⟩
  have hnR : 0 ≤ (n:ℝ)-1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have (x : Point m n) (i : Fin m) : Nonempty (OuterSmoothness.FixedSets (Away (x i)) k) :=
    OuterSmoothness.fixedSets_nonempty (by simpa [card_away] using hk)
  let u := fun (x : Point m n) (Y : PointedBox x k) B c =>
    classField f σ η J a B c x-
      selectedProject (retainedClass x Y a J) (fun B c => gradient f B σ η c x) B c
  have hu x Y B : MemLp (u x Y B) 2 (γpi (Point m n)) :=
    (classField_memLp f σ η J a B x).sub (memLp_selectedProject _ _ _)
  calc
    _ ≤ 𝔼 x : Point m n, 𝔼 Y : PointedBox x k, Real.sqrt (jointEnergy (u x Y)) :=
      Finset.expect_le_expect (fun x _ => Finset.expect_le_expect (fun Y _ => jointL1_le_sqrt _ (hu x Y)))
    _ ≤ Real.sqrt (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, jointEnergy (u x Y)) := by
      apply le_trans (Finset.expect_le_expect (fun x _ => expect_sqrt_le _ (fun Y => jointEnergy_nonneg (u x Y))))
      exact expect_sqrt_le _ (fun x => Finset.expect_nonneg (fun Y _ => jointEnergy_nonneg (u x Y)))
    _ ≤ Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))*σ⁻¹^2) :=
      Real.sqrt_le_sqrt (class_localization_energy f hσ.ne' η hn hk J hJ a)
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (inv_nonneg.mpr hσ.le), mul_comm]
end MinUncut.Inner

namespace MinUncut.Slice
open MeasureTheory GaussianHermite BinaryFourier
open scoped BigOperators
variable {Ω T W : Type*} [MeasurableSpace Ω] [Fintype T]
  [Fintype W] [AddCommGroup W] [Module F₂ W] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma processed_average_integral_loss (one : W) (v : T → Ω → W → ℝ)
    (hm : ∀ t w, Measurable (fun c => v t c w))
    (hv : ∀ t w, MemLp (fun c => v t c w) 2 μ)
    {H γ A : ℝ} (hH : 0<H) (hγ : 0<γ) (hA : 0<A) :
    (𝔼 t, ∫ c, (𝔼 w, |v t c w-processed H γ A one (v t c) w|) ∂μ) ≤
      (𝔼 t, ∫ c, energy (v t) c ∂μ)/H +
      Real.sqrt (𝔼 t, ∫ c, energy (v t) c ∂μ)*
        Real.sqrt ((𝔼 t, ∫ c, oddMax one (v t c) ∂μ)/γ) +
      (𝔼 t, ∫ c, energy (v t) c ∂μ)/A := by
  classical
  have he t : 0≤∫ c, energy (v t) c ∂μ := integral_nonneg (energy_nonneg (v t))
  have hq t : 0≤(∫ c, oddMax one (v t c) ∂μ)/γ :=
    div_nonneg (integral_nonneg (fun c => oddMax_nonneg one (v t c))) hγ.le
  calc
    _ ≤ 𝔼 t, ((∫ c, energy (v t) c ∂μ)/H +
        Real.sqrt (∫ c, energy (v t) c ∂μ)*Real.sqrt ((∫ c, oddMax one (v t c) ∂μ)/γ) +
        (∫ c, energy (v t) c ∂μ)/A) :=
      Finset.expect_le_expect (fun t _ => processed_integral_loss one (v t) (hm t) (hv t) hH hγ hA)
    _ = (𝔼 t, ∫ c, energy (v t) c ∂μ)/H +
        (𝔼 t, Real.sqrt (∫ c, energy (v t) c ∂μ)*Real.sqrt ((∫ c, oddMax one (v t c) ∂μ)/γ)) +
        (𝔼 t, ∫ c, energy (v t) c ∂μ)/A := by
      simp only [Finset.expect_add_distrib, Finset.expect_div]
    _ ≤ _ := by
      have hcs := Average.expect_sqrt_mul_sqrt
        (fun t => ∫ c, energy (v t) c ∂μ) (fun t => (∫ c, oddMax one (v t c) ∂μ)/γ) he hq
      rw [← Finset.expect_div] at hcs
      linarith only [hcs]
end MinUncut.Slice

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

def pairProcessed (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ A₀ : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ) : ℝ :=
  Slice.processed H γ A₀ (AffineMap.const F₂ A 1) (pairSlice f σ η x Y p J B c)
    (B ⟨p.val.1,face x p.val.1⟩+B ⟨p.val.2,face x p.val.2⟩)

lemma pairSlice_resample (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (B : FaceArray A m n) (b : Forms A) :
    pairSlice f σ η x Y p J (joinRow ⟨p.val.1,face x p.val.1⟩ b (fun t => B t.val)) =
      pairSlice f σ η x Y p J B := by
  apply pairSlice_background
  intro t ht
  have htr : t≠⟨p.val.1,face x p.val.1⟩ := by
    rintro rfl
    exact ht (local_free_left x Y p)
  exact joinRow_other _ _ _ ⟨t,htr⟩

attribute [local irreducible] gradient selectedProject retainedClass pairSlice pairProcessed Slice.processed

lemma pair_processing_loss_law (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ A₀ : ℝ) (c : Point m n → ℝ) :
    (𝔼 B : FaceArray A m n, |selectedProject (retainedClass x Y (some p) J)
      (fun B c => gradient f B σ η c x) B c - pairProcessed f σ η x Y p J H γ A₀ B c|) =
    𝔼 B : FaceArray A m n, 𝔼 b : Forms A, |pairSlice f σ η x Y p J B c b -
      Slice.processed H γ A₀ (AffineMap.const F₂ A 1) (pairSlice f σ η x Y p J B c) b| := by
  let r : Row m n := ⟨p.val.1,face x p.val.1⟩
  let s : Row m n := ⟨p.val.2,face x p.val.2⟩
  have hsr : s≠r := by
    intro h
    exact (ne_of_lt p.property) (congrArg Sigma.fst h).symm
  let L := fun B : FaceArray A m n => |selectedProject (retainedClass x Y (some p) J)
      (fun B c => gradient f B σ η c x) B c - pairProcessed f σ η x Y p J H γ A₀ B c|
  have hB (B : FaceArray A m n) :
      (𝔼 b : Forms A, L (joinRow r b (fun t => B t.val))) =
      𝔼 b : Forms A, |pairSlice f σ η x Y p J B c b -
        Slice.processed H γ A₀ (AffineMap.const F₂ A 1) (pairSlice f σ η x Y p J B c) b| := by
    calc
      _ = 𝔼 b : Forms A, |pairSlice f σ η x Y p J B c (B s+b) -
          Slice.processed H γ A₀ (AffineMap.const F₂ A 1) (pairSlice f σ η x Y p J B c) (B s+b)| := by
        apply Finset.expect_congr rfl
        intro b _
        dsimp only [L]
        rw [pairSlice_row f hσ]
        unfold pairProcessed
        rw [pairSlice_resample, joinRow_at, joinRow_other _ _ _ ⟨s,hsr⟩]
        rw [add_comm b]
      _ = _ := expect_translate (fun b => |pairSlice f σ η x Y p J B c b -
          Slice.processed H γ A₀ (AffineMap.const F₂ A 1) (pairSlice f σ η x Y p J B c) b|) (B s)
  exact (expect_resample_row r L).symm.trans (Finset.expect_congr rfl (fun B _ => hB B))

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pairProcessed_measurable (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ A₀ : ℝ) (B : FaceArray A m n) :
    Measurable (pairProcessed f σ η x Y p J H γ A₀ B) := by
  unfold pairProcessed
  exact Slice.processed_measurable _ _ (pairSlice_measurable f σ η x Y p J B) _ _ _ _

lemma pairProcessed_memLp (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ : ℝ) {A₀ : ℝ} (hA : 0≤A₀)
    (B : FaceArray A m n) : MemLp (pairProcessed f σ η x Y p J H γ A₀ B) 2 (γpi (Point m n)) := by
  unfold pairProcessed
  exact Slice.processed_memLp _ _ (pairSlice_measurable f σ η x Y p J B) hA _

lemma pairSlice_jointEnergy (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) :
    (𝔼 B : FaceArray A m n, ∫ c, Slice.energy (pairSlice f σ η x Y p J B) c ∂γpi (Point m n)) =
      jointEnergy (selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x)) := by
  rw [← integral_expect _ (fun B => Slice.energy_integrable _ (pairSlice_memLp f σ η x Y p J B))]
  change (∫ c, (𝔼 B : FaceArray A m n, 𝔼 b : Forms A,
    (pairSlice f σ η x Y p J B c b)^2) ∂γpi (Point m n)) = _
  simp_rw [pairSlice_energy_law f hσ]
  exact integral_expect _ (fun B => (memLp_selectedProject _ _ B).integrable_sq)

lemma pair_processing_loss_integral (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) {H γ A₀ : ℝ}
    (hH : 0<H) (hγ : 0<γ) (hA : 0<A₀) :
    jointL1 (fun B c => selectedProject (retainedClass x Y (some p) J)
      (fun B c => gradient f B σ η c x) B c - pairProcessed f σ η x Y p J H γ A₀ B c) ≤
      jointEnergy (selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x))/H +
      Real.sqrt (jointEnergy (selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x))) *
        Real.sqrt ((𝔼 B : FaceArray A m n, ∫ c, Slice.oddMax (AffineMap.const F₂ A 1)
          (pairSlice f σ η x Y p J B c) ∂γpi (Point m n))/γ) +
      jointEnergy (selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x))/A₀ := by
  have hi B : Integrable (fun c => |selectedProject (retainedClass x Y (some p) J)
      (fun B c => gradient f B σ η c x) B c - pairProcessed f σ η x Y p J H γ A₀ B c|) (γpi (Point m n)) :=
    ((memLp_selectedProject _ _ _).sub (pairProcessed_memLp f σ η x Y p J H γ hA.le B)).integrable (by norm_num) |>.abs
  have hj B : Integrable (fun c => 𝔼 b : Forms A, |pairSlice f σ η x Y p J B c b -
      Slice.processed H γ A₀ (AffineMap.const F₂ A 1) (pairSlice f σ η x Y p J B c) b|) (γpi (Point m n)) := by
    simp only [Fintype.expect_eq_sum_div_card]
    apply Integrable.div_const
    apply integrable_finsetSum
    intro b _
    exact ((pairSlice_memLp f σ η x Y p J B b).sub
      (Slice.processed_memLp _ _ (pairSlice_measurable f σ η x Y p J B) hA.le b)).integrable (by norm_num) |>.abs
  have hh := Slice.processed_average_integral_loss (μ := γpi (Point m n)) (AffineMap.const F₂ A 1)
    (pairSlice f σ η x Y p J) (pairSlice_measurable f σ η x Y p J) (pairSlice_memLp f σ η x Y p J) hH hγ hA
  rw [pairSlice_jointEnergy f hσ] at hh
  apply le_trans ?_ hh
  unfold jointL1
  rw [← integral_expect _ hi, ← integral_expect _ hj]
  exact le_of_eq (integral_congr_ae (ae_of_all _ (pair_processing_loss_law f hσ η x Y p J H γ A₀)))

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pairSlice_atom_integral_law (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) :
    (𝔼 B : FaceArray A m n, ∫ c, Slice.oddMax (AffineMap.const F₂ A 1)
        (pairSlice f σ η x Y p J B c) ∂γpi (Point m n)) =
      𝔼 D, ∫ c, oddAtom ⟨p.val.1,face x p.val.1⟩ (AffineMap.const F₂ A 1)
        (fun B => selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x) B c) D ∂γpi (Point m n) := by
  rw [← integral_expect _ (fun B => (Slice.oddMax_memLp _ _
    (pairSlice_memLp f σ η x Y p J B)).integrable (by norm_num))]
  simp_rw [pairSlice_atom_mean f hσ]
  exact integral_expect _ (fun D => (memLp_oddAtom _ _ _ (memLp_selectedProject _ _) D).integrable (by norm_num))

lemma pairSlice_atom_integral_le (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) :
    (𝔼 B : FaceArray A m n, ∫ c, Slice.oddMax (AffineMap.const F₂ A 1)
        (pairSlice f σ η x Y p J B c) ∂γpi (Point m n)) ≤
      (J.card:ℝ)*(2:ℝ)^Fintype.card (Row m n) * Real.sqrt
        (𝔼 D, ∫ c, (oddAtom ⟨p.val.1,face x p.val.1⟩ (AffineMap.const F₂ A 1)
          (fun B => gradient f B σ η c x) D)^2 ∂γpi (Point m n)) := by
  rw [pairSlice_atom_integral_law f hσ]
  have hh := selectedProject_atom_mean (retainedClass x Y (some p) J)
    ⟨p.val.1,face x p.val.1⟩ (AffineMap.const F₂ A 1)
    (fun B c => gradient f B σ η c x) (fun B => gradient_memLp f B hσ η x)
  apply hh.trans
  gcongr
  intro j hj
  unfold retainedClass classSelection at hj
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1

lemma retained_energy_le (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : PointedBox x k) (a : Option (PairClass m))
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) :
    jointEnergy (selectedProject (retainedClass x Y a J) (fun B c => gradient f B σ η c x)) ≤
      jointEnergy (fun B c => gradient f B σ η c x) :=
  selectedProject_energy_le _ _ (fun B => gradient_memLp f B hσ η x)
end MinUncut.Inner

open scoped BigOperators
variable {m n : ℕ}
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory GaussianHermite
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [Nonempty W] [Fintype ι]

omit [Nonempty W] in
lemma jointL1_sub_triangle (u v w : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) (hv : ∀ B, MemLp (v B) 2 (γpi ι))
    (hw : ∀ B, MemLp (w B) 2 (γpi ι)) :
    jointL1 (fun B c => u B c-w B c) ≤
      jointL1 (fun B c => u B c-v B c)+jointL1 (fun B c => v B c-w B c) := by
  unfold jointL1
  rw [← Finset.expect_add_distrib]
  apply Finset.expect_le_expect
  intro B _
  change (∫ c, |u B c-w B c| ∂γpi ι) ≤
    (∫ c, |(u B-v B) c| ∂γpi ι) + (∫ c, |(v B-w B) c| ∂γpi ι)
  rw [← integral_add ((hu B).sub (hv B) |>.integrable (by norm_num) |>.abs)
    ((hv B).sub (hw B) |>.integrable (by norm_num) |>.abs)]
  apply integral_mono ((hu B).sub (hw B) |>.integrable (by norm_num) |>.abs)
    (((hu B).sub (hv B) |>.integrable (by norm_num) |>.abs).add
      ((hv B).sub (hw B) |>.integrable (by norm_num) |>.abs))
  intro c
  simpa only [sub_add_sub_cancel, Pi.add_apply, Pi.sub_apply] using abs_add_le (u B c-v B c) (v B c-w B c)
end MinUncut.RowNoise

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] faceCorrelation pointEmbed pointBox
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pointedJointL1_bayes {k : ℕ}
    (u : (x : Point m n) → PointedBox x k → FaceArray A m n → (Point m n → ℝ) → ℝ)
    (hu : ∀ x Y B, Integrable (u x Y B) (γpi (Point m n))) :
    (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, jointL1 (u x Y)) =
      𝔼 Y : UnpointedBox (Fin m) (Fin n) k, 𝔼 B : FaceArray A m n,
        ∫ c, (𝔼 t : Point m (k+1), |u (pointEmbed Y t) (pointBox Y t) B c|) ∂γpi (Point m n) := by
  rw [pointed_bayes]
  apply Finset.expect_congr rfl
  intro Y _
  unfold jointL1
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro B _
  exact (integral_expect _ (fun t => (hu (pointEmbed Y t) (pointBox Y t) B).abs)).symm

lemma faceCorrelation_pointed_compare {k : ℕ} (hk : k≤n-1)
    (u : Point m n → ℝ) (v : (x : Point m n) → PointedBox x k → ℝ) :
    faceCorrelation u ≤
      (𝔼 Y : UnpointedBox (Fin m) (Fin n) k,
        faceCorrelation (fun t : Point m (k+1) => v (pointEmbed Y t) (pointBox Y t))) +
      (𝔼 Y : UnpointedBox (Fin m) (Fin n) k,
        𝔼 t : Point m (k+1), |u (pointEmbed Y t)-v (pointEmbed Y t) (pointBox Y t)|) := by
  have ht := faceCorrelation_restriction hk u
  rw [← Finset.expect_add_distrib]
  apply ht.trans
  apply Finset.expect_le_expect
  intro Y _
  have hl := faceCorrelation_lipschitz (fun t : Point m (k+1) => u (pointEmbed Y t))
    (fun t : Point m (k+1) => v (pointEmbed Y t) (pointBox Y t))
  linarith only [le_trans (le_abs_self _) hl]

lemma averagedCorrelation_pointed_compare {k : ℕ} (hk : k≤n-1)
    (u : FaceArray A m n → (Point m n → ℝ) → Point m n → ℝ)
    (v : (x : Point m n) → PointedBox x k → FaceArray A m n → (Point m n → ℝ) → ℝ)
    (hum : ∀ B x, Measurable (fun c => u B c x))
    (hui : ∀ B x, Integrable (fun c => u B c x) (γpi (Point m n)))
    (hvm : ∀ x Y B, Measurable (v x Y B))
    (hvi : ∀ x Y B, Integrable (v x Y B) (γpi (Point m n))) :
    averagedCorrelation u ≤
      (𝔼 Y : UnpointedBox (Fin m) (Fin n) k, 𝔼 B : FaceArray A m n,
        ∫ c, faceCorrelation (fun t : Point m (k+1) => v (pointEmbed Y t) (pointBox Y t) B c) ∂γpi (Point m n)) +
      (𝔼 x : Point m n, 𝔼 Y : PointedBox x k,
        jointL1 (fun B c => u B c x-v x Y B c)) := by
  let C := fun (Y : UnpointedBox (Fin m) (Fin n) k) (B : FaceArray A m n) c =>
    faceCorrelation (fun t : Point m (k+1) => v (pointEmbed Y t) (pointBox Y t) B c)
  let D := fun (Y : UnpointedBox (Fin m) (Fin n) k) (B : FaceArray A m n) c =>
    𝔼 t : Point m (k+1), |u B c (pointEmbed Y t)-v (pointEmbed Y t) (pointBox Y t) B c|
  have hC Y B : Integrable (C Y B) (γpi (Point m n)) :=
    faceCorrelation_integrable _ (fun t => hvm _ _ B) (fun t => hvi _ _ B)
  have hD Y B : Integrable (D Y B) (γpi (Point m n)) := by
    simp only [D,Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun t _ => ((hui B _).sub (hvi _ _ B)).abs)).div_const _
  have hu' B : Integrable (fun c => faceCorrelation (u B c)) (γpi (Point m n)) :=
    faceCorrelation_integrable _ (hum B) (hui B)
  have hCi B : Integrable (fun c => 𝔼 Y, C Y B c) (γpi (Point m n)) := by
    simp only [Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun Y _ => hC Y B)).div_const _
  have hDi B : Integrable (fun c => 𝔼 Y, D Y B c) (γpi (Point m n)) := by
    simp only [Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun Y _ => hD Y B)).div_const _
  have hB B : (∫ c, faceCorrelation (u B c) ∂γpi (Point m n)) ≤
      (𝔼 Y, ∫ c, C Y B c ∂γpi (Point m n)) + (𝔼 Y, ∫ c, D Y B c ∂γpi (Point m n)) := by
    rw [← integral_expect _ (fun Y => hC Y B), ← integral_expect _ (fun Y => hD Y B),
      ← integral_add (hCi B) (hDi B)]
    exact integral_mono (hu' B) ((hCi B).add (hDi B))
      (fun c => faceCorrelation_pointed_compare hk (u B c) (fun x Y => v x Y B c))
  have hh := Finset.expect_le_expect (fun B (_ : B∈(Finset.univ : Finset (FaceArray A m n))) => hB B)
  rw [Finset.expect_add_distrib] at hh
  rw [Finset.expect_comm (f := fun B Y => ∫ c, C Y B c ∂γpi (Point m n)),
    Finset.expect_comm (f := fun B Y => ∫ c, D Y B c ∂γpi (Point m n))] at hh
  have hl := pointedJointL1_bayes
    (fun x Y B c => u B c x-v x Y B c) (fun x Y B => (hui B x).sub (hvi x Y B))
  rw [hl]
  exact hh
end MinUncut.Inner

open scoped BigOperators
variable {m n : ℕ}
namespace MinUncut.Slice

def lossBound (H γ A E q : ℝ) : ℝ := E/H+Real.sqrt E*Real.sqrt (q/γ)+E/A

lemma lossBound_mono {H γ A E E' q q' : ℝ} (hH : 0≤H) (hγ : 0≤γ) (hA : 0≤A)
    (hE : E≤E') (hq : q≤q') : lossBound H γ A E q ≤ lossBound H γ A E' q' := by
  unfold lossBound
  gcongr

lemma lossBound_expect {T : Type*} [Fintype T] (H γ A : ℝ) (E q : T → ℝ)
    (hγ : 0≤γ) (hE : ∀ t, 0≤E t) (hq : ∀ t, 0≤q t) :
    (𝔼 t, lossBound H γ A (E t) (q t)) ≤ lossBound H γ A (𝔼 t, E t) (𝔼 t, q t) := by
  unfold lossBound
  simp only [Finset.expect_add_distrib, ← Finset.expect_div]
  have hh := Average.expect_sqrt_mul_sqrt E (fun t => q t/γ) hE (fun t => div_nonneg (hq t) hγ)
  rw [← Finset.expect_div] at hh
  linarith only [hh]

lemma lossBound_weighted {T : Type*} [Fintype T] (H γ A : ℝ) (w E q : T → ℝ)
    (hw : ∀ t, 0≤w t) (hγ : 0≤γ) (hE : ∀ t, 0≤E t) (hq : ∀ t, 0≤q t) :
    (∑ t, w t*lossBound H γ A (E t) (q t)) ≤
      lossBound H γ A (∑ t, w t*E t) (∑ t, w t*q t) := by
  unfold lossBound
  simp only [mul_add, Finset.sum_add_distrib, ← mul_div_assoc, ← Finset.sum_div]
  have hh := Average.weighted_sqrt_mul_sqrt w E (fun t => q t/γ) hw hE
    (fun t => div_nonneg (hq t) hγ)
  simp only [← mul_div_assoc, ← Finset.sum_div] at hh
  linarith only [hh]
end MinUncut.Slice

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] gradient selectedProject retainedClass pairSlice pairProcessed Slice.processed
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

def pairAtomMean (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) : ℝ :=
  𝔼 B : FaceArray A m n, ∫ c, Slice.oddMax (AffineMap.const F₂ A 1)
      (pairSlice f σ η x Y p J B c) ∂γpi (Point m n)

lemma pairAtomMean_nonneg (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) : 0≤pairAtomMean f σ η x Y p J :=
  Finset.expect_nonneg (fun _ _ => integral_nonneg (fun _ => Slice.oddMax_nonneg _ _))

lemma pairAtomMean_uniform_le (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k s : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j ∈ J, GaussianHermite.degree j.2 ≤ s) :
    pairAtomMean f σ η x Y p J ≤
      (4:ℝ)^Fintype.card (Row m n) * ((Fintype.card (Point m n)+s).choose s:ℝ) * Real.sqrt
        (𝔼 D, ∫ c, (oddAtom ⟨p.val.1,face x p.val.1⟩ (AffineMap.const F₂ A 1)
          (fun B => gradient f B σ η c x) D)^2 ∂γpi (Point m n)) := by
  unfold pairAtomMean
  rw [pairSlice_atom_integral_law f hσ]
  apply selectedProject_atom_mean_uniform s _ _ _ _ _ (fun B => gradient_memLp f B hσ η x)
  intro j hj
  apply hJ j
  unfold retainedClass classSelection at hj
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1

lemma pair_processing_loss_average (f : FoldedProof A) {σ : ℝ} (hσ : 0<σ) (η : ℝ)
    (hn : 0<n) {k : ℕ} (hk : k≤n-1) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    {H γ A₀ : ℝ} (hH : 0<H) (hγ : 0<γ) (hA : 0<A₀) :
    (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, jointL1 (fun B c =>
      selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x) B c -
        pairProcessed f σ η x Y p J H γ A₀ B c)) ≤
      Slice.lossBound H γ A₀ (σ⁻¹^2) (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, pairAtomMean f σ η x Y p J) := by
  have : NeZero n := ⟨by omega⟩
  have (x : Point m n) (i : Fin m) : Nonempty (OuterSmoothness.FixedSets (Away (x i)) k) :=
    OuterSmoothness.fixedSets_nonempty (by simpa [card_away] using hk)
  let E := fun (x : Point m n) (Y : PointedBox x k) =>
    jointEnergy (selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x))
  let q := pairAtomMean f σ η (k := k) (p := p) (J := J)
  have hE x Y : 0≤E x Y := jointEnergy_nonneg _
  have hq x Y : 0≤q x Y := pairAtomMean_nonneg _ _ _ _ _ _ _
  have hcap : (𝔼 x, 𝔼 Y, E x Y) ≤ σ⁻¹^2 := by
    calc
      _ ≤ 𝔼 x : Point m n, 𝔼 _Y : PointedBox x k, jointEnergy (fun B c => gradient f B σ η c x) :=
        Finset.expect_le_expect (fun x _ => Finset.expect_le_expect (fun Y _ => retained_energy_le f hσ.ne' η x Y (some p) J))
      _ = averagedEnergy (fun B c => gradient (m := m) (n := n) f B σ η c) := by
        simp only [Fintype.expect_const]
        exact (averagedEnergy_eq_expect_joint _ (fun B x => gradient_memLp f B hσ.ne' η x)).symm
      _ ≤ _ := averagedEnergy_gradient_le f hn hσ.ne' η
  calc
    _ ≤ 𝔼 x, 𝔼 Y, Slice.lossBound H γ A₀ (E x Y) (q x Y) :=
      Finset.expect_le_expect (fun x _ => Finset.expect_le_expect (fun Y _ =>
        pair_processing_loss_integral f hσ.ne' η x Y p J hH hγ hA))
    _ ≤ 𝔼 x, Slice.lossBound H γ A₀ (𝔼 Y, E x Y) (𝔼 Y, q x Y) :=
      Finset.expect_le_expect (fun x _ => Slice.lossBound_expect H γ A₀ _ _ hγ.le (hE x) (hq x))
    _ ≤ Slice.lossBound H γ A₀ (𝔼 x, 𝔼 Y, E x Y) (𝔼 x, 𝔼 Y, q x Y) :=
      Slice.lossBound_expect H γ A₀ _ _ hγ.le
        (fun x => Finset.expect_nonneg (fun Y _ => hE x Y)) (fun x => Finset.expect_nonneg (fun Y _ => hq x Y))
    _ ≤ _ := Slice.lossBound_mono hH.le hγ.le hA.le hcap le_rfl
end MinUncut.Inner

open scoped BigOperators
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
attribute [local instance] Classical.propDecidable
local instance innerAssemblyDualFintype {U : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
variable {R W Ω : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [MeasurableSpace Ω]

omit [Fintype R] [DecidableEq W] in
lemma oddAtom_le_bound (r : R) (one : W) (f : (R → W) → ℝ) (D : Rest (W := W) r)
    {a : ℝ} (ha : 0 ≤ a) (hf : ∀ B, |f B| ≤ a) : oddAtom r one f D ≤ a := by
  apply oddAtom_le r one f D ha
  intro α _
  calc
    |rowCoefficient r f α D| ≤ 𝔼 b, |f (joinRow r b D) * character α b| :=
      Finset.abs_expect_le _ _
    _ = 𝔼 b, |f (joinRow r b D)| := by simp only [abs_mul, character_abs, mul_one]
    _ ≤ 𝔼 _b : W, a := Finset.expect_le_expect (fun b _ => hf _)
    _ = a := Fintype.expect_const a

omit [Fintype R] [DecidableEq W] in
lemma measurable_oddAtom (r : R) (one : W) (u : (R → W) → Ω → ℝ)
    (hu : ∀ B, Measurable (u B)) (D : Rest (W := W) r) :
    Measurable (fun c => oddAtom r one (fun B => u B c) D) := by
  let fs : Module.Dual F₂ W → Ω → ℝ := fun α c =>
    if α one=1 then |rowCoefficient r (fun B => u B c) α D| else 0
  have hfs (α : Module.Dual F₂ W) : Measurable (fs α) := by
    by_cases h : α one=1
    · simp only [fs, ite_eq_left h, rowCoefficient, Finset.expect_eq_sum_div_card]
      exact ((Finset.measurable_sum _ (fun b _ => (hu _).mul_const _)).div_const _).abs
    · simpa only [fs, ite_eq_right h] using (measurable_const : Measurable (fun _ : Ω => (0:ℝ)))
  have hh : Measurable (Finset.univ.sup' Finset.univ_nonempty fs) :=
    Finset.sup'_induction (p := fun f => Measurable f) Finset.univ_nonempty fs
      (fun _ hf _ hg => hf.max hg) (fun α _ => hfs α)
  convert hh using 1
  funext c
  simp only [Finset.sup'_apply, fs, oddAtom]
end MinUncut.RowNoise

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite
attribute [local instance] Classical.propDecidable
attribute [local irreducible] gradient oddAtom
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A] {m n : ℕ}

def rowAtom (f : FoldedProof A) (σ η : ℝ) (x : Point m n) (i : Fin m)
    (D : Rest (W := AffineMap F₂ A F₂) (⟨i,face x i⟩ : Row m n)) (c : Point m n → ℝ) : ℝ :=
  oddAtom ⟨i,face x i⟩ (AffineMap.const F₂ A 1) (fun B => gradient f B σ η c x) D

lemma rowAtom_nonneg (f : FoldedProof A) (σ η : ℝ) (x : Point m n) (i : Fin m)
    (D : Rest (W := AffineMap F₂ A F₂) (⟨i,face x i⟩ : Row m n)) (c : Point m n → ℝ) :
    0 ≤ rowAtom f σ η x i D c := oddAtom_nonneg _ _ _ _

lemma rowAtom_le_gradientBound (f : FoldedProof A) {σ : ℝ} (hσ : 0 < σ) (η : ℝ)
    (x : Point m n) (i : Fin m) (D : Rest (W := AffineMap F₂ A F₂) (⟨i,face x i⟩ : Row m n))
    (c : Point m n → ℝ) : rowAtom f σ η x i D c ≤ Real.sqrt (n^m : ℕ)/σ :=
  oddAtom_le_bound _ _ _ _ (by positivity) (fun B => gradient_abs_le f B hσ η c x)

lemma gradient_measurable (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (x : Point m n) :
    Measurable (fun c => gradient f B σ η c x) := by
  have hh := (measurable_score 1 σ (measurable_tableSmooth f B η) x).const_mul
    (Real.sqrt (n^m : ℕ)/σ)
  convert hh using 1
  funext c
  rw [gradient_score f B hσ]
  simp only [score,one_smul]
  rfl

lemma rowAtom_measurable (f : FoldedProof A) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (x : Point m n) (i : Fin m)
    (D : Rest (W := AffineMap F₂ A F₂) (⟨i,face x i⟩ : Row m n)) :
    Measurable (rowAtom f σ η x i D) :=
  measurable_oddAtom _ _ _ (fun B => gradient_measurable f B hσ η x) _

lemma rowAtom_memLp (f : FoldedProof A) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (x : Point m n) (i : Fin m)
    (D : Rest (W := AffineMap F₂ A F₂) (⟨i,face x i⟩ : Row m n)) :
    MemLp (rowAtom f σ η x i D) 2 (γpi (Point m n)) :=
  memLp_oddAtom _ _ _ (fun B => gradient_memLp f B hσ η x) _

def rowAtomIndicator (f : FoldedProof A) (σ η θ : ℝ) (x : Point m n) (i : Fin m)
    (D : Rest (W := AffineMap F₂ A F₂) (⟨i,face x i⟩ : Row m n)) (c : Point m n → ℝ) : ℝ :=
  if θ ≤ rowAtom f σ η x i D c then 1 else 0

lemma rowAtomIndicator_integrable (f : FoldedProof A) {σ : ℝ} (hσ : σ ≠ 0) (η θ : ℝ) (x : Point m n) (i : Fin m)
    (D : Rest (W := AffineMap F₂ A F₂) (⟨i,face x i⟩ : Row m n)) :
    Integrable (rowAtomIndicator f σ η θ x i D) (γpi (Point m n)) := by
  have hm : Measurable (rowAtomIndicator f σ η θ x i D) :=
    Measurable.ite (measurableSet_le measurable_const (rowAtom_measurable f hσ η x i D))
      measurable_const measurable_const
  apply (MemLp.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ (fun c => ?_)) :
    MemLp (rowAtomIndicator f σ η θ x i D) 2 (γpi (Point m n))).integrable (by norm_num)
  unfold rowAtomIndicator
  split_ifs <;> norm_num

def rowEventProbability (f : FoldedProof A) (σ η θ : ℝ) (x : Point m n) (i : Fin m) : ℝ :=
  𝔼 D, ∫ c, rowAtomIndicator f σ η θ x i D c ∂γpi (Point m n)

def atomProbability (f : FoldedProof A) (σ η θ : ℝ) : ℝ :=
  𝔼 x : Point m n, 𝔼 i : Fin m, rowEventProbability f σ η θ x i

lemma rowEventProbability_nonneg (f : FoldedProof A) (σ η θ : ℝ) (x : Point m n) (i : Fin m) :
    0 ≤ rowEventProbability f σ η θ x i := by
  apply Finset.expect_nonneg
  intro D _
  exact integral_nonneg (fun c => by unfold rowAtomIndicator; split_ifs <;> norm_num)

lemma rowAtom_sq_le (f : FoldedProof A) {σ θ : ℝ} (hσ : 0 < σ) (hθ : 0 ≤ θ) (η : ℝ)
    (x : Point m n) (i : Fin m) (D : Rest (W := AffineMap F₂ A F₂) (⟨i,face x i⟩ : Row m n))
    (c : Point m n → ℝ) :
    (rowAtom f σ η x i D c)^2 ≤ θ^2 + (n^m : ℕ)/σ^2*rowAtomIndicator f σ η θ x i D c := by
  have hn : 0 ≤ (n^m : ℕ) := Nat.zero_le _
  have hu := rowAtom_le_gradientBound f hσ η x i D c
  have hl := rowAtom_nonneg f σ η x i D c
  have hs : (Real.sqrt (n^m : ℕ)/σ)^2 = (n^m : ℕ)/σ^2 := by
    rw [div_pow,Real.sq_sqrt (by positivity)]
  unfold rowAtomIndicator
  split_ifs with h
  · have hh := sq_le_sq₀ hl (by positivity) |>.mpr hu
    nlinarith [sq_nonneg θ]
  · simp only [mul_zero,add_zero]
    exact sq_le_sq₀ hl hθ |>.mpr (le_of_lt (lt_of_not_ge h))

lemma rowAtom_secondMoment (f : FoldedProof A) {σ θ : ℝ} (hσ : 0 < σ) (hθ : 0 ≤ θ) (η : ℝ)
    (x : Point m n) (i : Fin m) :
    (𝔼 D, ∫ c, (rowAtom f σ η x i D c)^2 ∂γpi (Point m n)) ≤
      θ^2 + (n^m : ℕ)/σ^2*rowEventProbability f σ η θ x i := by
  calc
    _ ≤ 𝔼 D, ∫ c, θ^2 + (n^m : ℕ)/σ^2*rowAtomIndicator f σ η θ x i D c ∂γpi (Point m n) := by
      apply Finset.expect_le_expect
      intro D _
      exact integral_mono (rowAtom_memLp f hσ.ne' η x i D).integrable_sq
        ((integrable_const _).add ((rowAtomIndicator_integrable f hσ.ne' η θ x i D).const_mul _))
        (rowAtom_sq_le f hσ hθ η x i D)
    _ = _ := by
      simp_rw [integral_add (integrable_const _) ((rowAtomIndicator_integrable f hσ.ne' η θ x i _).const_mul _),
        integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul]
      rw [Finset.expect_add_distrib,Fintype.expect_const, ← Finset.mul_expect]
      rfl

lemma fixed_row_probability_le (f : FoldedProof A) (σ η θ : ℝ) (i : Fin m) :
    (𝔼 x : Point m n, rowEventProbability f σ η θ x i) ≤ (m:ℝ)*atomProbability (m := m) (n := n) f σ η θ := by
  have hm : m ≠ 0 := by have := i.isLt; omega
  have hx (x : Point m n) : rowEventProbability f σ η θ x i ≤
      (m:ℝ)*(𝔼 j : Fin m, rowEventProbability f σ η θ x j) := by
    rw [Fintype.expect_eq_sum_div_card,Fintype.card_fin,mul_div_cancel₀ _ (by exact_mod_cast hm)]
    exact Finset.single_le_sum (fun j _ => rowEventProbability_nonneg f σ η θ x j) (Finset.mem_univ i)
  have h := Finset.expect_le_expect (fun x (_ : x ∈ (Finset.univ : Finset (Point m n))) => hx x)
  simpa only [← Finset.mul_expect, atomProbability] using h
end MinUncut.Inner

end

end OAI
