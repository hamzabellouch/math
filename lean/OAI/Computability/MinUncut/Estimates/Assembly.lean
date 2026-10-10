import Mathlib
import OAI.Computability.MinUncut.Search.Parameters
import OAI.Computability.MinUncut.Estimates.AnalyticOuter
import OAI.Computability.MinUncut.Analysis.GaussianAssembly

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox BoxGaussian
attribute [local instance] Classical.propDecidable
attribute [local irreducible] gradient selectedProject retainedClass Slice.centeredClip
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

def zeroProcessed (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (A₀ : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ) : ℝ :=
  Slice.centeredClip γ A₀ (gaussianSlice f σ η x Y J B c) (c x)

lemma zeroProcessed_measurable (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (A₀ : ℝ)
    (B : FaceArray A m n) : Measurable (zeroProcessed f σ η x Y J A₀ B) :=
  centered_gaussianSlice_diagonal_measurable f σ η x Y J B A₀

lemma zeroProcessed_memLp (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    {A₀ : ℝ} (hA : 0≤A₀) (B : FaceArray A m n) :
    MemLp (zeroProcessed f σ η x Y J A₀ B) 2 (γpi (Point m n)) := by
  unfold zeroProcessed gaussianSlice
  exact centered_resample_memLp x _ (selectedProject_continuous _ _ _).measurable hA

lemma zero_processing_loss_integral (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j ∈ J, j.1.card < (m-(∑ u, j.2 u)).choose 2)
    {A₀ : ℝ} (hA : 0<A₀) :
    jointL1 (fun B c => selectedProject (retainedClass x Y none J) (fun B c => gradient f B σ η c x) B c -
      zeroProcessed f σ η x Y J A₀ B c) ≤
      2*jointEnergy (selectedProject (retainedClass x Y none J) (fun B c => gradient f B σ η c x))/A₀ := by
  have hB (B : FaceArray A m n) := centered_resample_loss x
    (selectedProject (retainedClass x Y none J) (fun B c => gradient f B σ η c x) B)
    (selectedProject_continuous _ _ _).measurable (memLp_selectedProject _ _ _)
    (fun C => gaussianSlice_memLp f σ η x Y J B C)
    (fun C => gaussianSlice_mean f σ η x Y J hJ B C) hA
  unfold jointL1 jointEnergy
  simp only [Finset.mul_expect, Finset.expect_div]
  apply Finset.expect_le_expect
  intro B _
  unfold zeroProcessed
  exact hB B

lemma zero_processing_loss_average (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (hn : 0<n) {k : ℕ} (hk : k≤n-1)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j ∈ J, j.1.card < (m-(∑ u, j.2 u)).choose 2)
    {A₀ : ℝ} (hA : 0<A₀) :
    (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, jointL1 (fun B c =>
      selectedProject (retainedClass x Y none J) (fun B c => gradient f B σ η c x) B c -
        zeroProcessed f σ η x Y J A₀ B c)) ≤ 2*(σ⁻¹^2)/A₀ := by
  have : NeZero n := ⟨by omega⟩
  have (x : Point m n) (i : Fin m) : Nonempty (OuterSmoothness.FixedSets (Away (x i)) k) :=
    OuterSmoothness.fixedSets_nonempty (by simpa [card_away] using hk)
  calc
    _ ≤ 𝔼 x : Point m n, 𝔼 Y : PointedBox x k,
        2*jointEnergy (selectedProject (retainedClass x Y none J) (fun B c => gradient f B σ η c x))/A₀ :=
      Finset.expect_le_expect (fun x _ => Finset.expect_le_expect (fun Y _ => zero_processing_loss_integral f σ η x Y J hJ hA))
    _ ≤ 𝔼 x : Point m n, 𝔼 _Y : PointedBox x k,
        2*jointEnergy (fun B c => gradient f B σ η c x)/A₀ := by
      apply Finset.expect_le_expect
      intro x _
      apply Finset.expect_le_expect
      intro Y _
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (retained_energy_le f hσ η x Y none J) (by norm_num)) hA.le
    _ = 2*averagedEnergy (fun B c => gradient (m := m) (n := n) f B σ η c)/A₀ := by
      simp only [Fintype.expect_const, ← Finset.expect_div, ← Finset.mul_expect]
      rw [averagedEnergy_eq_expect_joint _ (fun B x => gradient_memLp f B hσ η x)]
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (averagedEnergy_gradient_le f hn hσ η) (by norm_num)) hA.le

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] classField pairSlice Slice.processed gaussianSlice
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma class_correlation_processing (f : FoldedProof A) {σ : ℝ} (hσ : 0 < σ) (η : ℝ)
    (hn : 2 ≤ n) {k s D : ℕ} (hk : k ≤ n-1) (a : Option (PairClass m))
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j∈ J, (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ D)
    (v : (x : Point m n) → PointedBox x k → FaceArray A m n → (Point m n → ℝ) → ℝ)
    (hvm : ∀ x Y B, Measurable (v x Y B))
    (hv : ∀ x Y B, MemLp (v x Y B) 2 (γpi (Point m n))) :
    averagedCorrelation (classField f σ η J a) ≤
      σ⁻¹*Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) +
      (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, jointL1 (fun B c =>
        selectedProject (retainedClass x Y a J) (fun B c => gradient f B σ η c x) B c-v x Y B c)) +
      (𝔼 Y : UnpointedBox (Fin m) (Fin n) k, 𝔼 B : FaceArray A m n,
        ∫ c, faceCorrelation (fun t : Point m (k+1) => v (pointEmbed Y t) (pointBox Y t) B c) ∂γpi (Point m n)) := by
  have hcmp := averagedCorrelation_pointed_compare hk (classField f σ η J a) v
    (classField_measurable f σ η J a) (fun B x => (classField_memLp f σ η J a B x).integrable (by norm_num))
    hvm (fun x Y B => (hv x Y B).integrable (by norm_num))
  have ht (x : Point m n) (Y : PointedBox x k) := jointL1_sub_triangle
    (fun B c => classField f σ η J a B c x)
    (selectedProject (retainedClass x Y a J) (fun B c => gradient f B σ η c x)) (v x Y)
    (fun B => classField_memLp f σ η J a B x) (memLp_selectedProject _ _) (hv x Y)
  have hta := Finset.expect_le_expect (fun x (_ : x∈(Finset.univ : Finset (Point m n))) =>
    Finset.expect_le_expect (fun Y (_ : Y∈(Finset.univ : Finset (PointedBox x k))) => ht x Y))
  simp only [Finset.expect_add_distrib] at hta
  have hl := class_localization_l1 f hσ η hn hk J hJ a
  linarith only [hcmp,hta,hl]

lemma pair_class_correlation (f : FoldedProof A) {σ : ℝ} (hσ : 0 < σ) (η : ℝ)
    (hn : 2 ≤ n) {k s D : ℕ} (hk : k ≤ n-1) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j∈ J, (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ D)
    {H γ A₀ : ℝ} (hH : 0 < H) (hγ : 0 < γ) (hA : 0 < A₀) :
    averagedCorrelation (classField f σ η J (some p)) ≤
      σ⁻¹*Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) +
      Slice.lossBound H γ A₀ (σ⁻¹^2) (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, pairAtomMean f σ η x Y p J) +
      A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) + Real.sqrt (H*(γ+H^2/A₀)) := by
  have : Nonempty (OuterSmoothness.FixedSets (Fin n) (k+1)) :=
    OuterSmoothness.fixedSets_nonempty (by simp only [Fintype.card_fin]; omega)
  have hc := class_correlation_processing f hσ η hn hk (some p) J hJ
    (fun x Y => pairProcessed f σ η x Y p J H γ A₀)
    (fun x Y B => pairProcessed_measurable f σ η x Y p J H γ A₀ B)
    (fun x Y B => pairProcessed_memLp f σ η x Y p J H γ hA.le B)
  have hl := pair_processing_loss_average f hσ η (by omega : 0 < n) hk p J hH hγ hA
  have hb (Y : UnpointedBox (Fin m) (Fin n) k) :
      (𝔼 B : FaceArray A m n, ∫ c, faceCorrelation (pairProcessedOnBox f σ η Y p J H γ A₀ B c) ∂γpi (Point m n)) ≤
      A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) + Real.sqrt (H*(γ+H^2/A₀)) := by
    have hi (B : FaceArray A m n) : Integrable (fun c =>
        faceCorrelation (pairProcessedOnBox f σ η Y p J H γ A₀ B c)) (γpi (Point m n)) := by
      apply faceCorrelation_integrable _ (fun t => pairProcessedOnBox_c_measurable f σ η Y p J H γ A₀ B t)
      intro t
      exact
        (pairProcessed_memLp f σ η (pointEmbed Y t) (pointBox Y t) p J H γ hA.le B).integrable (by norm_num : (1:ENNReal) ≤ 2)
    rw [← integral_expect _ hi]
    exact actual_pair_box_average f hσ.ne' η Y p J hH.le hA hγ.le
  have hba := Finset.expect_le_expect (fun Y (_ : Y∈(Finset.univ : Finset (UnpointedBox (Fin m) (Fin n) k))) => hb Y)
  rw [Fintype.expect_const] at hba
  unfold pairProcessedOnBox at hba
  dsimp only [pairProcessed] at hc hl
  linarith only [hc,hl,hba]

lemma zero_class_correlation (f : FoldedProof A) {σ : ℝ} (hσ : 0 < σ) (η : ℝ)
    (hm : 0 < m) (hn : 2 ≤ n) {k s D : ℕ} (hk : k ≤ n-1)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j∈ J, (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ D)
    (hJ0 : ∀ j∈ J, j.1.card < (m-(∑ u, j.2 u)).choose 2)
    {A₀ : ℝ} (hA : 0 < A₀) :
    averagedCorrelation (classField f σ η J none) ≤
      σ⁻¹*Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) + 2*(σ⁻¹^2)/A₀ +
      2*A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) := by
  have : Nonempty (OuterSmoothness.FixedSets (Fin n) (k+1)) :=
    OuterSmoothness.fixedSets_nonempty (by simp only [Fintype.card_fin]; omega)
  have hc := class_correlation_processing f hσ η hn hk none J hJ
    (fun x Y => zeroProcessed f σ η x Y J A₀)
    (fun x Y B => zeroProcessed_measurable f σ η x Y J A₀ B)
    (fun x Y B => zeroProcessed_memLp f σ η x Y J hA.le B)
  have hl := zero_processing_loss_average f hσ.ne' η (by omega : 0 < n) hk J hJ0 hA
  have hb (Y : UnpointedBox (Fin m) (Fin n) k) :
      (𝔼 B : FaceArray A m n, ∫ c, faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B c) ∂γpi (Point m n)) ≤
      2*A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) := by
    have hi (B : FaceArray A m n) : Integrable (fun c =>
        faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B c)) (γpi (Point m n)) := by
      apply faceCorrelation_integrable _
      · intro t
        exact
          zeroProcessed_measurable f σ η (pointEmbed Y t) (pointBox Y t) J A₀ B
      · intro t
        exact
          (zeroProcessed_memLp f σ η (pointEmbed Y t) (pointBox Y t) J hA.le B).integrable (by norm_num : (1:ENNReal) ≤ 2)
    rw [← integral_expect _ hi]
    exact actual_zero_box_average f σ η hm Y J hA.le
  have hba := Finset.expect_le_expect (fun Y (_ : Y∈(Finset.univ : Finset (UnpointedBox (Fin m) (Fin n) k))) => hb Y)
  rw [Fintype.expect_const] at hba
  unfold zeroProcessedOnBox at hba
  dsimp only [zeroProcessed] at hc hl
  linarith only [hc,hl,hba]

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] oddAtom rowAtom pairAtomMean lowGradient
variable {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
  [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
  [∀ ξ, Fintype (A ξ)] {m n : ℕ}

lemma weighted_pair_class_correlation (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ) (hw1 : ∑ ξ, w ξ=1)
    (f : ∀ ξ, FoldedProof (A ξ)) {σ θ p : ℝ} (hσ : 0 < σ) (hθ : 0 ≤ θ) (η : ℝ)
    (hn : 2 ≤ n) {k s D : ℕ} (hk : k ≤ n-1) (r : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j∈ J, (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ D)
    {H γ A₀ : ℝ} (hH : 0 < H) (hγ : 0 < γ) (hA : 0 < A₀)
    (hp : (∑ ξ, w ξ*atomProbability (m := m) (n := n) (f ξ) σ η θ) ≤ p) :
    (∑ ξ, w ξ*averagedCorrelation (classField (n := n) (f ξ) σ η J (some r))) ≤
      σ⁻¹*Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) +
      Slice.lossBound H γ A₀ (σ⁻¹^2)
        ((4:ℝ)^Fintype.card (Row m n)*((Fintype.card (Point m n)+s).choose s:ℝ)*
          Real.sqrt (θ^2+(m:ℝ)*p*(n^m:ℕ)/σ^2)) +
      A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) + Real.sqrt (H*(γ+H^2/A₀)) := by
  let q (ξ : Ξ) := 𝔼 x : Point m n, 𝔼 Y : PointedBox x k, pairAtomMean (f ξ) σ η x Y r J
  have hq ξ : 0 ≤ q ξ := Finset.expect_nonneg (fun x _ =>
    Finset.expect_nonneg (fun Y _ => pairAtomMean_nonneg _ _ _ _ _ _ _))
  have hcls := Finset.sum_le_sum (s := (Finset.univ : Finset Ξ)) (fun ξ _ =>
    mul_le_mul_of_nonneg_left (pair_class_correlation (f ξ) hσ η hn hk r J hJ hH hγ hA) (hw ξ))
  simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hw1,one_mul] at hcls
  rw [← mul_add] at hcls
  have hloss := Slice.lossBound_weighted H γ A₀ w (fun _ : Ξ => σ⁻¹^2) q hw hγ.le
    (fun _ => sq_nonneg _) hq
  rw [← Finset.sum_mul,hw1,one_mul] at hloss
  have hatom := weighted_pairAtomMean V A w hw hw1 f hσ hθ η (by omega) hk r J
    (fun j hj => (hJ j hj).1) hp
  have hloss' := Slice.lossBound_mono hH.le hγ.le hA.le (le_refl (σ⁻¹^2)) hatom
  dsimp only [q] at hloss
  linarith only [hcls, hloss, hloss']

lemma weighted_zero_class_correlation (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ) (hw1 : ∑ ξ, w ξ=1)
    (f : ∀ ξ, FoldedProof (A ξ)) {σ : ℝ} (hσ : 0 < σ) (η : ℝ)
    (hm : 0 < m) (hn : 2 ≤ n) {k s D : ℕ} (hk : k ≤ n-1)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j∈ J, (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ D)
    (hJ0 : ∀ j∈ J, j.1.card < (m-(∑ u, j.2 u)).choose 2)
    {A₀ : ℝ} (hA : 0 < A₀) :
    (∑ ξ, w ξ*averagedCorrelation (classField (n := n) (f ξ) σ η J none)) ≤
      σ⁻¹*Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) + 2*(σ⁻¹^2)/A₀ +
      2*A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset Ξ)) (fun ξ _ =>
    mul_le_mul_of_nonneg_left (zero_class_correlation (f ξ) hσ η hm hn hk J hJ hJ0 hA) (hw ξ))
  rwa [← Finset.sum_mul,hw1,one_mul] at hh

lemma weighted_lowGradient_classes (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ)
    (D s : ℕ) (f : ∀ ξ, FoldedProof (A ξ)) (σ η : ℝ) :
    (∑ ξ, w ξ*averagedCorrelation (lowGradient (m := m) (n := n) D s (f ξ) σ η)) ≤
      ∑ a : Option (PairClass m), ∑ ξ, w ξ*averagedCorrelation (classField (n := n) (f ξ) σ η (rectangle D s) a) := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset Ξ)) (fun ξ _ =>
    mul_le_mul_of_nonneg_left (lowGradient_classes_correlation (m := m) (n := n) D s (f ξ) σ η) (hw ξ))
  simp only [Finset.mul_sum] at hh
  rwa [Finset.sum_comm] at hh

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

def classTarget (T : ℝ) (m : ℕ) : ℝ := 1/(4*T*(Fintype.card (Option (PairClass m)):ℝ))

lemma classTarget_pos {T : ℝ} (hT : 0 < T) (m : ℕ) : 0 < classTarget T m := by
  unfold classTarget
  positivity

lemma classes_times_target {T : ℝ} (hT : 0 < T) (m : ℕ) :
    (Fintype.card (Option (PairClass m)):ℝ)*classTarget T m = 1/(4*T) := by
  have hc : (Fintype.card (Option (PairClass m)):ℝ) ≠ 0 := by positivity
  unfold classTarget
  field_simp

lemma rectangle_bounds (D s : ℕ) (j : Finset (Row m n) × (Point m n → ℕ))
    (hj : j ∈ rectangle D s) : (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ D := by
  obtain ⟨hS,hI⟩ := Finset.mem_product.mp hj
  exact ⟨(mem_low _ _).mp hI,(Finset.mem_filter.mp hS).2⟩

lemma rectangle_pair_room {D s : ℕ} (hroom : D < (m-s).choose 2)
    (j : Finset (Row m n) × (Point m n → ℕ)) (hj : j ∈ rectangle D s) :
    j.1.card < (m-(∑ u, j.2 u)).choose 2 := by
  obtain ⟨hi,hS⟩ := rectangle_bounds D s j hj
  exact lt_of_le_of_lt hS (lt_of_lt_of_le hroom (Nat.choose_le_choose 2 (by omega)))

theorem inner_atom_of_errors {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
    [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
    [∀ ξ, Fintype (A ξ)] (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ) (hw1 : ∑ ξ, w ξ=1)
    (f : ∀ ξ, FoldedProof (A ξ)) {J : ℝ} (hJ : 1 ≤ J) {m n k s : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : k ≤ n-1)
    (hs : ∀ t : ℕ, s+2 ≤ t → (t:ℝ)*(smoothingRho (sourceSigma J))^(2*t) ≤ 1/16)
    (hroom : sourceR J*m < (m-s).choose 2)
    {H γ A₀ θ p : ℝ} (hH : 0 < H) (hγ : 0 < γ) (hA : 0 < A₀) (hθ : 0 ≤ θ)
    (hloc : (sourceSigma J)⁻¹*Real.sqrt (((s+sourceR J*m:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) <
      classTarget (sourceT J) m/10)
    (henergy : (sourceSigma J)⁻¹^2/H < classTarget (sourceT J) m/10)
    (hclip : 2*((sourceSigma J)⁻¹^2)/A₀ < classTarget (sourceT J) m/10)
    (hcollision : 2*A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) < classTarget (sourceT J) m/10)
    (hfourth : Real.sqrt (H*(γ+H^2/A₀)) < classTarget (sourceT J) m/10)
    (hatom : Real.sqrt ((sourceSigma J)⁻¹^2)*Real.sqrt
      (((4:ℝ)^Fintype.card (Row m n)*((Fintype.card (Point m n)+s).choose s:ℝ)*
        Real.sqrt (θ^2+(m:ℝ)*p*(n^m:ℕ)/(sourceSigma J)^2))/γ) < classTarget (sourceT J) m/10)
    (h1 : (∑ ξ, w ξ*firstError (m := m) (n := n) (f ξ) (sourceSigma J) (sourceEta J)) ≤
      J*(10*sourceSigma J))
    (h2 : (∑ ξ, w ξ*secondError (m := m) (n := n) (f ξ)
      ((sourceEta J)^2/(m:ℝ)) (sourceSigma J) (sourceEta J)) ≤ J*(10*(sourceEta J+sourceEta J)))
    (h3 : (∑ ξ, w ξ*thirdError (m := m) (n := n) (f ξ) (sourceSigma J) (sourceEta J)) ≤
      J/(Fintype.card (Code m n):ℝ)) :
    p ≤ ∑ ξ, w ξ*atomProbability (m := m) (n := n) (f ξ) (sourceSigma J) (sourceEta J) θ := by
  by_contra hp
  have hp' := le_of_lt (lt_of_not_ge hp)
  have hσ := sourceSigma_pos hJ
  have hT : (0:ℝ) < sourceT J := by exact_mod_cast sourceT_pos hJ
  have hd := classTarget_pos hT m
  have heA : 0 ≤ (sourceSigma J)⁻¹^2/A₀ := by positivity
  have hcol0 : 0 ≤ A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) := by positivity
  have hclip' : (sourceSigma J)⁻¹^2/A₀ < classTarget (sourceT J) m/10 := by
    have hh : 2*((sourceSigma J)⁻¹^2/A₀) < classTarget (sourceT J) m/10 := by
      simpa only [mul_div_assoc] using hclip
    linarith only [hh,heA]
  have hcollision' : A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) < classTarget (sourceT J) m/10 := by
    have hh : 2*(A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹)) < classTarget (sourceT J) m/10 := by
      simpa only [mul_assoc] using hcollision
    linarith only [hh,hcol0]
  have hcls (a : Option (PairClass m)) :
      (∑ ξ, w ξ*averagedCorrelation (classField (n := n) (f ξ) (sourceSigma J) (sourceEta J)
        (rectangle (sourceR J*m) s) a)) < classTarget (sourceT J) m := by
    cases a with
    | none =>
      have hh := weighted_zero_class_correlation V A w hw hw1 f hσ (sourceEta J) (by omega : 0 < m)
        hn hk _ (rectangle_bounds (sourceR J*m) s) (rectangle_pair_room hroom) hA
      linarith only [hh,hloc,hclip,hcollision,hd]
    | some r =>
      have hh := weighted_pair_class_correlation V A w hw hw1 f hσ hθ (sourceEta J)
        hn hk r _ (rectangle_bounds (sourceR J*m) s) hH hγ hA hp'
      unfold Slice.lossBound at hh
      linarith only [hh,hloc,henergy,hclip',hcollision',hfourth,hatom,hd]
  have hsum : (∑ a : Option (PairClass m), ∑ ξ, w ξ*averagedCorrelation
      (classField (n := n) (f ξ) (sourceSigma J) (sourceEta J) (rectangle (sourceR J*m) s) a)) <
      (Fintype.card (Option (PairClass m)):ℝ)*classTarget (sourceT J) m := by
    calc
      _ < ∑ _a : Option (PairClass m), classTarget (sourceT J) m :=
        Finset.sum_lt_sum (fun a _ => (hcls a).le) ⟨none,Finset.mem_univ _,hcls none⟩
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [classes_times_target hT] at hsum
  have hup := weighted_lowGradient_classes (m := m) (n := n) V A w hw (sourceR J*m) s f
    (sourceSigma J) (sourceEta J)
  have hlo := source_lowGradient_correlation V A w hw hw1 f hJ hm hn s hs h1 h2 h3
  linarith only [hsum,hup,hlo]

lemma exists_dimension (R s : ℕ) : ∃ m : ℕ, 2 ≤ m ∧ s+1 < m ∧ R*m < (m-s).choose 2 := by
  let m := 4*(R+s+1)
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hs : s+1 < m := by dsimp [m]; omega
  have ha : m-s = 4*R+3*s+4 := by dsimp [m]; omega
  have hb : m-s-1 = 4*R+3*s+3 := by omega
  have hprod : 2*(R*m+1) ≤ (m-s)*(m-s-1) := by
    rw [hb,ha]
    dsimp [m]
    nlinarith
  refine ⟨m,hm,hs,?_⟩
  rw [Nat.choose_two_right]
  omega

lemma exists_positive_nat_div_lt {E e : ℝ} (he : 0 < e) :
    ∃ H : ℕ, 0 < H ∧ E/(H:ℝ) < e := by
  obtain ⟨H,hH⟩ := exists_nat_gt (max 0 (E/e))
  have hH0 : (0:ℝ) < H := lt_of_le_of_lt (le_max_left _ _) hH
  have hEH : E < e*(H:ℝ) := by
    have := (div_lt_iff₀ he).mp (lt_of_le_of_lt (le_max_right _ _) hH)
    linarith
  exact ⟨H,by exact_mod_cast hH0,(div_lt_iff₀ hH0).mpr hEH⟩

lemma exists_reciprocal_processing {E e : ℝ} (he : 0 < e) :
    ∃ (H A₀ : ℕ) (γ : ℚ), 0 < H ∧ 0 < A₀ ∧ 0 < (γ:ℝ) ∧ (γ:ℝ) < 1 ∧
      E/(H:ℝ) < e ∧ 2*E/(A₀:ℝ) < e ∧
      Real.sqrt ((H:ℝ)*((γ:ℝ)+(H:ℝ)^2/(A₀:ℝ))) < e := by
  obtain ⟨H,hH,hHbound⟩ := exists_positive_nat_div_lt (E := E) he
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  obtain ⟨γ,hγ,hγub⟩ := exists_rat_btwn (show (0:ℝ) < min 1 (e^2/(4*(H:ℝ))) by positivity)
  have hg1 := (lt_min_iff.mp hγub).1
  have hgE : (H:ℝ)*(γ:ℝ) < e^2/4 := by
    have hh := (lt_div_iff₀ (show (0:ℝ) < 4*(H:ℝ) by positivity)).mp (lt_min_iff.mp hγub).2
    nlinarith
  obtain ⟨A₀,hA⟩ := exists_nat_gt (max 0 (max (2*E/e) (4*(H:ℝ)^3/e^2)))
  have hAr : (0:ℝ) < A₀ := lt_of_le_of_lt (le_max_left _ _) hA
  have hAE : 2*E/(A₀:ℝ) < e := by
    apply (div_lt_iff₀ hAr).mpr
    have hh := (div_lt_iff₀ he).mp (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hA)
    linarith
  have hAH : (H:ℝ)^3/(A₀:ℝ) < e^2/4 := by
    have hh := (div_lt_iff₀ (show 0 < e^2 by positivity)).mp
      (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hA)
    apply (div_lt_iff₀ hAr).mpr
    nlinarith
  refine ⟨H,A₀,γ,hH,by exact_mod_cast hAr,hγ,hg1,hHbound,hAE,?_⟩
  apply Real.sqrt_lt' he |>.mpr
  have heq : (H:ℝ)*((γ:ℝ)+(H:ℝ)^2/(A₀:ℝ)) = (H:ℝ)*(γ:ℝ)+(H:ℝ)^3/(A₀:ℝ) := by ring
  rw [heq]
  nlinarith

lemma exists_box_scale (m : ℕ) {A₀ e : ℝ} (hA : 0 < A₀) (he : 0 < e) :
    ∃ k : ℕ, 1 ≤ k ∧ 2*A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) < e := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max 1 ((m:ℝ)/(e/(2*A₀))^(2^m)))
  have hk1 : (1:ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hk0 : (0:ℝ) < (k:ℝ)+1 := by linarith
  have hq : (m:ℝ)/(e/(2*A₀))^(2^m) < (k:ℝ)+1 :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hk) (by linarith)
  have hratio : (m:ℝ)/((k:ℝ)+1) < (e/(2*A₀))^(2^m) := by
    apply (div_lt_iff₀ hk0).mpr
    have hh := (div_lt_iff₀ (show (0:ℝ) < (e/(2*A₀))^(2^m) by positivity)).mp hq
    linarith
  have hroot : ((m:ℝ)/((k:ℝ)+1))^(((2^m:ℕ):ℝ)⁻¹) < e/(2*A₀) := by
    apply (Real.rpow_inv_lt_iff_of_pos (by positivity) (by positivity) (by positivity)).mpr
    rwa [Real.rpow_natCast]
  refine ⟨k,by exact_mod_cast hk1.le,?_⟩
  simpa only [mul_comm] using (lt_div_iff₀ (show 0 < 2*A₀ by positivity)).mp hroot

lemma exists_ambient_scale (s D k : ℕ) {σ e : ℝ} (hσ : 0 < σ) (he : 0 < e) :
    ∃ n : ℕ, k+2 ≤ n ∧ σ⁻¹*Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) < e := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max (k+2:ℝ) (((s+D:ℕ):ℝ)*(k:ℝ)/(e*σ)^2+1))
  have hnK : (k:ℝ)+2 < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hn0 : (0:ℝ) < (n:ℝ)-1 := by have : (0:ℝ) ≤ k := Nat.cast_nonneg _; linarith
  have hnB : ((s+D:ℕ):ℝ)*(k:ℝ)/(e*σ)^2 < (n:ℝ)-1 := by
    have := lt_of_le_of_lt (le_max_right _ _) hn
    linarith
  have hr : ((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1)) < (e*σ)^2 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hn0).mpr
    have := (div_lt_iff₀ (show 0 < (e*σ)^2 by positivity)).mp hnB
    linarith
  have hh := (Real.sqrt_lt' (show 0 < e*σ by positivity)).mpr hr
  refine ⟨n,?_,?_⟩
  · exact_mod_cast hnK.le
  · calc
      _ = Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1)))/σ := by ring
      _ < e := (div_lt_iff₀ hσ).mpr hh

lemma exists_small_rational_atoms {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    ∃ p θ : ℚ, 0 < (p:ℝ) ∧ (p:ℝ) < 1 ∧ 0 < (θ:ℝ) ∧ (θ:ℝ) < 1 ∧
      (θ:ℝ)^2+L*(p:ℝ) < B := by
  obtain ⟨θ,hθ,hθb⟩ := exists_rat_btwn (show (0:ℝ) < min 1 (B/4) by positivity)
  obtain ⟨p,hp,hpb⟩ := exists_rat_btwn (show (0:ℝ) < min 1 (B/(4*L)) by positivity)
  obtain ⟨hθ1,hθB⟩ := lt_min_iff.mp hθb
  obtain ⟨hp1,hpB⟩ := lt_min_iff.mp hpb
  have hLp : L*(p:ℝ) < B/4 := by
    have hh := (lt_div_iff₀ (show 0 < 4*L by positivity)).mp hpB
    nlinarith
  exact ⟨p,θ,hp,hp1,hθ,hθ1,by nlinarith⟩

lemma nested_atom_lt {σ e γ C Q : ℝ} (hσ : 0 < σ) (he : 0 < e) (hγ : 0 < γ) (hC : 0 < C)
    (hQ : Q < (e^2*σ^2*γ/C)^2) :
    Real.sqrt (σ⁻¹^2)*Real.sqrt (C*Real.sqrt Q/γ) < e := by
  have h1 := (Real.sqrt_lt' (show 0 < e^2*σ^2*γ/C by positivity)).mpr hQ
  have h2 : C*Real.sqrt Q/γ < (e*σ)^2 := by
    have hh := (lt_div_iff₀ hC).mp h1
    apply (div_lt_iff₀ hγ).mpr
    nlinarith
  have h3 := (Real.sqrt_lt' (show 0 < e*σ by positivity)).mpr h2
  rw [Real.sqrt_sq (by positivity : 0 ≤ σ⁻¹)]
  rw [mul_comm,← div_eq_mul_inv]
  exact (div_lt_iff₀ hσ).mpr h3
end MinUncut.Inner

end

end OAI
