import Mathlib
import OAI.Computability.MinUncut.Analysis.GaussianSliceContinuous
import OAI.Computability.MinUncut.Estimates.EraseAway
import OAI.Computability.MinUncut.Analysis.OddMaxTranslate

namespace OAI

variable {m n : ℕ}
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.RowNoise
open BinaryFourier GaussianHermite MeasureTheory
open scoped BigOperators
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι] [DecidableEq ι]

omit [DecidableEq W] [Module F₂ W] in
lemma expect_resample_row (r : R) (f : (R → W) → ℝ) :
    (𝔼 B : R → W, 𝔼 b : W, f (joinRow r b (fun t => B t.val)))=𝔼 B, f B := by
  conv_lhs => rw [expect_splitRow r]
  simp only [joinRow_other, Fintype.expect_const]
  rw [Finset.expect_comm]
  exact (expect_splitRow r f).symm

omit [DecidableEq W] [Module F₂ W] in
lemma expect_rest (r : R) (f : Rest (W := W) r → ℝ) :
    (𝔼 B : R → W, f (fun t => B t.val))=𝔼 D, f D := by
  rw [expect_splitRow r]
  simp only [joinRow_other, Fintype.expect_const]

omit [AddCommGroup W] [Module F₂ W] [DecidableEq ι] in
lemma selectedProject_continuous (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (B : R → W) :
    Continuous (selectedProject J u B) := by
  unfold selectedProject
  apply continuous_finsetSum
  intro j _
  change Continuous (fun c => maskHermite j.1 j.2 u B c)
  simp only [maskHermite_eq]
  exact (continuous_psi j.2).mul_const _
end MinUncut.RowNoise

namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pairSlice_measurable (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (B : FaceArray A m n) (b : Forms A) :
    Measurable (fun c => pairSlice f σ η x Y p J B c b) :=
  (selectedProject_continuous _ _ _).measurable

lemma pairSlice_memLp (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (B : FaceArray A m n) (b : Forms A) :
    MemLp (fun c => pairSlice f σ η x Y p J B c b) 2 (γpi (Point m n)) :=
  memLp_selectedProject _ _ _

lemma pairSlice_row (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (B : FaceArray A m n)
    (c : Point m n → ℝ) (b : Forms A) :
    selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x)
      (joinRow ⟨p.val.1,face x p.val.1⟩ b (fun t => B t.val)) c =
      pairSlice f σ η x Y p J B c (B ⟨p.val.2,face x p.val.2⟩+b) := by
  have hrs : (⟨p.val.2,face x p.val.2⟩ : Row m n) ≠ ⟨p.val.1,face x p.val.1⟩ := by
    intro h
    exact (ne_of_lt p.property) (congrArg Sigma.fst h).symm
  rw [retained_local_sum f hσ η x Y p J _ B]
  · rw [joinRow_at, joinRow_other _ _ _ ⟨_,hrs⟩, add_comm]
  · intro t ht
    have htr : t≠⟨p.val.1,face x p.val.1⟩ := by
      intro he; subst t; exact ht (local_free_left x Y p)
    exact joinRow_other _ _ _ ⟨t,htr⟩

theorem pairSlice_energy_law (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (c : Point m n → ℝ) :
    (𝔼 B : FaceArray A m n, 𝔼 b : Forms A, (pairSlice f σ η x Y p J B c b)^2) =
      𝔼 B, (selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x) B c)^2 := by
  let r : Row m n := ⟨p.val.1,face x p.val.1⟩
  let g : FaceArray A m n → ℝ := fun B =>
    (selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x) B c)^2
  have hB (B : FaceArray A m n) :
      (𝔼 b : Forms A, g (joinRow r b (fun t => B t.val))) =
        𝔼 b : Forms A, (pairSlice f σ η x Y p J B c b)^2 := by
    calc
      _ = 𝔼 b : Forms A, (pairSlice f σ η x Y p J B c (B ⟨p.val.2,face x p.val.2⟩+b))^2 := by
        apply Finset.expect_congr rfl
        intro b _
        exact congrArg (fun t : ℝ => t^2) (pairSlice_row f hσ η x Y p J B c b)
      _ = _ := expect_translate (fun b => (pairSlice f σ η x Y p J B c b)^2) _
  have h := expect_resample_row r g
  simp_rw [hB] at h
  exact h

lemma pairSlice_atom_law (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (B : FaceArray A m n) (c : Point m n → ℝ) :
    oddAtom ⟨p.val.1,face x p.val.1⟩ (AffineMap.const F₂ A 1)
      (fun B => selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x) B c)
      (fun t => B t.val) = Slice.oddMax (AffineMap.const F₂ A 1) (pairSlice f σ η x Y p J B c) := by
  change Slice.oddMax (AffineMap.const F₂ A 1) (fun b => selectedProject _ _ (joinRow _ b _) c)=_
  simp only [pairSlice_row f hσ, Slice.oddMax_translate]

theorem pairSlice_atom_mean (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (c : Point m n → ℝ) :
    (𝔼 B : FaceArray A m n, Slice.oddMax (AffineMap.const F₂ A 1) (pairSlice f σ η x Y p J B c)) =
      𝔼 D, oddAtom ⟨p.val.1,face x p.val.1⟩ (AffineMap.const F₂ A 1)
        (fun B => selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x) B c) D := by
  simp_rw [← pairSlice_atom_law f hσ]
  exact expect_rest _ _
end MinUncut.Inner
namespace MinUncut.Subbox
open OuterSmoothness
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

def pointBox {k : ℕ} (Y : UnpointedBox ι A k) (u : ι → Fin (k+1)) :
    PointedBox (pointEmbed Y u) k :=
  fun i => unpoint (pointEmbed Y u i) (Y i) (pointEmbed_mem Y u i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma pointBox_set {k : ℕ} (Y : UnpointedBox ι A k) (u : ι → Fin (k+1)) (i : ι) :
    pointedSet (pointEmbed Y u i) (pointBox Y u i)=(Y i).val :=
  pointed_unpoint _ _ _
end MinUncut.Subbox

namespace MinUncut.Inner
open Subbox
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def faceEmbed {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (i : Fin m)
    (v : {j : Fin m // j≠i} → Fin (k+1)) : {j : Fin m // j≠i} → Fin n :=
  fun j => (coordinateEnum Y j.val (v j)).val

lemma faceEmbed_injective {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (i : Fin m) :
    Function.Injective (faceEmbed Y i) := by
  intro u v h
  funext j
  apply (coordinateEnum Y j.val).injective
  apply Subtype.ext
  exact congrFun h j

lemma faceEmbed_mem {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (i : Fin m)
    (v : {j : Fin m // j≠i} → Fin (k+1)) (j : {j : Fin m // j≠i}) :
    faceEmbed Y i v j∈(Y j.val).val := (coordinateEnum Y j.val (v j)).property

@[simp] lemma faceEmbed_face {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k)
    (i : Fin m) (u : Point m (k+1)) : faceEmbed Y i (face u i)=face (pointEmbed Y u) i := rfl

def embedSingle {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (i : Fin m)
    (v : {j : Fin m // j≠i} → Fin (k+1)) : Row m n := ⟨i,faceEmbed Y i v⟩

lemma embedSingle_injective {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (i : Fin m) :
    Function.Injective (embedSingle Y i) := by
  intro u v h
  exact faceEmbed_injective Y i (sigma_mk_injective h)

def extendSingle {W : Type*} [Zero W] {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k)
    (i : Fin m) (B : ({j : Fin m // j≠i} → Fin (k+1)) → W) : Row m n → W :=
  Function.extend (embedSingle Y i) B (fun _ => 0)

@[simp] lemma extendSingle_local {W : Type*} [Zero W] {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (i : Fin m)
    (B : ({j : Fin m // j≠i} → Fin (k+1)) → W) (u : Point m (k+1)) :
    extendSingle Y i B ⟨i,face (pointEmbed Y u) i⟩ = B (face u i) :=
  (embedSingle_injective Y i).extend_apply B (fun _ => 0) (face u i)

lemma extendSingle_other {W : Type*} [Zero W] {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (i j : Fin m) (hij : i≠j)
    (B : ({j : Fin m // j≠i} → Fin (k+1)) → W) (v : {t : Fin m // t≠j} → Fin n) :
    extendSingle Y i B ⟨j,v⟩=0 := by
  apply Function.extend_apply'
  rintro ⟨u,hu⟩
  exact hij (congrArg Sigma.fst hu)

lemma extendSingle_support {W : Type*} [Zero W] {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (i : Fin m)
    (B : ({j : Fin m // j≠i} → Fin (k+1)) → W) (r : Row m n)
    (hr : extendSingle Y i B r≠0) : r.fst=i ∧ ∀ j, r.snd j∈(Y j.val).val := by
  by_cases h : ∃ u, embedSingle Y i u=r
  · obtain ⟨u,rfl⟩ := h
    exact ⟨rfl,faceEmbed_mem Y i u⟩
  · exact (hr (Function.extend_apply' _ _ _ h)).elim
end MinUncut.Inner
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

omit [Fintype A] in
lemma extendSingle_zero_outside_pair {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k)
    (u : Point m (k+1)) (p : PairClass m) (i : Fin m) (hi : i=p.val.1 ∨ i=p.val.2)
    (B : ({j : Fin m // j≠i} → Fin (k+1)) → Forms A) (r : Row m n)
    (hr : r∉freePairRows (pointEmbed Y u) (pointBox Y u) p) : extendSingle Y i B r=0 := by
  by_contra he
  have hs := extendSingle_support Y i B r he
  apply hr
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_,?_⟩
  · simpa only [hs.1] using hi
  · simpa only [FaceInBox, pointBox_set] using hs.2

lemma pairSlice_add_rows (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (u : Point m (k+1)) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (B : FaceArray A m n)
    (Bi : ({j : Fin m // j≠p.val.1} → Fin (k+1)) → Forms A)
    (Bj : ({j : Fin m // j≠p.val.2} → Fin (k+1)) → Forms A) :
    pairSlice f σ η (pointEmbed Y u) (pointBox Y u) p J
      (B+extendSingle Y p.val.1 Bi+extendSingle Y p.val.2 Bj) =
    pairSlice f σ η (pointEmbed Y u) (pointBox Y u) p J B := by
  apply pairSlice_background
  intro r hr
  simp only [Pi.add_apply, extendSingle_zero_outside_pair Y u p p.val.1 (Or.inl rfl) Bi r hr,
    extendSingle_zero_outside_pair Y u p p.val.2 (Or.inr rfl) Bj r hr, add_zero]

def pairProcessedOnBox (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ A₀ : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ) (u : Point m (k+1)) : ℝ :=
  Slice.processed H γ A₀ (AffineMap.const F₂ A 1)
    (pairSlice f σ η (pointEmbed Y u) (pointBox Y u) p J B c)
    (B ⟨p.val.1,face (pointEmbed Y u) p.val.1⟩+B ⟨p.val.2,face (pointEmbed Y u) p.val.2⟩)

lemma pairProcessedOnBox_resample (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ A₀ : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ)
    (Bi : ({j : Fin m // j≠p.val.1} → Fin (k+1)) → Forms A)
    (Bj : ({j : Fin m // j≠p.val.2} → Fin (k+1)) → Forms A) :
    pairProcessedOnBox f σ η Y p J H γ A₀ (B+extendSingle Y p.val.1 Bi+extendSingle Y p.val.2 Bj) c =
      pairField p.val.1 p.val.2
        (fun u => Slice.processed H γ A₀ (AffineMap.const F₂ A 1)
          (pairSlice f σ η (pointEmbed Y u) (pointBox Y u) p J B c))
        ((fun v => B ⟨p.val.2,faceEmbed Y p.val.2 v⟩)+Bj)
        ((fun v => B ⟨p.val.1,faceEmbed Y p.val.1 v⟩)+Bi) := by
  funext u
  have hij := ne_of_lt p.property
  unfold pairProcessedOnBox pairField
  rw [pairSlice_add_rows]
  simp only [Pi.add_apply,extendSingle_local,extendSingle_other Y _ _ hij,
    extendSingle_other Y _ _ hij.symm,add_zero,faceEmbed_face]
  congr 1
  abel

theorem pairProcessedOnBox_law (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ A₀ : ℝ) (c : Point m n → ℝ) :
    (𝔼 B : FaceArray A m n, faceCorrelation (pairProcessedOnBox f σ η Y p J H γ A₀ B c)) =
      𝔼 B : FaceArray A m n, 𝔼 Bj, 𝔼 Bi, faceCorrelation (pairField p.val.1 p.val.2
        (fun u => Slice.processed H γ A₀ (AffineMap.const F₂ A 1)
          (pairSlice f σ η (pointEmbed Y u) (pointBox Y u) p J B c)) Bj Bi) := by
  let G (B : FaceArray A m n) := faceCorrelation (pairProcessedOnBox f σ η Y p J H γ A₀ B c)
  have hm : (𝔼 B : FaceArray A m n,
      𝔼 Bj : ({j : Fin m // j≠p.val.2} → Fin (k+1)) → Forms A,
      𝔼 Bi : ({j : Fin m // j≠p.val.1} → Fin (k+1)) → Forms A,
      G (B+extendSingle Y p.val.1 Bi+extendSingle Y p.val.2 Bj)) = 𝔼 B, G B := by
    rw [Finset.expect_comm]
    conv_lhs => arg 2; ext Bj; rw [Finset.expect_comm]
    have ht (Bj : ({j : Fin m // j≠p.val.2} → Fin (k+1)) → Forms A)
        (Bi : ({j : Fin m // j≠p.val.1} → Fin (k+1)) → Forms A) :
        (𝔼 B : FaceArray A m n, G (B+extendSingle Y p.val.1 Bi+extendSingle Y p.val.2 Bj))=𝔼 B,G B := by
      have he (B : FaceArray A m n) :
          B+extendSingle Y p.val.1 Bi+extendSingle Y p.val.2 Bj=
            (extendSingle Y p.val.1 Bi+extendSingle Y p.val.2 Bj)+B := by abel
      simp_rw [he]
      exact expect_translate G _
    simp only [ht,Fintype.expect_const]
  rw [← hm]
  apply Finset.expect_congr rfl
  intro B _
  simp only [G,pairProcessedOnBox_resample]
  let P := fun Bj Bi => faceCorrelation (pairField p.val.1 p.val.2
    (fun u => Slice.processed H γ A₀ (AffineMap.const F₂ A 1)
      (pairSlice f σ η (pointEmbed Y u) (pointBox Y u) p J B c)) Bj Bi)
  let Rj := fun v => B ⟨p.val.2,faceEmbed Y p.val.2 v⟩
  let Ri := fun v => B ⟨p.val.1,faceEmbed Y p.val.1 v⟩
  change (𝔼 Bj,𝔼 Bi,P (Rj+Bj) (Ri+Bi))=𝔼 Bj,𝔼 Bi,P Bj Bi
  calc
    _ = 𝔼 Bj, 𝔼 Bi, P (Rj+Bj) Bi := by
      apply Finset.expect_congr rfl
      intro Bj _
      exact expect_translate (fun Bi => P (Rj+Bj) Bi) Ri
    _ = _ := expect_translate (fun Bj => 𝔼 Bi,P Bj Bi) Rj

theorem actual_pair_box_power (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (hm : 0 < m) {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (c : Point m n → ℝ)
    {H γ A₀ : ℝ} (hA : 0 < A₀) (hγ : 0 ≤ γ) :
    (𝔼 B : FaceArray A m n, faceCorrelation (pairProcessedOnBox f σ η Y p J H γ A₀ B c))^(2^m) ≤
      A₀^(2^m)*((m:ℝ)/(k+1)) + ((γ+H^2/A₀)^2*H^2)^(2^Fintype.card (CubeRows.Other p.val.1 p.val.2)) := by
  rw [pairProcessedOnBox_law]
  calc
    _ ≤ 𝔼 B : FaceArray A m n, (𝔼 Bj, 𝔼 Bi, faceCorrelation (pairField p.val.1 p.val.2
      (fun u => Slice.processed H γ A₀ (AffineMap.const F₂ A 1)
        (pairSlice f σ η (pointEmbed Y u) (pointBox Y u) p J B c)) Bj Bi))^(2^m) := Box.expect_pow_two_pow _ m
    _ ≤ 𝔼 _B : FaceArray A m n, (A₀^(2^m)*((m:ℝ)/(k+1)) +
        ((γ+H^2/A₀)^2*H^2)^(2^Fintype.card (CubeRows.Other p.val.1 p.val.2))) := by
      apply Finset.expect_le_expect
      intro B _
      rw [show (k : ℝ)+1=((k+1 : ℕ) : ℝ) by push_cast; rfl]
      apply pair_correlation_power hm (by omega) _ _ (ne_of_lt p.property) _ (γ+H^2/A₀) H A₀
        (by positivity) hA.le
      · intro u α
        exact Slice.processed_coefficient_le hA hγ _ _
          (pairSlice_coefficient_zero f hσ η (pointEmbed Y u) (pointBox Y u) p J B c) α
      · intro u
        exact Slice.processed_energy_le hA.le _ _
      · intro u b
        exact Slice.processed_abs_le hA.le _ _ b
    _ = _ := Fintype.expect_const _
end MinUncut.Inner
namespace MinUncut.BoxGaussian
open MeasureTheory
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
attribute [local instance] Classical.propDecidable

abbrev Outside (e : κ → ι) := {i : ι // i∉Set.range e}

def indexEquiv (e : κ → ι) (he : Function.Injective e) : κ ⊕ Outside e ≃ ι :=
  ((Equiv.ofInjective e he).sumCongr (Equiv.refl (Outside e))).trans (Equiv.Set.sumCompl (Set.range e))

omit [Fintype ι] in
@[simp] lemma indexEquiv_left (e : κ → ι) (he : Function.Injective e) (j : κ) :
    indexEquiv e he (Sum.inl j)=e j := rfl
omit [Fintype ι] in
@[simp] lemma indexEquiv_right (e : κ → ι) (he : Function.Injective e) (j : Outside e) :
    indexEquiv e he (Sum.inr j)=j.val := rfl

omit [Fintype ι] in
lemma indexEquiv_symm_left (e : κ → ι) (he : Function.Injective e) (j : κ) :
    (indexEquiv e he).symm (e j)=Sum.inl j := by
  apply (indexEquiv e he).injective
  simp only [Equiv.apply_symm_apply,indexEquiv_left]

omit [Fintype ι] in
lemma indexEquiv_symm_right (e : κ → ι) (he : Function.Injective e) (j : Outside e) :
    (indexEquiv e he).symm j.val=Sum.inr j := by
  apply (indexEquiv e he).injective
  simp only [Equiv.apply_symm_apply,indexEquiv_right]

def joinEquiv (e : κ → ι) (he : Function.Injective e) :
    ((κ → ℝ) × (Outside e → ℝ)) ≃ᵐ (ι → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : κ ⊕ Outside e => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) (indexEquiv e he))

def join (e : κ → ι) (he : Function.Injective e) (C : κ → ℝ) (D : Outside e → ℝ) : ι → ℝ :=
  joinEquiv e he (C,D)

omit [Fintype ι] in
@[simp] lemma join_at (e : κ → ι) (he : Function.Injective e) (C : κ → ℝ) (D : Outside e → ℝ) (j : κ) :
    join e he C D (e j)=C j := by
  simp [join,joinEquiv,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,indexEquiv_symm_left,MeasurableEquiv.coe_sumPiEquivProdPi_symm]

omit [Fintype ι] in
@[simp] lemma join_other (e : κ → ι) (he : Function.Injective e) (C : κ → ℝ) (D : Outside e → ℝ) (j : Outside e) :
    join e he C D j.val=D j := by
  simp [join,joinEquiv,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,indexEquiv_symm_right,MeasurableEquiv.coe_sumPiEquivProdPi_symm]

lemma join_preserves (μ : Measure ℝ) [SigmaFinite μ] (e : κ → ι) (he : Function.Injective e) :
    MeasurePreserving (joinEquiv e he)
      ((Measure.pi (fun _ : κ => μ)).prod (Measure.pi (fun _ : Outside e => μ)))
      (Measure.pi (fun _ : ι => μ)) :=
  (measurePreserving_piCongrLeft (fun _ : ι => μ) (indexEquiv e he)).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ Outside e => μ))

lemma integral_split (μ : Measure ℝ) [SigmaFinite μ] (e : κ → ι) (he : Function.Injective e)
    (f : (ι → ℝ) → ℝ) (hf : Integrable f (Measure.pi (fun _ : ι => μ))) :
    (∫ c, f c ∂Measure.pi (fun _ : ι => μ)) =
      ∫ D, ∫ C, f (join e he C D) ∂Measure.pi (fun _ : κ => μ) ∂Measure.pi (fun _ : Outside e => μ) := by
  have hp := join_preserves μ e he
  have hi := (hp.integrable_comp_emb (joinEquiv e he).measurableEmbedding).mpr hf
  rw [← hp.integral_comp (joinEquiv e he).measurableEmbedding]
  exact integral_prod_symm _ hi
end MinUncut.BoxGaussian
namespace MinUncut.Box
lemma power_le_root {x a : ℝ} (hx : 0≤x) (ha : 0≤a) {q : ℕ} (hq : q≠0)
    (h : x^q≤a) : x≤a^((q:ℝ)⁻¹) := by
  apply (pow_le_pow_iff_left₀ hx (Real.rpow_nonneg ha _) hq).mp
  rwa [Real.rpow_inv_natCast_pow ha hq]

lemma power_sum_root {x a b : ℝ} (hx : 0≤x) (ha : 0≤a) (hb : 0≤b)
    {q : ℕ} (hq : q≠0) (h : x^q≤a+b) :
    x≤a^((q:ℝ)⁻¹)+b^((q:ℝ)⁻¹) := by
  apply (pow_le_pow_iff_left₀ hx (by positivity) hq).mp
  calc
    _ ≤ a+b := h
    _ = (a^((q:ℝ)⁻¹))^q+(b^((q:ℝ)⁻¹))^q := by
      rw [Real.rpow_inv_natCast_pow ha hq,Real.rpow_inv_natCast_pow hb hq]
    _ ≤ _ := pow_add_pow_le (by positivity) (by positivity) hq

lemma square_root_power {H ε : ℝ} (hH : 0≤H) (hε : 0≤ε) {m : ℕ} (hm : 2 ≤ m) :
    (Real.sqrt (H*ε))^(2^m)=(ε^2*H^2)^(2^(m-2)) := by
  have he : 2^m=4*2^(m-2) := by
    calc
      _ = 2^(2+(m-2)) := by congr; omega
      _ = _ := by rw [pow_add]; norm_num
  rw [he,pow_mul]
  have hh : (Real.sqrt (H*ε))^4=ε^2*H^2 := by
    calc
      _ = ((Real.sqrt (H*ε))^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (mul_nonneg hH hε)]; ring
  rw [hh]

lemma cube_power_to_bound {x A H ε d : ℝ} (hx : 0≤x) (hA : 0≤A)
    (hH : 0≤H) (hε : 0≤ε) (hd : 0≤d) {m : ℕ} (hm : 2 ≤ m)
    (h : x^(2^m)≤A^(2^m)*d+(ε^2*H^2)^(2^(m-2))) :
    x≤A*d^(((2^m:ℕ):ℝ)⁻¹)+Real.sqrt (H*ε) := by
  have hq : (2^m:ℕ)≠0 := by positivity
  apply (pow_le_pow_iff_left₀ hx (by positivity) hq).mp
  calc
    _ ≤ A^(2^m)*d+(ε^2*H^2)^(2^(m-2)) := h
    _ = (A*d^(((2^m:ℕ):ℝ)⁻¹))^(2^m)+(Real.sqrt (H*ε))^(2^m) := by
      rw [mul_pow A (d^(((2^m:ℕ):ℝ)⁻¹)) (2^m),Real.rpow_inv_natCast_pow hd hq,square_root_power hH hε hm]
    _ ≤ _ := pow_add_pow_le (by positivity) (by positivity) hq
end MinUncut.Box
namespace MinUncut.CubeRows
lemma card_other {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) (hij : i≠j) :
    Fintype.card {k : ι // k≠i ∧ k≠j}=Fintype.card ι-2 := by
  let e : {k : ι // k≠i ∧ k≠j} ≃ {k : ι // k∈({i,j}:Finset ι)ᶜ} :=
    Equiv.subtypeEquivRight (fun k => by simp only [Finset.mem_compl,Finset.mem_insert,
      Finset.mem_singleton,not_or])
  calc
    _ = (({i,j}:Finset ι)ᶜ).card := (Fintype.card_congr e).trans (Fintype.card_coe _)
    _ = _ := by simp [Finset.card_compl,hij]; omega
end MinUncut.CubeRows
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma gaussianSlice_background (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (C D : Point m n → ℝ)
    (hCD : ∀ y ∉ freeGaussianPoints x Y, C y=D y) :
    gaussianSlice f σ η x Y J B C=gaussianSlice f σ η x Y J B D := by
  funext t
  unfold gaussianSlice
  have hh := selectedProject_gaussian_local (retainedClass x Y none J)
    (fun B c => gradient f B σ η c x) x (freeGaussianPoints x Y)
    (retained_gaussian_local x Y none J) B (Function.update C x t) (Function.update D x t)
    (fun y hy => by
      by_cases he : y=x
      · subst y; simp only [Function.update_self]
      · simp only [Function.update_of_ne he,hCD y hy])
  simpa only [Function.update_idem,Function.update_self] using hh

lemma faceCorrelation_measurable_field {Ω : Type*} [MeasurableSpace Ω]
    (v : Ω → Point m n → ℝ) (hv : ∀ x, Measurable (fun t => v t x)) :
    Measurable (fun t => faceCorrelation (v t)) := by
  have hh : Measurable (Finset.sup' Finset.univ Finset.univ_nonempty
      (fun (z : Code m n) t => |𝔼 x, v t x * sign (z.val x)|)) := by
    apply Finset.measurable_sup'
    intro z _
    apply Measurable.abs
    simp only [Finset.expect_eq_sum_div_card]
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro x _
    exact (hv x).mul measurable_const
  change Measurable (fun t => (Finset.univ.sup' Finset.univ_nonempty
    (fun (z : Code m n) t => |𝔼 x, v t x * sign (z.val x)|)) t) at hh
  simpa only [faceCorrelation,Finset.sup'_apply] using hh

lemma gaussianSlice_joint_continuous (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) :
    Continuous (fun p : (Point m n → ℝ) × ℝ => gaussianSlice f σ η x Y J B p.1 p.2) := by
  apply (selectedProject_continuous _ _ B).comp
  apply continuous_pi
  intro y
  by_cases he : y=x
  · subst y; simpa only [Function.update_self] using continuous_snd
  · simp only [Function.update_of_ne he]
    exact (continuous_apply y).comp continuous_fst

lemma centered_gaussianSlice_measurable (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (A₀ : ℝ) :
    Measurable (fun p : (Point m n → ℝ) × ℝ =>
      Slice.centeredClip γ A₀ (gaussianSlice f σ η x Y J B p.1) p.2) := by
  have hc : Continuous (fun p : (Point m n → ℝ) × ℝ =>
      Slice.clip A₀ (gaussianSlice f σ η x Y J B p.1 p.2)) := by
    unfold Slice.clip
    exact continuous_const.max ((gaussianSlice_joint_continuous f σ η x Y J B).min continuous_const)
  unfold Slice.centeredClip
  have hi : Measurable (fun C => ∫ t, Slice.clip A₀ (gaussianSlice f σ η x Y J B C t) ∂γ) :=
    hc.stronglyMeasurable.integral_prod_right.measurable
  exact hc.measurable.sub (hi.comp measurable_fst)

def zeroProcessedOnBox (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (A₀ : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ) (u : Point m (k+1)) : ℝ :=
  Slice.centeredClip γ A₀ (gaussianSlice f σ η (pointEmbed Y u) (pointBox Y u) J B c)
    (c (pointEmbed Y u))

attribute [local irreducible] gaussianSlice Slice.centeredClip

lemma centered_gaussianSlice_diagonal_measurable (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (A₀ : ℝ) :
    Measurable (fun c : Point m n → ℝ =>
      Slice.centeredClip γ A₀ (gaussianSlice f σ η x Y J B c) (c x)) := by
  have hh := centered_gaussianSlice_measurable f σ η x Y J B A₀
  have hg : Measurable (fun c : Point m n → ℝ => (c,c x)) :=
    measurable_id.prodMk (measurable_pi_apply x)
  exact hh.comp hg

attribute [local irreducible] pointEmbed coordinateEnum

lemma zeroProcessedOnBox_measurable (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (A₀ : ℝ)
    (B : FaceArray A m n) (u : Point m (k+1)) :
    Measurable (fun c => zeroProcessedOnBox f σ η Y J A₀ B c u) := by
  simpa only [zeroProcessedOnBox] using
    centered_gaussianSlice_diagonal_measurable f σ η (pointEmbed Y u) (pointBox Y u) J B A₀

lemma zeroProcessedOnBox_abs_le (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) {A₀ : ℝ} (hA : 0≤A₀)
    (B : FaceArray A m n) (c : Point m n → ℝ) (u : Point m (k+1)) :
    |zeroProcessedOnBox f σ η Y J A₀ B c u|≤2*A₀ :=
  Slice.centeredClip_abs_le hA (gaussianSlice_memLp f σ η (pointEmbed Y u) (pointBox Y u) J B c) (c (pointEmbed Y u))

lemma freeGaussianPoints_range {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k)
    (u : Point m (k+1)) (x : Point m n) :
    x∈freeGaussianPoints (pointEmbed Y u) (pointBox Y u) ↔ x∈Set.range (pointEmbed Y) := by
  simp only [freeGaussianPoints,Finset.mem_filter,Finset.mem_univ,true_and,InBox,pointBox_set]
  constructor
  · intro hx
    let v : BoxPoint Y := fun i => ⟨x i,hx i⟩
    unfold pointEmbed
    exact ⟨(pointEnum Y).symm v, congrArg (fun v : BoxPoint Y => fun i => (v i).val) ((pointEnum Y).apply_symm_apply v)⟩
  · rintro ⟨v,rfl⟩
    exact pointEmbed_mem Y v

lemma zeroProcessedOnBox_join (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (A₀ : ℝ)
    (B : FaceArray A m n) (C : Point m (k+1) → ℝ) (D : BoxGaussian.Outside (pointEmbed Y) → ℝ) :
    zeroProcessedOnBox f σ η Y J A₀ B (BoxGaussian.join _ (pointEmbed_injective Y) C D) =
      pointField (fun u => Slice.centeredClip γ A₀
        (gaussianSlice f σ η (pointEmbed Y u) (pointBox Y u) J B
          (BoxGaussian.join _ (pointEmbed_injective Y) 0 D))) C := by
  funext u
  unfold zeroProcessedOnBox pointField
  rw [BoxGaussian.join_at]
  have hh : gaussianSlice f σ η (pointEmbed Y u) (pointBox Y u) J B
      (BoxGaussian.join _ (pointEmbed_injective Y) C D) =
      gaussianSlice f σ η (pointEmbed Y u) (pointBox Y u) J B
      (BoxGaussian.join _ (pointEmbed_injective Y) 0 D) := by
    apply gaussianSlice_background
    intro x hx
    have ho : x∉Set.range (pointEmbed Y) := by simpa only [← freeGaussianPoints_range Y u] using hx
    exact (BoxGaussian.join_other _ _ C D ⟨x,ho⟩).trans (BoxGaussian.join_other _ _ 0 D ⟨x,ho⟩).symm
  rw [hh]
end MinUncut.Inner
namespace MinUncut.BoxGaussian
open MeasureTheory ProbabilityTheory
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
attribute [local instance] Classical.propDecidable

lemma integral_split_power_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (e : κ → ι) (he : Function.Injective e) (G : (ι → ℝ) → ℝ)
    (hG : Measurable G) {C L : ℝ} (hb : ∀ c, |G c|≤C)
    (hp : ∀ c, 0≤G c) (q : ℕ)
    (hlocal : ∀ D : Outside e → ℝ,
      (∫ c, G (join e he c D) ∂Measure.pi (fun _ : κ => μ))^q≤L) :
    (∫ c, G c ∂Measure.pi (fun _ : ι => μ))^q≤L := by
  let F := fun p : (Outside e → ℝ) × (κ → ℝ) => G (join e he p.2 p.1)
  have hF : Measurable F := hG.comp ((joinEquiv e he).measurable.comp (measurable_snd.prodMk measurable_fst))
  let Q := fun D : Outside e → ℝ => ∫ c, F (D,c) ∂Measure.pi (fun _ : κ => μ)
  have hQ : Measurable Q := hF.stronglyMeasurable.integral_prod_right.measurable
  have hQb D : |Q D|≤C := by
    calc
      _ ≤ ∫ c, |F (D,c)| ∂Measure.pi (fun _ : κ => μ) := abs_integral_le_integral_abs
      _ ≤ ∫ _c : κ → ℝ, C ∂Measure.pi (fun _ : κ => μ) := by
        apply integral_mono
        · exact (Box.bounded_integrable (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (fun c => hb _)).abs
        · exact integrable_const _
        · intro c; exact hb _
      _ = _ := by simp
  have hQp D : 0≤Q D := integral_nonneg (fun c => hp _)
  rw [integral_split μ e he G (Box.bounded_integrable hG.aestronglyMeasurable hb)]
  calc
    _ ≤ ∫ D, (Q D)^q ∂Measure.pi (fun _ : Outside e => μ) :=
      Box.integral_pow_bound hQ.aestronglyMeasurable hQb hQp q
    _ ≤ ∫ _D : Outside e → ℝ, L ∂Measure.pi (fun _ : Outside e => μ) := by
      apply integral_mono
      · apply Box.bounded_integrable (C := C^q) (hQ.aestronglyMeasurable.pow q)
        intro D
        simpa only [Pi.pow_apply,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hQb D) q
      · exact integrable_const _
      · exact hlocal
    _ = _ := by simp
end MinUncut.BoxGaussian
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] pointEmbed coordinateEnum gaussianSlice Slice.centeredClip zeroProcessedOnBox faceCorrelation Finset.univ Fintype.piFinset
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

theorem actual_zero_box_power (f : FoldedProof A) (σ η : ℝ) (hm : 0 < m) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) {A₀ : ℝ} (hA : 0≤A₀)
    (B : FaceArray A m n) :
    (∫ c, faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B c) ∂γpi (Point m n))^(2^m) ≤
      (2*A₀)^(2^m)*((m:ℝ)/(k+1)) := by
  let G := fun c => faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B c)
  have hG : Measurable G := faceCorrelation_measurable_field _ (zeroProcessedOnBox_measurable f σ η Y J A₀ B)
  have hGb (c : Point m n → ℝ) : |G c|≤2*A₀ := by
    rw [abs_of_nonneg (faceCorrelation_nonneg _)]
    exact (faceCorrelation_le_l1 _).trans ((Finset.expect_le_expect (fun u _ =>
      zeroProcessedOnBox_abs_le f σ η Y J hA B c u)).trans_eq (Fintype.expect_const _))
  apply BoxGaussian.integral_split_power_bound γ (pointEmbed Y) (pointEmbed_injective Y) G hG hGb
    (fun c => faceCorrelation_nonneg _) (2^m)
  intro D
  change (∫ C, faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B
    (BoxGaussian.join (pointEmbed Y) (pointEmbed_injective Y) C D)) ∂γpi (Point m (k+1)))^(2^m)≤_
  simp_rw [zeroProcessedOnBox_join]
  rw [show (k : ℝ)+1=((k+1 : ℕ) : ℝ) by push_cast; rfl]
  exact centered_point_correlation_power γ _
    (fun u => Slice.centeredClip_continuous γ A₀ _
      (gaussianSlice_continuous f σ η (pointEmbed Y u) (pointBox Y u) J B _))
    (by positivity)
    (fun u t => Slice.centeredClip_abs_le hA (gaussianSlice_memLp f σ η (pointEmbed Y u) (pointBox Y u) J B _) t)
    (fun u => Slice.centeredClip_mean_zero hA (gaussianSlice_memLp f σ η (pointEmbed Y u) (pointBox Y u) J B _))
    hm (by omega)
end MinUncut.Inner
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] pointEmbed coordinateEnum pairSlice Slice.processed pairProcessedOnBox faceCorrelation
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pairClass_dimension (p : PairClass m) : 2 ≤ m := by
  have h1 := p.property
  have h2 := p.val.2.isLt
  have h0 := p.val.1.isLt
  change p.val.1.val < p.val.2.val at h1
  omega

theorem actual_pair_box_bound (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (c : Point m n → ℝ)
    {H γ A₀ : ℝ} (hH : 0≤H) (hA : 0<A₀) (hγ : 0≤γ) :
    (𝔼 B : FaceArray A m n, faceCorrelation (pairProcessedOnBox f σ η Y p J H γ A₀ B c)) ≤
      A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹)+Real.sqrt (H*(γ+H^2/A₀)) := by
  have hm := pairClass_dimension p
  apply Box.cube_power_to_bound (Finset.expect_nonneg (fun B _ => faceCorrelation_nonneg _))
    hA.le hH (by positivity) (by positivity) hm
  have hh := actual_pair_box_power f hσ η (by omega) Y p J c (H := H) hA hγ
  simpa only [CubeRows.Other,CubeRows.card_other p.val.1 p.val.2 (ne_of_lt p.property),Fintype.card_fin] using hh

lemma pairSlice_c_measurable (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (B : FaceArray A m n) (b : Forms A) :
    Measurable (fun c => pairSlice f σ η x Y p J B c b) := by
  unfold pairSlice localSlice
  exact (selectedProject_continuous _ _ _).measurable

lemma pairProcessedOnBox_c_measurable (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ A₀ : ℝ)
    (B : FaceArray A m n) (u : Point m (k+1)) :
    Measurable (fun c => pairProcessedOnBox f σ η Y p J H γ A₀ B c u) := by
  unfold pairProcessedOnBox
  exact Slice.processed_measurable _ _ (pairSlice_c_measurable f σ η _ _ p J B) H γ A₀ _

lemma pairProcessedOnBox_abs_le (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ : ℝ) {A₀ : ℝ} (hA : 0≤A₀)
    (B : FaceArray A m n) (c : Point m n → ℝ) (u : Point m (k+1)) :
    |pairProcessedOnBox f σ η Y p J H γ A₀ B c u|≤A₀ := by
  unfold pairProcessedOnBox
  exact Slice.processed_abs_le hA _ _ _
end MinUncut.Inner
namespace MinUncut.Subbox
open OuterSmoothness
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

theorem pointed_bayes (k : ℕ) (f : (x : ι → A) → PointedBox x k → ℝ) :
    (𝔼 x : ι → A, 𝔼 H : PointedBox x k, f x H) =
      𝔼 Y : UnpointedBox ι A k, 𝔼 u : ι → Fin (k+1), f (pointEmbed Y u) (pointBox Y u) := by
  rw [expect_sigma_const _ (fun x => card_pointedBox x k)]
  have hb : (𝔼 Y : UnpointedBox ι A k, 𝔼 u : ι → Fin (k+1), f (pointEmbed Y u) (pointBox Y u)) =
      𝔼 Y : UnpointedBox ι A k, 𝔼 v : BoxPoint Y,
        f (fun i => (v i).val) (fun i => unpoint (v i).val (Y i) (v i).property) := by
    apply Finset.expect_congr rfl
    intro Y _
    exact Fintype.expect_equiv (pointEnum Y) _ _ (fun u => rfl)
  rw [hb,expect_sigma_const _ (fun Y => card_boxPoint Y)]
  apply Fintype.expect_equiv (boxJointEquiv (ι := ι) (A := A) k)
  rintro ⟨x,H⟩
  change f x H=f x (fun i => unpoint (x i) ⟨pointedSet (x i) (H i),pointedSet_card (x i) (H i)⟩ (mem_pointedSet_self (x i) (H i)))
  congr 1
  funext i
  exact (unpoint_pointed (x i) (H i)).symm
end MinUncut.Subbox
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] pointEmbed coordinateEnum pairSlice Slice.processed pairProcessedOnBox faceCorrelation
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

theorem actual_pair_box_average (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    {H γ₀ A₀ : ℝ} (hH : 0≤H) (hA : 0<A₀) (hγ : 0≤γ₀) :
    (∫ c, (𝔼 B : FaceArray A m n,
      faceCorrelation (pairProcessedOnBox f σ η Y p J H γ₀ A₀ B c)) ∂γpi (Point m n)) ≤
      A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹)+Real.sqrt (H*(γ₀+H^2/A₀)) := by
  let G := fun c : Point m n → ℝ => 𝔼 B : FaceArray A m n,
    faceCorrelation (pairProcessedOnBox f σ η Y p J H γ₀ A₀ B c)
  have hm : Measurable G := by
    simp only [G,Finset.expect_eq_sum_div_card]
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro B _
    exact faceCorrelation_measurable_field _ (pairProcessedOnBox_c_measurable f σ η Y p J H γ₀ A₀ B)
  have hb c : |G c|≤A₀ := by
    rw [abs_of_nonneg (Finset.expect_nonneg (fun B _ => faceCorrelation_nonneg _))]
    calc
      _ ≤ 𝔼 _B : FaceArray A m n, A₀ := by
        apply Finset.expect_le_expect
        intro B _
        exact (faceCorrelation_le_l1 _).trans ((Finset.expect_le_expect (fun u _ =>
          pairProcessedOnBox_abs_le f σ η Y p J H γ₀ hA.le B c u)).trans_eq (Fintype.expect_const _))
      _ = _ := Fintype.expect_const _
  change (∫ c, G c ∂γpi (Point m n))≤_
  calc
    _ ≤ ∫ _c : Point m n → ℝ,
        A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹)+Real.sqrt (H*(γ₀+H^2/A₀)) ∂γpi (Point m n) := by
      apply integral_mono (Box.bounded_integrable hm.aestronglyMeasurable hb) (integrable_const _)
      intro c
      exact actual_pair_box_bound f hσ η Y p J c hH hA hγ
    _ = _ := by simp
end MinUncut.Inner

end

end OAI
