import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.LabeledPolynomial

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open ElementaryPositivity.SeparatedSymmetry
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A B : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
  [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)]

noncomputable def sumPackCut (A B : I → Type*) [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
    [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)] :
    PackConvolution.Cut (fun i=>(Finset.univ : Finset (A i ⊕ B i))) := fun i=>
  ⟨((Finset.univ.map Function.Embedding.inl),(Finset.univ.map Function.Embedding.inr)),by
    constructor
    · apply Finset.disjoint_left.mpr
      intro x hx hy
      simp only [Finset.mem_map,Finset.mem_univ,true_and] at hx hy
      obtain ⟨x,rfl⟩ := hx
      obtain ⟨y,h⟩ := hy
      change Sum.inr y = Sum.inl x at h
      cases h
    · ext x
      cases x <;> simp⟩

abbrev FourPacks (d₁ e₁ d₂ e₂ : I → ℕ) (i : I) :=
  (Fin (d₁ i) ⊕ Fin (e₁ i)) ⊕ (Fin (d₂ i) ⊕ Fin (e₂ i))

noncomputable def canonicalGridCut (d₁ e₁ d₂ e₂ : I → ℕ) :=
  sumPackCut (fun i=>Fin (d₁ i) ⊕ Fin (e₁ i)) (fun i=>Fin (d₂ i) ⊕ Fin (e₂ i))

noncomputable def canonicalLeftCut (d₁ e₁ d₂ e₂ : I → ℕ) :
    PackConvolution.Cut (left (canonicalGridCut d₁ e₁ d₂ e₂)) :=
  embedPackCut (fun _=>Function.Embedding.inl)
    (sumPackCut (fun i=>Fin (d₁ i)) (fun i=>Fin (e₁ i)))

noncomputable def canonicalRightCut (d₁ e₁ d₂ e₂ : I → ℕ) :
    PackConvolution.Cut (right (canonicalGridCut d₁ e₁ d₂ e₂)) :=
  embedPackCut (fun _=>Function.Embedding.inr)
    (sumPackCut (fun i=>Fin (d₂ i)) (fun i=>Fin (e₂ i)))

noncomputable def canonicalGridPolynomial (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g : S e) (d₁ e₁ d₂ e₂ : I → ℕ) :
    MvPolynomial (Σi,FourPacks d₁ e₁ d₂ e₂ i) ℚ :=
  gridPolynomial a f g (canonicalGridCut d₁ e₁ d₂ e₂)
    (canonicalLeftCut d₁ e₁ d₂ e₂) (canonicalRightCut d₁ e₁ d₂ e₂)

def fourPackAction (d₁ e₁ d₂ e₂ : I → ℕ)
    (σ : CellGroup d₁ e₁ × CellGroup d₂ e₂) (i : I) :
    Equiv.Perm (FourPacks d₁ e₁ d₂ e₂ i) :=
  Equiv.sumCongr (Equiv.sumCongr (σ.1.1 i) (σ.1.2 i))
    (Equiv.sumCongr (σ.2.1 i) (σ.2.2 i))

lemma gridPolynomial_stabilized {C : I → Type*} [∀ i,Fintype (C i)] [∀ i,DecidableEq (C i)]
    (σ : ∀ i,Equiv.Perm (C i)) (a : I → I → ℕ) {d e : I → ℕ} (f : S d) (g : S e)
    {s : Pack (A:=C)} (p : PackConvolution.Cut s)
    (q : PackConvolution.Cut (left p)) (r : PackConvolution.Cut (right p))
    (hp₁ : mapPack σ (left p) = left p) (hp₂ : mapPack σ (right p) = right p)
    (hq₁ : mapPack σ (left q) = left q) (hq₂ : mapPack σ (right q) = right q)
    (hr₁ : mapPack σ (left r) = left r) (hr₂ : mapPack σ (right r) = right r) :
    rename (packAction C σ) (gridPolynomial a f g p q r) = gridPolynomial a f g p q r := by
  have hc : rename (packAction C σ) (crossKernelPolynomial a p q r) =
      crossKernelPolynomial a p q r := by
    apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,C i) ℚ))
    rw [← renameFraction_algebraMap (packAction C σ),← crossKernelPolynomial_spec,
      map_mul,map_mul,renameFraction_algebraMap,rename_sameDen,
      rename_pack_kernel,rename_pack_kernel,hp₁,hp₂,hq₁,hq₂,hr₁,hr₂]
  simp only [gridPolynomial,map_mul,rename_labeledPolynomial,mapPack_union,hq₁,hq₂,hr₁,hr₂,hc]

lemma canonicalGridPolynomial_invariant (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g : S e) (d₁ e₁ d₂ e₂ : I → ℕ)
    (σ : CellGroup d₁ e₁ × CellGroup d₂ e₂) :
    rename (packAction (FourPacks d₁ e₁ d₂ e₂) (fourPackAction d₁ e₁ d₂ e₂ σ))
      (canonicalGridPolynomial a f g d₁ e₁ d₂ e₂) =
      canonicalGridPolynomial a f g d₁ e₁ d₂ e₂ := by
  apply gridPolynomial_stabilized
  all_goals
    funext i
    ext x
    rcases x with (x|x) <;> rcases x with (x|x) <;>
      simp [mapPack,canonicalGridCut,canonicalLeftCut,canonicalRightCut,
        sumPackCut,left,right,embedPackCut,fourPackAction,Finset.mem_map,Equiv.sumCongr]

def fourPackEquiv (d₁ e₁ d₂ e₂ : I → ℕ) :
    (Σi,FourPacks d₁ e₁ d₂ e₂ i) ≃ (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) where
  toFun
    | ⟨i,Sum.inl (Sum.inl x)⟩ => Sum.inl (Sum.inl ⟨i,x⟩)
    | ⟨i,Sum.inl (Sum.inr x)⟩ => Sum.inl (Sum.inr ⟨i,x⟩)
    | ⟨i,Sum.inr (Sum.inl x)⟩ => Sum.inr (Sum.inl ⟨i,x⟩)
    | ⟨i,Sum.inr (Sum.inr x)⟩ => Sum.inr (Sum.inr ⟨i,x⟩)
  invFun
    | Sum.inl (Sum.inl ⟨i,x⟩) => ⟨i,Sum.inl (Sum.inl x)⟩
    | Sum.inl (Sum.inr ⟨i,x⟩) => ⟨i,Sum.inl (Sum.inr x)⟩
    | Sum.inr (Sum.inl ⟨i,x⟩) => ⟨i,Sum.inr (Sum.inl x)⟩
    | Sum.inr (Sum.inr ⟨i,x⟩) => ⟨i,Sum.inr (Sum.inr x)⟩
  left_inv := by rintro ⟨i,((x|x)|(x|x))⟩ <;> rfl
  right_inv := by rintro ((⟨i,x⟩|⟨i,x⟩)|(⟨i,x⟩|⟨i,x⟩)) <;> rfl

noncomputable def fourGridPolynomial (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g : S e) (d₁ e₁ d₂ e₂ : I → ℕ) :=
  rename (fourPackEquiv d₁ e₁ d₂ e₂) (canonicalGridPolynomial a f g d₁ e₁ d₂ e₂)

lemma fourGridPolynomial_invariant (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g : S e) (d₁ e₁ d₂ e₂ : I → ℕ)
    (σ : CellGroup d₁ e₁ × CellGroup d₂ e₂) :
    rename (sumAction (cellAction d₁ e₁) (cellAction d₂ e₂) σ)
      (fourGridPolynomial a f g d₁ e₁ d₂ e₂) = fourGridPolynomial a f g d₁ e₁ d₂ e₂ := by
  have he : (sumAction (cellAction d₁ e₁) (cellAction d₂ e₂) σ) ∘
      fourPackEquiv d₁ e₁ d₂ e₂ = fourPackEquiv d₁ e₁ d₂ e₂ ∘
        packAction (FourPacks d₁ e₁ d₂ e₂) (fourPackAction d₁ e₁ d₂ e₂ σ) := by
    funext z
    rcases z with ⟨i,z⟩
    rcases z with (x|x) <;> rcases x with (x|x) <;> rfl
  unfold fourGridPolynomial
  rw [rename_rename,he,← rename_rename,canonicalGridPolynomial_invariant]

lemma fourGridPolynomial_transfer (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g : S e) (d₁ e₁ d₂ e₂ : I → ℕ) :
    doubleTensorShuffle a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂) =
      localizeTensor (d₁+e₁) (d₂+e₂)
        (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)) :=
  doubleTensorShuffle_invariant a d₁ e₁ d₂ e₂ _
    (fourGridPolynomial_invariant a f g d₁ e₁ d₂ e₂)

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

lemma gridPolynomial_congr (a : I → I → ℕ) {d e : I → ℕ} (f : S d) (g : S e)
    {s t : Pack (A:=A)} (p : PackConvolution.Cut s) (p' : PackConvolution.Cut t)
    (q : PackConvolution.Cut (left p)) (r : PackConvolution.Cut (right p))
    (q' : PackConvolution.Cut (left p')) (r' : PackConvolution.Cut (right p'))
    (hp₁ : left p = left p') (hp₂ : right p = right p')
    (hq₁ : left q = left q') (hq₂ : right q = right q')
    (hr₁ : left r = left r') (hr₂ : right r = right r') :
    gridPolynomial a f g p q r = gridPolynomial a f g p' q' r' := by
  have hc : crossKernelPolynomial a p q r = crossKernelPolynomial a p' q' r' := by
    apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,A i) ℚ))
    rw [← crossKernelPolynomial_spec,← crossKernelPolynomial_spec]
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·)
      (congrArg (algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)))
        (congrArg₂ sameDen hp₁ hp₂))
      (congrArg₂ (kernel (pairKernel a)) hq₁ hr₂))
      (congrArg₂ (kernel (pairKernel a)) hr₁ hq₂)
  simp only [gridPolynomial,hq₁,hq₂,hr₁,hr₂,hc]

noncomputable def gridEmbedding {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) (i : I) :
    FourPacks d₁ e₁ d₂ e₂ i ↪ A i where
  toFun := Sum.elim (fun x=>↑(R i (packSplit u i x))) (fun x=>↑(T i (packSplit v i x)))
  inj' := by
    rintro (x|x) (y|y) h
    · congr 1
      exact (packSplit u i).injective ((R i).injective (Subtype.ext h))
    · change (R i (packSplit u i x)).val = (T i (packSplit v i y)).val at h
      exact (Finset.disjoint_left.mp (p i).property.1
        (R i (packSplit u i x)).property (h.symm ▸ (T i (packSplit v i y)).property)).elim
    · change (T i (packSplit v i x)).val = (R i (packSplit u i y)).val at h
      exact (Finset.disjoint_left.mp (p i).property.1
        (R i (packSplit u i y)).property (h ▸ (T i (packSplit v i x)).property)).elim
    · congr 1
      exact (packSplit v i).injective ((T i).injective (Subtype.ext h))

omit [Fintype I] [DecidableEq I] in
lemma gridEmbedding_outer_left {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    embedPack (gridEmbedding p R T u v) (left (canonicalGridCut d₁ e₁ d₂ e₂)) = left p := by
  funext i
  change Finset.map _ (Finset.univ.map Function.Embedding.inl) = _
  rw [Finset.map_map]
  change Finset.univ.map ((packSplit u i).toEmbedding.trans (PackEnumeration.embedding (R i))) = _
  rw [← Finset.map_map,Finset.map_univ_equiv,PackEnumeration.map_univ]

omit [Fintype I] [DecidableEq I] in
lemma gridEmbedding_outer_right {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    embedPack (gridEmbedding p R T u v) (right (canonicalGridCut d₁ e₁ d₂ e₂)) = right p := by
  funext i
  change Finset.map _ (Finset.univ.map Function.Embedding.inr) = _
  rw [Finset.map_map]
  change Finset.univ.map ((packSplit v i).toEmbedding.trans (PackEnumeration.embedding (T i))) = _
  rw [← Finset.map_map,Finset.map_univ_equiv,PackEnumeration.map_univ]

omit [Fintype I] [DecidableEq I] in
lemma gridEmbedding_cell₁ {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    embedPack (gridEmbedding p R T u v) (left (canonicalLeftCut d₁ e₁ d₂ e₂)) =
      left (cutRealizationEquiv R u).val := by
  funext i
  change Finset.map _ ((Finset.univ.map Function.Embedding.inl).map Function.Embedding.inl) = _
  rw [Finset.map_map,Finset.map_map]
  change Finset.univ.map ((PackEnumeration.embedding (leftEnum u i)).trans
    (PackEnumeration.embedding (R i))) = _
  rw [← Finset.map_map,PackEnumeration.map_univ]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma gridEmbedding_cell₂ {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    embedPack (gridEmbedding p R T u v) (right (canonicalLeftCut d₁ e₁ d₂ e₂)) =
      right (cutRealizationEquiv R u).val := by
  funext i
  change Finset.map _ ((Finset.univ.map Function.Embedding.inr).map Function.Embedding.inl) = _
  rw [Finset.map_map,Finset.map_map]
  change Finset.univ.map ((PackEnumeration.embedding (rightEnum u i)).trans
    (PackEnumeration.embedding (R i))) = _
  rw [← Finset.map_map,PackEnumeration.map_univ]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma gridEmbedding_cell₃ {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    embedPack (gridEmbedding p R T u v) (left (canonicalRightCut d₁ e₁ d₂ e₂)) =
      left (cutRealizationEquiv T v).val := by
  funext i
  change Finset.map _ ((Finset.univ.map Function.Embedding.inl).map Function.Embedding.inr) = _
  rw [Finset.map_map,Finset.map_map]
  change Finset.univ.map ((PackEnumeration.embedding (leftEnum v i)).trans
    (PackEnumeration.embedding (T i))) = _
  rw [← Finset.map_map,PackEnumeration.map_univ]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma gridEmbedding_cell₄ {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    embedPack (gridEmbedding p R T u v) (right (canonicalRightCut d₁ e₁ d₂ e₂)) =
      right (cutRealizationEquiv T v).val := by
  funext i
  change Finset.map _ ((Finset.univ.map Function.Embedding.inr).map Function.Embedding.inr) = _
  rw [Finset.map_map,Finset.map_map]
  change Finset.univ.map ((PackEnumeration.embedding (rightEnum v i)).trans
    (PackEnumeration.embedding (T i))) = _
  rw [← Finset.map_map,PackEnumeration.map_univ]
  rfl

lemma gridPolynomial_realization (a : I → I → ℕ) {d e : I → ℕ} (f : S d) (g : S e)
    {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    rename (packEmbedding (gridEmbedding p R T u v)) (canonicalGridPolynomial a f g d₁ e₁ d₂ e₂) =
      gridPolynomial a f g p (cutRealizationEquiv R u).val (cutRealizationEquiv T v).val := by
  rw [canonicalGridPolynomial,embed_gridPolynomial]
  apply gridPolynomial_congr
  · exact gridEmbedding_outer_left p R T u v
  · exact gridEmbedding_outer_right p R T u v
  · exact gridEmbedding_cell₁ p R T u v
  · exact gridEmbedding_cell₂ p R T u v
  · exact gridEmbedding_cell₃ p R T u v
  · exact gridEmbedding_cell₄ p R T u v

end ElementaryPositivity.RawShuffle

end

end OAI
