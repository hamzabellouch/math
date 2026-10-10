import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.SameDen

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

noncomputable def labeledPolynomial {d : I → ℕ} (f : S d) (s : Pack (A:=A)) :
    MvPolynomial (Σi,A i) ℚ :=
  if h : ∀ i,(s i).card = d i then rename (realizationMap (defaultRealization h)) f.val else 0

omit [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma labeledPolynomial_eq {d : I → ℕ} {s : Pack (A:=A)} (r : Realization d s) (f : S d) :
    labeledPolynomial f s = rename (realizationMap r) f.val := by
  have h : ∀ i,(s i).card = d i := by
    intro i
    simpa using (Fintype.card_congr (r i)).symm
  rw [labeledPolynomial,dite_eq_left h,rename_realization_independent _ r]

omit [DecidableEq I] [∀ i,DecidableEq (A i)] in
@[simp] lemma labeledPolynomial_algebraMap {d : I → ℕ} (f : S d) (s : Pack (A:=A)) :
    algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (labeledPolynomial f s) =
      labeledValue f s := by
  unfold labeledPolynomial labeledValue
  split_ifs <;> simp [valueAt]

def mapPack (σ : ∀ i,Equiv.Perm (A i)) (s : Pack (A:=A)) : Pack (A:=A) :=
  fun i=>(s i).map (σ i).toEmbedding

noncomputable def mapRealization (σ : ∀ i,Equiv.Perm (A i)) {d : I → ℕ}
    {s : Pack (A:=A)} (r : Realization d s) : Realization d (mapPack σ s) :=
  fun i=>(r i).trans (PackEnumeration.mapEquiv (σ i).toEmbedding (s i))

omit [Fintype I] [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma mapRealization_map (σ : ∀ i,Equiv.Perm (A i)) {d : I → ℕ}
    {s : Pack (A:=A)} (r : Realization d s) :
    realizationMap (mapRealization σ r) = packAction A σ ∘ realizationMap r := rfl

omit [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma rename_labeledPolynomial (σ : ∀ i,Equiv.Perm (A i)) {d : I → ℕ}
    (f : S d) (s : Pack (A:=A)) :
    rename (packAction A σ) (labeledPolynomial f s) = labeledPolynomial f (mapPack σ s) := by
  by_cases h : ∀ i,(s i).card = d i
  · rw [labeledPolynomial_eq (defaultRealization h),
      labeledPolynomial_eq (mapRealization σ (defaultRealization h)),mapRealization_map,rename_rename]
  · have hm : ¬ ∀ i,(mapPack σ s i).card = d i := by simpa [mapPack] using h
    simp only [labeledPolynomial,dite_eq_right h,dite_eq_right hm,map_zero]

omit [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma rename_sameDen (σ : ∀ i,Equiv.Perm (A i)) (s t : Pack (A:=A)) :
    rename (packAction A σ) (sameDen s t) = sameDen (mapPack σ s) (mapPack σ t) := by
  simp only [sameDen,mapPack,map_prod,Finset.prod_map,diagonal,map_sub,rename_X]
  rfl

omit [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma rename_arrowNum (σ : ∀ i,Equiv.Perm (A i)) (a : I → I → ℕ) (s t : Pack (A:=A)) :
    rename (packAction A σ) (arrowNum a s t) = arrowNum a (mapPack σ s) (mapPack σ t) := by
  simp only [arrowNum,mapPack,map_prod,map_pow,Finset.prod_map,diagonal,map_sub,rename_X]
  rfl

omit [∀ i,DecidableEq (A i)] in
lemma rename_pack_kernel (σ : ∀ i,Equiv.Perm (A i)) (a : I → I → ℕ) (s t : Pack (A:=A)) :
    renameFraction (packAction A σ) (kernel (pairKernel a) s t) =
      kernel (pairKernel a) (mapPack σ s) (mapPack σ t) := by
  rw [kernel_polynomial_ratio,kernel_polynomial_ratio,map_div₀,
    renameFraction_algebraMap,renameFraction_algebraMap,rename_sameDen,rename_arrowNum]

noncomputable def mapPackCut (σ : ∀ i,Equiv.Perm (A i)) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) : PackConvolution.Cut (mapPack σ s) := fun i=>
  ⟨((left p i).map (σ i).toEmbedding,(right p i).map (σ i).toEmbedding),
    (Finset.disjoint_map _).mpr (p i).property.1,by
      rw [← Finset.map_union]
      change Finset.map (σ i).toEmbedding ((p i).val.1 ∪ (p i).val.2) = _
      rw [(p i).property.2]
      rfl⟩

omit [Fintype I] [DecidableEq I] in
@[simp] lemma mapPackCut_left (σ : ∀ i,Equiv.Perm (A i)) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) : left (mapPackCut σ p) = mapPack σ (left p) := rfl
omit [Fintype I] [DecidableEq I] in
@[simp] lemma mapPackCut_right (σ : ∀ i,Equiv.Perm (A i)) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) : right (mapPackCut σ p) = mapPack σ (right p) := rfl

lemma rename_crossKernelPolynomial (σ : ∀ i,Equiv.Perm (A i)) (a : I → I → ℕ)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (q : PackConvolution.Cut (left p)) (r : PackConvolution.Cut (right p)) :
    rename (packAction A σ) (crossKernelPolynomial a p q r) =
      crossKernelPolynomial a (mapPackCut σ p) (mapPackCut σ q) (mapPackCut σ r) := by
  apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,A i) ℚ))
  rw [← renameFraction_algebraMap (packAction A σ),← crossKernelPolynomial_spec,
    map_mul,map_mul,renameFraction_algebraMap,rename_sameDen,
    rename_pack_kernel,rename_pack_kernel]
  exact crossKernelPolynomial_spec a (mapPackCut σ p) (mapPackCut σ q) (mapPackCut σ r)

noncomputable def gridPolynomial (a : I → I → ℕ) {d e : I → ℕ} (f : S d) (g : S e)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (q : PackConvolution.Cut (left p)) (r : PackConvolution.Cut (right p)) :
    MvPolynomial (Σi,A i) ℚ :=
  labeledPolynomial f (fun i=>left q i ∪ left r i) *
    labeledPolynomial g (fun i=>right q i ∪ right r i) * crossKernelPolynomial a p q r

omit [Fintype I] [DecidableEq I] in
lemma mapPack_union (σ : ∀ i,Equiv.Perm (A i)) (s t : Pack (A:=A)) :
    mapPack σ (fun i=>s i ∪ t i) = fun i=>mapPack σ s i ∪ mapPack σ t i := by
  funext i
  exact Finset.map_union _ _

lemma rename_gridPolynomial (σ : ∀ i,Equiv.Perm (A i)) (a : I → I → ℕ)
    {d e : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (q : PackConvolution.Cut (left p)) (r : PackConvolution.Cut (right p)) :
    rename (packAction A σ) (gridPolynomial a f g p q r) =
      gridPolynomial a f g (mapPackCut σ p) (mapPackCut σ q) (mapPackCut σ r) := by
  simp only [gridPolynomial,map_mul,rename_labeledPolynomial,rename_crossKernelPolynomial,
    mapPack_union,mapPackCut_left,mapPackCut_right]

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A B : I → Type*} [∀ i,DecidableEq (A i)] [∀ i,DecidableEq (B i)]

def packEmbedding (φ : ∀ i,A i ↪ B i) : (Σi,A i) ↪ (Σi,B i) :=
  Function.Embedding.sigmaMap (Function.Embedding.refl I) φ

def embedPack (φ : ∀ i,A i ↪ B i) (s : Pack (A:=A)) : Pack (A:=B) :=
  fun i=>(s i).map (φ i)

noncomputable def embedRealization (φ : ∀ i,A i ↪ B i) {d : I → ℕ}
    {s : Pack (A:=A)} (r : Realization d s) : Realization d (embedPack φ s) :=
  fun i=>(r i).trans (PackEnumeration.mapEquiv (φ i) (s i))

omit [Fintype I] [DecidableEq I] [∀ i,DecidableEq (A i)] [∀ i,DecidableEq (B i)] in
lemma embedRealization_map (φ : ∀ i,A i ↪ B i) {d : I → ℕ}
    {s : Pack (A:=A)} (r : Realization d s) :
    realizationMap (embedRealization φ r) = packEmbedding φ ∘ realizationMap r := rfl

omit [DecidableEq I] [∀ i,DecidableEq (A i)] [∀ i,DecidableEq (B i)] in
lemma embed_labeledPolynomial (φ : ∀ i,A i ↪ B i) {d : I → ℕ}
    (f : S d) (s : Pack (A:=A)) :
    rename (packEmbedding φ) (labeledPolynomial f s) = labeledPolynomial f (embedPack φ s) := by
  by_cases h : ∀ i,(s i).card = d i
  · rw [labeledPolynomial_eq (defaultRealization h),
      labeledPolynomial_eq (embedRealization φ (defaultRealization h)),embedRealization_map,rename_rename]
  · have hm : ¬ ∀ i,(embedPack φ s i).card = d i := by simpa [embedPack] using h
    simp only [labeledPolynomial,dite_eq_right h,dite_eq_right hm,map_zero]

omit [DecidableEq I] [∀ i,DecidableEq (A i)] [∀ i,DecidableEq (B i)] in
lemma embed_sameDen (φ : ∀ i,A i ↪ B i) (s t : Pack (A:=A)) :
    rename (packEmbedding φ) (sameDen s t) = sameDen (embedPack φ s) (embedPack φ t) := by
  simp only [sameDen,embedPack,map_prod,Finset.prod_map,diagonal,map_sub,rename_X]
  rfl

omit [DecidableEq I] [∀ i,DecidableEq (A i)] [∀ i,DecidableEq (B i)] in
lemma embed_arrowNum (φ : ∀ i,A i ↪ B i) (a : I → I → ℕ) (s t : Pack (A:=A)) :
    rename (packEmbedding φ) (arrowNum a s t) = arrowNum a (embedPack φ s) (embedPack φ t) := by
  simp only [arrowNum,embedPack,map_prod,map_pow,Finset.prod_map,diagonal,map_sub,rename_X]
  rfl

omit [∀ i,DecidableEq (A i)] [∀ i,DecidableEq (B i)] in
lemma embed_pack_kernel (φ : ∀ i,A i ↪ B i) (a : I → I → ℕ) (s t : Pack (A:=A)) :
    renameInjFraction (packEmbedding φ) (packEmbedding φ).injective (kernel (pairKernel a) s t) =
      kernel (pairKernel a) (embedPack φ s) (embedPack φ t) := by
  rw [kernel_polynomial_ratio,kernel_polynomial_ratio,map_div₀,
    renameInjFraction_algebraMap,renameInjFraction_algebraMap,embed_sameDen,embed_arrowNum]

noncomputable def embedPackCut (φ : ∀ i,A i ↪ B i) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) : PackConvolution.Cut (embedPack φ s) := fun i=>
  ⟨((left p i).map (φ i),(right p i).map (φ i)),
    (Finset.disjoint_map _).mpr (p i).property.1,by
      rw [← Finset.map_union]
      change Finset.map (φ i) ((p i).val.1 ∪ (p i).val.2) = _
      rw [(p i).property.2]
      rfl⟩

omit [Fintype I] [DecidableEq I] in
@[simp] lemma embedPackCut_left (φ : ∀ i,A i ↪ B i) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) : left (embedPackCut φ p) = embedPack φ (left p) := rfl
omit [Fintype I] [DecidableEq I] in
@[simp] lemma embedPackCut_right (φ : ∀ i,A i ↪ B i) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) : right (embedPackCut φ p) = embedPack φ (right p) := rfl

lemma embed_crossKernelPolynomial (φ : ∀ i,A i ↪ B i) (a : I → I → ℕ)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (q : PackConvolution.Cut (left p)) (r : PackConvolution.Cut (right p)) :
    rename (packEmbedding φ) (crossKernelPolynomial a p q r) =
      crossKernelPolynomial a (embedPackCut φ p) (embedPackCut φ q) (embedPackCut φ r) := by
  apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,B i) ℚ))
  rw [← renameInjFraction_algebraMap (packEmbedding φ) (packEmbedding φ).injective,← crossKernelPolynomial_spec,
    map_mul,map_mul,renameInjFraction_algebraMap,embed_sameDen,
    embed_pack_kernel,embed_pack_kernel]
  exact crossKernelPolynomial_spec a (embedPackCut φ p) (embedPackCut φ q) (embedPackCut φ r)

omit [Fintype I] [DecidableEq I] in
lemma embedPack_union (φ : ∀ i,A i ↪ B i) (s t : Pack (A:=A)) :
    embedPack φ (fun i=>s i ∪ t i) = fun i=>embedPack φ s i ∪ embedPack φ t i := by
  funext i
  exact Finset.map_union _ _

lemma embed_gridPolynomial (φ : ∀ i,A i ↪ B i) (a : I → I → ℕ)
    {d e : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (q : PackConvolution.Cut (left p)) (r : PackConvolution.Cut (right p)) :
    rename (packEmbedding φ) (gridPolynomial a f g p q r) =
      gridPolynomial a f g (embedPackCut φ p) (embedPackCut φ q) (embedPackCut φ r) := by
  simp only [gridPolynomial,map_mul,embed_labeledPolynomial,embed_crossKernelPolynomial,
    embedPack_union,embedPackCut_left,embedPackCut_right]

end ElementaryPositivity.RawShuffle

end

end OAI
