import Mathlib
import OAI.GroupTheory.FiniteType.BasedHorn
import OAI.GroupTheory.FiniteType.SimplexSign

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval
namespace BoundaryValue
section
open Set Topology SimplexBoundary SimplexAddition SimplexVertexMaps
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

abbrev A (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X) :=
  Additive (HomotopyGroup.Pi (n+2) X x)

def value (f : BasedSimplex.Space (n+2) X x) : A n X x :=
  Additive.ofMul (DuffyBased.homotopyClass f)

def boundary (F : C(Simplex (n+3),X))
    (h₂ : ∀ s ∈ DuffyTriangle.DoubleBoundary (n+3), F s = x) : A n X x :=
  ∑ i : Fin (n+4), (-1:ℤ)^i.val • value (basedFace F h₂ i)

lemma value_permute (f : BasedSimplex.Space (n+2) X x) (p : Equiv.Perm (Fin (n+3))) :
    value (RotationClass.permute f p) = ((Equiv.Perm.sign p : ℤˣ) : ℤ) • value f :=
  congrArg Additive.ofMul (SimplexSign.class_sign f p)

lemma boundary_permutation (F : C(Simplex (n+3),X))
    (h₂ : ∀ s ∈ DuffyTriangle.DoubleBoundary (n+3), F s = x)
    (p : Equiv.Perm (Fin (n+4))) :
    boundary (F.comp (vertexMap p))
      (fun s hs => h₂ _ (vertexMap_perm_doubleBoundary p s hs)) =
    ((Equiv.Perm.sign p : ℤˣ) : ℤ) • boundary F h₂ := by
  have hf (i : Fin (n+4)) :
      basedFace (F.comp (vertexMap p))
        (fun s hs => h₂ _ (vertexMap_perm_doubleBoundary p s hs)) i =
      RotationClass.permute (basedFace F h₂ (p i)) (FacePermutation.restrict p i).symm := by
    apply Subtype.ext
    change (F.comp (vertexMap p)).comp (face i) = _
    rw [ContinuousMap.comp_assoc,vertexMap_face,← ContinuousMap.comp_assoc,vertexMap_perm]
    rfl
  have hs (i : Fin (n+4)) :
      (-1:ℤ)^i.val * ((Equiv.Perm.sign (FacePermutation.restrict p i) : ℤˣ) : ℤ) =
        ((Equiv.Perm.sign p : ℤˣ) : ℤ) * (-1:ℤ)^(p i).val := by
    exact congrArg (fun z : ℤˣ => (z:ℤ)) (FacePermutation.sign_restrict p i)
  simp only [boundary,hf,value_permute,Equiv.Perm.sign_symm]
  simp_rw [← mul_zsmul,hs,mul_zsmul]
  rw [← Finset.smul_sum]
  exact congrArg (fun z : A n X x => ((Equiv.Perm.sign p : ℤˣ) : ℤ) • z)
    (Equiv.sum_comp p (fun i => (-1:ℤ)^i.val • value (basedFace F h₂ i)))

end

open Set Topology SimplexBoundary SimplexAddition SimplexVertexMaps DuffyTriangle
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

@[simp] lemma value_const : value (BasedSimplex.const (n+2) x) = 0 := by
  rfl

lemma boundary_three (F : C(Simplex (n+3),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x)
    (he : ∀ i : Fin (n+4), i.val < n+1 → F.comp (face i) = ContinuousMap.const _ x) :
    boundary F h₂ = 0 := by
  unfold boundary
  rw [HurewiczAddition.alternating_three (n+1) _ (by
    intro i hi
    have hf : basedFace F h₂ i = BasedSimplex.const (n+2) x := Subtype.ext (he i hi)
    rw [hf,value_const])]
  have h := congrArg Additive.ofMul (SimplexAddition.three_face F h₂ he)
  change value (basedFace F h₂ (lastFace (n+1) 1)) =
    value (basedFace F h₂ (lastFace (n+1) 2)) + value (basedFace F h₂ (lastFace (n+1) 0)) at h
  rw [h]
  have hz : value (basedFace F h₂ (lastFace (n+1) 0)) -
      (value (basedFace F h₂ (lastFace (n+1) 2)) + value (basedFace F h₂ (lastFace (n+1) 0))) +
      value (basedFace F h₂ (lastFace (n+1) 2)) = 0 := by abel
  rw [hz,smul_zero]

lemma boundary_three_at (F : C(Simplex (n+3),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x) (a : Fin (n+4)) (ha : a.val < n+2)
    (he : ∀ i : Fin (n+4), i ≠ a → i ≠ lastFace (n+1) 1 → i ≠ lastFace (n+1) 2 →
      F.comp (face i) = ContinuousMap.const _ x) : boundary F h₂ = 0 := by
  let p := Equiv.swap a (lastFace (n+1) 0)
  have hp : p (lastFace (n+1) 0) = a := Equiv.swap_apply_right _ _
  have hpfix (j : Fin 3) (hj : 1 ≤ j.val) : p (lastFace (n+1) j) = lastFace (n+1) j := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      have hv := congrArg Fin.val h
      simp only [lastFace_val] at hv
      omega
    · exact fun h => (by have := BasedHorn.lastFace_injective (n+1) h; subst j; simp at hj)
  have hz := boundary_three (F.comp (vertexMap p))
    (fun s hs => h₂ _ (vertexMap_perm_doubleBoundary p s hs)) (by
      intro i hi
      have hineq (j : Fin 3) : i ≠ lastFace (n+1) j := by
        intro h
        have hv := congrArg Fin.val h
        simp only [lastFace_val] at hv
        omega
      have hia : p i ≠ a := by rw [← hp]; exact p.injective.ne (hineq 0)
      have hi1 : p i ≠ lastFace (n+1) 1 := by
        rw [← hpfix 1 (by decide)]
        exact p.injective.ne (hineq 1)
      have hi2 : p i ≠ lastFace (n+1) 2 := by
        rw [← hpfix 2 (by decide)]
        exact p.injective.ne (hineq 2)
      rw [ContinuousMap.comp_assoc,vertexMap_face,← ContinuousMap.comp_assoc,he (p i) hia hi1 hi2]
      rfl)
  rw [boundary_permutation] at hz
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> simpa [h] using hz

end BoundaryValue

namespace SimplexDegeneracy
open Set Topology SimplexBoundary SimplexVertexMaps
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

def append (v : Fin (n+1)) : Fin (n+2) → Fin (n+1) := Fin.lastCases v id

@[simp] lemma append_castSucc (v j : Fin (n+1)) : append v j.castSucc = j := by
  simp [append]
@[simp] lemma append_last (v : Fin (n+1)) : append v (Fin.last (n+1)) = v := by
  simp [append]

lemma append_eq (v i : Fin (n+1)) (hiv : i ≠ v) (j : Fin (n+2))
    (h : append v j = i) : j = i.castSucc := by
  induction j using Fin.lastCases with
  | last => exact (hiv (by simpa using h.symm)).elim
  | cast j => simpa only [append_castSucc,Fin.castSucc_inj] using h

lemma append_face_last (v : Fin (n+1)) : append v ∘ (Fin.last (n+1)).succAbove = id := by
  funext i
  simp

lemma append_face_last_castSucc :
    append (Fin.last n) ∘ (Fin.last n).castSucc.succAbove = (id : Fin (n+1) → Fin (n+1)) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [Fin.succAbove]
  | cast i =>
    have hi : i.castSucc.castSucc < (Fin.last n).castSucc := by
      simpa only [Fin.lt_def,Fin.val_castSucc,Fin.val_last] using i.isLt
    rw [Function.comp_apply,Fin.succAbove_of_castSucc_lt _ _ hi,append_castSucc]
    rfl

lemma append_face_penult {n : ℕ} :
    append (Fin.last n).castSucc ∘ (Fin.last n).castSucc.castSucc.succAbove =
      (SimplexSign.lastSwap n : Fin (n+2) → Fin (n+2)) := by
  funext i
  induction i using Fin.lastCases with
  | last =>
    rw [Function.comp_apply,Fin.succAbove_of_le_castSucc _ _ (by
      simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_last]; omega),Fin.succ_last,append_last]
    exact (Equiv.swap_apply_right _ _).symm
  | cast i =>
    induction i using Fin.lastCases with
    | last =>
      rw [Function.comp_apply,Fin.succAbove_of_le_castSucc _ _ le_rfl]
      have he : (Fin.last n).castSucc.succ = (Fin.last (n+1)).castSucc := Fin.ext rfl
      rw [he,append_castSucc]
      exact (Equiv.swap_apply_left _ _).symm
    | cast i =>
      have hi : i.castSucc.castSucc.castSucc < (Fin.last n).castSucc.castSucc := by
        simpa only [Fin.lt_def,Fin.val_castSucc,Fin.val_last] using i.isLt
      rw [Function.comp_apply,Fin.succAbove_of_castSucc_lt _ _ hi,append_castSucc]
      simp only [SimplexSign.lastSwap]
      exact (Equiv.swap_apply_of_ne_of_ne (by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castSucc] at hv
        omega) (Fin.castSucc_ne_last _)).symm

def degenerate (f : BasedSimplex.Space n X x) (v : Fin (n+1)) : C(Simplex (n+1),X) :=
  f.1.comp (vertexMap (append v))

lemma degenerate_face_last (f : BasedSimplex.Space n X x) (v : Fin (n+1)) :
    (degenerate f v).comp (face (Fin.last (n+1))) = f.1 := by
  change (f.1.comp (vertexMap (append v))).comp (vertexMap (Fin.last (n+1)).succAbove) = _
  rw [ContinuousMap.comp_assoc,vertexMap_comp,append_face_last,vertexMap_id,ContinuousMap.comp_id]

lemma degenerate_face_const (f : BasedSimplex.Space n X x) (v i : Fin (n+1)) (hiv : i ≠ v) :
    (degenerate f v).comp (face i.castSucc) = ContinuousMap.const _ x := by
  change (f.1.comp (vertexMap (append v))).comp (vertexMap i.castSucc.succAbove) = _
  rw [ContinuousMap.comp_assoc,vertexMap_comp]
  apply ContinuousMap.ext
  intro s
  apply f.2
  refine ⟨i,vertexMap_zero_of_notMem_range _ i ?_ s⟩
  rintro ⟨j,hj⟩
  exact Fin.succAbove_ne i.castSucc j (append_eq v i hiv _ hj)

lemma degenerate_standard_face (f : BasedSimplex.Space n X x) :
    (degenerate f (Fin.last n)).comp (face (Fin.last n).castSucc) = f.1 := by
  change (f.1.comp (vertexMap (append (Fin.last n)))).comp (vertexMap (Fin.last n).castSucc.succAbove) = _
  rw [ContinuousMap.comp_assoc,vertexMap_comp,append_face_last_castSucc,vertexMap_id,ContinuousMap.comp_id]

lemma degenerate_twisted_face (f : BasedSimplex.Space (n+1) X x) :
    (degenerate f (Fin.last n).castSucc).comp (face (Fin.last n).castSucc.castSucc) =
      (RotationClass.permute f (SimplexSign.lastSwap n)).1 := by
  change (f.1.comp (vertexMap (append (Fin.last n).castSucc))).comp
    (vertexMap (Fin.last n).castSucc.castSucc.succAbove) = _
  rw [ContinuousMap.comp_assoc,vertexMap_comp,append_face_penult,vertexMap_perm]
  rfl

end SimplexDegeneracy

namespace SimplexHorn
open Set Topology SimplexBoundary
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

lemma compatible_of_ordered (hole : Fin (n+3)) (f : Fin (n+3) → C(Simplex (n+1),X))
    (hc : ∀ (i j : Fin (n+2)), i ≤ j → i.castSucc ≠ hole → j.succ ≠ hole →
      (f i.castSucc).comp (face j) = (f j.succ).comp (face i)) :
    ∀ (i j : Faces hole) (a b : Simplex (n+1)), face i.1 a = face j.1 b → f i.1 a = f j.1 b := by
  have aux (i j : Faces hole) (hij : i.1 < j.1) (a b : Simplex (n+1))
      (hab : face i.1 a = face j.1 b) : f i.1 a = f j.1 b := by
    obtain ⟨l,s,hj,rfl,rfl⟩ := face_overlap hij.ne hab
    have hiLast : i.1 ≠ Fin.last (n+2) := ne_of_lt (lt_of_lt_of_le hij (Fin.le_last _))
    let k : Fin (n+2) := i.1.castPred hiLast
    have hk : k.castSucc = i.1 := Fin.castSucc_castPred i.1 hiLast
    have hle : i.1 ≤ l.castSucc := by
      by_contra! h
      rw [Fin.succAbove_of_castSucc_lt _ _ h] at hj
      exact (not_lt_of_ge (le_of_lt h)) (hj ▸ hij)
    have hkl : k ≤ l := by
      rw [← hk] at hle
      exact Fin.castSucc_le_castSucc_iff.mp hle
    rw [Fin.succAbove_of_le_castSucc _ _ hle] at hj
    have hp : l.predAbove i.1 = k := by rw [← hk,Fin.predAbove_castSucc_of_le _ _ hkl]
    rw [hp,← hk, hj]
    exact DFunLike.congr_fun (hc k l hkl (hk ▸ i.2) (hj ▸ j.2)) s
  intro i j a b hab
  rcases lt_trichotomy i.1 j.1 with h | h | h
  · exact aux i j h a b hab
  · have hij : i = j := Subtype.ext h
    subst j
    exact congrArg (f i.1) (face_injective i.1 hab)
  · exact (aux j i h b a hab.symm).symm

end SimplexHorn

end

end OAI
