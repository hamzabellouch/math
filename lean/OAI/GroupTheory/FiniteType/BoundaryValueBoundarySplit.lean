import Mathlib
import OAI.GroupTheory.FiniteType.HornElimination

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
open Set Topology SimplexBoundary SimplexAddition SimplexVertexMaps DuffyTriangle
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

lemma boundary_split (F : C(Simplex (n+3),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x) :
    boundary F h₂ =
      (∑ i : Fin (n+2), (-1:ℤ)^i.val • value (basedFace F h₂ i.castSucc.castSucc)) +
      (-1:ℤ)^(n+2) • value (basedFace F h₂ (Fin.last (n+2)).castSucc) +
      (-1:ℤ)^(n+3) • value (basedFace F h₂ (Fin.last (n+3))) := by
  rw [boundary,Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  rfl

lemma pivot_boundary_zero (F : C(Simplex (n+3),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x) (a : Fin (n+2)) :
    boundary (HornElimination.pivot F h₂ a) (HornElimination.pivot_double F h₂ a) = 0 := by
  apply boundary_three_at _ _ a.castSucc.castSucc (by simpa only [Fin.val_castSucc] using a.isLt)
  intro i hi h1 h2
  induction i using Fin.lastCases with
  | last => exact (h2 (Fin.ext (by simp [lastFace_val]))).elim
  | cast i =>
    induction i using Fin.lastCases with
    | last => exact (h1 (Fin.ext (by simp [lastFace_val]))).elim
    | cast i =>
      have hia : i ≠ a := fun h => hi (h ▸ rfl)
      rw [HornElimination.pivot_early,ite_eq_right hia]

lemma replacement_boundary (F : C(Simplex (n+3),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x) (a : Fin (n+2)) :
    boundary (HornElimination.replacement F h₂ a) (HornElimination.replacement_double F h₂ a) =
      boundary F h₂ := by
  let P := HornElimination.pivot F h₂ a
  let hP := HornElimination.pivot_double F h₂ a
  let R := HornElimination.replacement F h₂ a
  let hR := HornElimination.replacement_double F h₂ a
  have he (i : Fin (n+2)) :
      value (basedFace R hR i.castSucc.castSucc) - value (basedFace F h₂ i.castSucc.castSucc) =
        value (basedFace P hP i.castSucc.castSucc) := by
    have hf := HornElimination.new_basedFace F h₂ a i.castSucc.castSucc
    have hp : basedFace P hP i.castSucc.castSucc =
        if i = a then RotationClass.permute (HornElimination.earlyFace F h₂ i) (SimplexSign.lastSwap (n+1))
        else BasedSimplex.const _ x := by
      by_cases hia : i = a
      · rw [ite_eq_left hia]
        apply Subtype.ext
        simpa only [P,basedFace,ite_eq_left hia] using HornElimination.pivot_early F h₂ a i
      · rw [ite_eq_right hia]
        apply Subtype.ext
        simpa only [P,basedFace,BasedSimplex.const,ite_eq_right hia] using HornElimination.pivot_early F h₂ a i
    dsimp only [HornElimination.newFaces] at hf
    simp only [Fin.lastCases_castSucc] at hf
    change basedFace R hR _ = _ at hf
    rw [hf,hp]
    by_cases hia : i = a
    · simp only [ite_eq_left hia,value_const,zero_sub,value_permute]
      have hsign : Equiv.Perm.sign (SimplexSign.lastSwap (n+1)) = -1 := by
        exact Equiv.Perm.sign_swap (by
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_last] at hv
          omega)
      rw [hsign]
      simp only [Units.val_neg,Units.val_one,neg_one_zsmul]

    · simp only [ite_eq_right hia, HornElimination.earlyFace,sub_self,value_const]
  have hs :
      (∑ i : Fin (n+2), (-1:ℤ)^i.val • value (basedFace R hR i.castSucc.castSucc)) -
      (∑ i : Fin (n+2), (-1:ℤ)^i.val • value (basedFace F h₂ i.castSucc.castSucc)) =
      (∑ i : Fin (n+2), (-1:ℤ)^i.val • value (basedFace P hP i.castSucc.castSucc)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [← smul_sub,he])
  have hrp : basedFace R hR (Fin.last (n+2)).castSucc = basedFace P hP (Fin.last (n+2)).castSucc :=
    Subtype.ext (HornElimination.replacement_pivot F h₂ a)
  have hrl : basedFace R hR (Fin.last (n+3)) = basedFace F h₂ (Fin.last (n+3)) :=
    Subtype.ext (HornElimination.replacement_last F h₂ a)
  have hpl : basedFace P hP (Fin.last (n+3)) = basedFace F h₂ (Fin.last (n+2)).castSucc :=
    Subtype.ext (HornElimination.pivot_last F h₂ a)
  have hz := pivot_boundary_zero F h₂ a
  change boundary P hP = 0 at hz
  rw [boundary_split,hpl] at hz
  change boundary R hR = boundary F h₂
  rw [boundary_split,boundary_split,hrp,hrl]
  have hpow : (-1:ℤ)^(n+3) = -((-1:ℤ)^(n+2)) := by rw [pow_succ]; ring
  rw [hpow,neg_smul] at hz
  rw [← hs] at hz
  apply sub_eq_zero.mp
  convert hz using 1; abel

theorem boundary_zero (F : C(Simplex (n+3),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x) : boundary F h₂ = 0 := by
  have aux : ∀ m k : ℕ, k+m = n+1 → ∀ (F : C(Simplex (n+3),X))
      (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x),
      (∀ i : Fin (n+4), i.val < k → F.comp (face i) = ContinuousMap.const _ x) → boundary F h₂ = 0 := by
    intro m
    induction m with
    | zero =>
      intro k hk F h₂ he
      have hk' : k = n+1 := by omega
      subst k
      exact boundary_three F h₂ he
    | succ m ih =>
      intro k hk F h₂ he
      let a : Fin (n+2) := ⟨k,by omega⟩
      let R := HornElimination.replacement F h₂ a
      let hR := HornElimination.replacement_double F h₂ a
      rw [← replacement_boundary F h₂ a]
      apply ih (k+1) (by omega) R hR
      intro i hi
      have hib : i.val < n+2 := by omega
      let j : Fin (n+2) := ⟨i.val,hib⟩
      have hij : j.castSucc.castSucc = i := Fin.ext rfl
      rw [← hij]
      change (HornElimination.replacement F h₂ a).comp (face j.castSucc.castSucc) = _
      rw [HornElimination.replacement_early]
      split_ifs with hja
      · rfl
      · apply he
        have hv : j.val ≠ k := by
          intro hjv
          exact hja (Fin.ext hjv)
        change i.val < k
        change i.val ≠ k at hv
        omega
  exact aux (n+1) 0 (by omega) F h₂ (fun i hi => (Nat.not_lt_zero _ hi).elim)

end BoundaryValue

namespace FixedSingularTightening
attribute [local instance] Classical.propDecidable
open Set Topology Metric
open scoped unitInterval
open SimplexBoundary
universe u
variable {Y : Type u} [TopologicalSpace Y]

structure System (k m : ℕ) (y₀ : Y) where
  hom : ∀ p, p ≤ m → C(Simplex p,Y) → C(I × Simplex p,Y)
  zero : ∀ p hp f s, hom p hp f (0,s) = f s
  face : ∀ p (hp : p+1 ≤ m) (f : C(Simplex (p+1),Y)) (i : Fin (p+2)) t s,
    hom (p+1) hp f (t,SimplexBoundary.face i s) =
      hom p (Nat.le_trans (Nat.le_succ p) hp) (f.comp (SimplexBoundary.face i)) (t,s)
  top : ∀ p hp, p < k → ∀ f s, hom p hp f (1,s) = y₀
  fixed : ∀ p hp, hom p hp (ContinuousMap.const _ y₀) = ContinuousMap.const _ y₀

variable {k m : ℕ} {y₀ : Y}

def topMap (S : System k m y₀) (p : ℕ) (hp : p ≤ m) (f : C(Simplex p,Y)) :
    C(Simplex p,Y) := (S.hom p hp f).comp ⟨fun s => (1,s),continuous_const.prodMk continuous_id⟩

lemma boundary_compatible (S : System k m y₀) (f : C(Simplex (m+1),Y)) :
    ∀ t i j a b, SimplexBoundary.face i a = SimplexBoundary.face j b →
      S.hom m le_rfl (f.comp (SimplexBoundary.face i)) (t,a) =
        S.hom m le_rfl (f.comp (SimplexBoundary.face j)) (t,b) := by
  intro t
  apply compatible_faces
  intro p hp i j s
  subst m
  change S.hom (p+1) _ _ (t,SimplexBoundary.face (j.predAbove i) s) =
    S.hom (p+1) _ _ (t,SimplexBoundary.face j s)
  rw [S.face p,S.face p]
  congr 2
  apply ContinuousMap.ext
  intro a
  exact congrArg f (face_face i j a)

def boundaryHom (S : System k m y₀) (f : C(Simplex (m+1),Y)) :
    C(I × Boundary (m+1),Y) :=
  glueHomotopies (fun i => S.hom m le_rfl (f.comp (SimplexBoundary.face i)))
    (boundary_compatible S f)

lemma boundaryHom_zero (S : System k m y₀) (f : C(Simplex (m+1),Y)) (b : Boundary (m+1)) :
    boundaryHom S f (0,b) = f b.1 := by
  obtain ⟨⟨i,s⟩,rfl⟩ := faceQuot_surjective m b
  rw [boundaryHom,glueHomotopies_face,S.zero]
  rfl

lemma boundaryHom_one (S : System k m y₀) (hmk : m < k) (f : C(Simplex (m+1),Y))
    (b : Boundary (m+1)) : boundaryHom S f (1,b) = y₀ := by
  obtain ⟨⟨i,s⟩,rfl⟩ := faceQuot_surjective m b
  rw [boundaryHom,glueHomotopies_face,S.top m le_rfl hmk]

theorem exists_next (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (f : C(Simplex (m+1),Y)) :
    ∃ F : C(I × Simplex (m+1),Y), (∀ s, F (0,s) = f s) ∧
      (∀ t b, F (t,b.1) = boundaryHom S f (t,b)) ∧
      (m+1 < k → ∀ s, F (1,s) = y₀) := by
  by_cases hmk : m+1 < k
  · obtain ⟨F,h₀,h₁,hb⟩ := SimplexHomotopy.exists_prescribed (hπ _ hmk) f
      (ContinuousMap.const _ y₀) (boundaryHom S f) (boundaryHom_zero S f)
      (boundaryHom_one S (Nat.lt_of_le_of_lt (Nat.le_succ m) hmk) f)
    exact ⟨F,h₀,hb,fun _ => h₁⟩
  · obtain ⟨F,h₀,hb⟩ := SimplexHomotopy.exists_extension f (boundaryHom S f) (boundaryHom_zero S f)
    exact ⟨F,h₀,hb,fun h => (hmk h).elim⟩

def next (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (f : C(Simplex (m+1),Y)) : C(I × Simplex (m+1),Y) :=
  if f = ContinuousMap.const _ y₀ then ContinuousMap.const _ y₀ else (exists_next hπ S f).choose

lemma next_zero (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (f : C(Simplex (m+1),Y)) (s : Simplex (m+1)) :
    next hπ S f (0,s) = f s := by
  by_cases hf : f = ContinuousMap.const _ y₀
  · simp [next,hf]
  · simpa only [next,ite_eq_right hf] using (exists_next hπ S f).choose_spec.1 s

lemma next_face (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (f : C(Simplex (m+1),Y)) (i : Fin (m+2)) t s :
    next hπ S f (t,SimplexBoundary.face i s) =
      S.hom m le_rfl (f.comp (SimplexBoundary.face i)) (t,s) := by
  by_cases hf : f = ContinuousMap.const _ y₀
  · subst f
    simpa only [next,ite_true,ContinuousMap.const_comp,ContinuousMap.const_apply] using
      (congrArg (fun a : C(I × Simplex m,Y) => a (t,s)) (S.fixed m le_rfl)).symm
  have h := (exists_next hπ S f).choose_spec.2.1 t (faceQuot m (i,s))
  rw [show next hπ S f = (exists_next hπ S f).choose by simp only [next,ite_eq_right hf]]
  change (exists_next hπ S f).choose (t,SimplexBoundary.face i s) = boundaryHom S f (t,faceQuot m (i,s)) at h
  rw [show boundaryHom S f (t,faceQuot m (i,s)) = S.hom m le_rfl (f.comp (SimplexBoundary.face i)) (t,s) from glueHomotopies_face _ _ _ _ _] at h
  exact h

lemma next_top (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (h : m+1 < k) (f : C(Simplex (m+1),Y)) s :
    next hπ S f (1,s) = y₀ := by
  by_cases hf : f = ContinuousMap.const _ y₀
  · simp [next,hf]
  · simpa only [next,ite_eq_right hf] using (exists_next hπ S f).choose_spec.2.2 h s

lemma next_fixed (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) : next hπ S (ContinuousMap.const _ y₀) = ContinuousMap.const _ y₀ := by
  simp [next]

def extendHom (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (p : ℕ) (hp : p ≤ m+1) : C(Simplex p,Y) → C(I × Simplex p,Y) := by
  by_cases h : p ≤ m
  · exact S.hom p h
  · have he : p = m+1 := by omega
    subst p
    exact next hπ S

lemma extendHom_old (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (p : ℕ) (hp : p ≤ m) :
    extendHom hπ S p (hp.trans (Nat.le_succ m)) = S.hom p hp := by
  simp [extendHom,hp]

lemma extendHom_new (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) : extendHom hπ S (m+1) le_rfl = next hπ S := by
  simp [extendHom]

def extend (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) : System k (m+1) y₀ where
  hom := extendHom hπ S
  zero p hp f s := by
    by_cases h : p ≤ m
    · rw [extendHom_old hπ S p h]
      exact S.zero p h f s
    · have he : p = m+1 := by omega
      subst p
      rw [extendHom_new]
      exact next_zero hπ S f s
  face p hp f i t s := by
    by_cases h : p+1 ≤ m
    · rw [extendHom_old hπ S (p+1) h,extendHom_old hπ S p (by omega)]
      exact S.face p h f i t s
    · have he : p = m := by omega
      subst p
      rw [extendHom_new,extendHom_old hπ S m le_rfl]
      exact next_face hπ S f i t s
  top p hp hk f s := by
    by_cases h : p ≤ m
    · rw [extendHom_old hπ S p h]
      exact S.top p h hk f s
    · have he : p = m+1 := by omega
      subst p
      rw [extendHom_new]
      exact next_top hπ S hk f s
  fixed p hp := by
    by_cases h : p ≤ m
    · rw [extendHom_old hπ S p h]
      exact S.fixed p h
    · have he : p = m+1 := by omega
      subst p
      rw [extendHom_new]
      exact next_fixed hπ S

theorem exists_baseHom (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (f : C(Simplex 0,Y)) :
    ∃ F : C(I × Simplex 0,Y), (∀ s, F (0,s) = f s) ∧
      (0 < k → ∀ s, F (1,s) = y₀) := by
  by_cases hk : 0 < k
  · let h : C(I × Boundary 0,Y) := ⟨fun b => isEmptyElim b.2,continuous_of_discreteTopology⟩
    obtain ⟨F,h₀,h₁,_⟩ := SimplexHomotopy.exists_prescribed (hπ 0 hk) f
      (ContinuousMap.const _ y₀) h (fun b => isEmptyElim b) (fun b => isEmptyElim b)
    exact ⟨F,h₀,fun _ => h₁⟩
  · exact ⟨f.comp ContinuousMap.snd,fun _ => rfl,fun h => (hk h).elim⟩

def baseHom (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (f : C(Simplex 0,Y)) : C(I × Simplex 0,Y) :=
  if f = ContinuousMap.const _ y₀ then ContinuousMap.const _ y₀ else (exists_baseHom hπ y₀ f).choose

def base (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) : System k 0 y₀ where
  hom p hp := by
    have he : p = 0 := Nat.eq_zero_of_le_zero hp
    subst p
    exact baseHom hπ y₀
  zero p hp f s := by
    obtain rfl : p = 0 := Nat.eq_zero_of_le_zero hp
    by_cases hf : f = ContinuousMap.const _ y₀
    · simp only [baseHom,hf,ite_true,ContinuousMap.const_apply]
    · simpa only [baseHom,ite_eq_right hf] using (exists_baseHom hπ y₀ f).choose_spec.1 s
  face p hp := by omega
  top p hp hk f s := by
    obtain rfl : p = 0 := Nat.eq_zero_of_le_zero hp
    by_cases hf : f = ContinuousMap.const _ y₀
    · simp only [baseHom,ite_eq_left hf,ContinuousMap.const_apply]
    · simpa only [baseHom,ite_eq_right hf] using (exists_baseHom hπ y₀ f).choose_spec.2 hk s
  fixed p hp := by
    obtain rfl : p = 0 := Nat.eq_zero_of_le_zero hp
    simp only [baseHom,ite_true]

def system (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) : ∀ m, System k m y₀
  | 0 => base hπ y₀
  | m+1 => extend hπ (system hπ y₀ m)

def hom (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (n : ℕ) : C(Simplex n,Y) → C(I × Simplex n,Y) :=
  (system hπ y₀ n).hom n le_rfl

lemma hom_zero (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (n : ℕ) (f : C(Simplex n,Y)) s : hom hπ y₀ n f (0,s) = f s :=
  (system hπ y₀ n).zero n le_rfl f s

lemma hom_top (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (n : ℕ) (hn : n < k) (f : C(Simplex n,Y)) s : hom hπ y₀ n f (1,s) = y₀ :=
  (system hπ y₀ n).top n le_rfl hn f s

lemma hom_face (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (n : ℕ) (f : C(Simplex (n+1),Y)) (i : Fin (n+2)) t s :
    hom hπ y₀ (n+1) f (t,SimplexBoundary.face i s) =
      hom hπ y₀ n (f.comp (SimplexBoundary.face i)) (t,s) := by
  change (system hπ y₀ (n+1)).hom (n+1) le_rfl f _ = _
  rw [(system hπ y₀ (n+1)).face]
  change extendHom hπ (system hπ y₀ n) n _ _ _ = _
  rw [extendHom_old hπ _ n le_rfl]
  rfl

lemma hom_fixed (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (n : ℕ) : hom hπ y₀ n (ContinuousMap.const _ y₀) = ContinuousMap.const _ y₀ :=
  (system hπ y₀ n).fixed n le_rfl

end FixedSingularTightening

end

end OAI
