import Mathlib
import OAI.GroupTheory.FiniteType.CubeDisk
import OAI.GroupTheory.FiniteType.DiskHEP

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
namespace SimplexHomotopy
open Set Topology Metric
open scoped unitInterval
open SimplexBoundary
universe u
variable {Y : Type u} [TopologicalSpace Y]

def diskMap {n : ℕ} (f : C(Simplex n,Y)) : C(DiskHEP.Disk n,Y) :=
  f.comp ⟨(SimplexDisk.diskEquiv n).symm,(SimplexDisk.diskEquiv n).symm.continuous⟩

def sideMap {n : ℕ} (h : C(I × Boundary n,Y)) : C(I × DiskHEP.Boundary n,Y) :=
  h.comp ⟨fun z => (z.1,(boundaryEquiv n).symm z.2),
    continuous_fst.prodMk ((boundaryEquiv n).symm.continuous.comp continuous_snd)⟩

lemma boundary_compat {n : ℕ} (b : DiskHEP.Boundary n) :
    (SimplexDisk.diskEquiv n).symm (DiskHEP.boundaryInclusion n b) =
      ((boundaryEquiv n).symm b).1 := rfl

lemma boundary_compat_forward {n : ℕ} (b : Boundary n) :
    SimplexDisk.diskEquiv n b.1 = DiskHEP.boundaryInclusion n (boundaryEquiv n b) := rfl

lemma sideMap_time {n : ℕ} (f : C(Simplex n,Y)) (h : C(I × Boundary n,Y)) (t : I)
    (ht : ∀ b, h (t,b) = f b.1) (b : DiskHEP.Boundary n) :
    sideMap h (t,b) = diskMap f (DiskHEP.boundaryInclusion n b) := ht _

theorem exists_extension {n : ℕ} (f : C(Simplex n,Y)) (h : C(I × Boundary n,Y))
    (h0 : ∀ b, h (0,b) = f b.1) :
    ∃ F : C(I × Simplex n,Y), (∀ s, F (0,s) = f s) ∧
      ∀ t b, F (t,b.1) = h (t,b) := by
  let hd := sideMap_time f h 0 h0
  let K := DiskHEP.extend (diskMap f) (sideMap h) hd
  let F : C(I × Simplex n,Y) := K.comp
    ⟨fun z => (z.1,SimplexDisk.diskEquiv n z.2),
      continuous_fst.prodMk ((SimplexDisk.diskEquiv n).continuous.comp continuous_snd)⟩
  refine ⟨F,?_,?_⟩
  · intro s
    change DiskHEP.extend _ _ hd (0,SimplexDisk.diskEquiv n s) = _
    rw [DiskHEP.extend_zero]
    exact congrArg f ((SimplexDisk.diskEquiv n).symm_apply_apply s)
  · intro t b
    change DiskHEP.extend _ _ hd (t,SimplexDisk.diskEquiv n b.1) = _
    rw [boundary_compat_forward,DiskHEP.extend_side]
    exact congrArg h (Prod.ext rfl ((boundaryEquiv n).symm_apply_apply b))

theorem exists_disk_cylinder {n : ℕ}
    (hπ : ∀ y : Y, Subsingleton (HomotopyGroup (Fin n) Y y))
    (f₀ f₁ : C(CWCylinder.Disk n,Y)) (h : C(I × CWCylinder.Boundary n,Y))
    (h₀ : ∀ v, h (0,v) = f₀ (CWCylinder.boundaryDisk n v))
    (h₁ : ∀ v, h (1,v) = f₁ (CWCylinder.boundaryDisk n v)) :
    ∃ F : C(I × CWCylinder.Disk n,Y),
      (∀ v, F (0,v) = f₀ v) ∧ (∀ v, F (1,v) = f₁ v) ∧
      ∀ t v, F (t,CWCylinder.boundaryDisk n v) = h (t,v) := by
  let b := CWCylinder.boundaryMap f₀ f₁ h h₀ h₁
  let := hπ (b (SphereQuotient.pole n))
  obtain ⟨g,hg⟩ := SphereExtension.exists_extension b (WeakSphere.sphere_nullhomotopic n b)
  have hg' (v : CWCylinder.Boundary (n+1)) : g (CWCylinder.boundaryDisk (n+1) v) = b v := hg v
  refine ⟨g.comp (CWCylinder.encode n),?_,?_,?_⟩
  · intro v
    change g (CWCylinder.encode n (0,v)) = _
    rw [show (0,v) = CWCylinder.faceCylinder n (Sum.inl v) from rfl,CWCylinder.face_encode,hg']
    exact CWCylinder.boundaryMap_face f₀ f₁ h h₀ h₁ (Sum.inl v)
  · intro v
    change g (CWCylinder.encode n (1,v)) = _
    rw [show (1,v) = CWCylinder.faceCylinder n (Sum.inr (Sum.inl v)) from rfl,CWCylinder.face_encode,hg']
    exact CWCylinder.boundaryMap_face f₀ f₁ h h₀ h₁ (Sum.inr (Sum.inl v))
  · intro t v
    change g (CWCylinder.encode n (t,CWCylinder.boundaryDisk n v)) = _
    rw [show (t,CWCylinder.boundaryDisk n v) = CWCylinder.faceCylinder n (Sum.inr (Sum.inr (t,v))) from rfl,
      CWCylinder.face_encode,hg']
    exact CWCylinder.boundaryMap_face f₀ f₁ h h₀ h₁ (Sum.inr (Sum.inr (t,v)))

theorem exists_prescribed {n : ℕ}
    (hπ : ∀ y : Y, Subsingleton (HomotopyGroup (Fin n) Y y))
    (f₀ f₁ : C(Simplex n,Y)) (h : C(I × Boundary n,Y))
    (h₀ : ∀ b, h (0,b) = f₀ b.1) (h₁ : ∀ b, h (1,b) = f₁ b.1) :
    ∃ F : C(I × Simplex n,Y), (∀ s, F (0,s) = f₀ s) ∧
      (∀ s, F (1,s) = f₁ s) ∧ ∀ t b, F (t,b.1) = h (t,b) := by
  obtain ⟨K,hK₀,hK₁,hKs⟩ := exists_disk_cylinder hπ (diskMap f₀) (diskMap f₁)
    (sideMap h) (sideMap_time f₀ h 0 h₀) (sideMap_time f₁ h 1 h₁)
  let F : C(I × Simplex n,Y) := K.comp
    ⟨fun z => (z.1,SimplexDisk.diskEquiv n z.2),
      continuous_fst.prodMk ((SimplexDisk.diskEquiv n).continuous.comp continuous_snd)⟩
  refine ⟨F,?_,?_,?_⟩
  · intro s
    change K (0,SimplexDisk.diskEquiv n s) = _
    rw [hK₀]
    exact congrArg f₀ ((SimplexDisk.diskEquiv n).symm_apply_apply s)
  · intro s
    change K (1,SimplexDisk.diskEquiv n s) = _
    rw [hK₁]
    exact congrArg f₁ ((SimplexDisk.diskEquiv n).symm_apply_apply s)
  · intro t b
    change K (t,SimplexDisk.diskEquiv n b.1) = _
    rw [boundary_compat_forward]
    change K (t,CWCylinder.boundaryDisk n (boundaryEquiv n b)) = _
    rw [hKs]
    exact congrArg h (Prod.ext rfl ((boundaryEquiv n).symm_apply_apply b))

end SimplexHomotopy

namespace SimplexBoundary
open Set Topology Metric
open scoped unitInterval

lemma face_injective {n : ℕ} (i : Fin (n+2)) : Function.Injective (face i) := by
  intro a b h
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro j
  simpa only [face_succAbove] using congrArg (fun s : Simplex (n+1) => s.weights (i.succAbove j)) h

lemma face_face {n : ℕ} (i : Fin (n+3)) (j : Fin (n+2)) (s : Simplex n) :
    face (i.succAbove j) (face (j.predAbove i) s) = face i (face j s) := by
  change Convexity.StdSimplex.map (i.succAbove j).succAbove (Convexity.StdSimplex.map (j.predAbove i).succAbove s) =
    Convexity.StdSimplex.map i.succAbove (Convexity.StdSimplex.map j.succAbove s)
  rw [Convexity.StdSimplex.map_map, Convexity.StdSimplex.map_map]
  congr 1
  funext k
  exact Fin.succAbove_succAbove_succAbove_predAbove i j k

instance boundary_zero_isEmpty : IsEmpty (Boundary 0) := by
  constructor
  intro s
  obtain ⟨i,hi⟩ := s.2
  have hs := s.1.total_of_fintype
  have hi0 : i = 0 := Fin.ext (by omega)
  rw [hi0] at hi
  have hs' : s.1.weights 0 = 1 := (Fin.sum_univ_one _).symm.trans hs
  exact zero_ne_one (hi.symm.trans hs')

theorem face_overlap {n : ℕ} {i j : Fin (n+3)} (hij : i ≠ j)
    {a b : Simplex (n+1)} (h : face i a = face j b) :
    ∃ (k : Fin (n+2)) (s : Simplex n), j = i.succAbove k ∧
      a = face k s ∧ b = face (k.predAbove i) s := by
  obtain ⟨k,hk⟩ : ∃ k, j = i.succAbove k := by
    rcases Fin.eq_self_or_eq_succAbove i j with h' | h'
    · exact False.elim (hij h'.symm)
    · exact h'
  subst j
  have ha : a.weights k = 0 := by
    have he := congrArg (fun s : Simplex (n+2) => s.weights (i.succAbove k)) h
    simpa only [face_succAbove,face_zero] using he
  let s := drop k a ha
  have has : face k s = a := face_drop _ _ _
  refine ⟨k,s,rfl,has.symm,?_⟩
  apply (face_injective (i.succAbove k))
  rw [face_face,has]
  exact h.symm

universe u
variable {Y : Type u} [TopologicalSpace Y]

omit [TopologicalSpace Y] in
theorem compatible_faces {n : ℕ} (h : Fin (n+2) → Simplex n → Y)
    (hh : ∀ (m : ℕ) (hm : n = m+1) (i : Fin (m+3)) (j : Fin (m+2)) (s : Simplex m),
      h (hm ▸ i.succAbove j) (hm ▸ face (j.predAbove i) s) =
        h (hm ▸ i) (hm ▸ face j s)) :
    ∀ i j a b, face i a = face j b → h i a = h j b := by
  intro i j a b hab
  by_cases hij : i = j
  · subst j
    exact congrArg (h i) (face_injective i hab)
  cases n with
  | zero =>
    have hx : (face i a).weights j = 0 := by rw [hab]; exact face_zero _ _
    obtain ⟨k,hk⟩ : ∃ k, j = i.succAbove k := by
      rcases Fin.eq_self_or_eq_succAbove i j with h' | h'
      · exact False.elim (hij h'.symm)
      · exact h'
    rw [hk,face_succAbove] at hx
    have hs := a.total_of_fintype
    have hk0 : k = 0 := Subsingleton.elim _ _
    have hs' : a.weights 0 = 1 := (Fin.sum_univ_one _).symm.trans hs
    rw [hk0] at hx
    exact False.elim (zero_ne_one (hx.symm.trans hs'))
  | succ n =>
    obtain ⟨k,s,rfl,rfl,rfl⟩ := face_overlap hij hab
    exact (hh n rfl i k s).symm

def glueHomotopies {n : ℕ} (h : Fin (n+2) → C(I × Simplex n,Y))
    (hh : ∀ t i j a b, face i a = face j b → h i (t,a) = h j (t,b)) :
    C(I × Boundary (n+1),Y) :=
  let h' : Fin (n+2) → C(Simplex n,C(I,Y)) := fun i => ((h i).comp ⟨Prod.swap,continuous_swap⟩).curry
  let b := glueFaces h' (by
    intro i j a b hab
    apply ContinuousMap.ext
    intro t
    exact hh t i j a b hab)
  b.uncurry.comp ⟨Prod.swap,continuous_swap⟩

@[simp] theorem glueHomotopies_face {n : ℕ} (h : Fin (n+2) → C(I × Simplex n,Y))
    (hh : ∀ t i j a b, face i a = face j b → h i (t,a) = h j (t,b))
    (i : Fin (n+2)) (a : Simplex n) (t : I) :
    glueHomotopies h hh (t,faceQuot n (i,a)) = h i (t,a) := by
  unfold glueHomotopies
  dsimp only [ContinuousMap.comp_apply,ContinuousMap.coe_mk,Prod.swap,ContinuousMap.uncurry,Function.uncurry]
  rw [glueFaces_face]
  rfl

end SimplexBoundary

namespace SingularTightening
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
  (exists_next hπ S f).choose

lemma next_zero (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (f : C(Simplex (m+1),Y)) (s : Simplex (m+1)) :
    next hπ S f (0,s) = f s := (exists_next hπ S f).choose_spec.1 s

lemma next_face (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (f : C(Simplex (m+1),Y)) (i : Fin (m+2)) t s :
    next hπ S f (t,SimplexBoundary.face i s) =
      S.hom m le_rfl (f.comp (SimplexBoundary.face i)) (t,s) := by
  have h := (exists_next hπ S f).choose_spec.2.1 t (faceQuot m (i,s))
  change next hπ S f (t,SimplexBoundary.face i s) = boundaryHom S f (t,faceQuot m (i,s)) at h
  rw [boundaryHom,glueHomotopies_face] at h
  exact h

lemma next_top (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (h : m+1 < k) (f : C(Simplex (m+1),Y)) s :
    next hπ S f (1,s) = y₀ := (exists_next hπ S f).choose_spec.2.2 h s

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
  (exists_baseHom hπ y₀ f).choose

def base (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) : System k 0 y₀ where
  hom p hp := by
    have he : p = 0 := Nat.eq_zero_of_le_zero hp
    subst p
    exact baseHom hπ y₀
  zero p hp f s := by
    obtain rfl : p = 0 := Nat.eq_zero_of_le_zero hp
    exact (exists_baseHom hπ y₀ f).choose_spec.1 s
  face p hp := by omega
  top p hp hk f s := by
    obtain rfl : p = 0 := Nat.eq_zero_of_le_zero hp
    exact (exists_baseHom hπ y₀ f).choose_spec.2 hk s

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

end SingularTightening

end

end OAI
