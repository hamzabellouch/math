import Mathlib.Tactic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace OAI

noncomputable section

open Classical Set

open Classical
namespace CubicalChains
variable {G A : Type*} [Group G]
abbrev Chains (G A : Type*) := (G × List A) →₀ ℤ

def front (x : A) : Chains G A →ₗ[ℤ] Chains G A :=
  Finsupp.lmapDomain ℤ ℤ (fun p => (p.1,x :: p.2))

def shift (v : A → G) (x : A) : Chains G A →ₗ[ℤ] Chains G A :=
  Finsupp.lmapDomain ℤ ℤ (fun p => (p.1 * v x,p.2))

omit [Group G] in
@[simp] theorem front_single (x : A) (g : G) (w : List A) (n : ℤ) :
    front x (Finsupp.single (g,w) n) = Finsupp.single (g,x::w) n := by
  simp [front]

@[simp] theorem shift_single (v : A → G) (x : A) (g : G) (w : List A) (n : ℤ) :
    shift v x (Finsupp.single (g,w) n) = Finsupp.single (g*v x,w) n := by
  simp [shift]

def boundaryTerm (v : A → G) (g : G) : List A → Chains G A
  | [] => 0
  | x :: w => Finsupp.single (g*v x,w) 1 - Finsupp.single (g,w) 1 -
      front x (boundaryTerm v g w)

def boundary (v : A → G) : Chains G A →ₗ[ℤ] Chains G A :=
  Finsupp.linearCombination ℤ (fun p => boundaryTerm v p.1 p.2)

@[simp] theorem boundary_single (v : A → G) (g : G) (w : List A) (n : ℤ) :
    boundary v (Finsupp.single (g,w) n) = n • boundaryTerm v g w := by
  simp [boundary]

@[simp] theorem boundaryTerm_nil (v : A → G) (g : G) : boundaryTerm v g [] = 0 := rfl
@[simp] theorem boundaryTerm_cons (v : A → G) (g : G) (x : A) (w : List A) :
    boundaryTerm v g (x :: w) = Finsupp.single (g*v x,w) 1 - Finsupp.single (g,w) 1 -
      front x (boundaryTerm v g w) := rfl

theorem boundary_front (v : A → G) (x : A) (c : Chains G A) :
    boundary v (front x c) = shift v x c - c - front x (boundary v c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]; abel
  | single p n =>
      rcases p with ⟨g,w⟩
      simp only [front_single,boundary_single,boundaryTerm_cons,shift_single,map_smul]
      simp only [smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem shift_front (v : A → G) (x y : A) (c : Chains G A) :
    shift v x (front y c) = front y (shift v x c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single p n => rcases p with ⟨g,w⟩; simp

theorem boundaryTerm_shift (v : A → G) (x : A) (g : G) (w : List A)
    (hw : ∀ y ∈ w, Commute (v x) (v y)) :
    boundaryTerm v (g * v x) w = shift v x (boundaryTerm v g w) := by
  induction w with
  | nil => simp
  | cons y w ih =>
      rw [boundaryTerm_cons,boundaryTerm_cons,map_sub,map_sub,shift_single,shift_single,
        shift_front,ih (fun z hz => hw z (by simp [hz]))]
      rw [mul_assoc,(hw y (by simp)).eq,← mul_assoc]

theorem boundary_boundaryTerm (v : A → G) (g : G) (w : List A)
    (hw : w.Pairwise (fun x y => Commute (v x) (v y))) :
    boundary v (boundaryTerm v g w) = 0 := by
  induction w generalizing g with
  | nil => simp
  | cons x w ih =>
      obtain ⟨hx,hw⟩ := List.pairwise_cons.mp hw
      simp only [boundaryTerm_cons,map_sub,boundary_single,one_smul,boundary_front]
      rw [ih _ hw,map_zero,boundaryTerm_shift v x g w hx]
      abel


/-- The part of the boundary incident to the top vertex. -/
def upperTerm (g : G) : List A → Chains G A
  | [] => 0
  | x :: w => -Finsupp.single (g,w) 1 - front x (upperTerm g w)

def upper : Chains G A →ₗ[ℤ] Chains G A :=
  Finsupp.linearCombination ℤ (fun p => upperTerm p.1 p.2)

omit [Group G] in
@[simp] theorem upper_single (g : G) (w : List A) (n : ℤ) :
    upper (Finsupp.single (g,w) n) = n • upperTerm g w := by simp [upper]

omit [Group G] in
@[simp] theorem upperTerm_nil (g : G) : upperTerm g ([] : List A) = 0 := rfl

omit [Group G] in
@[simp] theorem upperTerm_cons (g : G) (x : A) (w : List A) :
    upperTerm g (x::w) = -Finsupp.single (g,w) 1 - front x (upperTerm g w) := rfl

omit [Group G] in
 theorem upper_front (x : A) (c : Chains G A) :
    upper (front x c) = -c - front x (upper c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]; abel
  | single p n =>
      rcases p with ⟨g,w⟩
      simp [smul_sub, Finsupp.smul_single]

def coneTerm (a : G → A) (g : G) (w : List A) : Chains G A :=
  if a g ∈ w then 0 else -Finsupp.single (g,a g::w) 1

def cone (a : G → A) : Chains G A →ₗ[ℤ] Chains G A :=
  Finsupp.linearCombination ℤ (fun p => coneTerm a p.1 p.2)

omit [Group G] in
@[simp] theorem cone_single (a : G → A) (g : G) (w : List A) (n : ℤ) :
    cone a (Finsupp.single (g,w) n) = n • coneTerm a g w := by simp [cone]

omit [Group G] in
 theorem supported_map {I J : Type*} (f : (I →₀ ℤ) →ₗ[ℤ] (J →₀ ℤ))
    (P : Set I) (Q : Set J)
    (h : ∀ i ∈ P, f (Finsupp.single i 1) ∈ Finsupp.supported ℤ ℤ Q)
    {c : I →₀ ℤ} (hc : c ∈ Finsupp.supported ℤ ℤ P) :
    f c ∈ Finsupp.supported ℤ ℤ Q := by
  rw [Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => f c ∈ Finsupp.supported ℤ ℤ Q) _ _ _ _ hc
  · rintro _ ⟨i,hi,rfl⟩; exact h i hi
  · simp
  · intro x y _ _ hx hy; simpa using (Finsupp.supported ℤ ℤ Q).add_mem hx hy
  · intro n x _ hx; simpa using (Finsupp.supported ℤ ℤ Q).smul_mem n hx

omit [Group G] in
 theorem upperTerm_supported (g : G) (w : List A) :
    upperTerm g w ∈ Finsupp.supported ℤ ℤ
      {p : G × List A | p.1 = g ∧ p.2.Sublist w ∧ p.2.length + 1 = w.length} := by
  induction w with
  | nil => simp
  | cons x w ih =>
      rw [upperTerm_cons]
      apply Submodule.sub_mem
      · apply Submodule.neg_mem
        exact Finsupp.single_mem_supported ℤ 1 ⟨rfl, List.sublist_cons_self _ _, rfl⟩
      · apply supported_map (front x) _ _ _ ih
        rintro ⟨g',w'⟩ ⟨rfl,hs,hl⟩
        rw [front_single]
        exact Finsupp.single_mem_supported ℤ 1 ⟨rfl,hs.cons_cons x,by simp; omega⟩

omit [Group G] in
 theorem cone_absent_upper (a : G → A) (g : G) (w : List A) (ha : a g ∉ w) :
    cone a (upperTerm g w) = -front (a g) (upperTerm g w) := by
  have hh := upperTerm_supported g w
  rw [Finsupp.supported_eq_span_single] at hh
  apply Submodule.span_induction (p := fun c _ => cone a c = -front (a g) c) _ _ _ _ hh
  · rintro _ ⟨⟨g',w'⟩,⟨rfl,hs,_⟩,rfl⟩
    have ha' : a g' ∉ w' := fun hm => ha (hs.subset hm)
    simp [coneTerm,ha']
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd,neg_add]
  · intro n c _ hc; simp only [map_smul,hc,smul_neg]

omit [Group G] in
 theorem cone_front_present (a : G → A) (g : G) (w : List A) :
    cone a (front (a g) (upperTerm g w)) = 0 := by
  have hh := upperTerm_supported g w
  rw [Finsupp.supported_eq_span_single] at hh
  apply Submodule.span_induction
    (p := fun c _ => cone a (front (a g) c) = 0) _ _ _ _ hh
  · rintro _ ⟨⟨g',w'⟩,⟨rfl,_,_⟩,rfl⟩
    simp [coneTerm]
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd,add_zero]
  · intro n c _ hc; simp only [map_smul,hc,smul_zero]

omit [Group G] in
 theorem upper_cone_identity (a : G → A) (g : G) (w : List A)
    (hw : a g ∉ w ∨ ∃ u, w = a g :: u ∧ a g ∉ u) :
    upper (coneTerm a g w) + cone a (upperTerm g w) = Finsupp.single (g,w) 1 := by
  rcases hw with ha | ⟨u,rfl,hu⟩
  · rw [coneTerm,ite_eq_right ha,map_neg,upper_single,one_smul,upperTerm_cons,
      cone_absent_upper a g w ha,neg_sub]
    abel
  · simp only [coneTerm,List.mem_cons_self,↓reduceIte,map_zero,upperTerm_cons,
      map_sub,map_neg,cone_single,one_smul,cone_front_present,coneTerm,ite_eq_right hu]
    abel


/-- A lower face is obtained by deleting one direction and crossing it. -/
def Removed (x : A) (w u : List A) : Prop :=
  ∃ p q, w = p ++ x :: q ∧ u = p ++ q

omit [Group G] in
 theorem Removed.mem {x : A} {w u : List A} (h : Removed x w u) : x ∈ w := by
  obtain ⟨p,q,rfl,rfl⟩ := h
  simp

omit [Group G] in
 theorem Removed.sublist {x : A} {w u : List A} (h : Removed x w u) : u.Sublist w := by
  obtain ⟨p,q,rfl,rfl⟩ := h
  exact (List.sublist_cons_self x q).append_left p

omit [Group G] in
 theorem Removed.length {x : A} {w u : List A} (h : Removed x w u) : u.length + 1 = w.length := by
  obtain ⟨p,q,rfl,rfl⟩ := h
  simp; omega

omit [Group G] in
 theorem Removed.not_mem {x : A} {w u : List A} (h : Removed x w u) (hw : w.Nodup) : x ∉ u := by
  obtain ⟨p,q,rfl,rfl⟩ := h
  rw [List.mem_append,not_or]
  refine ⟨?_,(List.nodup_cons.mp (List.nodup_append.mp hw).2.1).1⟩
  intro hx
  exact (List.nodup_append.mp hw).2.2 x hx x (by simp) rfl

omit [Group G] in
 theorem Removed.cons {x y : A} {w u : List A} (h : Removed x w u) : Removed x (y::w) (y::u) := by
  obtain ⟨p,q,rfl,rfl⟩ := h
  exact ⟨y::p,q,rfl,rfl⟩

def lowerTerm (v : A → G) (g : G) (w : List A) := boundaryTerm v g w - upperTerm g w

def lower (v : A → G) : Chains G A →ₗ[ℤ] Chains G A := boundary v - upper

@[simp] theorem lower_single (v : A → G) (g : G) (w : List A) (n : ℤ) :
    lower v (Finsupp.single (g,w) n) = n • lowerTerm v g w := by
  simp [lower,lowerTerm,smul_sub]

@[simp] theorem lowerTerm_nil (v : A → G) (g : G) : lowerTerm v g [] = 0 := by simp [lowerTerm]

@[simp] theorem lowerTerm_cons (v : A → G) (g : G) (x : A) (w : List A) :
    lowerTerm v g (x::w) = Finsupp.single (g*v x,w) 1 - front x (lowerTerm v g w) := by
  simp only [lowerTerm,boundaryTerm_cons,upperTerm_cons,map_sub]
  abel

 theorem lowerTerm_supported (v : A → G) (g : G) (w : List A) :
    lowerTerm v g w ∈ Finsupp.supported ℤ ℤ
      {p : G × List A | ∃ x, Removed x w p.2 ∧ p.1 = g * v x} := by
  induction w with
  | nil => simp
  | cons x w ih =>
      rw [lowerTerm_cons]
      apply Submodule.sub_mem
      · exact Finsupp.single_mem_supported ℤ 1 ⟨x,⟨[],w,rfl,rfl⟩,rfl⟩
      · apply supported_map (front x) _ _ _ ih
        rintro ⟨g',w'⟩ ⟨y,hy,rfl⟩
        rw [front_single]
        exact Finsupp.single_mem_supported ℤ 1 ⟨y,hy.cons,rfl⟩

variable [LinearOrder A]

/-- Local combinatorial descending-cube data. All these fields will be supplied
by the actual trace normal form, not by a geometric exactness assumption. -/
structure DescentSystem (v : A → G) where
  length : G → ℕ
  desc : G → Set A
  step : ∀ g x, x ∈ desc g → length (g*v x)+1 = length g
  preserve : ∀ g x y, x ∈ desc g → y ∈ desc g → x ≠ y → y ∈ desc (g*v x)
  commute : ∀ g x y, x ∈ desc g → y ∈ desc g → x ≠ y → Commute (v x) (v y)
  choose : G → A
  choose_mem : ∀ g, 0 < length g → choose g ∈ desc g
  choose_le : ∀ g x, x ∈ desc g → choose g ≤ x

namespace DescentSystem
variable {v : A → G} (D : DescentSystem v)

def Valid (g : G) (w : List A) : Prop := w.Pairwise (· < ·) ∧ ∀ x ∈ w, x ∈ D.desc g

def admissible (k N : ℕ) : Submodule ℤ (Chains G A) :=
  Finsupp.supported ℤ ℤ {p | D.Valid p.1 p.2 ∧ p.2.length = k ∧ D.length p.1 ≤ N}

theorem valid_sublist {g : G} {w u : List A} (hw : D.Valid g w) (hu : u.Sublist w) : D.Valid g u :=
  ⟨hw.1.sublist hu,fun x hx => hw.2 x (hu.subset hx)⟩

theorem valid_nodup {g : G} {w : List A} (hw : D.Valid g w) : w.Nodup := hw.1.imp_of_mem (by
  intro x y _ _ h; exact ne_of_lt h)

theorem valid_removed {g : G} {w u : List A} {x : A}
    (hw : D.Valid g w) (hu : Removed x w u) : D.Valid (g*v x) u := by
  refine ⟨hw.1.sublist hu.sublist,?_⟩
  intro y hy
  exact D.preserve g x y (hw.2 x hu.mem) (hw.2 y (hu.sublist.subset hy))
    (fun he => hu.not_mem (D.valid_nodup hw) (he ▸ hy))

theorem valid_zero_length {g : G} {w : List A} (hw : D.Valid g w) (hg : D.length g = 0) : w = [] := by
  cases w with
  | nil => rfl
  | cons x w => have := D.step g x (hw.2 x (by simp)); omega

theorem choose_head {g : G} {w : List A} (hw : D.Valid g w) :
    D.choose g ∉ w ∨ ∃ u, w = D.choose g :: u ∧ D.choose g ∉ u := by
  by_cases ha : D.choose g ∈ w
  · right
    cases w with
    | nil => simp at ha
    | cons x w =>
        have hp := List.pairwise_cons.mp hw.1
        have hx : D.choose g = x := by
          rcases List.mem_cons.mp ha with h | h
          · exact h
          · exact False.elim ((not_lt_of_ge (D.choose_le g x (hw.2 x (by simp))))
              (hp.1 (D.choose g) h))
        subst x
        exact ⟨w,rfl,(List.nodup_cons.mp (D.valid_nodup hw)).1⟩
  · exact Or.inl ha

theorem valid_cone {g : G} {w : List A} (hw : D.Valid g w)
    (hg : 0 < D.length g) (ha : D.choose g ∉ w) : D.Valid g (D.choose g :: w) := by
  refine ⟨List.pairwise_cons.mpr ⟨?_,hw.1⟩,?_⟩
  · intro y hy
    exact lt_of_le_of_ne (D.choose_le g y (hw.2 y hy)) (fun he => ha (he ▸ hy))
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact D.choose_mem g hg
    · exact hw.2 y hy

theorem upperTerm_admissible {g : G} {w : List A} (hw : D.Valid g w) :
    upperTerm g w ∈ D.admissible (w.length-1) (D.length g) := by
  apply Finsupp.supported_mono _ (upperTerm_supported g w)
  rintro ⟨g',w'⟩ ⟨rfl,hs,hl⟩
  exact ⟨D.valid_sublist hw hs,by omega,le_rfl⟩

theorem lowerTerm_admissible {g : G} {w : List A} (hw : D.Valid g w) :
    lowerTerm v g w ∈ D.admissible (w.length-1) (D.length g-1) := by
  apply Finsupp.supported_mono _ (lowerTerm_supported v g w)
  rintro ⟨g',w'⟩ ⟨x,hs,rfl⟩
  have hl := D.step g x (hw.2 x hs.mem)
  exact ⟨D.valid_removed hw hs,by have := hs.length; omega,by simpa using (show D.length (g*v x) ≤ D.length g-1 by omega)⟩

def homotopyTerm (g : G) (w : List A) : Chains G A :=
  if D.length g = 0 then 0 else coneTerm D.choose g w

def homotopy : Chains G A →ₗ[ℤ] Chains G A :=
  Finsupp.linearCombination ℤ (fun p => D.homotopyTerm p.1 p.2)

@[simp] theorem homotopy_single (g : G) (w : List A) (n : ℤ) :
    D.homotopy (Finsupp.single (g,w) n) = n • D.homotopyTerm g w := by simp [homotopy]

theorem homotopyTerm_admissible {g : G} {w : List A} (hw : D.Valid g w) :
    D.homotopyTerm g w ∈ D.admissible (w.length+1) (D.length g) := by
  unfold homotopyTerm coneTerm
  split
  · exact Submodule.zero_mem _
  · rename_i hg
    split
    · exact Submodule.zero_mem _
    · rename_i ha
      apply Submodule.neg_mem
      exact Finsupp.single_mem_supported ℤ 1 ⟨D.valid_cone hw (Nat.pos_of_ne_zero hg) ha,rfl,le_rfl⟩


theorem admissible_mono {k N M : ℕ} (hNM : N ≤ M) : D.admissible k N ≤ D.admissible k M := by
  apply Finsupp.supported_mono
  rintro p ⟨hv,hk,hl⟩
  exact ⟨hv,hk,hl.trans hNM⟩

theorem upper_admissible {k N : ℕ} {c : Chains G A} (hc : c ∈ D.admissible k N) :
    upper c ∈ D.admissible (k-1) N := by
  apply supported_map upper _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hk,hN⟩
  dsimp only [Prod.fst,Prod.snd] at hw hk hN
  simp only [upper_single,one_smul]
  simpa only [admissible,hk] using D.admissible_mono hN (D.upperTerm_admissible hw)

theorem lower_admissible {k N : ℕ} {c : Chains G A} (hc : c ∈ D.admissible k N) :
    lower v c ∈ D.admissible (k-1) (N-1) := by
  apply supported_map (lower v) _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hk,hN⟩
  dsimp only [Prod.fst,Prod.snd] at hw hk hN
  simp only [lower_single,one_smul]
  simpa only [admissible,hk] using D.admissible_mono (Nat.sub_le_sub_right hN 1) (D.lowerTerm_admissible hw)

theorem boundary_admissible {k N : ℕ} {c : Chains G A} (hc : c ∈ D.admissible k N) :
    boundary v c ∈ D.admissible (k-1) N := by
  have h : boundary v c = upper c + lower v c := by simp [lower]
  rw [h]
  exact Submodule.add_mem _ (D.upper_admissible hc)
    (D.admissible_mono (Nat.sub_le _ _) (D.lower_admissible hc))

theorem homotopy_admissible {k N : ℕ} {c : Chains G A} (hc : c ∈ D.admissible k N) :
    D.homotopy c ∈ D.admissible (k+1) N := by
  apply supported_map D.homotopy _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hk,hN⟩
  dsimp only [Prod.fst,Prod.snd] at hw hk hN
  simp only [homotopy_single,one_smul]
  simpa only [admissible,hk] using D.admissible_mono hN (D.homotopyTerm_admissible hw)

theorem boundary_squared {k N : ℕ} {c : Chains G A} (hc : c ∈ D.admissible k N) :
    boundary v (boundary v c) = 0 := by
  rw [admissible,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => boundary v (boundary v c) = 0) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨hw,_,_⟩,rfl⟩
    simp only [boundary_single,one_smul]
    apply boundary_boundaryTerm
    exact hw.1.imp_of_mem (fun {x y} hx hy h => D.commute g x y (hw.2 x hx) (hw.2 y hy) (ne_of_lt h))
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd,add_zero]
  · intro n c _ hc; simp only [map_smul,hc,smul_zero]

theorem homotopy_upperTerm {g : G} (w : List A) (hg : D.length g ≠ 0) :
    D.homotopy (upperTerm g w) = cone D.choose (upperTerm g w) := by
  have hh := upperTerm_supported g w
  rw [Finsupp.supported_eq_span_single] at hh
  apply Submodule.span_induction
    (p := fun c _ => D.homotopy c = cone D.choose c) _ _ _ _ hh
  · rintro _ ⟨⟨g',w'⟩,⟨rfl,_,_⟩,rfl⟩
    simp only [homotopy_single,cone_single,one_smul,homotopyTerm,ite_eq_right hg]
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

theorem upper_homotopy_identity {g : G} {w : List A} (hw : D.Valid g w)
    (hg : D.length g ≠ 0) :
    upper (D.homotopyTerm g w) + D.homotopy (upperTerm g w) = Finsupp.single (g,w) 1 := by
  rw [homotopyTerm,ite_eq_right hg,D.homotopy_upperTerm w hg]
  exact upper_cone_identity D.choose g w (D.choose_head hw)

def remainder : Chains G A →ₗ[ℤ] Chains G A :=
  LinearMap.id - (boundary v).comp D.homotopy - D.homotopy.comp (boundary v)

theorem remainder_single {g : G} {w : List A} (hw : D.Valid g w) (hg : D.length g ≠ 0) :
    D.remainder (Finsupp.single (g,w) 1) =
      -(lower v (D.homotopyTerm g w) + D.homotopy (lowerTerm v g w)) := by
  have he := D.upper_homotopy_identity hw hg
  simp only [remainder,LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.id_apply,
    homotopy_single,boundary_single,one_smul]
  simp only [lower,LinearMap.sub_apply,lowerTerm,map_sub]
  rw [← he]
  abel

theorem remainder_admissible {k N : ℕ} (hk : 0 < k) {c : Chains G A}
    (hc : c ∈ D.admissible k (N+1)) : D.remainder c ∈ D.admissible k N := by
  apply supported_map D.remainder _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hk',hN⟩
  dsimp only [Prod.fst,Prod.snd] at hw hk' hN
  have hpos : D.length g ≠ 0 := by
    intro hz
    have he := D.valid_zero_length hw hz
    simp only [he,List.length_nil] at hk'
    omega
  rw [D.remainder_single hw hpos]
  apply Submodule.neg_mem
  apply Submodule.add_mem
  · have hh := D.lower_admissible (D.homotopyTerm_admissible hw)
    have hNN : D.length g - 1 ≤ N := by omega
    simpa only [admissible,Nat.add_sub_cancel,hk'] using D.admissible_mono hNN hh
  · have hh := D.homotopy_admissible (D.lowerTerm_admissible hw)
    have hlen : w.length - 1 + 1 = k := by omega
    have hNN : D.length g - 1 ≤ N := by omega
    simpa only [admissible,hlen] using D.admissible_mono hNN hh

theorem admissible_zero {k : ℕ} (hk : 0 < k) : D.admissible k 0 = ⊥ := by
  apply le_antisymm _ bot_le
  suffices he : {p : G × List A | D.Valid p.1 p.2 ∧ p.2.length = k ∧ D.length p.1 ≤ 0} = ∅ by
    change Finsupp.supported ℤ ℤ _ ≤ ⊥
    rw [he,Finsupp.supported_empty]
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ⟨g,w⟩ ⟨hw,hl,hg⟩
  dsimp only [Prod.fst,Prod.snd] at hw hl hg
  have he := D.valid_zero_length hw (by omega)
  simp only [he,List.length_nil] at hl
  omega

/-- Finite-support descending-cube contraction: every positive-dimensional
cycle bounds, with no topological exactness or contractibility assumption. -/
theorem cycle_bounds {k N : ℕ} (hk : 0 < k) (c : Chains G A)
    (hc : c ∈ D.admissible k N) (hz : boundary v c = 0) :
    ∃ b ∈ D.admissible (k+1) N, boundary v b = c := by
  induction N generalizing c with
  | zero =>
      rw [D.admissible_zero hk,Submodule.mem_bot] at hc
      subst c
      exact ⟨0,Submodule.zero_mem _,map_zero _⟩
  | succ N ih =>
      let r := D.remainder c
      have hr : r = c - boundary v (D.homotopy c) := by
        simp [r,remainder,hz]
      have hrz : boundary v r = 0 := by
        rw [hr,map_sub,hz,D.boundary_squared (D.homotopy_admissible hc),sub_zero]
      obtain ⟨b,hb,hdb⟩ := ih r (D.remainder_admissible hk hc) hrz
      refine ⟨D.homotopy c + b,Submodule.add_mem _ (D.homotopy_admissible hc)
        (D.admissible_mono (Nat.le_succ N) hb),?_⟩
      rw [map_add,hdb,hr]
      abel

end DescentSystem
end CubicalChains


end

end OAI
