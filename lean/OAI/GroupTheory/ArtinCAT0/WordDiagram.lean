import OAI.GroupTheory.ArtinCAT0.Grid

namespace OAI

namespace ArtinCAT0.WordDiagram

abbrev Letter := Fin 3 × Bool
abbrev Word := FreeMonoid Letter

def positive (i : Fin 3) : Word := FreeMonoid.of (i,true)
def signed (s : Letter) : TriangleGroup := if s.2 then triangleGen s.1 else (triangleGen s.1)⁻¹

inductive Rel : Word → Word → Prop
  | cancel (s : Letter) : Rel (FreeMonoid.of s * FreeMonoid.of (s.1,!s.2)) 1
  | braid (i : Fin 3) : Rel (positive i * positive (i+1) * positive i)
      (positive (i+1) * positive i * positive (i+1))

abbrev P := PresentedMonoid Rel

def eval : Word →* TriangleGroup := FreeMonoid.lift signed

lemma rel_sound {u v : Word} (h : Rel u v) : eval u = eval v := by
  cases h with
  | cancel s => rcases s with ⟨i,b⟩; cases b <;> simp [eval,signed]
  | braid i => simpa [eval,positive,signed] using triangle_braid i

lemma isUnit_of (s : Letter) : IsUnit (PresentedMonoid.of Rel s) := by
  let a := PresentedMonoid.of Rel s
  let b := PresentedMonoid.of Rel (s.1,!s.2)
  have hab : a*b = 1 := by
    simpa only [a,b,PresentedMonoid.of,map_mul,map_one] using
      PresentedMonoid.mk_eq_mk_of_rel (Rel.cancel s)
  have hba : b*a = 1 := by
    simpa only [a,b,PresentedMonoid.of,map_mul,map_one,Bool.not_not] using
      PresentedMonoid.mk_eq_mk_of_rel (Rel.cancel (s.1,!s.2))
  exact ⟨⟨a,b,hab,hba⟩,rfl⟩

lemma all_isUnit (x : P) : IsUnit x := by
  induction x using PresentedMonoid.inductionOn with | h w =>
    induction w with
    | one => exact isUnit_one
    | of s => exact isUnit_of s
    | mul a b ha hb => exact ha.mul hb

noncomputable instance : Group P := groupOfIsUnit all_isUnit

lemma negative_of (i : Fin 3) :
    PresentedMonoid.of Rel (i,false) = (PresentedMonoid.of Rel (i,true))⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  simpa only [PresentedMonoid.of,map_mul,map_one,Bool.not_true] using
    PresentedMonoid.mk_eq_mk_of_rel (Rel.cancel (i,true))

noncomputable def fromTriangle : TriangleGroup →* P :=
  triangleLift (fun i => PresentedMonoid.of Rel (i,true)) (by
    intro i
    simpa only [positive,PresentedMonoid.of,map_mul] using
      PresentedMonoid.mk_eq_mk_of_rel (Rel.braid i))

lemma fromTriangle_eval : fromTriangle.comp eval = PresentedMonoid.mk Rel := by
  apply FreeMonoid.hom_eq
  rintro ⟨i,b⟩
  cases b
  · simpa [eval,signed,fromTriangle,triangleLift_gen,PresentedMonoid.of] using (negative_of i).symm
  · simp [eval,signed,fromTriangle,triangleLift_gen,PresentedMonoid.of]

/-- Null words have actual finite derivations from cancellation and braid moves;
this is not an assumed van Kampen theorem. -/
theorem null_derivation (w : Word) (h : eval w = 1) : conGen Rel w 1 := by
  apply PresentedMonoid.mk_eq_mk_iff.1
  rw [← fromTriangle_eval]
  simp [h]

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram
open Relation

/-- A single local cancellation or braid replacement, with fixed contexts. -/
inductive Step : Word → Word → Prop
  | context (l r : Word) {u v : Word} (h : Rel u v) : Step (l*u*r) (l*v*r)

lemma step_context {u v : Word} (h : Step u v) (l r : Word) : Step (l*u*r) (l*v*r) := by
  cases h with
  | context a b h => simpa only [mul_assoc] using Step.context (l*a) (b*r) h

lemma homotopy_context {u v : Word} (h : EqvGen Step u v) (l r : Word) :
    EqvGen Step (l*u*r) (l*v*r) := by
  induction h with
  | rel a b h => exact .rel _ _ (step_context h l r)
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c hab hbc ih1 ih2 => exact .trans _ _ _ ih1 ih2

lemma derivation_homotopy {u v : Word} (h : conGen Rel u v) : EqvGen Step u v := by
  induction h with
  | of u v h =>
    simpa only [one_mul,mul_one] using EqvGen.rel _ _ (Step.context 1 1 h)
  | refl u => exact .refl _
  | symm h ih => exact .symm _ _ ih
  | trans h1 h2 ih1 ih2 => exact .trans _ _ _ ih1 ih2
  | @mul w x y z h1 h2 ih1 ih2 =>
    exact .trans _ _ _ (by simpa only [one_mul] using homotopy_context ih1 1 y)
      (by simpa only [mul_one] using homotopy_context ih2 x 1)

theorem null_local_moves (w : Word) (h : eval w = 1) :
    ReflTransGen (SymmGen Step) w 1 := by
  rw [EqvGen.reflTransGen_symmGen]
  exact derivation_homotopy (null_derivation w h)

end ArtinCAT0.WordDiagram

namespace ArtinCAT0

def positiveValue (q : Fin 9) : TriangleGroup :=
  if h : q.val < 3 then triangleGen ⟨q.val,h⟩
  else if h' : q.val < 6 then triangleX ⟨q.val-3,by omega⟩ 2
  else triangleH ⟨q.val-6,by omega⟩

def positivePerm (q : Fin 9) : Equiv.Perm Mirror :=
  if h : q.val < 3 then mirrorPerm ⟨q.val,h⟩
  else if h' : q.val < 6 then
    let b : Fin 3 := ⟨q.val-3,by omega⟩
    (mirrorPerm (b+1))⁻¹ * mirrorPerm b * mirrorPerm (b+1)
  else
    let b : Fin 3 := ⟨q.val-6,by omega⟩
    mirrorPerm b * mirrorPerm (b+1)

def positiveDegree (q : Fin 9) : ℤ := if q.val < 6 then 1 else 2

def directionValue (d : LinkDirection) : TriangleGroup :=
  if h : d.val < 9 then positiveValue ⟨d.val,h⟩
  else (positiveValue ⟨d.val-9,by omega⟩)⁻¹

def directionPerm (d : LinkDirection) : Equiv.Perm Mirror :=
  if h : d.val < 9 then positivePerm ⟨d.val,h⟩
  else (positivePerm ⟨d.val-9,by omega⟩)⁻¹

def directionDegree (d : LinkDirection) : ℤ :=
  if h : d.val < 9 then positiveDegree ⟨d.val,h⟩
  else -positiveDegree ⟨d.val-9,by omega⟩

@[simp] lemma positiveValue_xLetter (b i : Fin 3) : positiveValue (xLetter b i) = triangleX b i := by
  fin_cases b <;> fin_cases i <;> rfl

@[simp] lemma positiveValue_hLetter (b : Fin 3) : positiveValue (hLetter b) = triangleH b := by
  fin_cases b <;> rfl

@[simp] lemma directionValue_positive (q : Fin 9) : directionValue (positiveDirection q) = positiveValue q := by
  simp [directionValue,positiveDirection,q.isLt]

@[simp] lemma directionValue_negative (q : Fin 9) : directionValue (negativeDirection q) = (positiveValue q)⁻¹ := by
  simp [directionValue,negativeDirection,show ¬q.val+9 < 9 by omega]

lemma positiveValue_linear (q : Fin 9) : mirrorLinear (positiveValue q) = positivePerm q := by
  fin_cases q <;> simp [positiveValue,positivePerm,mirrorLinear,triangleX,triangleH,mirrorGenerator]

lemma positiveValue_degree (q : Fin 9) :
    (triangleExponent (positiveValue q)).toAdd = positiveDegree q := by
  fin_cases q <;> norm_num [positiveValue,positiveDegree]

lemma directionValue_linear (d : LinkDirection) :
    mirrorLinear (directionValue d) = directionPerm d := by
  unfold directionValue directionPerm
  split_ifs
  · exact positiveValue_linear _
  · simp only [mirrorLinear,map_inv,SemidirectProduct.inv_right]
    exact congrArg Inv.inv (positiveValue_linear _)

lemma directionValue_degree (d : LinkDirection) :
    (triangleExponent (directionValue d)).toAdd = directionDegree d := by
  unfold directionValue directionDegree
  split_ifs
  · exact positiveValue_degree _
  · simpa using congrArg Neg.neg (positiveValue_degree ⟨d.val-9,by omega⟩)

def directionSignature (d : LinkDirection) : ℤ × Mirror × Mirror × Mirror :=
  (directionDegree d,directionPerm d (0,0),directionPerm d (1,0),directionPerm d (2,0))

lemma directionSignature_injective : Function.Injective directionSignature := by decide

lemma directionValue_injective : Function.Injective directionValue := by
  intro d e h
  apply directionSignature_injective
  unfold directionSignature
  have hp := congrArg mirrorLinear h
  rw [directionValue_linear,directionValue_linear] at hp
  have hd := congrArg (fun x => (triangleExponent x).toAdd) h
  rw [directionValue_degree,directionValue_degree] at hd
  rw [hp,hd]

lemma TargetTriangle.difference (c : TargetTriangle) (s t : Fin 3) (h : s ≠ t) :
    (c.vertex s)⁻¹ * c.vertex t = directionValue (c.direction s t) := by
  have hr := triangular_relation c.block c.rel
  unfold TargetTriangle.direction
  fin_cases s <;> fin_cases t <;> try contradiction
  all_goals simp [TargetTriangle.vertex,cellDirection,Fin.ext_iff]
  all_goals rw [← hr]
  all_goals group

end ArtinCAT0

namespace ArtinCAT0.TriangleMesh

variable {F V : Type*} (M : TriangleMesh F V)

/-- Group-vertex labels determine the labelled directions: the nine positive
letters and their inverses are distinct in the actual triangle Artin group. -/
noncomputable def SimplicialLabeling.ofVertices (v : V → TriangleGroup)
    (h : ∀ f : F, ∃ c : TargetTriangle, ∀ i : Fin 3, ∃ j, c.vertex j = v (M.tail (f,i))) :
    M.SimplicialLabeling := by
  classical
  choose c k hk using h
  have hv (f : F) (i : Fin 3) : v (M.tail (f,i)) = (c f).vertex (k f i) := (hk f i).symm
  have he (f : F) (i j : Fin 3) :
      k f i ≠ k f j ↔ v (M.tail (f,i)) ≠ v (M.tail (f,j)) := by
    rw [hv,hv]
    exact not_congr (c f).vertex_injective.eq_iff.symm
  refine ⟨c,k,v,fun d => hv d.1 d.2,?_,?_⟩
  · intro d
    rw [he,he]
    change v (M.tail (M.mate d)) ≠ v (M.tail (rotate (M.mate d))) ↔ _
    rw [M.tail_mate,M.tail_rotate_mate]
    exact ne_comm
  · intro d hd
    have hm : k (M.mate d).1 (M.mate d).2 ≠ k (M.mate d).1 ((M.mate d).2+1) := by
      rw [he]
      change v (M.tail (M.mate d)) ≠ v (M.tail (rotate (M.mate d)))
      rw [M.tail_mate,M.tail_rotate_mate]
      exact ((he d.1 d.2 (d.2+1)).1 hd).symm
    change (c (M.mate d).1).direction _ _ = reverseDirection ((c d.1).direction _ _)
    rw [show reverseDirection ((c d.1).direction (k d.1 d.2) (k d.1 (d.2+1))) =
      (c d.1).direction (k d.1 (d.2+1)) (k d.1 d.2) from
      (cellDirection_reverse _ _ _ _ hd).symm]
    apply directionValue_injective
    rw [← TargetTriangle.difference _ _ _ hm,← TargetTriangle.difference _ _ _ hd.symm]
    rw [← hv,← hv,← hv,← hv]
    change (v (M.tail (M.mate d)))⁻¹ * v (M.tail (rotate (M.mate d))) = _
    rw [M.tail_mate,M.tail_rotate_mate]

end ArtinCAT0.TriangleMesh

namespace ArtinCAT0.WordDiagram
open Relation

def Legal (a b c : TriangleGroup) : Prop :=
  ∃ t : TargetTriangle, ∃ i j k : Fin 3, t.vertex i = a ∧ t.vertex j = b ∧ t.vertex k = c

lemma Legal.of_corners (t : TargetTriangle) (i j k : Fin 3) :
    Legal (t.vertex i) (t.vertex j) (t.vertex k) := ⟨t,i,j,k,rfl,rfl,rfl⟩

lemma Legal.constant (g : TriangleGroup) : Legal g g g := by
  refine ⟨⟨g,0,0⟩,0,0,0,?_,?_,?_⟩ <;> simp [TargetTriangle.vertex]

lemma Legal.swap (a b c : TriangleGroup) (h : Legal a b c) : Legal c b a := by
  obtain ⟨t,i,j,k,h1,h2,h3⟩ := h
  exact ⟨t,k,j,i,h3,h2,h1⟩

lemma legal_signed (g : TriangleGroup) (s : Letter) : Legal g (g*signed s) g := by
  rcases s with ⟨i,b⟩
  cases b
  · refine ⟨⟨g*(triangleGen i)⁻¹,i,0⟩,1,0,1,?_,?_,?_⟩
    all_goals simp [TargetTriangle.vertex,triangleX,signed]
  · refine ⟨⟨g,i,0⟩,0,1,0,?_,?_,?_⟩
    all_goals simp [TargetTriangle.vertex,triangleX,signed]

inductive PathStep : List TriangleGroup → List TriangleGroup → Prop
  | triangle (l r : List TriangleGroup) {a b c : TriangleGroup} (h : Legal a b c) :
      PathStep (l ++ [a,b,c] ++ r) (l ++ [a,c] ++ r)
  | stutter (l r : List TriangleGroup) (a : TriangleGroup) :
      PathStep (l ++ [a,a] ++ r) (l ++ [a] ++ r)

abbrev PathHomotopy := EqvGen PathStep

lemma pathStep_context {u v : List TriangleGroup} (h : PathStep u v) (l r : List TriangleGroup) :
    PathStep (l++u++r) (l++v++r) := by
  cases h with
  | triangle a b h => simpa only [List.append_assoc] using PathStep.triangle (l++a) (b++r) h
  | stutter a b g => simpa only [List.append_assoc] using PathStep.stutter (l++a) (b++r) g

lemma path_context {u v : List TriangleGroup} (h : PathHomotopy u v) (l r : List TriangleGroup) :
    PathHomotopy (l++u++r) (l++v++r) := by
  induction h with
  | rel a b h => exact .rel _ _ (pathStep_context h l r)
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c hab hbc ih1 ih2 => exact .trans _ _ _ ih1 ih2

def walk (g : TriangleGroup) : List Letter → List TriangleGroup
  | [] => [g]
  | s::w => g :: walk (g*signed s) w

lemma walk_ne_nil (g : TriangleGroup) (w : List Letter) : walk g w ≠ [] := by cases w <;> simp [walk]
lemma walk_head (g : TriangleGroup) (w : List Letter) : (walk g w).head (walk_ne_nil g w) = g := by
  cases w <;> rfl

lemma eval_cons (s : Letter) (w : List Letter) :
    eval (FreeMonoid.ofList (s::w)) = signed s * eval (FreeMonoid.ofList w) := by
  simp [eval]

lemma walk_append (g : TriangleGroup) (u v : List Letter) :
    walk g (u++v) = (walk g u).dropLast ++ walk (g*eval (FreeMonoid.ofList u)) v := by
  induction u generalizing g with
  | nil => simp [walk]
  | cons s u ih =>
    simp only [walk, List.dropLast_cons_of_ne_nil (walk_ne_nil _ _), List.cons_append, ih]
    simp [eval,mul_assoc]

lemma walk_concat (g : TriangleGroup) (u v : List Letter) :
    PathHomotopy (walk g (u++v)) (walk g u ++ walk (g*eval (FreeMonoid.ofList u)) v) := by
  induction u generalizing g with
  | nil =>
    cases v with
    | nil => simpa [walk] using EqvGen.symm _ _ (EqvGen.rel _ _ (PathStep.stutter [] [] g))
    | cons s v =>
      simpa [walk] using EqvGen.symm _ _ (EqvGen.rel _ _ (PathStep.stutter [] (walk (g*signed s) v) g))
  | cons s u ih =>
    simpa [walk,eval,mul_assoc] using path_context (ih (g*signed s)) [g] []

lemma braid_path (g : TriangleGroup) (i : Fin 3) :
    PathHomotopy
      [g,g*triangleGen i,g*triangleGen i*triangleGen (i+1),g*triangleGen i*triangleGen (i+1)*triangleGen i]
      [g,g*triangleGen (i+1),g*triangleGen (i+1)*triangleGen i,g*triangleGen (i+1)*triangleGen i*triangleGen (i+1)] := by
  let u := triangleGen i
  let v := triangleGen (i+1)
  have hb : g*u*v*u = g*v*u*v := by simpa [u,v,mul_assoc] using congrArg (g*·) (triangle_braid i)
  have h1 : Legal g (g*u) (g*u*v) := by
    refine ⟨⟨g,i,0⟩,0,1,2,?_,?_,?_⟩
    all_goals simp [TargetTriangle.vertex,triangleX,triangleH,u,v,mul_assoc,Fin.ext_iff]
  have h2 : Legal g (g*v) (g*u*v) := by
    refine ⟨⟨g,i,1⟩,0,1,2,?_,?_,?_⟩
    all_goals simp [TargetTriangle.vertex,triangleX,triangleH,u,v,mul_assoc,Fin.ext_iff]
  have h3 : Legal (g*v) (g*u*v) (g*v*u*v) := by
    refine ⟨⟨g*v,i,2⟩,0,1,2,?_,?_,?_⟩
    all_goals simp [TargetTriangle.vertex,triangleX,triangleH,u,v,mul_assoc,Fin.ext_iff]
  have h4 : Legal (g*v) (g*v*u) (g*v*u*v) := by
    refine ⟨⟨g*v,i,0⟩,0,1,2,?_,?_,?_⟩
    all_goals simp [TargetTriangle.vertex,triangleX,triangleH,u,v,mul_assoc,Fin.ext_iff]
  change PathHomotopy [g,g*u,g*u*v,g*u*v*u] [g,g*v,g*v*u,g*v*u*v]
  rw [hb]
  exact .trans _ _ _ (.rel _ _ (PathStep.triangle [] [g*v*u*v] h1))
    (.trans _ _ _ (.symm _ _ (.rel _ _ (PathStep.triangle [] [g*v*u*v] h2)))
      (.trans _ _ _ (.rel _ _ (PathStep.triangle [g] [] h3))
        (.symm _ _ (.rel _ _ (PathStep.triangle [g] [] h4)))))

lemma rel_path (g : TriangleGroup) {u v : Word} (h : Rel u v) :
    PathHomotopy (walk g u.toList) (walk g v.toList) := by
  cases h with
  | cancel s =>
    have hi : signed s * signed (s.1,!s.2) = 1 := by
      rcases s with ⟨i,b⟩; cases b <;> simp [signed]
    change PathHomotopy [g,g*signed s,g*signed s*signed (s.1,!s.2)] [g]
    rw [mul_assoc,hi,mul_one]
    exact .trans _ _ _ (.rel _ _ (PathStep.triangle [] [] (legal_signed g s)))
      (.rel _ _ (PathStep.stutter [] [] g))
  | braid i => simpa [walk,positive,signed,mul_assoc] using braid_path g i

lemma step_sound {u v : Word} (h : Step u v) : eval u = eval v := by
  cases h with
  | context l r h => simp only [map_mul,rel_sound h]

lemma walk_context {u v : Word} (he : eval u = eval v)
    (h : ∀ g, PathHomotopy (walk g u.toList) (walk g v.toList))
    (l r : Word) (g : TriangleGroup) :
    PathHomotopy (walk g (l*u*r).toList) (walk g (l*v*r).toList) := by
  have splitwalk (w : Word) : PathHomotopy (walk g (l*w*r).toList)
      (walk g l.toList ++ walk (g*eval l) w.toList ++ walk (g*eval l*eval w) r.toList) := by
    exact .trans _ _ _ (walk_concat g (l*w).toList r.toList)
      (by simpa [mul_assoc] using (path_context (walk_concat g l.toList w.toList) []
        (walk (g*eval l*eval w) r.toList)))
  exact .trans _ _ _ (splitwalk u) (.trans _ _ _
    (by simpa only [List.append_assoc,he] using
      path_context (h (g*eval l)) (walk g l.toList) (walk (g*eval l*eval u) r.toList))
    (.symm _ _ (splitwalk v)))

lemma step_path {u v : Word} (h : Step u v) (g : TriangleGroup) :
    PathHomotopy (walk g u.toList) (walk g v.toList) := by
  cases h with
  | context l r h => exact walk_context (rel_sound h) (fun g => rel_path g h) l r g

lemma homotopy_path {u v : Word} (h : EqvGen Step u v) (g : TriangleGroup) :
    PathHomotopy (walk g u.toList) (walk g v.toList) := by
  induction h with
  | rel a b h => exact step_path h g
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c h1 h2 ih1 ih2 => exact .trans _ _ _ ih1 ih2

/-- Every null word admits an explicit finite homotopy using only actual
triangles of the Cayley complex and repeated vertices. -/
theorem null_path (w : Word) (hw : eval w = 1) (g : TriangleGroup) :
    PathHomotopy (walk g w.toList) [g] :=
  homotopy_path (derivation_homotopy (null_derivation w hw)) g

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram
open Relation Fin.NatCast

lemma Legal.permute {a b c : TriangleGroup} (h : Legal a b c) :
    Legal b c a ∧ Legal a c b ∧ Legal a b a ∧ Legal b c b ∧ Legal a c a := by
  obtain ⟨t,i,j,k,hi,hj,hk⟩ := h
  exact ⟨⟨t,j,k,i,hj,hk,hi⟩,⟨t,i,k,j,hi,hk,hj⟩,⟨t,i,j,i,hi,hj,hi⟩,
    ⟨t,j,k,j,hj,hk,hj⟩,⟨t,i,k,i,hi,hk,hi⟩⟩

abbrev Edge (a b : TriangleGroup) := Legal a b a
lemma edge_refl (a : TriangleGroup) : Edge a a := Legal.constant a
lemma edge_symm {a b : TriangleGroup} (h : Edge a b) : Edge b a := by
  obtain ⟨t,i,j,k,hi,hj,_⟩ := h
  exact ⟨t,j,i,j,hj,hi,hj⟩
lemma edge_dup {a b : TriangleGroup} (h : Edge a b) : Legal a b b := by
  obtain ⟨t,i,j,k,hi,hj,_⟩ := h
  exact ⟨t,i,j,j,hi,hj,hj⟩

variable {N : ℕ} [NeZero N]
abbrev Row (N : ℕ) := Fin N → TriangleGroup

def RowGood (x : Row N) : Prop := ∀ i, Edge (x i) (x (i+1))
def Strip (x y : Row N) : Prop := ∀ i,
  Legal (y i) (y (i+1)) (x (i+1)) ∧ Legal (y i) (x (i+1)) (x i)

lemma strip_good {x y : Row N} (h : Strip x y) : RowGood x ∧ RowGood y := by
  constructor <;> intro i
  · exact edge_symm (h i).2.permute.2.2.2.1
  · exact (h i).1.permute.2.2.1

lemma strip_refl {x : Row N} (h : RowGood x) : Strip x x := by
  intro i
  exact ⟨edge_dup (h i), h i⟩

lemma strip_rotate (x : Row N) (h : RowGood x) : Strip x (fun i => x (i+1)) := by
  intro i
  exact ⟨h (i+1), Legal.swap _ _ _ (edge_dup (h i))⟩

lemma strip_swap_rotate {x y : Row N} (h : Strip x y) : Strip y (fun i => x (i+1)) := by
  intro i
  exact ⟨Legal.swap _ _ _ (h (i+1)).2, Legal.swap _ _ _ (h i).1⟩

lemma good_shift {x : Row N} (h : RowGood x) (k : Fin N) : RowGood (fun i => x (i+k)) := by
  intro i
  simpa only [add_right_comm] using h (i+k)

lemma reachable_rotate (x : Row N) (h : RowGood x) (k : ℕ) :
    ReflTransGen Strip x (fun i => x (i+(k : Fin N))) := by
  induction k with
  | zero => simpa using (ReflTransGen.refl : ReflTransGen Strip x x)
  | succ k ih =>
    apply ih.tail
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      strip_rotate (fun i => x (i+(k : Fin N))) (good_shift h _)

lemma strip_symmetric {x y : Row N} (h : Strip x y) : ReflTransGen Strip y x := by
  have hn : 0 < N := NeZero.pos N
  have hrot := reachable_rotate (fun i => x (i+1)) (good_shift (strip_good h).1 1) (N-1)
  have eq : (fun i : Fin N => x (i+(N-1 : ℕ)+1)) = x := by
    funext i
    congr 1
    have hc : ((N-1 : ℕ) : Fin N) + 1 = 0 := by
      calc
        _ = ((N-1+1 : ℕ) : Fin N) := by rw [Nat.cast_add, Nat.cast_one]
        _ = 0 := by rw [Nat.sub_add_cancel hn,Fin.natCast_self]
    simp only [add_assoc,hc,add_zero]
  refine (ReflTransGen.single (strip_swap_rotate h)).trans ?_
  simpa only [eq] using hrot

lemma strip_reach_reverse {x y : Row N} (h : ReflTransGen Strip x y) : ReflTransGen Strip y x := by
  induction h with
  | refl => exact .refl
  | tail h1 h2 ih => exact (strip_symmetric h2).trans ih

lemma strip_homotopy {x y : Row N} (h : EqvGen Strip x y) : ReflTransGen Strip x y := by
  induction h with
  | rel a b h => exact .single h
  | refl a => exact .refl
  | symm a b h ih => exact strip_reach_reverse ih
  | trans a b c h1 h2 ih1 ih2 => exact ih1.trans ih2

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram
open Relation Fin.NatCast

lemma getD_append_formula (l r : List TriangleGroup) (g : TriangleGroup) (n : ℕ) :
    (l++r).getD n g = if n < l.length then l.getD n g else r.getD (n-l.length) g := by
  simp only [List.getD, List.getElem?_append]
  split_ifs <;> rfl

lemma getD_delete (l r : List TriangleGroup) (a b g : TriangleGroup) (n : ℕ) :
    (l++a::r).getD n g = if n ≤ l.length then (l++a::b::r).getD n g
      else (l++a::b::r).getD (n+1) g := by
  induction l generalizing n with
  | nil => cases n <;> simp
  | cons x l ih =>
    cases n with
    | zero => simp
    | succ n =>
      simpa only [List.cons_append,List.getD_cons_succ,List.length_cons,Nat.add_le_add_iff_right] using ih n

lemma getD_stutter (l r : List TriangleGroup) (a g : TriangleGroup) (n : ℕ) :
    (l++a::r).getD n g = if n < l.length then (l++a::a::r).getD n g
      else (l++a::a::r).getD (n+1) g := by
  induction l generalizing n with
  | nil => cases n <;> simp
  | cons x l ih =>
    cases n with
    | zero => simp
    | succ n =>
      simpa only [List.cons_append,List.getD_cons_succ,List.length_cons,Nat.add_lt_add_iff_right] using ih n

def GoodPath (g : TriangleGroup) (p : List TriangleGroup) : Prop :=
  p.headD g = g ∧ List.IsChain Edge (p++[g])

lemma step_good {p q : List TriangleGroup} (h : PathStep p q) (g : TriangleGroup) :
    GoodPath g p ↔ GoodPath g q := by
  cases h with
  | @triangle l r a b c h =>
    obtain ⟨hbc,hac,hab,hbc',hac'⟩ := h.permute
    dsimp [GoodPath]
    have heads : (l++[a,b,c]++r).headD g = (l++[a,c]++r).headD g := by
      cases l <;> rfl
    rw [heads]
    simp only [List.append_assoc,List.isChain_append,List.isChain_cons_cons,
      List.head?_cons,List.cons_append,List.nil_append,Option.mem_def,hab,hbc',hac',true_and]
  | stutter l r a =>
    dsimp [GoodPath]
    have heads : (l++[a,a]++r).headD g = (l++[a]++r).headD g := by
      cases l <;> rfl
    rw [heads]
    simp only [List.append_assoc,List.isChain_append,List.isChain_cons_cons,
      List.head?_cons,List.cons_append,List.nil_append,Option.mem_def,edge_refl,true_and]

lemma goodPath_padded {g : TriangleGroup} {p : List TriangleGroup} (h : GoodPath g p) (n : ℕ) :
    Edge (p.getD n g) (p.getD (n+1) g) := by
  by_cases hn : n+1 < p.length
  · have hc := List.isChain_iff_getElem.1 h.2 n (by simp; omega)
    rw [List.getD_eq_getElem _ _ (by omega : n<p.length), List.getD_eq_getElem _ _ hn]
    simpa only [List.getElem_append_left (by omega : n < p.length),
      List.getElem_append_left hn] using hc
  · by_cases hn' : n < p.length
    · have hn'' : n+1 = p.length := by omega
      have hc := List.isChain_iff_getElem.1 h.2 n (by simp; omega)
      rw [List.getD_eq_getElem _ _ hn', List.getD_eq_default _ _ (by omega : p.length≤n+1)]
      simpa [List.getElem_append_left hn',List.getElem_append_right (by omega : p.length ≤ n+1),hn''] using hc
    · rw [List.getD_eq_default _ _ (by omega : p.length≤n),
        List.getD_eq_default _ _ (by omega : p.length≤n+1)]
      exact edge_refl g

variable {N : ℕ} [NeZero N]
def padded (g : TriangleGroup) (p : List TriangleGroup) : Row N := fun i => p.getD i.val g

lemma padded_good {g : TriangleGroup} {p : List TriangleGroup} (h : GoodPath g p)
    (hn : p.length ≤ N) : RowGood (padded g p : Row N) := by
  intro i
  have hiv : (i+1).val = (i.val+1)%N := by simp [Fin.val_add,Nat.add_mod]
  by_cases hi : i.val+1 < N
  · simpa only [padded,hiv,Nat.mod_eq_of_lt hi] using goodPath_padded h i.val
  · have he : i.val+1 = N := by omega
    have he0 : p.getD 0 g = g := by simpa only [← List.headD_eq_getD] using h.1
    simp only [padded,hiv,he,Nat.mod_self,he0]
    simpa only [List.getD_eq_default _ _ (by omega : p.length ≤ i.val+1)] using goodPath_padded h i.val

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram
open Relation Fin.NatCast

lemma triangle_strip_nat (l r : List TriangleGroup) (a b c g : TriangleGroup)
    (h : Legal a b c)
    (hp : ∀ n, Edge ((l++[a,b,c]++r).getD n g) ((l++[a,b,c]++r).getD (n+1) g)) (n : ℕ) :
    Legal ((l++[a,c]++r).getD n g) ((l++[a,c]++r).getD (n+1) g) ((l++[a,b,c]++r).getD (n+1) g) ∧
    Legal ((l++[a,c]++r).getD n g) ((l++[a,b,c]++r).getD (n+1) g) ((l++[a,b,c]++r).getD n g) := by
  simp only [List.append_assoc,List.cons_append,List.nil_append] at hp ⊢
  by_cases hn : n < l.length
  · rw [getD_delete l (c::r) a b g n, getD_delete l (c::r) a b g (n+1)]
    simp only [ite_eq_left (show n ≤ l.length by omega), ite_eq_left (show n+1 ≤ l.length by omega)]
    exact ⟨edge_dup (hp n), hp n⟩
  · by_cases he : n = l.length
    · subst n
      simpa [getD_append_formula] using And.intro h.permute.2.1 h.permute.2.2.1
    · rw [getD_delete l (c::r) a b g n, getD_delete l (c::r) a b g (n+1)]
      simp only [ite_eq_right (show ¬n ≤ l.length by omega), ite_eq_right (show ¬n+1 ≤ l.length by omega)]
      exact ⟨hp (n+1), Legal.swap _ _ _ (edge_dup (hp n))⟩

lemma stutter_strip_nat (l r : List TriangleGroup) (a g : TriangleGroup)
    (hp : ∀ n, Edge ((l++[a,a]++r).getD n g) ((l++[a,a]++r).getD (n+1) g)) (n : ℕ) :
    Legal ((l++[a]++r).getD n g) ((l++[a]++r).getD (n+1) g) ((l++[a,a]++r).getD (n+1) g) ∧
    Legal ((l++[a]++r).getD n g) ((l++[a,a]++r).getD (n+1) g) ((l++[a,a]++r).getD n g) := by
  simp only [List.append_assoc,List.cons_append,List.nil_append] at hp ⊢
  by_cases hn : n < l.length
  · rw [getD_delete l r a a g n, getD_delete l r a a g (n+1)]
    simp only [ite_eq_left (show n ≤ l.length by omega), ite_eq_left (show n+1 ≤ l.length by omega)]
    exact ⟨edge_dup (hp n), hp n⟩
  · rw [getD_stutter l r a g n, getD_stutter l r a g (n+1)]
    simp only [ite_eq_right hn, ite_eq_right (show ¬n+1 < l.length by omega)]
    exact ⟨hp (n+1), Legal.swap _ _ _ (edge_dup (hp n))⟩

variable {N : ℕ} [NeZero N]
lemma strip_padded_of_nat {g : TriangleGroup} {p q : List TriangleGroup}
    (hp : GoodPath g p) (hq : GoodPath g q) (hnp : p.length ≤ N) (hnq : q.length ≤ N)
    (h : ∀ n, Legal (q.getD n g) (q.getD (n+1) g) (p.getD (n+1) g) ∧
      Legal (q.getD n g) (p.getD (n+1) g) (p.getD n g)) :
    Strip (padded g p : Row N) (padded g q) := by
  intro i
  have hiv : (i+1).val = (i.val+1)%N := by simp [Fin.val_add,Nat.add_mod]
  by_cases hi : i.val+1 < N
  · simpa only [padded,hiv,Nat.mod_eq_of_lt hi] using h i.val
  · have he : i.val+1 = N := by omega
    have hp0 : p.getD 0 g = g := by simpa only [← List.headD_eq_getD] using hp.1
    have hq0 : q.getD 0 g = g := by simpa only [← List.headD_eq_getD] using hq.1
    simp only [padded,hiv,he,Nat.mod_self,hp0,hq0]
    simpa only [List.getD_eq_default _ _ (by omega : p.length ≤ i.val+1),
      List.getD_eq_default _ _ (by omega : q.length ≤ i.val+1)] using h i.val

lemma step_strip {g : TriangleGroup} {p q : List TriangleGroup}
    (hs : PathStep p q) (hp : GoodPath g p) (hn : p.length ≤ N) :
    Strip (padded g p : Row N) (padded g q) := by
  have hq := (step_good hs g).1 hp
  have hlen : q.length ≤ p.length := by cases hs <;> simp
  apply strip_padded_of_nat hp hq hn (by omega)
  cases hs with
  | triangle l r h => exact triangle_strip_nat l r _ _ _ g h (goodPath_padded hp)
  | stutter l r a => exact stutter_strip_nat l r a g (goodPath_padded hp)

lemma homotopy_good {p q : List TriangleGroup} (h : PathHomotopy p q) (g : TriangleGroup) :
    GoodPath g p ↔ GoodPath g q := by
  induction h with
  | rel a b h => exact step_good h g
  | refl a => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h1 h2 ih1 ih2 => exact ih1.trans ih2

/-- A legal path homotopy is realizable on every sufficiently wide cyclic grid.
All extra columns are repeated base vertices. -/
theorem path_grid {p q : List TriangleGroup} (h : PathHomotopy p q) (g : TriangleGroup) :
    ∃ B : ℕ, ∀ N : ℕ, B ≤ N → GoodPath g p →
      ReflTransGen Strip (padded g p : Row (N+1)) (padded g q) := by
  induction h with
  | rel a b h =>
    exact ⟨a.length,fun N hN hp => .single (step_strip h hp (by omega))⟩
  | refl a => exact ⟨0,fun _ _ _ => .refl⟩
  | symm a b h ih =>
    obtain ⟨B,hB⟩ := ih
    exact ⟨B,fun N hN hp => strip_reach_reverse (hB N hN ((homotopy_good h g).2 hp))⟩
  | trans a b c h1 h2 ih1 ih2 =>
    obtain ⟨B1,hB1⟩ := ih1
    obtain ⟨B2,hB2⟩ := ih2
    exact ⟨max B1 B2,fun N hN hp => (hB1 N (by omega) hp).trans
      (hB2 N (by omega) ((homotopy_good h1 g).1 hp))⟩

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram
open Relation

lemma walk_append_chain (g : TriangleGroup) (w : List Letter) :
    List.IsChain Edge (walk g w ++ [g*eval (FreeMonoid.ofList w)]) := by
  induction w generalizing g with
  | nil => simp [walk,edge_refl]
  | cons s w ih =>
    have hi := ih (g*signed s)
    have hh : (walk (g*signed s) w ++ [g*eval (FreeMonoid.ofList (s::w))]).head? = some (g*signed s) := by
      cases w <;> rfl
    rw [walk,List.cons_append,List.isChain_cons]
    constructor
    · intro y hy
      simp only [hh,Option.mem_def,Option.some.injEq] at hy
      rw [← hy]
      exact legal_signed g s
    · simpa [eval,mul_assoc] using hi

lemma walk_good (g : TriangleGroup) (w : Word) (h : eval w = 1) : GoodPath g (walk g w.toList) := by
  constructor
  · cases hw : w.toList <;> rfl
  · simpa only [FreeMonoid.ofList_toList,h,mul_one] using walk_append_chain g w.toList

variable {N : ℕ} [NeZero N]

lemma reachable_sequence {x y : Row N} (h : ReflTransGen Strip x y) (hx : RowGood x) :
    ∃ L : ℕ, ∃ f : ℕ → Row N, f 0 = x ∧ (∀ i, L ≤ i → f i = y) ∧ ∀ i, Strip (f i) (f (i+1)) := by
  induction h with
  | refl => exact ⟨0,fun _ => x,rfl,fun _ _ => rfl,fun _ => strip_refl hx⟩
  | @tail y z h hs ih =>
    obtain ⟨L,f,h0,hL,hf⟩ := ih
    let f' : ℕ → Row N := fun i => if i ≤ L then f i else z
    refine ⟨L+1,f',?_,?_,?_⟩
    · simpa [f'] using h0
    · intro i hi; simp [f',show ¬i ≤ L by omega]
    · intro i
      by_cases hi : i < L
      · simpa only [f',ite_eq_left (show i ≤ L by omega),ite_eq_left (show i+1 ≤ L by omega)] using hf i
      · by_cases he : i = L
        · subst i
          simpa only [f',ite_eq_left (le_refl _),ite_eq_right (show ¬L+1 ≤ L by omega),hL L (le_refl _)] using hs
        · simpa only [f',ite_eq_right (show ¬i ≤ L by omega),ite_eq_right (show ¬i+1 ≤ L by omega)] using
            strip_refl (strip_good hs).2

lemma Legal.target {a b c : TriangleGroup} (h : Legal a b c) (v : Fin 3 → TriangleGroup)
    (h0 : v 0 = a) (h1 : v 1 = b) (h2 : v 2 = c) :
    ∃ t : TargetTriangle, ∀ i, ∃ j, t.vertex j = v i := by
  obtain ⟨t,i,j,k,hi,hj,hk⟩ := h
  refine ⟨t,?_⟩
  intro s
  fin_cases s
  · exact ⟨i,hi.trans h0.symm⟩
  · exact ⟨j,hj.trans h1.symm⟩
  · exact ⟨k,hk.trans h2.symm⟩

noncomputable def gridLabels (H : ℕ) (g : TriangleGroup) (f : ℕ → Row N) : GridDisk.Vertex H N → TriangleGroup
  | Sum.inl (r,i) => f r.val i
  | Sum.inr _ => g

lemma gridLabels_legal (H : ℕ) (g : TriangleGroup) (f : ℕ → Row N)
    (h0 : f 0 = fun _ => g) (hf : ∀ i, Strip (f i) (f (i+1))) :
    ∀ a : GridDisk.Face H N, ∃ t : TargetTriangle, ∀ k, ∃ j,
      t.vertex j = gridLabels H g f ((GridDisk.patch H N).tail (a,k)) := by
  intro a
  rcases a with ⟨r,i,b⟩ | i
  · cases b
    · apply ((hf r.val i).1).target
      all_goals simp [gridLabels,GridDisk.patch,GridDisk.tail]
    · apply ((hf r.val i).2).target
      all_goals simp [gridLabels,GridDisk.patch,GridDisk.tail]
  · apply (Legal.constant g).target
    all_goals simp [gridLabels,GridDisk.patch,GridDisk.tail,h0]

/-- Every null original-generator loop has legal grid fillings of all
sufficiently large widths. The entire disk is actual labelled triangles. -/
theorem null_grid (g : TriangleGroup) (w : Word) (hw : eval w = 1) :
    ∃ B : ℕ, ∀ N : ℕ, B ≤ N → ∃ H : ℕ, ∃ v : GridDisk.Vertex H (N+1) → TriangleGroup,
      (∀ i, v (Sum.inl (Fin.last (H+1),i)) = (walk g w.toList).getD i.val g) ∧
      (∀ a : GridDisk.Face H (N+1), ∃ t : TargetTriangle, ∀ k, ∃ j,
        t.vertex j = v ((GridDisk.patch H (N+1)).tail (a,k))) := by
  obtain ⟨B,hB⟩ := path_grid (null_path w hw g) g
  refine ⟨B,fun N hN => ?_⟩
  have hc : (padded g [g] : Row (N+1)) = fun _ => g := by
    funext i
    by_cases hi : i.val = 0
    · simp [padded,hi]
    · rw [padded,List.getD_eq_default _ _ (by simp; omega)]
  have hg : RowGood (fun _ : Fin (N+1) => g) := fun _ => edge_refl g
  have hs := strip_reach_reverse (hB N hN (walk_good g w hw))
  rw [hc] at hs
  obtain ⟨L,f,h0,hL,hf⟩ := reachable_sequence hs hg
  refine ⟨L,gridLabels L g f,?_,gridLabels_legal L g f h0 hf⟩
  intro i
  change f (L+1) i = _
  rw [hL (L+1) (by omega)]
  rfl

end ArtinCAT0.WordDiagram

namespace ArtinCAT0
section CommutingOrbit
variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]
  [ProperSpace X] [Nonempty X]

/-- A common minimizing point for two commuting elements, obtained by applying
semisimplicity inside the first minimum set. No flat-torus theorem is assumed. -/
lemma commuting_minimizer (hG : GeometricAction G X) (y : X) {g h : G}
    (hc : Commute g h) : ∃ x : X,
      dist x (g • x) = stableLengthAt y g ∧ dist x (h • x) = stableLengthAt y h := by
  classical
  let A := stableLengthAt y g
  let q : Unit → G := fun _ => g
  obtain ⟨z,hz⟩ := exists_displacement_minimizer hG g
  have hzA : dist z (g • z) = A := by
    rw [← stableLength_minimizer hG.1 hG.2.1 g hz]
    exact stableLength_basepoint hG.2.1 z y g
  let C := displacementSublevel (X := X) q A
  have hA : 0 ≤ A := stableLength_nonneg hG.2.1 y g
  let : Nonempty C := ⟨⟨z,fun _ => hzA.le⟩⟩
  let : ProperSpace C := sublevel_properSpace hG.2.1 q A
  let := sublevelAction hG.2.1 q A
  have hCG := geometric_tupleCentralizer hG q A hA
  let h' : tupleCentralizer q := ⟨h,fun _ => hc.symm⟩
  obtain ⟨x,hx⟩ := exists_displacement_minimizer hCG h'
  have hlen := stableLength_minimizer hCG.1 hCG.2.1 h' hx
  refine ⟨x.val,le_antisymm (x.property ()) ?_,?_⟩
  · rw [← stableLength_basepoint hG.2.1 x.val y g]
    exact stableLength_le_displacement hG.2.1 x.val g
  · change dist x (h' • x) = _
    rw [← hlen,sublevelAction_stableLength hG.2.1 q A x h']
    exact stableLength_basepoint hG.2.1 x.val y h

omit [ProperSpace X] [Nonempty X] in
lemma minimizer_of_length_eq (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x y : X) (g : G) (hx : dist x (g • x) = stableLengthAt y g) :
    ∀ z : X, dist x (g • x) ≤ dist z (g • z) := by
  intro z
  rw [hx,← stableLength_basepoint hi z y g]
  exact stableLength_le_displacement hi z g

omit [ProperSpace X] [Nonempty X] in
lemma minimizer_zpow (hG : GeometricAction G X) (x : X) (g : G)
    (hx : ∀ z : X, dist x (g • x) ≤ dist z (g • z)) (i : ℤ) :
    dist x ((g^i) • x) = stableLengthAt x (g^i) := by
  cases i with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast,zpow_natCast,stableLength_pow hG.2.1,
      stableLength_minimizer hG.1 hG.2.1 g hx]
    exact minimizer_displacement_pow hG.1 hG.2.1 g hx n
  | negSucc n =>
    rw [zpow_negSucc,displacement_inv hG.2.1,stableLength_inv hG.2.1,
      stableLength_pow hG.2.1,stableLength_minimizer hG.1 hG.2.1 g hx]
    exact minimizer_displacement_pow hG.1 hG.2.1 g hx (n+1)

omit [ProperSpace X] [Nonempty X] in
lemma commuting_minimizer_product (hG : GeometricAction G X) (x : X) {g h : G}
    (hc : Commute g h)
    (hg : dist x (g • x) = stableLengthAt x g)
    (hh : dist x (h • x) = stableLengthAt x h) :
    dist x ((g*h) • x) = stableLengthAt x (g*h) := by
  have hq := commuting_displacement_quadrilateral hG.1 hG.2.1 x hc
  have hl := length_parallelogram hG.1 hG.2.1 x hc
  have ha := stableLength_le_displacement hG.2.1 x (g*h)
  have hb := stableLength_le_displacement hG.2.1 x (g*h⁻¹)
  have hn := stableLength_nonneg hG.2.1 x (g*h)
  have hm := stableLength_nonneg hG.2.1 x (g*h⁻¹)
  rw [hg,hh] at hq
  nlinarith [dist_nonneg (x := x) (y := (g*h) • x),
    dist_nonneg (x := x) (y := (g*h⁻¹) • x)]

theorem commuting_orbit_uniform (hG : GeometricAction G X) (y : X) {g h : G}
    (hc : Commute g h) : ∃ C : ℝ, 0 ≤ C ∧ ∀ i j : ℤ,
      |dist y ((g^i*h^j) • y) - stableLengthAt y (g^i*h^j)| ≤ C := by
  obtain ⟨x,hg,hh⟩ := commuting_minimizer hG y hc
  have hgm := minimizer_of_length_eq hG.2.1 x y g hg
  have hhm := minimizer_of_length_eq hG.2.1 x y h hh
  refine ⟨2*dist y x,by positivity,fun i j => ?_⟩
  have he := commuting_minimizer_product hG x (hc.zpow_zpow i j)
    (minimizer_zpow hG x g hgm i) (minimizer_zpow hG x h hhm j)
  rw [← stableLength_basepoint hG.2.1 x y (g^i*h^j),← he]
  have h1 := displacement_change_base hG.2.1 y x (g^i*h^j)
  have h2 := displacement_change_base hG.2.1 x y (g^i*h^j)
  rw [dist_comm x y] at h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end CommutingOrbit
end ArtinCAT0

namespace ArtinCAT0.WordDiagram
open Relation

lemma step_length {p q : List TriangleGroup} (h : PathStep p q) : q.length ≤ p.length := by
  cases h <;> simp

lemma deletions_length {p q : List TriangleGroup} (h : ReflTransGen PathStep p q) : q.length ≤ p.length := by
  induction h with
  | refl => rfl
  | tail h1 h2 ih => exact (step_length h2).trans ih

lemma deletions_homotopy {p q : List TriangleGroup} (h : ReflTransGen PathStep p q) : PathHomotopy p q := by
  induction h with
  | refl => exact .refl _
  | tail h1 h2 ih => exact .trans _ _ _ ih (.rel _ _ h2)

lemma deletions_context {p q : List TriangleGroup} (h : ReflTransGen PathStep p q) (l r : List TriangleGroup) :
    ReflTransGen PathStep (l++p++r) (l++q++r) := by
  induction h with
  | refl => exact .refl
  | tail h1 h2 ih => exact ih.tail (pathStep_context h2 l r)

variable {N : ℕ} [NeZero N]
lemma deletions_grid {g : TriangleGroup} {p q : List TriangleGroup}
    (h : ReflTransGen PathStep p q) (hp : GoodPath g p) (hn : p.length ≤ N) :
    ReflTransGen Strip (padded g p : Row N) (padded g q) := by
  induction h with
  | refl => exact .refl
  | tail h1 h2 ih =>
    exact ih.tail (step_strip h2 ((homotopy_good (deletions_homotopy h1) g).1 hp)
      ((deletions_length h1).trans hn))

lemma fill_row (g : TriangleGroup) (x : Row N)
    (h : ReflTransGen Strip x (fun _ => g)) :
    ∃ H : ℕ, ∃ v : GridDisk.Vertex H N → TriangleGroup,
      (∀ i, v (Sum.inl (Fin.last (H+1),i)) = x i) ∧
      (∀ a : GridDisk.Face H N, ∃ t : TargetTriangle, ∀ k, ∃ j,
        t.vertex j = v ((GridDisk.patch H N).tail (a,k))) := by
  have hg : RowGood (fun _ : Fin N => g) := fun _ => edge_refl g
  obtain ⟨L,f,h0,hL,hf⟩ := reachable_sequence (strip_reach_reverse h) hg
  refine ⟨L,gridLabels L g f,?_,gridLabels_legal L g f h0 hf⟩
  intro i
  change f (L+1) i = _
  rw [hL (L+1) (by omega)]

omit [NeZero N] in
lemma pad_singleton (g : TriangleGroup) : (padded g [g] : Row N) = fun _ => g := by
  funext i
  by_cases hi : i.val = 0
  · simp [padded,hi]
  · rw [padded,List.getD_eq_default _ _ (by simp; omega)]

/-- Padding a boundary by repeated vertices does not demand additional
uncontrolled width: the deletions themselves realize its prescribed boundary. -/
theorem refined_grid (g : TriangleGroup) (w : Word) (hw : eval w = 1) :
    ∃ B : ℕ, ∀ N : ℕ, B ≤ N → ∀ p : List TriangleGroup,
      ReflTransGen PathStep p (walk g w.toList) → p.length ≤ N+1 →
      ∃ H : ℕ, ∃ v : GridDisk.Vertex H (N+1) → TriangleGroup,
      (∀ i, v (Sum.inl (Fin.last (H+1),i)) = p.getD i.val g) ∧
      (∀ a : GridDisk.Face H (N+1), ∃ t : TargetTriangle, ∀ k, ∃ j,
        t.vertex j = v ((GridDisk.patch H (N+1)).tail (a,k))) := by
  obtain ⟨B,hB⟩ := path_grid (null_path w hw g) g
  refine ⟨B,fun N hN p hp hlen => ?_⟩
  have hg := walk_good g w hw
  have hpGood := (homotopy_good (deletions_homotopy hp) g).2 hg
  have hs := (deletions_grid hp hpGood hlen).trans (hB N hN hg)
  rw [pad_singleton] at hs
  exact fill_row g (padded g p) hs

lemma walk_join (g : TriangleGroup) (u v : List Letter) :
    ReflTransGen PathStep (walk g u ++ walk (g*eval (FreeMonoid.ofList u)) v) (walk g (u++v)) := by
  induction u generalizing g with
  | nil =>
    cases v with
    | nil => simpa [walk] using ReflTransGen.single (PathStep.stutter [] [] g)
    | cons s v =>
      simpa [walk] using ReflTransGen.single (PathStep.stutter [] (walk (g*signed s) v) g)
  | cons s u ih =>
    simpa [walk,eval,mul_assoc] using deletions_context (ih (g*signed s)) [g] []

lemma repeat_contract (g : TriangleGroup) (k : ℕ) :
    ReflTransGen PathStep (List.replicate (k+1) g) [g] := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
    apply ReflTransGen.trans _ ih
    simpa only [List.replicate_succ,List.nil_append,List.cons_append] using
      ReflTransGen.single (PathStep.stutter [] (List.replicate k g) g)

lemma walk_pad_contract (g : TriangleGroup) (w : List Letter) (k : ℕ) :
    ReflTransGen PathStep (walk g w ++ List.replicate k (g*eval (FreeMonoid.ofList w))) (walk g w) := by
  induction w generalizing g with
  | nil => simpa [walk,List.replicate_succ] using repeat_contract g k
  | cons s w ih =>
    simpa [walk,eval,mul_assoc] using deletions_context (ih (g*signed s)) [g] []

def sidePath (g : TriangleGroup) (w : Word) (K : ℕ) : List TriangleGroup :=
  walk g w.toList ++ List.replicate (K-(w.toList.length+1)) (g*eval w)

lemma sidePath_contract (g : TriangleGroup) (w : Word) (K : ℕ) :
    ReflTransGen PathStep (sidePath g w K) (walk g w.toList) :=
  walk_pad_contract g w.toList (K-(w.toList.length+1))

lemma walk_length (g : TriangleGroup) (w : List Letter) : (walk g w).length = w.length+1 := by
  induction w generalizing g with
  | nil => rfl
  | cons s w ih => simp [walk,ih]

lemma sidePath_length (g : TriangleGroup) (w : Word) (K : ℕ) (h : w.toList.length+1 ≤ K) :
    (sidePath g w K).length = K := by
  simp only [sidePath,List.length_append,List.length_replicate,walk_length]
  omega

def triangleBoundary (g : TriangleGroup) (u v w : Word) (K : ℕ) : List TriangleGroup :=
  sidePath g u K ++ sidePath (g*eval u) v K ++ sidePath (g*eval u*eval v) w K

lemma triangleBoundary_contract (g : TriangleGroup) (u v w : Word) (K : ℕ) :
    ReflTransGen PathStep (triangleBoundary g u v w K) (walk g (u*v*w).toList) := by
  have h1 := deletions_context (sidePath_contract g u K) []
    (sidePath (g*eval u) v K ++ sidePath (g*eval u*eval v) w K)
  have h2 := deletions_context (sidePath_contract (g*eval u) v K) (walk g u.toList)
    (sidePath (g*eval u*eval v) w K)
  have h3 := deletions_context (sidePath_contract (g*eval u*eval v) w K)
    (walk g u.toList ++ walk (g*eval u) v.toList) []
  have h4 := deletions_context (walk_join g u.toList v.toList) [] (walk (g*eval u*eval v) w.toList)
  have h5 := walk_join g (u*v).toList w.toList
  have h12 := h1.trans (by simpa [List.append_assoc] using h2)
  have h123 := h12.trans (by simpa [List.append_assoc] using h3)
  have h1234 := h123.trans (by simpa [List.append_assoc] using h4)
  simpa [triangleBoundary,List.append_assoc,mul_assoc] using
    h1234.trans (by simpa [mul_assoc] using h5)

lemma triangleBoundary_length (g : TriangleGroup) (u v w : Word) (K : ℕ)
    (hu : u.toList.length+1 ≤ K) (hv : v.toList.length+1 ≤ K) (hw : w.toList.length+1 ≤ K) :
    (triangleBoundary g u v w K).length = 3*K := by
  simp only [triangleBoundary,List.length_append,sidePath_length _ _ _ hu,
    sidePath_length _ _ _ hv,sidePath_length _ _ _ hw]
  omega

lemma fill_row_tall (g : TriangleGroup) (x : Row N)
    (h : ReflTransGen Strip x (fun _ => g)) :
    ∃ L : ℕ, ∀ H : ℕ, L ≤ H → ∃ v : GridDisk.Vertex H N → TriangleGroup,
      (∀ i, v (Sum.inl (Fin.last (H+1),i)) = x i) ∧
      (∀ a : GridDisk.Face H N, ∃ t : TargetTriangle, ∀ k, ∃ j,
        t.vertex j = v ((GridDisk.patch H N).tail (a,k))) := by
  have hg : RowGood (fun _ : Fin N => g) := fun _ => edge_refl g
  obtain ⟨L,f,h0,hL,hf⟩ := reachable_sequence (strip_reach_reverse h) hg
  refine ⟨L,fun H hH => ⟨gridLabels H g f,?_,gridLabels_legal H g f h0 hf⟩⟩
  intro i
  change f (H+1) i = _
  rw [hL (H+1) (by omega)]

lemma PathStep.reverse {p q : List TriangleGroup} (h : PathStep p q) :
    PathStep p.reverse q.reverse := by
  cases h with
  | triangle l r h =>
    simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.append_assoc,
      List.nil_append,List.cons_append] using PathStep.triangle r.reverse l.reverse (Legal.swap _ _ _ h)
  | stutter l r g =>
    simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.append_assoc,
      List.nil_append,List.cons_append] using PathStep.stutter r.reverse l.reverse g

lemma deletions_reverse {p q : List TriangleGroup} (h : ReflTransGen PathStep p q) :
    ReflTransGen PathStep p.reverse q.reverse := by
  induction h with
  | refl => exact .refl
  | tail h1 h2 ih => exact ih.tail h2.reverse

def inverseLetter (s : Letter) : Letter := (s.1,!s.2)
def inverseLetters (l : List Letter) : List Letter := l.reverse.map inverseLetter

@[simp] lemma signed_inverseLetter (s : Letter) : signed (inverseLetter s) = (signed s)⁻¹ := by
  rcases s with ⟨i,b⟩
  cases b <;> simp [signed,inverseLetter]

@[simp] lemma inverseLetters_cons (s : Letter) (l : List Letter) :
    inverseLetters (s::l) = inverseLetters l ++ [inverseLetter s] := by
  simp [inverseLetters]

@[simp] lemma eval_inverseLetters (l : List Letter) :
    eval (FreeMonoid.ofList (inverseLetters l)) = (eval (FreeMonoid.ofList l))⁻¹ := by
  induction l with
  | nil => simp [inverseLetters,eval]
  | cons s l ih =>
    rw [inverseLetters_cons,FreeMonoid.ofList_append,map_mul,ih,eval_cons]
    simp [eval]

lemma walk_last_append (g : TriangleGroup) (l : List Letter) :
    (walk g l).dropLast ++ [g*eval (FreeMonoid.ofList l)] = walk g l := by
  simpa [walk] using (walk_append g l []).symm

lemma walk_append_one (g : TriangleGroup) (l : List Letter) (s : Letter) :
    walk g (l++[s]) = walk g l ++ [g*eval (FreeMonoid.ofList l)*signed s] := by
  rw [walk_append]
  change (walk g l).dropLast ++ ([g*eval (FreeMonoid.ofList l)] ++
      [g*eval (FreeMonoid.ofList l)*signed s]) = _
  rw [← List.append_assoc,walk_last_append]

lemma walk_reverse (g : TriangleGroup) (l : List Letter) :
    (walk g l).reverse = walk (g*eval (FreeMonoid.ofList l)) (inverseLetters l) := by
  induction l generalizing g with
  | nil => simp [walk,inverseLetters]
  | cons s l ih =>
    simp only [walk,List.reverse_cons,ih,inverseLetters_cons,walk_append_one,eval_cons]
    congr 1
    · rw [mul_assoc]
    · simp only [eval_inverseLetters,signed_inverseLetter]
      congr 1
      group

lemma repeat_pre_contract (g : TriangleGroup) (w : List Letter) (k : ℕ) :
    ReflTransGen PathStep (List.replicate k g ++ walk g w) (walk g w) := by
  cases w with
  | nil => simpa [walk,List.replicate_succ',List.append_assoc] using repeat_contract g k
  | cons s w =>
    have h := deletions_context (repeat_contract g k) [] (walk (g*signed s) w)
    simpa [walk,List.replicate_succ',List.append_assoc] using h

/-- Extra endpoint stutters allow either orientation to be trimmed while
retaining both endpoints. This ensures exact shared-edge parametrizations. -/
def fullSide (g : TriangleGroup) (w : Word) (K : ℕ) : List TriangleGroup :=
  [g] ++ walk g w.toList ++ List.replicate (K-(w.toList.length+1)) (g*eval w)

lemma fullSide_length (g : TriangleGroup) (w : Word) (K : ℕ)
    (h : w.toList.length+1 ≤ K) : (fullSide g w K).length = K+1 := by
  simp only [fullSide,List.length_append,List.length_replicate,walk_length,List.length_singleton]
  omega

lemma fullSide_trim_forward (g : TriangleGroup) (w : Word) (K : ℕ)
    (h : w.toList.length+2 ≤ K) :
    ReflTransGen PathStep (fullSide g w K).dropLast (walk g w.toList) := by
  have hk : K-(w.toList.length+1) = (K-(w.toList.length+2))+1 := by omega
  simp only [fullSide,hk,List.replicate_succ',← List.append_assoc,List.dropLast_concat]
  have h1 := deletions_context (repeat_pre_contract g w.toList 1) []
    (List.replicate (K-(w.toList.length+2)) (g*eval w))
  apply ReflTransGen.trans _ (walk_pad_contract g w.toList (K-(w.toList.length+2)))
  simpa using h1

lemma fullSide_trim_reverse (g : TriangleGroup) (w : Word) (K : ℕ) :
    ReflTransGen PathStep (fullSide g w K).reverse.dropLast
      (walk (g*eval w) (inverseLetters w.toList)) := by
  simp only [fullSide,List.reverse_append,List.reverse_replicate,List.reverse_singleton,
    ← List.append_assoc,List.dropLast_concat]
  rw [walk_reverse]
  simpa only [FreeMonoid.ofList_toList] using repeat_pre_contract (g*eval w) (inverseLetters w.toList) (K-(w.toList.length+1))

end ArtinCAT0.WordDiagram

end OAI
