import Mathlib
import OAI.GroupTheory.FiniteType.DuffySimplex

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
namespace DuffyTriangle
open Set Topology
open scoped unitInterval
open DuffySimplex SimplexBoundary

lemma cone_face {n : ℕ} (t : I) (i : Fin (n+2)) (s : Std n) :
    cone t (face i s) = face i.succ (cone t s) := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro coordinate
  rcases Fin.eq_self_or_eq_succAbove i.succ coordinate with rfl | ⟨k,rfl⟩
  · rw [cone_succ,face_zero,face_zero,mul_zero]
  · rw [face_succAbove]
    induction k using Fin.cases with
    | zero => rw [Fin.succ_succAbove_zero,cone_zero,cone_zero]
    | succ k => rw [Fin.succ_succAbove_succ,cone_succ,face_succAbove,cone_succ]

def edge : ∀ n, C((Fin n → I) × Std 1,Std (n+1))
  | 0 => ⟨Prod.snd,continuous_snd⟩
  | n+1 => ⟨fun z => cone (z.1 0) (edge n ((fun i => z.1 i.succ),z.2)),by
      have h : Continuous (fun z : (Fin (n+1) → I) × Std 1 =>
          (z.1 0,edge n ((fun i => z.1 i.succ),z.2))) :=
        ((continuous_apply 0).comp continuous_fst).prodMk
          ((edge n).continuous.comp ((continuous_pi (fun i =>
            (continuous_apply i.succ).comp continuous_fst)).prodMk continuous_snd))
      exact (continuous_cone (n+1)).comp h⟩

def triangle : ∀ n, C((Fin n → I) × Std 2,Std (n+2))
  | 0 => ⟨Prod.snd,continuous_snd⟩
  | n+1 => ⟨fun z => cone (z.1 0) (triangle n ((fun i => z.1 i.succ),z.2)),by
      have h : Continuous (fun z : (Fin (n+1) → I) × Std 2 =>
          (z.1 0,triangle n ((fun i => z.1 i.succ),z.2))) :=
        ((continuous_apply 0).comp continuous_fst).prodMk
          ((triangle n).continuous.comp ((continuous_pi (fun i =>
            (continuous_apply i.succ).comp continuous_fst)).prodMk continuous_snd))
      exact (continuous_cone (n+2)).comp h⟩

def lastFace : ∀ n, Fin 3 → Fin (n+3)
  | 0,i => i
  | n+1,i => (lastFace n i).succ

lemma lastFace_val : ∀ n (i : Fin 3), (lastFace n i).val = n+i.val
  | 0,i => by simp [lastFace]
  | n+1,i => by simp only [lastFace,Fin.val_succ,lastFace_val]; omega

lemma triangle_face : ∀ n (t : Fin n → I) (i : Fin 3) (s : Std 1),
    triangle n (t,face i s) = face (lastFace n i) (edge n (t,s))
  | 0,t,i,s => rfl
  | n+1,t,i,s => by
    change cone (t 0) (triangle n ((fun j => t j.succ),face i s)) =
      face (lastFace n i).succ (cone (t 0) (edge n ((fun j => t j.succ),s)))
    rw [triangle_face,cone_face]

lemma edge_cube : ∀ n (t : Fin n → I) (a : I),
    edge n (t,toSimplex 1 (fun _ => a)) = toSimplex (n+1) (Fin.snoc t a)
  | 0,t,a => rfl
  | n+1,t,a => by
    change cone (t 0) (edge n ((fun i => t i.succ),toSimplex 1 (fun _ => a))) =
      cone ((Fin.snoc t a : Fin (n+2) → I) 0) (toSimplex (n+1) (fun i => (Fin.snoc t a : Fin (n+2) → I) i.succ))
    rw [edge_cube,Fin.snoc_apply_zero]
    congr 2
    have ht : t = Fin.cons (t 0) (fun i => t i.succ) := (Fin.cons_self_tail t).symm
    rw [ht,← Fin.cons_snoc_eq_snoc_cons]
    rfl

def DoubleBoundary (n : ℕ) : Set (Std n) := {s | ∃ i j, i ≠ j ∧ s.1 i = 0 ∧ s.1 j = 0}

lemma doubleBoundary_cone {n : ℕ} (t : I) (s : Std n) (hs : s ∈ DoubleBoundary n) :
    cone t s ∈ DoubleBoundary (n+1) := by
  obtain ⟨i,j,hij,hi,hj⟩ := hs
  exact ⟨i.succ,j.succ,fun h => hij (Fin.succ_inj.mp h),by simp [hi],by simp [hj]⟩

lemma doubleBoundary_cone_one {n : ℕ} (s : Std (n+1)) : cone 1 s ∈ DoubleBoundary (n+2) := by
  refine ⟨(0 : Fin (n+2)).succ,(1 : Fin (n+2)).succ,?_,?_,?_⟩
  · intro h
    have hh := Fin.succ_inj.mp h
    have hh' := congrArg Fin.val hh
    simp only [Fin.val_zero,Fin.val_one] at hh'
    omega
  · rw [cone_succ]; simp
  · rw [cone_succ]; simp

universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

lemma triangle_boundary : ∀ n (F : C(Std (n+2),X))
    (_ : ∀ s ∈ DoubleBoundary (n+2), F s = x)
    (_ : ∀ i : Fin (n+3), i.val < n → F.comp (face i) = ContinuousMap.const _ x)
    (t : Fin n → I), t ∈ Cube.boundary (Fin n) → ∀ s, F (triangle n (t,s)) = x
  | 0,F,h₂,he,t,ht,s => by obtain ⟨i,_⟩ := ht; exact Fin.elim0 i
  | n+1,F,h₂,he,t,ht,s => by
    obtain ⟨i,hi⟩ := ht
    induction i using Fin.cases with
    | zero =>
      rcases hi with hi | hi
      · change F (cone (t 0) (triangle n ((fun j => t j.succ),s))) = x
        have hz : (cone (t 0) (triangle n ((fun j => t j.succ),s))).1 0 = 0 := by simp [hi]
        rw [← face_drop 0 _ hz]
        exact DFunLike.congr_fun (he 0 (by simp)) _
      · change F (cone (t 0) (triangle n ((fun j => t j.succ),s))) = x
        rw [hi]
        exact h₂ _ (doubleBoundary_cone_one _)
    | succ i =>
      let G : C(Std (n+2),X) := F.comp ⟨fun s => cone (t 0) s,
        (continuous_cone (n+2)).comp (continuous_const.prodMk continuous_id)⟩
      apply triangle_boundary n G
      · intro v hv
        exact h₂ _ (doubleBoundary_cone (t 0) v hv)
      · intro j hj
        ext a
        change F (cone (t 0) (face j a)) = x
        rw [cone_face]
        exact DFunLike.congr_fun (he j.succ (by simpa only [Fin.val_succ] using Nat.succ_lt_succ hj)) _
      · exact ⟨i,hi⟩

def looped (n : ℕ) (F : C(Std (n+2),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+2), F s = x)
    (he : ∀ i : Fin (n+3), i.val < n → F.comp (face i) = ContinuousMap.const _ x) :
    C(Std 2,GenLoop (Fin n) X x) :=
  let K : C(Std 2 × (Fin n → I),X) := (F.comp (triangle n)).comp ⟨Prod.swap,continuous_swap⟩
  ⟨fun s => ⟨K.curry s,fun t ht => triangle_boundary n F h₂ he t ht s⟩,
    K.curry.continuous.subtype_mk _⟩

@[simp] lemma looped_apply (n : ℕ) (F : C(Std (n+2),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+2), F s = x)
    (he : ∀ i : Fin (n+3), i.val < n → F.comp (face i) = ContinuousMap.const _ x)
    (s : Std 2) (t : Fin n → I) : looped n F h₂ he s t = F (triangle n (t,s)) := rfl

end DuffyTriangle

namespace TrianglePath
open Set Topology DuffySimplex SimplexBoundary
open scoped unitInterval

lemma duffy_one_zero : toSimplex 1 (fun _ => (0 : I)) = Convexity.StdSimplex.single 1 := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro coordinate
  fin_cases coordinate <;> norm_num [toSimplex,cone,Finsupp.single_apply]

lemma duffy_one_one : toSimplex 1 (fun _ => (1 : I)) = Convexity.StdSimplex.single 0 := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro coordinate
  fin_cases coordinate <;> norm_num [toSimplex,cone,Finsupp.single_apply]

lemma face_vertex {n : ℕ} (i : Fin (n+2)) (j : Fin (n+1)) :
    face i (Convexity.StdSimplex.single j) = Convexity.StdSimplex.single (i.succAbove j) :=
  Convexity.StdSimplex.map_single _ _

def edgePath (i : Fin 3) :
    Path (Convexity.StdSimplex.single (i.succAbove 1) : Std 2)
      (Convexity.StdSimplex.single (i.succAbove 0)) where
  toFun a := face i (toSimplex 1 (fun _ => a))
  continuous_toFun := (face i).continuous.comp ((toSimplex 1).continuous.comp
    (continuous_pi (fun _ => continuous_id)))
  source' := by rw [duffy_one_zero,face_vertex]
  target' := by rw [duffy_one_one,face_vertex]

lemma edgePath_add : ((edgePath 0).trans (edgePath 2)).Homotopic (edgePath 1) := by
  let : ContractibleSpace (closedBall (0 : Fin 2 → ℝ) 1) :=
    (convex_closedBall (0 : Fin 2 → ℝ) 1).contractibleSpace ⟨0,by simp⟩
  let : ContractibleSpace (Std 2) := (SimplexDisk.diskEquiv 2).contractibleSpace
  exact SimplyConnectedSpace.paths_homotopic _ _

universe u
variable {Y : Type u} [TopologicalSpace Y] {y : Y}

def mappedEdge (F : C(Std 2,Y)) (hF : ∀ i : Fin 3, F (Convexity.StdSimplex.single i) = y)
    (i : Fin 3) : Path y y where
  toFun a := F (edgePath i a)
  continuous_toFun := F.continuous.comp (edgePath i).continuous
  source' := (congrArg F (edgePath i).source).trans (hF _)
  target' := (congrArg F (edgePath i).target).trans (hF _)

lemma mappedEdge_add (F : C(Std 2,Y)) (hF : ∀ i : Fin 3, F (Convexity.StdSimplex.single i) = y) :
    ((mappedEdge F hF 0).trans (mappedEdge F hF 2)).Homotopic (mappedEdge F hF 1) := by
  obtain ⟨H⟩ := edgePath_add.map F
  refine ⟨{
    toHomotopy := {
      toContinuousMap := H.toContinuousMap
      map_zero_left := ?_
      map_one_left := ?_ }
    prop' := ?_ }⟩
  · intro a
    exact (H.apply_zero a).trans (congrArg (fun p => p a)
      (Path.map_trans (edgePath 0) (edgePath 2) F.continuous))
  · intro a
    exact H.apply_one a
  · intro t a ha
    exact (H.eq_fst t ha).trans (congrArg (fun p => p a)
      (Path.map_trans (edgePath 0) (edgePath 2) F.continuous))

end TrianglePath

namespace DuffyTriangle
open Set Topology DuffySimplex SimplexBoundary
open scoped unitInterval

lemma triangle_doubleBoundary : ∀ n (t : Fin n → I) (s : Std 2),
    s ∈ DoubleBoundary 2 → triangle n (t,s) ∈ DoubleBoundary (n+2)
  | 0,_,_,hs => hs
  | n+1,_,_,hs => doubleBoundary_cone _ _ (triangle_doubleBoundary n _ _ hs)

lemma vertex_doubleBoundary (i : Fin 3) : Convexity.StdSimplex.single (R := ℝ) i ∈ DoubleBoundary 2 := by
  fin_cases i
  · exact ⟨1,2,by decide,by simp,by simp⟩
  · exact ⟨0,2,by decide,by simp,by simp⟩
  · exact ⟨0,1,by decide,by simp,by simp⟩

universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

lemma looped_vertex (n : ℕ) (F : C(Std (n+2),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+2), F s = x)
    (he : ∀ i : Fin (n+3), i.val < n → F.comp (face i) = ContinuousMap.const _ x)
    (i : Fin 3) : looped n F h₂ he (Convexity.StdSimplex.single i) = GenLoop.const := by
  ext t
  exact h₂ _ (triangle_doubleBoundary n t _ (vertex_doubleBoundary i))

end DuffyTriangle

end

end OAI
