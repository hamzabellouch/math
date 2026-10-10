import Mathlib
import OAI.GroupTheory.FiniteType.DuffyTriangle

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
namespace LoopPath
open Set Topology
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

def fromPath (P : Path (GenLoop.const : GenLoop (Fin n) X x) GenLoop.const) :
    GenLoop (Fin (n+1)) X x :=
  ⟨⟨fun t => P (t (Fin.last n)) (Fin.init t), by
    exact ((continuous_subtype_val.comp P.continuous).comp (continuous_apply (Fin.last n))).eval
      (continuous_pi (fun i : Fin n => continuous_apply i.castSucc))⟩,by
    rintro t ⟨i,hi⟩
    change P (t (Fin.last n)) (Fin.init t) = x
    induction i using Fin.lastCases with
    | last =>
      rcases hi with hi | hi
      · rw [hi,P.source]; rfl
      · rw [hi,P.target]; rfl
    | cast i => exact (P (t (Fin.last n))).2 _ ⟨i,hi⟩⟩

@[simp] lemma fromPath_apply (P : Path (GenLoop.const : GenLoop (Fin n) X x) GenLoop.const)
    (t : Fin (n+1) → I) : fromPath P t = P (t (Fin.last n)) (Fin.init t) := rfl

lemma fromPath_trans (P Q : Path (GenLoop.const : GenLoop (Fin n) X x) GenLoop.const) :
    fromPath (P.trans Q) = GenLoop.transAt (Fin.last n) (fromPath P) (fromPath Q) := by
  ext t
  simp only [fromPath_apply,Path.trans_apply,GenLoop.transAt,GenLoop.coe_copy,
    Function.update_self]
  split_ifs with h
  · congr 1
    · rw [Set.projIcc_of_mem _ (show 2*(t (Fin.last n):ℝ) ∈ Set.Icc 0 1 from
        ⟨by linarith [(t (Fin.last n)).2.1],by linarith⟩)]
    · funext i
      simp [Fin.init]
  · congr 1
    · rw [Set.projIcc_of_mem _ (show 2*(t (Fin.last n):ℝ)-1 ∈ Set.Icc 0 1 from
        ⟨by linarith,by linarith [(t (Fin.last n)).2.2]⟩)]
    · funext i
      simp [Fin.init]

def fromHomotopy {P Q : Path (GenLoop.const : GenLoop (Fin n) X x) GenLoop.const}
    (H : P.Homotopy Q) : (fromPath P).1.HomotopyRel (fromPath Q).1 (Cube.boundary (Fin (n+1))) where
  toHomotopy :=
  { toFun z := H (z.1,z.2 (Fin.last n)) (Fin.init z.2)
    continuous_toFun := ((continuous_subtype_val.comp H.continuous).comp
      (continuous_fst.prodMk ((continuous_apply (Fin.last n)).comp continuous_snd))).eval
        (continuous_pi (fun i : Fin n => (continuous_apply i.castSucc).comp continuous_snd))
    map_zero_left := fun t => congrArg (fun p : GenLoop (Fin n) X x => p (Fin.init t))
      (H.apply_zero (t (Fin.last n)))
    map_one_left := fun t => congrArg (fun p : GenLoop (Fin n) X x => p (Fin.init t))
      (H.apply_one (t (Fin.last n))) }
  prop' := by
    rintro a t ⟨i,hi⟩
    rw [(fromPath P).2 t ⟨i,hi⟩]
    induction i using Fin.lastCases with
    | last =>
      rcases hi with hi | hi
      · change H (a,t (Fin.last n)) (Fin.init t) = x
        rw [hi,H.source]; rfl
      · change H (a,t (Fin.last n)) (Fin.init t) = x
        rw [hi,H.target]; rfl
    | cast i => exact (H (a,t (Fin.last n))).2 _ ⟨i,hi⟩

end LoopPath

namespace SimplexAddition
open Set Topology DuffySimplex SimplexBoundary DuffyTriangle
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

def basedFace (F : C(Std (n+2),X)) (h₂ : ∀ s ∈ DoubleBoundary (n+2), F s = x)
    (i : Fin (n+3)) : BasedSimplex.Space (n+1) X x :=
  ⟨F.comp (face i),by
    rintro s ⟨j,hj⟩
    apply h₂
    refine ⟨i,i.succAbove j,?_,face_zero i s,?_⟩
    · exact (Fin.succAbove_ne i j).symm
    · exact (face_succAbove i s j).trans hj⟩

lemma loop_face (F : C(Std (n+2),X)) (h₂ : ∀ s ∈ DoubleBoundary (n+2), F s = x)
    (he : ∀ i : Fin (n+3), i.val < n → F.comp (face i) = ContinuousMap.const _ x)
    (i : Fin 3) : DuffyBased.loop (basedFace F h₂ (lastFace n i)) =
      LoopPath.fromPath (TrianglePath.mappedEdge (looped n F h₂ he) (looped_vertex n F h₂ he) i) := by
  ext t
  change F (face (lastFace n i) (toSimplex (n+1) t)) =
    F (triangle n (Fin.init t,face i (toSimplex 1 (fun _ => t (Fin.last n)))))
  rw [triangle_face,edge_cube,Fin.snoc_init_self]

theorem three_face (F : C(Std (n+2),X)) (h₂ : ∀ s ∈ DoubleBoundary (n+2), F s = x)
    (he : ∀ i : Fin (n+3), i.val < n → F.comp (face i) = ContinuousMap.const _ x) :
    DuffyBased.homotopyClass (basedFace F h₂ (lastFace n 1)) =
      DuffyBased.homotopyClass (basedFace F h₂ (lastFace n 2)) *
        DuffyBased.homotopyClass (basedFace F h₂ (lastFace n 0)) := by
  let p := DuffyBased.loop (basedFace F h₂ (lastFace n 0))
  let q := DuffyBased.loop (basedFace F h₂ (lastFace n 2))
  have hrel : GenLoop.Homotopic (DuffyBased.loop (basedFace F h₂ (lastFace n 1)))
      (GenLoop.transAt (Fin.last n) p q) := by
    obtain ⟨H⟩ := TrianglePath.mappedEdge_add (looped n F h₂ he) (looped_vertex n F h₂ he)
    dsimp only [p,q]
    rw [loop_face F h₂ he 0,loop_face F h₂ he 1,loop_face F h₂ he 2,← LoopPath.fromPath_trans]
    exact ⟨(LoopPath.fromHomotopy H).symm⟩
  exact (Quotient.sound hrel).trans
    (HomotopyGroup.mul_spec (i := Fin.last n) (p := q) (q := p)).symm

end SimplexAddition

namespace SimplexHorn
open Set Topology
open SimplexBoundary
abbrev Std (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n+1))
variable {n : ℕ}

abbrev Horn (i : Fin (n+2)) := {s : Std (n+1) // ∃ j, j ≠ i ∧ s.1 j = 0}

def minimum (i : Fin (n+2)) (s : Std (n+1)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j : Fin (n+1) => s.1 (i.succAbove j))

lemma minimum_nonneg (i : Fin (n+2)) (s : Std (n+1)) : 0 ≤ minimum i s := by
  exact Finset.le_inf' _ _ (fun coordinate _ => s.weights_nonneg (i.succAbove coordinate))

lemma minimum_le (i : Fin (n+2)) (s : Std (n+1)) (j : Fin (n+1)) :
    minimum i s ≤ s.1 (i.succAbove j) :=
  Finset.inf'_le _ (Finset.mem_univ j)

lemma minimum_attained (i : Fin (n+2)) (s : Std (n+1)) :
    ∃ j : Fin (n+1), minimum i s = s.1 (i.succAbove j) := by
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty
    (fun j : Fin (n+1) => s.1 (i.succAbove j))
  exact ⟨j,hj⟩

lemma minimum_eq_zero (i : Fin (n+2)) (s : Horn i) : minimum i s.1 = 0 := by
  obtain ⟨j,hji,hj⟩ := s.2
  obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hji
  exact le_antisymm (by simpa only [hj] using minimum_le i s.1 k) (minimum_nonneg i s.1)

lemma continuous_minimum (i : Fin (n+2)) : Continuous (minimum i) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun j _ => Convexity.StdSimplex.continuous_weights_apply ℝ (i.succAbove j))

def retract (i : Fin (n+2)) (s : Std (n+1)) : Std (n+1) where
  weights := Finsupp.equivFunOnFinite.symm (fun coordinate =>
    if coordinate = i then s.1 i + (n+1:ℕ)*minimum i s else s.1 coordinate-minimum i s)
  nonneg := by
    intro coordinate
    change 0 ≤ if coordinate = i then s.1 i + (n+1:ℕ)*minimum i s
      else s.1 coordinate-minimum i s
    split_ifs with coordinate_eq
    · exact add_nonneg (s.weights_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (minimum_nonneg i s))
    · obtain ⟨other,rfl⟩ := Fin.exists_succAbove_eq coordinate_eq
      exact sub_nonneg.mpr (minimum_le i s other)
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑ coordinate : Fin (n+2), if coordinate = i then s.1 i + (n+1:ℕ)*minimum i s
      else s.1 coordinate-minimum i s) = 1
    rw [Fin.sum_univ_succAbove _ i]
    simp only [ite_true,Fin.succAbove_ne,ite_false,Finset.sum_sub_distrib,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have total_eq := s.total_of_fintype
    rw [Fin.sum_univ_succAbove _ i] at total_eq
    convert total_eq using 1
    ring

@[simp] lemma retract_self (i : Fin (n+2)) (s : Std (n+1)) :
    (retract i s).1 i = s.1 i+(n+1:ℕ)*minimum i s := by simp [retract]

@[simp] lemma retract_succAbove (i : Fin (n+2)) (s : Std (n+1)) (j : Fin (n+1)) :
    (retract i s).1 (i.succAbove j) = s.1 (i.succAbove j)-minimum i s := by simp [retract]

lemma retract_mem (i : Fin (n+2)) (s : Std (n+1)) :
    ∃ j, j ≠ i ∧ (retract i s).1 j = 0 := by
  obtain ⟨j,hj⟩ := minimum_attained i s
  exact ⟨i.succAbove j,Fin.succAbove_ne _ _,by rw [retract_succAbove,hj,sub_self]⟩

@[simp] lemma retract_fix (i : Fin (n+2)) (s : Horn i) : retract i s.1 = s.1 := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro coordinate
  simp [retract,minimum_eq_zero i s]
  intro h
  rw [h]

lemma continuous_retract (i : Fin (n+2)) : Continuous (retract i) := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff.mpr
  apply continuous_pi
  intro j
  change Continuous (fun s : Std (n+1) =>
    if j = i then s.1 i+(n+1:ℕ)*minimum i s else s.1 j-minimum i s)
  split_ifs with h
  · exact (Convexity.StdSimplex.continuous_weights_apply ℝ i).add
      (continuous_const.mul (continuous_minimum i))
  · exact (Convexity.StdSimplex.continuous_weights_apply ℝ j).sub (continuous_minimum i)

def retraction (i : Fin (n+2)) : C(Std (n+1),Horn i) :=
  ⟨fun s => ⟨retract i s,retract_mem i s⟩,(continuous_retract i).subtype_mk _⟩

abbrev Faces (i : Fin (n+2)) := {j : Fin (n+2) // j ≠ i}

def quotient (i : Fin (n+2)) : C(Faces i × Std n,Horn i) :=
  ⟨fun z => ⟨face z.1.1 z.2,⟨z.1.1,z.1.2,face_zero _ _⟩⟩,
    (continuous_prod_of_discrete_left.mpr (fun j => (face j.1).continuous)).subtype_mk _⟩

lemma quotient_surjective (i : Fin (n+2)) : Function.Surjective (quotient i) := by
  intro s
  obtain ⟨j,hji,hj⟩ := s.2
  exact ⟨(⟨j,hji⟩,drop j s.1 hj),Subtype.ext (face_drop j s.1 hj)⟩

lemma quotient_isQuotientMap (i : Fin (n+2)) : IsQuotientMap (quotient i) :=
  IsQuotientMap.of_surjective_continuous (quotient_surjective i) (quotient i).continuous

universe u
variable {X : Type u} [TopologicalSpace X]

def glue (i : Fin (n+2)) (f : Faces i → C(Std n,X))
    (hf : ∀ (j k : Faces i) (a b : Std n), face j.1 a = face k.1 b → f j a = f k b) : C(Horn i,X) :=
  (quotient_isQuotientMap i).lift
    ⟨fun z => f z.1 z.2,continuous_prod_of_discrete_left.mpr (fun j => (f j).continuous)⟩
    (fun a b hab => hf a.1 b.1 a.2 b.2 (congrArg Subtype.val hab))

@[simp] lemma glue_face (i : Fin (n+2)) (f : Faces i → C(Std n,X))
    (hf : ∀ (j k : Faces i) (a b : Std n), face j.1 a = face k.1 b → f j a = f k b)
    (j : Faces i) (a : Std n) : glue (n := n) (X := X) i f hf (quotient (n := n) i (j,a)) = f j a :=
  DFunLike.congr_fun ((quotient_isQuotientMap i).lift_comp
    (⟨fun z => f z.1 z.2,continuous_prod_of_discrete_left.mpr (fun j => (f j).continuous)⟩ :
      C(Faces i × Std n,X))
    (fun a b hab => hf a.1 b.1 a.2 b.2 (congrArg Subtype.val hab))) (j,a)

def fill (i : Fin (n+2)) (f : Faces i → C(Std n,X))
    (hf : ∀ (j k : Faces i) (a b : Std n), face j.1 a = face k.1 b → f j a = f k b) : C(Std (n+1),X) :=
  (glue (n := n) (X := X) i f hf).comp (retraction i)

@[simp] lemma fill_face (i : Fin (n+2)) (f : Faces i → C(Std n,X))
    (hf : ∀ (j k : Faces i) (a b : Std n), face j.1 a = face k.1 b → f j a = f k b)
    (j : Faces i) : (fill (n := n) (X := X) i f hf).comp (face j.1) = f j := by
  ext a
  have h : retraction i (face j.1 a) = quotient (n := n) i (j,a) := by
    apply Subtype.ext
    exact retract_fix i (quotient (n := n) i (j,a))
  exact (congrArg (glue (n := n) (X := X) i f hf) h).trans (glue_face i f hf j a)

end SimplexHorn

end

end OAI
