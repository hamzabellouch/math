import Mathlib
import OAI.Geometry.NearbyLagrangian.BalancedCoordinates

namespace OAI

/-! Balanced stabilization identities and persistence of nonzero stable classes. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes

@[simp] lemma split_fst_apply {k l : ℕ} (w : Euclidean (k+l)) (i : Fin k) :
    (EuclideanSpace.finAddEquivProd w).1 i = w (i.castAdd l) := rfl
@[simp] lemma split_snd_apply {k l : ℕ} (w : Euclidean (k+l)) (i : Fin l) :
    (EuclideanSpace.finAddEquivProd w).2 i = w (i.natAdd k) := rfl

@[simp] lemma sumCoordinates_fst_neg {k l r s : ℕ}
    (w : Euclidean ((k+r)+(l+s))) (i : Fin k) :
    (sumCoordinates k l r s w).1 (i.castAdd l) =
      w ((i.castAdd r).castAdd (l+s)) := by
  rw [← split_fst_apply (sumCoordinates k l r s w).1 i]
  change ((EuclideanSpace.finAddEquivProd (n:=k) (m:=l))
    ((EuclideanSpace.finAddEquivProd (n:=k) (m:=l)).symm _)).1 i = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

@[simp] lemma sumCoordinates_fst_pos {k l r s : ℕ}
    (w : Euclidean ((k+r)+(l+s))) (i : Fin l) :
    (sumCoordinates k l r s w).1 (i.natAdd k) =
      w ((i.castAdd s).natAdd (k+r)) := by
  rw [← split_snd_apply (sumCoordinates k l r s w).1 i]
  change ((EuclideanSpace.finAddEquivProd (n:=k) (m:=l))
    ((EuclideanSpace.finAddEquivProd (n:=k) (m:=l)).symm _)).2 i = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

@[simp] lemma sumCoordinates_snd_neg {k l r s : ℕ}
    (w : Euclidean ((k+r)+(l+s))) (i : Fin r) :
    (sumCoordinates k l r s w).2 (i.castAdd s) =
      w ((i.natAdd k).castAdd (l+s)) := by
  rw [← split_fst_apply (sumCoordinates k l r s w).2 i]
  change ((EuclideanSpace.finAddEquivProd (n:=r) (m:=s))
    ((EuclideanSpace.finAddEquivProd (n:=r) (m:=s)).symm _)).1 i = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

@[simp] lemma sumCoordinates_snd_pos {k l r s : ℕ}
    (w : Euclidean ((k+r)+(l+s))) (i : Fin s) :
    (sumCoordinates k l r s w).2 (i.natAdd r) =
      w ((i.natAdd l).natAdd (k+r)) := by
  rw [← split_snd_apply (sumCoordinates k l r s w).2 i]
  change ((EuclideanSpace.finAddEquivProd (n:=r) (m:=s))
    ((EuclideanSpace.finAddEquivProd (n:=r) (m:=s)).symm _)).2 i = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

lemma sumCoordinates_old_succ (m d : ℕ)
    (w : Euclidean ((m+(d+1))+(m+(d+1)))) :
    (sumCoordinates m m (d+1) (d+1) w).1 =
      (sumCoordinates m m d d (sumCoordinates (m+d) (m+d) 1 1 w).1).1 := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [sumCoordinates_fst_neg]
    apply congrArg (fun i => w i)
    apply Fin.ext
    simp
  · simp only [sumCoordinates_fst_pos]
    apply congrArg (fun i => w i)
    apply Fin.ext
    simp [Nat.add_assoc]

lemma sumCoordinates_quadratic_succ (m d : ℕ)
    (w : Euclidean ((m+(d+1))+(m+(d+1)))) :
    standardForm (d+1) (d+1) (sumCoordinates m m (d+1) (d+1) w).2 =
      standardForm d d
        (sumCoordinates m m d d (sumCoordinates (m+d) (m+d) 1 1 w).1).2 +
      standardForm 1 1 (sumCoordinates (m+d) (m+d) 1 1 w).2 := by
  let c := sumCoordinates m m (d+1) (d+1) w
  let z := sumCoordinates (m+d) (m+d) 1 1 w
  let u := sumCoordinates m m d d z.1
  let a := (EuclideanSpace.finAddEquivProd (n:=d+1) (m:=d+1) c.2).1
  let b := (EuclideanSpace.finAddEquivProd (n:=d+1) (m:=d+1) c.2).2
  have han : (EuclideanSpace.finAddEquivProd (n:=d) (m:=1) a).1 =
      (EuclideanSpace.finAddEquivProd (n:=d) (m:=d) u.2).1 := by
    ext i
    simp only [a,c,u,z,split_fst_apply,sumCoordinates_snd_neg,sumCoordinates_fst_neg]
    apply congrArg (fun i => w i)
    apply Fin.ext
    simp
  have hap : (EuclideanSpace.finAddEquivProd (n:=d) (m:=1) a).2 =
      (EuclideanSpace.finAddEquivProd (n:=1) (m:=1) z.2).1 := by
    ext i
    simp only [a,c,z,split_snd_apply,split_fst_apply,sumCoordinates_snd_neg]
    apply congrArg (fun i => w i)
    apply Fin.ext
    simp
  have hbn : (EuclideanSpace.finAddEquivProd (n:=d) (m:=1) b).1 =
      (EuclideanSpace.finAddEquivProd (n:=d) (m:=d) u.2).2 := by
    ext i
    simp only [b,c,u,z,split_fst_apply,split_snd_apply,sumCoordinates_snd_pos,
      sumCoordinates_fst_pos]
    apply congrArg (fun i => w i)
    apply Fin.ext
    simp [Nat.add_assoc]
  have hbp : (EuclideanSpace.finAddEquivProd (n:=d) (m:=1) b).2 =
      (EuclideanSpace.finAddEquivProd (n:=1) (m:=1) z.2).2 := by
    ext i
    simp only [b,c,z,split_snd_apply,sumCoordinates_snd_pos]
    apply congrArg (fun i => w i)
    apply Fin.ext
    simp [Nat.add_assoc]
  change -‖a‖^2+‖b‖^2 = standardForm d d u.2 + standardForm 1 1 z.2
  rw [norm_sq_split a,norm_sq_split b,han,hap,hbn,hbp]
  simp only [standardForm_apply]
  ring

lemma sumCoordinates_old_zero (m : ℕ) (w : Euclidean (m+m)) :
    (sumCoordinates m m 0 0 w).1 = w := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [sumCoordinates_fst_neg]
    apply congrArg (fun i => w i)
    apply Fin.ext
    simp
  · simp only [sumCoordinates_fst_pos]
    apply congrArg (fun i => w i)
    apply Fin.ext
    simp

theorem addBalanced_eq_stabilizeFor (m d : ℕ) : addBalanced m d = stabilizeFor m d := by
  induction d with
  | zero =>
    ext a
    apply Subtype.ext
    apply RegularHomogeneous.ext
    intro w
    rw [addBalanced_apply,sumCoordinates_old_zero]
    change a.val w + standardForm 0 0 _ = a.val w
    have hz : ∀ v : Euclidean (0+0), standardForm 0 0 v = 0 := by
      intro v
      have hv : v = 0 := by
        ext i
        exact Fin.elim0 i
      simp [hv]
    rw [hz,add_zero]
  | succ d ih =>
    ext a
    apply Subtype.ext
    apply RegularHomogeneous.ext
    intro w
    change (addBalanced m (d+1) a).val w =
      (stabilize (m+d) (stabilizeFor m d a)).val w
    rw [← ih,addBalanced_apply]
    change _ = (addBalanced m d a).val (sumCoordinates (m+d) (m+d) 1 1 w).1 +
      standardForm 1 1 (sumCoordinates (m+d) (m+d) 1 1 w).2
    rw [addBalanced_apply,sumCoordinates_old_succ,sumCoordinates_quadratic_succ]
    ring

open ContinuousMap

def tubeCast {m n : ℕ} (h : m = n) : C(Tube m m,Tube n n) := by
  subst n
  exact ContinuousMap.id _

@[simp] lemma tubeCast_rfl {m : ℕ} : tubeCast (rfl : m = m) = ContinuousMap.id _ := rfl

lemma tubeCast_stabilize {m n : ℕ} (h : m = n) (a : Tube m m) :
    tubeCast (congrArg (fun k => k+1) h) (stabilize m a) = stabilize n (tubeCast h a) := by
  subst n
  rfl

lemma stabilizeFor_comp (m r s : ℕ) :
    (tubeCast (Nat.add_assoc m r s)).comp
      ((stabilizeFor (m+r) s).comp (stabilizeFor m r)) = stabilizeFor m (r+s) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    ext a
    change tubeCast (congrArg (fun k => k+1) (Nat.add_assoc m r s))
      (stabilize ((m+r)+s) (stabilizeFor (m+r) s (stabilizeFor m r a))) =
      stabilize (m+(r+s)) (stabilizeFor m (r+s) a)
    rw [tubeCast_stabilize (Nat.add_assoc m r s)]
    exact congrArg (stabilize (m+(r+s))) (congrArg (fun g => g a) ih)

variable {B : Type*} [TopologicalSpace B]

theorem StablyNonNull.stabilize {m : ℕ} {a : C(B,Tube m m)}
    (ha : StablyNonNull a) (r : ℕ) : StablyNonNull ((stabilizeFor m r).comp a) := by
  intro s h
  obtain ⟨v,hv⟩ := h
  apply ha (r+s)
  have heq : (tubeCast (Nat.add_assoc m r s)).comp
      ((stabilizeFor (m+r) s).comp ((stabilizeFor m r).comp a)) =
      (stabilizeFor m (r+s)).comp a := by
    ext x
    exact congrArg (fun g : C(Tube m m,Tube (m+(r+s)) (m+(r+s))) => g (a x))
      (stabilizeFor_comp m r s)
  refine ⟨tubeCast (Nat.add_assoc m r s) v,?_⟩
  rw [← heq]
  exact (Homotopic.refl (tubeCast (Nat.add_assoc m r s))).comp hv

theorem kernel_finite_negative_trivial {m : ℕ} (a : C(B,Tube m m))
    (ha : StablyNonNull a) (hn : StableNegativeTrivial a) :
    ∃ r : ℕ, StablyNonNull ((stabilizeFor m r).comp a) ∧
      NegativeTrivial ((stabilizeFor m r).comp a) := by
  obtain ⟨r,hr⟩ := hn
  exact ⟨r,ha.stabilize r,hr⟩

end NearbyLagrangian.Tubes

namespace NearbyLagrangian.Tubes
open ContinuousMap
variable {B : Type*} [TopologicalSpace B]

theorem StablyNonNull.addBalanced {m : ℕ} {a : C(B,Tube m m)}
    (ha : StablyNonNull a) (d : ℕ) : StablyNonNull ((addBalanced m d).comp a) := by
  rw [addBalanced_eq_stabilizeFor]
  exact ha.stabilize d

theorem StablyNonNull.addBalancedFor {m : ℕ} {a : C(B,Tube m m)}
    (ha : StablyNonNull a) (d n : ℕ) : StablyNonNull ((addBalancedFor m d n).comp a) := by
  induction n with
  | zero => exact ha
  | succ n ih => exact ih.addBalanced d

end NearbyLagrangian.Tubes

end

end OAI
