import Mathlib
import OAI.Geometry.NearbyLagrangian.PhaseConjugacy
import OAI.Geometry.NearbyLagrangian.Stabilization

namespace OAI

/-! Hyperbolic and balanced coordinates for iterated transport. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport
open ContinuousLinearMap
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def hyperbolicCoordinates : (E × E) ≃L[ℝ] (E × E) where
  toFun q := (q.1+q.2,q.1-q.2)
  invFun q := ((1/2:ℝ) • (q.1+q.2),(1/2:ℝ) • (q.1-q.2))
  map_add' x y := by ext <;> dsimp <;> abel
  map_smul' c q := by ext <;> simp [smul_add,smul_sub]
  left_inv q := by ext <;> dsimp <;> module
  right_inv q := by ext <;> dsimp <;> module
  continuous_toFun := (continuous_fst.add continuous_snd).prodMk (continuous_fst.sub continuous_snd)
  continuous_invFun := ((continuous_fst.add continuous_snd).const_smul (1/2:ℝ)).prodMk
    ((continuous_fst.sub continuous_snd).const_smul (1/2:ℝ))

lemma hyperbolicCoordinates_form (q : E × E) :
    -inner ℝ (hyperbolicCoordinates q).1 (hyperbolicCoordinates q).2 =
      -‖q.1‖^2+‖q.2‖^2 := by
  change -inner ℝ (q.1+q.2) (q.1-q.2) = _
  simp only [inner_add_left,inner_sub_right,real_inner_self_eq_norm_sq,real_inner_comm q.2 q.1]
  ring

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Tubes
open ContinuousMap

def addBalanced (m d : ℕ) : C(Tube m m,Tube (m+d) (m+d)) :=
  (tubeSum m m d d).comp
    ⟨fun f => (f,standardTube d d),continuous_id.prodMk continuous_const⟩

@[simp] lemma addBalanced_apply (m d : ℕ) (a : Tube m m)
    (w : Euclidean ((m+d)+(m+d))) :
    (addBalanced m d a).val w =
      a.val (sumCoordinates m m d d w).1 +
      standardForm d d (sumCoordinates m m d d w).2 := rfl

def transportIndex (m d : ℕ) : ℕ → ℕ
  | 0 => m
  | n+1 => transportIndex m d n+d

lemma le_transportIndex (m d n : ℕ) : m ≤ transportIndex m d n := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih.trans (Nat.le_add_right _ _)

lemma transportIndex_eq (m d n : ℕ) : transportIndex m d n = m+n*d := by
  induction n with
  | zero => simp [transportIndex]
  | succ n ih => simp [transportIndex,ih,Nat.add_mul,Nat.add_assoc]

def addBalancedFor (m d : ℕ) : (n : ℕ) →
    C(Tube m m,Tube (transportIndex m d n) (transportIndex m d n))
  | 0 => ContinuousMap.id _
  | n+1 => (addBalanced (transportIndex m d n) d).comp (addBalancedFor m d n)

end NearbyLagrangian.Tubes

namespace NearbyLagrangian.Transport
open Tubes

def transportCoordinates (m d : ℕ) : (n : ℕ) →
    Euclidean (transportIndex m d n+transportIndex m d n) ≃L[ℝ]
      TransportFiber (Euclidean d) (Euclidean (m+m)) n
  | 0 => ContinuousLinearEquiv.refl ℝ _
  | n+1 => (sumCoordinates (transportIndex m d n) (transportIndex m d n) d d).trans
    ((transportCoordinates m d n).prodCongr
      ((EuclideanSpace.finAddEquivProd (n:=d) (m:=d)).trans hyperbolicCoordinates))

lemma iterReference_transportCoordinates {m d : ℕ}
    (a : Euclidean d → Tube m m) (n : ℕ) (b : Euclidean d)
    (w : Euclidean (transportIndex m d n+transportIndex m d n)) :
    iterReference (fun q => (a q.1).val q.2) n (b,transportCoordinates m d n w) =
      (addBalancedFor m d n (a b)).val w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let c := sumCoordinates (transportIndex m d n) (transportIndex m d n) d d w
    change iterReference (fun q => (a q.1).val q.2) n
      (b,transportCoordinates m d n c.1) -
      inner ℝ (hyperbolicCoordinates (EuclideanSpace.finAddEquivProd c.2)).1
        (hyperbolicCoordinates (EuclideanSpace.finAddEquivProd c.2)).2 =
      (addBalancedFor m d n (a b)).val c.1 + standardForm d d c.2
    rw [sub_eq_add_neg,hyperbolicCoordinates_form,ih]
    rfl

lemma iterReference_transportCoordinates_at {m d : ℕ}
    {g : Euclidean d × Euclidean (m+m) → ℝ} (n : ℕ) (x : Euclidean d)
    (a : Tube m m) (hg : ∀ w, g (x,w) = a.val w)
    (w : Euclidean (transportIndex m d n+transportIndex m d n)) :
    iterReference g n (x,transportCoordinates m d n w) =
      (addBalancedFor m d n a).val w := by
  induction n with
  | zero => exact hg w
  | succ n ih =>
    let c := sumCoordinates (transportIndex m d n) (transportIndex m d n) d d w
    change iterReference g n (x,transportCoordinates m d n c.1) -
      inner ℝ (hyperbolicCoordinates (EuclideanSpace.finAddEquivProd c.2)).1
        (hyperbolicCoordinates (EuclideanSpace.finAddEquivProd c.2)).2 =
      (addBalancedFor m d n a).val c.1 + standardForm d d c.2
    rw [sub_eq_add_neg,hyperbolicCoordinates_form,ih]
    rfl

end NearbyLagrangian.Transport

end

end OAI
