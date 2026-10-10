import Mathlib
import OAI.Combinatorics.UniformKServer.IntegerParks

namespace OAI

                                      
section

/-! The literal one-step matching realization of joint tree rounding. The
coincident-label charge is restricted to labels occupied at both times. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset TreeAncestry
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X : Type*} [PseudoMetricSpace X]

def Realization.permute {x : Vertex n→ℤ} (R : Realization (k:=k) (S:=S) x)
    (π : Equiv.Perm (Fin k)) : Realization (k:=k) (S:=S) x where
  tuple i := R.tuple (π i)
  sum f := (Equiv.sum_comp π (fun i=>f (R.tuple i))).trans (R.sum f)
  positive i := R.positive (π i)

def commonDistance (a b : Allocation S k) (f g : Vertex n→X) (v : Vertex n) : ℝ :=
  if 0<park S a.amount v ∧ 0<park S b.amount v then dist (f v) (g v) else 0

theorem commonDistance_nonneg (a b : Allocation S k) (f g : Vertex n→X) (v : Vertex n) :
    0≤commonDistance a b f g v := by unfold commonDistance; split <;> positivity

theorem parked_matching (a b : Allocation S k) (w : Vertex n→ℝ) (hw : ∀ v,0≤w v)
    (f g : Vertex n→X) (G : ℝ) (hG : 0≤G)
    (hgeo : ∀ u v,0<park S a.amount u → 0<park S b.amount v → u≠v →
      dist (f u) (g v)≤G*pathCost (S:=S) w u v)
    {x y : Vertex n→ℤ} (hx : Rounded a x) (hy : Rounded b y)
    (R : Realization (k:=k) (S:=S) x) (T : Realization (k:=k) (S:=S) y) :
    ∃ π : Equiv.Perm (Fin k),
      (∑ i,dist (f (R.tuple i)) (g (T.tuple (π i))))≤
      G*(∑ v : Vertex n,if v=0 then 0 else w (S.parent v)*|(y v:ℝ)-x v|)+
      ∑ v,(intPark S y v:ℝ)*commonDistance a b f g v := by
  obtain ⟨π,hπ⟩ := matching (S:=S) w R.tuple T.tuple
  refine ⟨π,?_⟩
  have hmatch : (∑ i,pathCost (S:=S) w (R.tuple i) (T.tuple (π i)))=
      ∑ v : Vertex n,if v=0 then 0 else w (S.parent v)*|(y v:ℝ)-x v| := by
    rw [hπ]
    apply sum_congr rfl
    intro v _
    rw [R.subtree hx,T.subtree hy,abs_sub_comm]
  have hpoint (i : Fin k) : dist (f (R.tuple i)) (g (T.tuple (π i)))≤
      G*pathCost (S:=S) w (R.tuple i) (T.tuple (π i))+
        commonDistance a b f g (T.tuple (π i)) := by
    have hu := R.valid hx i
    have hv := T.valid hy (π i)
    by_cases he : R.tuple i=T.tuple (π i)
    · rw [he] at hu ⊢
      simp only [commonDistance]
      rw [ite_eq_left (And.intro hu hv)]
      have hn : 0≤pathCost (S:=S) w (T.tuple (π i)) (T.tuple (π i)) := by
        apply sum_nonneg
        intro v _
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (hw _) (abs_nonneg _)
      linarith [mul_nonneg hG hn]
    · exact (hgeo _ _ hu hv he).trans (le_add_of_nonneg_right (commonDistance_nonneg a b f g _))
  calc
    _≤∑ i,(G*pathCost (S:=S) w (R.tuple i) (T.tuple (π i))+
      commonDistance a b f g (T.tuple (π i))) := sum_le_sum (fun i _=>hpoint i)
    _=G*(∑ v : Vertex n,if v=0 then 0 else w (S.parent v)*|(y v:ℝ)-x v|)+
      ∑ v,(intPark S y v:ℝ)*commonDistance a b f g v := by
        rw [sum_add_distrib,←mul_sum,hmatch]
        congr 1
        exact (T.permute π).sum _

theorem mean_intPark {a : Allocation S k} (L : Law) (x : L.State→Vertex n→ℤ)
    (hm : ∀ v,mean L (fun s=>(x s v:ℝ))=a.amount v) (v : Vertex n) :
    mean L (fun s=>(intPark S (x s) v:ℝ))=park S a.amount v := by
  simp only [cast_intPark]
  rw [mean_sub,mean_sum,hm]
  unfold park
  congr 1
  exact sum_congr rfl (fun c _=>hm c.val)

end UniformKServer.TreeRounding

end


end

end OAI
