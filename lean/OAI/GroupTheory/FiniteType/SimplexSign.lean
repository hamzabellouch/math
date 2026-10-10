import Mathlib
import OAI.GroupTheory.FiniteType.DuffyTriangle
import OAI.GroupTheory.FiniteType.SimplexRotation

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
namespace SimplexSign
open Set Topology SimplexRotation RotationClass DuffySimplex
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

def lastSwap (n : ℕ) : Equiv.Perm (Fin (n+2)) :=
  Equiv.swap ⟨n,by omega⟩ (Fin.last (n+1))

lemma lastSwap_zero (n : ℕ) : lastSwap (n+1) 0 = 0 := by
  apply Equiv.swap_apply_of_ne_of_ne <;> intro h <;> have := congrArg Fin.val h <;> simp at this

lemma lastSwap_succ (n : ℕ) (i : Fin (n+2)) :
    lastSwap (n+1) i.succ = (lastSwap n i).succ := by
  exact (Function.Injective.map_swap (Fin.succ_injective _) ⟨n,by omega⟩ (Fin.last (n+1)) i).symm

def reverseLast (n : ℕ) (t : Fin (n+1) → I) : Fin (n+1) → I :=
  fun i => if i = Fin.last n then σ (t i) else t i

lemma reverseLast_succ_zero (n : ℕ) (t : Fin (n+2) → I) : reverseLast (n+1) t 0 = t 0 := by
  simp [reverseLast,show (0 : Fin (n+2)) ≠ Fin.last (n+1) by intro h; have := congrArg Fin.val h; simp at this]

lemma reverseLast_succ_succ (n : ℕ) (t : Fin (n+2) → I) (i : Fin (n+1)) :
    reverseLast (n+1) t i.succ = reverseLast n (fun j => t j.succ) i := by
  simp only [reverseLast]
  congr 1
  apply propext
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ,Fin.val_last] at hv ⊢
    omega
  · rintro rfl
    rfl

lemma simplex_lastSwap : ∀ n (t : Fin (n+1) → I),
    perm (lastSwap n) (toSimplex (n+1) t) = toSimplex (n+1) (reverseLast n t)
  | 0,t => by
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [perm,lastSwap,toSimplex,cone,reverseLast,unitInterval.symm]
  | n+1,t => by
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro i
    induction i using Fin.cases with
    | zero =>
      change (toSimplex (n+2) t).weights (lastSwap (n+1) 0) = _
      rw [lastSwap_zero,toSimplex_succ_zero,toSimplex_succ_zero,reverseLast_succ_zero]
    | succ i =>
      change (toSimplex (n+2) t).weights (lastSwap (n+1) i.succ) = _
      rw [lastSwap_succ,toSimplex_succ_succ,toSimplex_succ_succ,reverseLast_succ_zero]
      congr 1
      have h := congrArg (fun s : DuffySimplex.Std (n+1) => s.weights i) (simplex_lastSwap n (fun j => t j.succ))
      simpa only [perm,ContinuousMap.coe_mk,Finsupp.coe_equivFunOnFinite_symm,
        reverseLast_succ_succ] using h

lemma class_lastSwap (n : ℕ) (f : BasedSimplex.Space (n+1) X x) :
    DuffyBased.homotopyClass (permute f (lastSwap n)) = (DuffyBased.homotopyClass f)⁻¹ := by
  have h : DuffyBased.loop (permute f (lastSwap n)) = GenLoop.symmAt (Fin.last n) (DuffyBased.loop f) := by
    ext t
    change f.1 (perm (lastSwap n) (toSimplex (n+1) t)) = f.1 _
    rw [simplex_lastSwap]
    congr 2
    funext j
    simp only [reverseLast]
    split_ifs with h
    · rw [h]
    · rfl
  exact (congrArg (Quotient.mk _) h).trans (HomotopyGroup.inv_spec (i:=Fin.last n)).symm

def classStabilizer (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X) :
    Subgroup (Equiv.Perm (Fin (n+1))) where
  carrier := {p | ∀ f : BasedSimplex.Space n X x,
    DuffyBased.homotopyClass (permute f p) = DuffyBased.homotopyClass f}
  one_mem' := fun f => by rw [permute_one]
  mul_mem' := by
    intro p q hp hq f
    rw [← permute_mul,hp,hq]
  inv_mem' := by
    intro p hp f
    have h := hp (permute f p⁻¹)
    rw [permute_mul,mul_inv_cancel,permute_one] at h
    exact h.symm

lemma alternating_le_classStabilizer (n : ℕ) :
    alternatingGroup (Fin (n+1)) ≤ classStabilizer n X x := by
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
  apply (Subgroup.closure_le _).mpr
  intro p hp f
  apply class_cube
  intro i
  have h : p^3 = 1 := hp.orderOf ▸ pow_orderOf_eq_one p
  exact congrArg (fun q : Equiv.Perm (Fin (n+1)) => q i) h

lemma class_even {n : ℕ} (f : BasedSimplex.Space n X x)
    (p : Equiv.Perm (Fin (n+1))) (hp : Equiv.Perm.sign p = 1) :
    DuffyBased.homotopyClass (permute f p) = DuffyBased.homotopyClass f :=
  alternating_le_classStabilizer n (Equiv.Perm.mem_alternatingGroup.mpr hp) f

lemma class_odd {n : ℕ} (f : BasedSimplex.Space (n+1) X x)
    (p : Equiv.Perm (Fin (n+2))) (hp : Equiv.Perm.sign p = -1) :
    DuffyBased.homotopyClass (permute f p) = (DuffyBased.homotopyClass f)⁻¹ := by
  have hs : Equiv.Perm.sign (lastSwap n) = -1 := Equiv.Perm.sign_swap (by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega)
  have h := class_even f (lastSwap n * p) (by rw [map_mul,hp,hs]; norm_num)
  rw [← permute_mul,class_lastSwap] at h
  exact inv_eq_iff_eq_inv.mp h

lemma class_sign {n : ℕ} (f : BasedSimplex.Space (n+1) X x)
    (p : Equiv.Perm (Fin (n+2))) :
    DuffyBased.homotopyClass (permute f p) =
      (DuffyBased.homotopyClass f)^((Equiv.Perm.sign p : ℤˣ) : ℤ) := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h
  · rw [class_even f p h,h]
    simp
  · rw [class_odd f p h,h]
    simp

end SimplexSign

namespace FacePermutation
open Equiv
variable {n : ℕ}

def restrict (p : Perm (Fin (n+1))) (i : Fin (n+1)) : Perm (Fin n) :=
  (finSuccAboveEquiv i).trans
    ((p.subtypeEquiv (fun j => by simp only [ne_eq, p.injective.eq_iff])).trans (finSuccAboveEquiv (p i)).symm)

lemma succAbove_restrict (p : Perm (Fin (n+1))) (i : Fin (n+1)) (k : Fin n) :
    (p i).succAbove (restrict p i k) = p (i.succAbove k) := by
  exact congrArg Subtype.val ((finSuccAboveEquiv (p i)).apply_symm_apply
    ((p.subtypeEquiv (fun j => by simp only [ne_eq, p.injective.eq_iff])) (finSuccAboveEquiv i k)))

def liftZero (q : Perm (Fin n)) : Perm (Fin (n+1)) :=
  Perm.decomposeFin.symm (0,q)

@[simp] lemma liftZero_zero (q : Perm (Fin n)) : liftZero q 0 = 0 := by
  simp [liftZero]
@[simp] lemma liftZero_succ (q : Perm (Fin n)) (i : Fin n) : liftZero q i.succ = (q i).succ := by
  simp [liftZero,Perm.decomposeFin_symm_apply_succ]
@[simp] lemma sign_liftZero (q : Perm (Fin n)) : Perm.sign (liftZero q) = Perm.sign q := by
  simp [liftZero,Perm.decomposeFin.symm_sign]

lemma decomposition (p : Perm (Fin (n+1))) (i : Fin (n+1)) :
    p = (p i).cycleRange⁻¹ * liftZero (restrict p i) * i.cycleRange := by
  apply Equiv.ext
  intro j
  obtain rfl | ⟨k,rfl⟩ := Fin.eq_self_or_eq_succAbove i j
  · simp
  · simp [succAbove_restrict]

lemma sign_restrict (p : Perm (Fin (n+1))) (i : Fin (n+1)) :
    (-1 : ℤˣ)^i.val * Perm.sign (restrict p i) = Perm.sign p * (-1 : ℤˣ)^(p i).val := by
  have h := congrArg Perm.sign (decomposition p i)
  simp only [map_mul,map_inv,Fin.sign_cycleRange,sign_liftZero] at h
  rw [h]
  calc
    (-1 : ℤˣ)^i.val * Perm.sign (restrict p i) =
        (((-1 : ℤˣ)^(p i).val)⁻¹ * (-1 : ℤˣ)^(p i).val) *
          (Perm.sign (restrict p i) * (-1 : ℤˣ)^i.val) := by simp [mul_comm]
    _ = _ := by ac_rfl

end FacePermutation

namespace SimplexVertexMaps
open Set Topology SimplexBoundary
variable {n m k : ℕ}

def vertexMap (f : Fin (n+1) → Fin (m+1)) : C(Simplex n,Simplex m) :=
  ⟨Convexity.StdSimplex.map f,Convexity.StdSimplex.continuous_map ℝ f⟩

@[simp] lemma vertexMap_id : vertexMap (id : Fin (n+1) → Fin (n+1)) = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro s
  exact Convexity.StdSimplex.map_id s

lemma vertexMap_comp (f : Fin (n+1) → Fin (m+1)) (g : Fin (m+1) → Fin (k+1)) :
    (vertexMap g).comp (vertexMap f) = vertexMap (g ∘ f) := by
  apply ContinuousMap.ext
  intro s
  exact Convexity.StdSimplex.map_map s f g

lemma vertexMap_perm (p : Equiv.Perm (Fin (n+1))) : vertexMap p = SimplexRotation.perm p.symm := by
  ext s i
  change Finsupp.mapDomain p s.weights i = s.weights (p.symm i)
  simpa only [Equiv.apply_symm_apply] using
    Finsupp.mapDomain_apply_of_injective p.injective s.weights (p.symm i)

lemma vertexMap_face (p : Equiv.Perm (Fin (n+2))) (i : Fin (n+2)) :
    (vertexMap p).comp (face i) = (face (p i)).comp (vertexMap (FacePermutation.restrict p i)) := by
  change (vertexMap p).comp (vertexMap i.succAbove) =
    (vertexMap (p i).succAbove).comp (vertexMap (FacePermutation.restrict p i))
  rw [vertexMap_comp,vertexMap_comp]
  congr 1
  funext j
  exact (FacePermutation.succAbove_restrict p i j).symm

lemma vertexMap_perm_coordinate (p : Equiv.Perm (Fin (n+1))) (s : Simplex n) (i : Fin (n+1)) :
    (vertexMap p s).weights (p i) = s.weights i := by
  rw [vertexMap_perm]
  simp [SimplexRotation.perm]

lemma vertexMap_perm_doubleBoundary (p : Equiv.Perm (Fin (n+1))) (s : Simplex n)
    (hs : s ∈ DuffyTriangle.DoubleBoundary n) : vertexMap p s ∈ DuffyTriangle.DoubleBoundary n := by
  obtain ⟨i,j,hij,hi,hj⟩ := hs
  exact ⟨p i,p j,p.injective.ne hij,(vertexMap_perm_coordinate p s i).trans hi,
    (vertexMap_perm_coordinate p s j).trans hj⟩

lemma vertexMap_zero_of_notMem_range (f : Fin (n+1) → Fin (m+1)) (i : Fin (m+1))
    (hi : i ∉ Set.range f) (s : Simplex n) : (vertexMap f s).weights i = 0 := by
  exact Finsupp.mapDomain_of_notMem_range s.weights i hi

end SimplexVertexMaps

end

end OAI
