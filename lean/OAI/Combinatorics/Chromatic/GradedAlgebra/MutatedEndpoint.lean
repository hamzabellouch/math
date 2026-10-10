import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutationChamberPaths

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd : ∀r≠0,∃m,Ω r m≠0)

def strictRootsThrough (D : ℕ) : Finset M := by
  classical
  exact (Finset.range D).biUnion (fun n=>(rootDegree_finite C (n+1)).toFinset)
omit [DecidableEq I] in
lemma mem_strictRootsThrough (D : ℕ) (m : M) :
    m∈strictRootsThrough C D ↔ ∃n,n+1≤D ∧ HasRootDegree C (n+1) m := by
  classical
  simp only [strictRootsThrough,Finset.mem_biUnion,Finset.mem_range,Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq,Nat.lt_iff_add_one_le]

omit [FiniteDimensional ℝ E] in
include hdeg in
lemma RegularCovector.simple_ne {a : Module.Dual ℝ E} (HA : RegularCovector C e a) :
    a (e (simpleRoot C pc))≠0 :=
  HA 1 _ (realRoot_mem e C 1 1 le_rfl _ (simpleRoot_degree C pc))
    (realRoot_ne_zero C e L hdeg 1 (by omega) _ (simpleRoot_degree C pc))

include hnd in
lemma mutatedTransport_endpoint_support (V : M → Prop)
    (hV : ∀a b,V a → V b → V (a+b)) (D : ℕ)
    {a b : Module.Dual ℝ E} (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (hmatch : ∀n,n+1≤D → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m → ¬V m →
      (0<realMutationCovector e S (simpleRoot C pc) a (e m) ∧
       0<realMutationCovector e S (simpleRoot C pc) b (e m)) ∨
      (realMutationCovector e S (simpleRoot C pc) a (e m)<0 ∧
       realMutationCovector e S (simpleRoot C pc) b (e m)<0)) :
    ∀n,n+1≤D → SupportedOn LaurentRay.vUnit Ω V
      (coeff (n+1) (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB).val) := by
  classical
  let f (m : M) : E:=if 0<realMutationCovector e S (simpleRoot C pc) a (e m) then e m else -e m
  let R:=(strictRootsThrough (mutatedRoots Ω C pc) D).filter (fun m=>¬V m)
  let P:=R.image f
  have hp (n : ℕ) (hn : n+1≤D) (m : M)
      (hm : HasRootDegree (mutatedRoots Ω C pc) (n+1) m) (hv : ¬V m) : f m∈P:=
    Finset.mem_image.mpr ⟨m,Finset.mem_filter.mpr
      ⟨(mem_strictRootsThrough _ _ _).mpr ⟨n,hn,hm⟩,hv⟩,rfl⟩
  have hab : a∈mutationSignRegion e S (simpleRoot C pc) P ∧
      b∈mutationSignRegion e S (simpleRoot C pc) P:=by
    have aux (x : E) (hx : x∈P) :
        0<realMutationCovector e S (simpleRoot C pc) a x ∧
        0<realMutationCovector e S (simpleRoot C pc) b x:=by
      obtain ⟨m,hm,rfl⟩:=Finset.mem_image.mp hx
      obtain ⟨hm,hv⟩:=Finset.mem_filter.mp hm
      obtain ⟨n,hn,hm⟩:=(mem_strictRootsThrough _ _ _).mp hm
      rcases hmatch n hn m hm hv with hh|hh
      · dsimp only [f]
        rw [ite_eq_left hh.1]
        exact hh
      · dsimp only [f]
        rw [ite_eq_right (not_lt.mpr hh.1.le),map_neg,map_neg]
        exact ⟨neg_pos.mpr hh.1,neg_pos.mpr hh.2⟩
    exact ⟨fun x hx=>(aux x hx).1,fun x hx=>(aux x hx).2⟩
  apply mutatedTransport_protected Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    P V hV D _ HA HB hab.1 hab.2 (HA.simple_ne C pc e L hdeg) (HB.simple_ne C pc e L hdeg)
  intro n hn m hm hv
  have hh:=hp n hn m hm hv
  dsimp [f] at hh
  split_ifs at hh
  · exact Or.inl hh
  · exact Or.inr hh
end
end ElementaryPositivity.QuantumTorus

end

end OAI
