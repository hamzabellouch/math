import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphAction
import OAI.Probability.CriticalPercolation.Modular.GraphModular

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

structure OrbitRepresentatives where
  roots : Finset V
  cover : ∀ x : V, ∃ u ∈ roots, ∃ φ : G.Aut, φ.vertex u = x
  unique : ∀ u ∈ roots, ∀ v ∈ roots, ∀ φ : G.Aut, φ.vertex u = v → u = v

lemma finite_vertexOrbits (hq : G.QuasiTransitive) :
    Finite (MulAction.orbitRel.Quotient G.Aut V) := by
  obtain ⟨S,hS,hcover⟩ := hq
  apply Set.finite_univ_iff.mp
  apply (hS.image (fun x : V => (Quotient.mk'' x : MulAction.orbitRel.Quotient G.Aut V))).subset
  intro q _
  induction q using Quotient.inductionOn' with
  | h x =>
    obtain ⟨u,hu,φ,hφ⟩ := hcover x
    refine ⟨u,hu,?_⟩
    apply Quotient.sound
    exact MulAction.mem_orbit_symm.mpr (MulAction.mem_orbit_iff.mpr ⟨φ,hφ⟩)

def orbitRepresentatives (hq : G.QuasiTransitive) : G.OrbitRepresentatives := by
  letI := G.finite_vertexOrbits hq
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient G.Aut V)
  let S : Finset V := Finset.univ.image (Quotient.out : MulAction.orbitRel.Quotient G.Aut V → V)
  refine ⟨S,?_,?_⟩
  · intro x
    let q : MulAction.orbitRel.Quotient G.Aut V := Quotient.mk'' x
    refine ⟨q.out,Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩,?_⟩
    have heq : (Quotient.mk'' q.out : MulAction.orbitRel.Quotient G.Aut V) = Quotient.mk'' x := q.out_eq'
    exact MulAction.mem_orbit_iff.mp (MulAction.mem_orbit_symm.mp (Quotient.exact heq))
  · intro u hu v hv φ hφ
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hv
    have heq : (Quotient.mk'' r.out : MulAction.orbitRel.Quotient G.Aut V) = Quotient.mk'' q.out :=
      Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨φ,hφ⟩)
    rw [Quotient.out_eq',Quotient.out_eq'] at heq
    exact congrArg Quotient.out heq.symm

abbrev PairOrbit := MulAction.orbitRel.Quotient G.Aut (V × V)

def pairOrbit (x y : V) : G.PairOrbit := Quotient.mk'' (x,y)

lemma pairOrbit_eq {x y u v : V} : G.pairOrbit x y = G.pairOrbit u v ↔
    ∃ φ : G.Aut, φ.vertex x = u ∧ φ.vertex y = v := by
  constructor
  · intro h
    obtain ⟨φ,hφ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h.symm)
    exact ⟨φ,congrArg Prod.fst hφ,congrArg Prod.snd hφ⟩
  · rintro ⟨φ,hx,hy⟩
    apply Eq.symm
    apply Quotient.sound
    exact MulAction.mem_orbit_iff.mpr ⟨φ,Prod.ext hx hy⟩

lemma Aut.pairOrbit (φ : G.Aut) (x y : V) :
    G.pairOrbit (φ.vertex x) (φ.vertex y) = G.pairOrbit x y :=
  (G.pairOrbit_eq.mpr ⟨φ,rfl,rfl⟩).symm

namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

abbrev RootedPair := {x // x ∈ R.roots} × V

def pairMap (p : R.RootedPair) : G.PairOrbit := G.pairOrbit p.1 p.2

lemma fiber_root_eq (x : {x // x∈R.roots}) (y : V)
    (p : (pairMap G R) ⁻¹' {G.pairOrbit x y}) : p.val.1 = x := by
  have hh : G.pairOrbit (x:V) y = G.pairOrbit (p.val.1:V) p.val.2 := p.property.symm
  obtain ⟨φ,hφ,_⟩ := G.pairOrbit_eq.mp hh
  exact Subtype.ext (R.unique x x.property p.val.1 p.val.1.property φ hφ).symm

lemma fiber_snd_mem (x : {x // x∈R.roots}) (y : V)
    (p : (pairMap G R) ⁻¹' {G.pairOrbit x y}) : p.val.2 ∈ G.stabilizerOrbit x y := by
  have hh : G.pairOrbit (x:V) y = G.pairOrbit (p.val.1:V) p.val.2 := p.property.symm
  obtain ⟨φ,hφ,hy⟩ := G.pairOrbit_eq.mp hh
  exact G.mem_stabilizerOrbit.mpr ⟨φ,by rw [hφ,fiber_root_eq G R x y p],hy⟩

def fiberEquiv (x : {x // x∈R.roots}) (y : V) :
    (pairMap G R) ⁻¹' {G.pairOrbit x y} ≃ G.stabilizerOrbit x y where
  toFun p := ⟨p.val.2,fiber_snd_mem G R x y p⟩
  invFun z := ⟨(x,z),by
    obtain ⟨φ,hx,hz⟩ := G.mem_stabilizerOrbit.mp z.property
    exact (G.pairOrbit_eq.mpr ⟨φ,hx,hz⟩).symm⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (fiber_root_eq G R x y p).symm rfl
  right_inv z := rfl

end OrbitRepresentatives
end CriticalPercolation.BondGraph
end
end

end OAI
