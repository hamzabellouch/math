import Mathlib

namespace OAI

section
noncomputable section
open Set
open scoped Classical BigOperators

namespace ActionOrbitTransport
variable (Λ X : Type*) [Group Λ] [MulAction Λ X]

structure Representatives where
  roots : Finset X
  cover : ∀ x : X, ∃ u ∈ roots, ∃ φ : Λ, φ • u = x
  unique : ∀ u ∈ roots, ∀ v ∈ roots, ∀ φ : Λ, φ • u = v → u = v

lemma finite_orbits (S : Set X) (hS : S.Finite)
    (hcover : ∀ x : X, ∃ u∈S, x∈MulAction.orbit Λ u) :
    Finite (MulAction.orbitRel.Quotient Λ X) := by
  apply Set.finite_univ_iff.mp
  apply (hS.image (fun x : X => (Quotient.mk'' x : MulAction.orbitRel.Quotient Λ X))).subset
  intro q _
  induction q using Quotient.inductionOn' with
  | h x =>
    obtain ⟨u,hu,φ,hφ⟩ := hcover x
    refine ⟨u,hu,?_⟩
    apply Quotient.sound
    exact MulAction.mem_orbit_symm.mpr (MulAction.mem_orbit_iff.mpr ⟨φ,hφ⟩)

def representatives (S : Set X) (hS : S.Finite)
    (hcover : ∀ x : X, ∃ u∈S, x∈MulAction.orbit Λ u) : Representatives Λ X := by
  letI := finite_orbits Λ X S hS hcover
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient Λ X)
  let R : Finset X := Finset.univ.image (Quotient.out : MulAction.orbitRel.Quotient Λ X → X)
  refine ⟨R,?_,?_⟩
  · intro x
    let q : MulAction.orbitRel.Quotient Λ X := Quotient.mk'' x
    refine ⟨q.out,Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩,?_⟩
    have heq : (Quotient.mk'' q.out : MulAction.orbitRel.Quotient Λ X) = Quotient.mk'' x := q.out_eq'
    exact MulAction.mem_orbit_iff.mp (MulAction.mem_orbit_symm.mp (Quotient.exact heq))
  · intro u hu v hv φ hφ
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hv
    have heq : (Quotient.mk'' r.out : MulAction.orbitRel.Quotient Λ X) = Quotient.mk'' q.out :=
      Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨φ,hφ⟩)
    rw [Quotient.out_eq',Quotient.out_eq'] at heq
    exact congrArg Quotient.out heq.symm

abbrev PairOrbit := MulAction.orbitRel.Quotient Λ (X × X)
def pairOrbit (x y : X) : PairOrbit Λ X := Quotient.mk'' (x,y)
def stabilizerOrbit (x y : X) : Set X := MulAction.orbit (MulAction.stabilizer Λ x) y
def suborbitCard (x y : X) : ℕ := (stabilizerOrbit Λ X x y).ncard

lemma mem_stabilizerOrbit {x y z : X} : z ∈ stabilizerOrbit Λ X x y ↔
    ∃ φ : Λ, φ • x = x ∧ φ • y = z := by
  simp only [stabilizerOrbit,MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨φ,hφ⟩
    exact ⟨φ,φ.property,hφ⟩
  · rintro ⟨φ,hx,hy⟩
    exact ⟨⟨φ,hx⟩,hy⟩

lemma pairOrbit_eq {x y u v : X} : pairOrbit Λ X x y = pairOrbit Λ X u v ↔
    ∃ φ : Λ, φ • x = u ∧ φ • y = v := by
  constructor
  · intro h
    obtain ⟨φ,hφ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h.symm)
    exact ⟨φ,congrArg Prod.fst hφ,congrArg Prod.snd hφ⟩
  · rintro ⟨φ,hx,hy⟩
    apply Eq.symm
    apply Quotient.sound
    exact MulAction.mem_orbit_iff.mpr ⟨φ,Prod.ext hx hy⟩

lemma smul_pairOrbit (φ : Λ) (x y : X) :
    pairOrbit Λ X (φ • x) (φ • y) = pairOrbit Λ X x y :=
  (pairOrbit_eq Λ X |>.mpr ⟨φ,rfl,rfl⟩).symm

lemma smul_suborbitCard (φ : Λ) (x y : X) :
    suborbitCard Λ X (φ • x) (φ • y) = suborbitCard Λ X x y := by
  have heq : (fun z => φ • z) '' stabilizerOrbit Λ X x y =
      stabilizerOrbit Λ X (φ • x) (φ • y) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      obtain ⟨ψ,hx,hy⟩ := (mem_stabilizerOrbit Λ X).mp hw
      apply (mem_stabilizerOrbit Λ X).mpr
      refine ⟨φ*ψ*φ⁻¹,?_,?_⟩
      · simp only [mul_smul,inv_smul_smul,hx]
      · simp only [mul_smul,inv_smul_smul,hy]
    · intro hz
      obtain ⟨ψ,hx,hy⟩ := (mem_stabilizerOrbit Λ X).mp hz
      refine ⟨φ⁻¹ • z,?_,smul_inv_smul φ z⟩
      apply (mem_stabilizerOrbit Λ X).mpr
      refine ⟨φ⁻¹*ψ*φ,?_,?_⟩
      · simp only [mul_smul,hx,inv_smul_smul]
      · simp only [mul_smul,hy]
  rw [suborbitCard,←heq,Set.ncard_image_of_injective _ (MulAction.injective φ)]
  rfl

private def swapFn : PairOrbit Λ X → PairOrbit Λ X :=
  Quotient.map Prod.swap (by
    intro a b hab
    obtain ⟨φ,hφ⟩ := MulAction.mem_orbit_iff.mp hab
    exact MulAction.mem_orbit_iff.mpr ⟨φ,Prod.ext (congrArg Prod.snd hφ) (congrArg Prod.fst hφ)⟩)

def swapPairOrbit : PairOrbit Λ X ≃ PairOrbit Λ X where
  toFun := swapFn Λ X
  invFun := swapFn Λ X
  left_inv q := by induction q using Quotient.inductionOn' with | h p => rfl
  right_inv q := by induction q using Quotient.inductionOn' with | h p => rfl

namespace Representatives
variable (R : Representatives Λ X)
abbrev RootedPair := {x // x∈R.roots} × X
def pairMap (p : R.RootedPair) : PairOrbit Λ X := pairOrbit Λ X p.1 p.2

lemma fiber_root_eq (x : {x // x∈R.roots}) (y : X)
    (p : (pairMap Λ X R) ⁻¹' {pairOrbit Λ X x y}) : p.val.1 = x := by
  have hh : pairOrbit Λ X (x:X) y = pairOrbit Λ X (p.val.1:X) p.val.2 := p.property.symm
  obtain ⟨φ,hφ,_⟩ := (pairOrbit_eq Λ X).mp hh
  exact Subtype.ext (R.unique x x.property p.val.1 p.val.1.property φ hφ).symm

lemma fiber_snd_mem (x : {x // x∈R.roots}) (y : X)
    (p : (pairMap Λ X R) ⁻¹' {pairOrbit Λ X x y}) : p.val.2 ∈ stabilizerOrbit Λ X x y := by
  have hh : pairOrbit Λ X (x:X) y = pairOrbit Λ X (p.val.1:X) p.val.2 := p.property.symm
  obtain ⟨φ,hφ,hy⟩ := (pairOrbit_eq Λ X).mp hh
  exact (mem_stabilizerOrbit Λ X).mpr ⟨φ,by rw [hφ,fiber_root_eq Λ X R x y p],hy⟩

def fiberEquiv (x : {x // x∈R.roots}) (y : X) :
    (pairMap Λ X R) ⁻¹' {pairOrbit Λ X x y} ≃ stabilizerOrbit Λ X x y where
  toFun p := ⟨p.val.2,fiber_snd_mem Λ X R x y p⟩
  invFun z := ⟨(x,z),by
    obtain ⟨φ,hx,hz⟩ := (mem_stabilizerOrbit Λ X).mp z.property
    exact ((pairOrbit_eq Λ X).mpr ⟨φ,hx,hz⟩).symm⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (fiber_root_eq Λ X R x y p).symm rfl
  right_inv z := rfl

end Representatives
end ActionOrbitTransport
end
end

end OAI
