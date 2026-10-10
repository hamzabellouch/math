import Mathlib

namespace OAI


/-!
Contracted monoid algebras, selectors, and the simplicity criterion.
-/


namespace FiniteAlgebraicEnvelopes.Contracted
open MonoidAlgebra
open scoped Classical
noncomputable section
variable (k H : Type*) [CommRing k] [MonoidWithZero H]

/-- The one-dimensional ideal spanned by the absorbing monoid zero. -/
def zeroSupported (f : MonoidAlgebra k H) : Prop := ∀ h : H, h ≠ 0 → f.coeff h = 0

theorem zeroSupported_iff (f : MonoidAlgebra k H) :
    zeroSupported k H f ↔ f = single 0 (f.coeff 0) := by
  classical
  constructor
  · intro h
    ext a
    by_cases ha : a=0
    · subst a; simp
    · simp [h a ha,ha]
  · intro h a ha
    rw [h]
    simp [ha]

def zeroIdeal : TwoSidedIdeal (MonoidAlgebra k H) :=
  TwoSidedIdeal.mk' {f | zeroSupported k H f}
    (by intro h hh; simp)
    (by intro f g hf hg h hh; simp [hf h hh,hg h hh])
    (by intro f hf h hh; simp [hf h hh])
    (by
      intro f g hg h hh
      rw [(zeroSupported_iff k H g).mp hg]
      exact coeff_mul_single_of_forall_mul_ne _ _ (by simpa using fun _ : H => Ne.symm hh))
    (by
      intro f g hf h hh
      rw [(zeroSupported_iff k H f).mp hf]
      exact coeff_single_mul_of_forall_mul_ne _ _ (by simpa using fun _ : H => Ne.symm hh))

abbrev Algebra := (zeroIdeal k H).ringCon.Quotient

def quotient : MonoidAlgebra k H →ₐ[k] Algebra k H := (zeroIdeal k H).ringCon.mkₐ k

theorem quotient_eq (f g : MonoidAlgebra k H) :
    quotient k H f = quotient k H g ↔ ∀ h : H, h ≠ 0 → f.coeff h = g.coeff h := by
  change (zeroIdeal k H).ringCon.toQuotient f = (zeroIdeal k H).ringCon.toQuotient g ↔ _
  rw [RingCon.eq]
  change zeroSupported k H (f-g) ↔ _
  simp only [zeroSupported,
    MonoidAlgebra.coeff_sub,Finsupp.sub_apply,sub_eq_zero]

def basis (h : H) (c : k) : Algebra k H := quotient k H (single h c)
@[simp] theorem basis_mul (h g : H) (c d : k) :
    basis k H h c * basis k H g d = basis k H (h*g) (c*d) := by
  simp [basis,← map_mul]
@[simp] theorem basis_zero (c : k) : basis k H 0 c = 0 := by
  change quotient k H (single 0 c) = quotient k H 0
  rw [quotient_eq]
  intro h hh
  simp [hh]
@[simp] theorem basis_coeff_zero (h : H) : basis k H h 0 = 0 := by simp [basis]
@[simp] theorem basis_one (c : k) : basis k H 1 c = algebraMap k (Algebra k H) c := rfl
@[simp] theorem basis_identity : basis k H 1 1 = 1 := by simp

instance [Nontrivial k] [Nontrivial H] : Nontrivial (Algebra k H) := by
  apply nontrivial_of_ne (1 : Algebra k H) 0
  intro h
  have h' : quotient k H 1 = quotient k H 0 := h
  have hh := (quotient_eq k H 1 0).mp h' 1 one_ne_zero
  simp at hh

variable {k H}

/-- Ordered finite selectors, expressed by a finite support and distinguished entry. -/
def Selectors (H : Type*) [MonoidWithZero H] : Prop :=
  ∀ (S : Finset H), (0:H) ∉ S → ∀ h ∈ S, ∃ L R : H,
    L*h*R=1 ∧ ∀ g ∈ S, g ≠ h → L*g*R=0

/-- The quotient retains exactly the nonzero monoid coefficients. -/
theorem exists_nonzero_coeff (f : MonoidAlgebra k H) (hf : quotient k H f ≠ 0) :
    ∃ h : H, h ≠ 0 ∧ f.coeff h ≠ 0 := by
  by_contra! h
  apply hf
  change quotient k H f = quotient k H 0
  rw [quotient_eq]
  intro a ha
  simpa using h a ha

/-- Expansion in the exact contracted monoid basis. -/
theorem expansion (f : MonoidAlgebra k H) :
    quotient k H f = f.coeff.sum (fun h c => basis k H h c) := by
  conv_lhs => rw [← sum_coeff_single f]
  simp only [Finsupp.sum,map_sum,basis]

/-- The selector sandwich extracts a single nonzero coefficient. -/
theorem sandwich (f : MonoidAlgebra k H) (h L R : H)
    (he : L*h*R=1) (hz : ∀ g ∈ f.coeff.support, g ≠ h → L*g*R=0) :
    basis k H L 1 * quotient k H f * basis k H R 1 =
      algebraMap k (Algebra k H) (f.coeff h) := by
  classical
  rw [expansion]
  simp only [Finsupp.sum,Finset.mul_sum,Finset.sum_mul,basis_mul,one_mul,mul_one]
  rw [Finset.sum_eq_single h]
  · rw [he,basis_one]
  · intro g hg hgh
    rw [hz g hg hgh,basis_zero]
  · intro hh
    have hf : f.coeff h = 0 := Finsupp.notMem_support_iff.mp hh
    simp [hf]

/-- Coefficients at nonzero monoid elements descend unchanged to the quotient. -/
def coefficient (h : H) (hh : h ≠ 0) : Algebra k H →ₗ[k] k where
  toFun := Quotient.lift (fun f : MonoidAlgebra k H => f.coeff h) (by
    intro f g hfg
    exact (quotient_eq k H f g).mp ((zeroIdeal k H).ringCon.eq.mpr hfg) h hh)
  map_add' x y := Quotient.inductionOn₂ x y (fun f g => by
    change (f+g).coeff h = f.coeff h + g.coeff h
    simp)
  map_smul' c x := Quotient.inductionOn x (fun f => by
    change (c • f).coeff h = c • f.coeff h
    simp)

@[simp] theorem coefficient_quotient (h : H) (hh : h ≠ 0) (f : MonoidAlgebra k H) :
    coefficient h hh (quotient k H f) = f.coeff h := rfl
@[simp] theorem coefficient_basis (h : H) (hh : h ≠ 0) (g : H) (c : k) :
    coefficient h hh (basis k H g c) = if h=g then c else 0 := by
  classical
  simp [basis,Finsupp.single_apply,eq_comm]

theorem coefficient_ext {x y : Algebra k H}
    (h : ∀ a (ha : a ≠ 0), coefficient a ha x = coefficient a ha y) : x=y := by
  induction x using Quotient.inductionOn with | h f =>
    induction y using Quotient.inductionOn with | h g =>
      exact (quotient_eq k H f g).mpr h

/-- The actual basis consists precisely of the nonzero monoid elements. -/
theorem basis_linearIndependent :
    LinearIndependent k (fun h : {h : H // h ≠ 0} => basis k H h 1) := by
  classical
  rw [linearIndependent_iff']
  intro S a ha h hh
  have he := congrArg (coefficient (k:=k) h.val h.property) ha
  have eqv (g : {h : H // h ≠ 0}) : h.val=g.val ↔ h=g := Subtype.ext_iff.symm
  simpa [map_sum,coefficient_basis,eqv,hh] using he

theorem basis_spans :
    (⊤ : Submodule k (Algebra k H)) ≤
      Submodule.span k (Set.range (fun h : {h : H // h ≠ 0} => basis k H h 1)) := by
  intro x hx
  clear hx
  obtain ⟨f,rfl⟩ := (zeroIdeal k H).ringCon.mkₐ_surjective (α:=k) x
  change quotient k H f ∈ _
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | single h r =>
    by_cases hh : h=0
    · subst h; change basis k H 0 r ∈ _; simp
    · have he : quotient k H (single h r) = r • basis k H h 1 := by
        change quotient k H (single h r) = r • quotient k H (single h 1)
        rw [← map_smul]
        congr 1
        simp
      rw [he]
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨⟨h,hh⟩,rfl⟩

def monoidBasis : Module.Basis {h : H // h ≠ 0} k (Algebra k H) :=
  Module.Basis.mk basis_linearIndependent basis_spans

@[simp] theorem monoidBasis_apply (h : {h : H // h ≠ 0}) :
    monoidBasis (k:=k) h = basis k H h 1 := Module.Basis.mk_apply _ _ h

section Lift
variable {C : Type*} [Ring C] [_root_.Algebra k C]
variable (f : MonoidAlgebra k H →ₙₐ[k] C) (hz : f (single (0:H) 1)=0)

include hz in
theorem kill_zeroSupported (x : MonoidAlgebra k H) (hx : zeroSupported k H x) : f x=0 := by
  rw [(zeroSupported_iff k H x).mp hx]
  have he : single (0:H) (x.coeff 0) = x.coeff 0 • single (0:H) (1:k) := by simp
  rw [he,map_smul,hz,smul_zero]

def lift : Algebra k H →ₙₐ[k] C where
  toFun := Quotient.lift f (by
    intro x y hxy
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply kill_zeroSupported f hz
    exact hxy)
  map_zero' := map_zero f
  map_add' x y := Quotient.inductionOn₂ x y (fun a b => map_add f a b)
  map_mul' x y := Quotient.inductionOn₂ x y (fun a b => map_mul f a b)
  map_smul' c x := Quotient.inductionOn x (fun a => map_smul f c a)

@[simp] theorem lift_quotient (x : MonoidAlgebra k H) :
    lift f hz (quotient k H x) = f x := rfl
end Lift

section Embedded
variable {J : Type*} [MonoidWithZero J]
variable (c : H →ₙ* J)

/-- The shift by c(0), essential because c need not preserve either 0 or 1. -/
def shifted : H →ₙ* Algebra k J where
  toFun h := basis k J (c h) 1 - basis k J (c 0) 1
  map_mul' h g := by
    simp only [sub_mul,mul_sub,basis_mul,one_mul,← map_mul,mul_zero,zero_mul]
    abel

def shiftedLift : MonoidAlgebra k H →ₙₐ[k] Algebra k J := MonoidAlgebra.liftMagma k (shifted (k:=k) c)

@[simp] theorem shiftedLift_single (h : H) (r : k) :
    shiftedLift (k:=k) c (single h r) = r • (basis k J (c h) 1 - basis k J (c 0) 1) := by
  simp [shiftedLift,MonoidAlgebra.liftMagma,shifted,smul_sub]

def embedding : Algebra k H →ₙₐ[k] Algebra k J :=
  lift (shiftedLift (k:=k) c) (by simp)

@[simp] theorem embedding_basis (h : H) (r : k) :
    embedding (k:=k) c (basis k H h r) = r • (basis k J (c h) 1 - basis k J (c 0) 1) := by
  simp [embedding,basis]

/-- Every nonzero coefficient is retained at its distinct new basis element. -/
theorem coefficient_embedding (hc : Function.Injective c) (hz : ∀ h, c h ≠ 0)
    (h : H) (hh : h ≠ 0) (x : Algebra k H) :
    coefficient (c h) (hz h) (embedding (k:=k) c x) = coefficient h hh x := by
  obtain ⟨f,rfl⟩ := (zeroIdeal k H).ringCon.mkₐ_surjective (α:=k) x
  change coefficient (c h) (hz h) (embedding c (quotient k H f)) =
    coefficient h hh (quotient k H f)
  induction f using MonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg => simpa only [map_add] using congrArg₂ (·+·) hf hg
    | single g r =>
      change coefficient (c h) (hz h) (embedding (k:=k) c (basis k H g r)) = coefficient h hh (basis k H g r)
      rw [embedding_basis,map_smul,map_sub,coefficient_basis,coefficient_basis]
      have hne : c h ≠ c 0 := fun he => hh (hc he)
      simp only [ite_eq_right hne,sub_zero,coefficient_basis]
      by_cases he : h=g
      · subst g; simp
      · simp [he,hc.eq_iff]

theorem embedding_injective (hc : Function.Injective c) (hz : ∀ h, c h ≠ 0) :
    Function.Injective (embedding (k:=k) c) := by
  intro x y hxy
  apply coefficient_ext
  intro h hh
  rw [← coefficient_embedding c hc hz h hh,← coefficient_embedding c hc hz h hh,hxy]

/-- The unit of B is outside the entire embedded subalgebra, not only different from e. -/
theorem one_not_mem_range [Nontrivial k] [Nontrivial J] (hc : ∀ h, c h ≠ 1) :
    (1 : Algebra k J) ∉ Set.range (embedding (k:=k) c) := by
  rintro ⟨x,hx⟩
  have hz : coefficient (k:=k) (1:J) one_ne_zero (embedding c x) = 0 := by
    clear hx
    obtain ⟨f,rfl⟩ := (zeroIdeal k H).ringCon.mkₐ_surjective (α:=k) x
    change coefficient (1:J) one_ne_zero (embedding c (quotient k H f)) = 0
    induction f using MonoidAlgebra.induction_linear with
      | zero => simp
      | add f g hf hg => simp only [map_add,hf,hg,add_zero]
      | single h r =>
        change coefficient (1:J) one_ne_zero (embedding c (basis k H h r)) = 0
        rw [embedding_basis,map_smul,map_sub,coefficient_basis,coefficient_basis]
        simp [Ne.symm (hc h),Ne.symm (hc 0)]
  rw [hx] at hz
  have hone : coefficient (k:=k) (1:J) one_ne_zero 1 = 1 :=
    (coefficient_basis (k:=k) (1:J) one_ne_zero 1 1).trans (ite_eq_left rfl)
  rw [hone] at hz
  exact one_ne_zero hz

/-- Source support identity e=c(1)−c(0) is proper in the ambient unital algebra. -/
theorem embedding_one_ne_one [Nontrivial k] [Nontrivial J]
    (hc : ∀ h, c h ≠ 1) : embedding (k:=k) c 1 ≠ 1 := by
  intro he
  have h := congrArg (coefficient (k:=k) (1:J) one_ne_zero) he
  have hcoeff : ∀ h, coefficient (k:=k) (1:J) one_ne_zero (basis k J (c h) 1)=0 := by
    intro h; simp only [coefficient_basis,ite_eq_right (Ne.symm (hc h))]
  rw [← basis_identity k H,embedding_basis,one_smul,map_sub,hcoeff,hcoeff,sub_self] at h
  have hone : coefficient (k:=k) (1:J) one_ne_zero 1 = 1 := by
    exact (coefficient_basis (k:=k) (1:J) one_ne_zero 1 1).trans (ite_eq_left rfl)
  rw [hone] at h
  exact zero_ne_one h
end Embedded

/-- Zero-preserving unital monoid maps induce unital maps of contracted algebras. -/
def map {J : Type*} [MonoidWithZero J] (c : H →*₀ J) : Algebra k H →ₐ[k] Algebra k J :=
  { embedding (k:=k) c.toMulHom with
    map_one' := by
      change embedding (k:=k) c.toMulHom 1 = 1
      rw [← basis_identity k H,embedding_basis]
      simp
    commutes' r := by
      change embedding (k:=k) c.toMulHom (algebraMap k (Algebra k H) r) = _
      rw [← basis_one k H r,embedding_basis]
      simp [Algebra.algebraMap_eq_smul_one] }

@[simp] theorem map_basis {J : Type*} [MonoidWithZero J] (c : H →*₀ J) (h : H) (r : k) :
    map (k:=k) c (basis k H h r) = basis k J (c h) r := by
  change embedding c.toMulHom (basis k H h r) = _
  rw [embedding_basis]
  change r • (basis k J (c h) 1 - basis k J (c 0) 1) = _
  rw [c.map_zero, basis_zero, sub_zero]
  change r • quotient k J (single (c h) 1) = quotient k J (single (c h) r)
  rw [← map_smul]
  congr 1
  simp


section Field
variable {K : Type*} [Field K] {H : Type*} [MonoidWithZero H] [Nontrivial H]

/-- The simplicity argument for contracted monoid algebras over any coefficient field. -/
theorem simple_of_selectors (hS : Selectors H) : IsSimpleRing (Algebra K H) := by
  classical
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  by_cases hI : I=⊥
  · exact Or.inl hI
  right
  rw [← I.one_mem_iff]
  obtain ⟨a,ha,ha0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : ⊥ < I)
  obtain ⟨f,rfl⟩ := (zeroIdeal K H).ringCon.mkₐ_surjective (α:=K) a
  obtain ⟨h,hh,hfh⟩ := exists_nonzero_coeff f ha0
  have hmem : h ∈ f.coeff.support.erase 0 := by simp [hh,Finsupp.mem_support_iff,hfh]
  obtain ⟨L,R,he,hz⟩ := hS (f.coeff.support.erase 0) (by simp) h hmem
  have hz' : ∀ g ∈ f.coeff.support, g ≠ h → L*g*R=0 := by
    intro g hg hgh
    by_cases hg0 : g=0
    · simp [hg0]
    · exact hz g (by simp [hg,hg0]) hgh
  have hc : algebraMap K (Algebra K H) (f.coeff h) ∈ I := by
    rw [← sandwich f h L R he hz']
    exact I.mul_mem_right _ _ (I.mul_mem_left _ _ ha)
  have hi := I.mul_mem_left (algebraMap K (Algebra K H) (f.coeff h)⁻¹) _ hc
  simpa only [← map_mul,inv_mul_cancel₀ hfh,map_one] using hi
end Field

end
end FiniteAlgebraicEnvelopes.Contracted


/- Finite weak components and bounded normalization for the finite compiler. -/

end OAI
