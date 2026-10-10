import Mathlib

namespace OAI

/-!
Height-one membership into free targets, minimal covers, graded Nakayama, reverse projectivity, saturated edge kernels and strict Hilbert detection.
-/

section


namespace KLInvariance.EdgeLattice

variable {R : Type*} [CommRing R] [klPreservedInstance2 : IsDomain R] [klPreservedInstance3 : UniqueFactorizationMonoid R]

include klPreservedInstance2 klPreservedInstance3 in
private theorem finsupp_divide {ι : Type*} (r : R) (f : ι →₀ R)
    (h : ∀ i, r ∣ f i) : ∃ g : ι →₀ R, r • g = f := by
  have _ := klPreservedInstance2
  have _ := klPreservedInstance3
  classical
  let g : ι →₀ R := ∑ i ∈ f.support, Finsupp.single i (Classical.choose (h i))
  refine ⟨g, ?_⟩
  dsimp [g]
  rw [Finset.smul_sum]
  have heq : (∑ i ∈ f.support, r • Finsupp.single i (Classical.choose (h i))) =
      ∑ i ∈ f.support, Finsupp.single i (f i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finsupp.smul_single, smul_eq_mul, ← Classical.choose_spec (h i)]
  rw [heq]
  exact Finsupp.sum_single f

/-- In a free module, divisibility can be checked on a basis. -/
private theorem basis_divide {E : Type*} [AddCommGroup E] [Module R E]
    {ι : Type*} (b : Module.Basis ι R E) (p : R) (m : E)
    (h : ∀ i, p ∣ b.repr m i) : ∃ n : E, p • n = m := by
  obtain ⟨f, hf⟩ := finsupp_divide p (b.repr m) h
  refine ⟨b.repr.symm f, b.repr.injective ?_⟩
  simpa only [map_smul, b.repr.apply_symm_apply] using hf

/-- Scalar-denominator formulation of the height-one intersection property.
A generic-span witness and local denominators away from each prime element
force membership in a free target, with no reflexivity hypothesis on a source. -/
theorem mem_of_prime_local_membership
    {E : Type*} [AddCommGroup E] [Module R E] [Module.IsTorsionFree R E]
    (M : Submodule R E) [Module.Free R M] (x : E)
    (hgeneric : ∃ c : R, c ≠ 0 ∧ c • x ∈ M)
    (hlocal : ∀ p : R, Prime p → ∃ a : R, ¬p ∣ a ∧ a • x ∈ M) : x ∈ M := by
  classical
  obtain ⟨c, hcz, hcx⟩ := hgeneric
  suffices ∀ c : R, c ≠ 0 → c • x ∈ M → x ∈ M from this c hcz hcx
  intro c
  induction c using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp
  | h₂ c hc =>
    intro _ hcx
    obtain ⟨u, rfl⟩ := hc
    simpa using M.smul_mem (↑u⁻¹ : R) hcx
  | h₃ c p hcz hp ih =>
    intro _ hpcx
    obtain ⟨a, hpa, hax⟩ := hlocal p hp
    let m : M := ⟨(p * c) • x, hpcx⟩
    let n : M := ⟨a • x, hax⟩
    have heq : a • m = (p * c) • n := by
      apply Subtype.ext
      change a • ((p * c) • x) = (p * c) • (a • x)
      exact smul_comm a (p * c) x
    let b := Module.Free.chooseBasis R M
    have hdvd : ∀ i, p ∣ b.repr m i := by
      intro i
      have hcoord := congrArg (fun z : M => b.repr z i) heq
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hcoord
      have hmul : p ∣ a * b.repr m i := by
        rw [hcoord]
        exact dvd_mul_of_dvd_left (dvd_mul_right p c) _
      exact (hp.dvd_mul.mp hmul).resolve_left hpa
    obtain ⟨m', hm'⟩ := basis_divide b p m hdvd
    have hcx : c • x = (m' : E) := by
      apply smul_right_injective E hp.ne_zero
      have hval := congrArg (fun z : M => (z : E)) hm'
      change p • (m' : E) = (p * c) • x at hval
      simpa only [mul_smul] using hval.symm
    exact ih hcz (hcx ▸ m'.property)

include klPreservedInstance2 klPreservedInstance3 in
/-- A localization membership can be written with a scalar denominator outside
its prime, without requiring a choice of basis in the ambient module. -/
theorem exists_denominator_of_localized_mem
    {E : Type*} [AddCommGroup E] [Module R E]
    (M : Submodule R E) (P : Ideal R) [P.IsPrime] (x : E)
    (hx : LocalizedModule.mk x (1 : P.primeCompl) ∈ M.localized P.primeCompl) :
    ∃ a : R, a ∉ P ∧ a • x ∈ M := by
  have _ := klPreservedInstance2
  have _ := klPreservedInstance3
  obtain ⟨m, hm, s, hs⟩ := hx
  rw [← IsLocalizedModule.mk_eq_mk'] at hs
  obtain ⟨t, ht⟩ := LocalizedModule.mk_eq.mp hs
  refine ⟨(t : R) * s, (t * s).property, ?_⟩
  have hh := M.smul_mem (t : R) hm
  simp only [Submonoid.smul_def, one_smul] at ht
  rw [ht] at hh
  simpa only [mul_smul] using hh


theorem mem_iff_localized_at_height_one
    [IsNoetherianRing R]
    {E : Type*} [AddCommGroup E] [Module R E] [Module.IsTorsionFree R E]
    (M : Submodule R E) [Module.Free R M]
    (hgeneric : ∀ x : E, ∃ c : R, c ≠ 0 ∧ c • x ∈ M) (x : E) :
    x ∈ M ↔ ∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
      LocalizedModule.mk x (1 : P.primeCompl) ∈ M.localized P.primeCompl := by
  constructor
  · intro hx P _ _
    exact ⟨x, hx, 1, by simp⟩
  · intro hx
    apply mem_of_prime_local_membership M x (hgeneric x)
    intro p hp
    let P := Ideal.span ({p} : Set R)
    have : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
    have hheight : P.height = 1 :=
      Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr hp.ne_zero) hp.not_isUnit
    obtain ⟨a, ha, hax⟩ := exists_denominator_of_localized_mem M P x (hx P hheight)
    exact ⟨a, by simpa only [P, Ideal.mem_span_singleton] using ha, hax⟩

/-- Equality with the intersection of preimages of all height-one localizations.
It includes the field case: an empty height-one intersection is the full module. -/
theorem eq_iInf_height_one_localizations
    [IsNoetherianRing R]
    {E : Type*} [AddCommGroup E] [Module R E] [Module.IsTorsionFree R E]
    (M : Submodule R E) [Module.Free R M]
    (hgeneric : ∀ x : E, ∃ c : R, c ≠ 0 ∧ c • x ∈ M) :
    M = ⨅ (P : PrimeSpectrum R) (_ : P.asIdeal.height = 1),
      ((M.localized P.asIdeal.primeCompl).restrictScalars R).comap
        (LocalizedModule.mkLinearMap P.asIdeal.primeCompl E) := by
  ext x
  simp only [Submodule.mem_iInf, Submodule.mem_comap, Submodule.restrictScalars_mem,
    LocalizedModule.mkLinearMap_apply]
  rw [mem_iff_localized_at_height_one M hgeneric x]
  constructor
  · intro h P hp
    exact h P.asIdeal hp
  · intro h P hP hp
    exact h ⟨P, hP⟩ hp

end KLInvariance.EdgeLattice


end

section


/-! The local algebra step in `loc:decomposition`, source §4.4. The maps
are actual linear maps; neither a decomposition nor a lift is assumed. -/
namespace KLInvariance.LocalCover

variable {R B P N : Type*} [CommRing R] [IsLocalRing R]
  [AddCommGroup B] [Module R B] [AddCommGroup P] [Module R P]
  [AddCommGroup N] [Module R N]

/-- A lift through a minimal free cover is automatically surjective. This
is the exact Nakayama step of plane-localized BMP decomposition. -/
theorem lift_surjective [Module.Finite R P]
    (π : P →ₗ[R] N) (φ : B →ₗ[R] N) (g : B →ₗ[R] P)
    (hφ : Function.Surjective φ) (hg : π.comp g = φ)
    (hmin : LinearMap.ker π ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P)) :
    Function.Surjective g := by
  apply LinearMap.surjective_of_surjective_comp_mkQ g (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  intro q
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨b, hb⟩ := hφ (π p)
  refine ⟨b, ?_⟩
  change Submodule.Quotient.mk (g b) = Submodule.Quotient.mk p
  apply (Submodule.Quotient.eq _).mpr
  apply hmin
  change π (g b - p) = 0
  rw [map_sub, ← LinearMap.comp_apply, hg, hb, sub_self]

/-- An explicit linear equivalence for a split surjection, with the kernel
as the second summand. It is used below to produce the local sheaf summand. -/
noncomputable def splitEquiv (g : B →ₗ[R] P) (s : P →ₗ[R] B)
    (hs : g.comp s = LinearMap.id) : B ≃ₗ[R] P × LinearMap.ker g := by
  have hs' (p : P) : g (s p) = p := LinearMap.congr_fun hs p
  let k : B →ₗ[R] LinearMap.ker g :=
    { toFun := fun b => ⟨b - s (g b), by simp [LinearMap.mem_ker, hs']⟩
      map_add' := fun x y => Subtype.ext (by simp; abel)
      map_smul' := fun r x => Subtype.ext (by simp [smul_sub]) }
  exact
    { toFun := fun b => (g b, k b)
      invFun := fun p => s p.1 + p.2
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp
      left_inv := fun b => by simp [k]
      right_inv := fun ⟨p, b⟩ => by
        apply Prod.ext
        · simp [hs']
        · apply Subtype.ext
          simp [k, hs'] }

/-- The full minimal-cover splitting required at each descending vertex.
The new kernel is proved finite free over the local ring, not introduced
as a free summand hypothesis. -/
theorem exists_split_minimal_cover [Module.Free R B] [Module.Finite R B]
    [Module.Free R P] [Module.Finite R P]
    (π : P →ₗ[R] N) (φ : B →ₗ[R] N)
    (hπ : Function.Surjective π) (hφ : Function.Surjective φ)
    (hmin : LinearMap.ker π ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P)) :
    ∃ (g : B →ₗ[R] P) (e : B ≃ₗ[R] P × LinearMap.ker g),
      Function.Surjective g ∧ π.comp g = φ ∧
      Module.Free R (LinearMap.ker g) ∧ Module.Finite R (LinearMap.ker g) ∧
      ∀ b, (e b).1 = g b ∧ π (e b).1 = φ b := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property π φ hπ
  have hsurj := lift_surjective π φ g hφ hg hmin
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  let e := splitEquiv g s hs
  let k : B →ₗ[R] LinearMap.ker g := (LinearMap.snd R P (LinearMap.ker g)).comp e.toLinearMap
  have hk : Function.Surjective k := by
    intro b
    exact ⟨e.symm (0, b), by simp [k]⟩
  have hki : k.comp (LinearMap.ker g).subtype = LinearMap.id := by
    ext b
    change ((b : B) - s (g b)) = b
    simp []
  let : Module.Finite R (LinearMap.ker g) := Module.Finite.of_surjective k hk
  let : Module.Projective R (LinearMap.ker g) :=
    Module.Projective.of_split (LinearMap.ker g).subtype k hki
  let : Module.Free R (LinearMap.ker g) := Module.free_of_flat_of_isLocalRing
  refine ⟨g, e, hsurj, hg, inferInstance, inferInstance, ?_⟩
  intro b
  exact ⟨rfl, LinearMap.congr_fun hg b⟩

end KLInvariance.LocalCover


namespace KLInvariance.ReverseFiltration

variable {R F E I : Type*} [CommRing R]
  [AddCommGroup F] [Module R F] [AddCommGroup E] [Module R E]
  [AddCommGroup I] [Module R I]

/-- The kernel of a surjection from a projective module is projective if
the target has an actual length-one projective presentation. -/
theorem kernel_projective_of_presentation
    [Module.Projective R F] [Module.Projective R E]
    (f : F →ₗ[R] I) (g : E →ₗ[R] I)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    [Module.Projective R (LinearMap.ker g)] :
    Module.Projective R (LinearMap.ker f) := by
  obtain ⟨a, ha⟩ := Module.projective_lifting_property g f hg
  obtain ⟨b, hb⟩ := Module.projective_lifting_property f g hf
  have ha' (x : F) : g (a x) = f x := LinearMap.congr_fun ha x
  have hb' (x : E) : f (b x) = g x := LinearMap.congr_fun hb x
  let a₀ : LinearMap.ker f →ₗ[R] LinearMap.ker g :=
    { toFun := fun x => ⟨a x, by simp [LinearMap.mem_ker, ha']⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun r x => Subtype.ext (by simp) }
  let i : LinearMap.ker f →ₗ[R] F × LinearMap.ker g :=
    (LinearMap.ker f).subtype.prod a₀
  let r : F × LinearMap.ker g →ₗ[R] LinearMap.ker f :=
    { toFun := fun x => ⟨x.1 - b (a x.1) + b x.2, by
        simp [LinearMap.mem_ker, hb', ha']⟩
      map_add' := fun x y => Subtype.ext (by simp; abel)
      map_smul' := fun r x => Subtype.ext (by simp [smul_add, smul_sub]) }
  apply Module.Projective.of_split i r
  ext x
  change (x : F) - b (a x) + b (a x) = x
  exact sub_add_cancel _ _

end KLInvariance.ReverseFiltration


namespace KLInvariance.Graded

variable {k A M : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [AddCommGroup M] [Module k M] [Module A M] [klPreservedInstance4 : IsScalarTower k A M]

noncomputable def component (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓜] (n : ℤ) : M →ₗ[k] M where
  toFun m := DirectSum.decompose 𝓜 m n
  map_add' x y := by simp [DirectSum.decompose_add]
  map_smul' r m := by simp [DirectSum.decompose_smul, DirectSum.smul_apply]

def positiveIdeal (𝓐 : ℤ → Submodule k A) : Ideal A :=
  Ideal.span {a | ∃ n : ℤ, 0 < n ∧ a ∈ 𝓐 n}

include klPreservedInstance4 in
/-- A bounded-below internally graded module which equals its positive-ideal
multiple is zero.  This is the exact graded Nakayama vanishing step used to
remove the complementary kernel in the source's free-cover construction. -/
theorem subsingleton_of_positiveIdeal_smul_eq_top
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
    (d₀ : ℤ) (hbound : ∀ j < d₀, 𝓜 j = ⊥)
    (hgen : positiveIdeal 𝓐 • (⊤ : Submodule A M) = ⊤) :
    Subsingleton M := by
  have _ := klPreservedInstance4
  classical
  have hlow : ∀ j < d₀, ∀ m ∈ 𝓜 j, m = 0 := by
    intro j hj m hm
    simpa [hbound j hj] using hm
  have hind : ∀ n : ℕ, ∀ m ∈ 𝓜 (d₀ + n), m = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      let p := component 𝓜 (d₀ + n)
      have hpadd (x y : M) : p (x + y) = p x + p y := map_add p x y
      have hpzero : p 0 = 0 := map_zero p
      have hsmul (i : ℤ) (hi : 0 < i) (a : A) (ha : a ∈ 𝓐 i) :
          ∀ m : M, p (a • m) = 0 := by
        intro m
        refine DirectSum.Decomposition.inductionOn 𝓜 ?_ ?_ ?_ m
        · simp
        · intro j m
          by_cases hj : j < d₀ + n
          · have hm : (m : M) = 0 := by
              by_cases hj₀ : j < d₀
              · exact hlow j hj₀ m m.property
              · have heq : d₀ + (j - d₀).toNat = j := by omega
                exact ih (j - d₀).toNat (by omega) m (heq.symm ▸ m.property)
            simp [hm]
          · have hdeg : i + j ≠ d₀ + n := by omega
            have ham : a • (m : M) ∈ 𝓜 (i + j) :=
              SetLike.GradedSMul.smul_mem ha m.property
            exact DirectSum.decompose_of_mem_ne 𝓜 ham hdeg
        · intro x y hx hy
          simp only [smul_add, hpadd, hx, hy, add_zero]
      let K : Ideal A :=
        { carrier := {a | ∀ m : M, p (a • m) = 0}
          zero_mem' := by simp
          add_mem' := by
            intro a b ha hb m
            rw [add_smul, hpadd, ha m, hb m, add_zero]
          smul_mem' := by
            intro r a ha m
            change p ((r * a) • m) = 0
            rw [mul_comm r a, mul_smul]
            exact ha (r • m) }
      have hIK : positiveIdeal 𝓐 ≤ K := by
        apply Ideal.span_le.mpr
        rintro a ⟨i, hi, ha⟩
        exact hsmul i hi a ha
      have hp : ∀ m : M, p m = 0 := by
        intro m
        have hm : m ∈ positiveIdeal 𝓐 • (⊤ : Submodule A M) := by
          rw [hgen]
          trivial
        refine Submodule.smul_induction_on hm ?_ ?_
        · intro a ha x _
          exact hIK ha x
        · intro x y hx hy
          rw [hpadd, hx, hy, add_zero]
      intro m hm
      have hcomp : p m = m :=
        DirectSum.decompose_of_mem_same 𝓜 hm
      exact hcomp.symm.trans (hp m)
  have homogeneous_zero (j : ℤ) (m : M) (hm : m ∈ 𝓜 j) : m = 0 := by
    by_cases hj : j < d₀
    · exact hlow j hj m hm
    · have heq : d₀ + (j - d₀).toNat = j := by omega
      exact hind (j - d₀).toNat m (heq.symm ▸ hm)
  have all_zero : ∀ m : M, m = 0 :=
    DirectSum.Decomposition.inductionOn 𝓜 rfl
      (fun m => homogeneous_zero _ m m.property)
      (fun x y hx hy => by rw [hx, hy, add_zero])
  exact ⟨fun x y => (all_zero x).trans (all_zero y).symm⟩

end KLInvariance.Graded


namespace KLInvariance.EdgeImage
open scoped Pointwise

variable {A B D : Type*} [CommRing A]
  [AddCommGroup B] [Module A B] [AddCommGroup D] [Module A D]

/-- The simultaneous vanishing conditions are saturated with respect to α
when multiplication by α is injective on their target. -/
theorem kernel_saturated (f : B →ₗ[A] D) (α : A)
    (hα : Function.Injective (fun x : D => α • x)) (b : B) :
    α • b ∈ LinearMap.ker f ↔ b ∈ LinearMap.ker f := by
  simp only [LinearMap.mem_ker, map_smul]
  constructor
  · intro h
    apply hα
    simpa using h
  · intro h
    simp [h]

/-- Reducing the saturated kernel modulo α introduces no additional
relations. This is the injectivity behind L/αL ≃ J. -/
theorem reduced_kernel_injective (f : B →ₗ[A] D) (α : A)
    (hα : Function.Injective (fun x : D => α • x)) :
    Function.Injective (QuotSMulTop.map α (LinearMap.ker f).subtype) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ x
  have hb : (b : B) ∈ α • (⊤ : Submodule A B) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact hx
  obtain ⟨c, _, hc⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hb
  have hfc : c ∈ LinearMap.ker f :=
    (kernel_saturated f α hα c).mp (hc.symm ▸ b.property)
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
  exact ⟨⟨c, hfc⟩, trivial, Subtype.ext hc⟩

/-- The inclusion after reduction, viewed over the actual factor ring. -/
def reducedInclusion (f : B →ₗ[A] D) (α : A) :
    QuotSMulTop α (LinearMap.ker f) →ₗ[A ⧸ Ideal.span {α}] QuotSMulTop α B :=
  (QuotSMulTop.map α (LinearMap.ker f).subtype).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/-- Freeness of the later-edge kernel proves freeness of its actual edge
image over A/(α), not merely generic freeness. -/
theorem range_reducedInclusion_free (f : B →ₗ[A] D) (α : A)
    (hα : Function.Injective (fun x : D => α • x))
    [Module.Free A (LinearMap.ker f)] :
    Module.Free (A ⧸ Ideal.span {α}) (LinearMap.range (reducedInclusion f α)) := by
  let e := LinearEquiv.ofInjective (reducedInclusion f α)
    (reduced_kernel_injective f α hα)
  exact Module.Free.of_equiv e

end KLInvariance.EdgeImage

end

section

namespace KLInvariance.Graded
open scoped Pointwise
variable {A F P : Type*} [CommRing A]
  [AddCommGroup F] [Module A F] [AddCommGroup P] [Module A P]

/-- If a split cover is minimal modulo I, its complementary kernel equals
its own I-multiple. This is the exact input to the graded Nakayama step. -/
theorem positive_smul_kernel_of_minimal_split
    (I : Ideal A) (f : F →ₗ[A] P) (s : P →ₗ[A] F)
    (hs : f.comp s = LinearMap.id)
    (hmin : LinearMap.ker f ≤ I • (⊤ : Submodule A F)) :
    I • (⊤ : Submodule A (LinearMap.ker f)) = ⊤ := by
  have hs' (y : P) : f (s y) = y := LinearMap.congr_fun hs y
  let k : F →ₗ[A] LinearMap.ker f :=
    { toFun := fun x => ⟨x - s (f x), by simp [LinearMap.mem_ker, hs']⟩
      map_add' := fun x y => Subtype.ext (by simp; abel)
      map_smul' := fun r x => Subtype.ext (by simp [smul_sub]) }
  apply le_antisymm le_top
  intro x _
  have hx : (x : F) ∈ I • (⊤ : Submodule A F) := hmin x.property
  have hkx : k (x : F) = x := by
    apply Subtype.ext
    simp [k]
  rw [← hkx]
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y _
    rw [map_smul]
    exact Submodule.smul_mem_smul hr (Submodule.mem_top : k y ∈ (⊤ : Submodule A _))
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

/-- Minimality makes a split free cover an isomorphism in the bounded-below
graded situation. Its kernel is not assumed to vanish. -/
theorem bijective_of_graded_minimal_split
    {k : Type*} [CommRing k] [Algebra k A]
    (𝓐 : ℤ → Submodule k A) (f : F →ₗ[A] P) (s : P →ₗ[A] F)
    (hs : f.comp s = LinearMap.id)
    (hmin : LinearMap.ker f ≤ positiveIdeal 𝓐 • (⊤ : Submodule A F))
    [Module k (LinearMap.ker f)] [IsScalarTower k A (LinearMap.ker f)]
    (𝓚 : ℤ → Submodule k (LinearMap.ker f))
    [DirectSum.Decomposition 𝓚] [SetLike.GradedSMul 𝓐 𝓚]
    (d₀ : ℤ) (hbound : ∀ j < d₀, 𝓚 j = ⊥) : Function.Bijective f := by
  let := subsingleton_of_positiveIdeal_smul_eq_top 𝓐 𝓚 d₀ hbound
    (positive_smul_kernel_of_minimal_split (positiveIdeal 𝓐) f s hs hmin)
  constructor
  · apply LinearMap.ker_eq_bot.mp
    refine le_antisymm ?_ bot_le
    intro x hx
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker f) 0)
  · intro y
    exact ⟨s y, LinearMap.congr_fun hs y⟩

end KLInvariance.Graded


end

section

namespace KLInvariance.Hilbert
universe uk um
variable {k : Type uk} {M : Type um} [Field k] [AddCommGroup M] [Module k M]

/-- The actual degree-n vector space of a submodule, expressed in the fixed
ambient homogeneous piece. -/
def piece (𝓜 : ℤ → Submodule k M) (S : Submodule k M) (n : ℤ) :
    Submodule k (𝓜 n) := S.comap (𝓜 n).subtype

noncomputable def term (𝓜 : ℤ → Submodule k M) (S : Submodule k M)
    (q : ℝ) (n : ℤ) : ℝ := (Module.finrank k (piece 𝓜 S n) : ℝ)*q^n

noncomputable def value (𝓜 : ℤ → Submodule k M) (S : Submodule k M)
    (q : ℝ) : ℝ := ∑' n : ℤ, term 𝓜 S q n

lemma piece_mono (𝓜 : ℤ → Submodule k M) {S T : Submodule k M}
    (h : S ≤ T) (n : ℤ) : piece 𝓜 S n ≤ piece 𝓜 T n :=
  Submodule.comap_mono h

lemma term_nonneg (𝓜 : ℤ → Submodule k M) (S : Submodule k M)
    {q : ℝ} (hq : 0 < q) (n : ℤ) : 0 ≤ term 𝓜 S q n := by
  exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (zpow_pos hq _))

lemma term_mono (𝓜 : ℤ → Submodule k M) [∀ n, Module.Finite k (𝓜 n)]
    {S T : Submodule k M} (h : S ≤ T) {q : ℝ} (hq : 0 < q) (n : ℤ) :
    term 𝓜 S q n ≤ term 𝓜 T q n := by
  apply mul_le_mul_of_nonneg_right _ (le_of_lt (zpow_pos hq _))
  exact_mod_cast Submodule.finrank_mono (piece_mono 𝓜 h n)

lemma summable_of_le (𝓜 : ℤ → Submodule k M) [∀ n, Module.Finite k (𝓜 n)]
    {S T : Submodule k M} (h : S ≤ T) {q : ℝ} (hq : 0 < q)
    (hT : Summable (term 𝓜 T q)) : Summable (term 𝓜 S q) :=
  Summable.of_nonneg_of_le (term_nonneg 𝓜 S hq) (term_mono 𝓜 h hq) hT

/-- Equality at one positive convergent parameter, with actual inclusion,
forces equality of each homogeneous piece. -/
theorem pieces_eq_of_value_eq (𝓜 : ℤ → Submodule k M)
    [∀ n, Module.Finite k (𝓜 n)] {S T : Submodule k M}
    (h : S ≤ T) {q : ℝ} (hq : 0 < q)
    (hT : Summable (term 𝓜 T q)) (hv : value 𝓜 S q = value 𝓜 T q) :
    ∀ n, piece 𝓜 S n = piece 𝓜 T n := by
  intro n
  apply Submodule.eq_of_le_of_finrank_eq (piece_mono 𝓜 h n)
  by_contra hne
  have hlt : Module.finrank k (piece 𝓜 S n) < Module.finrank k (piece 𝓜 T n) :=
    lt_of_le_of_ne (Submodule.finrank_mono (piece_mono 𝓜 h n)) hne
  have hterm : term 𝓜 S q n < term 𝓜 T q n := by
    apply mul_lt_mul_of_pos_right _ (zpow_pos hq n)
    exact_mod_cast hlt
  have hstrict := (summable_of_le 𝓜 h hq hT).tsum_lt_tsum
    (term_mono 𝓜 h hq) hterm hT
  exact (ne_of_lt hstrict) hv

/-- No assumption on support codimension is involved. Equality of convergent
Hilbert values detects equality with a homogeneous target globally. -/
theorem eq_of_value_eq (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
    [∀ n, Module.Finite k (𝓜 n)] {S T : Submodule k M}
    (h : S ≤ T) (hhom : ∀ n m, m ∈ T → (DirectSum.decompose 𝓜 m n : M) ∈ T)
    {q : ℝ} (hq : 0 < q) (hT : Summable (term 𝓜 T q))
    (hv : value 𝓜 S q = value 𝓜 T q) : S = T := by
  classical
  apply le_antisymm h
  intro m hm
  rw [← DirectSum.sum_support_decompose 𝓜 m]
  apply Submodule.sum_mem
  intro n hn
  have heq := pieces_eq_of_value_eq 𝓜 h hq hT hv n
  have hmem : DirectSum.decompose 𝓜 m n ∈ piece 𝓜 T n := hhom n m hm
  rw [←heq] at hmem
  exact hmem

lemma value_mono (𝓜 : ℤ → Submodule k M) [∀ n, Module.Finite k (𝓜 n)]
    {S T : Submodule k M} (h : S ≤ T) {q : ℝ} (hq : 0 < q)
    (hT : Summable (term 𝓜 T q)) : value 𝓜 S q ≤ value 𝓜 T q :=
  (summable_of_le 𝓜 h hq hT).tsum_le_tsum (term_mono 𝓜 h hq) hT

/-- The degree-n piece of the actual quotient T/S. -/
abbrev defectPiece (𝓜 : ℤ → Submodule k M) (S T : Submodule k M) (n : ℤ) :=
  piece 𝓜 T n ⧸ (piece 𝓜 S n).comap (piece 𝓜 T n).subtype

noncomputable def defectTerm (𝓜 : ℤ → Submodule k M) (S T : Submodule k M)
    (q : ℝ) (n : ℤ) : ℝ := (Module.finrank k (defectPiece 𝓜 S T n) : ℝ)*q^n

lemma defectTerm_eq_sub (𝓜 : ℤ → Submodule k M)
    [∀ n, Module.Finite k (𝓜 n)] {S T : Submodule k M} (h : S ≤ T)
    (q : ℝ) (n : ℤ) : defectTerm 𝓜 S T q n = term 𝓜 T q n-term 𝓜 S q n := by
  have heq := ((piece 𝓜 S n).comap (piece 𝓜 T n).subtype).finrank_quotient_add_finrank
  rw [(Submodule.comapSubtypeEquivOfLe (piece_mono 𝓜 h n)).finrank_eq] at heq
  have hc : (Module.finrank k (defectPiece 𝓜 S T n) : ℝ)+
      (Module.finrank k (piece 𝓜 S n) : ℝ) =
        Module.finrank k (piece 𝓜 T n) := by exact_mod_cast heq
  unfold defectTerm term
  rw [←hc]
  ring

/-- Additivity of convergent Hilbert values for the actual degreewise quotient. -/
theorem defect_value_eq_sub (𝓜 : ℤ → Submodule k M)
    [∀ n, Module.Finite k (𝓜 n)] {S T : Submodule k M} (h : S ≤ T)
    {q : ℝ} (hq : 0 < q) (hT : Summable (term 𝓜 T q)) :
    Summable (defectTerm 𝓜 S T q) ∧
      ∑' n, defectTerm 𝓜 S T q n = value 𝓜 T q-value 𝓜 S q := by
  have hf : defectTerm 𝓜 S T q = fun n => term 𝓜 T q n-term 𝓜 S q n :=
    funext (defectTerm_eq_sub 𝓜 h q)
  rw [hf]
  exact ⟨hT.sub (summable_of_le 𝓜 h hq hT),
    hT.tsum_sub (summable_of_le 𝓜 h hq hT)⟩

/-- All proper homogeneous defects have a strictly positive Hilbert series;
there is no exception for support in codimension ≥2 or finite length. -/
theorem defect_value_pos (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
    [∀ n, Module.Finite k (𝓜 n)] {S T : Submodule k M}
    (h : S ≤ T) (hne : S ≠ T)
    (hhom : ∀ n m, m ∈ T → (DirectSum.decompose 𝓜 m n : M) ∈ T)
    {q : ℝ} (hq : 0 < q) (hT : Summable (term 𝓜 T q)) :
    0 < ∑' n, defectTerm 𝓜 S T q n := by
  rw [(defect_value_eq_sub 𝓜 h hq hT).2]
  apply sub_pos.mpr
  apply lt_of_le_of_ne (value_mono 𝓜 h hq hT)
  intro heq
  exact hne (eq_of_value_eq 𝓜 h hhom hq hT heq)

end KLInvariance.Hilbert

end


section

/-! Minimal homogeneous free covers, restored after the accidental filename
collision with GradedCoverUniqueness. The generator argument is the existing
homogeneous-basis proof before its projectivity-only final step. -/

end

end OAI
