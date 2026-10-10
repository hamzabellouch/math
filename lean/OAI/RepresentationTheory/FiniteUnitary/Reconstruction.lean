import OAI.RepresentationTheory.FiniteUnitary.Frames
import OAI.RepresentationTheory.RowColumn.Basic

namespace OAI

section
noncomputable section
open scoped BigOperators ComplexOrder
namespace RowColumn.UnitaryFrame
variable {A G : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [FiniteDimensional ℂ A] [Group G]

omit [FiniteDimensional ℂ A] in
lemma positive_functional_bound (f : A →ₚ[ℂ] ℂ) (x : A) :
    ‖f x‖ ≤ 4 * ‖f 1‖ * ‖x‖ := by
  obtain ⟨y, hy_nonneg, hy_norm, hy⟩ := CStarAlgebra.exists_sum_four_nonneg x
  conv_lhs => rw [hy]
  simp only [map_sum, map_smul]
  apply (norm_sum_le _ _).trans
  simp only [norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
  apply (Finset.sum_le_sum (g := fun _ => ‖f 1‖ * ‖x‖) (fun i _ => ?_)).trans
  · simp [mul_assoc]
  · exact (f.norm_apply_le_of_nonneg _ (hy_nonneg i)).trans
      (mul_le_mul_of_nonneg_left (hy_norm i) (norm_nonneg _))

/-- Finite-dimensional unitary reconstruction with polynomial Fourier cost.
Only the actual operator norm of B occurs; the auxiliary Hilbert norm is used
solely to construct the frame and does not alter that norm. -/
theorem reconstruction_bound (τ : A →ₗ[ℂ] ℂ) (core : InnerProductSpace.Core ℂ A)
    (hinner : ∀ x y, core.inner x y = τ (star x*y))
    (u : G →* unitary A)
    (hspan : Submodule.span ℂ (Set.range fun g : G => (u g : A)) = ⊤)
    (B : A) (ℓ : A →ₗ[ℂ] ℂ) (R : ℝ) (_ : 0 ≤ R)
    (hU : ∀ g, ‖ℓ (u g : A)‖ ≤ R) :
    ‖ℓ B‖ ≤ 4 * (Module.finrank ℂ A : ℝ) * ‖B‖ * R := by
  obtain ⟨D,hD,hpos,hrec⟩ := exists_density τ core hinner u hspan
  let φ : A →ₗ[ℂ] ℂ := τ.comp (LinearMap.mulRight ℂ D)
  have hφpos (a : A) (ha : 0 ≤ a) : 0 ≤ φ a := by
    have hh := hpos (CFC.sqrt a)
    have hs : star (CFC.sqrt a) * CFC.sqrt a = a := by
      rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq]
      exact CFC.sqrt_mul_sqrt_self a ha
    change 0 ≤ τ (a*D)
    simpa only [hs] using hh
  let f : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ φ hφpos
  have hf1 : ‖f 1‖ = (Module.finrank ℂ A : ℝ) := by
    change ‖τ (1*D)‖ = _
    rw [one_mul, hD]
    simp
  apply hrec B ℓ
  intro g
  rw [← mul_assoc]
  change ‖φ (star (u g : A)*B) * ℓ (u g : A)‖ ≤ _
  rw [norm_mul]
  have hb : ‖φ (star (u g : A)*B)‖ ≤ 4 * (Module.finrank ℂ A : ℝ) * ‖B‖ := by
    have hh := positive_functional_bound f (star (u g : A)*B)
    rw [hf1] at hh
    change ‖f (star (u g : A)*B)‖ ≤ _
    simpa only [← Unitary.coe_star, CStarRing.norm_coe_unitary_mul] using hh
  exact mul_le_mul hb (hU g) (norm_nonneg _) (by positivity)

end RowColumn.UnitaryFrame
noncomputable section
open scoped ComplexConjugate
namespace RowColumn.FiniteStarAlgebra
variable {A : Type*} [Ring A] [Module ℂ A] [StarRing A] [FiniteDimensional ℂ A]

/-- A finite-dimensional two-sided star ideal has a central orthogonal unit.
The two inner-product identities hold for the actual Hilbert–Schmidt trace.
This constructs the central support used in the occupied-board filter. -/
theorem complementary_central_projection (core : InnerProductSpace.Core ℂ A) (K : Submodule ℂ A)
    (hL : ∀ a x, x ∈ K → a*x ∈ K) (hR : ∀ a x, x ∈ K → x*a ∈ K)
    (hstar : ∀ x, x ∈ K → star x ∈ K)
    (hadjL : ∀ a x y : A, core.inner (a*x) y = core.inner x (star a*y))
    (hadjR : ∀ a x y : A, core.inner (x*a) y = core.inner x (y*star a)) :
    ∃ q : A, star q = q ∧ q*q = q ∧ (∀ a, q*a = a*q) ∧
      1-q ∈ K ∧ (∀ x, x ∈ K → q*x = 0 ∧ x*q = 0) := by
  let : NormedAddCommGroup A := core.toNormedAddCommGroup
  let : InnerProductSpace ℂ A := InnerProductSpace.ofCore { __ := core }
  change ∀ a x y : A, inner ℂ (a*x) y = inner ℂ x (star a*y) at hadjL
  change ∀ a x y : A, inner ℂ (x*a) y = inner ℂ x (y*star a) at hadjR
  have hoL (a x : A) (hx : x ∈ Kᗮ) : a*x ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro y hy
    have hh := hx (star a*y) (hL (star a) y hy)
    simpa only [hadjL, star_star] using hh
  have hoR (a x : A) (hx : x ∈ Kᗮ) : x*a ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro y hy
    have hh := hx (y*star a) (hR (star a) y hy)
    simpa only [hadjR, star_star] using hh
  have hz (x : A) (hk : x ∈ K) (ho : x ∈ Kᗮ) : x = 0 :=
    (inner_self_eq_zero (𝕜 := ℂ)).mp ((K.mem_orthogonal x).mp ho x hk)
  let k : A := K.starProjection 1
  let q : A := 1-k
  have hk : k ∈ K := (K.orthogonalProjectionOnto 1).property
  have hq : q ∈ Kᗮ := K.sub_starProjection_mem_orthogonal 1
  have hqa (x : A) (hx : x ∈ K) : q*x = 0 :=
    hz _ (hL q x hx) (hoR x q hq)
  have haq (x : A) (hx : x ∈ K) : x*q = 0 :=
    hz _ (hR q x hx) (hoL x q hq)
  have hsk : star k = k := by
    have e₁ : star k = k*star k := by
      have he := hqa (star k) (hstar k hk)
      change (1-k)*star k = 0 at he
      simpa only [sub_mul, one_mul, sub_eq_zero] using he
    have e₂ := congrArg star e₁
    simp only [star_star, star_mul] at e₂
    exact e₁.trans e₂.symm
  refine ⟨q, ?_, ?_, ?_, ?_, fun x hx => ⟨hqa x hx, haq x hx⟩⟩
  · simp only [q, star_sub, star_one, hsk]
  · change q*(1-k) = q
    rw [mul_sub, mul_one, hqa k hk, sub_zero]
  · intro a
    have hka : k*a = k*a*k := by
      have he := haq (k*a) (hR a k hk)
      change (k*a)*(1-k) = 0 at he
      simpa only [mul_sub, mul_one, sub_eq_zero] using he
    have hak : a*k = k*a*k := by
      have he := hqa (a*k) (hL a k hk)
      change (1-k)*(a*k) = 0 at he
      simpa only [sub_mul, one_mul, sub_eq_zero, ← mul_assoc] using he
    change (1-k)*a = a*(1-k)
    rw [sub_mul, one_mul, mul_sub, mul_one]
    exact congrArg (fun z => a-z) (hka.trans hak.symm)
  · simpa only [q, sub_sub_cancel] using hk

end RowColumn.FiniteStarAlgebra

namespace RowColumn.FiniteStarAlgebra
open scoped ComplexOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

abbrev Ambient := E →L[ℂ] E

def algebraToEnd (A : StarSubalgebra ℂ (Ambient (E := E))) : A →ₗ[ℂ] (E →ₗ[ℂ] E) :=
  { toFun a := (a : Ambient (E := E)).toLinearMap
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

lemma algebraToEnd_injective (A : StarSubalgebra ℂ (Ambient (E := E))) :
    Function.Injective (algebraToEnd A) := by
  intro a b h
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact LinearMap.congr_fun h x

@[instance_reducible]
def algebraCore (A : StarSubalgebra ℂ (Ambient (E := E))) : InnerProductSpace.Core ℂ A where
  inner a b := HilbertSchmidt.endCore.inner (algebraToEnd A a) (algebraToEnd A b)
  conj_inner_symm a b := HilbertSchmidt.endCore.conj_inner_symm _ _
  re_inner_nonneg a := HilbertSchmidt.endCore.re_inner_nonneg _
  add_left a b c := by rw [map_add]; exact HilbertSchmidt.endCore.add_left _ _ _
  smul_left a b c := by rw [map_smul]; exact HilbertSchmidt.endCore.smul_left _ _ _
  definite a h := (algebraToEnd_injective A) (by simpa only [map_zero] using HilbertSchmidt.endCore.definite _ h)

def physicalTrace (A : StarSubalgebra ℂ (Ambient (E := E))) : A →ₗ[ℂ] ℂ :=
  (LinearMap.trace ℂ E).comp (algebraToEnd A)

lemma core_inner_trace (A : StarSubalgebra ℂ (Ambient (E := E))) (a b : A) :
    (algebraCore A).inner a b = physicalTrace A (star a*b) := by
  change LinearMap.trace ℂ E (LinearMap.adjoint (a : Ambient (E := E)).toLinearMap ∘ₗ
    (b : Ambient (E := E)).toLinearMap) = LinearMap.trace ℂ E ((star (a : Ambient (E := E)) * (b : Ambient (E := E))).toLinearMap)
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_toLinearMap]
  rfl

lemma physicalTrace_mul_comm (A : StarSubalgebra ℂ (Ambient (E := E))) (a b : A) :
    physicalTrace A (a*b) = physicalTrace A (b*a) :=
  LinearMap.trace_comp_comm' (b : Ambient (E := E)).toLinearMap (a : Ambient (E := E)).toLinearMap

/-- Restriction to a subspace preserved by the whole star algebra is a genuine
star homomorphism (both the subspace and its orthogonal complement are reducing). -/
def restrictHom (A : StarSubalgebra ℂ (Ambient (E := E))) (F : Submodule ℂ E)
    (hF : ∀ a : A, ∀ x ∈ F, (a : Ambient (E := E)) x ∈ F) : A →⋆ₐ[ℂ] (F →L[ℂ] F) where
  toFun a := (a : Ambient (E := E)).restrict (hF a)
  map_zero' := by ext x; rfl
  map_add' a b := by ext x; rfl
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl
  commutes' c := by ext x; rfl
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ ((star (a : Ambient (E := E))) (x : E)) (y : E) =
      inner ℂ (x : E) ((a : Ambient (E := E)) (y : E))
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- Central support of a reducing physical subspace. Its algebraic kernel is
removed, so no other unsupported sector can inflate the Fourier norm. -/
theorem exists_central_support (A : StarSubalgebra ℂ (Ambient (E := E))) (F : Submodule ℂ E)
    (hF : ∀ a : A, ∀ x ∈ F, (a : Ambient (E := E)) x ∈ F) :
    ∃ q : A, star q = q ∧ q*q=q ∧ (∀ a, q*a=a*q) ∧
      restrictHom A F hF q = 1 ∧
      (∀ a : A, restrictHom A F hF a = 0 → q*a=0) := by
  let : FiniteDimensional ℂ A := FiniteDimensional.of_injective
    (algebraToEnd A) (algebraToEnd_injective A)
  let φ := restrictHom A F hF
  let K := LinearMap.ker φ.toLinearMap
  have hk (a : A) : a ∈ K ↔ φ a = 0 := Iff.rfl
  obtain ⟨q,hs,hqq,hc,hkq,hkill⟩ := complementary_central_projection (algebraCore A) K
    (fun a x hx => by rw [hk, map_mul, (hk x).mp hx, mul_zero])
    (fun a x hx => by rw [hk, map_mul, (hk x).mp hx, zero_mul])
    (fun x hx => by rw [hk, map_star, (hk x).mp hx]; exact star_zero (F →L[ℂ] F))
    (fun a x y => by simp only [core_inner_trace, star_mul, mul_assoc])
    (fun a x y => by
      simp only [core_inner_trace, star_mul]
      rw [mul_assoc, physicalTrace_mul_comm A (star a) _, mul_assoc])
  refine ⟨q,hs,hqq,hc,?_,fun a ha => (hkill a ((hk a).mpr ha)).1⟩
  have hh := (hk (1-q)).mp hkq
  have he : 1-φ q=0 := by simpa only [map_sub, map_one] using hh
  exact (sub_eq_zero.mp he).symm

end RowColumn.FiniteStarAlgebra
noncomputable section
namespace RowColumn.FiniteStarAlgebra
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def supportedAlgebra (q : A) (hs : star q = q) (hc : ∀ a, q*a=a*q) :
    NonUnitalStarSubalgebra ℂ A where
  carrier := {a | q*a=a}
  zero_mem' := mul_zero q
  add_mem' := by intro a b ha hb; change q*(a+b)=a+b; rw [mul_add, ha, hb]
  mul_mem' := by intro a b ha hb; change q*(a*b)=a*b; rw [← mul_assoc, ha]
  smul_mem' := by intro c a ha; change q*(c • a)=c • a; rw [mul_smul_comm, ha]
  star_mem' := by
    intro a ha
    change q*star a=star a
    rw [hc]
    simpa only [star_mul, hs] using congrArg star ha

lemma supportedAlgebra_closed (q : A) (hs : star q = q) (hc : ∀ a, q*a=a*q) :
    IsClosed (supportedAlgebra q hs hc : Set A) :=
  isClosed_eq (continuous_const.mul continuous_id) continuous_id

/-- Removing the kernel by its central support makes restriction isometric.
This avoids choosing irreducible compact-group carriers or using unproved
Schur--Weyl decompositions. -/
theorem norm_supported_eq (φ : A →⋆ₐ[ℂ] B) (q : A) (hs : star q = q)
    (hqq : q*q=q) (hc : ∀ a, q*a=a*q) (hq : φ q=1)
    (hkill : ∀ a, φ a=0 → q*a=0) (a : A) : ‖q*a‖ = ‖φ a‖ := by
  let J := supportedAlgebra q hs hc
  let : IsClosed (J : Set A) := supportedAlgebra_closed q hs hc
  let ψ : J →⋆ₙₐ[ℂ] B := φ.toNonUnitalStarAlgHom.comp (NonUnitalStarSubalgebraClass.subtype J)
  have hinj : Function.Injective ψ := by
    intro x y h
    apply Subtype.ext
    have he : φ ((x : A)-(y : A))=0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr h
    have hz := hkill _ he
    change q*((x : A)-(y : A))=0 at hz
    rw [mul_sub, x.property, y.property] at hz
    exact sub_eq_zero.mp hz
  let x : J := ⟨q*a, by change q*(q*a)=q*a; rw [← mul_assoc, hqq]⟩
  have hh := NonUnitalStarAlgHom.norm_map ψ hinj x
  change ‖φ (q*a)‖ = ‖q*a‖ at hh
  rw [map_mul, hq, one_mul] at hh
  exact hh.symm

end RowColumn.FiniteStarAlgebra
noncomputable section
open scoped BigOperators ComplexConjugate
namespace RowColumn.Isotypic
variable {G V E : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (ρ : Representation ℂ G V) (τ : Representation ℂ G E)

def carrier : Submodule ℂ E := Submodule.span ℂ
  (Set.range fun p : Representation.IntertwiningMap ρ τ × V => p.1 p.2)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] in
lemma mem_carrier (f : Representation.IntertwiningMap ρ τ) (v : V) : f v ∈ carrier ρ τ :=
  Submodule.subset_span ⟨(f,v),rfl⟩

lemma projection_intertwines (F : Submodule ℂ E)
    (hF : ∀ g x, x ∈ F → τ g x ∈ F)
    (hτ : ∀ g x y, inner ℂ (τ g x) (τ g y) = inner ℂ x y) :
    ∀ g x, F.starProjection (τ g x) = τ g (F.starProjection x) := by
  intro g x
  let e : E →ₗᵢ[ℂ] E := (τ g).isometryOfInner (hτ g)
  have hmap : F.map e.toLinearMap = F := by
    apply le_antisymm
    · rintro _ ⟨y,hy,rfl⟩
      exact hF g y hy
    · intro y hy
      refine ⟨τ g⁻¹ y, hF g⁻¹ y hy, ?_⟩
      change (τ g * τ g⁻¹) y = y
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
  have he := e.map_starProjection F x
  simpa only [hmap, e, LinearMap.coe_isometryOfInner] using he.symm

omit [FiniteDimensional ℂ V] in
/-- On an isotypic unitary representation, every eigenspace of an operator in
the group commutant has dimension at least that of the irreducible type. -/
theorem eigenspace_finrank [Representation.IsIrreducible ρ]
    (hspan : carrier ρ τ = ⊤)
    (hτ : ∀ g x y, inner ℂ (τ g x) (τ g y) = inner ℂ x y)
    (T : E →ₗ[ℂ] E) (hT : ∀ g x, T (τ g x) = τ g (T x))
    (μ : ℂ) (hμ : Module.End.HasEigenvalue T μ) :
    Module.finrank ℂ V ≤ Module.finrank ℂ (Module.End.eigenspace T μ) := by
  classical
  let F := Module.End.eigenspace T μ
  have hf (g : G) (x : E) (hx : x ∈ F) : τ g x ∈ F := by
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hT, hx, map_smul]
  let P : Representation.IntertwiningMap τ τ :=
    { toLinearMap := F.starProjection.toLinearMap
      isIntertwining' g := by ext x; exact projection_intertwines τ F hf hτ g x }
  have hex : ∃ f : Representation.IntertwiningMap ρ τ, P.comp f ≠ 0 := by
    by_contra! h
    have hz (x : E) (hx : x ∈ carrier ρ τ) : P x = 0 := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨f,v⟩,rfl⟩ := hx
        exact congrArg (fun L : Representation.IntertwiningMap ρ τ => L v) (h f)
      | zero => exact map_zero P
      | add x y hx hy hpx hpy => simp only [map_add, hpx, hpy, add_zero]
      | smul c x hx hpx => simp only [map_smul, hpx, smul_zero]
    obtain ⟨x,hx,hxn⟩ := hμ.exists_hasEigenvector
    have he := hz x (by rw [hspan]; trivial)
    change F.starProjection x = 0 at he
    rw [F.starProjection_eq_self_iff.mpr hx] at he
    exact hxn he
  obtain ⟨f,hfne⟩ := hex
  have hi : Function.Injective (P.comp f) :=
    (Representation.IsIrreducible.injective_or_eq_zero (P.comp f)).resolve_right hfne
  let L : V →ₗ[ℂ] F := (P.comp f).toLinearMap.codRestrict F (fun v =>
    (F.orthogonalProjectionOnto (f v)).property)
  apply LinearMap.finrank_le_finrank_of_injective (f := L)
  intro x y h
  exact hi (congrArg Subtype.val h)

end RowColumn.Isotypic
namespace RowColumn.Isotypic
variable {G V E : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (ρ : Representation ℂ G V) (τ : Representation ℂ G E)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] in
lemma carrier_invariant (g : G) (x : E) (hx : x ∈ carrier ρ τ) : τ g x ∈ carrier ρ τ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨f,v⟩,rfl⟩ := hx
    rw [← Representation.IntertwiningMap.isIntertwining ρ τ f]
    exact mem_carrier ρ τ f _
  | zero => simpa only [map_zero] using (carrier ρ τ).zero_mem
  | add x y hx hy hx' hy' => simpa only [map_add] using (carrier ρ τ).add_mem hx' hy'
  | smul c x hx hx' => simpa only [map_smul] using (carrier ρ τ).smul_mem c hx'

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] in
lemma carrier_commutant (T : E →ₗ[ℂ] E) (hT : ∀ g x, T (τ g x) = τ g (T x))
    (x : E) (hx : x ∈ carrier ρ τ) : T x ∈ carrier ρ τ := by
  let t : Representation.IntertwiningMap τ τ :=
    { toLinearMap := T
      isIntertwining' g := by ext x; exact hT g x }
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨f,v⟩,rfl⟩ := hx
    exact mem_carrier ρ τ (t.comp f) v
  | zero => simpa only [map_zero] using (carrier ρ τ).zero_mem
  | add x y hx hy hx' hy' => simpa only [map_add] using (carrier ρ τ).add_mem hx' hy'
  | smul c x hx hx' => simpa only [map_smul] using (carrier ρ τ).smul_mem c hx'

def restricted : Representation ℂ G (carrier ρ τ) where
  toFun g := (τ g).restrict (carrier_invariant ρ τ g)
  map_one' := by ext x; exact LinearMap.congr_fun (map_one τ) x
  map_mul' g h := by ext x; exact LinearMap.congr_fun (map_mul τ g h) x

def restrictIntertwiner (f : Representation.IntertwiningMap ρ τ) :
    Representation.IntertwiningMap ρ (restricted ρ τ) where
  toLinearMap := f.toLinearMap.codRestrict (carrier ρ τ) (mem_carrier ρ τ f)
  isIntertwining' g := by
    ext v
    exact Representation.IntertwiningMap.isIntertwining ρ τ f g v

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] in
lemma restricted_unitary (hτ : ∀ g x y, inner ℂ (τ g x) (τ g y) = inner ℂ x y) :
    ∀ g (x y : carrier ρ τ), inner ℂ (restricted ρ τ g x) (restricted ρ τ g y) = inner ℂ x y := by
  intro g x y
  exact hτ g x y

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] in
lemma restricted_isotypic : carrier ρ (restricted ρ τ) = ⊤ := by
  let F := carrier ρ τ
  let K := (carrier ρ (restricted ρ τ)).map F.subtype
  have hFK : F ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨f,v⟩,rfl⟩
    exact ⟨restrictIntertwiner ρ τ f v, mem_carrier ρ (restricted ρ τ)
      (restrictIntertwiner ρ τ f) v, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y,hy,hxy⟩ := hFK x.property
  have he : y=x := Subtype.ext hxy
  exact he ▸ hy

end RowColumn.Isotypic
noncomputable section
open scoped BigOperators ComplexOrder
namespace RowColumn.SpectralMultiplicity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma positive_norm_le_of_eigenvalues (T : E →L[ℂ] E) (hT : T.IsPositive)
    (c : ℝ) (hc : 0 ≤ c)
    (hval : ∀ i, hT.toLinearMap.isSymmetric.eigenvalues rfl i ≤ c) : ‖T‖ ≤ c := by
  let b := hT.toLinearMap.isSymmetric.eigenvectorBasis rfl
  apply T.opNorm_le_bound hc
  intro x
  apply le_of_sq_le_sq _ (mul_nonneg hc (norm_nonneg _))
  rw [← b.repr.norm_map (T x), ← b.repr.norm_map x, mul_pow]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi := hT.toLinearMap.nonneg_eigenvalues rfl i
  have he := hT.toLinearMap.isSymmetric.eigenvectorBasis_apply_self_apply rfl x i
  change (b.repr (T x)) i = _ at he
  change ‖(b.repr (T x)) i‖^2 ≤ _
  rw [he, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hi, mul_pow]
  exact mul_le_mul_of_nonneg_right (sq_le_sq₀ hi hc |>.mpr (hval i)) (sq_nonneg _)

/-- An eigenvalue supported on at least d dimensions pays a trace factor d.
This is the precise spectral normalization needed for the global filter. -/
theorem norm_le_trace_div (T : E →L[ℂ] E) (hT : T.IsPositive) (d : ℕ) (hd : 0 < d)
    (hmult : ∀ μ : ℂ, Module.End.HasEigenvalue T.toLinearMap μ →
      d ≤ Module.finrank ℂ (Module.End.eigenspace T.toLinearMap μ)) :
    ‖T‖ ≤ (LinearMap.trace ℂ E T.toLinearMap).re / d := by
  have htrace : 0 ≤ (LinearMap.trace ℂ E T.toLinearMap).re :=
    (Complex.nonneg_iff.mp hT.toLinearMap.trace_nonneg).1
  apply positive_norm_le_of_eigenvalues T hT _ (div_nonneg htrace (by positivity))
  intro i
  let μ := hT.toLinearMap.isSymmetric.eigenvalues rfl i
  have hμ : 0 ≤ μ := hT.toLinearMap.nonneg_eigenvalues rfl i
  have hcount := hmult (μ : ℂ) (hT.toLinearMap.isSymmetric.hasEigenvalue_eigenvalues rfl i)
  have hcard := hT.toLinearMap.isSymmetric.card_filter_eigenvalues_eq rfl (μ : ℂ)
  rw [← hcard] at hcount
  simp only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_inj] at hcount
  apply (le_div_iff₀ (by exact_mod_cast hd)).mpr
  calc
    μ * (d : ℝ) ≤ μ * ((Finset.univ.filter fun j =>
      hT.toLinearMap.isSymmetric.eigenvalues rfl j = μ).card : ℕ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcount) hμ
    _ = ∑ j ∈ Finset.univ.filter (fun j =>
      hT.toLinearMap.isSymmetric.eigenvalues rfl j = μ),
        hT.toLinearMap.isSymmetric.eigenvalues rfl j := by
      symm
      calc
        _ = ∑ j ∈ Finset.univ.filter (fun j =>
          hT.toLinearMap.isSymmetric.eigenvalues rfl j = μ), μ :=
            Finset.sum_congr rfl (fun j hj => (Finset.mem_filter.mp hj).2)
        _ = _ := by simp [nsmul_eq_mul, mul_comm]
    _ ≤ ∑ j, hT.toLinearMap.isSymmetric.eigenvalues rfl j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => hT.toLinearMap.nonneg_eigenvalues rfl j)
    _ = _ := (hT.toLinearMap.isSymmetric.re_trace_eq_sum_eigenvalues rfl).symm

end RowColumn.SpectralMultiplicity
noncomputable section
open scoped ComplexOrder
namespace RowColumn.SpectralMultiplicity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma trace_compression (T : E →L[ℂ] E) (F : Submodule ℂ E) :
    LinearMap.trace ℂ F (F.orthogonalProjectionOnto ∘L T ∘L F.subtypeL).toLinearMap =
      LinearMap.trace ℂ E (T ∘L F.starProjection).toLinearMap := by
  have he := LinearMap.trace_comp_comm' (T.toLinearMap ∘ₗ F.subtype)
    F.orthogonalProjectionOnto.toLinearMap
  exact he

lemma trace_compression_le (T : E →L[ℂ] E) (hT : T.IsPositive)
    (F : Submodule ℂ E) :
    (LinearMap.trace ℂ F (F.orthogonalProjectionOnto ∘L T ∘L F.subtypeL).toLinearMap).re ≤
      (LinearMap.trace ℂ E T.toLinearMap).re := by
  have hp := (hT.orthogonalProjectionOnto_comp Fᗮ).toLinearMap.trace_nonneg
  have hn := (Complex.nonneg_iff.mp hp).1
  rw [trace_compression] at hn ⊢
  have he : F.starProjection + Fᗮ.starProjection = (1 : E →L[ℂ] E) := by
    ext x
    exact F.starProjection_add_starProjection_orthogonal x
  have ht : T ∘L F.starProjection + T ∘L Fᗮ.starProjection = T := by
    rw [← ContinuousLinearMap.comp_add, he]
    rfl
  have htr := congrArg (fun S : E →L[ℂ] E => (LinearMap.trace ℂ E S.toLinearMap).re) ht
  simp only [ContinuousLinearMap.toLinearMap_add, map_add, Complex.add_re] at htr
  linarith

lemma restrict_positive (T : E →L[ℂ] E) (hT : T.IsPositive)
    (F : Submodule ℂ E) (hF : ∀ x ∈ F, T x ∈ F) : (T.restrict hF).IsPositive := by
  have he : T.restrict hF = F.orthogonalProjectionOnto ∘L T ∘L F.subtypeL := by
    ext x
    change T x = F.starProjection (T x)
    exact (F.starProjection_eq_self_iff.mpr (hF x x.property)).symm
  rw [he]
  exact hT.orthogonalProjectionOnto_comp F

lemma trace_restrict_le (T : E →L[ℂ] E) (hT : T.IsPositive)
    (F : Submodule ℂ E) (hF : ∀ x ∈ F, T x ∈ F) :
    (LinearMap.trace ℂ F (T.restrict hF).toLinearMap).re ≤
      (LinearMap.trace ℂ E T.toLinearMap).re := by
  have he : T.restrict hF = F.orthogonalProjectionOnto ∘L T ∘L F.subtypeL := by
    ext x
    change T x = F.starProjection (T x)
    exact (F.starProjection_eq_self_iff.mpr (hF x x.property)).symm
  rw [he]
  exact trace_compression_le T hT F

end RowColumn.SpectralMultiplicity

end
end
end
end
end
end
end


section
noncomputable section
open scoped ComplexOrder
namespace RowColumn.FiniteStarAlgebra
variable {G V E : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

instance algebraFiniteDimensional (A : StarSubalgebra ℂ (E →L[ℂ] E)) : FiniteDimensional ℂ A :=
  FiniteDimensional.of_injective (algebraToEnd A) (algebraToEnd_injective A)

instance algebraIsClosed (A : StarSubalgebra ℂ (E →L[ℂ] E)) : IsClosed (A : Set (E →L[ℂ] E)) :=
  A.toSubalgebra.toSubmodule.closed_of_finiteDimensional

lemma supported_restriction_norm (A : StarSubalgebra ℂ (E →L[ℂ] E)) (F : Submodule ℂ E)
    (φ : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (q : A) (hs : star q=q) (hqq : q*q=q) (hc : ∀ a, q*a=a*q)
    (hq : φ q=1) (hkill : ∀ a : A, φ a=0 → q*a=0) (a : A) :
    ‖q*a‖ = ‖φ a‖ := by
  let J : NonUnitalStarSubalgebra ℂ A :=
    { carrier := {x | q*x=x}
      zero_mem' := mul_zero q
      add_mem' := by intro x y hx hy; change q*(x+y)=x+y; rw [mul_add,hx,hy]
      mul_mem' := by intro x y hx hy; change q*(x*y)=x*y; rw [← mul_assoc,hx]
      smul_mem' := by intro c x hx; change q*(c • x)=c • x; rw [mul_smul_comm,hx]
      star_mem' := by
        intro x hx
        change q*star x=star x
        rw [hc]
        simpa only [star_mul,hs] using congrArg star hx }
  let : IsClosed (J : Set A) := isClosed_eq (continuous_const.mul continuous_id) continuous_id
  let ψ : J →⋆ₙₐ[ℂ] (F →L[ℂ] F) := φ.toNonUnitalStarAlgHom.comp (NonUnitalStarSubalgebraClass.subtype J)
  have hinj : Function.Injective ψ := by
    intro x y h
    apply Subtype.ext
    have he : φ ((x : A)-(y : A))=0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr h
    have hz := hkill _ he
    change q*((x : A)-(y : A))=0 at hz
    rw [mul_sub,x.property,y.property] at hz
    exact sub_eq_zero.mp hz
  let x : J := ⟨q*a,by change q*(q*a)=q*a; rw [← mul_assoc,hqq]⟩
  have hh := NonUnitalStarAlgHom.norm_map ψ hinj x
  change ‖φ (q*a)‖ = ‖q*a‖ at hh
  rw [map_mul,hq,one_mul] at hh
  exact hh.symm

/-- The exact dimension normalization of the occupied-board global filter.
No highest-weight entropy or Schur--Weyl hypothesis is required: restriction
of the supported algebra is faithful, and every eigenspace contains the
irreducible carrier. -/
theorem exists_isotypic_filter (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (τ : Representation ℂ G E)
    (hτ : ∀ g x y, inner ℂ (τ g x) (τ g y) = inner ℂ x y)
    (A : StarSubalgebra ℂ (E →L[ℂ] E))
    (hA : ∀ a : A, ∀ g x, (a : E →L[ℂ] E) (τ g x) = τ g ((a : E →L[ℂ] E) x)) :
    ∃ q : A, star q = q ∧ q*q=q ∧ (∀ a, q*a=a*q) ∧
      (∀ x ∈ Isotypic.carrier ρ τ, (q : E →L[ℂ] E) x = x) ∧
      ∀ a : A, (a : E →L[ℂ] E).IsPositive →
        ‖q*a‖ ≤ (physicalTrace A a).re / Module.finrank ℂ V := by
  let : Nontrivial V := by
    let := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
    exact ρ.asModuleEquiv.symm.toEquiv.nontrivial
  let F := Isotypic.carrier ρ τ
  have hF : ∀ a : A, ∀ x ∈ F, (a : E →L[ℂ] E) x ∈ F := fun a =>
    Isotypic.carrier_commutant ρ τ (a : E →L[ℂ] E).toLinearMap (hA a)
  let φ := restrictHom A F hF
  obtain ⟨q,hqs,hqq,hqc,hq,hkill⟩ := exists_central_support A F hF
  refine ⟨q,hqs,hqq,hqc,?_,?_⟩
  · intro x hx
    exact congrArg Subtype.val (congrArg (fun T : F →L[ℂ] F => T ⟨x,hx⟩) hq)
  · intro a ha
    rw [supported_restriction_norm A F φ q hqs hqq hqc hq hkill a]
    have hp : (φ a).IsPositive := SpectralMultiplicity.restrict_positive
      (a : E →L[ℂ] E) ha F (hF a)
    apply (SpectralMultiplicity.norm_le_trace_div (φ a) hp (Module.finrank ℂ V)
      (Module.finrank_pos) ?_).trans
    · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact SpectralMultiplicity.trace_restrict_le (a : E →L[ℂ] E) ha F (hF a)
    · intro μ hμ
      apply Isotypic.eigenspace_finrank ρ (Isotypic.restricted ρ τ)
        (Isotypic.restricted_isotypic ρ τ) (Isotypic.restricted_unitary ρ τ hτ)
        (φ a).toLinearMap _ μ hμ
      intro g x
      apply Subtype.ext
      exact hA a g x

end RowColumn.FiniteStarAlgebra
noncomputable section
open scoped BigOperators ComplexOrder
namespace RowColumn.UnitaryFrame
variable {A G E : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [FiniteDimensional ℂ A] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The finite Fourier reconstruction bound for arbitrary Hilbert-valued
linear maps, in particular weighted Hilbert–Schmidt sandwich maps. -/
theorem reconstruction_hilbert_bound (τ : A →ₗ[ℂ] ℂ) (core : InnerProductSpace.Core ℂ A)
    (hinner : ∀ x y, core.inner x y = τ (star x*y))
    (u : G →* unitary A)
    (hspan : Submodule.span ℂ (Set.range fun g : G => (u g : A)) = ⊤)
    (B : A) (F : A →ₗ[ℂ] E) (R : ℝ) (hR : 0 ≤ R)
    (hU : ∀ g, ‖F (u g : A)‖ ≤ R) :
    ‖F B‖ ≤ 4 * (Module.finrank ℂ A : ℝ) * ‖B‖ * R := by
  let ℓ := (innerSL ℂ (F B)).toLinearMap.comp F
  have hu (g : G) : ‖ℓ (u g : A)‖ ≤ ‖F B‖ * R :=
    (norm_inner_le_norm (F B) (F (u g : A))).trans
      (mul_le_mul_of_nonneg_left (hU g) (norm_nonneg _))
  have hh := reconstruction_bound τ core hinner u hspan B ℓ (‖F B‖ * R)
    (mul_nonneg (norm_nonneg _) hR) hu
  change ‖inner ℂ (F B) (F B)‖ ≤ _ at hh
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _)] at hh
  by_cases hz : ‖F B‖=0
  · rw [hz]
    positivity
  · have hp : 0 < ‖F B‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith [hh]

end RowColumn.UnitaryFrame
noncomputable section
namespace RowColumn
variable {A : Type*} [CStarAlgebra A]

lemma supported_fourth (q F : A) (hq : q*q=q) (hc : Commute q F) :
    (q*F)^4 = q*(F^4) := by
  rw [hc.mul_pow]
  have hq4 : q^4=q := by calc
    q^4=(q*q)*(q*q) := by noncomm_ring
    _=q := by rw [hq,hq]
  rw [hq4]

/-- The quarter-root estimate at the level of the genuine operator norm.
The two fourth-moment bounds imply the exact squared sandwich bound. -/
theorem filterNorm_sq (q F G : A) (hsq : IsSelfAdjoint q) (hqq : q*q=q)
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) (hcF : Commute q F) (hcG : Commute q G)
    (d : ℝ) (_ : 0 < d) (hFb : ‖q * F^4‖ ≤ 1/d) (hGb : ‖q * G^4‖ ≤ 1/d) :
    ‖F*q*G‖^2 ≤ 1/d := by
  have hsF : IsSelfAdjoint (q*F) := by
    change star (q*F)=q*F
    rw [star_mul,hsq.star_eq,hF.star_eq,hcF.eq]
  have hsG : IsSelfAdjoint (q*G) := by
    change star (q*G)=q*G
    rw [star_mul,hsq.star_eq,hG.star_eq,hcG.eq]
  have hnF : ‖q*F‖^4 ≤ 1/d := by
    have hn : ‖(q*F)^4‖=‖q*F‖^4 := by simpa using hsF.norm_pow_two_pow 2
    rw [← hn,supported_fourth q F hqq hcF]
    exact hFb
  have hnG : ‖q*G‖^4 ≤ 1/d := by
    have hn : ‖(q*G)^4‖=‖q*G‖^4 := by simpa using hsG.norm_pow_two_pow 2
    rw [← hn,supported_fourth q G hqq hcG]
    exact hGb
  have he : F*q*G=(q*F)*(q*G) := by
    calc
      _ = F*(q*q)*G := by rw [hqq]
      _ = (F*q)*(q*G) := by noncomm_ring
      _ = _ := by rw [hcF.eq]
  have hn := norm_mul_le (q*F) (q*G)
  rw [← he] at hn
  have hp : (‖q*F‖*‖q*G‖)^2 ≤ 1/d := by
    have ha := sq_nonneg (‖q*F‖^2-‖q*G‖^2)
    nlinarith
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hp
end RowColumn

end
end
end
end

end OAI
