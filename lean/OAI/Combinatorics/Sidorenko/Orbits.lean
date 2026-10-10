import OAI.Combinatorics.Sidorenko.TripleRanks

namespace OAI

namespace SidorenkoCounterexample
open Module
open scoped BigOperators

/-- Counting a finite set by uniformly bounded fibers. -/
theorem card_le_card_mul_of_fibers {A B : Type*} [Finite A] [Finite B]
    (f : A → B) (m : ℕ) (h : ∀ b, Nat.card {a : A // f a = b} ≤ m) :
    Nat.card A ≤ Nat.card B * m := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  calc
    Nat.card A = Nat.card (Σ b : B, {a : A // f a = b}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ b : B, Nat.card {a : A // f a = b} := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]
    _ ≤ ∑ _b : B, m := Finset.sum_le_sum (fun b _ => h b)
    _ = Nat.card B * m := by simp [Nat.card_eq_fintype_card]

section NormSphere
variable {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]

/-- A quadratic equation with no linear term has at most two roots. -/
theorem square_fiber_card (a : K) : Nat.card {x : K // x^2 = a} ≤ 2 := by
  classical
  by_cases h : ∃ x : K, x^2 = a
  · obtain ⟨x,hx⟩ := h
    let f : {z : K // z^2 = a} → (↑({x,-x} : Finset K)) := fun z =>
      ⟨z.val,by
        have hh : z.val = x ∨ z.val = -x := sq_eq_sq_iff_eq_or_eq_neg.mp (z.property.trans hx.symm)
        simpa only [Finset.mem_insert,Finset.mem_singleton] using hh⟩
    have hf : Function.Injective f := by
      intro z w he
      apply Subtype.ext
      exact congrArg (fun t : ↑({x,-x} : Finset K) => (t : K)) he
    calc
      _ ≤ Nat.card (↑({x,-x} : Finset K)) := Nat.card_le_card_of_injective f hf
      _ = ({x,-x} : Finset K).card := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_coe _
      _ ≤ 2 := Finset.card_le_two
  · have he : IsEmpty {x : K // x^2 = a} := ⟨fun x => h ⟨x.val,x.property⟩⟩
    let := he
    simp

omit [FiniteDimensional K E] in
/-- Split along any vector of nonzero norm; this bounds a norm sphere by
exactly two choices over every point of the orthogonal complement. -/
theorem norm_sphere_count (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (x : E) (hx : B x x ≠ 0) (a : K) :
    Nat.card {v : E // B v v = a} ≤
      2 * Nat.card (B.orthogonal (K ∙ x)) := by
  classical
  have hx0 : x ≠ 0 := by intro hh; subst x; simp at hx
  let P := B.orthogonal (K ∙ x)
  let c : ((K ∙ x) × P) ≃ₗ[K] E :=
    (K ∙ x).prodEquivOfIsCompl P (B.isCompl_span_singleton_orthogonal hx)
  let e : (K × P) ≃ₗ[K] E :=
    ((LinearEquiv.toSpanNonzeroSingleton K E x hx0).prodCongr (LinearEquiv.refl K P)).trans c
  have he (z : K × P) : e z = z.1 • x + z.2.val := rfl
  have hnorm (z : K × P) : B (e z) (e z) = z.1^2 * B x x + B z.2.val z.2.val := by
    have h1 : B x z.2.val = 0 := z.2.property x (Submodule.mem_span_singleton_self x)
    have h2 : B z.2.val x = 0 := hs.eq _ _ ▸ h1
    rw [he]
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
      smul_eq_mul,h1,h2,mul_zero,add_zero,zero_add]
    ring
  let f : {v : E // B v v = a} → P := fun v => (e.symm v.val).2
  have hf (p : P) : Nat.card {v : {v : E // B v v = a} // f v = p} ≤ 2 := by
    let g : {v : {v : E // B v v = a} // f v = p} →
        {t : K // t^2 = (a - B p.val p.val) / B x x} := fun v =>
      ⟨(e.symm v.val.val).1,by
        have hh := hnorm (e.symm v.val.val)
        have hv : (e.symm v.val.val).2 = p := v.property
        rw [e.apply_symm_apply,v.val.property,hv] at hh
        apply (eq_div_iff hx).mpr
        linear_combination -hh⟩
    have hg : Function.Injective g := by
      intro v w h
      apply Subtype.ext
      apply Subtype.ext
      apply e.symm.injective
      apply Prod.ext
      · exact congrArg Subtype.val h
      · exact v.property.trans w.property.symm
    exact (Nat.card_le_card_of_injective g hg).trans (square_fiber_card _)
  exact (card_le_card_mul_of_fibers f 2 hf).trans_eq (Nat.mul_comm _ _)



theorem norm_sphere_count_pow (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (x : E) (hx : B x x ≠ 0) (a : K) :
    Nat.card {v : E // B v v = a} ≤ 2 * Fintype.card K ^ (finrank K E - 1) := by
  have hx0 : x ≠ 0 := by intro hh; subst x; simp at hx
  have hd := Submodule.finrank_add_eq_of_isCompl (B.isCompl_span_singleton_orthogonal hx)
  rw [finrank_span_singleton hx0] at hd
  have hp : finrank K (B.orthogonal (K ∙ x)) = finrank K E - 1 := by omega
  have hc : Nat.card (B.orthogonal (K ∙ x)) = Fintype.card K ^ (finrank K E - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := K), hp, Nat.card_eq_fintype_card]
  exact (norm_sphere_count B hs x hx a).trans_eq (congrArg (2 * ·) hc)

end NormSphere
section Isometries
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- Linear automorphisms preserving a specified bilinear form. -/
def BilinAut (B : LinearMap.BilinForm K E) :=
  {e : E ≃ₗ[K] E // ∀ x y, B (e x) (e y) = B x y}

instance (B : LinearMap.BilinForm K E) [Finite E] : Finite (BilinAut B) := by
  apply Finite.of_injective (fun e : BilinAut B => (e.val : E → E))
  intro e f h
  apply Subtype.ext
  exact LinearEquiv.ext (congrFun h)

noncomputable def restrictBilinAut (B : LinearMap.BilinForm K E)
    (x : E) (e : BilinAut B) (hfix : e.val x = x) :
    BilinAut (B.restrict (B.orthogonal (K ∙ x))) := by
  let P := B.orthogonal (K ∙ x)
  have hp : ∀ z ∈ P, e.val z ∈ P := by
    intro z hz a ha
    obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp ha
    have hh : B x (e.val z) = 0 := by
      calc
        _ = B (e.val x) (e.val z) := by rw [hfix]
        _ = B x z := e.property x z
        _ = 0 := hz x (Submodule.mem_span_singleton_self x)
    simp [hh]
  let g : P →ₗ[K] P := e.val.toLinearMap.restrict hp
  have hg : Function.Injective g := by
    intro z w h
    apply Subtype.ext
    exact e.val.injective (congrArg Subtype.val h)
  let f : P ≃ₗ[K] P := LinearEquiv.ofBijective g
    ⟨hg,LinearMap.injective_iff_surjective.mp hg⟩
  refine ⟨f,?_⟩
  intro z w
  exact e.property z.val w.val

@[simp] theorem restrictBilinAut_apply (B : LinearMap.BilinForm K E)
    (x : E) (e : BilinAut B) (hfix : e.val x = x)
    (z : B.orthogonal (K ∙ x)) :
    ((restrictBilinAut B x e hfix).val z).val = e.val z.val := rfl

/-- An isometry fixing a nonzero-norm vector is determined by its action
on the orthogonal complement. -/
theorem restrictBilinAut_injective (B : LinearMap.BilinForm K E)
    (x : E) (hx : B x x ≠ 0) :
    Function.Injective (fun e : {e : BilinAut B // e.val x = x} =>
      restrictBilinAut B x e.val e.property) := by
  intro e f h
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  have hz : z ∈ (K ∙ x) ⊔ B.orthogonal (K ∙ x) := by
    rw [(B.isCompl_span_singleton_orthogonal hx).sup_eq_top]
    trivial
  obtain ⟨a,ha,p,hp,rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp ha
  have hh := congrArg (fun g : BilinAut (B.restrict (B.orthogonal (K ∙ x))) =>
    (g.val (⟨p,hp⟩ : B.orthogonal (K ∙ x))).val) h
  change e.val.val p = f.val.val p at hh
  simp only [map_add,map_smul,e.property,f.property,hh]

noncomputable def relativeBilinAut (B : LinearMap.BilinForm K E)
    (e f : BilinAut B) : BilinAut B :=
  ⟨e.val.trans f.val.symm,by
    intro x y
    have hf := f.property (f.val.symm (e.val x)) (f.val.symm (e.val y))
    simp only [LinearEquiv.apply_symm_apply] at hf
    exact hf.symm.trans (e.property x y)⟩

omit [FiniteDimensional K E] in
theorem relativeBilinAut_injective (B : LinearMap.BilinForm K E) (f : BilinAut B) :
    Function.Injective (fun e => relativeBilinAut B e f) := by
  intro e g h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hh := congrArg (fun a : BilinAut B => f.val (a.val x)) h
  simpa only [relativeBilinAut,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply] using hh

variable [Finite E]

/-- The fibers of evaluation at x inject into the stabilizer of x by
translation by any chosen member of the fiber. -/
theorem bilinAut_eval_fiber_bound (B : LinearMap.BilinForm K E) (x y : E)
    (hx : B x x ≠ 0) :
    Nat.card {e : BilinAut B // e.val x = y} ≤
      Nat.card (BilinAut (B.restrict (B.orthogonal (K ∙ x)))) := by
  classical
  by_cases hn : Nonempty {e : BilinAut B // e.val x = y}
  · let e0 := hn.some
    let f : {e : BilinAut B // e.val x = y} → {e : BilinAut B // e.val x = x} := fun e =>
      ⟨relativeBilinAut B e.val e0.val,by
        change e0.val.val.symm (e.val.val x) = x
        exact (congrArg e0.val.val.symm (e.property.trans e0.property.symm)).trans
          (e0.val.val.symm_apply_apply x)⟩
    have hf : Function.Injective f := by
      intro e g h
      apply Subtype.ext
      apply relativeBilinAut_injective B e0.val
      exact congrArg Subtype.val h
    exact (Nat.card_le_card_of_injective f hf).trans
      (Nat.card_le_card_of_injective _ (restrictBilinAut_injective B x hx))
  · have : IsEmpty {e : BilinAut B // e.val x = y} := not_nonempty_iff.mp hn
    let := this
    simp

/-- A nonzero-norm vector splits the cardinality estimate into its norm
sphere and the isometries of the smaller orthogonal complement. -/
theorem bilinAut_step (B : LinearMap.BilinForm K E) (x : E) (hx : B x x ≠ 0) :
    Nat.card (BilinAut B) ≤ Nat.card {y : E // B y y = B x x} *
      Nat.card (BilinAut (B.restrict (B.orthogonal (K ∙ x)))) := by
  let s : BilinAut B → {y : E // B y y = B x x} := fun e => ⟨e.val x,e.property x x⟩
  apply card_le_card_mul_of_fibers s
  intro y
  let f : {e : BilinAut B // s e = y} → {e : BilinAut B // e.val x = y.val} :=
    fun e => ⟨e.val,congrArg Subtype.val e.property⟩
  have hf : Function.Injective f := by
    intro e g h
    apply Subtype.ext
    exact congrArg (fun t : {e : BilinAut B // e.val x = y.val} => t.val) h
  exact (Nat.card_le_card_of_injective f hf).trans (bilinAut_eval_fiber_bound B x y.val hx)

variable [Fintype K] [Invertible (2 : K)]




theorem bilinAut_card_bound (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (hB : B.Nondegenerate) :
    Nat.card (BilinAut B) ≤ 2 ^ finrank K E * Fintype.card K ^ (finrank K E).choose 2 := by
  suffices ∀ d, finrank K E = d →
      Nat.card (BilinAut B) ≤ 2 ^ d * Fintype.card K ^ d.choose 2 by exact this _ rfl
  intro d hd
  induction d generalizing E with
  | zero =>
    have : Subsingleton E := Module.finrank_zero_iff.mp hd
    have : Subsingleton (BilinAut B) := by
      refine ⟨fun e f => ?_⟩
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      exact Subsingleton.elim _ _
    simpa using Nat.card_le_card_of_injective (fun _ : BilinAut B => ())
      (fun _ _ _ => Subsingleton.elim _ _)
  | succ d ih =>
    have hB0 : B ≠ 0 := by
      intro hh
      have hz : ∀ x : E, x = 0 := by
        intro x
        apply hB.1
        intro y
        rw [hh]
        rfl
      have hh0 : finrank K E = 0 := (finrank_zero_iff_forall_zero).mpr hz
      omega
    obtain ⟨x,hx⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero hB0 (LinearMap.BilinForm.isSymm_iff.mp hs)
    have hx0 : x ≠ 0 := by intro hh; subst x; simp at hx
    let P := B.orthogonal (K ∙ x)
    have hP : finrank K P = d := by
      change finrank K (B.orthogonal (K ∙ x)) = d
      have hh := Submodule.finrank_add_eq_of_isCompl (B.isCompl_span_singleton_orthogonal hx)
      rw [finrank_span_singleton hx0,hd] at hh
      omega
    have hp := ih (B.restrict P) (by constructor; intro x y; exact hs.eq x.val y.val)
      (B.restrict_nondegenerate_orthogonal_spanSingleton hB hs.isRefl hx) hP
    have hn := norm_sphere_count_pow B hs x hx (B x x)
    rw [hd,Nat.add_sub_cancel] at hn
    calc
      _ ≤ Nat.card {y : E // B y y = B x x} * Nat.card (BilinAut (B.restrict P)) :=
        bilinAut_step B x hx
      _ ≤ (2 * Fintype.card K ^ d) * (2^d * Fintype.card K ^ d.choose 2) :=
        Nat.mul_le_mul hn hp
      _ = 2 ^ (d+1) * Fintype.card K ^ (d+1).choose 2 := by
        rw [Nat.choose_succ_succ,Nat.choose_one_right,pow_add,pow_succ]
        ring

end Isometries
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FormOrbits
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- Evaluate a linear automorphism on a fixed basis. -/
noncomputable def linearAutTuple : (E ≃ₗ[K] E) →
    {v : Fin (finrank K E) → E // LinearIndependent K v} := fun e =>
  ⟨fun i => e (finBasis K E i), (finBasis K E).linearIndependent.map' e.toLinearMap
    (LinearMap.ker_eq_bot.mpr e.injective)⟩

theorem linearAutTuple_bijective : Function.Bijective (linearAutTuple (K := K) (E := E)) := by
  constructor
  · intro e f h
    apply LinearEquiv.toLinearMap_injective
    apply (finBasis K E).ext
    intro i
    exact congrFun (congrArg Subtype.val h) i
  · intro v
    have hspan : Submodule.span K (Set.range v.val) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card v.property,Fintype.card_fin]
    let b : Basis (Fin (finrank K E)) K E := Basis.mk v.property (by rw [hspan])
    refine ⟨(finBasis K E).equiv b (Equiv.refl _),?_⟩
    apply Subtype.ext
    funext i
    simp [linearAutTuple,b]

variable [Fintype K] [Finite E]

/-- General linear group order, obtained directly by counting ordered bases. -/
theorem linearAut_card : Nat.card (E ≃ₗ[K] E) =
    ∏ i : Fin (finrank K E), (Fintype.card K ^ finrank K E - Fintype.card K ^ i.val) := by
  rw [Nat.card_congr (Equiv.ofBijective _ (linearAutTuple_bijective (K := K) (E := E)))]
  exact card_linearIndependent le_rfl

/-- The congruence orbit of the literal form, not merely its rank stratum. -/
abbrev FormOrbit (B : LinearMap.BilinForm K E) :=
  {C : LinearMap.BilinForm K E // ∃ e : E ≃ₗ[K] E, C = B.comp e.toLinearMap e.toLinearMap}

instance linearAut_finite : Finite (E ≃ₗ[K] E) :=
  Finite.of_injective (fun e : E ≃ₗ[K] E => (e : E → E))
    (fun _ _ h => LinearEquiv.ext (congrFun h))

instance formOrbit_finite (B : LinearMap.BilinForm K E) : Finite (FormOrbit B) :=
  Finite.of_injective (fun C : FormOrbit B => fun x y => C.val x y) (by
    intro C D h
    apply Subtype.ext
    ext x y
    exact congrFun (congrFun h x) y)

def formOrbitMap (B : LinearMap.BilinForm K E) (e : E ≃ₗ[K] E) : FormOrbit B :=
  ⟨B.comp e.toLinearMap e.toLinearMap,⟨e,rfl⟩⟩

omit [FiniteDimensional K E] [Fintype K] in
/-- Every orbit-map fiber embeds into the isometry group; this is the
inequality direction of orbit--stabilizer, without assuming a form classification. -/
theorem formOrbit_fiber_bound (B : LinearMap.BilinForm K E) (C : FormOrbit B) :
    Nat.card {e : E ≃ₗ[K] E // formOrbitMap B e = C} ≤ Nat.card (BilinAut B) := by
  classical
  obtain ⟨e0,he0⟩ := C.property
  let f : {e : E ≃ₗ[K] E // formOrbitMap B e = C} → BilinAut B := fun e =>
    ⟨e0.symm.trans e.val,by
      intro x y
      have hh := congrArg (fun D : FormOrbit B => D.val (e0.symm x) (e0.symm y)) e.property
      change B (e.val (e0.symm x)) (e.val (e0.symm y)) = C.val (e0.symm x) (e0.symm y) at hh
      rw [he0] at hh
      simpa only [LinearMap.BilinForm.comp_apply,LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply,LinearEquiv.trans_apply] using hh⟩
  apply Nat.card_le_card_of_injective f
  intro e g h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hh := congrArg (fun a : BilinAut B => a.val (e0 x)) h
  simpa only [f,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] using hh

omit [FiniteDimensional K E] in
theorem formOrbit_card_mul_bound (B : LinearMap.BilinForm K E) :
    Nat.card (E ≃ₗ[K] E) ≤ Nat.card (FormOrbit B) * Nat.card (BilinAut B) :=
  card_le_card_mul_of_fibers (formOrbitMap B) _ (formOrbit_fiber_bound B)



theorem linearAut_card_lower : Fintype.card K ^ (finrank K E * finrank K E) ≤
    2 ^ finrank K E * Nat.card (E ≃ₗ[K] E) := by
  rw [linearAut_card]
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hfac (i : Fin (finrank K E)) : Fintype.card K ^ finrank K E ≤
      2 * (Fintype.card K ^ finrank K E - Fintype.card K ^ i.val) := by
    have hle : Fintype.card K ^ (i.val+1) ≤ Fintype.card K ^ finrank K E :=
      Nat.pow_le_pow_right (by omega) i.isLt
    have hh : 2 * Fintype.card K ^ i.val ≤ Fintype.card K ^ finrank K E := by
      calc
        _ ≤ Fintype.card K * Fintype.card K ^ i.val := Nat.mul_le_mul_right _ hq
        _ = Fintype.card K ^ (i.val+1) := by rw [pow_succ]; ring
        _ ≤ _ := hle
    omega
  calc
    _ = ∏ _i : Fin (finrank K E), Fintype.card K ^ finrank K E := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul]
    _ ≤ ∏ i : Fin (finrank K E), 2 * (Fintype.card K ^ finrank K E - Fintype.card K ^ i.val) :=
      Finset.prod_le_prod (fun i _ => hfac i)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

variable [Invertible (2 : K)]

/-- Every nonsingular symmetric form class occupies a fixed positive
proportion of the full symmetric-form space, uniformly in the finite field.
The deliberately coarse constant 4⁻ᵈ is enough for the manuscript's tail bound. -/
theorem formOrbit_card_lower (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (hB : B.Nondegenerate) :
    Fintype.card K ^ (finrank K E+1).choose 2 ≤
      4 ^ finrank K E * Nat.card (FormOrbit B) := by
  let d := finrank K E
  let q := Fintype.card K
  have h1 := (linearAut_card_lower (K := K) (E := E)).trans
    (Nat.mul_le_mul_left (2^d) (formOrbit_card_mul_bound B))
  have h2 := Nat.mul_le_mul_left (2^d * Nat.card (FormOrbit B)) (bilinAut_card_bound B hs hB)
  have hh : q^(d*d) ≤ (4^d * Nat.card (FormOrbit B)) * q^d.choose 2 := by
    calc
      _ ≤ 2^d * (Nat.card (FormOrbit B) * Nat.card (BilinAut B)) := h1
      _ = (2^d * Nat.card (FormOrbit B)) * Nat.card (BilinAut B) := by ring
      _ ≤ (2^d * Nat.card (FormOrbit B)) * (2^d * q^d.choose 2) := h2
      _ = _ := by rw [show (4 : ℕ) = 2*2 from rfl,mul_pow]; ring
  have hd : d*d = (d+1).choose 2 + d.choose 2 := by
    have hc : ∀ n : ℕ, n*n = n + 2*n.choose 2 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Nat.choose_succ_succ,Nat.choose_one_right]
        nlinarith
    rw [Nat.choose_succ_succ,Nat.choose_one_right]
    linear_combination hc d
  rw [hd,pow_add] at hh
  exact Nat.le_of_mul_le_mul_right hh (pow_pos Fintype.card_pos _)

end FormOrbits
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section TransverseForms
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Graph coordinates for a transverse Lagrangian, with the full symmetric
form retained rather than only its dimension or square class. -/
theorem fullGraph_selforthogonal (B : LinearMap.BilinForm K V) (hs : B.IsSymm) :
    canonicalSymplectic.orthogonal B.graph = B.graph := by
  ext x
  constructor
  · intro hx
    apply (B.mem_graph_iff x).mpr
    ext y
    have hh := hx (y,B y) (by rfl)
    change x.2 y - B y x.1 = 0 at hh
    exact (sub_eq_zero.mp hh).trans (hs.eq y x.1)
  · intro hx y hy
    have hx' := (B.mem_graph_iff x).mp hx
    have hy' := (B.mem_graph_iff y).mp hy
    change x.2 y.1 - y.2 x.1 = 0
    rw [hx',hy',hs.eq]
    exact sub_self _

theorem fullGraph_injective : Function.Injective
    (fun B : LinearMap.BilinForm K V => B.graph) := by
  intro B C h
  change B.graph = C.graph at h
  apply LinearMap.ext
  intro x
  have hx : (x,B x) ∈ C.graph := by rw [← h]; rfl
  exact (C.mem_graph_iff _).mp hx

/-- The coordinate action corresponding to a change of basis of a form. -/
def formCoordinateEquiv (g : V ≃ₗ[K] V) :
    (V × Module.Dual K V) ≃ₗ[K] (V × Module.Dual K V) :=
  g.symm.prodCongr g.dualMap

theorem formCoordinateEquiv_isometry (g : V ≃ₗ[K] V) (x y : V × Module.Dual K V) :
    canonicalSymplectic (formCoordinateEquiv g x) (formCoordinateEquiv g y) =
      canonicalSymplectic x y := by
  simp [formCoordinateEquiv,canonicalSymplectic_apply]

theorem fullGraph_congruence (B : LinearMap.BilinForm K V) (g : V ≃ₗ[K] V) :
    B.graph.map (formCoordinateEquiv g).toLinearMap = (B.comp g.toLinearMap g.toLinearMap).graph := by
  apply subspace_map_eq_of_mem_iff
  intro x
  change g.dualMap x.2 = (B.comp g.toLinearMap g.toLinearMap) (g.symm x.1) ↔ x.2 = B x.1
  constructor
  · intro h
    ext y
    have hh := LinearMap.congr_fun h (g.symm y)
    simpa [LinearEquiv.dualMap_apply,LinearMap.BilinForm.comp_apply] using hh
  · intro h
    ext y
    simp [LinearEquiv.dualMap_apply,LinearMap.BilinForm.comp_apply,h]

end TransverseForms
section TransverseTripleCoordinates
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)

/-- Three pairwise transverse Lagrangians admit literal symmetric-form
coordinates; transversality to both axes is exactly nonsingularity. -/
theorem exists_transverse_triple_form (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M N : Submodule K E) (hL : ω.orthogonal L = L)
    (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥) :
    ∃ (e : (L × Module.Dual K L) ≃ₗ[K] E) (B : LinearMap.BilinForm K L),
      B.IsSymm ∧ B.Nondegenerate ∧
      (∀ x, e x ∈ L ↔ x.2 = 0) ∧ (∀ x, e x ∈ M ↔ x.1 = 0) ∧
      (∀ x, e x ∈ N ↔ x.2 = B x.1) ∧
      (∀ x y, ω (e x) (e y) = canonicalSymplectic x y) := by
  obtain ⟨e,heL,heM,heform⟩ := exists_transverse_pair_coordinates ω ha hω L M hL hM hLM
  let p : N →ₗ[K] L := (LinearMap.fst K L (Module.Dual K L)).comp
    (e.symm.toLinearMap.comp N.subtype)
  have hp : Function.Injective p := by
    apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).mpr
    intro n hn
    have hm : n.val ∈ M := by
      have hh : e (e.symm n.val) ∈ M := (heM _).mpr hn
      simpa only [e.apply_symm_apply] using hh
    have hz : n.val ∈ M ⊓ N := ⟨hm,n.property⟩
    apply Subtype.ext
    change n.val = 0
    simpa only [hMN,Submodule.mem_bot] using hz
  have hd : finrank K N = finrank K L := by
    have h1 := self_orthogonal_twice_finrank ω N hω hN
    have h2 := self_orthogonal_twice_finrank ω L hω hL
    omega
  let a : N ≃ₗ[K] L := LinearEquiv.ofBijective p
    ⟨hp,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hp⟩
  let B : LinearMap.BilinForm K L := (LinearMap.snd K L (Module.Dual K L)).comp
    (e.symm.toLinearMap.comp (N.subtype.comp a.symm.toLinearMap))
  have hcoord (x : L) : e.symm (a.symm x).val = (x,B x) := by
    apply Prod.ext
    · exact a.apply_symm_apply x
    · rfl
  have hNgraph (x : L × Module.Dual K L) : e x ∈ N ↔ x.2 = B x.1 := by
    constructor
    · intro hx
      let n : N := ⟨e x,hx⟩
      have haN : a n = x.1 := by
        change (e.symm (e x)).1 = x.1
        rw [e.symm_apply_apply]
      have hh := hcoord (a n)
      rw [a.symm_apply_apply,haN] at hh
      have hh' := congrArg Prod.snd hh
      change (e.symm (e x)).2 = B x.1 at hh'
      simpa only [e.symm_apply_apply] using hh'
    · intro hx
      have hh := congrArg e (hcoord x.1)
      rw [e.apply_symm_apply,← hx] at hh
      exact hh ▸ (a.symm x.1).property
  have hs : B.IsSymm := by
    constructor
    intro x y
    have hh := hN.ge ((a.symm y).property) (a.symm x).val ((a.symm x).property)
    rw [← e.apply_symm_apply (a.symm x).val,← e.apply_symm_apply (a.symm y).val,
      heform,hcoord,hcoord] at hh
    change B y x - B x y = 0 at hh
    exact (sub_eq_zero.mp hh).symm
  have hleft (x : L) (hx : ∀ y, B x y = 0) : x = 0 := by
    have hxB : B x = 0 := by ext y; exact hx y
    have hxL : (a.symm x).val ∈ L := by
      have hh := (heL (x,B x)).mpr hxB
      have hc := congrArg e (hcoord x)
      rw [e.apply_symm_apply] at hc
      exact hc.symm ▸ hh
    have hz : (a.symm x).val ∈ L ⊓ N := ⟨hxL,(a.symm x).property⟩
    have hn0 : a.symm x = 0 := Subtype.ext (by
      change (a.symm x).val = 0
      simpa only [hLN,Submodule.mem_bot] using hz)
    have hh := congrArg a hn0
    simpa only [a.apply_symm_apply,map_zero] using hh
  refine ⟨e,B,hs,⟨hleft,?_⟩,heL,heM,hNgraph,heform⟩
  intro x hx
  exact hleft x (fun y => (hs.eq x y).trans (hx y))

end TransverseTripleCoordinates
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section FixedPairOrbit
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : Submodule K E)

/-- Third members reachable while fixing both members of the ordered pair. -/
abbrev FixedPairOrbit := {N' : Submodule K E //
  ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
    L.map e.toLinearMap = L ∧ M.map e.toLinearMap = M ∧ N.map e.toLinearMap = N'}

theorem fixedPairOrbit_selforthogonal (hN : ω.orthogonal N = N)
    (N' : FixedPairOrbit ω L M N) : ω.orthogonal N'.val = N'.val := by
  obtain ⟨e,he,_,_,hne⟩ := N'.property
  rw [←hne,orthogonal_map_of_isometry ω e he,hN]

variable [FiniteDimensional K E]

/-- Congruence classes inject into the actual third-member fiber of the
ordered symplectic orbit. No classification of forms is used. -/
theorem fixedPairOrbit_form_injection (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥) :
    ∃ B : LinearMap.BilinForm K L, B.IsSymm ∧ B.Nondegenerate ∧
      ∃ f : FormOrbit B → FixedPairOrbit ω L M N, Function.Injective f := by
  classical
  obtain ⟨e,B,hs,hB,heL,heM,heN,heform⟩ :=
    exists_transverse_triple_form ω ha hω L M N hL hM hN hLM hLN hMN
  have hgood (C : FormOrbit B) :
      ∃ f : E ≃ₗ[K] E, (∀ x y, ω (f x) (f y) = ω x y) ∧
        L.map f.toLinearMap = L ∧ M.map f.toLinearMap = M ∧
        N.map f.toLinearMap = C.val.graph.map e.toLinearMap := by
    obtain ⟨g,hg⟩ := C.property
    let f := e.symm.trans ((formCoordinateEquiv g).trans e)
    refine ⟨f,?_,?_,?_,?_⟩
    · intro x y
      change ω (e (formCoordinateEquiv g (e.symm x)))
        (e (formCoordinateEquiv g (e.symm y)))=ω x y
      rw [heform,formCoordinateEquiv_isometry,←heform,e.apply_symm_apply,e.apply_symm_apply]
    · apply subspace_map_eq_of_mem_iff f
      intro x
      change e (formCoordinateEquiv g (e.symm x)) ∈ L ↔ x ∈ L
      rw [heL]
      change g.dualMap (e.symm x).2 = 0 ↔ x ∈ L
      rw [LinearEquiv.map_eq_zero_iff]
      simpa only [e.apply_symm_apply] using (heL (e.symm x)).symm
    · apply subspace_map_eq_of_mem_iff f
      intro x
      change e (formCoordinateEquiv g (e.symm x)) ∈ M ↔ x ∈ M
      rw [heM]
      change g.symm (e.symm x).1 = 0 ↔ x ∈ M
      rw [LinearEquiv.map_eq_zero_iff]
      simpa only [e.apply_symm_apply] using (heM (e.symm x)).symm
    · apply subspace_map_eq_of_mem_iff f
      intro x
      rw [Submodule.mem_map_equiv]
      change e.symm (e (formCoordinateEquiv g (e.symm x))) ∈ C.val.graph ↔ x ∈ N
      rw [e.symm_apply_apply,hg,←fullGraph_congruence,Submodule.mem_map_equiv]
      rw [LinearEquiv.symm_apply_apply,LinearMap.mem_graph_iff]
      simpa only [e.apply_symm_apply] using (heN (e.symm x)).symm
  let f : FormOrbit B → FixedPairOrbit ω L M N :=
    fun C => ⟨C.val.graph.map e.toLinearMap,hgood C⟩
  refine ⟨B,hs,hB,f,?_⟩
  intro C D h
  apply Subtype.ext
  apply fullGraph_injective
  exact Submodule.map_injective_of_injective e.injective (congrArg Subtype.val h)

variable [Fintype K] [Finite E] [Invertible (2 : K)]

/-- The essential residual orbit lower bound, with a concrete uniform
fixed-dimension constant, for each individual target ordered triple. -/
theorem fixedPairOrbit_card_lower (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥) :
    Fintype.card K ^ (finrank K L+1).choose 2 ≤
      4 ^ finrank K L * Nat.card (FixedPairOrbit ω L M N) := by
  obtain ⟨B,hs,hB,f,hf⟩ := fixedPairOrbit_form_injection ω L M N ha hω hL hM hN hLM hLN hMN
  exact (formOrbit_card_lower B hs hB).trans
    (Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective f hf))

end FixedPairOrbit
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section UniformCountingBounds
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Finite V]

/-- Reindexing the exact graph-chart count by projection dimension. -/
theorem lagrangian_card_by_dimension :
    Nat.card (Lagrangian (K := K) (V := V)) =
      ∑ k : Fin (finrank K V+1), Nat.card (DimSubspace K V k.val) *
        Fintype.card K ^ (k.val+1).choose 2 := by
  classical
  let := Fintype.ofFinite (Submodule K V)
  let d : Submodule K V → Fin (finrank K V+1) :=
    fun U => ⟨finrank K U,Nat.lt_succ_of_le (Submodule.finrank_le U)⟩
  rw [lagrangian_card_sum,← Fintype.sum_fiberwise d]
  apply Finset.sum_congr rfl
  intro k _
  have hc : Nat.card {U : Submodule K V // d U = k} = Nat.card (DimSubspace K V k.val) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun U => by
      change (⟨finrank K U,_⟩ : Fin _)=k ↔ finrank K U=k.val
      exact Fin.ext_iff))
  have he (U : {U : Submodule K V // d U = k}) : finrank K U.val = k.val :=
    congrArg Fin.val U.property
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Nat.card_eq_fintype_card,hc,Nat.cast_id]

/-- A field-independent fixed-dimension upper normalization constant. -/
noncomputable def lagrangianConstant (n : ℕ) : ℝ := (n+1) * 2^n

theorem lagrangianConstant_pos (n : ℕ) : 0 < lagrangianConstant n := by
  unfold lagrangianConstant
  positivity

theorem lagrangian_card_upper :
    (Nat.card (Lagrangian (K := K) (V := V)) : ℝ) ≤
      lagrangianConstant (finrank K V) * (Fintype.card K : ℝ)^((finrank K V+1).choose 2) := by
  rw [lagrangian_card_by_dimension,Nat.cast_sum]
  let n := finrank K V
  let q : ℝ := Fintype.card K
  have hq : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos (α := K)))
  have hterm (k : Fin (n+1)) :
      (Nat.card (DimSubspace K V k.val) : ℝ) * q^(k.val+1).choose 2 ≤
        2^n*q^(n+1).choose 2 := by
    have hk : k.val ≤ n := Nat.le_of_lt_succ k.isLt
    have he : k.val*(n-k.val)+(k.val+1).choose 2 ≤ (n+1).choose 2 := by
      have hh := symmetric_nullity_exponent n (n-k.val) (Nat.sub_le n k.val)
      rw [Nat.sub_sub_self hk] at hh
      nlinarith
    calc
      _ ≤ (2^k.val*q^(k.val*(n-k.val)))*q^(k.val+1).choose 2 :=
        mul_le_mul_of_nonneg_right (subspace_count_upper k.val hk) (by positivity)
      _ = 2^k.val*q^(k.val*(n-k.val)+(k.val+1).choose 2) := by rw [pow_add]; ring
      _ ≤ 2^n*q^(n+1).choose 2 := mul_le_mul
        (pow_le_pow_right₀ (by norm_num) hk) (pow_le_pow_right₀ hq he) (by positivity) (by positivity)
  calc
    _ ≤ ∑ _k : Fin (n+1), 2^n*q^(n+1).choose 2 := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [Nat.cast_mul,Nat.cast_pow] using hterm k
    _ = _ := by simp [lagrangianConstant,n,q]; ring

theorem lagrangian_card_lower :
    (Fintype.card K : ℝ)^((finrank K V+1).choose 2) ≤
      Nat.card (Lagrangian (K := K) (V := V)) := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  have h := Nat.card_le_card_of_injective (graphLagrangian (K := K) (V := V) (⊤ : Submodule K V))
    (graphLagrangian_form_injective (⊤ : Submodule K V))
  rw [symForm_card] at h
  simpa only [finrank_top,Nat.cast_pow] using (show
    ((Fintype.card K^((finrank K ↥(⊤ : Submodule K V)+1).choose 2) : ℕ) : ℝ) ≤
      (Nat.card (Lagrangian (K := K) (V := V)) : ℝ) from by exact_mod_cast h)

end UniformCountingBounds
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section FullTripleOrbit
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
abbrev SymplecticLagrangian := {L : Submodule K E // ω.orthogonal L = L}
abbrev OrderedTransversePair := {p : SymplecticLagrangian ω × SymplecticLagrangian ω //
  p.1.val ⊓ p.2.val = ⊥}
abbrev OrderedTripleOrbit (L M N : Submodule K E) :=
  {p : Submodule K E × Submodule K E × Submodule K E //
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      L.map e.toLinearMap = p.1 ∧ M.map e.toLinearMap = p.2.1 ∧
      N.map e.toLinearMap = p.2.2}

variable [FiniteDimensional K E]
theorem orderedTripleOrbit_pair_injection (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M N : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLM : L ⊓ M = ⊥) :
    ∃ f : OrderedTransversePair ω × FixedPairOrbit ω L M N → OrderedTripleOrbit ω L M N,
      Function.Injective f := by
  classical
  have ht (p : OrderedTransversePair ω) := transverse_pair_transitivity ω ha hω
    L M p.val.1.val p.val.2.val hL hM p.val.1.property p.val.2.property hLM p.property
  let e (p : OrderedTransversePair ω) := (ht p).choose
  have he (p) := (ht p).choose_spec
  have hgood (p : OrderedTransversePair ω) (N' : FixedPairOrbit ω L M N) :
      ∃ f : E ≃ₗ[K] E, (∀ x y, ω (f x) (f y) = ω x y) ∧
        L.map f.toLinearMap = p.val.1.val ∧ M.map f.toLinearMap = p.val.2.val ∧
        N.map f.toLinearMap = N'.val.map (e p).toLinearMap := by
    obtain ⟨g,hg,hgL,hgM,hgN⟩ := N'.property
    refine ⟨g.trans (e p),?_,?_,?_,?_⟩
    · intro x y
      exact ((he p).1 (g x) (g y)).trans (hg x y)
    · change L.map ((e p).toLinearMap.comp g.toLinearMap) = _
      rw [Submodule.map_comp,hgL]
      exact (he p).2.1
    · change M.map ((e p).toLinearMap.comp g.toLinearMap) = _
      rw [Submodule.map_comp,hgM]
      exact (he p).2.2
    · change N.map ((e p).toLinearMap.comp g.toLinearMap) = _
      rw [Submodule.map_comp,hgN]
  let f : OrderedTransversePair ω × FixedPairOrbit ω L M N → OrderedTripleOrbit ω L M N :=
    fun x => ⟨(x.1.val.1.val,x.1.val.2.val,x.2.val.map (e x.1).toLinearMap),hgood x.1 x.2⟩
  refine ⟨f,?_⟩
  rintro ⟨p,A⟩ ⟨q,B⟩ h
  have hv := congrArg Subtype.val h
  have hp : p = q := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hv)
    · exact Subtype.ext (congrArg (fun x => x.2.1) hv)
  subst q
  have hab : A = B := by
    apply Subtype.ext
    exact Submodule.map_injective_of_injective (e p).injective
      (congrArg (fun x => x.2.2) hv)
  subst B
  rfl
end FullTripleOrbit

section CanonicalTripleMass
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Finite V]
local notation "ω" => (canonicalSymplectic (K := K) (V := V))

 theorem transverse_to_card (h2 : (2 : K) ≠ 0) (A : Lagrangian (K := K) (V := V)) :
    Nat.card {B : Lagrangian (K := K) (V := V) // A.val ⊓ B.val = ⊥} =
      Fintype.card K^((finrank K V+1).choose 2) := by
  have h := lagrangian_pair_count h2 A 0 (Nat.zero_le _)
  have hc : Nat.card {U : Submodule K V // finrank K U = finrank K V} = 1 := by
    let : Unique {U : Submodule K V // finrank K U = finrank K V} :=
      ⟨⟨⊤,finrank_top K V⟩,fun U => Subtype.ext (Submodule.eq_top_of_finrank_eq U.property)⟩
    exact Nat.card_unique
  have he : {B : Lagrangian (K := K) (V := V) // A.val ⊓ B.val = ⊥} ≃
      {B : Lagrangian (K := K) (V := V) // finrank K ↥(B.val ⊓ A.val) = 0} :=
    Equiv.subtypeEquiv (Equiv.refl _) (by
      intro B
      change A.val ⊓ B.val = ⊥ ↔ finrank K ↥(B.val ⊓ A.val) = 0
      rw [Submodule.finrank_eq_zero,inf_comm])
  rw [Nat.card_congr he,h]
  simp only [Nat.sub_zero,hc,one_mul]

 theorem orderedTransversePair_card (h2 : (2 : K) ≠ 0) :
    Nat.card (OrderedTransversePair ω) = Nat.card (Lagrangian (K := K) (V := V)) *
      Fintype.card K^((finrank K V+1).choose 2) := by
  classical
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let := Fintype.ofFinite (Lagrangian (K := K) (V := V))
  let e : OrderedTransversePair ω ≃
      Σ A : Lagrangian (K := K) (V := V), {B : Lagrangian (K := K) (V := V) // A.val ⊓ B.val = ⊥} :=
    { toFun := fun p => ⟨p.val.1,⟨p.val.2,p.property⟩⟩
      invFun := fun p => ⟨(p.1,p.2.val),p.2.property⟩
      left_inv := fun p => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e,Nat.card_sigma]
  simp only [transverse_to_card h2,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    Nat.card_eq_fintype_card]

 theorem orderedTransverseTriple_card_lower [Invertible (2 : K)]
    (L M N : Lagrangian (K := K) (V := V))
    (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥) :
    Nat.card (Lagrangian (K := K) (V := V)) *
        (Fintype.card K^((finrank K V+1).choose 2)) ^ 2 ≤
      4^finrank K V * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  have hcard := fixedPairOrbit_card_lower ω L.val M.val N.val
    canonicalSymplectic_alt canonicalSymplectic_nondegenerate
    L.property M.property N.property hLM hLN hMN
  rw [lagrangian_finrank L] at hcard
  obtain ⟨f,hf⟩ := orderedTripleOrbit_pair_injection ω canonicalSymplectic_alt
    canonicalSymplectic_nondegenerate L.val M.val N.val L.property M.property hLM
  have hi := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod,orderedTransversePair_card (isUnit_of_invertible (2 : K)).ne_zero] at hi
  calc
    _ = (Nat.card (Lagrangian (K := K) (V := V)) * Fintype.card K^((finrank K V+1).choose 2)) *
        Fintype.card K^((finrank K V+1).choose 2) := by rw [pow_two]; ac_rfl
    _ ≤ (Nat.card (Lagrangian (K := K) (V := V)) * Fintype.card K^((finrank K V+1).choose 2)) *
        (4^finrank K V * Nat.card (FixedPairOrbit ω L.val M.val N.val)) := Nat.mul_le_mul_left _ hcard
    _ = 4^finrank K V * (Nat.card (Lagrangian (K := K) (V := V)) *
        Fintype.card K^((finrank K V+1).choose 2) * Nat.card (FixedPairOrbit ω L.val M.val N.val)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hi
end CanonicalTripleMass
end SidorenkoCounterexample

end OAI
