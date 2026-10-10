import OAI.Probability.ThorpShuffle.Parity

namespace OAI

universe uG uE uX uH

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Specht

variable {G : Type uG} [Group G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def cyclic (ρ : Representation ℂ G E) (e : E) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g => ρ g e)
  apply_mem_toSubmodule g := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨h, rfl⟩ := hv
      exact Submodule.subset_span ⟨g * h, by simp⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa using (Submodule.span ℂ (Set.range fun h => ρ h e)).add_mem ihx ihy
    | smul a x hx ih =>
      simpa using (Submodule.span ℂ (Set.range fun h => ρ h e)).smul_mem a ih

lemma self_mem_cyclic (ρ : Representation ℂ G E) (e : E) : e ∈ cyclic ρ e := by
  exact Submodule.subset_span ⟨1, by simp⟩

theorem submodule_alternative (ρ : Representation ℂ G E) (e : E)
    (hunit : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (K : Module.End ℂ E) (hK : ∀ v, K v = ⟪e, v⟫_ℂ • e)
    (hstable : ∀ U : Subrepresentation ρ, ∀ v ∈ U, K v ∈ U)
    (U : Subrepresentation ρ) :
    cyclic ρ e ≤ U ∨ ∀ u ∈ U, ∀ v ∈ cyclic ρ e, ⟪v, u⟫_ℂ = 0 := by
  classical
  by_cases he : e ∈ U
  · left
    exact Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact U.apply_mem_toSubmodule g he)
  · right
    intro u hu v hv
    have horth (g : G) : ⟪ρ g e, u⟫_ℂ = 0 := by
      have hgu : ρ g⁻¹ u ∈ U := U.apply_mem_toSubmodule g⁻¹ hu
      have hk := hstable U _ hgu
      rw [hK] at hk
      have hz : ⟪e, ρ g⁻¹ u⟫_ℂ = 0 := by
        by_contra hne
        apply he
        have hh := U.toSubmodule.smul_mem (⟪e, ρ g⁻¹ u⟫_ℂ)⁻¹ hk
        change e ∈ U.toSubmodule
        simpa [smul_smul, hne] using hh
      have hi := hunit g e (ρ g⁻¹ u)
      simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply] using hi.trans hz
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨g, rfl⟩ := hv; exact horth g
    | zero => simp
    | add x y hx hy ihx ihy => simp [ihx, ihy]
    | smul a x hx ih => simp [ih]

theorem cyclic_irreducible (ρ : Representation ℂ G E) (e : E) (he : e ≠ 0)
    (hunit : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (K : Module.End ℂ E) (hK : ∀ v, K v = ⟪e, v⟫_ℂ • e)
    (hstable : ∀ U : Subrepresentation ρ, ∀ v ∈ U, K v ∈ U) :
    Representation.IsIrreducible (cyclic ρ e).toRepresentation := by
  let S := cyclic ρ e
  let eS : S.toSubmodule := ⟨e, self_mem_cyclic ρ e⟩
  have heS : eS ≠ 0 := by intro hh; apply he; exact congrArg Subtype.val hh
  have htb : (⊤ : Subrepresentation S.toRepresentation) ≠ ⊥ := by
    intro hh
    have hel : eS ∈ (⊤ : Subrepresentation S.toRepresentation) := by trivial
    rw [hh] at hel
    exact heS hel
  let : Nontrivial (Subrepresentation S.toRepresentation) := ⟨⟨⊤, ⊥, htb⟩⟩
  refine ⟨fun U => ?_⟩
  let U' : Subrepresentation ρ := {
    toSubmodule := U.toSubmodule.map S.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact ⟨S.toRepresentation g u, U.apply_mem_toSubmodule g hu, rfl⟩ }
  rcases submodule_alternative ρ e hunit K hK hstable U' with h | h
  · right
    apply top_unique
    intro u _
    obtain ⟨v, hv, heq⟩ := h u.property
    have hvu : v = u := Subtype.ext heq
    exact hvu ▸ hv
  · left
    apply bot_unique
    intro u hu
    have hum : (u : E) ∈ U' := ⟨u, hu, rfl⟩
    have hh := h _ hum _ u.property
    have hz : (u : E) = 0 := inner_self_eq_zero.mp hh
    exact Subtype.ext hz

namespace PermutationSpace
open scoped Classical

variable {X : Type uX} [Fintype X] [MulAction G X]

def rep : Representation ℂ G (EuclideanSpace ℂ X) where
  toFun g := {
    toFun v := WithLp.toLp 2 (fun x => v (g⁻¹ • x))
    map_add' := by intro v w; rfl
    map_smul' := by intro a v; rfl }
  map_one' := by ext v x; simp
  map_mul' := by
    intro g h
    ext v x
    change v ((g * h)⁻¹ • x) = v (h⁻¹ • g⁻¹ • x)
    simp [mul_smul]

omit [Fintype X] in
@[simp] lemma rep_apply (g : G) (v : EuclideanSpace ℂ X) (x : X) :
    rep g v x = v (g⁻¹ • x) := rfl

lemma rep_unitary (g : G) (v w : EuclideanSpace ℂ X) :
    ⟪rep g v, rep g w⟫_ℂ = ⟪v, w⟫_ℂ := by
  simp only [PiLp.inner_apply, rep_apply]
  exact Equiv.sum_comp (MulAction.toPerm g⁻¹) (fun x => inner ℂ (v x) (w x))

omit [Fintype X] in
lemma rep_single (g : G) (x : X) :
    rep g (EuclideanSpace.single x (1 : ℂ)) = EuclideanSpace.single (g • x) (1 : ℂ) := by
  classical
  ext y
  simp only [rep_apply, PiLp.single_apply, inv_smul_eq_iff]

variable {H : Type uH} [Group H] [Fintype H]

def alternator (ι : H →* G) (χ : H →* ℂ) : Module.End ℂ (EuclideanSpace ℂ X) :=
  ∑ h, χ h • rep (ι h)

omit [Fintype X] in
lemma alternator_apply (ι : H →* G) (χ : H →* ℂ) (v : EuclideanSpace ℂ X) :
    alternator ι χ v = ∑ h, χ h • rep (ι h) v := by
  simp [alternator, LinearMap.sum_apply]

omit [Fintype X] in
lemma alternator_stable (ι : H →* G) (χ : H →* ℂ)
    (U : Subrepresentation (rep : Representation ℂ G (EuclideanSpace ℂ X)))
    (v : EuclideanSpace ℂ X) (hv : v ∈ U) : alternator ι χ v ∈ U := by
  rw [alternator_apply]
  exact U.toSubmodule.sum_mem fun h _ => U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule _ hv)

omit [Fintype X] in
lemma alternator_translate (ι : H →* G) (χ : H →* ℂ) (a : H)
    (v : EuclideanSpace ℂ X) :
    alternator ι χ (rep (ι a) v) = χ a⁻¹ • alternator ι χ v := by
  rw [alternator_apply, alternator_apply, Finset.smul_sum]
  have he := Equiv.sum_comp (Equiv.mulRight a)
    (fun h => χ a⁻¹ • (χ h • (rep (ι h) v : EuclideanSpace ℂ X)))
  rw [← he]
  apply Finset.sum_congr rfl
  intro h _
  simp only [Equiv.coe_mulRight, smul_smul, map_mul]
  rw [show χ a⁻¹ * (χ h * χ a) = χ h by
    calc
      _ = χ h * (χ a⁻¹ * χ a) := by ring
      _ = χ h := by rw [← map_mul, inv_mul_cancel, map_one, mul_one]]
  simp only [Module.End.mul_apply]

omit [Fintype X] in
lemma alternator_single_zero (ι : H →* G) (χ : H →* ℂ)
    (x : X) (a : H) (ha : ι a • x = x) (hs : χ a = -1) :
    alternator ι χ (EuclideanSpace.single x (1 : ℂ)) = 0 := by
  have hh := alternator_translate ι χ a (EuclideanSpace.single x (1 : ℂ))
  rw [rep_single, ha, map_inv, hs, inv_neg, inv_one, neg_smul, one_smul] at hh
  have hz := congrArg (fun z => z + alternator ι χ (EuclideanSpace.single x (1 : ℂ))) hh
  have ht : (2 : ℂ) • alternator ι χ (EuclideanSpace.single x (1 : ℂ)) = 0 := by
    simpa [two_smul] using hz
  exact (smul_eq_zero.mp ht).resolve_left (by norm_num)

omit [Fintype X] in
lemma alternator_coeff (ι : H →* G) (χ : H →* ℂ) (v : EuclideanSpace ℂ X) (x : X) :
    alternator ι χ v x = ∑ h, χ h * v ((ι h)⁻¹ • x) := by
  simp [alternator_apply, WithLp.ofLp_sum, Finset.sum_apply]

omit [Fintype X] in
lemma polytabloid_base (ι : H →* G) (χ : H →* ℂ) (b : X)
    (hfree : ∀ h : H, ι h • b = b → h = 1) :
    alternator ι χ (EuclideanSpace.single b (1 : ℂ)) b = 1 := by
  classical
  rw [alternator_coeff, Finset.sum_eq_single 1]
  · simp
  · intro h _ hh
    have hn : (ι h)⁻¹ • b ≠ b := by
      intro he
      have hi : h⁻¹ = 1 := hfree h⁻¹ (by simpa using he)
      exact hh (inv_eq_one.mp hi)
    simp [hn]
  · simp

lemma polytabloid_inner (ι : H →* G) (χ : H →* ℂ) (b : X)
    (hreal : ∀ h, conj (χ h) = χ h) (hinv : ∀ h, χ h⁻¹ = χ h)
    (v : EuclideanSpace ℂ X) :
    ⟪alternator ι χ (EuclideanSpace.single b (1 : ℂ)), v⟫_ℂ = alternator ι χ v b := by
  classical
  rw [alternator_apply, sum_inner, alternator_coeff]
  simp only [inner_smul_left, rep_single, EuclideanSpace.inner_single_left, map_one,
    one_mul, hreal]
  have hh := Equiv.sum_comp (Equiv.inv H) (fun h => χ h * v ((ι h)⁻¹ • b))
  simpa only [Equiv.inv_apply, map_inv, inv_inv, hinv] using hh

theorem alternator_rank_one (ι : H →* G) (χ : H →* ℂ) (b : X)
    (hreal : ∀ h, conj (χ h) = χ h) (hinv : ∀ h, χ h⁻¹ = χ h)
    (hfree : ∀ h : H, ι h • b = b → h = 1)
    (halt : ∀ x : X, (∃ a : H, ι a • x = x ∧ χ a = -1) ∨
      ∃ a : H, x = ι a • b) (v : EuclideanSpace ℂ X) :
    alternator ι χ v =
      ⟪alternator ι χ (EuclideanSpace.single b (1 : ℂ)), v⟫_ℂ •
        alternator ι χ (EuclideanSpace.single b (1 : ℂ)) := by
  classical
  let e := alternator ι χ (EuclideanSpace.single b (1 : ℂ))
  have hs (x : X) : alternator ι χ (EuclideanSpace.single x (1 : ℂ)) ∈ Submodule.span ℂ {e} := by
    rcases halt x with ⟨a, ha, hχ⟩ | ⟨a, rfl⟩
    · rw [alternator_single_zero ι χ x a ha hχ]
      exact Submodule.zero_mem _
    · rw [← rep_single, alternator_translate]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton e))
  have hv : alternator ι χ v ∈ Submodule.span ℂ {e} := by
    have hexp := (EuclideanSpace.basisFun X ℂ).sum_repr v
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hexp
    rw [← hexp, map_sum]
    exact Submodule.sum_mem _ fun x _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hs x)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
  have heb : e b = 1 := polytabloid_base ι χ b hfree
  have hab : a = alternator ι χ v b := by
    have hh := congrArg (fun z : EuclideanSpace ℂ X => z b) ha
    simpa only [PiLp.smul_apply, smul_eq_mul, heb, mul_one] using hh
  rw [← ha, hab, polytabloid_inner ι χ b hreal hinv]

end PermutationSpace

end Thorp.Specht

end

end OAI
