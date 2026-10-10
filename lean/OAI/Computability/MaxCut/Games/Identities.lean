import Mathlib
import OAI.Computability.MaxCut.Games.RankAdditivity
import OAI.Computability.MaxCut.Games.Restriction

namespace OAI

namespace MaxCutGames.Appendix.Identities

abbrev Vector (n : Nat) := Fin n → Bool

def add {n : Nat} (v w : Vector n) : Vector n := fun i => v i ^^ w i

def zero (n : Nat) : Vector n := fun _ => false

theorem add_assoc {n : Nat} (u v w : Vector n) :
    add (add u v) w = add u (add v w) := by
  funext i
  exact Bool.xor_assoc (u i) (v i) (w i)

theorem add_self {n : Nat} (u : Vector n) : add u u = zero n := by
  funext i
  exact Bool.xor_self (u i)

theorem add_zero {n : Nat} (u : Vector n) : add u (zero n) = u := by
  funext i
  exact Bool.xor_false (u i)

theorem zero_add {n : Nat} (u : Vector n) : add (zero n) u = u := by
  funext i
  exact Bool.false_xor (u i)

theorem add_comm {n : Nat} (u v : Vector n) : add u v = add v u := by
  funext i
  exact Bool.xor_comm (u i) (v i)

theorem add_shuffle {n : Nat} (u v w x : Vector n) :
    add (add u v) (add w x) = add (add u w) (add v x) := by
  funext i
  change ((u i ^^ v i) ^^ (w i ^^ x i)) = ((u i ^^ w i) ^^ (v i ^^ x i))
  cases u i <;> cases v i <;> cases w i <;> cases x i <;> rfl

structure Subspace (n : Nat) where
  mem : Vector n → Prop
  zero_mem : mem (zero n)
  add_mem : ∀ {u v}, mem u → mem v → mem (add u v)

def Subspace.Included {n : Nat} (A B : Subspace n) : Prop :=
  ∀ v, A.mem v → B.mem v

structure LinearMap (n m : Nat) where
  apply : Vector n → Vector m
  map_zero : apply (zero n) = zero m
  map_add : ∀ u v, apply (add u v) = add (apply u) (apply v)

def Hybrid {n m : Nat} (Y : LinearMap n m) (A : Subspace m)
    (B : Subspace n) : Prop :=
  (∀ a, A.mem a → ∃ w, Y.apply w = a) ∧
  (∀ w, A.mem (Y.apply w) → B.mem w)

/-- The hybrid selector for `Q_A₀ Y|_B₀` at `(A/A₀, B)`.

The first component states that every coset of `A/A₀` has a preimage in
`B₀`; the second states that the preimage of `A/A₀` is contained in `B`.
`A₀ ≤ A` and `B ≤ B₀` are supplied by the composition theorem.
-/
def OuterHybrid {n m : Nat} (Y : LinearMap n m)
    (A₀ A : Subspace m) (B B₀ : Subspace n) : Prop :=
  (∀ a, A.mem a → ∃ b, B₀.mem b ∧
    ∃ a₀, A₀.mem a₀ ∧ Y.apply b = add a a₀) ∧
  (∀ b, B₀.mem b → A.mem (Y.apply b) → B.mem b)

/-- Equation (A.3), at the level of the exact character selectors.

In particular the forward proof checks the subtle point that the outer
image condition forces the full preimage `Y⁻¹(A)` into `B₀`.
-/
theorem nested_hybrid_selector_iff {n m : Nat} (Y : LinearMap n m)
    (A₀ A : Subspace m) (B B₀ : Subspace n)
    (hA : A₀.Included A) (hB : B.Included B₀) :
    (Hybrid Y A₀ B₀ ∧ OuterHybrid Y A₀ A B B₀) ↔ Hybrid Y A B := by
  constructor
  · rintro ⟨inner, outer⟩
    constructor
    · intro a ha
      rcases outer.1 a ha with ⟨b, _, a₀, ha₀, hb⟩
      rcases inner.1 a₀ ha₀ with ⟨c, hc⟩
      refine ⟨add b c, ?_⟩
      rw [Y.map_add, hb, hc, add_assoc, add_self, add_zero]
    · intro w hw
      rcases outer.1 (Y.apply w) hw with ⟨b, hb, a₀, ha₀, hyb⟩
      have hpre : Y.apply (add w b) = a₀ := by
        rw [Y.map_add, hyb, ← add_assoc, add_self, zero_add]
      have hwb : B₀.mem (add w b) := inner.2 (add w b) (hpre ▸ ha₀)
      have hw₀ : B₀.mem w := by
        have h := B₀.add_mem hwb hb
        simpa only [add_assoc, add_self, add_zero] using h
      exact outer.2 w hw₀ hw
  · intro full
    constructor
    · constructor
      · intro a₀ ha₀
        exact full.1 a₀ (hA a₀ ha₀)
      · intro w hw
        exact hB w (full.2 w (hA (Y.apply w) hw))
    · constructor
      · intro a ha
        rcases full.1 a ha with ⟨w, hw⟩
        have hwB : B.mem w := full.2 w (hw ▸ ha)
        refine ⟨w, hB w hwB, zero m, A₀.zero_mem, ?_⟩
        rw [hw, add_zero]
      · intro w _ hw
        exact full.2 w hw

/-- Disjointness of the images of `Q_A X|_B` and `Q_A Z|_B`, written
without quotient objects. Equality of the two cosets means their sum lies
in `A`, in which case both cosets must be zero. -/
def ImagesDisjointModulo {n m : Nat} (X Z : LinearMap n m)
    (A : Subspace m) (B : Subspace n) : Prop :=
  ∀ b c, B.mem b → B.mem c → A.mem (add (X.apply b) (Z.apply c)) →
    A.mem (X.apply b) ∧ A.mem (Z.apply c)

theorem reverse_sum_image {n m : Nat} (X Y Z : LinearMap n m)
    (A₀ : Subspace m) (B₀ : Subspace n)
    (hZ : ∀ w, Z.apply w = add (Y.apply w) (X.apply w))
    (inner : Hybrid Y A₀ B₀)
    (avoids : ∀ w, A₀.mem (X.apply w) → X.apply w = zero m)
    (disjoint : ImagesDisjointModulo X Z A₀ B₀) :
    ∀ a₀, A₀.mem a₀ → ∃ w, Z.apply w = a₀ := by
  intro a₀ ha₀
  rcases inner.1 a₀ ha₀ with ⟨w, hw⟩
  have hw₀ : B₀.mem w := inner.2 w (hw ▸ ha₀)
  have hsum : add (X.apply w) (Z.apply w) = a₀ := by
    rw [hZ, add_comm (Y.apply w), ← add_assoc, add_self, zero_add, hw]
  have hx := avoids w ((disjoint w w hw₀ hw₀ (hsum ▸ ha₀)).1)
  refine ⟨w, ?_⟩
  rw [hZ, hw, hx, add_zero]

/-- The second asserted implication in the reverse direction of (A.5).

`covered` expresses `B₀ + ker X = W`; `localLift` expresses
`im (Q_A₀ X|_B₀) ≤ im (Q_A₀ Y|_B₀)`. The rank-additive summand gives
the latter inclusion. This theorem checks the passage from those
specific linear-algebra hypotheses to the full preimage inclusion.
-/
theorem reverse_sum_preimage {n m : Nat} (X Y Z : LinearMap n m)
    (A₀ : Subspace m) (B₀ : Subspace n)
    (hZ : ∀ w, Z.apply w = add (Y.apply w) (X.apply w))
    (inner : Hybrid Y A₀ B₀)
    (covered : ∀ w, ∃ b, B₀.mem b ∧ X.apply b = X.apply w)
    (localLift : ∀ b, B₀.mem b →
      ∃ c, B₀.mem c ∧ A₀.mem (add (Y.apply c) (X.apply b))) :
    ∀ w, A₀.mem (Z.apply w) → B₀.mem w := by
  intro w hw
  rcases covered w with ⟨b, hb, hxb⟩
  rcases localLift b hb with ⟨c, hc, hyc⟩
  rw [hxb] at hyc
  have hsum : add (Z.apply w) (add (Y.apply c) (X.apply w)) =
      Y.apply (add w c) := by
    rw [hZ, add_shuffle, add_self, add_zero, Y.map_add]
  have hpre : A₀.mem (Y.apply (add w c)) :=
    hsum ▸ A₀.add_mem hw hyc
  have hwc := inner.2 (add w c) hpre
  have h := B₀.add_mem hwc hc
  simpa only [add_assoc, add_self, add_zero] using h

end MaxCutGames.Appendix.Identities

namespace MaxCutGames.Appendix.LinearIdentities

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

/-- The actual hybrid selector from Appendix A.1, for genuine linear maps. -/
def Hybrid (Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W) : Prop :=
  A ≤ LinearMap.range Y ∧ A.comap Y ≤ B

/-- The compressed dual frequency `Q_A Y|_B`. -/
def compress (Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W) :
    B →ₗ[K] (V ⧸ A) := A.mkQ.comp (Y.domRestrict B)

@[simp] theorem compress_apply (Y : W →ₗ[K] V) (A : Submodule K V)
    (B : Submodule K W) (b : B) : compress Y A B b = A.mkQ (Y b) := rfl

theorem compress_sub (X Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W) :
    compress (Y - X) A B = compress Y A B - compress X A B := by
  ext b
  simp only [compress_apply, LinearMap.sub_apply, map_sub]

theorem quotient_mem_image_iff (A₀ A : Submodule K V) (hA : A₀ ≤ A) (v : V) :
    A₀.mkQ v ∈ A.map A₀.mkQ ↔ v ∈ A := by
  change v ∈ (A.map A₀.mkQ).comap A₀.mkQ ↔ v ∈ A
  rw [Submodule.comap_map_mkQ, sup_of_le_right hA]

/-- The exact nested-selector equivalence of (A.3), now using Mathlib's
linear maps, submodules, restriction, and quotient construction. -/
theorem nested_hybrid_iff (Y : W →ₗ[K] V) (A₀ A : Submodule K V)
    (B B₀ : Submodule K W) (hA : A₀ ≤ A) (hB : B ≤ B₀) :
    (Hybrid Y A₀ B₀ ∧
      Hybrid (compress Y A₀ B₀) (A.map A₀.mkQ) (B.comap B₀.subtype)) ↔
    Hybrid Y A B := by
  constructor
  · rintro ⟨inner, outer⟩
    constructor
    · intro a ha
      have hqa : A₀.mkQ a ∈ A.map A₀.mkQ := ⟨a, ha, rfl⟩
      rcases outer.1 hqa with ⟨b, hb⟩
      have hdiff : Y b - a ∈ A₀ :=
        (Submodule.Quotient.eq A₀).mp hb
      rcases inner.1 hdiff with ⟨c, hc⟩
      refine ⟨(b : W) - c, ?_⟩
      rw [map_sub, hc]
      abel
    · intro w hw
      have hqa : A₀.mkQ (Y w) ∈ A.map A₀.mkQ := ⟨Y w, hw, rfl⟩
      rcases outer.1 hqa with ⟨b, hb⟩
      have hdiff : Y w - Y b ∈ A₀ :=
        (Submodule.Quotient.eq A₀).mp hb.symm
      have hwb : w - b ∈ B₀ := inner.2 (by
        change Y (w - b) ∈ A₀
        simpa only [map_sub] using hdiff)
      have hw₀ : w ∈ B₀ := by
        have h := B₀.add_mem hwb b.property
        simpa only [sub_add_cancel] using h
      have hout : (⟨w, hw₀⟩ : B₀) ∈ (A.map A₀.mkQ).comap (compress Y A₀ B₀) := hqa
      exact outer.2 hout
  · intro full
    constructor
    · exact ⟨hA.trans full.1, (Submodule.comap_mono hA).trans (full.2.trans hB)⟩
    · constructor
      · intro q hq
        rcases hq with ⟨a, ha, rfl⟩
        rcases full.1 ha with ⟨w, hw⟩
        have hwB : w ∈ B := full.2 (by
          change Y w ∈ A
          rw [hw]
          exact ha)
        refine ⟨⟨w, hB hwB⟩, ?_⟩
        simp only [compress_apply, hw]
      · intro b hb
        have hYb : Y b ∈ A := (quotient_mem_image_iff A₀ A hA (Y b)).mp hb
        exact full.2 hYb

variable [FiniteDimensional K W] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- Compression preserves the full rank when its quotient is disjoint
from the image and its restricted domain spans the domain modulo the kernel. -/
theorem compress_rank_preserved (X : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hdis : Disjoint A (LinearMap.range X))
    (hcover : B ⊔ LinearMap.ker X = ⊤) :
    Module.finrank K (LinearMap.range (compress X A B)) =
      Module.finrank K (LinearMap.range X) := by
  have hrestrict : LinearMap.range (X.domRestrict B) = LinearMap.range X := by
    apply le_antisymm (LinearMap.range_domRestrict_le_range X B)
    intro v hv
    rcases hv with ⟨w, hw⟩
    have hwtop : w ∈ B ⊔ LinearMap.ker X := by rw [hcover]; trivial
    rcases Submodule.mem_sup.mp hwtop with ⟨b, hb, k, hk, hbk⟩
    refine ⟨⟨b, hb⟩, ?_⟩
    change X b = v
    rw [← hw, ← hbk, map_add, show X k = 0 from hk, add_zero]
  have h := (A.mkQ.comp (LinearMap.range X).subtype).finrank_range_add_finrank_ker
  have hr : LinearMap.range (A.mkQ.comp (LinearMap.range X).subtype) =
      LinearMap.range (compress X A B) := by
    simp only [compress, LinearMap.range_comp, Submodule.range_subtype, hrestrict]
  rw [hr, LinearMap.ker_comp, Submodule.ker_mkQ,
    Submodule.disjoint_iff_comap_eq_bot.mp hdis.symm] at h
  simpa using h

omit [FiniteDimensional K V] in
/-- The reverse summand of (A.5) really satisfies the hybrid selector for
the remainder `Y - X`. The hypotheses here are exactly the inner hybrid
selector, complement conditions, and the compressed rank-order selector.
No image-lifting or disjointness conclusion is assumed separately. -/
theorem reverse_hybrid_of_compressed_rankBelow (X Y : W →ₗ[K] V)
    (A₀ : Submodule K V) (B₀ : Submodule K W)
    (inner : Hybrid Y A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hlocal : RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀)) :
    Hybrid (Y - X) A₀ B₀ := by
  have hker := RankAdditivity.ker_le_of_rankBelow
    (compress X A₀ B₀) (compress Y A₀ B₀) hlocal
  have himg := RankAdditivity.range_le_of_rankBelow
    (compress X A₀ B₀) (compress Y A₀ B₀) hlocal
  constructor
  · intro a ha
    rcases inner.1 ha with ⟨w, hw⟩
    have hwB : w ∈ B₀ := inner.2 (by change Y w ∈ A₀; rw [hw]; exact ha)
    have hwy : (⟨w, hwB⟩ : B₀) ∈ LinearMap.ker (compress Y A₀ B₀) := by
      change Y w ∈ LinearMap.ker A₀.mkQ
      rw [Submodule.ker_mkQ, hw]
      exact ha
    have hxA : X w ∈ A₀ := by
      have hx : X w ∈ LinearMap.ker A₀.mkQ := hker hwy
      simpa only [Submodule.ker_mkQ] using hx
    have hx : X w = 0 := Submodule.disjoint_def.mp hdis (X w) hxA ⟨w, rfl⟩
    exact ⟨w, by change Y w - X w = a; rw [hw, hx, sub_zero]⟩
  · intro w hw
    have hwZ : Y w - X w ∈ A₀ := hw
    have hwtop : w ∈ B₀ ⊔ LinearMap.ker X := by rw [hcover]; trivial
    rcases Submodule.mem_sup.mp hwtop with ⟨b, hb, k, hk, hbk⟩
    have hxb : X b = X w := by
      rw [← hbk, map_add, show X k = 0 from hk, add_zero]
    have hxran : compress X A₀ B₀ ⟨b, hb⟩ ∈ LinearMap.range (compress X A₀ B₀) :=
      ⟨⟨b, hb⟩, rfl⟩
    rcases himg hxran with ⟨c, hc⟩
    have hdiff : X w - Y c ∈ A₀ := by
      rw [← hxb]
      exact (Submodule.Quotient.eq A₀).mp hc.symm
    have hsum : Y (w - c) ∈ A₀ := by
      have h := A₀.add_mem hwZ hdiff
      have heq : (Y w - X w) + (X w - Y c) = Y (w - c) := by rw [map_sub]; abel
      exact heq ▸ h
    have hwc : w - c ∈ B₀ := inner.2 hsum
    have h := B₀.add_mem hwc c.property
    simpa only [sub_add_cancel] using h

omit [FiniteDimensional K V] in
/-- A surviving right-hand summand of (A.5) forces the original rank
order `X ⪯ Y`. This lifts the local rank equation using the two actual
hybrid rank-loss equalities, so it does not assume global rank additivity. -/
theorem rankBelow_of_compressed_rankBelow (X Y : W →ₗ[K] V)
    (A₀ : Submodule K V) (B₀ : Submodule K W)
    (inner : Hybrid Y A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hlocal : RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀)) :
    RankAdditivity.RankBelow X Y := by
  have remainder := reverse_hybrid_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have hY := Level.LinearRank.hybrid_rank_loss A₀ B₀ Y inner.1 inner.2
  have hZ := Level.LinearRank.hybrid_rank_loss A₀ B₀ (Y - X) remainder.1 remainder.2
  have hX := compress_rank_preserved X A₀ B₀ hdis hcover
  change Module.finrank K (LinearMap.range (compress Y A₀ B₀)) +
    Module.finrank K A₀ + Module.finrank K (W ⧸ B₀) = Module.finrank K (LinearMap.range Y) at hY
  change Module.finrank K (LinearMap.range (compress (Y - X) A₀ B₀)) +
    Module.finrank K A₀ + Module.finrank K (W ⧸ B₀) = Module.finrank K (LinearMap.range (Y - X)) at hZ
  have hloc : Module.finrank K (LinearMap.range (compress Y A₀ B₀)) =
      Module.finrank K (LinearMap.range (compress X A₀ B₀)) +
      Module.finrank K (LinearMap.range (compress (Y - X) A₀ B₀)) := by
    rw [compress_sub]
    exact hlocal
  change Module.finrank K (LinearMap.range Y) = Module.finrank K (LinearMap.range X) +
    Module.finrank K (LinearMap.range (Y - X))
  omega

omit [FiniteDimensional K V] in
/-- The complement in the codomain is forced by the remainder image. -/
theorem image_inter_complement_eq (A₀ I J : Submodule K V)
    (hA : A₀ ≤ J) (hdis : Disjoint I J) : J ⊓ (A₀ ⊔ I) = A₀ := by
  apply le_antisymm
  · intro v hv
    rcases Submodule.mem_sup.mp hv.2 with ⟨a, ha, i, hi, hai⟩
    have hiJ : i ∈ J := by
      have h := J.sub_mem hv.1 (hA ha)
      have heq : v - a = i := by rw [← hai]; abel
      exact heq ▸ h
    have hi0 := Submodule.disjoint_def.mp hdis i hi hiJ
    rw [hi0, add_zero] at hai
    exact hai ▸ ha
  · intro a ha
    exact ⟨hA ha, (show A₀ ≤ A₀ ⊔ I from le_sup_left) ha⟩

omit [FiniteDimensional K W] in
/-- The complement in the domain is forced by the remainder kernel. -/
theorem domain_complement_eq (B₀ K₀ J : Submodule K W)
    (hJ : J ≤ B₀) (hcover : K₀ ⊔ J = ⊤) : B₀ = (B₀ ⊓ K₀) ⊔ J := by
  apply le_antisymm
  · intro w hw
    have hwtop : w ∈ K₀ ⊔ J := by rw [hcover]; trivial
    rcases Submodule.mem_sup.mp hwtop with ⟨k, hk, j, hj, hkj⟩
    have hkB : k ∈ B₀ := by
      have h := B₀.sub_mem hw (hJ hj)
      have heq : w - j = k := by rw [← hkj]; abel
      exact heq ▸ h
    exact Submodule.mem_sup.mpr ⟨k, ⟨hkB, hk⟩, j, hj, hkj⟩
  · exact sup_le inf_le_left hJ

omit [FiniteDimensional K V] in
/-- Every surviving right-hand pair in (A.5) is the displayed canonical pair. -/
theorem surviving_pair_forced (X Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (inner : Hybrid Y A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hA : A₀ ⊔ LinearMap.range X = A)
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hB : B₀ ⊓ LinearMap.ker X = B)
    (hlocal : RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀)) :
    A₀ = LinearMap.range (Y - X) ⊓ A ∧ B₀ = B ⊔ LinearMap.ker (Y - X) := by
  have remainder := reverse_hybrid_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have global := rankBelow_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have geometry := (RankAdditivity.rankBelow_iff X Y).mp global
  constructor
  · have h := image_inter_complement_eq A₀ (LinearMap.range X)
      (LinearMap.range (Y - X)) remainder.1 geometry.1
    rw [hA] at h
    exact h.symm
  · have hker : LinearMap.ker (Y - X) ≤ B₀ := by
      intro w hw
      apply remainder.2
      change (Y - X) w ∈ A₀
      rw [show (Y - X) w = 0 from hw]
      exact A₀.zero_mem
    have h := domain_complement_eq B₀ (LinearMap.ker X) (LinearMap.ker (Y - X)) hker geometry.2
    rw [hB] at h
    exact h

omit [FiniteDimensional K V] in
theorem canonical_inner_hybrid (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hrank : RankAdditivity.RankBelow X Y)
    (outer : Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) :
    Hybrid Y (LinearMap.range (Y - X) ⊓ A) (B ⊔ LinearMap.ker (Y - X)) := by
  constructor
  · have hz : LinearMap.range (Y - X) ≤ LinearMap.range Y := by
      rw [RankAdditivity.range_remainder_eq_range_on_kernel X Y hrank]
      exact LinearMap.range_domRestrict_le_range Y (LinearMap.ker X)
    exact inf_le_left.trans hz
  · intro w hw
    have hy : Y w ∈ LinearMap.range (Y - X) ⊓ A := hw
    have hk : w ∈ LinearMap.ker X :=
      RankAdditivity.mem_ker_of_apply_mem_range_remainder X Y hrank w hy.1
    have hq : (⟨w, hk⟩ : LinearMap.ker X) ∈
        (A.map (LinearMap.range X).mkQ).comap
          (compress Y (LinearMap.range X) (LinearMap.ker X)) :=
      ⟨Y w, hy.2, rfl⟩
    have hb : w ∈ B := outer.2 hq
    exact (show B ≤ B ⊔ LinearMap.ker (Y - X) from le_sup_left) hb

omit [FiniteDimensional K V] in
theorem canonical_remainder_hybrid (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hrank : RankAdditivity.RankBelow X Y)
    (outer : Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) :
    Hybrid (Y - X) (LinearMap.range (Y - X) ⊓ A) (B ⊔ LinearMap.ker (Y - X)) := by
  constructor
  · exact inf_le_left
  · intro w hw
    have hwZ : (Y - X) w ∈ LinearMap.range (Y - X) ⊓ A := hw
    have hc := ((RankAdditivity.rankBelow_iff X Y).mp hrank).2
    have ht : w ∈ LinearMap.ker X ⊔ LinearMap.ker (Y - X) := by rw [hc]; trivial
    rcases Submodule.mem_sup.mp ht with ⟨k, hk, j, hj, hkj⟩
    have hzk : (Y - X) k = (Y - X) w := by
      rw [← hkj, map_add, show (Y - X) j = 0 from hj, add_zero]
    have hyk : Y k = (Y - X) w := by
      calc
        Y k = (Y - X) k := by
          change Y k = Y k - X k
          rw [show X k = 0 from hk, sub_zero]
        _ = (Y - X) w := hzk
    have hyA : Y k ∈ A := by rw [hyk]; exact hwZ.2
    have hq : (⟨k, hk⟩ : LinearMap.ker X) ∈
        (A.map (LinearMap.range X).mkQ).comap
          (compress Y (LinearMap.range X) (LinearMap.ker X)) :=
      ⟨Y k, hyA, rfl⟩
    have hkB : k ∈ B := outer.2 hq
    exact Submodule.mem_sup.mpr ⟨k, hkB, j, hj, hkj⟩

omit [FiniteDimensional K V] in
theorem canonical_codomain_complement (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hI : LinearMap.range X ≤ A) (hrank : RankAdditivity.RankBelow X Y)
    (outer : Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) :
    Disjoint (LinearMap.range (Y - X) ⊓ A) (LinearMap.range X) ∧
      (LinearMap.range (Y - X) ⊓ A) ⊔ LinearMap.range X = A := by
  have hd := ((RankAdditivity.rankBelow_iff X Y).mp hrank).1
  refine ⟨hd.symm.mono_left inf_le_left, ?_⟩
  apply le_antisymm (sup_le inf_le_right hI)
  intro a ha
  have hqa : (LinearMap.range X).mkQ a ∈ A.map (LinearMap.range X).mkQ := ⟨a, ha, rfl⟩
  rcases outer.1 hqa with ⟨k, hk⟩
  have hi : a - Y k ∈ LinearMap.range X :=
    (Submodule.Quotient.eq (LinearMap.range X)).mp hk.symm
  have hyA : Y k ∈ A := by
    have h := A.sub_mem ha (hI hi)
    have heq : a - (a - Y k) = Y k := by abel
    exact heq ▸ h
  have hyZ : Y k ∈ LinearMap.range (Y - X) :=
    ⟨(k : W), by
      change Y k - X k = Y k
      rw [show X k = 0 from k.property, sub_zero]⟩
  exact Submodule.mem_sup.mpr ⟨Y k, ⟨hyZ, hyA⟩, a - Y k, hi, by abel⟩

omit [FiniteDimensional K V] in
theorem canonical_domain_complement (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hB : B ≤ LinearMap.ker X) (hrank : RankAdditivity.RankBelow X Y)
    (outer : Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) :
    (B ⊔ LinearMap.ker (Y - X)) ⊓ LinearMap.ker X = B ∧
      (B ⊔ LinearMap.ker (Y - X)) ⊔ LinearMap.ker X = ⊤ := by
  constructor
  · apply le_antisymm
    · intro w hw
      rcases Submodule.mem_sup.mp hw.1 with ⟨b, hb, j, hj, hbj⟩
      have hjK : j ∈ LinearMap.ker X := by
        have h := (LinearMap.ker X).sub_mem hw.2 (hB hb)
        have heq : w - b = j := by rw [← hbj]; abel
        exact heq ▸ h
      have hyj : Y j = 0 := by
        have hz : Y j - X j = 0 := hj
        rw [show X j = 0 from hjK, sub_zero] at hz
        exact hz
      have hq : (⟨j, hjK⟩ : LinearMap.ker X) ∈
          (A.map (LinearMap.range X).mkQ).comap
            (compress Y (LinearMap.range X) (LinearMap.ker X)) := by
        change (LinearMap.range X).mkQ (Y j) ∈ A.map (LinearMap.range X).mkQ
        rw [hyj, map_zero]
        exact Submodule.zero_mem _
      have hjB : j ∈ B := outer.2 hq
      have h := B.add_mem hb hjB
      exact hbj ▸ h
    · exact le_inf le_sup_left hB
  · have hc := ((RankAdditivity.rankBelow_iff X Y).mp hrank).2
    calc
      (B ⊔ LinearMap.ker (Y - X)) ⊔ LinearMap.ker X =
        B ⊔ (LinearMap.ker X ⊔ LinearMap.ker (Y - X)) := by ac_rfl
      _ = ⊤ := by rw [hc, sup_top_eq]

omit [FiniteDimensional K V] in
theorem compressed_rankBelow_of_hybrids (X Y : W →ₗ[K] V)
    (A₀ : Submodule K V) (B₀ : Submodule K W)
    (hy : Hybrid Y A₀ B₀) (hz : Hybrid (Y - X) A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hrank : RankAdditivity.RankBelow X Y) :
    RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀) := by
  have hY := Level.LinearRank.hybrid_rank_loss A₀ B₀ Y hy.1 hy.2
  have hZ := Level.LinearRank.hybrid_rank_loss A₀ B₀ (Y - X) hz.1 hz.2
  have hX := compress_rank_preserved X A₀ B₀ hdis hcover
  change Module.finrank K (LinearMap.range (compress Y A₀ B₀)) +
    Module.finrank K A₀ + Module.finrank K (W ⧸ B₀) = Module.finrank K (LinearMap.range Y) at hY
  change Module.finrank K (LinearMap.range (compress (Y - X) A₀ B₀)) +
    Module.finrank K A₀ + Module.finrank K (W ⧸ B₀) = Module.finrank K (LinearMap.range (Y - X)) at hZ
  change Module.finrank K (LinearMap.range Y) = Module.finrank K (LinearMap.range X) +
    Module.finrank K (LinearMap.range (Y - X)) at hrank
  change Module.finrank K (LinearMap.range (compress Y A₀ B₀)) =
    Module.finrank K (LinearMap.range (compress X A₀ B₀)) +
    Module.finrank K (LinearMap.range (compress Y A₀ B₀ - compress X A₀ B₀))
  rw [← compress_sub]
  omega

omit [FiniteDimensional K V] in
theorem reverse_outer_hybrid (X Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (inner : Hybrid Y A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hA : A₀ ⊔ LinearMap.range X = A)
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hB : B₀ ⊓ LinearMap.ker X = B)
    (hlocal : RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀)) :
    Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype) := by
  have hg := rankBelow_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have hz := reverse_hybrid_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have hf := surviving_pair_forced X Y A₀ A B B₀ inner hdis hA hcover hB hlocal
  have hI : LinearMap.range X ≤ A := by rw [← hA]; exact le_sup_right
  constructor
  · intro q hq
    rcases hq with ⟨a, ha, rfl⟩
    have haSum : a ∈ A₀ ⊔ LinearMap.range X := by rw [hA]; exact ha
    rcases Submodule.mem_sup.mp haSum with ⟨a₀, ha₀, i, hi, hai⟩
    rcases inner.1 ha₀ with ⟨w, hw⟩
    have hyZ : Y w ∈ LinearMap.range (Y - X) := by rw [hw]; exact hz.1 ha₀
    have hwK : w ∈ LinearMap.ker X :=
      RankAdditivity.mem_ker_of_apply_mem_range_remainder X Y hg w hyZ
    refine ⟨⟨w, hwK⟩, ?_⟩
    have hqi : (LinearMap.range X).mkQ i = 0 := by
      change i ∈ LinearMap.ker (LinearMap.range X).mkQ
      rw [Submodule.ker_mkQ]
      exact hi
    change (LinearMap.range X).mkQ (Y w) = (LinearMap.range X).mkQ a
    rw [hw, ← hai, map_add, hqi, add_zero]
  · intro k hk
    have hyA : Y k ∈ A :=
      (quotient_mem_image_iff (LinearMap.range X) A hI (Y k)).mp hk
    have hZk : (Y - X) k = Y k := by
      change Y k - X k = Y k
      rw [show X k = 0 from k.property, sub_zero]
    have hyZ : Y k ∈ LinearMap.range (Y - X) := ⟨(k : W), hZk⟩
    have ha₀ : Y k ∈ A₀ := by rw [hf.1]; exact ⟨hyZ, hyA⟩
    have hkB₀ : (k : W) ∈ B₀ := hz.2 (by
      change (Y - X) k ∈ A₀
      rw [hZk]
      exact ha₀)
    change (k : W) ∈ B
    rw [← hB]
    exact ⟨hkB₀, k.property⟩

/-- The precise right-hand pair selector of (A.5). -/
def A5PairSurvives (X Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W)
    (p : Submodule K V × Submodule K W) : Prop :=
  Hybrid Y p.1 p.2 ∧ Disjoint p.1 (LinearMap.range X) ∧
  p.1 ⊔ LinearMap.range X = A ∧ p.2 ⊔ LinearMap.ker X = ⊤ ∧
  p.2 ⊓ LinearMap.ker X = B ∧
  RankAdditivity.RankBelow (compress X p.1 p.2) (compress Y p.1 p.2)

omit [FiniteDimensional K V] in
/-- The complete unique-summand selector identity in (A.5), in arbitrary
finite dimensions. In characteristic two the remainder `Y-X` is `Y+X`. -/
theorem a5_unique_selector (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hI : LinearMap.range X ≤ A) (hB : B ≤ LinearMap.ker X) :
    (RankAdditivity.RankBelow X Y ∧
      Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
        (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) ↔
      ∃! p : Submodule K V × Submodule K W, A5PairSurvives X Y A B p := by
  constructor
  · rintro ⟨hr, ho⟩
    have hy := canonical_inner_hybrid X Y A B hr ho
    have hz := canonical_remainder_hybrid X Y A B hr ho
    have ha := canonical_codomain_complement X Y A B hI hr ho
    have hb := canonical_domain_complement X Y A B hB hr ho
    have hl := compressed_rankBelow_of_hybrids X Y
      (LinearMap.range (Y - X) ⊓ A) (B ⊔ LinearMap.ker (Y - X)) hy hz ha.1 hb.2 hr
    refine ⟨(LinearMap.range (Y - X) ⊓ A, B ⊔ LinearMap.ker (Y - X)),
      ⟨hy, ha.1, ha.2, hb.2, hb.1, hl⟩, ?_⟩
    rintro ⟨A₀, B₀⟩ hp
    rcases hp with ⟨hi, hd, ha', hc, hb', hl'⟩
    have hf := surviving_pair_forced X Y A₀ A B B₀ hi hd ha' hc hb' hl'
    exact Prod.ext hf.1 hf.2
  · rintro ⟨⟨A₀, B₀⟩, hp, _⟩
    rcases hp with ⟨hi, hd, ha, hc, hb, hl⟩
    exact ⟨rankBelow_of_compressed_rankBelow X Y A₀ B₀ hi hd hc hl,
      reverse_outer_hybrid X Y A₀ A B B₀ hi hd ha hc hb hl⟩

/-! ## The unique selector in (A.4) -/

omit [FiniteDimensional K V] in
theorem a4_codomain_forced (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (inner : Hybrid Y A₀ B₀)
    (hker : LinearMap.ker X = B.comap B₀.subtype)
    (himage : LinearMap.range X = A.map A₀.mkQ)
    (hlocal : RankAdditivity.RankBelow X (compress Y A₀ B₀)) :
    A₀ = (B.map Y) ⊓ A := by
  have hk := RankAdditivity.ker_le_of_rankBelow X (compress Y A₀ B₀) hlocal
  have hd := ((RankAdditivity.rankBelow_iff X (compress Y A₀ B₀)).mp hlocal).1
  apply le_antisymm
  · intro a ha
    rcases inner.1 ha with ⟨w, hw⟩
    have hwB₀ : w ∈ B₀ := inner.2 (by change Y w ∈ A₀; rw [hw]; exact ha)
    have hwy : (⟨w, hwB₀⟩ : B₀) ∈ LinearMap.ker (compress Y A₀ B₀) := by
      change Y w ∈ LinearMap.ker A₀.mkQ
      rw [Submodule.ker_mkQ, hw]
      exact ha
    have hwX := hk hwy
    rw [hker] at hwX
    exact ⟨⟨w, hwX, hw⟩, hA ha⟩
  · intro a ha
    rcases ha.1 with ⟨b, hb, hYb⟩
    let bb : B₀ := ⟨b, hB hb⟩
    have hxb : X bb = 0 := by
      have hx : bb ∈ LinearMap.ker X := by rw [hker]; exact hb
      exact hx
    have hymem : compress Y A₀ B₀ bb ∈ LinearMap.range X := by
      rw [himage]
      exact ⟨Y b, by rw [hYb]; exact ha.2, rfl⟩
    have hzmem : compress Y A₀ B₀ bb ∈ LinearMap.range (compress Y A₀ B₀ - X) :=
      ⟨bb, by change compress Y A₀ B₀ bb - X bb = compress Y A₀ B₀ bb; rw [hxb, sub_zero]⟩
    have hz := Submodule.disjoint_def.mp hd (compress Y A₀ B₀ bb) hymem hzmem
    have hm : Y b ∈ LinearMap.ker A₀.mkQ := hz
    rw [Submodule.ker_mkQ, hYb] at hm
    exact hm

omit [FiniteDimensional K V] in
theorem a4_domain_forced (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (inner : Hybrid Y A₀ B₀)
    (hker : LinearMap.ker X = B.comap B₀.subtype)
    (himage : LinearMap.range X = A.map A₀.mkQ)
    (hlocal : RankAdditivity.RankBelow X (compress Y A₀ B₀)) :
    B₀ = B ⊔ A.comap Y := by
  have hrange := RankAdditivity.range_le_of_rankBelow X (compress Y A₀ B₀) hlocal
  have hcover := ((RankAdditivity.rankBelow_iff X (compress Y A₀ B₀)).mp hlocal).2
  apply le_antisymm
  · intro w hw
    let ww : B₀ := ⟨w, hw⟩
    have ht : ww ∈ LinearMap.ker X ⊔ LinearMap.ker (compress Y A₀ B₀ - X) := by
      rw [hcover]; trivial
    rcases Submodule.mem_sup.mp ht with ⟨b, hb, p, hp, hbp⟩
    have hbB : (b : W) ∈ B := by rw [hker] at hb; exact hb
    have hpEq : compress Y A₀ B₀ p = X p := by
      have hz : compress Y A₀ B₀ p - X p = 0 := hp
      exact sub_eq_zero.mp hz
    have hq : A₀.mkQ (Y p) ∈ A.map A₀.mkQ := by
      rw [← himage]
      change compress Y A₀ B₀ p ∈ LinearMap.range X
      rw [hpEq]
      exact ⟨p, rfl⟩
    have hpA : (p : W) ∈ A.comap Y :=
      (quotient_mem_image_iff A₀ A hA (Y p)).mp hq
    exact Submodule.mem_sup.mpr ⟨(b : W), hbB, (p : W), hpA, congrArg Subtype.val hbp⟩
  · apply sup_le hB
    intro w hw
    have hqx : A₀.mkQ (Y w) ∈ LinearMap.range X := by
      rw [himage]
      exact ⟨Y w, hw, rfl⟩
    rcases hrange hqx with ⟨c, hc⟩
    have hdiff : Y w - Y c ∈ A₀ := (Submodule.Quotient.eq A₀).mp hc.symm
    have hwc : w - c ∈ B₀ := inner.2 (by
      change Y (w - c) ∈ A₀
      simpa only [map_sub] using hdiff)
    have h := B₀.add_mem hwc c.property
    simpa only [sub_add_cancel] using h

omit [FiniteDimensional K V] in
theorem a4_apply_on_preimage (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (himage : LinearMap.range X = A.map A₀.mkQ)
    (hlocal : RankAdditivity.RankBelow X (compress Y A₀ B₀))
    (p : B₀) (hp : Y p ∈ A) : X p = A₀.mkQ (Y p) := by
  have hd := ((RankAdditivity.rankBelow_iff X (compress Y A₀ B₀)).mp hlocal).1
  have hy : compress Y A₀ B₀ p ∈ LinearMap.range X := by
    rw [himage]
    exact ⟨Y p, hp, rfl⟩
  have hx : X p ∈ LinearMap.range X := ⟨p, rfl⟩
  have hzX : (compress Y A₀ B₀ - X) p ∈ LinearMap.range X :=
    (LinearMap.range X).sub_mem hy hx
  have hzR : (compress Y A₀ B₀ - X) p ∈ LinearMap.range (compress Y A₀ B₀ - X) := ⟨p, rfl⟩
  have hz := Submodule.disjoint_def.mp hd ((compress Y A₀ B₀ - X) p) hzX hzR
  exact (sub_eq_zero.mp hz).symm

omit [FiniteDimensional K V] in
theorem a4_map_unique (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X₁ X₂ : B₀ →ₗ[K] (V ⧸ A₀))
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (inner : Hybrid Y A₀ B₀)
    (hk₁ : LinearMap.ker X₁ = B.comap B₀.subtype)
    (hk₂ : LinearMap.ker X₂ = B.comap B₀.subtype)
    (hi₁ : LinearMap.range X₁ = A.map A₀.mkQ)
    (hi₂ : LinearMap.range X₂ = A.map A₀.mkQ)
    (hr₁ : RankAdditivity.RankBelow X₁ (compress Y A₀ B₀))
    (hr₂ : RankAdditivity.RankBelow X₂ (compress Y A₀ B₀)) : X₁ = X₂ := by
  have hd := a4_domain_forced Y A₀ A B B₀ X₁ hA hB inner hk₁ hi₁ hr₁
  ext w
  have hw : (w : W) ∈ B ⊔ A.comap Y := by rw [← hd]; exact w.property
  rcases Submodule.mem_sup.mp hw with ⟨b, hb, p, hp, hbp⟩
  let bb : B₀ := ⟨b, hB hb⟩
  have hpB₀ : p ∈ B₀ := by rw [hd]; exact Submodule.mem_sup_right hp
  let pp : B₀ := ⟨p, hpB₀⟩
  have heq : w = bb + pp := Subtype.ext hbp.symm
  have hb₁ : X₁ bb = 0 := by
    have h : bb ∈ LinearMap.ker X₁ := by rw [hk₁]; exact hb
    exact h
  have hb₂ : X₂ bb = 0 := by
    have h : bb ∈ LinearMap.ker X₂ := by rw [hk₂]; exact hb
    exact h
  have hp₁ := a4_apply_on_preimage Y A₀ A B₀ X₁ hi₁ hr₁ pp hp
  have hp₂ := a4_apply_on_preimage Y A₀ A B₀ X₂ hi₂ hr₂ pp hp
  rw [heq, map_add, map_add, hb₁, hb₂, hp₁, hp₂]

omit [FiniteDimensional K V] in
theorem a4_weak_selector_of_summand (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀)) (inner : Hybrid Y A₀ B₀)
    (hker : LinearMap.ker X = B.comap B₀.subtype)
    (himage : LinearMap.range X = A.map A₀.mkQ)
    (hlocal : RankAdditivity.RankBelow X (compress Y A₀ B₀)) :
    A ≤ LinearMap.range Y ∧ LinearMap.ker Y ≤ B := by
  have hi := RankAdditivity.range_le_of_rankBelow X (compress Y A₀ B₀) hlocal
  have hk := RankAdditivity.ker_le_of_rankBelow X (compress Y A₀ B₀) hlocal
  constructor
  · intro a ha
    have hqa : A₀.mkQ a ∈ LinearMap.range X := by rw [himage]; exact ⟨a, ha, rfl⟩
    rcases hi hqa with ⟨c, hc⟩
    have hdiff : Y c - a ∈ A₀ := (Submodule.Quotient.eq A₀).mp hc
    rcases inner.1 hdiff with ⟨w, hw⟩
    refine ⟨(c : W) - w, ?_⟩
    rw [map_sub, hw]
    abel
  · intro w hw
    have hyw : Y w = 0 := hw
    have hwB₀ : w ∈ B₀ := inner.2 (by change Y w ∈ A₀; rw [hyw]; exact A₀.zero_mem)
    have hwq : (⟨w, hwB₀⟩ : B₀) ∈ LinearMap.ker (compress Y A₀ B₀) := by
      change A₀.mkQ (Y w) = 0
      rw [hyw, map_zero]
    have hwx := hk hwq
    rw [hker] at hwx
    exact hwx

omit [FiniteDimensional K W] [FiniteDimensional K V] in
theorem a4_kernel_of_gluing (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (hA₀ : A₀ = (B.map Y) ⊓ A) (hB₀ : B₀ = B ⊔ A.comap Y)
    (hKY : LinearMap.ker Y ≤ B)
    (hzero : ∀ b : B₀, (b : W) ∈ B → X b = 0)
    (hcopy : ∀ p : B₀, Y p ∈ A → X p = A₀.mkQ (Y p)) :
    LinearMap.ker X = B.comap B₀.subtype := by
  ext w
  constructor
  · intro hw
    have hwSum : (w : W) ∈ B ⊔ A.comap Y := by rw [← hB₀]; exact w.property
    rcases Submodule.mem_sup.mp hwSum with ⟨b, hb, p, hp, hbp⟩
    have hb₀ : b ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_left hb
    have hp₀ : p ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_right hp
    let bb : B₀ := ⟨b, hb₀⟩
    let pp : B₀ := ⟨p, hp₀⟩
    have heq : w = bb + pp := Subtype.ext hbp.symm
    have hxp : X pp = 0 := by
      have hxw : X w = 0 := hw
      rw [heq, map_add, hzero bb hb, zero_add] at hxw
      exact hxw
    have hqp : A₀.mkQ (Y p) = 0 := (hcopy pp hp).symm.trans hxp
    have hy₀ : Y p ∈ A₀ := by
      have hm : Y p ∈ LinearMap.ker A₀.mkQ := hqp
      simpa only [Submodule.ker_mkQ] using hm
    rw [hA₀] at hy₀
    rcases hy₀.1 with ⟨b', hb', hYb'⟩
    have hpk : p - b' ∈ LinearMap.ker Y := by
      change Y (p - b') = 0
      rw [map_sub, hYb', sub_self]
    have hpB : p ∈ B := by
      have h := B.add_mem (hKY hpk) hb'
      simpa only [sub_add_cancel] using h
    have h := B.add_mem hb hpB
    change (w : W) ∈ B
    exact hbp ▸ h
  · intro hw
    exact hzero w hw

omit [FiniteDimensional K V] in
theorem disjoint_quotient_images_of_intersection
    (A₀ A C : Submodule K V) (hA₀ : A₀ = C ⊓ A) :
    Disjoint (A.map A₀.mkQ) (C.map A₀.mkQ) := by
  apply Submodule.disjoint_def.mpr
  intro v hvA hvC
  rcases hvA with ⟨a, ha, hqa⟩
  rcases hvC with ⟨c, hc, hqc⟩
  have hdiff : c - a ∈ A₀ := (Submodule.Quotient.eq A₀).mp (hqc.trans hqa.symm)
  have hdiffA : c - a ∈ A := by rw [hA₀] at hdiff; exact hdiff.2
  have hcA : c ∈ A := by
    have h := A.add_mem hdiffA ha
    simpa only [sub_add_cancel] using h
  have hc₀ : c ∈ A₀ := by rw [hA₀]; exact ⟨hc, hcA⟩
  have hqzero : A₀.mkQ c = 0 := by
    change c ∈ LinearMap.ker A₀.mkQ
    rw [Submodule.ker_mkQ]
    exact hc₀
  exact hqc.symm.trans hqzero

omit [FiniteDimensional K W] [FiniteDimensional K V] in
theorem a4_range_of_gluing (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (hB₀ : B₀ = B ⊔ A.comap Y) (hAY : A ≤ LinearMap.range Y)
    (hzero : ∀ b : B₀, (b : W) ∈ B → X b = 0)
    (hcopy : ∀ p : B₀, Y p ∈ A → X p = A₀.mkQ (Y p)) :
    LinearMap.range X = A.map A₀.mkQ := by
  apply le_antisymm
  · rintro v ⟨w, hw⟩
    have hwSum : (w : W) ∈ B ⊔ A.comap Y := by rw [← hB₀]; exact w.property
    rcases Submodule.mem_sup.mp hwSum with ⟨b, hb, p, hp, hbp⟩
    have hb₀ : b ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_left hb
    have hp₀ : p ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_right hp
    let bb : B₀ := ⟨b, hb₀⟩
    let pp : B₀ := ⟨p, hp₀⟩
    have heq : w = bb + pp := Subtype.ext hbp.symm
    refine ⟨Y p, hp, ?_⟩
    rw [← hw, heq, map_add, hzero bb hb, hcopy pp hp, zero_add]
  · rintro v ⟨a, ha, hqa⟩
    rcases hAY ha with ⟨p, hp⟩
    have hpA : p ∈ A.comap Y := by change Y p ∈ A; rw [hp]; exact ha
    have hp₀ : p ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_right hpA
    let pp : B₀ := ⟨p, hp₀⟩
    refine ⟨pp, ?_⟩
    rw [hcopy pp hpA, hp, hqa]

omit [FiniteDimensional K W] [FiniteDimensional K V] in
theorem a4_remainder_of_gluing (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀)) (hB₀ : B₀ = B ⊔ A.comap Y)
    (hzero : ∀ b : B₀, (b : W) ∈ B → X b = 0)
    (hcopy : ∀ p : B₀, Y p ∈ A → X p = A₀.mkQ (Y p)) :
    LinearMap.range (compress Y A₀ B₀ - X) ≤ (B.map Y).map A₀.mkQ ∧
      LinearMap.ker X ⊔ LinearMap.ker (compress Y A₀ B₀ - X) = ⊤ := by
  have decomp : ∀ w : B₀, ∃ b p : B₀,
      (b : W) ∈ B ∧ Y p ∈ A ∧ b + p = w := by
    intro w
    have hw : (w : W) ∈ B ⊔ A.comap Y := by rw [← hB₀]; exact w.property
    rcases Submodule.mem_sup.mp hw with ⟨b, hb, p, hp, hbp⟩
    have hb₀ : b ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_left hb
    have hp₀ : p ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_right hp
    exact ⟨⟨b, hb₀⟩, ⟨p, hp₀⟩, hb, hp, Subtype.ext hbp⟩
  constructor
  · rintro v ⟨w, hw⟩
    rcases decomp w with ⟨b, p, hb, hp, hbp⟩
    have hz : (compress Y A₀ B₀ - X) w = A₀.mkQ (Y b) := by
      rw [← hbp, map_add]
      change (compress Y A₀ B₀ b - X b) + (compress Y A₀ B₀ p - X p) = A₀.mkQ (Y b)
      rw [hzero b hb, hcopy p hp]
      simp only [compress_apply, sub_zero, sub_self, add_zero]
    exact ⟨Y b, ⟨(b : W), hb, rfl⟩, hz.symm.trans hw⟩
  · apply le_antisymm le_top
    intro w _
    rcases decomp w with ⟨b, p, hb, hp, hbp⟩
    have hpker : p ∈ LinearMap.ker (compress Y A₀ B₀ - X) := by
      change compress Y A₀ B₀ p - X p = 0
      rw [hcopy p hp]
      exact sub_self _
    exact Submodule.mem_sup.mpr ⟨b, hzero b hb, p, hpker, hbp⟩

abbrev A4Index := Σ A₀ : Submodule K V, Σ B₀ : Submodule K W, B₀ →ₗ[K] (V ⧸ A₀)

/-- The full index and selectors of a right-hand summand of (A.4). -/
def A4Survives (Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W)
    (p : A4Index (K := K) (W := W) (V := V)) : Prop :=
  p.1 ≤ A ∧ B ≤ p.2.1 ∧ Hybrid Y p.1 p.2.1 ∧
    LinearMap.ker p.2.2 = B.comap p.2.1.subtype ∧
    LinearMap.range p.2.2 = A.map p.1.mkQ ∧
    RankAdditivity.RankBelow p.2.2 (compress Y p.1 p.2.1)

omit [FiniteDimensional K V] in
theorem a4_surviving_index_unique (Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (p q : A4Index (K := K) (W := W) (V := V))
    (hp : A4Survives Y A B p) (hq : A4Survives Y A B q) : p = q := by
  rcases p with ⟨A₀, B₀, X₀⟩
  rcases q with ⟨A₁, B₁, X₁⟩
  rcases hp with ⟨ha₀, hb₀, hi₀, hk₀, him₀, hr₀⟩
  rcases hq with ⟨ha₁, hb₁, hi₁, hk₁, him₁, hr₁⟩
  have heA : A₀ = A₁ := (a4_codomain_forced Y A₀ A B B₀ X₀ ha₀ hb₀ hi₀ hk₀ him₀ hr₀).trans
    (a4_codomain_forced Y A₁ A B B₁ X₁ ha₁ hb₁ hi₁ hk₁ him₁ hr₁).symm
  have heB : B₀ = B₁ := (a4_domain_forced Y A₀ A B B₀ X₀ ha₀ hb₀ hi₀ hk₀ him₀ hr₀).trans
    (a4_domain_forced Y A₁ A B B₁ X₁ ha₁ hb₁ hi₁ hk₁ him₁ hr₁).symm
  subst A₁
  subst B₁
  have heX := a4_map_unique Y A₀ A B B₀ X₀ X₁ ha₀ hb₀ hi₀ hk₀ hk₁ him₀ him₁ hr₀ hr₁
  cases heX
  rfl

end MaxCutGames.Appendix.LinearIdentities

namespace MaxCutGames.Appendix.BinaryA4

open LinearIdentities

abbrev F2 := DegreeCover.F2
variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 W] [FiniteDimensional F2 V]

omit [FiniteDimensional F2 W] [FiniteDimensional F2 V] in
/-- Construct the actual linear map in the canonical (A.4) summand by
gluing zero on `B` with `Q_A₀ Y` on `Y⁻¹(A)`. -/
theorem canonical_glued_map (Y : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W) :
    ∃ X : ↥(B ⊔ A.comap Y) →ₗ[F2] (V ⧸ ((B.map Y) ⊓ A)),
      (∀ b : ↥(B ⊔ A.comap Y), (b : W) ∈ B → X b = 0) ∧
      (∀ p : ↥(B ⊔ A.comap Y), Y p ∈ A → X p = ((B.map Y) ⊓ A).mkQ (Y p)) := by
  let P := A.comap Y
  let A₀ := (B.map Y) ⊓ A
  let B₀ := B ⊔ P
  let pp := P.comap B₀.subtype
  let bb := B.comap B₀.subtype
  let f := compress Y A₀ B₀
  have hc : pp ⊔ bb = ⊤ := by
    apply le_antisymm le_top
    intro w _
    rcases Submodule.mem_sup.mp w.property with ⟨b, hb, p, hp, hbp⟩
    let pv : B₀ := ⟨p, Submodule.mem_sup_right hp⟩
    let bv : B₀ := ⟨b, Submodule.mem_sup_left hb⟩
    refine Submodule.mem_sup.mpr ⟨pv, hp, bv, hb, ?_⟩
    apply Subtype.ext
    change p + b = (w : W)
    rw [add_comm]
    exact hbp
  have compat : ∀ w ∈ pp, w ∈ bb → f w = 0 := by
    intro w hp hb
    have hm : Y w ∈ A₀ := ⟨⟨(w : W), hb, rfl⟩, hp⟩
    change Y w ∈ LinearMap.ker A₀.mkQ
    rw [Submodule.ker_mkQ]
    exact hm
  obtain ⟨X, hcopy, hzero⟩ := DegreeCover.exists_glue_zero pp bb f hc compat
  refine ⟨X, ?_, ?_⟩
  · intro b hb
    exact hzero b hb
  · intro p hp
    exact hcopy p hp

theorem a4_selector_exists (Y : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W)
    (hAY : A ≤ LinearMap.range Y) (hKY : LinearMap.ker Y ≤ B) :
    ∃ p : A4Index (K := F2) (W := W) (V := V), A4Survives Y A B p := by
  obtain ⟨X, hzero, hcopy⟩ := canonical_glued_map Y A B
  let A₀ := (B.map Y) ⊓ A
  let B₀ := B ⊔ A.comap Y
  have inner : Hybrid Y A₀ B₀ := by
    constructor
    · intro a ha
      rcases ha.1 with ⟨b, _, hb⟩
      exact ⟨b, hb⟩
    · intro w hw
      have hy : Y w ∈ (B.map Y) ⊓ A := hw
      exact Submodule.mem_sup_right hy.2
  have hk := a4_kernel_of_gluing Y A₀ A B B₀ X rfl rfl hKY hzero hcopy
  have hi := a4_range_of_gluing Y A₀ A B B₀ X rfl hAY hzero hcopy
  have hr := a4_remainder_of_gluing Y A₀ A B B₀ X rfl hzero hcopy
  have hd := disjoint_quotient_images_of_intersection A₀ A (B.map Y) rfl
  have hl : RankAdditivity.RankBelow X (compress Y A₀ B₀) := by
    apply (RankAdditivity.rankBelow_iff X (compress Y A₀ B₀)).mpr
    refine ⟨?_, hr.2⟩
    rw [hi]
    exact hd.mono_right hr.1
  exact ⟨⟨A₀, B₀, X⟩, inf_le_right, le_sup_left, inner, hk, hi, hl⟩

/-- The complete unique-index selector identity in (A.4) for arbitrary
finite-dimensional binary vector spaces. The index records both subspaces
and the genuine linear map with the required kernel and range. -/
theorem a4_unique_selector (Y : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W) :
    (A ≤ LinearMap.range Y ∧ LinearMap.ker Y ≤ B) ↔
      ∃! p : A4Index (K := F2) (W := W) (V := V), A4Survives Y A B p := by
  constructor
  · rintro ⟨ha, hb⟩
    obtain ⟨p, hp⟩ := a4_selector_exists Y A B ha hb
    exact ⟨p, hp, fun q hq => a4_surviving_index_unique Y A B q p hq hp⟩
  · rintro ⟨⟨A₀, B₀, X⟩, hp, _⟩
    rcases hp with ⟨_, _, inner, hk, hi, hr⟩
    exact a4_weak_selector_of_summand Y A₀ A B B₀ X inner hk hi hr

end MaxCutGames.Appendix.BinaryA4

end OAI
