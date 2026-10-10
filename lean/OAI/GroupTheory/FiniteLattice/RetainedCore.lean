import OAI.GroupTheory.FiniteLattice.PerfectPreimage
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Simple

namespace OAI

/-!
A relative normal core retains a nonabelian simple quotient when the adjoining
subgroups normalize suitable normal full preimages and centralize their images
in the quotient.
-/

open scoped commutatorElement

namespace FiniteLattice.RetainedCore

variable {M H : Type*} [Group M] [Group H]

/-- Minimality plus full image forces stability under every compatible pair
of genuine group automorphisms. No invariance is assumed of `Q`. -/
theorem least_full_preimage_stable
    (f : M →* H) (Q : Subgroup M) [Q.Normal]
    (hfull : Q.map f = ⊤)
    (hleast : ∀ B : Subgroup M, B.Normal → B.map f = ⊤ → Q ≤ B)
    (a : M ≃* M) (b : H ≃* H)
    (hcompat : ∀ x, f (a x) = b (f x)) :
    ∀ x ∈ Q, a x ∈ Q := by
  have hcomap : (Q.comap a.toMonoidHom).map f = ⊤ := by
    apply top_unique
    intro y _
    have hy : b y ∈ Q.map f := by rw [hfull]; trivial
    obtain ⟨x, hx, hfx⟩ := hy
    refine ⟨a.symm x, ?_, ?_⟩
    · change a (a.symm x) ∈ Q
      rw [a.apply_symm_apply]
      exact hx
    · apply b.injective
      calc
        b (f (a.symm x)) = f (a (a.symm x)) := (hcompat _).symm
        _ = f x := congrArg f (a.apply_symm_apply x)
        _ = b y := hfx
  have hle : Q ≤ Q.comap a.toMonoidHom :=
    hleast _ inferInstance hcomap
  exact fun x hx => hle hx

theorem least_full_preimage_map_eq
    (f : M →* H) (Q : Subgroup M) [Q.Normal]
    (hfull : Q.map f = ⊤)
    (hleast : ∀ B : Subgroup M, B.Normal → B.map f = ⊤ → Q ≤ B)
    (a : M ≃* M) (b : H ≃* H)
    (hcompat : ∀ x, f (a x) = b (f x)) :
    Q.map a.toMonoidHom = Q := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact least_full_preimage_stable f Q hfull hleast a b hcompat x hx
  · intro x hx
    have hinv : ∀ y, f (a.symm y) = b.symm (f y) := by
      intro y
      apply b.injective
      rw [b.apply_symm_apply]
      exact (hcompat (a.symm y)).symm.trans
        (congrArg f (a.apply_symm_apply y))
    exact ⟨a.symm x,
      least_full_preimage_stable f Q hfull hleast a.symm b.symm hinv x hx,
      a.apply_symm_apply x⟩

/-- A relative normal core maps onto a nonabelian simple quotient.
The subgroups `T i` lie in `R₀`; their ambient images are used for normalization
and commutators. The normal core inside the generated subgroup `W` is
transported back to `R₀`. The finite indexing type may be empty. -/
def Statement (D : Type*) [Group D] [Finite D]
    (R₀ : Subgroup D) (C : Subgroup R₀) [C.Normal]
    [IsSimpleGroup (R₀ ⧸ C)]
    (ι : Type*) [Finite ι] (L : ι → Subgroup D)
    (T : ι → Subgroup R₀) : Prop :=
  (∃ x y : R₀ ⧸ C, x * y ≠ y * x) →
  (∀ i, R₀ ≤ Subgroup.normalizer (L i : Set D)) →
  (∀ i, (T i).Normal) →
  (∀ i, T i ⊔ C = ⊤) →
  (∀ i, L i ≤ Subgroup.normalizer ((T i).map R₀.subtype : Set D)) →
  (∀ i, ⁅(T i).map R₀.subtype, L i⁆ ≤
    (T i).map R₀.subtype ⊓ C.map R₀.subtype) →
  let W : Subgroup D := R₀ ⊔ ⨆ i, L i
  ((((R₀.subgroupOf W).normalCore.map W.subtype).comap R₀.subtype).map
    (QuotientGroup.mk' C)) = ⊤

/-- A least normal full preimage, with equality-shaped minimality. -/
theorem exists_least_full_preimage [Finite M] [Group.IsPerfect H]
    (f : M →* H) (hf : Function.Surjective f) :
    ∃ Q : Subgroup M, Q.Normal ∧ Q.map f = ⊤ ∧
      ∀ B : Subgroup M, B.Normal → B.map f = ⊤ → Q ≤ B := by
  have htop : (⊤ : Subgroup H) ≤ f.range := by
    rw [MonoidHom.range_eq_top.mpr hf]
  obtain ⟨Q, hQ, hfull, hmin⟩ :=
    FiniteLattice.exists_least_normal_perfect_preimage f (⊤ : Subgroup H) htop
  exact ⟨Q, hQ, hfull, fun B hB hb => hmin B hB (by rw [hb])⟩

/-- Restrict ambient conjugation to an embedded subgroup, without assuming
that conjugation preserves the larger group into which that subgroup embeds. -/
noncomputable def embeddedConj {D : Type*} [Group D]
    (K : Subgroup M) (j : M →* D) (hj : Function.Injective j)
    (g : D) (hg : g ∈ Subgroup.normalizer (K.map j : Set D)) : K ≃* K :=
  let e := K.equivMapOfInjective j hj
  (e.trans ((K.map j).normalizerMonoidHom ⟨g, hg⟩)).trans e.symm

theorem embeddedConj_val {D : Type*} [Group D]
    (K : Subgroup M) (j : M →* D) (hj : Function.Injective j)
    (g : D) (hg : g ∈ Subgroup.normalizer (K.map j : Set D)) (x : K) :
    j (embeddedConj K j hj g hg x : M) = g * j (x : M) * g⁻¹ := by
  let e := K.equivMapOfInjective j hj
  have he (z : K.map j) : j (e.symm z : M) = (z : D) := by
    have h := congrArg (fun w : K.map j => (w : D)) (e.apply_symm_apply z)
    exact h
  change j (e.symm (((K.map j).normalizerMonoidHom ⟨g, hg⟩) (e x)) : M) = _
  rw [he]
  rfl

/-- The least full preimage inside a normal subgroup equals that inside
its ambient group. The quotient may be any perfect group. -/
theorem least_inside_normal_eq [Finite M] [Group.IsPerfect H]
    (f : M →* H) (Q : Subgroup M) [Q.Normal]
    (hQ : Q.map f = ⊤)
    (hminQ : ∀ B : Subgroup M, B.Normal → B.map f = ⊤ → Q ≤ B)
    (K : Subgroup M) [K.Normal]
    (hK : K.map f = ⊤)
    (B : Subgroup K) [B.Normal]
    (hB : B.map (f.comp K.subtype) = ⊤)
    (hminB : ∀ A : Subgroup K, A.Normal →
      A.map (f.comp K.subtype) = ⊤ → B ≤ A) :
    B.map K.subtype = Q := by
  have hBK : (B.map K.subtype).Normal := by
    refine ⟨?_⟩
    intro x hx r
    obtain ⟨b, hb, rfl⟩ := hx
    let a : K ≃* K := K.normalizerMonoidHom
      ⟨r, by rw [Subgroup.normalizer_eq_top]; trivial⟩
    have hc : ∀ z : K,
        (f.comp K.subtype) (a z) = (MulAut.conj (f r)) ((f.comp K.subtype) z) := by
      intro z
      change f (r * (z : M) * r⁻¹) = f r * f (z : M) * (f r)⁻¹
      simp only [map_mul, map_inv]
    refine ⟨a b, least_full_preimage_stable (f.comp K.subtype) B hB hminB
      a (MulAut.conj (f r)) hc b hb, ?_⟩
    rfl
  have hBfull : (B.map K.subtype).map f = ⊤ := by
    rw [Subgroup.map_map]
    exact hB
  have hQB := hminQ _ hBK hBfull
  have hQK : Q ≤ K := hminQ K inferInstance hK
  have hQrestrict : (Q.comap K.subtype).map (f.comp K.subtype) = ⊤ := by
    apply top_unique
    intro y _
    have hy : y ∈ Q.map f := by rw [hQ]; trivial
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hQK hx⟩, hx, hxy⟩
  have hBQ := hminB (Q.comap K.subtype) inferInstance hQrestrict
  exact le_antisymm (by rintro _ ⟨b, hb, rfl⟩; exact hBQ hb) hQB

/-- The relative normal core retains the entire nonabelian simple quotient. -/
theorem retained_core (D : Type*) [Group D] [Finite D]
    (R₀ : Subgroup D) (C : Subgroup R₀) [C.Normal]
    [IsSimpleGroup (R₀ ⧸ C)]
    (ι : Type*) [Finite ι] (L : ι → Subgroup D)
    (T : ι → Subgroup R₀) : Statement D R₀ C ι L T := by
  classical
  intro hnonabelian hRL hTN hTC hLT hcomm
  let π : R₀ →* R₀ ⧸ C := QuotientGroup.mk' C
  have hperfect : Group.IsPerfect (R₀ ⧸ C) := by
    constructor
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (R₀ ⧸ C))
      inferInstance with hbot | htop
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnonabelian
      have hcenter := (commutator_eq_bot_iff_center_eq_top (R₀ ⧸ C)).mp hbot
      have hx : x ∈ Subgroup.center (R₀ ⧸ C) := by rw [hcenter]; trivial
      exact hxy ((Subgroup.mem_center_iff.mp hx) y).symm
    · exact htop
  let : Group.IsPerfect (R₀ ⧸ C) := hperfect
  obtain ⟨Q, hQN, hQfull, hQmin⟩ :=
    exists_least_full_preimage π (QuotientGroup.mk'_surjective C)
  let : Q.Normal := hQN
  have hTfull (i : ι) : (T i).map π = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
    change x ∈ ((T i).map (QuotientGroup.mk' C)).comap (QuotientGroup.mk' C)
    rw [QuotientGroup.comap_map_mk', sup_comm, hTC i]
    trivial
  let QD : Subgroup D := Q.map R₀.subtype
  have hRnorm : R₀ ≤ Subgroup.normalizer (QD : Set D) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro r hr x hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨⟨r, hr⟩ * q * (⟨r, hr⟩ : R₀)⁻¹,
      hQN.conj_mem q hq ⟨r, hr⟩, rfl⟩
  have hLnorm (i : ι) : L i ≤ Subgroup.normalizer (QD : Set D) := by
    let : (T i).Normal := hTN i
    have hsurj : Function.Surjective (π.comp (T i).subtype) := by
      intro y
      have hy : y ∈ (T i).map π := by rw [hTfull i]; trivial
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, hx⟩, hxy⟩
    obtain ⟨B, hBN, hBfull, hBmin⟩ :=
      exists_least_full_preimage (π.comp (T i).subtype) hsurj
    let : B.Normal := hBN
    have hBQ : B.map (T i).subtype = Q :=
      least_inside_normal_eq π Q hQfull hQmin (T i) (hTfull i) B hBfull hBmin
    apply Subgroup.le_normalizer_iff.mpr
    intro l hl q hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    rw [← hBQ] at hq₀
    obtain ⟨b, hb, rfl⟩ := hq₀
    let a : T i ≃* T i := embeddedConj (T i) R₀.subtype
      Subtype.val_injective l (hLT i hl)
    have ha (x : T i) : R₀.subtype (a x : R₀) =
        l * R₀.subtype (x : R₀) * l⁻¹ :=
      embeddedConj_val (T i) R₀.subtype Subtype.val_injective l (hLT i hl) x
    have hcompat : ∀ x : T i,
        (π.comp (T i).subtype) (a x) =
          (MulEquiv.refl (R₀ ⧸ C)) ((π.comp (T i).subtype) x) := by
      intro x
      have hc : ⁅R₀.subtype (x : R₀), l⁆ ∈ C.map R₀.subtype :=
        (hcomm i (Subgroup.commutator_mem_commutator
          (show R₀.subtype (x : R₀) ∈ (T i).map R₀.subtype from
            ⟨(x : R₀), x.property, rfl⟩) hl)).2
      have he : R₀.subtype ((x : R₀) * (a x : R₀)⁻¹) =
          ⁅R₀.subtype (x : R₀), l⁆ := by
        rw [map_mul, map_inv, ha]
        simp only [commutatorElement_def, mul_inv_rev, inv_inv]
        simp only [mul_assoc]
      have hm : (x : R₀) * (a x : R₀)⁻¹ ∈ C := by
        obtain ⟨c, hc, hce⟩ := hc
        have hce' : c = (x : R₀) * (a x : R₀)⁻¹ :=
          Subtype.val_injective (hce.trans he.symm)
        exact hce' ▸ hc
      have hquot : π ((x : R₀) * (a x : R₀)⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff (N := C) _).mpr hm
      rw [map_mul, map_inv] at hquot
      exact (mul_inv_eq_one.mp hquot).symm
    have hab : a b ∈ B := least_full_preimage_stable
      (π.comp (T i).subtype) B hBfull hBmin a
      (MulEquiv.refl (R₀ ⧸ C)) hcompat b hb
    refine ⟨(a b : R₀), ?_, ha b⟩
    rw [← hBQ]
    exact ⟨a b, hab, rfl⟩
  let W : Subgroup D := R₀ ⊔ ⨆ i, L i
  have hWnorm : W ≤ Subgroup.normalizer (QD : Set D) := sup_le hRnorm (iSup_le hLnorm)
  have hQDle : QD ≤ R₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact x.property
  have hcore : Q ≤ ((R₀.subgroupOf W).normalCore.map W.subtype).comap R₀.subtype := by
    intro q hq
    have hqD : R₀.subtype q ∈ QD := ⟨q, hq, rfl⟩
    have hqW : R₀.subtype q ∈ W := (show R₀ ≤ W from le_sup_left) q.property
    refine ⟨⟨R₀.subtype q, hqW⟩, ?_, rfl⟩
    intro w
    change (w : D) * R₀.subtype q * (w : D)⁻¹ ∈ R₀
    exact hQDle (Subgroup.le_normalizer_iff.mp hWnorm
      (w : D) w.property (R₀.subtype q) hqD)
  change (((R₀.subgroupOf W).normalCore.map W.subtype).comap R₀.subtype).map π = ⊤
  apply top_unique
  rw [← hQfull]
  exact Subgroup.map_mono hcore

end FiniteLattice.RetainedCore

end OAI
