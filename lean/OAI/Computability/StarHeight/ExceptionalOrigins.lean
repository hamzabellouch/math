import OAI.Computability.StarHeight.AffineClock

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uJ uC uAlphabet2 uJ2 uC2 uP uP2
universe uT uAlphabet3 uJ3 uC3
universe uPBad

namespace ExceptionalOrigins

open scoped Classical
open LocalMarkers

variable {Alphabet : Type uAlphabet} {J : Type uJ} {C : Type uC}

structure Parameters (Alphabet : Type uAlphabet2) (J : Type uJ2) (C : Type uC2) where
  endRule : CanonicalEpisodes.Parameters Alphabet
  d : ℕ
  K : ℕ
  B : ℕ
  B_pos : 0 < B
  end_modulus : endRule.B = B
  innerRule : Rule Alphabet d K
  offset : J → ℤ
  H : Fin B → ℤ
  w : ℤ
  w₀ : ℤ
  ext : ℤ
  φ : ℤ →+ (C → RobustClock.Circle)
  W : Set (C → RobustClock.Circle)

namespace Parameters

variable (A : Parameters Alphabet J C)

def residue (z : ℤ) : Fin A.B := by
  have hB : (0 : ℤ) < A.B := by exact_mod_cast A.B_pos
  exact ⟨(z % A.B).toNat, (Int.toNat_lt (Int.emod_nonneg z (ne_of_gt hB))).mpr
    (Int.emod_lt_of_pos z hB)⟩

lemma residue_val (z : ℤ) : ((A.residue z).val : ℤ) = z % A.B := by
  have hB : (0 : ℤ) < A.B := by exact_mod_cast A.B_pos
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (ne_of_gt hB))

lemma residue_ne {Q t δ δ' : ℤ} (hd : δ % A.B ≠ δ' % A.B) :
    A.residue (Q - (t + δ)) ≠ A.residue (Q - (t + δ')) := by
  intro he
  have hh := congrArg (fun u : Fin A.B => (u.val : ℤ)) he
  rw [A.residue_val,A.residue_val] at hh
  have hmod := (show Int.ModEq (A.B : ℤ) (Q - (t + δ)) (Q - (t + δ')) from hh).sub_left (Q-t)
  apply hd
  change Int.ModEq (A.B : ℤ) δ δ'
  convert hmod using 1 <;> ring

noncomputable def inner (f : ℤ → Alphabet) (j : J) (u : Fin A.B) (t : ℤ) : Option ℤ :=
  MarkerSearch.search (A.innerRule.markers f) (t + A.offset j) (t + A.offset j + A.H u)

def Z (f : ℤ → Alphabet) (t : ℤ) : Prop :=
  EndSearch.Unstable (A.endRule.rule.markers f) A.B A.endRule.S A.endRule.d
    (t + A.endRule.offset) A.w ∨
  EndSearch.Unstable (A.endRule.rule.markers f) A.B A.endRule.S (3 * A.endRule.d)
    (t + A.endRule.offset) A.w

def Star (f : ℤ → Alphabet) (t Q : ℤ) : Prop :=
  A.φ (Q-t) ∈ A.W ∨ ∃ j, MarkerSearch.InnerFailure (A.innerRule.markers f)
    (t + A.offset j) (A.H (A.residue (Q-t))) A.w₀ A.ext

def Failed (f : ℤ → Alphabet) (t Q : ℤ) : Prop := A.Z f t ∨ A.Star f t Q

noncomputable def anchor (f : ℤ → Alphabet) (q₀ t : ℤ) : ℤ :=
  (A.endRule.large f (t + A.endRule.offset)).getD q₀

noncomputable def bad {P : Type uPBad} [Fintype P] (p : P → ℤ) (f : ℤ → Alphabet) (t q₀ : ℤ) : Finset (P × P) :=
  Finset.univ.filter fun ij => ij.1 ≠ ij.2 ∧
    A.Failed f (t + (p ij.1 - p ij.2)) (A.anchor f q₀ (t + (p ij.1 - p ij.2)))

lemma width_inner_count {P : Type uP} (pairs : Finset (P × P)) (δ : P × P → ℤ)
    (h : ℤ) (hw₀ : 0 ≤ A.w₀) (hinner : 2 * h + 2 * A.w₀ < A.d)
    (hbound : ∀ ij ∈ pairs, |δ ij| ≤ h)
    (hgap : ∀ ij ∈ pairs, ∀ kl ∈ pairs, ij ≠ kl → 2 * A.w₀ < |δ ij - δ kl|)
    (hmod : ∀ ij ∈ pairs, ∀ kl ∈ pairs, ij ≠ kl → δ ij % A.B ≠ δ kl % A.B)
    (hwidth : ∀ u v, u ≠ v → 2 * h + 2 * max A.ext A.w₀ < |A.H u - A.H v|)
    (f : ℤ → Alphabet) (t Q : ℤ) (j : J) :
    (pairs.filter fun ij => MarkerSearch.InnerFailure (A.innerRule.markers f)
      (t + A.offset j + δ ij) (A.H (A.residue (Q - (t + δ ij)))) A.w₀ A.ext).card ≤ 3 := by
  classical
  apply MarkerSearch.innerFailure_card pairs δ
    (fun ij => A.H (A.residue (Q - (t + δ ij)))) (A.innerRule.separated f) hw₀ hinner hbound hgap
  intro ij hij kl hkl hn
  have hu := A.residue_ne (Q := Q) (t := t) (hmod ij hij kl hkl hn)
  have hw := hwidth _ _ hu
  have hi := abs_le.mp (hbound ij hij)
  have hk := abs_le.mp (hbound kl hkl)
  let a := A.H (A.residue (Q - (t + δ ij)))
  let b := A.H (A.residue (Q - (t + δ kl)))
  let z := t + A.offset j
  have hh : |a - b| ≤ |(z + δ ij + a) - (z + δ kl + b)| + |δ kl - δ ij| := by
    calc
      |a - b| = |((z + δ ij + a) - (z + δ kl + b)) + (δ kl - δ ij)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hd : |δ kl - δ ij| ≤ 2 * h := abs_le.mpr ⟨by omega,by omega⟩
  change 2 * max A.ext A.w₀ < |(z + δ ij + a) - (z + δ kl + b)|
  change 2 * h + 2 * max A.ext A.w₀ < |a - b| at hw
  omega

lemma bad_card {P : Type uP2} {T : Type uT} [Fintype P] [Fintype T] [Fintype C] [Fintype J]
    (clock : RobustClock.Specification T P C) (p : P → ℤ) (h hgap : ℤ)
    (hW : A.W = clock.W) (hpert : ∀ i, dist (A.φ (p i)) (clock.v i) < clock.η)
    (hbound : ∀ i j, |p i - p j| ≤ h)
    (hmod : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
      (p i - p j) % A.B ≠ (p i' - p j') % A.B)
    (hdiff : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
      hgap < |(p i - p j) - (p i' - p j')|)
    (hw₀ : 0 ≤ A.w₀) (hgap₀ : 2 * A.w₀ ≤ hgap)
    (hinner : 2 * h + 2 * A.w₀ < A.d)
    (hwidth : ∀ u v, u ≠ v → 2 * h + 2 * max A.ext A.w₀ < |A.H u - A.H v|)
    (hS : 2 * h + 2 * A.w < A.endRule.S)
    (hend : 2 * h + (A.B - 1) * A.endRule.S + 2 * A.w < A.endRule.d)
    (hanchor : 2 * h + 2 * (A.B - 1) * A.endRule.S < A.endRule.d)
    (μ : ℕ)
    (hμ : 20 * (10000000 * Real.log (2 * Fintype.card T) + 4 * Fintype.card J) + 10 < μ)
    (f : ℤ → Alphabet) (t q₀ : ℤ) : (A.bad p f t q₀).card < μ := by
  classical
  let : DecidableEq (P × P) := fun a b => Classical.propDecidable (a = b)
  let pairs : Finset (P × P) := Finset.univ.filter fun ij => ij.1 ≠ ij.2
  let δ : P × P → ℤ := fun ij => p ij.1 - p ij.2
  let Qs : Finset ℤ := (Finset.univ : Finset (P × P)).image
    (fun ij => A.anchor f q₀ (t + δ ij))
  let unstable := pairs.filter fun ij => A.Z f (t + δ ij)
  let clocks := fun Q => pairs.filter fun ij => A.φ (Q - (t + δ ij)) ∈ A.W
  let inners := fun Q j => pairs.filter fun ij => MarkerSearch.InnerFailure
    (A.innerRule.markers f) (t + A.offset j + δ ij)
      (A.H (A.residue (Q - (t + δ ij)))) A.w₀ A.ext
  have hB : (0 : ℤ) < A.B := by exact_mod_cast A.B_pos
  have hbound' : ∀ ij ∈ pairs, |δ ij| ≤ h := fun ij _ => hbound ij.1 ij.2
  have hmod' : ∀ ij ∈ pairs, ∀ kl ∈ pairs, ij ≠ kl → δ ij % A.B ≠ δ kl % A.B := by
    intro ij hij kl hkl hn
    exact hmod ij.1 ij.2 kl.1 kl.2 (Finset.mem_filter.mp hij).2
      (Finset.mem_filter.mp hkl).2 hn
  have hsepEnd : MarkerSearch.Separated (A.endRule.rule.markers f) A.endRule.d :=
    A.endRule.rule.separated f
  have hQs : Qs.card ≤ 20 := by
    have he := EndSearch.anchor_card (Finset.univ : Finset (P × P))
      (z := t + A.endRule.offset) (q₀ := q₀) δ hB A.endRule.S_nonneg
      (by have := A.endRule.d_ge; omega) hsepEnd hanchor (fun ij _ => hbound ij.1 ij.2)
    have hQeq : Qs = (Finset.univ : Finset (P × P)).image
        (fun ij => (EndSearch.search (A.endRule.rule.markers f) A.B A.endRule.S
          (3 * A.endRule.d) (t + A.endRule.offset + δ ij)).getD q₀) := by
      simp only [Qs,anchor,CanonicalEpisodes.Parameters.large,A.end_modulus,add_right_comm t]
    rw [hQeq]
    exact he.trans (by norm_num)
  have hUnstable : unstable.card ≤ 4 := by
    have he := EndSearch.two_searches_card (a₀ := A.endRule.d) (a₁ := 3 * A.endRule.d)
      (z := t + A.endRule.offset) pairs δ hB hS A.endRule.S_nonneg hsepEnd hend hbound' hmod'
    simpa only [unstable,Z,add_right_comm t] using he
  have hc : 0 ≤ 10000000 * Real.log (2 * Fintype.card T) := by
    by_cases hT : Fintype.card T = 0
    · simp [hT]
    · apply mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * Fintype.card T)))
  apply StencilSparsity.whole_stencil (A.bad p f t q₀) unstable Qs Finset.univ clocks inners
    (10000000 * Real.log (2 * Fintype.card T)) μ hc hQs hUnstable
  · intro Q _
    have hcc := clock.count (fun i => A.φ (p i)) hpert (A.φ (Q-t))
    have he : clocks Q = RobustClock.badPairs clock.W (A.φ (Q-t)) (fun i => A.φ (p i)) := by
      ext ij
      simp only [clocks,pairs,RobustClock.badPairs,Finset.mem_filter,Finset.mem_univ,true_and,hW]
      rw [show Q - (t + δ ij) = (Q-t) + p ij.2 - p ij.1 by dsimp [δ]; ring,
        map_sub,map_add]
    rw [he]
    exact hcc
  · intro Q _ j _
    exact A.width_inner_count pairs δ h hw₀ hinner hbound'
      (fun ij hij kl hkl hn => hgap₀.trans_lt (hdiff ij.1 ij.2 kl.1 kl.2
        (Finset.mem_filter.mp hij).2 (Finset.mem_filter.mp hkl).2 hn)) hmod' hwidth f t Q j
  · intro ij hij
    obtain ⟨_,hn,hfail⟩ := Finset.mem_filter.mp hij
    have hijp : ij ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩
    rcases hfail with hz | hc' | ⟨j,hj⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hijp,hz⟩)
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨A.anchor f q₀ (t + δ ij),Finset.mem_image.mpr ⟨ij,Finset.mem_univ _,rfl⟩,?_⟩
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hijp,hc'⟩)
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨A.anchor f q₀ (t + δ ij),Finset.mem_image.mpr ⟨ij,Finset.mem_univ _,rfl⟩,?_⟩
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hijp,by simpa only [add_right_comm t] using hj⟩⟩
  · simpa only [Finset.card_univ] using hμ

end Parameters

end ExceptionalOrigins

namespace MarkerSearch

lemma search_congr {S S' : Set ℤ} {l r : ℤ}
    (h : ∀ m, l ≤ m → m ≤ r → (m ∈ S ↔ m ∈ S')) : search S l r = search S' l r := by
  classical
  have he : (Finset.Icc l r).filter (· ∈ S) = (Finset.Icc l r).filter (· ∈ S') := by
    ext m
    simp only [Finset.mem_filter,Finset.mem_Icc]
    exact and_congr_right fun hm => h m hm.1 hm.2
  simp only [search,he]

lemma innerFailure_congr {S S' : Set ℤ} {z H w E : ℤ} (hw : 0 ≤ w)
    (h : ∀ m, z-w ≤ m → m ≤ z+H+max E w → (m ∈ S ↔ m ∈ S')) :
    InnerFailure S z H w E ↔ InnerFailure S' z H w E := by
  have hsearch : ∀ v, |v| ≤ w → search S (z+v) (z+H+v) = search S' (z+v) (z+H+v) := by
    intro v hv
    have hb := abs_le.mp hv
    apply search_congr
    intro m hm hm'
    exact h m (by omega) (by have := le_max_right E w; omega)
  have hzero := hsearch 0 (by simpa using hw)
  simp only [add_zero] at hzero
  have hex : (∃ m ∈ S, z ≤ m ∧ m ≤ z+H+E) ↔ (∃ m ∈ S', z ≤ m ∧ m ≤ z+H+E) := by
    constructor <;> rintro ⟨m,hm,hl,hr⟩
    · exact ⟨m,(h m (by omega) (by have := le_max_left E w; omega)).mp hm,hl,hr⟩
    · exact ⟨m,(h m (by omega) (by have := le_max_left E w; omega)).mpr hm,hl,hr⟩
  simp only [InnerFailure,hzero,hex]
  apply or_congr_left
  apply exists_congr
  intro v
  apply and_congr_right
  intro hv
  rw [hsearch v hv]

end MarkerSearch

namespace EndSearch

lemma unstable_congr {S S' : Set ℤ} {B D a z w : ℤ}
    (hzero : search S B D a z = search S' B D a z)
    (hshift : ∀ v, B ∣ v → |v| ≤ w → search S B D a (z+v) = search S' B D a (z+v)) :
    Unstable S B D a z w ↔ Unstable S' B D a z w := by
  unfold Unstable
  apply exists_congr
  intro v
  apply and_congr_right
  intro hv
  apply and_congr_right
  intro hw
  rw [hzero,hshift v hv hw]

end EndSearch

namespace ExceptionalOrigins.Parameters

open LocalMarkers

variable {Alphabet : Type uAlphabet3} {J : Type uJ3} {C : Type uC3} (A : ExceptionalOrigins.Parameters Alphabet J C)

structure Visible (s b t Q : ℤ) : Prop where
  base : A.endRule.Visible s b (t + A.endRule.offset)
  ends : ∀ v, (A.B : ℤ) ∣ v → |v| ≤ A.w →
    s ≤ t + A.endRule.offset + v - A.endRule.width - A.endRule.rule.r ∧
      t + A.endRule.offset + v + A.endRule.width + A.endRule.rule.r ≤ b
  inner : ∀ j,
    s ≤ t + A.offset j - A.w₀ - A.innerRule.r ∧
      t + A.offset j + A.H (A.residue (Q-t)) + max A.ext A.w₀ + A.innerRule.r ≤ b

lemma Visible.mono {s b s' b' t Q : ℤ} (hv : A.Visible s b t Q)
    (hs : s' ≤ s) (hb : b ≤ b') : A.Visible s' b' t Q := by
  refine ⟨CanonicalEpisodes.Parameters.Visible.mono A.endRule hv.base hs hb,?_,?_⟩
  · intro v hd hw
    exact ⟨hs.trans (hv.ends v hd hw).1,(hv.ends v hd hw).2.trans hb⟩
  · intro j
    exact ⟨hs.trans (hv.inner j).1,(hv.inner j).2.trans hb⟩

lemma Visible.min {s b b' t Q : ℤ} (hv : A.Visible s b t Q)
    (hv' : A.Visible s b' t Q) : A.Visible s (min b b') t Q := by
  refine ⟨⟨hv.base.1,le_min hv.base.2.1 hv'.base.2.1,
    hv.base.2.2.1,le_min hv.base.2.2.2 hv'.base.2.2.2⟩,?_,?_⟩
  · intro v hd hw
    exact ⟨(hv.ends v hd hw).1,le_min (hv.ends v hd hw).2 (hv'.ends v hd hw).2⟩
  · intro j
    exact ⟨(hv.inner j).1,le_min (hv.inner j).2 (hv'.inner j).2⟩

lemma Z_congr {s b t Q : ℤ} {f g : ℤ → Alphabet}
    (hv : A.Visible s b t Q) (he : AgreesOn f g s b) : A.Z f t ↔ A.Z g t := by
  have h0 := A.endRule.searches_congr hv.base he
  have hsh : ∀ v, (A.B : ℤ) ∣ v → |v| ≤ A.w →
      A.endRule.small f (t + A.endRule.offset + v) = A.endRule.small g (t + A.endRule.offset + v) ∧
      A.endRule.large f (t + A.endRule.offset + v) = A.endRule.large g (t + A.endRule.offset + v) := by
    intro v hd hw
    have hbounds := hv.ends v hd hw
    have hwidth := A.endRule.small_width_le
    constructor
    · apply EndSearch.search_local A.endRule.rule
      intro x hx hx'
      exact he x (by omega) (by omega)
    · apply EndSearch.search_local A.endRule.rule
      intro x hx hx'
      exact he x (by dsimp [CanonicalEpisodes.Parameters.width] at hbounds; omega)
        (by dsimp [CanonicalEpisodes.Parameters.width] at hbounds; omega)
  have hη : EndSearch.Unstable (A.endRule.rule.markers f) A.endRule.B A.endRule.S A.endRule.d
      (t + A.endRule.offset) A.w ↔ EndSearch.Unstable (A.endRule.rule.markers g)
        A.endRule.B A.endRule.S A.endRule.d (t + A.endRule.offset) A.w :=
    EndSearch.unstable_congr h0.1 (fun v hv hw => (hsh v (A.end_modulus ▸ hv) hw).1)
  have hζ : EndSearch.Unstable (A.endRule.rule.markers f) A.endRule.B A.endRule.S (3 * A.endRule.d)
      (t + A.endRule.offset) A.w ↔ EndSearch.Unstable (A.endRule.rule.markers g)
        A.endRule.B A.endRule.S (3 * A.endRule.d) (t + A.endRule.offset) A.w :=
    EndSearch.unstable_congr h0.2 (fun v hv hw => (hsh v (A.end_modulus ▸ hv) hw).2)
  simpa only [Z,A.end_modulus] using or_congr hη hζ

lemma Failed_congr {s b t Q : ℤ} {f g : ℤ → Alphabet}
    (hw₀ : 0 ≤ A.w₀) (hv : A.Visible s b t Q) (he : AgreesOn f g s b) :
    A.Failed f t Q ↔ A.Failed g t Q := by
  apply or_congr (A.Z_congr hv he)
  apply or_congr_right
  apply exists_congr
  intro j
  apply MarkerSearch.innerFailure_congr hw₀
  intro m hm hm'
  apply A.innerRule.locality
  intro x hx hx'
  exact he x (by have := (hv.inner j).1; omega) (by have := (hv.inner j).2; omega)

end ExceptionalOrigins.Parameters

end GeneralizedStarHeight

end OAI
