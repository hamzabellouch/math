import OAI.Combinatorics.PlanarL1.Probability

namespace OAI

section

namespace PlanarL1
/-! ## The deterministic clamping core of thin-band interpolation
No probabilistic or geometric claim is assumed by
these lemmas; they establish the scalar inequalities used at each actual node. -/

namespace Interpolation

/-- The exact parent/tentative clamp in the source: `U=max parent A`,
`L=min parent B`, and `F=min U (max L T)`. -/
def nodeValue (parent upper lower tentative : ℝ) : ℝ :=
  min (max parent upper) (max (min parent lower) tentative)

/-- Whenever both barrier cones exclude movement, an equality collar preserves
the parent value exactly. -/
theorem nodeValue_collar {parent upper lower tentative : ℝ}
    (hu : upper ≤ parent) (hl : parent ≤ lower) :
    nodeValue parent upper lower tentative = parent := by
  simp only [nodeValue, max_eq_left hu, min_eq_left hl]
  exact min_eq_left (le_max_left _ _)

/-- Clamping into an interval whose upper end is not too small and whose lower
end is not too large preserves the claimed accuracy window. -/
theorem nodeValue_bounds {parent upper lower tentative lo hi : ℝ}
    (hlo : lo ≤ upper) (hhi : lower ≤ hi)
    (htlo : lo ≤ tentative) (hthi : tentative ≤ hi) :
    lo ≤ nodeValue parent upper lower tentative ∧
      nodeValue parent upper lower tentative ≤ hi := by
  constructor
  · exact le_min (hlo.trans (le_max_right _ _)) (htlo.trans (le_max_right _ _))
  · exact (min_le_right _ _).trans (max_le ((min_le_right _ _).trans hhi) hthi)

/-- The obstruction in `int:depth`: a distant node cannot pass an accurate
parent value unchanged. The constants 6, 7 and 13 are the source's constants. -/
theorem distant_node_overwrites {parent upper lower tentative p δ : ℝ}
    (hδ : 0 < δ) (hp : |parent - p| ≤ 6 * δ)
    (hu : p + 7 * δ < upper) (hl : lower < p - 7 * δ)
    (ht : p + 13 * δ < tentative) :
    p + 7 * δ < nodeValue parent upper lower tentative ∧
      nodeValue parent upper lower tentative ≠ parent := by
  have habs := abs_le.mp hp
  have hup : parent < upper := by linarith
  have hlow : lower < parent := by linarith
  have hv : p + 7 * δ < nodeValue parent upper lower tentative := by
    simp only [nodeValue, max_eq_right hup.le, min_eq_right hlow.le]
    exact lt_min hu ((by linarith : p + 7 * δ < tentative).trans_le (le_max_right _ _))
  refine ⟨hv, ?_⟩
  intro heq
  rw [heq] at hv
  linarith

/-- An atom evaluation together with its deterministic priority/inheritance
name. Its value may depend on all the already sampled ancestor noises. -/
structure NamedValue where
  name : ℕ
  value : ℝ

/-- Minima and maxima both resolve ties toward the earliest atom name. -/
noncomputable def minNamed (a b : NamedValue) : NamedValue :=
  if a.value < b.value ∨ (a.value = b.value ∧ a.name ≤ b.name) then a else b

noncomputable def maxNamed (a b : NamedValue) : NamedValue :=
  if b.value < a.value ∨ (a.value = b.value ∧ a.name ≤ b.name) then a else b

lemma minNamed_mem (a b : NamedValue) : minNamed a b = a ∨ minNamed a b = b := by
  unfold minNamed
  split_ifs <;> simp

lemma maxNamed_mem (a b : NamedValue) : maxNamed a b = a ∨ maxNamed a b = b := by
  unfold maxNamed
  split_ifs <;> simp

@[simp]
lemma minNamed_value (a b : NamedValue) : (minNamed a b).value = min a.value b.value := by
  unfold minNamed
  split_ifs with h
  · rcases h with h | ⟨h, _⟩
    · exact (min_eq_left h.le).symm
    · exact (min_eq_left h.le).symm
  · have hh : b.value ≤ a.value := le_of_not_gt (fun hh => h (Or.inl hh))
    exact (min_eq_right hh).symm

@[simp]
lemma maxNamed_value (a b : NamedValue) : (maxNamed a b).value = max a.value b.value := by
  unfold maxNamed
  split_ifs with h
  · rcases h with h | ⟨h, _⟩
    · exact (max_eq_left h.le).symm
    · exact (max_eq_left h.ge).symm
  · have hh : a.value ≤ b.value := le_of_not_gt (fun hh => h (Or.inl hh))
    exact (max_eq_right hh).symm

/-- The clamp with the manuscript's consistent atom-name tie rule. -/
noncomputable def nodeNamed (parent upper lower tentative : NamedValue) : NamedValue :=
  minNamed (maxNamed parent upper) (maxNamed (minNamed parent lower) tentative)

@[simp]
lemma nodeNamed_value (parent upper lower tentative : NamedValue) :
    (nodeNamed parent upper lower tentative).value =
      nodeValue parent.value upper.value lower.value tentative.value := by
  simp [nodeNamed, nodeValue]

lemma nodeNamed_mem (parent upper lower tentative : NamedValue) :
    nodeNamed parent upper lower tentative = parent ∨
    nodeNamed parent upper lower tentative = upper ∨
    nodeNamed parent upper lower tentative = lower ∨
    nodeNamed parent upper lower tentative = tentative := by
  rcases minNamed_mem (maxNamed parent upper)
      (maxNamed (minNamed parent lower) tentative) with h | h
  · rcases maxNamed_mem parent upper with h' | h'
    · exact Or.inl (h.trans h')
    · exact Or.inr (Or.inl (h.trans h'))
  · rcases maxNamed_mem (minNamed parent lower) tentative with h' | h'
    · rcases minNamed_mem parent lower with h'' | h''
      · exact Or.inl ((h.trans h').trans h'')
      · exact Or.inr (Or.inr (Or.inl ((h.trans h').trans h'')))
    · exact Or.inr (Or.inr (Or.inr (h.trans h')))

/-- A name from before the current node can only be selected by literally
inheriting the parent's atom. In particular its scalar value is inherited too. -/
lemma nodeNamed_old {parent upper lower tentative : NamedValue} {cutoff : ℕ}
    (hu : cutoff ≤ upper.name) (hl : cutoff ≤ lower.name)
    (ht : cutoff ≤ tentative.name)
    (h : (nodeNamed parent upper lower tentative).name < cutoff) :
    nodeNamed parent upper lower tentative = parent := by
  rcases nodeNamed_mem parent upper lower tentative with heq | heq | heq | heq
  · exact heq
  all_goals rw [heq] at h; omega

/-- The complete equality collar, including exact retention of the parent
atom's name . -/
lemma nodeNamed_collar {parent upper lower tentative : NamedValue}
    (hu : upper.value < parent.value) (hl : parent.value < lower.value)
    (ht : parent.name ≤ tentative.name) :
    nodeNamed parent upper lower tentative = parent := by
  have hU : maxNamed parent upper = parent := by
    simp only [maxNamed, ite_eq_left (Or.inl hu)]
  have hL : minNamed parent lower = parent := by
    simp only [minNamed, ite_eq_left (Or.inl hl)]
  simp only [nodeNamed, hU, hL]
  rcases lt_trichotomy parent.value tentative.value with h | h | h
  · have hm : maxNamed parent tentative = tentative := by
      apply ite_eq_right
      push Not
      exact ⟨h.le, fun hh => (h.ne hh).elim⟩
    rw [hm]
    exact ite_eq_left (Or.inl h)
  · have hm : maxNamed parent tentative = parent := ite_eq_left (Or.inr ⟨h, ht⟩)
    rw [hm]
    exact ite_eq_left (Or.inr ⟨rfl, le_rfl⟩)
  · have hm : maxNamed parent tentative = parent := ite_eq_left (Or.inl h)
    rw [hm]
    exact ite_eq_left (Or.inr ⟨rfl, le_rfl⟩)

/-- Iterated inheritance along a fixed ancestor chain. This does not make
any independence assumption on the already computed scalar intercepts. -/
lemma chain_inherits {F U L T : ℕ → NamedValue} {k n cutoff : ℕ}
    (hkn : k ≤ n)
    (hrec : ∀ j, F (j + 1) = nodeNamed (F j) (U (j + 1)) (L (j + 1)) (T (j + 1)))
    (hnew : ∀ j, k ≤ j → j < n →
      cutoff ≤ (U (j + 1)).name ∧ cutoff ≤ (L (j + 1)).name ∧
        cutoff ≤ (T (j + 1)).name)
    (hout : (F n).name < cutoff) : F n = F k := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn ih =>
    obtain ⟨hu, hl, ht⟩ := hnew n hkn (Nat.lt_succ_self n)
    have hstep : F (n + 1) = F n := by
      rw [hrec n] at hout ⊢
      exact nodeNamed_old hu hl ht hout
    exact hstep.trans (ih (fun j hkj hjn => hnew j hkj (hjn.trans (Nat.lt_succ_self n)))
      (hstep ▸ hout))

/-- Quantitative bounded ancestry. At a distant node `k`, the source's 7δ/13δ
barriers prevent an accurate final value from retaining a name originating
strictly before `k`. All actual new atoms of stage `j` have names ≥ `6*j`.
This is the substantive inheritance argument of lemma `int:depth`. -/
theorem bounded_ancestry {F U L T : ℕ → NamedValue} {k n : ℕ} {p δ : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hδ : 0 < δ)
    (hrec : ∀ j, F (j + 1) = nodeNamed (F j) (U (j + 1)) (L (j + 1)) (T (j + 1)))
    (hnew : ∀ j, 6 * j ≤ (U j).name ∧ 6 * j ≤ (L j).name ∧ 6 * j ≤ (T j).name)
    (haccuracy : |(F n).value - p| ≤ 6 * δ)
    (hu : p + 7 * δ < (U k).value) (hl : (L k).value < p - 7 * δ)
    (ht : p + 13 * δ < (T k).value) : 6 * k ≤ (F n).name := by
  by_contra hh
  have hout : (F n).name < 6 * k := by omega
  have heq : F n = F (k - 1) := by
    apply chain_inherits (by omega) hrec _ hout
    intro j hj hjn
    have hkj : 6 * k ≤ 6 * (j + 1) := by omega
    exact ⟨hkj.trans (hnew (j + 1)).1, hkj.trans (hnew (j + 1)).2.1,
      hkj.trans (hnew (j + 1)).2.2⟩
  have hmid : F n = F k := by
    apply chain_inherits hkn hrec _ hout
    intro j hj hjn
    have hkj : 6 * k ≤ 6 * (j + 1) := by omega
    exact ⟨hkj.trans (hnew (j + 1)).1, hkj.trans (hnew (j + 1)).2.1,
      hkj.trans (hnew (j + 1)).2.2⟩
  have hkrec : F k = nodeNamed (F (k - 1)) (U k) (L k) (T k) := by
    simpa only [Nat.sub_add_cancel hk] using hrec (k - 1)
  have hp : |(F (k - 1)).value - p| ≤ 6 * δ := by simpa only [← heq] using haccuracy
  have hneq := (distant_node_overwrites hδ hp hu hl ht).2
  apply hneq
  rw [← nodeNamed_value, ← hkrec, ← hmid, heq]

/-- There are at most `6*(M+1)` names in the last `M+1` levels, independently
of the total depth. This is the exact deterministic list-size bound `N`. -/
lemma recent_name_count (n M : ℕ) :
    (Finset.Ico (6 * (n - M)) (6 * (n + 1))).card ≤ 6 * (M + 1) := by
  rw [Nat.card_Ico]
  omega

/-- Both signed distance cones have their exact unit Lipschitz constant. -/
lemma distance_cone_lipschitz {X : Type*} [PseudoMetricSpace X] (x : X) (c : ℝ) :
    LipschitzWith 1 (fun v => c + dist x v) ∧
      LipschitzWith 1 (fun v => c - dist x v) := by
  constructor <;> apply LipschitzWith.of_dist_le_mul <;> intro u v
  · simpa only [Real.dist_eq, add_sub_add_left_eq_sub, NNReal.coe_one, one_mul, dist_comm x] using
      abs_dist_sub_le u v x
  · rw [Real.dist_eq]
    have he : c - dist x u - (c - dist x v) = dist x v - dist x u := by ring
    rw [he, abs_sub_comm]
    simpa only [NNReal.coe_one, one_mul, dist_comm x] using abs_dist_sub_le u v x

lemma nodeValue_lipschitz {X : Type*} [PseudoMetricSpace X]
    {P A B T : X → ℝ} (hP : LipschitzWith 1 P) (hA : LipschitzWith 1 A)
    (hB : LipschitzWith 1 B) (hT : LipschitzWith 1 T) :
    LipschitzWith 1 (fun x => nodeValue (P x) (A x) (B x) (T x)) := by
  simpa only [nodeValue, max_self] using (hP.max hA).min ((hP.min hB).max hT)


end Interpolation



end PlanarL1

end

section

namespace PlanarL1.Interpolation
open scoped NNReal

/-- A continuous finite selection cannot change its recorded branch on a ball
without a near tie at the center. This includes the old-field branch of a
clipping, even though that branch has no fresh offset of its own. -/
lemma selection_near_tie {X : Type*} [PseudoMetricSpace X] {K : ℝ≥0}
    (F : X → NamedValue) (atom : ℕ → X → ℝ) (S : Finset ℕ)
    (hF : LipschitzWith K (fun z => (F z).value))
    (hA : ∀ i ∈ S, LipschitzWith K (atom i)) (x : X) {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hlist : ∀ z, dist x z ≤ ρ → (F z).name ∈ S ∧ (F z).value = atom (F z).name z)
    (hbad : ∃ z, dist x z ≤ ρ ∧ (F z).name ≠ (F x).name) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ |atom i x-atom j x| ≤ 2*K*ρ := by
  obtain ⟨z,hz,hn⟩ := hbad
  have hx := hlist x (by simpa using hρ)
  have hz' := hlist z hz
  refine ⟨(F x).name,hx.1,(F z).name,hz'.1,Ne.symm hn,?_⟩
  have hf := hF.dist_le_mul x z
  have ha := (hA (F z).name hz'.1).dist_le_mul z x
  rw [Real.dist_eq,dist_comm z x,← hz'.2] at ha
  rw [Real.dist_eq] at hf
  rw [← hx.2]
  have ht := abs_sub_le (F x).value (F z).value (atom (F z).name x)
  have hm := mul_le_mul_of_nonneg_left hz K.coe_nonneg
  linarith

lemma selection_probability {X Ω : Type*} [PseudoMetricSpace X] [Fintype Ω]
    {K : ℝ≥0} (F : Ω → X → NamedValue) (atom : Ω → ℕ → X → ℝ)
    (S : Finset ℕ) (hF : ∀ ω, LipschitzWith K (fun z => (F ω z).value))
    (hA : ∀ ω i, i ∈ S → LipschitzWith K (atom ω i)) (x : X) {ρ b : ℝ}
    (hρ : 0 ≤ ρ) (hb : 0 ≤ b)
    (hlist : ∀ ω z, dist x z ≤ ρ → (F ω z).name ∈ S ∧
      (F ω z).value = atom ω (F ω z).name z)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      FiniteRandom.prob (fun ω => |atom ω i x-atom ω j x| ≤ 2*K*ρ) ≤ b) :
    FiniteRandom.prob (fun ω => ∃ z, dist x z ≤ ρ ∧ (F ω z).name ≠ (F ω x).name) ≤
      S.card^2*b := by
  apply (FiniteRandom.prob_mono (fun ω h =>
    selection_near_tie (F ω) (atom ω) S (hF ω) (hA ω) x hρ (hlist ω) h)).trans
  exact FiniteRandom.prob_pair_bound S _ hb hpair

end PlanarL1.Interpolation


end

section

namespace PlanarL1.Interpolation
open scoped NNReal

noncomputable def clippedNamed (o p h : NamedValue) : NamedValue :=
  maxNamed o (minNamed p h)

lemma clippedNamed_mem (o p h : NamedValue) :
    clippedNamed o p h = o ∨ clippedNamed o p h = p ∨ clippedNamed o p h = h := by
  rcases maxNamed_mem o (minNamed p h) with he | he
  · exact Or.inl he
  · rcases minNamed_mem p h with he' | he'
    · exact Or.inr (Or.inl (he.trans he'))
    · exact Or.inr (Or.inr (he.trans he'))

lemma clippedNamed_value (o p h : NamedValue) :
    (clippedNamed o p h).value = max o.value (min p.value h.value) := by
  simp only [clippedNamed,maxNamed_value,minNamed_value]

noncomputable def clipNames (S : Finset ℕ) : Finset ℕ :=
  insert 0 (insert 1 (S.image (fun i => i+2)))

lemma clipNames_card (S : Finset ℕ) : (clipNames S).card ≤ S.card+2 := by
  calc
    _ ≤ (insert 1 (S.image (fun i => i+2))).card+1 := Finset.card_insert_le _ _
    _ ≤ (S.image (fun i => i+2)).card+1+1 := Nat.add_le_add_right (Finset.card_insert_le _ _) _
    _ ≤ S.card+2 := by have h := Finset.card_image_le (s := S) (f := fun i => i+2); omega

lemma mem_clipNames {S : Finset ℕ} {i : ℕ} :
    i ∈ clipNames S ↔ i = 0 ∨ i = 1 ∨ (2 ≤ i ∧ i-2 ∈ S) := by
  simp only [clipNames,Finset.mem_insert,Finset.mem_image]
  constructor
  · rintro (h | h | ⟨j,hj,rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨by omega,by simpa using hj⟩)
  · rintro (h | h | ⟨hi,hS⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨i-2,hS,by omega⟩)

/-- The old field has priority zero; the shield has priority one, and actual
inherited atom identities are shifted by two. Thus a retaining tie keeps the
old identifier, just as required by the source chart update. -/
noncomputable def namedClip {X : Type*} (F : X → NamedValue) (old shield : X → ℝ)
    (x : X) : NamedValue :=
  clippedNamed ⟨0,old x⟩ ⟨(F x).name+2,(F x).value⟩ ⟨1,shield x⟩

noncomputable def clipAtom {X : Type*} (atom : ℕ → X → ℝ) (old shield : X → ℝ)
    (i : ℕ) (x : X) : ℝ := if i = 0 then old x else if i = 1 then shield x else atom (i-2) x

lemma namedClip_list {X : Type*} (F : X → NamedValue) (atom : ℕ → X → ℝ)
    (old shield : X → ℝ) (S : Finset ℕ) (x : X)
    (hm : (F x).name ∈ S) (he : (F x).value = atom (F x).name x) :
    (namedClip F old shield x).name ∈ clipNames S ∧
      (namedClip F old shield x).value = clipAtom atom old shield (namedClip F old shield x).name x := by
  rcases clippedNamed_mem ⟨0,old x⟩ ⟨(F x).name+2,(F x).value⟩ ⟨1,shield x⟩ with h | h | h
  · change namedClip F old shield x = _ at h
    rw [h]
    simp [clipNames,clipAtom]
  · change namedClip F old shield x = _ at h
    rw [h]
    dsimp only
    have hz : (F x).name+2 ≠ 0 := by omega
    have ho : (F x).name+2 ≠ 1 := by omega
    constructor
    · exact mem_clipNames.mpr (Or.inr (Or.inr ⟨by omega,by simpa using hm⟩))
    · simpa only [clipAtom,ite_eq_right hz,ite_eq_right ho,Nat.add_sub_cancel] using he
  · change namedClip F old shield x = _ at h
    rw [h]
    simp [clipNames,clipAtom]

lemma clipAtom_lipschitz {X : Type*} [PseudoMetricSpace X] {K : ℝ≥0}
    (atom : ℕ → X → ℝ) (old shield : X → ℝ)
    (hA : ∀ i, LipschitzWith K (atom i)) (ho : LipschitzWith K old)
    (hh : LipschitzWith K shield) (i : ℕ) :
    LipschitzWith K (clipAtom atom old shield i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  dsimp only [clipAtom]
  split_ifs with hi hi'
  · exact ho.dist_le_mul x y
  · exact hh.dist_le_mul x y
  · exact (hA (i-2)).dist_le_mul x y

end PlanarL1.Interpolation


namespace PlanarL1.Interpolation
lemma clippedNamed_retains {o p h : NamedValue} (hp : p.value < o.value) :
    clippedNamed o p h = o := by
  have ht : (minNamed p h).value < o.value := by
    rw [minNamed_value]
    exact (min_le_left _ _).trans_lt hp
  exact ite_eq_left (Or.inl ht)
end PlanarL1.Interpolation


end

section

namespace PlanarL1.Interpolation
open scoped NNReal

noncomputable def secondaryNames (S : Finset ℕ) : Finset ℕ :=
  insert 0 (insert 1 (insert 2 (S.image (fun i => i+3))))

lemma secondaryNames_card (S : Finset ℕ) : (secondaryNames S).card ≤ S.card+3 := by
  unfold secondaryNames
  calc
    _ ≤ ((S.image (fun i => i+3)).card+1)+1+1 := by
      exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right
          (Finset.card_insert_le _ _) 1)) 1)
    _ ≤ S.card+3 := by have h := Finset.card_image_le (s := S) (f := fun i => i+3); omega

lemma mem_secondaryNames {S : Finset ℕ} {i : ℕ} :
    i ∈ secondaryNames S ↔ i=0 ∨ i=1 ∨ i=2 ∨ (3 ≤ i ∧ i-3 ∈ S) := by
  classical
  simp only [secondaryNames,Finset.mem_insert,Finset.mem_image]
  constructor
  · rintro (h | h | h | ⟨j,hj,h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · right; right; right
      exact ⟨by omega,by simpa only [← h,Nat.add_sub_cancel] using hj⟩
  · rintro (h | h | h | ⟨hi,h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · right; right; right
      exact ⟨i-3,h,by omega⟩

noncomputable def secondaryNamed {X : Type*} (F : X → NamedValue)
    (old ordered shield : X → ℝ) (ordinary : Bool) (x : X) : NamedValue :=
  clippedNamed ⟨0,old x⟩
    (if ordinary then minNamed ⟨(F x).name+3,(F x).value⟩ ⟨2,ordered x⟩
      else ⟨(F x).name+3,(F x).value⟩) ⟨1,shield x⟩

noncomputable def secondaryAtom {X : Type*} (atom : ℕ → X → ℝ)
    (old ordered shield : X → ℝ) (i : ℕ) (x : X) : ℝ :=
  if i=0 then old x else if i=1 then shield x else if i=2 then ordered x else atom (i-3) x

lemma secondaryNamed_value {X : Type*} (F : X → NamedValue)
    (old ordered shield : X → ℝ) (ordinary : Bool) (x : X) :
    (secondaryNamed F old ordered shield ordinary x).value =
      max (old x) (min (if ordinary then min (F x).value (ordered x) else (F x).value) (shield x)) := by
  cases ordinary <;> simp only [secondaryNamed,clippedNamed_value,Bool.false_eq_true,
    ite_false,ite_true,minNamed_value]

lemma secondaryNamed_mem {X : Type*} (F : X → NamedValue)
    (old ordered shield : X → ℝ) (ordinary : Bool) (x : X) :
    secondaryNamed F old ordered shield ordinary x = ⟨0,old x⟩ ∨
    secondaryNamed F old ordered shield ordinary x = ⟨1,shield x⟩ ∨
    secondaryNamed F old ordered shield ordinary x = ⟨2,ordered x⟩ ∨
    secondaryNamed F old ordered shield ordinary x = ⟨(F x).name+3,(F x).value⟩ := by
  rcases clippedNamed_mem ⟨0,old x⟩
    (if ordinary then minNamed ⟨(F x).name+3,(F x).value⟩ ⟨2,ordered x⟩
      else ⟨(F x).name+3,(F x).value⟩) ⟨1,shield x⟩ with h | h | h
  · exact Or.inl h
  · change secondaryNamed F old ordered shield ordinary x = _ at h
    cases ordinary with
    | false => exact Or.inr (Or.inr (Or.inr h))
    | true =>
      rcases minNamed_mem ⟨(F x).name+3,(F x).value⟩ ⟨2,ordered x⟩ with ha | ha
      · exact Or.inr (Or.inr (Or.inr (h.trans ha)))
      · exact Or.inr (Or.inr (Or.inl (h.trans ha)))
  · exact Or.inr (Or.inl h)

lemma secondaryNamed_list {X : Type*} (F : X → NamedValue) (atom : ℕ → X → ℝ)
    (old ordered shield : X → ℝ) (ordinary : Bool) (S : Finset ℕ) (x : X)
    (hm : (F x).name ∈ S) (he : (F x).value = atom (F x).name x) :
    (secondaryNamed F old ordered shield ordinary x).name ∈ secondaryNames S ∧
      (secondaryNamed F old ordered shield ordinary x).value =
        secondaryAtom atom old ordered shield (secondaryNamed F old ordered shield ordinary x).name x := by
  rcases secondaryNamed_mem F old ordered shield ordinary x with h | h | h | h
  · rw [h]; simp [secondaryNames,secondaryAtom]
  · rw [h]; simp [secondaryNames,secondaryAtom]
  · rw [h]; simp [secondaryNames,secondaryAtom]
  · rw [h]
    dsimp only
    have h0 : (F x).name+3 ≠ 0 := by omega
    have h1 : (F x).name+3 ≠ 1 := by omega
    have h2 : (F x).name+3 ≠ 2 := by omega
    constructor
    · exact mem_secondaryNames.mpr (Or.inr (Or.inr (Or.inr ⟨by omega,by simpa using hm⟩)))
    · simpa only [secondaryAtom,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,Nat.add_sub_cancel] using he

lemma secondaryAtom_lipschitz {X : Type*} [PseudoMetricSpace X] {K : ℝ≥0}
    (atom : ℕ → X → ℝ) (old ordered shield : X → ℝ)
    (hA : ∀ i, LipschitzWith K (atom i)) (ho : LipschitzWith K old)
    (hO : LipschitzWith K ordered) (hh : LipschitzWith K shield) (i : ℕ) :
    LipschitzWith K (secondaryAtom atom old ordered shield i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  dsimp only [secondaryAtom]
  split_ifs with hi hi' hi''
  · exact ho.dist_le_mul x y
  · exact hh.dist_le_mul x y
  · exact hO.dist_le_mul x y
  · exact (hA (i-3)).dist_le_mul x y

end PlanarL1.Interpolation


end

section

namespace PlanarL1.Interpolation
open scoped NNReal

/-- Retained old branches are shared (name zero). Every genuinely new group
branch receives a distinct name including its group, not merely its formula. -/
def familyName {k : ℕ} (g : Fin k) (i : ℕ) : ℕ :=
  if i=0 then 0 else Nat.pair g.val (i-1)+1

lemma familyName_zero {k : ℕ} (g : Fin k) : familyName g 0 = 0 := by
  simp [familyName]

lemma familyName_ne_zero {k : ℕ} (g : Fin k) {i : ℕ} (hi : i ≠ 0) :
    familyName g i ≠ 0 := by simp [familyName,hi]

lemma familyName_inj {k : ℕ} (g h : Fin k) {i j : ℕ} (hi : i ≠ 0) (hj : j ≠ 0) :
    familyName g i = familyName h j ↔ g=h ∧ i=j := by
  simp only [familyName,ite_eq_right hi,ite_eq_right hj,Nat.add_right_cancel_iff,Nat.pair_eq_pair]
  constructor
  · rintro ⟨hg,hs⟩
    exact ⟨Fin.ext hg,by omega⟩
  · rintro ⟨rfl,rfl⟩; exact ⟨rfl,rfl⟩

noncomputable def familyNames {k : ℕ} (S : Fin k → Finset ℕ) : Finset ℕ :=
  insert 0 (Finset.univ.biUnion (fun g => (S g).image (familyName g)))

lemma mem_familyNames {k : ℕ} {S : Fin k → Finset ℕ} {i : ℕ} :
    i ∈ familyNames S ↔ i=0 ∨ ∃ g, ∃ j ∈ S g, familyName g j=i := by
  classical
  simp [familyNames]

lemma familyNames_card {k N : ℕ} (S : Fin k → Finset ℕ)
    (hS : ∀ g, (S g).card ≤ N) : (familyNames S).card ≤ 1+k*N := by
  classical
  calc
    _ ≤ (Finset.univ.biUnion (fun g => (S g).image (familyName g))).card+1 := Finset.card_insert_le _ _
    _ ≤ (∑ g : Fin k, ((S g).image (familyName g)).card)+1 :=
      Nat.add_le_add_right Finset.card_biUnion_le 1
    _ ≤ (∑ _g : Fin k, N)+1 := Nat.add_le_add_right (Finset.sum_le_sum (fun g _ =>
      (Finset.card_image_le (s := S g) (f := familyName g)).trans (hS g))) 1
    _ = 1+k*N := by simp [Nat.add_comm]

noncomputable def familyAtom {X : Type*} {k : ℕ} (old : X → ℝ)
    (A : Fin k → ℕ → X → ℝ) (i : ℕ) (x : X) : ℝ :=
  if i=0 then old x else if h : (Nat.unpair (i-1)).1 < k then
    A ⟨(Nat.unpair (i-1)).1,h⟩ ((Nat.unpair (i-1)).2+1) x else old x

lemma familyAtom_zero {X : Type*} {k : ℕ} (old : X → ℝ)
    (A : Fin k → ℕ → X → ℝ) (x : X) : familyAtom old A 0 x = old x := by
  simp [familyAtom]

lemma familyAtom_name {X : Type*} {k : ℕ} (old : X → ℝ)
    (A : Fin k → ℕ → X → ℝ) (g : Fin k) {i : ℕ} (hi : i ≠ 0) (x : X) :
    familyAtom old A (familyName g i) x = A g i x := by
  have hg := g.isLt
  simp [familyAtom,familyName,hi,Nat.unpair_pair,hg,show i-1+1=i by omega]

lemma familyAtom_lipschitz {X : Type*} [PseudoMetricSpace X] {k : ℕ} {K : ℝ≥0}
    (old : X → ℝ) (A : Fin k → ℕ → X → ℝ) (ho : LipschitzWith K old)
    (hA : ∀ g i, LipschitzWith K (A g i)) (i : ℕ) :
    LipschitzWith K (familyAtom old A i) := by
  unfold familyAtom
  split_ifs with h h'
  · exact ho
  · exact hA _ _
  · exact ho

/-- Comparisons in one group use the local fresh-offset estimate. Comparisons
between groups condition on all other samples and then use a constant test. -/
lemma familyAtomPair_probability {X Ω : Type*} {k : ℕ} [Fintype Ω] [Nonempty Ω]
    (old : X → ℝ) (A : Fin k → Ω → ℕ → X → ℝ) (S : Fin k → Finset ℕ)
    (x : X) {t b : ℝ}
    (hpair : ∀ g i, i ∈ S g → ∀ j, j ∈ S g → i ≠ j →
      FiniteRandom.prob (fun ω => |A g ω i x-A g ω j x| ≤ t) ≤ b)
    (hconst : ∀ g i, i ∈ S g → i ≠ 0 → ∀ c : ℝ,
      FiniteRandom.prob (fun ω => |A g ω i x-c| ≤ t) ≤ b)
    (i j : ℕ) (hi : i ∈ familyNames S) (hj : j ∈ familyNames S) (hne : i ≠ j) :
    FiniteRandom.prob (fun ω : Fin k → Ω =>
      |familyAtom old (fun g => A g (ω g)) i x-familyAtom old (fun g => A g (ω g)) j x| ≤ t) ≤ b := by
  classical
  rcases mem_familyNames.mp hi with rfl | ⟨g,a,ha,rfl⟩
  · obtain ⟨h,c,hc,hcj⟩ := (mem_familyNames.mp hj).resolve_left (Ne.symm hne)
    subst j
    have hc0 : c ≠ 0 := by intro he; subst c; simp only [familyName_zero] at hne; exact hne rfl
    simp only [familyAtom_zero,familyAtom_name old _ h hc0]
    apply FiniteRandom.prob_update_bound h
    intro ω
    simpa only [Function.update_self,abs_sub_comm] using hconst h c hc hc0 (old x)
  · rcases mem_familyNames.mp hj with rfl | ⟨h,c,hc,rfl⟩
    · have ha0 : a ≠ 0 := by intro he; subst a; simp only [familyName_zero] at hne; exact hne rfl
      simp only [familyAtom_name old _ g ha0,familyAtom_zero]
      apply FiniteRandom.prob_update_bound g
      intro ω
      simpa only [Function.update_self] using hconst g a ha ha0 (old x)
    · by_cases ha0 : a=0
      · subst a
        have hc0 : c ≠ 0 := by intro he; subst c; simp only [familyName_zero] at hne; exact hne rfl
        simp only [familyName_zero,familyAtom_zero,familyAtom_name old _ h hc0]
        apply FiniteRandom.prob_update_bound h
        intro ω
        simpa only [Function.update_self,abs_sub_comm] using hconst h c hc hc0 (old x)
      · by_cases hc0 : c=0
        · subst c
          simp only [familyName_zero,familyAtom_zero,familyAtom_name old _ g ha0]
          apply FiniteRandom.prob_update_bound g
          intro ω
          simpa only [Function.update_self] using hconst g a ha ha0 (old x)
        · simp only [familyAtom_name old _ g ha0,familyAtom_name old _ h hc0]
          by_cases hgh : g=h
          · subst h
            have hac : a ≠ c := by intro he; subst c; exact hne rfl
            apply FiniteRandom.prob_update_bound g
            intro ω
            simpa only [Function.update_self] using hpair g a ha c hc hac
          · apply FiniteRandom.prob_update_bound g
            intro ω
            simpa only [Function.update_self,Function.update_of_ne (Ne.symm hgh)] using
              hconst g a ha ha0 (A h (ω h) c x)


noncomputable def maxSelection {X : Type*} (old : X → NamedValue) :
    List (X → NamedValue) → X → NamedValue
  | [], x => old x
  | F::Fs, x => maxNamed (F x) (maxSelection old Fs x)

lemma maxSelection_mem {X : Type*} (old : X → NamedValue)
    (Fs : List (X → NamedValue)) (x : X) :
    maxSelection old Fs x = old x ∨ ∃ F ∈ Fs, maxSelection old Fs x = F x := by
  induction Fs with
  | nil => exact Or.inl rfl
  | cons F Fs ih =>
    rcases maxNamed_mem (F x) (maxSelection old Fs x) with h | h
    · exact Or.inr ⟨F,by simp,h⟩
    · change maxSelection old (F::Fs) x = _ at h
      rcases ih with ih | ⟨G,hG,he⟩
      · exact Or.inl (h.trans ih)
      · exact Or.inr ⟨G,List.mem_cons_of_mem _ hG,h.trans he⟩

lemma maxSelection_lipschitz {X : Type*} [PseudoMetricSpace X] {K : ℝ≥0}
    (old : X → NamedValue) (Fs : List (X → NamedValue))
    (ho : LipschitzWith K (fun x => (old x).value))
    (hF : ∀ F ∈ Fs, LipschitzWith K (fun x => (F x).value)) :
    LipschitzWith K (fun x => (maxSelection old Fs x).value) := by
  induction Fs with
  | nil => exact ho
  | cons F Fs ih =>
    simp only [maxSelection,maxNamed_value]
    simpa only [max_self] using (hF F (by simp)).max (ih (fun G hG => hF G (List.mem_cons_of_mem _ hG)))

noncomputable def familySelection {X : Type*} {k : ℕ} (old : X → ℝ)
    (F : Fin k → X → NamedValue) : X → NamedValue :=
  maxSelection (fun x => ⟨0,old x⟩)
    (List.ofFn (fun g => fun x => ⟨familyName g (F g x).name,(F g x).value⟩))

lemma familySelection_list {X : Type*} {k : ℕ} (old : X → ℝ)
    (F : Fin k → X → NamedValue) (A : Fin k → ℕ → X → ℝ) (S : Fin k → Finset ℕ)
    (hzero : ∀ g x, A g 0 x = old x) (x : X)
    (hlist : ∀ g, (F g x).name ∈ S g ∧ (F g x).value = A g (F g x).name x) :
    (familySelection old F x).name ∈ familyNames S ∧
      (familySelection old F x).value = familyAtom old A (familySelection old F x).name x := by
  rcases maxSelection_mem (fun x => ⟨0,old x⟩)
    (List.ofFn (fun g => fun x => ⟨familyName g (F g x).name,(F g x).value⟩)) x with h | ⟨G,hG,h⟩
  · change familySelection old F x = _ at h
    rw [h]
    exact ⟨mem_familyNames.mpr (Or.inl rfl),(familyAtom_zero old A x).symm⟩
  · obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hG
    change familySelection old F x = _ at h
    rw [h]
    dsimp only
    constructor
    · exact mem_familyNames.mpr (Or.inr ⟨g,(F g x).name,(hlist g).1,rfl⟩)
    · rw [(hlist g).2]
      by_cases he : (F g x).name=0
      · rw [he,familyName_zero,familyAtom_zero,hzero]
      · rw [familyAtom_name old A g he]

lemma familySelection_lipschitz {X : Type*} [PseudoMetricSpace X] {k : ℕ} {K : ℝ≥0}
    (old : X → ℝ) (F : Fin k → X → NamedValue) (ho : LipschitzWith K old)
    (hF : ∀ g, LipschitzWith K (fun x => (F g x).value)) :
    LipschitzWith K (fun x => (familySelection old F x).value) := by
  apply maxSelection_lipschitz _ _ ho
  intro G hG
  obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hG
  exact hF g

/-- The literal deterministic finite maximum has a single identifier throughout
one small ball except for the finite pair-comparison events. -/
lemma familySelection_probability {X Ω : Type*} [PseudoMetricSpace X]
    [Fintype Ω] [Nonempty Ω] {k N : ℕ} {K : ℝ≥0}
    (old : X → ℝ) (F : Fin k → Ω → X → NamedValue)
    (A : Fin k → Ω → ℕ → X → ℝ) (S : Fin k → Finset ℕ)
    (ho : LipschitzWith K old)
    (hF : ∀ g ω, LipschitzWith K (fun z => (F g ω z).value))
    (hA : ∀ g ω i, LipschitzWith K (A g ω i))
    (hzero : ∀ g ω z, A g ω 0 z=old z) (hcard : ∀ g, (S g).card ≤ N)
    (x : X) {ρ b : ℝ} (hρ : 0 ≤ ρ) (hb : 0 ≤ b)
    (hlist : ∀ g ω z, dist x z ≤ ρ → (F g ω z).name ∈ S g ∧
      (F g ω z).value = A g ω (F g ω z).name z)
    (hpair : ∀ g i, i ∈ S g → ∀ j, j ∈ S g → i ≠ j →
      FiniteRandom.prob (fun ω => |A g ω i x-A g ω j x| ≤ 2*K*ρ) ≤ b)
    (hconst : ∀ g i, i ∈ S g → i ≠ 0 → ∀ c : ℝ,
      FiniteRandom.prob (fun ω => |A g ω i x-c| ≤ 2*K*ρ) ≤ b) :
    FiniteRandom.prob (fun ω : Fin k → Ω => ∃ z, dist x z ≤ ρ ∧
      (familySelection old (fun g => F g (ω g)) z).name ≠
        (familySelection old (fun g => F g (ω g)) x).name) ≤ (1+k*N : ℕ)^2*b := by
  have hp := selection_probability
    (fun ω : Fin k → Ω => familySelection old (fun g => F g (ω g)))
    (fun ω => familyAtom old (fun g => A g (ω g))) (familyNames S)
    (fun ω => familySelection_lipschitz old _ ho (fun g => hF g (ω g)))
    (fun ω i _ => familyAtom_lipschitz old _ ho (fun g j => hA g (ω g) j) i)
    x hρ hb (fun ω z hz => familySelection_list old _ _ S
      (fun g y => hzero g (ω g) y) z (fun g => hlist g (ω g) z hz))
    (fun i hi j hj hij => familyAtomPair_probability old A S x hpair hconst i j hi hj hij)
  refine hp.trans ?_
  apply mul_le_mul_of_nonneg_right _ hb
  apply pow_le_pow_left₀ (Nat.cast_nonneg _)
  exact_mod_cast familyNames_card S hcard

end PlanarL1.Interpolation


end

section

namespace PlanarL1.Interpolation
open scoped NNReal

lemma clippedNamed_eq_old_of_value {o p h : NamedValue}
    (hname : o.name = 0) (he : (clippedNamed o p h).value = o.value) :
    clippedNamed o p h = o := by
  have hle : (minNamed p h).value ≤ o.value := by
    rw [clippedNamed_value] at he
    rw [minNamed_value]
    exact max_eq_left_iff.mp he
  apply ite_eq_left
  rcases lt_or_eq_of_le hle with hh | hh
  · exact Or.inl hh
  · exact Or.inr ⟨hh.symm,by omega⟩

lemma namedClip_eq_old_iff {X : Type*} (F : X → NamedValue) (old shield : X → ℝ)
    (x : X) : (namedClip F old shield x).name = 0 ↔
      (namedClip F old shield x).value = old x := by
  constructor
  · intro hn
    rcases clippedNamed_mem ⟨0,old x⟩ ⟨(F x).name+2,(F x).value⟩ ⟨1,shield x⟩ with h | h | h
    · exact congrArg NamedValue.value h
    · change namedClip F old shield x = _ at h
      rw [h] at hn
      simp only at hn
      omega
    · change namedClip F old shield x = _ at h
      rw [h] at hn
      contradiction
  · intro he
    exact congrArg NamedValue.name (clippedNamed_eq_old_of_value rfl he)

end PlanarL1.Interpolation



end

end OAI
