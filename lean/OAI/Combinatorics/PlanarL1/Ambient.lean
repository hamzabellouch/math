import OAI.Combinatorics.PlanarL1.OrderedState
import OAI.Combinatorics.PlanarL1.Increments

namespace OAI

section

namespace PlanarL1.Columns.Model
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)}

/-- Full columns regarded in the unrestricted path pseudometric. Connectedness
here is supplied by the connected graph realization, not an extra condition on
the embedding theorem. -/
structure Ambient (M : Model (k+1)) where
  root : Fin (k+1)
  connected : ∀ i, (M.activeGraph Set.univ).Reachable root i

namespace Ambient
variable (A : Ambient M)

def point (i : Fin (k+1)) (H : ℝ) : M.Point Set.univ A.root :=
  ⟨i,H,Set.mem_univ H,A.connected i⟩

lemma point_dist (i : Fin (k+1)) (H T : ℝ) :
    dist (A.point i H) (A.point i T)=|H-T| := (A.point i H).dist_same_column _ rfl

lemma point_switch (i j : Fin (k+1)) (H : ℝ) (hh : H ∈ M.heights i j) :
    dist (A.point i H) (A.point j H)=0 := by
  apply le_antisymm _ dist_nonneg
  simpa only [point,sub_self,abs_zero,add_zero] using
    (A.point i H).dist_le_switch (A.point j H) (Set.mem_univ H) hh

lemma taper_switch {r : ℝ} (hr : 0 < r) (S : Set (M.Point Set.univ A.root))
    (i j : Fin (k+1)) (H : ℝ) (hh : H ∈ M.heights i j) :
    Increment.taper S r (A.point i H)=Increment.taper S r (A.point j H) := by
  have h := Increment.taper_difference (S := S) hr (A.point i H) (A.point j H)
  rw [A.point_switch i j H hh,zero_div] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

/-- Every signed increment from the recorded lifetime is retained. Regions are
those at their creation times and are not re-tapered after subsequent changes. -/
noncomputable def historyField {I : Set ℝ} (s : M.Field I 4) (a b : Fin (k+1))
    {m : ℕ} (r : Fin m → ℝ) (regions : Fin m → Set (M.Point Set.univ A.root))
    (sign : Fin m → Bool) (c : ℝ) (hc : 0 < c) (hcr : c ≤ 4)
    (hr : ∀ j, 0 < r j)
    (hsep : ∀ i j, i ≠ j → 10*r i ≤ c*r j ∨ 10*r j ≤ c*r i) : M.Field I 100 where
  value i H := ∑ j, Increment.signedDamped (sign j) (c*r j) (r j)
    ((s.transverse (by norm_num) a b).value i)
    (fun T : I => Increment.taper (regions j)ᶜ (r j) (A.point i T.val)) H
  vertical i := by
    have h := Increment.damped_lifetime Finset.univ (r := r)
      (t := (s.transverse (by norm_num) a b).value i)
      (w := fun j (H : I) => Increment.taper (regions j)ᶜ (r j) (A.point i H.val))
      sign hc hcr (fun j _ => hr j) ((s.transverse (by norm_num) a b).vertical i)
      (fun j _ H => Increment.taper_bounds (hr j) (A.point i H.val))
      (fun j _ H T => by
        have h := Increment.taper_difference (S := (regions j)ᶜ) (hr j) (A.point i H.val) (A.point i T.val)
        simpa only [A.point_dist,Subtype.dist_eq,Real.dist_eq] using h)
      (fun i _ j _ hij => hsep i j hij)
    simpa only [Finset.mem_univ,Finset.sum_const_zero,ite_true] using h.weaken (by norm_num : (68:ℝ≥0) ≤ 100)
  switch i j H hh := by
    apply Finset.sum_congr rfl
    intro q _
    have ht := (s.transverse (by norm_num) a b).switch i j H hh
    have hw := A.taper_switch (hr q) (regions q)ᶜ i j H.val hh
    simp only [Increment.signedDamped,Increment.damped,ht,hw]

end Ambient
end PlanarL1.Columns.Model



end

section

namespace PlanarL1.Columns.Model.Ambient
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)}

/-- The literal finite list of increments already recorded for an identifier.
Regions are recorded at creation time, as required by . -/
structure History (A : Ambient M) (c : ℝ) where
  count : ℕ
  radius : Fin count → ℝ
  region : Fin count → Set (M.Point Set.univ A.root)
  sign : Fin count → Bool
  positive : ∀ i, 0 < radius i
  separated : ∀ i j, i≠j → 10*radius i ≤ c*radius j ∨ 10*radius j ≤ c*radius i

namespace History
variable {A : Ambient M} {c : ℝ}

def empty (A : Ambient M) (c : ℝ) : History A c where
  count := 0
  radius := Fin.elim0
  region := Fin.elim0
  sign := Fin.elim0
  positive := fun i => Fin.elim0 i
  separated := fun i => Fin.elim0 i

noncomputable def field (H : History A c) {I : Set ℝ} (s : M.Field I 4)
    (a b : Fin (k+1)) (hc : 0 < c) (hcr : c ≤ 4) : M.Field I 100 :=
  A.historyField s a b H.radius H.region H.sign c hc hcr H.positive H.separated

lemma field_empty {I : Set ℝ} (s : M.Field I 4) (a b : Fin (k+1))
    (hc : 0 < c) (hcr : c ≤ 4) (i : Fin (k+1)) (T : I) :
    ((empty A c).field s a b hc hcr).value i T=0 := by
  simp only [field,empty,historyField]
  exact Finset.sum_eq_zero (fun i _ => Fin.elim0 i)

def append (H : History A c) (r : ℝ) (S : Set (M.Point Set.univ A.root)) (e : Bool)
    (hr : 0 < r) (hcross : ∀ j, 10*r ≤ c*H.radius j) : History A c where
  count := H.count+1
  radius := Fin.snoc H.radius r
  region := Fin.snoc H.region S
  sign := Fin.snoc H.sign e
  positive i := by
    cases i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hr
    | cast i => simpa only [Fin.snoc_castSucc] using H.positive i
  separated i j hij := by
    cases i using Fin.lastCases with
    | last =>
      cases j using Fin.lastCases with
      | last => exact (hij rfl).elim
      | cast j => exact Or.inl (by simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hcross j)
    | cast i =>
      cases j using Fin.lastCases with
      | last => exact Or.inr (by simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hcross i)
      | cast j =>
        simpa only [Fin.snoc_castSucc] using H.separated i j (fun h => hij (congrArg Fin.castSucc h))

/-- No earlier summand is re-tapered or otherwise modified by appending a step. -/
lemma field_append_value (H : History A c) (r : ℝ) (S : Set (M.Point Set.univ A.root))
    (e : Bool) (hr : 0 < r) (hcross : ∀ j, 10*r ≤ c*H.radius j)
    {I : Set ℝ} (s : M.Field I 4) (a b : Fin (k+1)) (hc : 0 < c) (hcr : c ≤ 4)
    (i : Fin (k+1)) (T : I) :
    ((H.append r S e hr hcross).field s a b hc hcr).value i T =
      (H.field s a b hc hcr).value i T+
      Increment.signedDamped e (c*r) r ((s.transverse (by norm_num) a b).value i)
        (fun U : I => Increment.taper Sᶜ r (A.point i U.val)) T := by
  change (∑ j : Fin (H.count+1), _) = (∑ j : Fin H.count, _)+_
  rw [Fin.sum_univ_castSucc]
  simp only [append,Fin.snoc_castSucc,Fin.snoc_last]

end History
end PlanarL1.Columns.Model.Ambient



end

section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

namespace BData
variable {A : Ambient M} {c : ℝ}

def Recorded (D : BData M) (H : A.History c) (hc : 0 < c) (hcr : c ≤ 4) : Prop :=
  match D with
  | .ordinary _ => True
  | .ordered D => ∀ i T, D.auxiliary.value i T=(H.field D.base D.lower D.upper hc hcr).value i T

noncomputable def incrementAuxiliary (D : BData M) (H : A.History c)
    (r : ℝ) (region : Set (M.Point Set.univ A.root)) (e : Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ j, 10*r ≤ c*H.radius j) : D.Auxiliary :=
  match D with
  | .ordinary _ => ()
  | .ordered D => (H.append r region e hr hcross).field D.base D.lower D.upper hc hcr

/-- The actual recorded increment, not a replacement of the old history. -/
lemma increment_difference (D : OrderedData M) (H : A.History c)
    (r : ℝ) (region : Set (M.Point Set.univ A.root)) (e : Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ j, 10*r ≤ c*H.radius j)
    (hrec : (BData.ordered D).Recorded H hc hcr)
    (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100)
    (i : Fin (k+1)) (T : D.band) :
    ((BData.ordered D).auxiliaryField
      ((BData.ordered D).incrementAuxiliary H r region e hc hcr hr hcross) lam hlam).value i T -
      D.value lam i T =
      lam*Increment.signedDamped e (c*r) r ((D.base.transverse (by norm_num) D.lower D.upper).value i)
        (fun U : D.band => Increment.taper regionᶜ r (A.point i U.val)) T := by
  change ((D.withAuxiliary ((H.append r region e hr hcross).field D.base D.lower D.upper hc hcr)).field lam hlam).value i T - D.value lam i T = _
  erw [OrderedData.field_value,OrderedData.withAuxiliary_value]
  rw [hrec i T,Ambient.History.field_append_value]
  ring

lemma increment_boundary (D : BData M) (H : A.History c)
    (r : ℝ) (region : Set (M.Point Set.univ A.root)) (e : Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ j, 10*r ≤ c*H.radius j) (hrec : D.Recorded H hc hcr)
    (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100)
    (i : Fin (k+1)) (T : D.band) (U : ℝ) (hU : A.point i U ∉ region) :
    |(D.auxiliaryField (D.incrementAuxiliary H r region e hc hcr hr hcross) lam hlam).value i T -
      D.value lam i T| ≤ (lam:ℝ)*10*|T.val-U| := by
  cases D with
  | ordinary D =>
    change |D.value i T-D.value i T| ≤ _
    rw [sub_self,abs_zero]
    positivity
  | ordered D =>
    dsimp only [BData.value]
    erw [increment_difference D H r region e hc hcr hr hcross hrec lam hlam]
    rw [abs_mul,abs_of_nonneg lam.coe_nonneg]
    have hb := Increment.signed_tapered_magnitude e (mul_pos hc hr) hr
      (by nlinarith : 2*(c*r) ≤ 8*r) (show A.point i U ∈ regionᶜ from hU)
      (x := A.point i T.val) (q := (D.base.transverse (by norm_num) D.lower D.upper).value i T)
    rw [A.point_dist] at hb
    simpa only [Increment.signedDamped,Increment.damped,mul_assoc] using
      mul_le_mul_of_nonneg_left hb lam.coe_nonneg

/-- Ordinary identifiers record no increments. Ordered identifiers keep the
entire old list and append precisely the new signed region-tapered term. -/
def incrementHistory (D : BData M) (H : A.History c)
    (r : ℝ) (region : Set (M.Point Set.univ A.root)) (e : Bool)
    (hr : 0 < r) (hcross : ∀ j, 10*r ≤ c*H.radius j) : A.History c :=
  match D with
  | .ordinary _ => H
  | .ordered _ => H.append r region e hr hcross

lemma increment_recorded (D : BData M) (H : A.History c)
    (r : ℝ) (region : Set (M.Point Set.univ A.root)) (e : Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ j, 10*r ≤ c*H.radius j) :
    (D.withAuxiliary (D.incrementAuxiliary H r region e hc hcr hr hcross)).Recorded
      (D.incrementHistory H r region e hr hcross) hc hcr := by
  cases D with
  | ordinary D => trivial
  | ordered D => exact fun _ _ => rfl

lemma increment_magnitude (D : BData M) (H : A.History c)
    (r : ℝ) (region : Set (M.Point Set.univ A.root)) (e : Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ j, 10*r ≤ c*H.radius j) (hrec : D.Recorded H hc hcr)
    (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100)
    (i : Fin (k+1)) (T : D.band) :
    |(D.auxiliaryField (D.incrementAuxiliary H r region e hc hcr hr hcross) lam hlam).value i T -
      D.value lam i T| ≤ (lam:ℝ)*10*r := by
  cases D with
  | ordinary D =>
    change |D.value i T-D.value i T| ≤ _
    rw [sub_self,abs_zero]
    positivity
  | ordered D =>
    dsimp only [BData.value]
    erw [increment_difference D H r region e hc hcr hr hcross hrec lam hlam,
      abs_mul,abs_of_nonneg lam.coe_nonneg]
    have hb : |Increment.signedDamped e (c*r) r
        ((D.base.transverse (by norm_num) D.lower D.upper).value i)
        (fun U : D.band => Increment.taper regionᶜ r (A.point i U.val)) T| ≤ 10*r := by
      have hs := Increment.scalar_magnitude (mul_pos hc hr) hr (by nlinarith : 2*(c*r) ≤ 8*r)
        (t := (D.base.transverse (by norm_num) D.lower D.upper).value i T)
      have ht := Increment.taper_bounds (S := regionᶜ) hr (A.point i T.val)
      have hh : |Increment.damped (c*r) r
          ((D.base.transverse (by norm_num) D.lower D.upper).value i)
          (fun U : D.band => Increment.taper regionᶜ r (A.point i U.val)) T| ≤ 10*r := by
        unfold Increment.damped
        rw [abs_mul,abs_of_nonneg ht.1]
        exact (mul_le_mul hs ht.2 ht.1 (by positivity)).trans_eq (mul_one _)
      cases e <;> simpa only [Increment.signedDamped,Bool.false_eq_true,ite_false,ite_true,abs_neg] using hh
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb lam.coe_nonneg

end BData

namespace BState
variable {κ : ℝ} {lam : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  (S : BState M κ lam Ω μ) (A : Ambient M)

/-- A region is exactly the old identifier's inverse image in the full-column
ambient model. No approximation of its boundary is used. -/
def region (a : Fin (S.count+1)) : Set (M.Point Set.univ A.root) :=
  {p | S.name p.column p.height=a}

lemma other_height_not_region (i : Fin (k+1)) (H T : ℝ)
    (hne : S.name i H≠S.name i T) : A.point i T ∉ S.region A (S.name i H) := by
  exact fun h => hne h.symm

noncomputable def incrementFields {c r : ℝ}
    (hist : Fin (S.count+1) → A.History c) (sign : Fin (S.count+1) → Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ a j, 10*r ≤ c*(hist a).radius j)
    (hlam : lam ≤ (1:ℝ≥0)/100) : ∀ a, M.Field (S.chart a).band 5 :=
  fun a => (S.chart a).auxiliaryField
    ((S.chart a).incrementAuxiliary (hist a) r (S.region A a) (sign a) hc hcr hr (hcross a)) lam hlam

lemma increment_boundary {c r : ℝ}
    (hist : Fin (S.count+1) → A.History c) (sign : Fin (S.count+1) → Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ a j, 10*r ≤ c*(hist a).radius j)
    (hrec : ∀ a, (S.chart a).Recorded (hist a) hc hcr)
    (hk : 0 ≤ κ) (hlam : lam ≤ (1:ℝ≥0)/100) (hsmall : κ*(lam:ℝ)*10 ≤ 1/8)
    (i : Fin (k+1)) (H T : ℝ) (hne : S.name i H≠S.name i T) :
    |S.newValue (S.incrementFields A hist sign hc hcr hr hcross hlam) i H-S.oldValue i H| ≤
      |H-T|/8 := by
  unfold newValue oldValue
  rw [← mul_sub,abs_mul,abs_of_nonneg hk]
  have hb := (S.chart (S.name i H)).increment_boundary (hist (S.name i H)) r
    (S.region A (S.name i H)) (sign (S.name i H)) hc hcr hr (hcross (S.name i H))
    (hrec (S.name i H)) lam hlam i ⟨H,S.height_in i H⟩ T
    (S.other_height_not_region A i H T hne)
  calc
    _ ≤ κ*((lam:ℝ)*10*|H-T|) := mul_le_mul_of_nonneg_left hb hk
    _ ≤ |H-T|/8 := by nlinarith [mul_le_mul_of_nonneg_right hsmall (abs_nonneg (H-T))]

noncomputable def increment {c r : ℝ}
    (hist : Fin (S.count+1) → A.History c) (sign : Fin (S.count+1) → Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ a j, 10*r ≤ c*(hist a).radius j)
    (hrec : ∀ a, (S.chart a).Recorded (hist a) hc hcr)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hboundary : κ*(lam:ℝ)*10 ≤ 1/8) : BState M κ lam Ω μ :=
  S.withAuxiliary
    (fun a => (S.chart a).incrementAuxiliary (hist a) r (S.region A a) (sign a) hc hcr hr (hcross a))
    hk hsmall hlam (S.increment_boundary A hist sign hc hcr hr hcross hrec hk hlam hboundary)

lemma increment_names {c r : ℝ}
    (hist : Fin (S.count+1) → A.History c) (sign : Fin (S.count+1) → Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ a j, 10*r ≤ c*(hist a).radius j)
    (hrec : ∀ a, (S.chart a).Recorded (hist a) hc hcr)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hboundary : κ*(lam:ℝ)*10 ≤ 1/8) :
    (S.increment A hist sign hc hcr hr hcross hrec hk hsmall hlam hboundary).name=S.name := rfl

lemma increment_recorded {c r : ℝ}
    (hist : Fin (S.count+1) → A.History c) (sign : Fin (S.count+1) → Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ a j, 10*r ≤ c*(hist a).radius j)
    (hrec : ∀ a, (S.chart a).Recorded (hist a) hc hcr)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hboundary : κ*(lam:ℝ)*10 ≤ 1/8) (a : Fin (S.count+1)) :
    ((S.increment A hist sign hc hcr hr hcross hrec hk hsmall hlam hboundary).chart a).Recorded
      ((S.chart a).incrementHistory (hist a) r (S.region A a) (sign a) hr (hcross a)) hc hcr :=
  (S.chart a).increment_recorded (hist a) r (S.region A a) (sign a) hc hcr hr (hcross a)

lemma increment_movement {c r : ℝ}
    (hist : Fin (S.count+1) → A.History c) (sign : Fin (S.count+1) → Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ a j, 10*r ≤ c*(hist a).radius j)
    (hrec : ∀ a, (S.chart a).Recorded (hist a) hc hcr)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hboundary : κ*(lam:ℝ)*10 ≤ 1/8) (i : Fin (k+1)) (H : ℝ) :
    (∫ ω, |((S.increment A hist sign hc hcr hr hcross hrec hk hsmall hlam hboundary).sets.activity ω).indicator i H-
      (S.sets.activity ω).indicator i H| ∂μ) ≤ κ*(lam:ℝ)*10*r := by
  change (∫ ω, |(S.fieldActivity (S.incrementFields A hist sign hc hcr hr hcross hlam)
    hk hsmall hlam (S.increment_boundary A hist sign hc hcr hr hcross hrec hk hlam hboundary) ω).indicator i H-(S.sets.activity ω).indicator i H| ∂μ) ≤ _
  simp_rw [S.field_indicator,S.old_indicator]
  rw [(S.labels (S.name i H)).distance,sub_self,abs_zero,max_eq_right (abs_nonneg _)]
  unfold newValue oldValue
  rw [← mul_sub,abs_mul,abs_of_nonneg hk]
  have hb := (S.chart (S.name i H)).increment_magnitude (hist (S.name i H)) r
    (S.region A (S.name i H)) (sign (S.name i H)) hc hcr hr (hcross (S.name i H))
    (hrec (S.name i H)) lam hlam i ⟨H,S.height_in i H⟩
  simpa only [mul_assoc,incrementFields] using mul_le_mul_of_nonneg_left hb hk

end BState
end PlanarL1.Columns.Model



end

end OAI
