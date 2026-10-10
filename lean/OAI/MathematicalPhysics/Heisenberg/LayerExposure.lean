import OAI.MathematicalPhysics.Heisenberg.FiniteHistories

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical

namespace Heisenberg.Exposure

section
open Heisenberg.Cycle Heisenberg.LayeredExchange
variable {T V : Type*} [Fintype T] [Fintype V]

def layerHistory (s : Equiv.Perm T) (τ : T → Equiv.Perm V) (b : T → Bool) :
    Equiv.Perm (T × V) := wiring s (fun t => if b t then τ t else 1)

def layerRevealed (τ : T → Equiv.Perm V) (A : Set (T × V)) (t : T) : Prop :=
  ∃ v, (t,v) ∈ A ∧ τ t v ≠ v

omit [Fintype T] [Fintype V] in
lemma layer_matches_iff (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (A : Set (T × V)) (b c : T → Bool) :
    (∀ z ∈ A, layerHistory s τ b z = layerHistory s τ c z) ↔
      ∀ t, layerRevealed τ A t → c t = b t := by
  constructor
  · intro h t ht
    obtain ⟨v,hv,hne⟩ := ht
    have he := congrArg Prod.snd (h (t,v) hv)
    change (if b t then τ t else 1) v = (if c t then τ t else 1) v at he
    cases hb : b t <;> cases hc : c t
    · rfl
    · exact (hne (by simpa only [hb,hc,Bool.false_eq_true,↓reduceIte,Equiv.Perm.one_apply] using he.symm)).elim
    · exact (hne (by simpa only [hb,hc,Bool.false_eq_true,↓reduceIte,Equiv.Perm.one_apply] using he)).elim
    · rfl
  · intro h ⟨t,v⟩ hv
    simp only [layerHistory,wiring_apply]
    by_cases ht : layerRevealed τ A t
    · rw [h t ht]
    · have he : τ t v = v := by by_contra hn; exact ht ⟨v,hv,hn⟩
      congr 1
      split_ifs <;> first | exact he | exact he.symm | rfl

def layerExposure (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (P : Set (T × V)) (b c : T → Bool) : Prop :=
  (∀ z ∈ MissingSet (layerHistory s τ b) P, layerHistory s τ b z = layerHistory s τ c z) ∧
    MissingSet (layerHistory s τ c) P = MissingSet (layerHistory s τ b) P

lemma layerExposure_iff (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (P : Set (T × V)) (b c : T → Bool) :
    layerExposure s τ P b c ↔
      (∀ t, layerRevealed τ (MissingSet (layerHistory s τ b) P) t → c t = b t) ∧
      OutsideHit (layerHistory s τ c) P (MissingSet (layerHistory s τ b) P) := by
  constructor
  · rintro ⟨hm,he⟩
    exact ⟨(layer_matches_iff ..).mp hm,(sameMissing_iff_outsideHit _ _ _ hm).mp he⟩
  · rintro ⟨hc,hh⟩
    have hm := (layer_matches_iff s τ _ b c).mpr hc
    exact ⟨hm,(sameMissing_iff_outsideHit _ _ _ hm).mpr hh⟩

lemma layerExposure_weight (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (P : Set (T × V)) (b c : T → Bool) (h : layerExposure s τ P b c) :
    missingCount (layerHistory s τ c) P = missingCount (layerHistory s τ b) P :=
  (missing_weight_rigid _ _ P h.2.symm h.1).symm

theorem layer_exposure_disintegration (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (w : T → Bool → ℝ) (P : Set (T × V)) (b : T → Bool) (F : (T → Bool) → ℝ) :
    let A := MissingSet (layerHistory s τ b) P
    let M := layerRevealed τ A
    let a : {t // M t} → Bool := fun t => b t
    (∑ c : T → Bool, if layerExposure s τ P b c then
      productWeight w c * (2:ℝ)^missingCount (layerHistory s τ c) P * F c else 0) =
    (2:ℝ)^missingCount (layerHistory s τ b) P *
      productWeight (fun t : {t // M t} => w t) a *
      ∑ c : {t // ¬M t} → Bool, if OutsideHit (layerHistory s τ (merge M a c)) P A then
        productWeight (fun t : {t // ¬M t} => w t) c * F (merge M a c) else 0 := by
  dsimp only
  refine filtered_cylinder_disintegration w
    (layerRevealed τ (MissingSet (layerHistory s τ b) P)) (fun t => b t)
    (fun c => OutsideHit (layerHistory s τ c) P (MissingSet (layerHistory s τ b) P))
    (layerExposure s τ P b) (fun c => (2:ℝ)^missingCount (layerHistory s τ c) P) F
    ((2:ℝ)^missingCount (layerHistory s τ b) P) ?_ ?_
  · intro c
    rw [layerExposure_iff]
    constructor
    · rintro ⟨hc,hg⟩
      exact ⟨fun t => hc t t.property,hg⟩
    · rintro ⟨hc,hg⟩
      exact ⟨fun t ht => hc ⟨t,ht⟩,hg⟩
  · intro c hc
    rw [layerExposure_weight s τ P b c hc]

end

section
open LayeredExchange Heisenberg.Cycle
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma invariant_of_agree (π σ : Equiv.Perm V) (A : Set V)
    (hA : ∀ x,π x ∈ A ↔ x ∈ A) (he : ∀ x ∈ A,π x = σ x) :
    ∀ x,σ x ∈ A ↔ x ∈ A := by
  intro x
  constructor
  · intro hx
    have hy : π.symm (σ x) ∈ A := (hA _).mp (by simpa using hx)
    have hs := he _ hy
    have hxy : π.symm (σ x) = x := σ.injective (by simpa using hs.symm)
    exact hxy ▸ hy
  · intro hx
    rw [← he x hx]
    exact (hA x).mpr hx

def residualCoins {n : ℕ} (M : Fin n → Prop) (base c : Fin n → Bool) : Fin n → Bool :=
  fun i => if M i then base i else c i

omit [Fintype V] [DecidableEq V] in
lemma residual_agrees {n : ℕ} (s : Equiv.Perm (Fin n)) (τ : Fin n → Equiv.Perm V)
    (P : Set (Fin n × V)) (base c : Fin n → Bool) :
    ∀ z ∈ MissingSet (layerHistory s τ base) P,
      layerHistory s τ base z = layerHistory s τ
        (residualCoins (layerRevealed τ (MissingSet (layerHistory s τ base) P)) base c) z := by
  apply (layer_matches_iff _ _ _ _ _).mpr
  intro t ht
  simp [residualCoins,ht]

omit [Fintype V] [DecidableEq V] in
lemma residual_invariant {n : ℕ} (s : Equiv.Perm (Fin n)) (τ : Fin n → Equiv.Perm V)
    (P : Set (Fin n × V)) (base c : Fin n → Bool) :
    ∀ z, layerHistory s τ
        (residualCoins (layerRevealed τ (MissingSet (layerHistory s τ base) P)) base c) z ∉
          MissingSet (layerHistory s τ base) P ↔ z ∉ MissingSet (layerHistory s τ base) P := by
  intro z
  exact not_congr (invariant_of_agree _ _ _ (missing_apply _ _)
    (residual_agrees s τ P base c) z)

lemma residual_determinantLaw {n : ℕ} (s : Equiv.Perm (Fin n)) (a b : Fin n → V)
    (P : Set (Fin n × V)) (base : Fin n → Bool) (p : Fin n → ℝ) :
    let τ := fun i => Equiv.swap (a i) (b i)
    let M := layerRevealed τ (MissingSet (layerHistory s τ base) P)
    DeterminantLaw (fun c : Fin n → Bool => ∏ i,if c i then p i else 1-p i)
      (fun c => forwardHom (R:=ℝ) (layerHistory s τ (residualCoins M base c))) := by
  dsimp only
  let τ := fun i => Equiv.swap (a i) (b i)
  let M := layerRevealed τ (MissingSet (layerHistory s τ base) P)
  let fixed := fun i => if M i then some (if base i then τ i else 1) else none
  have h := determinantLaw_wiring s a b p fixed
  convert h using 1
  funext c
  apply congrArg (forwardHom (R:=ℝ))
  apply congrArg (wiring s)
  funext i
  change (if residualCoins M base c i then τ i else 1) =
    (fixed i).getD (if c i then τ i else 1)
  by_cases hi : M i <;> simp [fixed,residualCoins,hi]

def residualHolePerm {n : ℕ} (s : Equiv.Perm (Fin n)) (τ : Fin n → Equiv.Perm V)
    (P : Set (Fin n × V)) (base c : Fin n → Bool) :
    Equiv.Perm {z : Fin n × V // z ∉ MissingSet (layerHistory s τ base) P} :=
  (layerHistory s τ (residualCoins
    (layerRevealed τ (MissingSet (layerHistory s τ base) P)) base c)).subtypePerm
      (p := fun z => z ∉ MissingSet (layerHistory s τ base) P)
      (residual_invariant s τ P base c)

attribute [local irreducible] MissingSet layerHistory

theorem residual_holes_determinantLaw {n : ℕ} (s : Equiv.Perm (Fin n)) (a b : Fin n → V)
    (P : Set (Fin n × V)) (base : Fin n → Bool) (p : Fin n → ℝ) :
    DeterminantLaw (fun c : Fin n → Bool => ∏ i,if c i then p i else 1-p i)
      (fun c => forwardHom (R:=ℝ)
        (residualHolePerm s (fun i => Equiv.swap (a i) (b i)) P base c)) := by
  let τ : Fin n → Equiv.Perm V := fun i => Equiv.swap (a i) (b i)
  let A : Set (Fin n × V) := MissingSet (layerHistory s τ base) P
  let π : (Fin n → Bool) → Equiv.Perm (Fin n × V) := fun c =>
    layerHistory s τ (residualCoins (layerRevealed τ A) base c)
  let μ : (Fin n → Bool) → ℝ := fun c => ∏ i,if c i then p i else 1-p i
  have h : DeterminantLaw μ (fun c => forwardHom (R:=ℝ) (π c)) :=
    residual_determinantLaw s a b P base p
  have hi : ∀ c z,π c z ∉ A ↔ z ∉ A := fun c => residual_invariant s τ P base c
  have hh := determinantLaw_holes (Ω:=Fin n → Bool) (V:=Fin n × V) (R:=ℝ)
    (μ:=μ) (π:=π) h (fun z => z ∉ A) hi
  change DeterminantLaw μ (fun c => forwardHom (R:=ℝ) ((π c).subtypePerm (p:= fun z => z ∉ A) (hi c)))
  exact hh

end

open Heisenberg.Cycle LayeredExchange
variable {V W : Type*}

lemma sameCycle_congr (e : V ≃ W) (π : Equiv.Perm V) (x y : V) :
    (e.permCongr π).SameCycle (e x) (e y) ↔ π.SameCycle x y := by
  change (∃ n : ℤ,((e.permCongr π)^n) (e x) = e y) ↔ ∃ n : ℤ,(π^n) x = y
  apply exists_congr
  intro n
  have he := map_zpow e.permCongrHom π n
  change e.permCongr (π^n) = (e.permCongr π)^n at he
  rw [←he,Equiv.permCongr_apply,Equiv.symm_apply_apply,e.injective.eq_iff]

def splitHolePerm (σ : Equiv.Perm V) (A P : Set V)
    (hA : ∀ x,σ x ∉ A ↔ x ∉ A) :
    Equiv.Perm ({x : {z : V // z ∉ A} // x.val ∈ P} ⊕
      {x : {z : V // z ∉ A} // x.val ∉ P}) :=
  (Equiv.sumCompl (fun x : {z : V // z ∉ A} => x.val ∈ P)).symm.permCongr
    (σ.subtypePerm hA)

lemma allHit_splitHolePerm (σ : Equiv.Perm V) (A P : Set V)
    (hA : ∀ x,σ x ∉ A ↔ x ∉ A) (hP : Disjoint A P) :
    AllHit (splitHolePerm σ A P hA) ↔ OutsideHit σ P A := by
  let e := Equiv.sumCompl (fun x : {z : V // z ∉ A} => x.val ∈ P)
  let π := σ.subtypePerm (p := fun z => z ∉ A) hA
  have he (x y) : (splitHolePerm σ A P hA).SameCycle x y ↔
      π.SameCycle (e x) (e y) := by
    have hh := sameCycle_congr e.symm π (e x) (e y)
    simpa only [Equiv.symm_apply_apply,e,splitHolePerm] using hh
  constructor
  · intro h x hx
    obtain ⟨j,hj⟩ := h (e.symm ⟨x,hx⟩)
    refine ⟨j.val.val,j.property,?_⟩
    have hc := (he _ _).mp hj
    rw [Equiv.apply_symm_apply] at hc
    exact Equiv.Perm.sameCycle_subtypePerm.mp hc
  · intro h x
    obtain ⟨j,hj,hc⟩ := h (e x).val (e x).property
    have hjA : j ∉ A := fun hA => Set.disjoint_left.mp hP hA hj
    let y : {x : {z : V // z ∉ A} // x.val ∈ P} := ⟨⟨j,hjA⟩,hj⟩
    refine ⟨y,(he _ _).mpr ?_⟩
    exact Equiv.Perm.sameCycle_subtypePerm.mpr hc

variable [Fintype V] [DecidableEq V]

theorem exposed_nextPin_first_moment {n : ℕ} (s : Equiv.Perm (Fin n))
    (a b : Fin n → V) (P : Set (Fin n × V)) (base : Fin n → Bool) (p : Fin n → ℝ) :
    let τ := fun i => Equiv.swap (a i) (b i)
    let A := MissingSet (layerHistory s τ base) P
    let π := fun c => splitHolePerm
      (layerHistory s τ (residualCoins (layerRevealed τ A) base c)) A P
        (residual_invariant s τ P base c)
    let μ := fun c : Fin n → Bool => ∏ i,if c i then p i else 1-p i
    hitWeight μ π ≠ 0 →
      (∑ c, if hw : AllHit (π c) then
        (μ c / hitWeight μ π) • nextPinMatrix ℝ (π c) hw else 0) =
      hittingResolvent ℝ (∑ c,μ c • columnPerm ℝ (π c)) := by
  dsimp only
  intro hg
  apply conditional_nextPin_first_moment _ _ _ hg
  have h := residual_holes_determinantLaw s a b P base p
  have hh := determinantLaw_reindexed h
    (Equiv.sumCompl (fun x : {z : Fin n × V // z ∉
      MissingSet (layerHistory s (fun i => Equiv.swap (a i) (b i)) base) P} => x.val ∈ P))
  exact hh

end Heisenberg.Exposure
end

end OAI
