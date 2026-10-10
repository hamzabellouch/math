import OAI.Combinatorics.HadwigerCounterexample.TerminalCut
import OAI.Combinatorics.HadwigerCounterexample.ProductLaws
import OAI.Combinatorics.HadwigerCounterexample.SampledGraphs
import Mathlib.Data.Fintype.Powerset

namespace OAI

/-! # Finite Graph Transfer -/

noncomputable section

namespace HadwigerCounterexample
open Finset Real HadwigerMatching
open scoped BigOperators
variable {A V : Type*}

/-- k distinct samples in S (unordered). -/
private def badS (S : A → Prop) (k : ℕ) (x : V → A) :=
  ∃ T : Finset V, T.card = k ∧ ∀ v ∈ T, S (x v)

private theorem badS_pr [Fintype A] {μ : Wgt A} (hμ : IsLaw μ)
    (S : A → Prop) (k m : ℕ) :
    pr (prodW (fun _ : Fin m => μ)) (badS S k) ≤
      2 ^ m * (pr μ S)^k := by
  classical
  let q := prodW (fun _ : Fin m => μ)
  have hp (T : Finset (Fin m)) :
      pr q (fun x => T.card = k ∧ ∀ v ∈ T, S (x v)) ≤ (pr μ S)^k := by
    by_cases h : T.card = k
    · have e (x : Fin m → A) : (∀ v ∈ T, S (x v)) ↔ ∀ v : T, S (x v.val) := by simp
      have h' := prodW_pr_inj (e:=fun v : T => v.val) Subtype.val_injective
        (w:=fun _ => μ) (fun _ => hμ) (fun _ : T => S)
      simp_rw [h, true_and, e]
      simp only [prod_const, Finset.card_univ, Fintype.card_coe,h] at h'
      exact h'.le
    · have hn : 0 ≤ pr μ S := pr_nonneg hμ.nz
      simp only [h, false_and, pr_false]
      positivity
  have he := pr_exists_le (prodW_nonneg (w:=fun _ : Fin m => μ) (fun _ => hμ.nz))
    (fun T : Finset (Fin m) => (fun x => T.card = k ∧ ∀ v ∈ T, S (x v)))
  refine he.trans ((sum_le_sum (fun i _ => hp i)).trans_eq ?_)
  simp

/-- k pair exceptions using disjoint sample positions (ordered pairs). -/
private def badE (E : A × A → Prop) (k : ℕ) (x : V → A) :=
  ∃ e : Fin k ⊕ Fin k → V, Function.Injective e ∧
    ∀ i, E (x (e (.inl i)), x (e (.inr i)))

private theorem badE_pr [Fintype A] {μ : Wgt A} (hμ : IsLaw μ)
    (E : A × A → Prop) (k m : ℕ) :
    pr (prodW (fun _ : Fin m => μ)) (badE E k) ≤
      (m : ℝ)^(k+k) * (pr (pairW μ μ) E)^k := by
  classical
  let Q := prodW (fun _ : Fin m => μ)
  let P (e : Fin k ⊕ Fin k → Fin m) (x : Fin m → A) :=
    Function.Injective e ∧ ∀ i, E (x (e (.inl i)), x (e (.inr i)))
  have hp (e : Fin k ⊕ Fin k → Fin m) :
      pr Q (P e) ≤ (pr (pairW μ μ) E)^k := by
    by_cases h : Function.Injective e
    · have h' := prodW_map_pairs e h hμ
      let f (x : Fin m → A) (i : Fin k) := (x (e (.inl i)), x (e (.inr i)))
      have hp : P e = (fun x => ∀ i, E (f x i)) := by simp [P,h,f]
      rw [hp, ← mapW_pr Q f (fun x => ∀ i, E (x i))]
      change mapW Q f = _ at h'
      rw [h']
      have hb := prodW_pr (w:=fun _ : Fin k => pairW μ μ) (p:=fun _ => E)
      simpa using hb.le
    · have hn : 0 ≤ pr (pairW μ μ) E := pr_nonneg (pairW_law hμ hμ).nz
      simp only [P,h,false_and,pr_false]; positivity
  have he := pr_exists_le (prodW_nonneg (w:=fun _ : Fin m => μ) (fun _ => hμ.nz)) P
  refine he.trans ((sum_le_sum (fun i _ => hp i)).trans_eq ?_)
  simp

private theorem many_bad {x : V → A} (S : A → Prop) (E : A × A → Prop)
    {k t : ℕ} (ht : k + k ≤ t + 1)
    {e : Fin t ⊕ Fin t → V} (he : Function.Injective e)
    (hp : ∀ i, S (x (e (.inl i))) ∨ S (x (e (.inr i))) ∨
      E (x (e (.inl i)), x (e (.inr i)))) :
    badS S k x ∨ badE E k x := by
  classical
  let p (i : Fin t) := S (x (e (.inl i))) ∨ S (x (e (.inr i)))
  let I := univ.filter p
  let J := univ.filter (fun i => ¬ p i)
  by_cases hI : k ≤ I.card
  · left
    obtain ⟨r⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card (Fin k) ≤ Fintype.card I by simpa using hI)
    let f : Fin k → Fin t := fun i => r i
    have hf : Function.Injective f := fun i j g => r.injective (Subtype.ext g)
    let y : Fin k → Fin t ⊕ Fin t :=
      fun i => if S (x (e (.inl (f i)))) then .inl (f i) else .inr (f i)
    have hy (i : Fin k) : S (x (e (y i))) := by
      have h : p (f i) := (mem_filter.mp (r i).property).2
      unfold p at h
      unfold y
      split
      · assumption
      · rename_i hn; exact h.resolve_left hn
    have hid i : Sum.elim id id (y i) = f i := by unfold y; split <;> rfl
    have hy' : Function.Injective y := fun i j g =>
      hf (by rw [←hid,←hid,g])
    refine ⟨univ.image (e ∘ y), by rw [card_image_of_injective _ (he.comp hy')]; simp,?_⟩
    intro v hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact hy i
  · right
    have hJ : k ≤ J.card := by
      have hsum : I.card + J.card = t := by
        simpa using Finset.card_filter_add_card_filter_not (s:=univ) p
      omega
    obtain ⟨r⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card (Fin k) ≤ Fintype.card J by simpa using hJ)
    let f : Fin k → Fin t := fun i => r i
    have hf : Function.Injective f := fun i j g => r.injective (Subtype.ext g)
    refine ⟨e ∘ Sum.map f f, he.comp (Sum.map_injective.mpr ⟨hf,hf⟩),?_⟩
    intro i
    have h : ¬p (f i) := (mem_filter.mp (r i).property).2
    exact ((hp _).resolve_left (fun g => h (Or.inl g))).resolve_left
      (fun g => h (Or.inr g))

/-- Finite transfer with an explicit error term. If T denotes the terminal count
bound, it suffices that
T*(2^m*(2/M)^k + m^(2*k)*(1/D)^k) < 1.
The rate version just instantiates these inequalities. -/
theorem transfer [Fintype A] [Nonempty A] (H : Holes A) {μ : Wgt A} (hμ : IsLaw μ)
    {M D ε : ℝ} (hM : 0 < M) (hD : 0 < D) (hε : 0 < ε)
    (hsat : ∀ w : Wgt (A × A), IsLaw w → pairCaps μ M D w → carried w H.unit →
      ε ≤ pr (pairW w w) (fun x => H.conflict x.1 x.2))
    {L m k : ℕ} (hL : Real.log (Fintype.card (A × A)) < L * (ε * Real.log 2))
    (hk : 200*k < m+200)
    (herr :
      ((Fintype.card (A × A) : ℝ) + 1)^L *
        (2^m * (2/M)^k + (m:ℝ)^(k+k) * D⁻¹^k) < 1) :
    ∃ x : Fin m → A,
      (H.graph x).indepNum ≤ 2 ∧
      (connectedMatchingNumber (H.graph x) : ℚ) < (m : ℚ)/100 := by
  classical
  let R := univ.filter H.unit
  let O := {w : Wgt (A × A) | IsLaw w} ∩ {w | pairCaps μ M D w}
  obtain ⟨C,hC,hTC,hCC⟩ := containers (ok:=O)
    (compact_isLaw.inter_right (closed_pairCaps _ _ _)) (fun _ h => h.1)
    (fun _ h _ g => ⟨mid_isLaw h.1 g.1, mid_pairCaps h.2 g.2⟩)
    H.conflict hε R (fun w hw g => hsat w hw.1 hw.2 (by simpa [carried,R] using g))
    L (fun w hw _ => by
      have h := log_card_le_negEnt hw.1
      linarith)
  have hx (r : C) :
      ∃ (S : A → Prop) (E : A × A → Prop), M* pr μ S < 2 ∧
        D * pr (pairW μ μ) E < 1 ∧ ∀ x : A × A, x ∈ r.val → S x.1 ∨ S x.2 ∨ E x :=
    terminal hμ.nz hM hD _ (fun ⟨w,h,g,k⟩ => (hTC _ r.property).2 ⟨w,⟨h,g⟩,k⟩)
  choose S E hs hq hcover using hx
  let P (r : C) (x : Fin m → A) := badS (S r) k x ∨ badE (E r) k x
  let W := prodW (fun _ : Fin m => μ)
  have hw : IsLaw W := prodW_law fun _ => hμ
  let b := (2:ℝ)^m * (2/M)^k + (m:ℝ)^(k+k) * D⁻¹^k
  have hp (r : C) : pr W (P r) ≤ b := by
    have h₁ := badS_pr hμ (S r) k m
    have h₂ := badE_pr hμ (E r) k m
    refine (pr_or_le hw.nz).trans ((add_le_add h₁ h₂).trans ?_)
    have hi : 0 ≤ pr μ (S r) := pr_nonneg hμ.nz
    have hj : 0 ≤ pr (pairW μ μ) (E r) := pr_nonneg (pairW_law hμ hμ).nz
    have hk : pr μ (S r) ≤ 2/M := (le_div_iff₀ hM).mpr (by linarith only [hs r])
    have hn : pr (pairW μ μ) (E r) ≤ D⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ hD).mpr
      linarith only [hq r]
    unfold b; gcongr
  have hf : pr W (fun x => ∃ r, P r x) < 1 := by
    have h : pr W (fun x => ∃ r, P r x) ≤ (C.card : ℝ) * b := by
      refine (pr_exists_le hw.nz P).trans ((sum_le_sum (fun i _ => hp i)).trans_eq ?_)
      simp
    apply lt_of_le_of_lt h
    apply lt_of_le_of_lt _ herr
    have hg : C.card ≤ (Fintype.card (A × A) + 1)^L :=
      hC.trans (by gcongr; exact card_le_univ _)
    have hb : 0 ≤ b := by unfold b; positivity
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hg) hb
  have hg : 0 < pr W (fun x => ¬∃ r, P r x) := by rw [pr_not, hw.total]; linarith only [hf]
  obtain ⟨x,hx,_⟩ := exists_of_pr_pos hw.nz hg
  refine ⟨x, H.indepNum_graph_le _,?_⟩
  let t := connectedMatchingNumber (H.graph x)
  by_contra! hn
  obtain ⟨e,he,he₁,he₂⟩ := H.matching_pairs x
  let f (i : Fin t) : A × A := (x (e (.inl i)), x (e (.inr i)))
  let I := univ.image f
  have hIR : I ⊆ R := by
    intro y hy; obtain ⟨i,_,rfl⟩ := mem_image.mp hy
    exact mem_filter.mpr ⟨mem_univ _, he₁ i⟩
  have hI (v) (hv : v ∈ I) (w) (hw : w ∈ I) : ¬ H.conflict v w := by
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    obtain ⟨j,_,rfl⟩ := mem_image.mp hw
    exact he₂ i j
  obtain ⟨r,hr,g⟩ := hCC I hIR hI
  have ht : m ≤ t * 100 := by
    change (m:ℚ)/100 ≤ (t:ℚ) at hn
    have h : (m:ℚ) ≤ (t:ℚ)*100 := by linarith
    exact_mod_cast h
  apply hx
  let r' : C := ⟨r,hr⟩
  refine ⟨r', many_bad (S r') (E r') (by omega) he fun i =>
    hcover r' (f i) (g (mem_image_of_mem f (mem_univ i)))⟩
end HadwigerCounterexample

end

end OAI
