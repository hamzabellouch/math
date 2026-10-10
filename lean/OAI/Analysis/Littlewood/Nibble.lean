import OAI.Analysis.Littlewood.ProductProbability

namespace OAI

universe uI uE uV

namespace AsymptoticallyMinimalLittlewood
namespace Nibble
open scoped BigOperators
open Finset
section SetUnions
variable {I : Type uI} {E : Type uE} [DecidableEq I] [DecidableEq E]

omit [DecidableEq I] in
lemma card_biUnion_upper (S : Finset I) (A : I → Finset E) {D : ℝ}
    (hD : ∀ i ∈ S, ((A i).card : ℝ) ≤ D) :
    ((S.biUnion A).card : ℝ) ≤ S.card * D := by
  calc
    _ ≤ ∑ i ∈ S, ((A i).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ S, D := Finset.sum_le_sum hD
    _ = _ := by simp

lemma card_biUnion_lower (S : Finset I) (A : I → Finset E) {C : ℝ} (hC : 0 ≤ C)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ((A i ∩ A j).card : ℝ) ≤ C) :
    (∑ i ∈ S, ((A i).card : ℝ)) ≤ ((S.biUnion A).card : ℝ) + (S.card : ℝ) ^ 2 * C := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hiS : ∀ j ∈ S, ((A i ∩ A j).card : ℝ) ≤ C := fun j hj ↦
      hpair i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (by intro h; subst j; contradiction)
    have hh := card_biUnion_upper S (fun j ↦ A i ∩ A j) hiS
    rw [← Finset.inter_biUnion] at hh
    have hcard := Finset.card_union_add_card_inter (A i) (S.biUnion A)
    have hcard' : ((A i ∪ S.biUnion A).card : ℝ) + (A i ∩ S.biUnion A).card =
        (A i).card + (S.biUnion A).card := by exact_mod_cast hcard
    have hind := ih (fun j hj k hk hjk ↦
      hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
    rw [Finset.sum_insert hi, Finset.biUnion_insert, Finset.card_insert_of_notMem hi]
    push_cast
    nlinarith [show (0 : ℝ) ≤ S.card from Nat.cast_nonneg _]

end SetUnions

section Hypergraph
variable {V : Type uV} {E : Type uE} [DecidableEq V] [Fintype E] [DecidableEq E]

def incident (S : Finset E) (A : E → Finset V) (v : V) : Finset E :=
  S.filter fun e ↦ v ∈ A e

def hits (S : Finset E) (A : E → Finset V) (W : Finset V) : Finset E :=
  W.biUnion (incident S A)

omit [Fintype E] [DecidableEq E] in
@[simp] lemma mem_incident (S : Finset E) (A : E → Finset V) (v : V) (e : E) :
    e ∈ incident S A v ↔ e ∈ S ∧ v ∈ A e := by simp [incident]

omit [Fintype E] in
@[simp] lemma mem_hits (S : Finset E) (A : E → Finset V) (W : Finset V) (e : E) :
    e ∈ hits S A W ↔ e ∈ S ∧ ∃ v ∈ W, v ∈ A e := by
  simp only [hits, Finset.mem_biUnion, mem_incident]
  aesop

omit [Fintype E] in
lemma hits_card_upper (S : Finset E) (A : E → Finset V) (W : Finset V) {D : ℝ}
    (hD : ∀ v ∈ W, ((incident S A v).card : ℝ) ≤ D) :
    ((hits S A W).card : ℝ) ≤ W.card * D := card_biUnion_upper W _ hD

omit [Fintype E] in
lemma hits_card_deviation (S : Finset E) (A : E → Finset V) (W : Finset V)
    {D e C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ v ∈ W, |((incident S A v).card : ℝ) - D| ≤ e)
    (hpair : ∀ v ∈ W, ∀ w ∈ W, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C) :
    |((hits S A W).card : ℝ) - W.card * D| ≤ W.card * e + (W.card : ℝ) ^ 2 * C := by
  have hupper := hits_card_upper S A W (D := D + e) (fun v hv ↦ by
    have := (abs_le.mp (hD v hv)).2
    linarith)
  have hlower := card_biUnion_lower W (incident S A) hC hpair
  have hsum : W.card * (D - e) ≤ ∑ v ∈ W, ((incident S A v).card : ℝ) := by
    calc
      _ = ∑ _v ∈ W, (D - e) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun v hv ↦ by have := (abs_le.mp (hD v hv)).1; linarith
  change (∑ v ∈ W, ((incident S A v).card : ℝ)) ≤
    ((hits S A W).card : ℝ) + (W.card : ℝ)^2 * C at hlower
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg (sq_nonneg (W.card : ℝ)) hC]

omit [Fintype E] in
lemma residual_test_frequency (S : Finset E) (A : E → Finset V) (v : V) (f : E) :
    ((incident S A v).filter fun e ↦ f ∈ hits S A ((A e).erase v)) =
      if f ∈ S then ((A f).erase v).biUnion (fun w ↦ incident S A v ∩ incident S A w) else ∅ := by
  ext e
  simp only [Finset.mem_filter, mem_incident, mem_hits, Finset.mem_erase,
    ]
  split_ifs <;> simp_all ; aesop

/-- Codegrees control the influence of each edge-bit on a residual degree. -/
lemma residual_degree_variance (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} {D C p : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card ≤ r)
    (hdeg : ∀ v ∈ U, ((incident S A v).card : ℝ) ≤ D)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C)
    (v : V) (hv : v ∈ U) :
    let Y : (E → Bool) → ℝ := fun s ↦
      ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s
    expectation p (fun s ↦ (Y s - expectation p Y)^2) ≤ p * (r : ℝ)^2 * D^2 * C := by
  classical
  let T := fun e ↦ hits S A ((A e).erase v)
  have hL : ∀ e ∈ incident S A v, ((T e).card : ℝ) ≤ r * D := by
    intro e he
    obtain ⟨heS, hve⟩ := mem_incident S A v e |>.mp he
    apply (hits_card_upper S A ((A e).erase v) (fun w hw ↦
      hdeg w (hsub e heS (Finset.mem_of_mem_erase hw)))).trans
    apply mul_le_mul_of_nonneg_right _ hD
    exact_mod_cast (Finset.card_erase_le.trans (hr e heS))
  have hK : ∀ f, (((incident S A v).filter fun e ↦ f ∈ T e).card : ℝ) ≤ r * C := by
    intro f
    dsimp [T]
    rw [residual_test_frequency]
    split_ifs with hf
    · apply (card_biUnion_upper ((A f).erase v) (fun w ↦ incident S A v ∩ incident S A w)
        (fun w hw ↦ hcodeg v hv w (hsub f hf (Finset.mem_of_mem_erase hw))
          (Ne.symm (Finset.mem_erase.mp hw).1))).trans
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast (Finset.card_erase_le.trans (hr f hf))
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  have hb := noHit_sum_variance hp hp1 (incident S A v) T (by positivity : 0 ≤ (r : ℝ)*C) hL hK
  apply hb.trans
  have hd := hdeg v hv
  have hm := mul_le_mul_of_nonneg_right hd (show 0 ≤ p * (r : ℝ)^2 * D * C by positivity)
  nlinarith

/-- Count the vertices missed by the selected edges. -/
def untouched (U : Finset V) (S : Finset E) (A : E → Finset V) (s : E → Bool) : Finset V :=
  U.filter fun v ↦ ∀ e ∈ incident S A v, s e = false

lemma untouched_card (U : Finset V) (S : Finset E) (A : E → Finset V) (s : E → Bool) :
    ((untouched U S A s).card : ℝ) = ∑ v ∈ U, noHit (incident S A v) s := by
  simp only [untouched, Finset.card_eq_sum_ones, Finset.sum_filter, noHit_eq,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma untouched_variance (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} {D p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : ∀ e ∈ S, (A e).card ≤ r)
    (hdeg : ∀ v ∈ U, ((incident S A v).card : ℝ) ≤ D) :
    let Y : (E → Bool) → ℝ := fun s ↦ ((untouched U S A s).card : ℝ)
    expectation p (fun s ↦ (Y s - expectation p Y)^2) ≤ p * U.card * D * r := by
  dsimp only
  simp_rw [untouched_card]
  apply noHit_sum_variance hp hp1 U (incident S A) (Nat.cast_nonneg r) hdeg
  intro e
  by_cases he : e ∈ S
  · have hsub : (U.filter fun v ↦ e ∈ incident S A v) ⊆ A e := by
      intro v hv
      exact (mem_incident S A v e |>.mp (Finset.mem_filter.mp hv).2).2
    exact_mod_cast (Finset.card_le_card hsub).trans (hr e he)
  · have hz : (U.filter fun v ↦ e ∈ incident S A v) = ∅ := by
      ext v
      simp [he]
    rw [hz]
    simp

lemma untouched_mean_upper (U : Finset V) (S : Finset E) (A : E → Finset V)
    {D Emax p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hE : 0 ≤ Emax)
    (hdeg : ∀ v ∈ U, D ≤ ((incident S A v).card : ℝ) ∧
      ((incident S A v).card : ℝ) ≤ Emax) :
    expectation p (fun s ↦ ((untouched U S A s).card : ℝ)) ≤
      U.card * (1 - p * D + (p * Emax)^2 / 2) := by
  simp_rw [untouched_card]
  rw [expectation_sum]
  calc
    _ ≤ ∑ _v ∈ U, (1 - p * D + (p * Emax)^2 / 2) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [expectation_noHit]
      have hb := pow_bonferroni hp hp1 (incident S A v).card
      have hd := mul_le_mul_of_nonneg_left (hdeg v hv).1 hp
      have hu := mul_le_mul_of_nonneg_left (hdeg v hv).2 hp
      have hs : (p * ((incident S A v).card : ℝ))^2 ≤ (p*Emax)^2 :=
        (sq_le_sq₀ (by positivity) (mul_nonneg hp hE)).mpr hu
      nlinarith
    _ = _ := by simp; ring

lemma residual_degree_mean (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hr0 : 1 ≤ r) {D ε C p : ℝ} (hD : 0 ≤ D) (he : 0 ≤ ε) (hC : 0 ≤ C)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card = r)
    (hdeg : ∀ v ∈ U, |((incident S A v).card : ℝ) - D| ≤ ε)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C)
    (v : V) (_hv : v ∈ U) :
    |expectation p (fun s ↦ ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s) -
      (incident S A v).card * (1 - p * ((r-1 : ℕ) : ℝ) * D)| ≤
      (incident S A v).card * (p * ((r : ℝ)*ε + (r : ℝ)^2*C) +
        (p * ((r : ℝ)*(D+ε)))^2/2) := by
  have htcard (e : E) (heS : e ∈ incident S A v) : ((A e).erase v).card = r-1 := by
    rw [Finset.card_erase_of_mem (mem_incident S A v e |>.mp heS).2, hr e
      (mem_incident S A v e |>.mp heS).1]
  have hrle : ((r-1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.sub_le r 1
  have hcard : ∀ e ∈ incident S A v,
      |((hits S A ((A e).erase v)).card : ℝ) - ((r-1 : ℕ) : ℝ)*D| ≤
        (r : ℝ)*ε + (r : ℝ)^2*C := by
    intro e heS
    have hsube : ∀ w ∈ (A e).erase v, w ∈ U := fun w hw ↦
      hsub e (mem_incident S A v e |>.mp heS).1 (Finset.mem_of_mem_erase hw)
    have hb := hits_card_deviation S A ((A e).erase v) hC
      (fun w hw ↦ hdeg w (hsube w hw))
      (fun w hw z hz hwz ↦ hcodeg w (hsube w hw) z (hsube z hz) hwz)
    rw [htcard e heS] at hb
    apply hb.trans
    exact add_le_add (mul_le_mul_of_nonneg_right hrle he)
      (mul_le_mul_of_nonneg_right ((sq_le_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr hrle) hC)
  have hupper : ∀ e ∈ incident S A v,
      ((hits S A ((A e).erase v)).card : ℝ) ≤ (r : ℝ)*(D+ε) := by
    intro e heS
    apply (hits_card_upper S A ((A e).erase v) (D := D+ε) ?_).trans
    · rw [htcard e heS]
      exact mul_le_mul_of_nonneg_right hrle (add_nonneg hD he)
    · intro w hw
      have hh := (abs_le.mp (hdeg w (hsub e (mem_incident S A v e |>.mp heS).1
        (Finset.mem_of_mem_erase hw)))).2
      linarith
  simpa only [mul_assoc] using noHit_mean_error hp hp1
    (by positivity : 0 ≤ (r : ℝ)*(D+ε)) (incident S A v)
    (fun e ↦ hits S A ((A e).erase v)) hcard hupper

/-- Edges remaining after a vertex deletion. -/
def restrictEdges (S : Finset E) (A : E → Finset V) (W : Finset V) : Finset E :=
  S.filter fun e ↦ A e ⊆ W

omit [Fintype E] [DecidableEq E] in
lemma incident_restrict (S : Finset E) (A : E → Finset V) (W : Finset V) (v : V) :
    incident (restrictEdges S A W) A v = (incident S A v).filter fun e ↦ A e ⊆ W := by
  ext e
  simp [incident, restrictEdges, and_left_comm, and_comm]

lemma residual_degree_eq (U : Finset V) (S : Finset E) (A : E → Finset V)
    (hsub : ∀ e ∈ S, A e ⊆ U) (s : E → Bool) (v : V) (hv : v ∈ untouched U S A s) :
    ((incident (restrictEdges S A (untouched U S A s)) A v).card : ℝ) =
      ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s := by
  have hvs : ∀ e ∈ incident S A v, s e = false := (Finset.mem_filter.mp hv).2
  rw [incident_restrict]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, noHit_eq]
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  apply propext
  constructor
  · intro hW f hf
    obtain ⟨hfS, w, hw, hwe⟩ := mem_hits S A ((A e).erase v) f |>.mp hf
    exact (Finset.mem_filter.mp (hW (Finset.mem_of_mem_erase hw))).2 f
      (mem_incident S A w f |>.mpr ⟨hfS, hwe⟩)
  · intro hN w hw
    apply Finset.mem_filter.mpr
    refine ⟨hsub e (mem_incident S A v e |>.mp he).1 hw, ?_⟩
    intro f hf
    by_cases hwv : w = v
    · exact hvs f (hwv ▸ hf)
    · exact hN f (mem_hits S A ((A e).erase v) f |>.mpr
        ⟨(mem_incident S A w f |>.mp hf).1, w, Finset.mem_erase.mpr ⟨hwv, hw⟩,
          (mem_incident S A w f |>.mp hf).2⟩)

omit [Fintype E] in
lemma degree_loss_deleting (U B : Finset V) (S : Finset E) (A : E → Finset V)
    {C : ℝ} (_hC : 0 ≤ C) (hsub : ∀ e ∈ S, A e ⊆ U)
    (v : V) (hc : ∀ w ∈ B, v ≠ w → ((incident S A v ∩ incident S A w).card : ℝ) ≤ C)
    (hv : v ∉ B) :
    ((incident S A v).card : ℝ) - B.card*C ≤
      ((incident (restrictEdges S A (U \ B)) A v).card : ℝ) := by
  classical
  have hd : incident S A v \ incident (restrictEdges S A (U \ B)) A v ⊆
      B.biUnion (fun w ↦ incident S A v ∩ incident S A w) := by
    intro e he
    obtain ⟨he, hn⟩ := Finset.mem_sdiff.mp he
    have hin := mem_incident S A v e |>.mp he
    have hnon : ¬ A e ⊆ U \ B := by
      intro h
      apply hn
      rw [incident_restrict]
      exact Finset.mem_filter.mpr ⟨he, h⟩
    obtain ⟨w, hw, hwB⟩ := Finset.not_subset.mp hnon
    have hwB' : w ∈ B := by simpa [Finset.mem_sdiff, hsub e hin.1 hw] using hwB
    exact Finset.mem_biUnion.mpr ⟨w, hwB', Finset.mem_inter.mpr
      ⟨he, mem_incident S A w e |>.mpr ⟨hin.1, hw⟩⟩⟩
  have hb := (show (((incident S A v \ incident (restrictEdges S A (U \ B)) A v).card) : ℝ) ≤
      (B.biUnion (fun w ↦ incident S A v ∩ incident S A w)).card from
        Nat.cast_le.mpr (Finset.card_le_card hd)).trans
    (card_biUnion_upper B _ (fun w hw ↦ hc w hw (fun h ↦ hv (h ▸ hw))))
  have hcard := Finset.card_le_card_sdiff_add_card (s := incident S A v)
    (t := incident (restrictEdges S A (U \ B)) A v)
  have hcard' : ((incident S A v).card : ℝ) ≤
    (incident S A v \ incident (restrictEdges S A (U \ B)) A v).card +
      (incident (restrictEdges S A (U \ B)) A v).card := by exact_mod_cast hcard
  linarith

/-- The selected edges that meet no other selected edge. -/
def isolated (S : Finset E) (A : E → Finset V) (s : E → Bool) : Finset E :=
  S.filter fun e ↦ s e = true ∧ ∀ f ∈ S, f ≠ e → s f = true → Disjoint (A e) (A f)

def colliding (S : Finset E) (A : E → Finset V) (s : E → Bool) : Finset E :=
  S.filter fun e ↦ s e = true ∧ ∃ f ∈ S, f ≠ e ∧ s f = true ∧ ¬ Disjoint (A e) (A f)

def collisionCount (U : Finset V) (S : Finset E) (A : E → Finset V) (s : E → Bool) : ℝ :=
  ∑ v ∈ U, ∑ e ∈ incident S A v, ∑ f ∈ (incident S A v).erase e,
    selectedIndicator e s * selectedIndicator f s

omit [Fintype E] in
lemma collisionCount_nonneg (U : Finset V) (S : Finset E) (A : E → Finset V) (s : E → Bool) :
    0 ≤ collisionCount U S A s := by
  apply Finset.sum_nonneg
  intro v hv
  apply Finset.sum_nonneg
  intro e he
  apply Finset.sum_nonneg
  intro f hf
  exact mul_nonneg (selectedIndicator_nonneg e s) (selectedIndicator_nonneg f s)

lemma collisionCount_mean (U : Finset V) (S : Finset E) (A : E → Finset V)
    {p D : ℝ} (hD : 0 ≤ D) (hdeg : ∀ v ∈ U, ((incident S A v).card : ℝ) ≤ D) :
    expectation p (collisionCount U S A) ≤ p^2 * U.card * D^2 := by
  change expectation p (fun s ↦ ∑ v ∈ U, ∑ e ∈ incident S A v,
    ∑ f ∈ (incident S A v).erase e, selectedIndicator e s * selectedIndicator f s) ≤ _
  simp_rw [expectation_sum]
  calc
    _ ≤ ∑ v ∈ U, (p^2 * D^2) := by
      apply Finset.sum_le_sum
      intro v hv
      calc
        _ = ∑ e ∈ incident S A v, ∑ f ∈ (incident S A v).erase e, p^2 := by
          apply Finset.sum_congr rfl
          intro e he
          apply Finset.sum_congr rfl
          intro f hf
          exact expectation_selected_mul p e f (Ne.symm (Finset.mem_erase.mp hf).1)
        _ ≤ ∑ e ∈ incident S A v, (incident S A v).card * p^2 := by
          apply Finset.sum_le_sum
          intro e he
          simp only [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr Finset.card_erase_le) (sq_nonneg p)
        _ = p^2 * ((incident S A v).card : ℝ)^2 := by simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (Nat.cast_nonneg _) hD).mpr (hdeg v hv)) (sq_nonneg p)
    _ = _ := by simp; ring

omit [Fintype E] in
lemma colliding_card_le (U : Finset V) (S : Finset E) (A : E → Finset V)
    (hsub : ∀ e ∈ S, A e ⊆ U) (s : E → Bool) :
    ((colliding S A s).card : ℝ) ≤ collisionCount U S A s := by
  classical
  let T : E → V → ℝ := fun e v ↦ if v ∈ A e then
    ∑ f ∈ (incident S A v).erase e, selectedIndicator e s * selectedIndicator f s else 0
  have hT : ∀ e v, 0 ≤ T e v := by
    intro e v
    dsimp [T]
    split_ifs
    · exact Finset.sum_nonneg fun f _ ↦
        mul_nonneg (selectedIndicator_nonneg e s) (selectedIndicator_nonneg f s)
    · rfl
  have hid : collisionCount U S A s = ∑ e ∈ S, ∑ v ∈ U, T e v := by
    dsimp [collisionCount, T, incident]
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hid]
  simp only [colliding, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_le_sum
  intro e he
  split_ifs with h
  · obtain ⟨hs, f, hf, hfe, hfs, hinter⟩ := h
    obtain ⟨v, hve, hvf⟩ := Finset.not_disjoint_iff.mp hinter
    have hvU := hsub e he hve
    have hfinc : f ∈ (incident S A v).erase e :=
      Finset.mem_erase.mpr ⟨hfe, mem_incident S A v f |>.mpr ⟨hf, hvf⟩⟩
    have hb : (1 : ℝ) ≤ T e v := by
      dsimp [T]
      rw [ite_eq_left hve]
      have hh := Finset.single_le_sum (fun g hg ↦
        mul_nonneg (selectedIndicator_nonneg e s) (selectedIndicator_nonneg g s)) hfinc
      simpa [selectedIndicator, hs, hfs] using hh
    exact hb.trans (Finset.single_le_sum (fun w _ ↦ hT e w) hvU)
  · exact Finset.sum_nonneg fun v hv ↦ hT e v

lemma isolated_pairwise (S : Finset E) (A : E → Finset V) (s : E → Bool) :
    (isolated S A s : Set E).Pairwise (fun e f ↦ Disjoint (A e) (A f)) := by
  intro e he f hf hef
  have hE := Finset.mem_filter.mp he
  have hF := Finset.mem_filter.mp hf
  exact hE.2.2 f hF.1 hef.symm hF.2.1

lemma isolated_untouched_disjoint (U : Finset V) (S : Finset E) (A : E → Finset V)
    (s : E → Bool) : Disjoint ((isolated S A s).biUnion A) (untouched U S A s) := by
  apply Finset.disjoint_left.mpr
  intro v hv hvW
  obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
  have heS := (Finset.mem_filter.mp he).1
  have hsel := (Finset.mem_filter.mp he).2.1
  have hno := (Finset.mem_filter.mp hvW).2 e (mem_incident S A v e |>.mpr ⟨heS, hve⟩)
  simp_all

lemma wasted_vertices_le (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card ≤ r)
    (s : E → Bool) :
    ((U \ (untouched U S A s ∪ (isolated S A s).biUnion A)).card : ℝ) ≤
      r * collisionCount U S A s := by
  classical
  have hsubset : U \ (untouched U S A s ∪ (isolated S A s).biUnion A) ⊆
      (colliding S A s).biUnion A := by
    intro v hv
    obtain ⟨hvU, hvnot⟩ := Finset.mem_sdiff.mp hv
    have hnot : ¬ ∀ e ∈ incident S A v, s e = false := by
      intro hh
      exact hvnot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvU, hh⟩))
    push Not at hnot
    obtain ⟨e, he, hse⟩ := hnot
    have hse' : s e = true := by cases hs : s e <;> simp_all
    have heS := (mem_incident S A v e |>.mp he).1
    have hve := (mem_incident S A v e |>.mp he).2
    have hnotiso : e ∉ isolated S A s := by
      intro hh
      exact hvnot (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, hh, hve⟩))
    have hcounter : ¬ ∀ f ∈ S, f ≠ e → s f = true → Disjoint (A e) (A f) := by
      intro hh
      exact hnotiso (Finset.mem_filter.mpr ⟨heS, hse', hh⟩)
    push Not at hcounter
    exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_filter.mpr ⟨heS, hse', hcounter⟩, hve⟩
  calc
    _ ≤ (((colliding S A s).biUnion A).card : ℝ) := by exact_mod_cast Finset.card_le_card hsubset
    _ ≤ (colliding S A s).card * (r : ℝ) := card_biUnion_upper _ _ fun e he ↦
      Nat.cast_le.mpr (hr e (Finset.mem_filter.mp he).1)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (colliding_card_le U S A hsub s) (Nat.cast_nonneg r)
      simpa only [mul_comm] using hh

lemma nibble_budget_inequalities {n r D C a K : ℝ}
    (hn : 0 < n) (_hr : 0 ≤ r) (hD : 0 < D) (_hC : 0 ≤ C)
    (ha : 0 < a) (hK : 0 ≤ K) (hcode : n*C ≤ K*D)
    (hsize : 512*r ≤ a*n) (hmany : 16*r^2*(K+1)^2 ≤ a^5*n) :
    4*n*(4*a*r^2*D*C) ≤ (a^2*D)^2 * (a^2*n/(K+1)) ∧
    4*(2*a*n*r) ≤ (a*n/8)^2 := by
  have hK1 : 0 < K+1 := by linarith
  have hh : 16*r^2*K*(K+1) ≤ a^5*n := by
    calc
      _ ≤ 16*r^2*(K+1)*(K+1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : K ≤ K+1)
          (by positivity : 0 ≤ 16*r^2)) hK1.le
      _ = 16*r^2*(K+1)^2 := by ring
      _ ≤ _ := hmany
  have hdiv : 16*r^2*K ≤ a^5*n/(K+1) := (le_div_iff₀ hK1).mpr hh
  constructor
  · calc
      _ = (16*a*r^2*D)*(n*C) := by ring
      _ ≤ (16*a*r^2*D)*(K*D) := mul_le_mul_of_nonneg_left hcode (by positivity)
      _ = (a*D^2)*(16*r^2*K) := by ring
      _ ≤ (a*D^2)*(a^5*n/(K+1)) := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by ring
  · have hh := mul_le_mul_of_nonneg_left hsize (show 0 ≤ a*n by positivity)
    nlinarith only [hh]

lemma nibble_bad_loss {n D C a K : ℝ} (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hcode : n*C ≤ K*D) :
    (a^2*n/(K+1))*C ≤ a^2*D := by
  have hK1 : 0 < K+1 := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hK1]
  have hh := mul_le_mul_of_nonneg_left hcode (sq_nonneg a)
  nlinarith only [hh, mul_nonneg (sq_nonneg a) hD]

lemma residual_mean_estimate (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hr0 : 1 ≤ r) {D ε C p a : ℝ}
    (hD : 0 < D) (he : 0 ≤ ε) (heD : ε ≤ D) (hC : 0 ≤ C) (hCa : C ≤ a*D)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (ha : 0 ≤ a) (hpa : p*D = a)
    (hra : (r : ℝ)*a ≤ 1)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card = r)
    (hdeg : ∀ v ∈ U, |((incident S A v).card : ℝ) - D| ≤ ε)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C)
    (v : V) (hv : v ∈ U) :
    |expectation p (fun s ↦ ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s) -
      (1 - ((r-1 : ℕ) : ℝ)*a)*D| ≤ (1+2*(r : ℝ)*a)*ε + 6*(r : ℝ)^2*a^2*D := by
  let d : ℝ := (incident S A v).card
  let q : ℝ := 1 - ((r-1 : ℕ) : ℝ)*a
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hd : d ≤ 2*D := by have := (abs_le.mp (hdeg v hv)).2; dsimp [d]; linarith
  have hq1 : q ≤ 1 := by
    dsimp [q]
    linarith [mul_nonneg (Nat.cast_nonneg (r-1)) ha]
  have hq0 : 0 ≤ q := by
    have hrl : ((r-1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.sub_le r 1
    have hh := mul_le_mul_of_nonneg_right hrl ha
    dsimp [q]
    linarith
  have hmean := residual_degree_mean U S A hr0 hD.le he hC hp hp1 hsub hr hdeg hcodeg v hv
  have hqeq : 1 - p*((r-1 : ℕ) : ℝ)*D = q := by dsimp [q]; nlinarith only [hpa]
  rw [hqeq] at hmean
  have hglobal : p * ((r : ℝ)*(D+ε)) ≤ 2*a*r := by
    calc
      _ ≤ p*((r : ℝ)*(2*D)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith : D+ε ≤ 2*D) (Nat.cast_nonneg _)) hp
      _ = _ := by nlinarith only [hpa]
  have hsq : (p*((r : ℝ)*(D+ε)))^2/2 ≤ 2*a^2*(r : ℝ)^2 := by
    have hh := (sq_le_sq₀ (show 0 ≤ p*((r : ℝ)*(D+ε)) by positivity)
      (show 0 ≤ 2*a*r by positivity)).mpr hglobal
    nlinarith only [hh]
  have hC' : p*(r : ℝ)^2*C ≤ a^2*(r : ℝ)^2 := by
    calc
      _ ≤ p*(r : ℝ)^2*(a*D) := mul_le_mul_of_nonneg_left hCa (by positivity)
      _ = _ := by linear_combination a * (r : ℝ)^2 * hpa
  have hinner : p*((r : ℝ)*ε+(r : ℝ)^2*C)+(p*((r : ℝ)*(D+ε)))^2/2 ≤
      p*(r : ℝ)*ε+3*a^2*(r : ℝ)^2 := by nlinarith only [hC', hsq]
  have hbound : d * (p*((r : ℝ)*ε+(r : ℝ)^2*C)+(p*((r : ℝ)*(D+ε)))^2/2) ≤
      2*(r : ℝ)*a*ε+6*(r : ℝ)^2*a^2*D := by
    calc
      _ ≤ d*(p*(r : ℝ)*ε+3*a^2*(r : ℝ)^2) := mul_le_mul_of_nonneg_left hinner hd0
      _ ≤ (2*D)*(p*(r : ℝ)*ε+3*a^2*(r : ℝ)^2) := mul_le_mul_of_nonneg_right hd (by positivity)
      _ = _ := by linear_combination 2 * (r : ℝ) * ε * hpa
  have hcenter : |d*q-q*D| ≤ ε := by
    have hh : |d*q-q*D| = |d-D| * q := by
      rw [show d*q-q*D = (d-D)*q by ring, abs_mul, abs_of_nonneg hq0]
    rw [hh]
    exact (mul_le_mul_of_nonneg_left hq1 (abs_nonneg _)).trans (by simpa [d] using hdeg v hv)
  calc
    _ ≤ |expectation p (fun s ↦ ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s) - d*q| +
        |d*q-q*D| := abs_sub_le _ _ _
    _ ≤ (2*(r : ℝ)*a*ε+6*(r : ℝ)^2*a^2*D)+ε := add_le_add (hmean.trans hbound) hcenter
    _ = _ := by ring

omit [Fintype E] [DecidableEq E] in
lemma incident_restrict_subset (S : Finset E) (A : E → Finset V) (W : Finset V) (v : V) :
    incident (restrictEdges S A W) A v ⊆ incident S A v := by
  rw [incident_restrict]
  exact Finset.filter_subset _ _

lemma one_round (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hr0 : 1 ≤ r) {D ε C a K : ℝ}
    (hD : 1 ≤ D) (he : 0 ≤ ε) (hequarter : ε ≤ D/4) (hC : 0 ≤ C)
    (ha : 0 < a) (ha16 : a ≤ 1/16) (hra : (r : ℝ)*a ≤ 1/4)
    (hK : 0 ≤ K) (hcode : U.card*C ≤ K*D) (hCa : C ≤ a*D)
    (hsize : 512*(r : ℝ) ≤ a*U.card)
    (hmany : 16*(r : ℝ)^2*(K+1)^2 ≤ a^5*U.card)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card = r)
    (hdeg : ∀ v ∈ U, |((incident S A v).card : ℝ) - D| ≤ ε)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C) :
    ∃ W : Finset V, ∃ T M : Finset E,
      W ⊆ U ∧ T ⊆ S ∧ (∀ e ∈ T, A e ⊆ W) ∧ M ⊆ S ∧
      (M : Set E).Pairwise (fun e f ↦ Disjoint (A e) (A f)) ∧
      Disjoint W (M.biUnion A) ∧
      ((W.card : ℝ) ≤ (1-a/2)*U.card) ∧
      (((U \ (W ∪ M.biUnion A)).card : ℝ) ≤ (16*(r : ℝ)+1)*a^2*U.card) ∧
      ∀ v ∈ W, |((incident T A v).card : ℝ) - (1-((r-1 : ℕ) : ℝ)*a)*D| ≤
        (1+2*(r : ℝ)*a)*ε + 8*(r : ℝ)^2*a^2*D := by
  classical
  let n : ℝ := U.card
  let p : ℝ := a/D
  let Y : V → (E → Bool) → ℝ := fun v s ↦
    ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr0
  have hD0 : 0 < D := by linarith
  have heD : ε ≤ D := by linarith
  have hn : 0 < n := by dsimp [n]; nlinarith only [hsize, hr1, ha]
  have hn0 : 0 ≤ n := hn.le
  have hp : 0 ≤ p := div_nonneg ha.le hD0.le
  have hp1 : p ≤ 1 := (div_le_one hD0).mpr (by linarith)
  have hpa : p*D = a := div_mul_cancel₀ a hD0.ne'
  have hK1 : 0 < K+1 := by linarith
  have hmax : ∀ v ∈ U, ((incident S A v).card : ℝ) ≤ D+ε := by
    intro v hv
    have := (abs_le.mp (hdeg v hv)).2
    linarith
  have hmult : p*(D+ε) ≤ 2*a := by
    have hh := mul_le_mul_of_nonneg_left heD hp
    nlinarith only [hh, hpa]
  have hmul0 : 0 ≤ p*(D+ε) := by positivity
  have hsq : (p*(D+ε))^2 ≤ 4*a^2 := by
    have hh := (sq_le_sq₀ hmul0 (by positivity : 0 ≤ 2*a)).mpr hmult
    nlinarith only [hh]
  have hY : ∀ v ∈ U, expectation p (fun s ↦ (Y v s - expectation p (Y v))^2) ≤
      4*a*(r : ℝ)^2*D*C := by
    intro v hv
    have hh := residual_degree_variance U S A (by linarith : 0 ≤ D+ε) hC hp hp1 hsub
      (fun e he ↦ (hr e he).le) hmax hcodeg v hv
    apply hh.trans
    have hsq' : (D+ε)^2 ≤ (2*D)^2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
    calc
      _ = (p*(r : ℝ)^2*C)*(D+ε)^2 := by ring
      _ ≤ (p*(r : ℝ)^2*C)*(2*D)^2 := mul_le_mul_of_nonneg_left hsq' (by positivity)
      _ = _ := by linear_combination 4*(r : ℝ)^2*D*C*hpa
  have hZ : expectation p (fun s ↦ (((untouched U S A s).card : ℝ) -
      expectation p (fun s ↦ ((untouched U S A s).card : ℝ)))^2) ≤ 2*a*n*r := by
    apply (untouched_variance U S A hp hp1 (fun e he ↦ (hr e he).le) hmax).trans
    calc
      _ ≤ p*n*(2*D)*r := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : D+ε ≤ 2*D)
          (by positivity : 0 ≤ p*n)) (Nat.cast_nonneg r)
      _ = _ := by linear_combination 2*n*(r : ℝ)*hpa
  have hCollision : expectation p (collisionCount U S A) ≤ 4*a^2*n := by
    apply (collisionCount_mean U S A (by linarith : 0 ≤ D+ε) hmax).trans
    have hh := mul_le_mul_of_nonneg_left hsq hn0
    nlinarith only [hh]
  have hbudgets := nibble_budget_inequalities hn (Nat.cast_nonneg r) hD0 hC ha hK hcode hsize hmany
  obtain ⟨s, hsB, hsZ, hsC⟩ := exists_controlled_outcome hp hp1 U Y
    (fun s ↦ ((untouched U S A s).card : ℝ)) (collisionCount U S A)
    (t := a^2*D) (b := a^2*n/(K+1)) (u := a*n/8) (c := 16*a^2*n)
    (by positivity) (by positivity) (by positivity) (by positivity)
    hY hZ (collisionCount_nonneg U S A) hCollision hbudgets.1 hbudgets.2 (by ring_nf; rfl)
  let B : Finset V := U.filter fun v ↦ a^2*D < |Y v s - expectation p (Y v)|
  let U₀ := untouched U S A s
  let W := U₀ \ B
  let S₀ := restrictEdges S A U₀
  let T := restrictEdges S₀ A W
  let M := isolated S A s
  have hU₀ : U₀ ⊆ U := Finset.filter_subset _ _
  have hW₀ : W ⊆ U₀ := Finset.sdiff_subset
  have hS₀ : S₀ ⊆ S := Finset.filter_subset _ _
  have hT₀ : T ⊆ S₀ := Finset.filter_subset _ _
  have hsub₀ : ∀ e ∈ S₀, A e ⊆ U₀ := fun e he ↦ (Finset.mem_filter.mp he).2
  have hTW : ∀ e ∈ T, A e ⊆ W := fun e he ↦ (Finset.mem_filter.mp he).2
  have hMS : M ⊆ S := Finset.filter_subset _ _
  have hBcard : (B.card : ℝ) ≤ a^2*n/(K+1) := hsB
  have hbmax : a^2*n/(K+1) ≤ a^2*n := by
    rw [div_le_iff₀ hK1]
    nlinarith only [mul_nonneg (show 0 ≤ a^2*n by positivity) hK]
  have hmeanZ : expectation p (fun s ↦ ((untouched U S A s).card : ℝ)) ≤ n*(1-5*a/8) := by
    apply (untouched_mean_upper U S A hp hp1 (by linarith : 0 ≤ D+ε) (D := D-ε) ?_).trans
    · apply mul_le_mul_of_nonneg_left _ hn0
      have hpe : p*ε ≤ a/4 := by
        have hh := mul_le_mul_of_nonneg_left hequarter hp
        nlinarith only [hh, hpa]
      have haa := mul_nonneg ha.le (sub_nonneg.mpr ha16)
      nlinarith only [hpe, hpa, hsq, haa]
    · intro v hv
      have hb := abs_le.mp (hdeg v hv)
      constructor <;> linarith
  have hUcard : (U₀.card : ℝ) ≤ (1-a/2)*n := by
    have hh := (abs_le.mp hsZ).2
    dsimp [U₀]
    linarith
  have hwaste0 : ((U \ (U₀ ∪ M.biUnion A)).card : ℝ) ≤ r*collisionCount U S A s :=
    wasted_vertices_le U S A hsub (fun e he ↦ (hr e he).le) s
  have hwaste : ((U \ (W ∪ M.biUnion A)).card : ℝ) ≤ (16*(r : ℝ)+1)*a^2*n := by
    have hset : U \ (W ∪ M.biUnion A) ⊆ (U \ (U₀ ∪ M.biUnion A)) ∪ B := by
      intro v hv
      simp only [W, Finset.mem_sdiff, Finset.mem_union] at *
      tauto
    have hcard : ((U \ (W ∪ M.biUnion A)).card : ℝ) ≤
        (U \ (U₀ ∪ M.biUnion A)).card + B.card := by
      exact_mod_cast (Finset.card_le_card hset).trans (Finset.card_union_le _ _)
    have hc := mul_le_mul_of_nonneg_left hsC (Nat.cast_nonneg r)
    nlinarith only [hcard, hwaste0, hBcard, hbmax, hc]
  refine ⟨W, T, M, hW₀.trans hU₀, hT₀.trans hS₀, hTW, hMS,
    isolated_pairwise S A s,
    (isolated_untouched_disjoint U S A s).symm.mono_left hW₀,
    (Nat.cast_le.mpr (Finset.card_le_card hW₀)).trans hUcard, hwaste, ?_⟩
  intro v hv
  obtain ⟨hv₀, hvB⟩ := Finset.mem_sdiff.mp hv
  have hvU := hU₀ hv₀
  have htest : |Y v s - expectation p (Y v)| ≤ a^2*D := by
    apply le_of_not_gt
    intro hh
    exact hvB (Finset.mem_filter.mpr ⟨hvU, hh⟩)
  have hmeanY := residual_mean_estimate U S A hr0 hD0 he heD hC hCa hp hp1 ha.le hpa
    (by linarith : (r : ℝ)*a ≤ 1) hsub hr hdeg hcodeg v hvU
  have hdegeq : ((incident S₀ A v).card : ℝ) = Y v s :=
    residual_degree_eq U S A hsub s v hv₀
  have hdegree0 : |((incident S₀ A v).card : ℝ) - (1-((r-1 : ℕ) : ℝ)*a)*D| ≤
      (1+2*(r : ℝ)*a)*ε + 6*(r : ℝ)^2*a^2*D + a^2*D := by
    rw [hdegeq]
    exact (abs_sub_le (Y v s) (expectation p (Y v)) _).trans (by linarith)
  have hc₀ : ∀ w ∈ B, v ≠ w → ((incident S₀ A v ∩ incident S₀ A w).card : ℝ) ≤ C := by
    intro w hw hvw
    apply (Nat.cast_le.mpr (Finset.card_le_card (Finset.inter_subset_inter
      (incident_restrict_subset S A U₀ v) (incident_restrict_subset S A U₀ w)))).trans
    exact hcodeg v hvU w (Finset.mem_filter.mp hw).1 hvw
  have hloss := degree_loss_deleting U₀ B S₀ A hC hsub₀ v hc₀ hvB
  change ((incident S₀ A v).card : ℝ) - B.card*C ≤ ((incident T A v).card : ℝ) at hloss
  have hBCloss : B.card*C ≤ a^2*D :=
    (mul_le_mul_of_nonneg_right hBcard hC).trans (nibble_bad_loss hD0.le hK hcode)
  have hupper : ((incident T A v).card : ℝ) ≤ (incident S₀ A v).card :=
    Nat.cast_le.mpr (Finset.card_le_card (incident_restrict_subset S₀ A W v))
  have hrerr : 2*a^2*D ≤ 2*(r : ℝ)^2*a^2*D := by
    have hh : (2 : ℝ) ≤ 2*(r : ℝ)^2 := by nlinarith only [hr1]
    have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ a^2*D by positivity)
    nlinarith only [hh']
  apply abs_le.mpr
  have hlow0 := (abs_le.mp hdegree0).1
  have hupp0 := (abs_le.mp hdegree0).2
  constructor <;> nlinarith only [hloss, hBCloss, hupper, hrerr, hlow0, hupp0]

omit [Fintype E] [DecidableEq E] in
lemma incident_mono {S T : Finset E} (h : S ⊆ T) (A : E → Finset V) (v : V) :
    incident S A v ⊆ incident T A v := by
  intro e he
  obtain ⟨he, hv⟩ := mem_incident S A v e |>.mp he
  exact mem_incident T A v e |>.mpr ⟨h he, hv⟩

/-- The bookkeeping invariant of a partial matching and its active graph. -/
structure PackingState (U : Finset V) (S : Finset E) (A : E → Finset V) where
  vertices : Finset V
  edges : Finset E
  chosen : Finset E
  vertices_sub : vertices ⊆ U
  edges_sub : edges ⊆ S
  support : ∀ e ∈ edges, A e ⊆ vertices
  chosen_sub : chosen ⊆ S
  matching : (chosen : Set E).Pairwise (fun e f ↦ Disjoint (A e) (A f))
  separation : Disjoint vertices (chosen.biUnion A)

namespace PackingState

noncomputable def initial (U : Finset V) (S : Finset E) (A : E → Finset V)
    (hsub : ∀ e ∈ S, A e ⊆ U) : PackingState U S A where
  vertices := U
  edges := S
  chosen := ∅
  vertices_sub := Finset.Subset.refl _
  edges_sub := Finset.Subset.refl _
  support := hsub
  chosen_sub := Finset.empty_subset _
  matching := by simp
  separation := by simp

noncomputable def compose {U : Finset V} {S : Finset E} {A : E → Finset V}
    (P : PackingState U S A) (Q : PackingState P.vertices P.edges A) : PackingState U S A where
  vertices := Q.vertices
  edges := Q.edges
  chosen := P.chosen ∪ Q.chosen
  vertices_sub := Q.vertices_sub.trans P.vertices_sub
  edges_sub := Q.edges_sub.trans P.edges_sub
  support := Q.support
  chosen_sub := Finset.union_subset P.chosen_sub (Q.chosen_sub.trans P.edges_sub)
  matching := by
    have hcross (e : E) (he : e ∈ P.chosen) (f : E) (hf : f ∈ Q.chosen) :
        Disjoint (A e) (A f) := by
      apply P.separation.symm.mono
      · intro v hv
        exact Finset.mem_biUnion.mpr ⟨e, he, hv⟩
      · exact P.support f (Q.chosen_sub hf)
    intro e he f hf hef
    rcases Finset.mem_union.mp he with he | he <;> rcases Finset.mem_union.mp hf with hf | hf
    · exact P.matching he hf hef
    · exact hcross e he f hf
    · exact (hcross f hf e he).symm
    · exact Q.matching he hf hef
  separation := by
    rw [Finset.union_biUnion]
    exact Finset.disjoint_union_right.mpr
      ⟨P.separation.mono_left Q.vertices_sub, Q.separation⟩

omit [Fintype E] in
lemma compose_waste {U : Finset V} {S : Finset E} {A : E → Finset V}
    (P : PackingState U S A) (Q : PackingState P.vertices P.edges A) :
    ((U \ ((P.compose Q).vertices ∪ (P.compose Q).chosen.biUnion A)).card : ℝ) ≤
      (U \ (P.vertices ∪ P.chosen.biUnion A)).card +
      (P.vertices \ (Q.vertices ∪ Q.chosen.biUnion A)).card := by
  have hsub : U \ ((P.compose Q).vertices ∪ (P.compose Q).chosen.biUnion A) ⊆
      (U \ (P.vertices ∪ P.chosen.biUnion A)) ∪
      (P.vertices \ (Q.vertices ∪ Q.chosen.biUnion A)) := by
    intro v hv
    simp only [compose, Finset.union_biUnion, Finset.mem_sdiff, Finset.mem_union] at *
    tauto
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

end PackingState

/-- Iteration with stopping when the requested small residual has already
been reached. All choices are finite and use the one-round theorem. -/
lemma nibble_iteration (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hr0 : 1 ≤ r) (k : ℕ) {D ε C a K d : ℝ}
    (hD : 0 < D) (he : 0 ≤ ε) (hC : 0 ≤ C)
    (ha : 0 < a) (ha16 : a ≤ 1/16) (hra : (r : ℝ)*a ≤ 1/4)
    (hK : 0 ≤ K) (_hd : 0 < d)
    (hDmin : 1 ≤ (1-((r-1 : ℕ) : ℝ)*a)^k*D)
    (hecap : (1+2*(r : ℝ)*a)^k*(ε+8*(r : ℝ)^2*a^2*D*k) ≤
      (1-((r-1 : ℕ) : ℝ)*a)^k*D/4)
    (hCmin : C ≤ a*((1-((r-1 : ℕ) : ℝ)*a)^k*D))
    (hcode : U.card*C ≤ K*((1-((r-1 : ℕ) : ℝ)*a)^k*D))
    (hsize : 512*(r : ℝ) ≤ a*d*U.card)
    (hmany : 16*(r : ℝ)^2*(K+1)^2 ≤ a^5*d*U.card)
    (hcontract : (1-a/2)^k ≤ d)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card = r)
    (hdeg : ∀ v ∈ U, |((incident S A v).card : ℝ) - D| ≤ ε)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C) :
    ∃ P : PackingState U S A,
      ((P.vertices.card : ℝ) ≤ d*U.card) ∧
      (((U \ (P.vertices ∪ P.chosen.biUnion A)).card : ℝ) ≤
        k*(16*(r : ℝ)+1)*a^2*U.card) := by
  classical
  let q : ℝ := 1-((r-1 : ℕ) : ℝ)*a
  let g : ℝ := 1+2*(r : ℝ)*a
  let b : ℝ := 1-a/2
  let er : ℕ → ℝ := fun i ↦ g^i*(ε+8*(r : ℝ)^2*a^2*D*i)
  let c : ℝ := (16*(r : ℝ)+1)*a^2
  have hr0' : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hrle : ((r-1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.sub_le r 1
  have hq0 : 0 ≤ q := by
    have hh := mul_le_mul_of_nonneg_right hrle ha.le
    dsimp [q]
    linarith
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [mul_nonneg (Nat.cast_nonneg (r-1)) ha.le]
  have hg : 1 ≤ g := by dsimp [g]; nlinarith only [mul_nonneg hr0' ha.le]
  have hg0 : 0 ≤ g := by linarith
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hDibounds (i : ℕ) (hi : i ≤ k) : q^k*D ≤ q^i*D ∧ q^i*D ≤ D := by
    constructor
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq0 hq1 hi) hD.le
    · exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) hD.le).trans_eq (one_mul D)
  have hernonneg (i : ℕ) : 0 ≤ er i := by dsimp [er]; positivity
  have herbounds (i : ℕ) (hi : i ≤ k) : er i ≤ q^i*D/4 := by
    have herle : er i ≤ er k := by
      apply mul_le_mul
      · exact pow_le_pow_right₀ hg hi
      · have hh : (i : ℝ) ≤ k := by exact_mod_cast hi
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hh
          (show 0 ≤ 8*(r : ℝ)^2*a^2*D by positivity))
      · positivity
      · positivity
    exact (herle.trans hecap).trans (div_le_div_of_nonneg_right (hDibounds i hi).1 (by norm_num))
  have herrec (i : ℕ) : g*er i+8*(r : ℝ)^2*a^2*(q^i*D) ≤ er (i+1) := by
    have hiD : q^i*D ≤ D :=
      (mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) hD.le).trans_eq (one_mul D)
    have hgpow : 1 ≤ g^(i+1) := one_le_pow₀ hg
    have hcD : 0 ≤ 8*(r : ℝ)^2*a^2*D := by positivity
    have hh : 8*(r : ℝ)^2*a^2*(q^i*D) ≤ g^(i+1)*(8*(r : ℝ)^2*a^2*D) := by
      calc
        _ ≤ 8*(r : ℝ)^2*a^2*D := mul_le_mul_of_nonneg_left hiD (by positivity)
        _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hgpow hcD
    have heq : er (i+1) = g*er i + g^(i+1)*(8*(r : ℝ)^2*a^2*D) := by
      dsimp [er]
      rw [pow_succ]
      push_cast
      ring
    rw [heq]
    exact add_le_add le_rfl hh
  have hiter : ∀ i ≤ k, ∃ P : PackingState U S A,
      (((P.vertices.card : ℝ) ≤ d*U.card) ∨
        ((P.vertices.card : ℝ) ≤ b^i*U.card) ∧
        ∀ v ∈ P.vertices, |((incident P.edges A v).card : ℝ)-q^i*D| ≤ er i) ∧
      (((U \ (P.vertices ∪ P.chosen.biUnion A)).card : ℝ) ≤ i*c*U.card) := by
    intro i
    induction i with
    | zero =>
      intro hi
      refine ⟨PackingState.initial U S A hsub, Or.inr ⟨?_, ?_⟩, ?_⟩
      · simp [PackingState.initial]
      · simpa [PackingState.initial, er] using hdeg
      · simp [PackingState.initial]
    | succ i ih =>
      intro hik
      have hik' : i ≤ k := (Nat.le_succ i).trans hik
      obtain ⟨P, hP, hwasteP⟩ := ih hik'
      rcases hP with hsmall | ⟨hcount, hregular⟩
      · refine ⟨P, Or.inl hsmall, hwasteP.trans ?_⟩
        have hh : (i : ℝ) ≤ (i+1 : ℕ) := by exact_mod_cast Nat.le_succ i
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hc0) (Nat.cast_nonneg U.card)
      · by_cases hsmall : (P.vertices.card : ℝ) ≤ d*U.card
        · refine ⟨P, Or.inl hsmall, hwasteP.trans ?_⟩
          have hh : (i : ℝ) ≤ (i+1 : ℕ) := by exact_mod_cast Nat.le_succ i
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hc0) (Nat.cast_nonneg U.card)
        have hlarge : d*U.card < (P.vertices.card : ℝ) := lt_of_not_ge hsmall
        have hni : (P.vertices.card : ℝ) ≤ U.card := Nat.cast_le.mpr (Finset.card_le_card P.vertices_sub)
        have hDi : 1 ≤ q^i*D := hDmin.trans (hDibounds i hik').1
        have hcodei : P.vertices.card*C ≤ K*(q^i*D) :=
          (mul_le_mul_of_nonneg_right hni hC).trans
            (hcode.trans (mul_le_mul_of_nonneg_left (hDibounds i hik').1 hK))
        have hsizei : 512*(r : ℝ) ≤ a*P.vertices.card := by
          have hh := mul_le_mul_of_nonneg_left hlarge.le ha.le
          nlinarith only [hsize, hh]
        have hmanyi : 16*(r : ℝ)^2*(K+1)^2 ≤ a^5*P.vertices.card := by
          have hh := mul_le_mul_of_nonneg_left hlarge.le (show 0 ≤ a^5 by positivity)
          nlinarith only [hmany, hh]
        have hcodegi : ∀ v ∈ P.vertices, ∀ w ∈ P.vertices, v ≠ w →
            ((incident P.edges A v ∩ incident P.edges A w).card : ℝ) ≤ C := by
          intro v hv w hw hvw
          apply (Nat.cast_le.mpr (Finset.card_le_card (Finset.inter_subset_inter
            (incident_mono P.edges_sub A v) (incident_mono P.edges_sub A w)))).trans
          exact hcodeg v (P.vertices_sub hv) w (P.vertices_sub hw) hvw
        obtain ⟨W, T, M, hWU, hTS, hTW, hMS, hmatch, hsep, hWcard, hwaste, hreg⟩ :=
          one_round P.vertices P.edges A hr0 hDi (hernonneg i) (herbounds i hik') hC
            ha ha16 hra hK hcodei
            (hCmin.trans (mul_le_mul_of_nonneg_left (hDibounds i hik').1 ha.le))
            hsizei hmanyi P.support (fun e he ↦ hr e (P.edges_sub he)) hregular hcodegi
        let Q : PackingState P.vertices P.edges A := ⟨W,T,M,hWU,hTS,hTW,hMS,hmatch,hsep⟩
        refine ⟨P.compose Q, Or.inr ⟨?_, ?_⟩, ?_⟩
        · change (W.card : ℝ) ≤ b^(i+1)*U.card
          calc
            _ ≤ b*P.vertices.card := hWcard
            _ ≤ b*(b^i*U.card) := mul_le_mul_of_nonneg_left hcount hb0
            _ = _ := by rw [pow_succ]; ring
        · intro v hv
          change |((incident T A v).card : ℝ)-q^(i+1)*D| ≤ er (i+1)
          have hh := hreg v hv
          have heq : (1-((r-1 : ℕ) : ℝ)*a)*(q^i*D) = q^(i+1)*D := by
            change q*(q^i*D) = _
            rw [pow_succ]
            ring
          rw [heq] at hh
          exact hh.trans (herrec i)
        · apply (PackingState.compose_waste P Q).trans
          change (U \ (P.vertices ∪ P.chosen.biUnion A)).card +
            ((P.vertices \ (W ∪ M.biUnion A)).card : ℝ) ≤ (i+1 : ℕ)*c*U.card
          have hh := mul_le_mul_of_nonneg_left hni hc0
          change ((P.vertices \ (W ∪ M.biUnion A)).card : ℝ) ≤ c*P.vertices.card at hwaste
          push_cast
          nlinarith only [hwasteP, hwaste, hh]
  obtain ⟨P, hP, hwaste⟩ := hiter k le_rfl
  refine ⟨P, ?_, ?_⟩
  · rcases hP with hsmall | ⟨hbound, _⟩
    · exact hsmall
    · exact hbound.trans (mul_le_mul_of_nonneg_right hcontract (Nat.cast_nonneg U.card))
  · simpa only [c, mul_assoc] using hwaste

open Filter Topology

/-- Fixed nibble parameters, chosen in the order required by packing:
first the tolerated residual, then finitely many rounds, then regularity. -/
lemma nibble_parameters (r : ℕ) {d : ℝ} (hd : 0 < d) :
    ∃ (a : ℝ) (k : ℕ) (e : ℝ), 0 < a ∧ a ≤ 1/16 ∧
      (r : ℝ)*a ≤ 1/4 ∧ 0 < e ∧
      0 < (1-((r-1 : ℕ) : ℝ)*a)^k ∧
      (1+2*(r : ℝ)*a)^k*(e+8*(r : ℝ)^2*a^2*k) ≤
        (1-((r-1 : ℕ) : ℝ)*a)^k/4 ∧
      (1-a/2)^k ≤ d ∧ k*(16*(r : ℝ)+1)*a^2 ≤ d := by
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hd
    (Real.exp_lt_one_iff.mpr (show (-1/2 : ℝ) < 0 by norm_num))
  let Q : ℝ := Real.exp (-((r-1 : ℕ) : ℝ))^M
  let G : ℝ := Real.exp (2*(r : ℝ))^M
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  let e : ℝ := Q/(16*G)
  have he : 0 < e := by dsimp [e]; positivity
  have ha0 : Tendsto (fun n : ℕ ↦ (1 : ℝ)/n) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop |>.congr (by simp)
  have ha2k : Tendsto (fun n : ℕ ↦ ((1 : ℝ)/n)^2*(n*M : ℕ)) atTop (𝓝 0) := by
    apply (show Tendsto (fun n : ℕ ↦ (1 : ℝ)/n * M) atTop (𝓝 0) by
      simpa using ha0.mul_const (M : ℝ)).congr' _
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    push_cast
    field_simp
  have hq : Tendsto (fun n : ℕ ↦ (1-((r-1 : ℕ) : ℝ)*(1/n))^(n*M))
      atTop (𝓝 Q) := by
    simpa only [pow_mul, div_eq_mul_inv, one_mul, sub_eq_add_neg, neg_mul]
      using (Real.tendsto_one_add_div_pow_exp (-((r-1 : ℕ) : ℝ))).pow M
  have hg : Tendsto (fun n : ℕ ↦ (1+2*(r : ℝ)*(1/n))^(n*M))
      atTop (𝓝 G) := by
    simpa only [pow_mul, div_eq_mul_inv, one_mul]
      using (Real.tendsto_one_add_div_pow_exp (2*(r : ℝ))).pow M
  have hb : Tendsto (fun n : ℕ ↦ (1-(1/(n : ℝ))/2)^(n*M))
      atTop (𝓝 (Real.exp (-1/2)^M)) := by
    convert (Real.tendsto_one_add_div_pow_exp (-1/2)).pow M using 1
    ext n
    rw [pow_mul]
    congr 2
    ring
  have herr : Tendsto (fun n : ℕ ↦
      (1+2*(r : ℝ)*(1/n))^(n*M)*(e+8*(r : ℝ)^2*(1/n)^2*(n*M : ℕ)))
      atTop (𝓝 (G*e)) := by
    have ht : Tendsto (fun n : ℕ ↦ e+8*(r : ℝ)^2*((1/(n : ℝ))^2*(n*M : ℕ)))
        atTop (𝓝 e) := by
      simpa using tendsto_const_nhds.add (ha2k.const_mul (8*(r : ℝ)^2))
    simpa only [mul_assoc] using hg.mul ht
  have hw : Tendsto (fun n : ℕ ↦ (n*M : ℕ)*(16*(r : ℝ)+1)*(1/(n : ℝ))^2)
      atTop (𝓝 0) := by
    convert ha2k.const_mul (16*(r : ℝ)+1) using 1 <;> (try {ext n; ring_nf})
  have hgap : G*e < Q/4 := by dsimp [e]; field_simp; nlinarith
  have hparams : ∀ᶠ n : ℕ in atTop,
      0 < (1 : ℝ)/n ∧ (1 : ℝ)/n ≤ 1/16 ∧
      (r : ℝ)*(1/n) ≤ 1/4 ∧
      0 < (1-((r-1 : ℕ) : ℝ)*(1/n))^(n*M) ∧
      (1+2*(r : ℝ)*(1/n))^(n*M)*(e+8*(r : ℝ)^2*(1/n)^2*(n*M : ℕ)) ≤
        (1-((r-1 : ℕ) : ℝ)*(1/n))^(n*M)/4 ∧
      (1-(1/(n : ℝ))/2)^(n*M) ≤ d ∧
      (n*M : ℕ)*(16*(r : ℝ)+1)*(1/(n : ℝ))^2 ≤ d := by
    filter_upwards [eventually_ge_atTop 1, ha0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/16)),
      (ha0.const_mul (r : ℝ)).eventually (gt_mem_nhds (by norm_num : (r : ℝ)*0 < 1/4)),
      hq.eventually (lt_mem_nhds hQ),
      herr.eventually_lt (hq.div_const 4) hgap,
      hb.eventually (gt_mem_nhds hM), hw.eventually (gt_mem_nhds hd)] with n hn ha hr hq' he1 hb' hw'
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    refine ⟨by positivity, ha.le, hr.le, hq', ?_, hb'.le, hw'.le⟩
    exact he1.le
  obtain ⟨n, hn⟩ := hparams.exists
  exact ⟨1/(n : ℝ), n*M, e, hn.1, hn.2.1, hn.2.2.1, he, hn.2.2.2⟩

theorem almost_perfect_matching (r : ℕ) (hr : 1 ≤ r) {K₀ η : ℝ}
    (hK₀ : 0 ≤ K₀) (hη : 0 < η) :
    ∃ e T : ℝ, 0 < e ∧ 0 < T ∧
    ∀ {V E : Type} [DecidableEq V] [Fintype E] [DecidableEq E],
    ∀ (U : Finset V) (S : Finset E) (A : E → Finset V) (D C : ℝ),
      T ≤ D → T ≤ (U.card : ℝ) → 0 ≤ C → C ≤ e*D →
      U.card*C ≤ K₀*D →
      (∀ i ∈ S, A i ⊆ U) → (∀ i ∈ S, (A i).card = r) →
      (∀ v ∈ U, |((incident S A v).card : ℝ)-D| ≤ e*D) →
      (∀ v ∈ U, ∀ w ∈ U, v ≠ w →
        ((incident S A v ∩ incident S A w).card : ℝ) ≤ C) →
      ∃ M ⊆ S, (M : Set E).Pairwise (fun i j ↦ Disjoint (A i) (A j)) ∧
        (1-η)*(U.card : ℝ) ≤ r*(M.card : ℝ) := by
  let d : ℝ := η/4
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨a,k,e₀,ha,ha16,hra,he₀,hq,hecap,hcontract,hwaste⟩ := nibble_parameters r hd
  let q : ℝ := (1-((r-1 : ℕ) : ℝ)*a)^k
  let K : ℝ := K₀/q
  have hq0 : 0 < q := hq
  have hK : 0 ≤ K := div_nonneg hK₀ hq0.le
  let e : ℝ := min e₀ (a*q)
  have he : 0 < e := lt_min he₀ (mul_pos ha hq0)
  let T : ℝ := max (1/q) (max (512*(r : ℝ)/(a*d))
    (16*(r : ℝ)^2*(K+1)^2/(a^5*d)))
  have hT1 : 1/q ≤ T := le_max_left _ _
  have hT2 : 512*(r : ℝ)/(a*d) ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hT3 : 16*(r : ℝ)^2*(K+1)^2/(a^5*d) ≤ T :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hT : 0 < T := (by positivity : 0 < (1 : ℝ)/q).trans_le hT1
  refine ⟨e,T,he,hT,?_⟩
  intro V E instV instF instE U S A D C hD hn hC hCe hcode hsub hunif hdeg hcodeg
  have hD0 : 0 < D := hT.trans_le hD
  have hDmin : 1 ≤ q*D := by
    have hh := (div_le_iff₀ hq0).mp (hT1.trans hD)
    nlinarith only [hh]
  have hcap : (1+2*(r : ℝ)*a)^k*(e₀*D+8*(r : ℝ)^2*a^2*D*k) ≤ q*D/4 := by
    have hh := mul_le_mul_of_nonneg_right hecap hD0.le
    dsimp [q]
    nlinarith only [hh]
  have hCmin : C ≤ a*(q*D) := by
    calc C ≤ e*D := hCe
         _ ≤ (a*q)*D := mul_le_mul_of_nonneg_right (min_le_right _ _) hD0.le
         _ = _ := by ring
  have hcod : U.card*C ≤ K*(q*D) := by
    have heq : K*(q*D)=K₀*D := by dsimp [K]; field_simp
    rw [heq]
    exact hcode
  have hsize : 512*(r : ℝ) ≤ a*d*U.card := by
    have hh := (div_le_iff₀ (mul_pos ha hd)).mp (hT2.trans hn)
    nlinarith only [hh]
  have hmany : 16*(r : ℝ)^2*(K+1)^2 ≤ a^5*d*U.card := by
    have hh := (div_le_iff₀ (mul_pos (pow_pos ha _) hd)).mp (hT3.trans hn)
    nlinarith only [hh]
  have hdeg' : ∀ v ∈ U, |((incident S A v).card : ℝ)-D| ≤ e₀*D := by
    intro v hv
    exact (hdeg v hv).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hD0.le)
  obtain ⟨P,hP,hwP⟩ := nibble_iteration U S A hr k hD0
    (mul_nonneg he₀.le hD0.le) hC ha ha16 hra hK hd hDmin hcap hCmin hcod
      hsize hmany hcontract hsub hunif hdeg' hcodeg
  refine ⟨P.chosen,P.chosen_sub,P.matching,?_⟩
  have hcard : (P.chosen.biUnion A).card = P.chosen.card*r := by
    rw [Finset.card_biUnion P.matching]
    calc
      _ = ∑ _i ∈ P.chosen, r := Finset.sum_congr rfl (fun i hi ↦ hunif i (P.chosen_sub hi))
      _ = _ := by simp
  have hsubset : P.vertices ∪ P.chosen.biUnion A ⊆ U := by
    refine Finset.union_subset P.vertices_sub ?_
    intro v hv
    obtain ⟨i,hi,hvi⟩ := Finset.mem_biUnion.mp hv
    exact hsub i (P.chosen_sub hi) hvi
  have hcount := Finset.card_sdiff_add_card_eq_card hsubset
  rw [Finset.card_union_of_disjoint P.separation, hcard] at hcount
  have hcount' : ((U \ (P.vertices ∪ P.chosen.biUnion A)).card : ℝ) +
      (P.vertices.card : ℝ) + P.chosen.card*r = U.card := by
    have hh : ((U \ (P.vertices ∪ P.chosen.biUnion A)).card : ℝ) +
      ((P.vertices.card : ℝ) + P.chosen.card*r) = U.card := by exact_mod_cast hcount
    linarith
  have hww := mul_le_mul_of_nonneg_right hwaste (Nat.cast_nonneg U.card)
  dsimp [d] at hP hww
  nlinarith only [hP,hwP,hww,hcount', show (0 : ℝ) ≤ U.card from Nat.cast_nonneg _, hη]

end Hypergraph

end Nibble
end AsymptoticallyMinimalLittlewood

end OAI
