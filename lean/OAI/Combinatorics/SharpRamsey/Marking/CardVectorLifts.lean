import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.HighRank

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
section
namespace SharpLogRamsey.RichUnion
noncomputable section
open Module
section ProjectiveLifts
variable {K : Type*} [Field K] [Fintype K] {n : ℕ}
theorem card_vectorLifts (X : Finset (Projectivization K (Fin n → K))) :
    (vectorLifts X).card = X.card * (Fintype.card K - 1) := by
  classical
  let e₁ := (Projectivization.nonZeroEquivProjectivizationProdUnits K (Fin n → K)).subtypeEquiv
    (p := fun v => Projectivization.mk K v.1 v.2 ∈ X)
    (q := fun z => z.1 ∈ X) (fun _ => Iff.rfl)
  let e₂ : {z : Projectivization K (Fin n → K) × Kˣ // z.1 ∈ X} ≃ X × Kˣ :=
    { toFun := fun z => (⟨z.1.1, z.2⟩, z.1.2)
      invFun := fun z => ⟨(z.1.1, z.2), z.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := Fintype.card_congr (e₁.trans e₂)
  simpa [vectorLifts, Fintype.card_units, Fintype.card_subtype] using h

def projectiveIn (X : Finset (Projectivization K (Fin n → K)))
    (W : Submodule K (Fin n → K)) : Finset (Projectivization K (Fin n → K)) := by
  classical
  exact X.filter (fun a => a.submodule ≤ W)
omit [Fintype K] in

@[simp] theorem mem_projectiveIn (X : Finset (Projectivization K (Fin n → K)))
    (W : Submodule K (Fin n → K)) (a : Projectivization K (Fin n → K)) :
    a ∈ projectiveIn X W ↔ a ∈ X ∧ a.submodule ≤ W := by
  classical
  simp [projectiveIn]

theorem vectorLifts_projectiveIn (X : Finset (Projectivization K (Fin n → K)))
    (W : Submodule K (Fin n → K)) :
    vectorLifts (projectiveIn X W) = inSubspace (vectorLifts X) W := by
  ext v
  simp only [mem_vectorLifts, mem_projectiveIn, Projectivization.submodule_mk,
    Submodule.span_singleton_le_iff_mem, mem_inSubspace]
  exact exists_and_right

def projectivePoints (W : Submodule K (Fin n → K)) :
    Finset (Projectivization K (Fin n → K)) := by
  classical
  letI := Fintype.ofFinite (Projectivization K (Fin n → K))
  exact Finset.univ.filter (fun a => a.submodule ≤ W)

@[simp] theorem mem_projectivePoints (W : Submodule K (Fin n → K))
    (a : Projectivization K (Fin n → K)) :
    a ∈ projectivePoints W ↔ a.submodule ≤ W := by
  classical
  simp [projectivePoints]

def projectiveUnion (𝓥 : Set (Submodule K (Fin n → K))) :
    Finset (Projectivization K (Fin n → K)) := by
  classical
  letI := Fintype.ofFinite (Projectivization K (Fin n → K))
  exact Finset.univ.filter (fun a => ∃ W ∈ 𝓥, a.submodule ≤ W)

@[simp] theorem mem_projectiveUnion (𝓥 : Set (Submodule K (Fin n → K)))
    (a : Projectivization K (Fin n → K)) :
    a ∈ projectiveUnion 𝓥 ↔ ∃ W ∈ 𝓥, a.submodule ≤ W := by
  classical
  simp [projectiveUnion]

def projectiveSubmoduleEquiv (W : Submodule K (Fin n → K)) :
    Projectivization K W ≃ {a : Projectivization K (Fin n → K) // a.submodule ≤ W} := by
  let f : Projectivization K W → {a : Projectivization K (Fin n → K) // a.submodule ≤ W} :=
    fun a => ⟨Projectivization.map W.subtype W.injective_subtype a, by
      induction a using Projectivization.ind with
      | h v hv =>
        rw [Projectivization.map_mk, Projectivization.submodule_mk,
          Submodule.span_singleton_le_iff_mem]
        exact v.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    exact Projectivization.map_injective W.subtype W.injective_subtype
      (congrArg Subtype.val h)
  · rintro ⟨a, ha⟩
    have hmem : a.rep ∈ W := ha (by
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _)
    let v : W := ⟨a.rep, hmem⟩
    have hv : v ≠ 0 := fun h => a.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk K v hv, ?_⟩
    apply Subtype.ext
    exact a.mk_rep

theorem card_projectivePoints (W : Submodule K (Fin n → K)) :
    (projectivePoints W).card = Nat.card (Projectivization K W) := by
  classical
  let := Fintype.ofFinite (Projectivization K (Fin n → K))
  rw [Nat.card_congr (projectiveSubmoduleEquiv W), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  rfl

theorem card_projectivePoints_mul (W : Submodule K (Fin n → K)) :
    (projectivePoints W).card * (Fintype.card K - 1) = Nat.card W - 1 := by
  rw [card_projectivePoints, ← Nat.card_eq_fintype_card]
  exact (Projectivization.card K W).symm

theorem rich_union_projective (hn : 0 < n)
    (X : Finset (Projectivization K (Fin n → K)))
    (𝓥 : Set (Submodule K (Fin n → K))) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hne : ∀ W ∈ 𝓥, W ≠ ⊥)
    (hrich : ∀ W ∈ 𝓥, δ*(projectivePoints W).card ≤ (projectiveIn X W).card) :
    ((projectiveUnion 𝓥).card : ℝ) ≤ (5*n/δ)^n * X.card := by
  classical
  have hq : 0 < Fintype.card K - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  have hqR : (0 : ℝ) < (Fintype.card K - 1 : ℕ) := by exact_mod_cast hq
  have hv : ∀ W ∈ 𝓥, δ*((Nat.card W : ℝ)-1) ≤
      (inSubspace (vectorLifts X) W).card := by
    intro W hW
    rw [← vectorLifts_projectiveIn, card_vectorLifts]
    have hN : 1 ≤ Nat.card W := Nat.card_pos
    have hcard := card_projectivePoints_mul W
    have hcardR : ((projectivePoints W).card : ℝ)*(Fintype.card K-1 : ℕ) =
        (Nat.card W : ℝ)-1 := by
      exact_mod_cast hcard
    rw [Nat.cast_mul, ← hcardR]
    nlinarith [mul_le_mul_of_nonneg_right (hrich W hW) hqR.le]
  have hcover : ∀ y ∈ vectorLifts (projectiveUnion 𝓥), ∃ W ∈ 𝓥, y ∈ W := by
    intro y hy
    obtain ⟨hy0, hY⟩ := (mem_vectorLifts _ _).mp hy
    obtain ⟨W, hW, hyW⟩ := (mem_projectiveUnion _ _).mp hY
    rw [Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem] at hyW
    exact ⟨W, hW, hyW⟩
  have h := rich_union_vector hn (vectorLifts X) (vectorLifts (projectiveUnion 𝓥))
    𝓥 δ hδ hδ1 hne hv hcover
  rw [card_vectorLifts, card_vectorLifts, Nat.cast_mul, Nat.cast_mul] at h
  exact (mul_le_mul_iff_left₀ hqR).mp (by simpa [mul_assoc] using h)

end ProjectiveLifts
end
end SharpLogRamsey.RichUnion
end
section

namespace SharpLogRamsey.HighRankGeometry
open scoped BigOperators
open SharpLogRamsey.RichUnion
noncomputable section
variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

lemma sum_powers_le_twice {q : ℝ} (hq : 2 ≤ q) {r : ℕ} (hr : 0 < r) :
    ∑ i ∈ Finset.range r, q^i ≤ 2*q^(r-1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.succ_sub_one]
  clear hr
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hqm : 0 ≤ q^m := pow_nonneg (by linarith) _
    have hmul : 2*q^m ≤ q^(m+1) := by rw [pow_succ]; nlinarith
    simp only [Nat.succ_eq_add_one] at ih
    linarith

lemma projective_card_le (W : Submodule K (Fin n → K)) {r : ℕ}
    (hr : 0 < r) (hdim : Module.finrank K W = r) :
    ((projectivePoints W).card : ℝ) ≤ 2*(Fintype.card K : ℝ)^(r-1) := by
  rw [card_projectivePoints, Projectivization.card_of_finrank K W hdim]
  simp only [Nat.cast_sum, Nat.cast_pow, Nat.card_eq_fintype_card]
  exact sum_powers_le_twice (by exact_mod_cast Fintype.one_lt_card (α := K)) hr

lemma subspace_mass_le (mass : Projectivization K (Fin n → K) → ℝ)
    (X : Finset (Projectivization K (Fin n → K)))
    (hsupport : ∀ x, x ∉ X → mass x = 0) (M : ℝ)
    (hcap : ∀ x ∈ X, mass x ≤ M) (W : Submodule K (Fin n → K)) :
    ∑ x ∈ projectivePoints W, mass x ≤ M*(projectiveIn X W).card := by
  classical
  have hsub : projectiveIn X W ⊆ projectivePoints W := by
    intro x hx
    exact (mem_projectivePoints W x).mpr ((mem_projectiveIn _ _ _).mp hx).2
  have he : ∑ x ∈ projectiveIn X W, mass x = ∑ x ∈ projectivePoints W, mass x := by
    apply Finset.sum_subset hsub
    intro x hx hnot
    apply hsupport x
    intro hxX
    exact hnot ((mem_projectiveIn X W x).mpr ⟨hxX, (mem_projectivePoints W x).mp hx⟩)
  rw [← he]
  calc
    _ ≤ ∑ _x ∈ projectiveIn X W, M := Finset.sum_le_sum (fun x hx =>
      hcap x ((mem_projectiveIn _ _ _).mp hx).1)
    _ = _ := by simp [mul_comm]

theorem threshold_rich (mass : Projectivization K (Fin n → K) → ℝ)
    (X : Finset (Projectivization K (Fin n → K)))
    (hsupport : ∀ x, x ∉ X → mass x = 0)
    (A u : ℝ) (hA : 0 < A) (hu : 0 < u)
    (r : ℕ) (hr : 0 < r)
    (hcap : ∀ x ∈ X, mass x ≤ A/(Fintype.card K : ℝ)^r)
    (W : Submodule K (Fin n → K)) (hrank : Module.finrank K W = r)
    (hhit : u ≤ (Fintype.card K : ℝ)*∑ x ∈ projectivePoints W, mass x) :
    (u/(2*A))*((projectivePoints W).card : ℝ) ≤ (projectiveIn X W).card := by
  have hq : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hp : (0 : ℝ) < (Fintype.card K : ℝ)^(r-1) := pow_pos hq _
  have hr' : r = (r-1)+1 := by omega
  have hm := mul_le_mul_of_nonneg_left (subspace_mass_le mass X hsupport _ hcap W) hq.le
  have hm' : u*(Fintype.card K : ℝ)^(r-1) ≤ A*(projectiveIn X W).card := by
    have hu' := hhit.trans hm
    rw [hr', pow_succ] at hu'
    have he : (Fintype.card K : ℝ)*(A/((Fintype.card K : ℝ)^(r-1)*(Fintype.card K : ℝ))*
        (projectiveIn X W).card) = (A*(projectiveIn X W).card)/(Fintype.card K : ℝ)^(r-1) := by
      have algebra (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
          a*(c/(b*a)*d) = c*d/b := by field_simp
      exact algebra _ _ _ _ (ne_of_gt hq) (ne_of_gt hp)
    rw [he] at hu'
    exact (le_div_iff₀ hp).mp hu'
  have hc := projective_card_le W hr hrank
  apply (mul_le_mul_iff_right₀ (show 0 < 2*A by positivity)).mp
  calc
    (2*A)*((u/(2*A))*((projectivePoints W).card : ℝ)) = u*(projectivePoints W).card := by
      have algebra (a b c : ℝ) (ha : a ≠ 0) : a*(b/a*c) = b*c := by
        rw [← mul_assoc, mul_div_cancel₀ _ ha]
      exact algebra _ _ _ (ne_of_gt (show 0 < 2*A by positivity))
    _ ≤ u*(2*(Fintype.card K : ℝ)^(r-1)) := mul_le_mul_of_nonneg_left hc hu.le
    _ ≤ (2*A)*(projectiveIn X W).card := by nlinarith

theorem high_rank_tail (hn : 0 < n)
    (mass : Projectivization K (Fin n → K) → ℝ)
    (X Y : Finset (Projectivization K (Fin n → K)))
    (hsupport : ∀ x, x ∉ X → mass x = 0)
    (A u : ℝ) (hA : 0 < A) (hu : 0 < u) (huA : u ≤ 2*A)
    (r : ℕ) (hr : 0 < r)
    (hcap : ∀ x ∈ X, mass x ≤ A/(Fintype.card K : ℝ)^r)
    (W : Projectivization K (Fin n → K) → Submodule K (Fin n → K))
    (hrank : ∀ y ∈ Y, Module.finrank K (W y) = r)
    (hy : ∀ y ∈ Y, y.submodule ≤ W y)
    (hhit : ∀ y ∈ Y, u ≤ (Fintype.card K : ℝ)*∑ x ∈ projectivePoints (W y), mass x) :
    (Y.card : ℝ) ≤ (10*(n : ℝ)*A/u)^n*X.card := by
  classical
  let 𝓥 : Set (Submodule K (Fin n → K)) := W '' (Y : Set _)
  have hδ : 0 < u/(2*A) := by positivity
  have hδ1 : u/(2*A) ≤ 1 := (div_le_one (by positivity)).mpr huA
  have hne : ∀ U ∈ 𝓥, U ≠ ⊥ := by
    rintro U ⟨y, hyY, rfl⟩ hz
    have h := hrank y hyY
    rw [hz, finrank_bot] at h
    omega
  have hrich : ∀ U ∈ 𝓥, (u/(2*A))*((projectivePoints U).card : ℝ) ≤
      (projectiveIn X U).card := by
    rintro U ⟨y, hyY, rfl⟩
    exact threshold_rich mass X hsupport A u hA hu r hr hcap (W y) (hrank y hyY) (hhit y hyY)
  have hh := rich_union_projective hn X 𝓥 (u/(2*A)) hδ hδ1 hne hrich
  have hsub : Y ⊆ projectiveUnion 𝓥 := by
    intro y hyY
    exact (mem_projectiveUnion 𝓥 y).mpr ⟨W y, ⟨y, hyY, rfl⟩, hy y hyY⟩
  calc
    _ ≤ ((projectiveUnion 𝓥).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ (5*(n : ℝ)/(u/(2*A)))^n*X.card := hh
    _ = _ := by congr 2; field_simp; ring

end
end SharpLogRamsey.HighRankGeometry
end

section

namespace SharpLogRamsey.FiniteSamplingBounds
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Ω : Type*} [Fintype Ω]

noncomputable def rowTail (w : Ω → ℝ) (E : Finset Ω) (h T : ℕ) : ℝ :=
  ∑ z : Fin h → Ω, if T ≤ hitCount E z then rowWeight w z else 0

lemma rowTail_nonneg (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (E : Finset Ω) (h T : ℕ) :
    0 ≤ rowTail w E h T := by
  apply Finset.sum_nonneg
  intro z _
  split_ifs
  · exact rowWeight_nonneg w hw z
  · exact le_rfl

lemma rowTail_le_one (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (ht : ∑ x, w x = 1)
    (E : Finset Ω) (h T : ℕ) : rowTail w E h T ≤ 1 := by
  rw [← rowWeight_total w ht h]
  apply Finset.sum_le_sum
  intro z _
  split_ifs <;> try rfl
  exact rowWeight_nonneg w hw z

lemma rowTail_moment (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (ht : ∑ x, w x = 1) (E : Finset Ω) (h T : ℕ) (b : ℝ) (hb : 1 ≤ b) :
    b^T*rowTail w E h T ≤ (1+(b-1)*(∑ x ∈ E, w x))^h := by
  classical
  rw [← rowMoment w ht E h b, rowTail, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  split_ifs with hz
  · rw [mul_comm (b^T)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb hz) (rowWeight_nonneg w hw z)
  · simp only [mul_zero]
    exact mul_nonneg (rowWeight_nonneg w hw z) (pow_nonneg (by linarith) _)

theorem rowTail_small (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (ht : ∑ x, w x = 1) (E : Finset Ω) (h T : ℕ)
    (q a : ℝ) (hq : 0 < q) (ha : 0 < a) (ha1 : a ≤ 1/20)
    (hp : ∑ x ∈ E, w x ≤ a/q) (hT : (h : ℝ)/(10*q) ≤ T) :
    rowTail w E h T ≤ (20*Real.exp (1/2)*a)^T := by
  let b : ℝ := 1/(20*a)
  have hb : 1 ≤ b := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hb0 : 0 < b := by linarith
  have hp0 : 0 ≤ ∑ x ∈ E, w x := Finset.sum_nonneg (fun x _ => hw x)
  have hv0 : 0 ≤ (b-1)*(∑ x ∈ E, w x) := mul_nonneg (by linarith) hp0
  have hM := rowTail_moment w hw ht E h T b hb
  have hExp : (1+(b-1)*(∑ x ∈ E, w x))^h ≤
      Real.exp ((h : ℝ)*((b-1)*(∑ x ∈ E, w x))) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (show 0 ≤ 1+(b-1)*(∑ x ∈ E, w x) by linarith)
    simpa only [add_comm] using Real.add_one_le_exp ((b-1)*(∑ x ∈ E, w x))
  have he : (h : ℝ)*((b-1)*(∑ x ∈ E, w x)) ≤ (T : ℝ)/2 := by
    have h1 : (b-1)*(∑ x ∈ E, w x) ≤ b*(a/q) := by
      exact mul_le_mul (by linarith) hp hp0 hb0.le
    have h2 : b*(a/q) = 1/(20*q) := by dsimp [b]; field_simp
    rw [h2] at h1
    have hh := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg h)
    have ht' : (h : ℝ)/(20*q) ≤ (T : ℝ)/2 := by
      have heq : (h : ℝ)/(20*q) = ((h : ℝ)/(10*q))/2 := by ring
      rw [heq]
      exact div_le_div_of_nonneg_right hT (by norm_num)
    have hh' : (h : ℝ)*((b-1)*(∑ x ∈ E, w x)) ≤ (h : ℝ)/(20*q) := by
      simpa only [mul_one_div] using hh
    exact hh'.trans ht'
  have hM' : b^T*rowTail w E h T ≤ Real.exp ((T : ℝ)/2) :=
    hM.trans (hExp.trans (Real.exp_le_exp.mpr he))
  have hdiv : rowTail w E h T ≤ Real.exp ((T : ℝ)/2)/b^T :=
    (le_div_iff₀ (pow_pos hb0 T)).mpr (by simpa only [mul_comm] using hM')
  convert hdiv using 1
  have hexp : Real.exp ((T : ℝ)/2) = (Real.exp (1/2))^T := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp, ← div_pow]
  congr 1
  dsimp [b]
  field_simp

lemma rowTail_zero (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (E : Finset Ω)
    (h T : ℕ) (hT : 0 < T) (hp : ∑ x ∈ E, w x = 0) :
    rowTail w E h T = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro z _
  split_ifs with hz
  · have hc : 0 < (univ.filter (fun i => z i ∈ E)).card := by
      change 0 < hitCount E z
      omega
    obtain ⟨i,hi⟩ := Finset.card_pos.mp hc
    have hxi : z i ∈ E := (mem_filter.mp hi).2
    have hwi : w (z i) = 0 := by
      apply le_antisymm _ (hw _)
      rw [← hp]
      exact Finset.single_le_sum (fun x _ => hw x) hxi
    exact Finset.prod_eq_zero (mem_univ i) hwi
  · rfl

end
end SharpLogRamsey.FiniteSamplingBounds
end

section

namespace SharpLogRamsey.DyadicTail
open scoped BigOperators
open Finset Classical
noncomputable section

lemma exists_band {a u : ℝ} (ha : 0 < a) (hu : 0 < u) (hau : a ≤ u) :
    ∃ j : ℕ, u*(1/2 : ℝ)^(j+1) < a ∧ a ≤ u*(1/2 : ℝ)^j := by
  have hex : ∃ j : ℕ, u*(1/2 : ℝ)^j < a := by
    obtain ⟨j,hj⟩ := exists_pow_lt_of_lt_one (div_pos ha hu) (by norm_num : (1/2 : ℝ) < 1)
    exact ⟨j,(by simpa only [mul_comm] using (lt_div_iff₀ hu).mp hj)⟩
  have hn : Nat.find hex ≠ 0 := by
    intro hz
    have hh := Nat.find_spec hex
    rw [hz, pow_zero, mul_one] at hh
    exact (not_lt_of_ge hau) hh
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hn
  refine ⟨j, ?_, ?_⟩
  · simpa only [hj, Nat.succ_eq_add_one] using Nat.find_spec hex
  · exact le_of_not_gt (fun h => by have hh := Nat.find_min' hex h; omega)

lemma finite_geometric (J : Finset ℕ) : ∑ j ∈ J, (1/2 : ℝ)^j ≤ 2 := by
  have hs : Summable (fun j : ℕ => (1/2 : ℝ)^j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hh := hs.sum_le_tsum J (fun j _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) j)
  simpa only [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1), show (1-(1/2 : ℝ))⁻¹ = 2 by norm_num] using hh

variable {Y : Type*} [Fintype Y]

theorem small_tail_sum (a w : Y → ℝ) (u C M : ℝ) (n T : ℕ)
    (hu : 0 < u) (hC : 0 ≤ C) (hM : 0 ≤ M) (hCu : C*u ≤ 1)
    (ha : ∀ x, 0 < a x ∧ a x ≤ u) (hw : ∀ x, w x ≤ (C*a x)^T)
    (hT : n+1 ≤ T)
    (htail : ∀ v, 0 < v → v ≤ u →
      ((univ.filter (fun x : Y => v ≤ a x)).card : ℝ) ≤ M*(u/v)^n) :
    ∑ x, w x ≤ M*2^(n+1) := by
  classical
  choose level hlower hupper using fun x => exists_band (ha x).1 hu (ha x).2
  let J : Finset ℕ := univ.image level
  have hband (j : ℕ) :
      ∑ x ∈ univ.filter (fun x : Y => level x = j), w x ≤ M*2^n*(1/2 : ℝ)^j := by
    let δ : ℝ := (1/2 : ℝ)^j
    have hδ : 0 < δ := pow_pos (by norm_num) _
    have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hv : 0 < u*δ/2 := by positivity
    have hvu : u*δ/2 ≤ u := by nlinarith
    have hcnt := htail (u*δ/2) hv hvu
    have hsub : univ.filter (fun x : Y => level x = j) ⊆
        univ.filter (fun x : Y => u*δ/2 ≤ a x) := by
      intro x hx
      have hh := hlower x
      rw [(mem_filter.mp hx).2, pow_succ] at hh
      exact mem_filter.mpr ⟨mem_univ _, by dsimp [δ]; linarith⟩
    have hc' : ((univ.filter (fun x : Y => level x = j)).card : ℝ) ≤
        ((univ.filter (fun x : Y => u*δ/2 ≤ a x)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hc := hc'.trans hcnt
    have hweight : ∀ x ∈ univ.filter (fun x : Y => level x = j), w x ≤ δ^(n+1) := by
      intro x hx
      have ha' : a x ≤ u*δ := by simpa only [(mem_filter.mp hx).2] using hupper x
      have hca : C*a x ≤ δ := by nlinarith [mul_le_mul_of_nonneg_left ha' hC]
      exact (hw x).trans ((pow_le_pow_left₀ (mul_nonneg hC (ha x).1.le) hca T).trans
        (pow_le_pow_of_le_one hδ.le hδ1 hT))
    calc
      _ ≤ ∑ _x ∈ univ.filter (fun x : Y => level x = j), δ^(n+1) :=
        Finset.sum_le_sum hweight
      _ = ((univ.filter (fun x : Y => level x = j)).card : ℝ)*δ^(n+1) := by simp
      _ ≤ (M*(u/(u*δ/2))^n)*δ^(n+1) := mul_le_mul_of_nonneg_right hc (pow_nonneg hδ.le _)
      _ = M*2^n*δ := by
        have he : u/(u*δ/2) = 2/δ := by field_simp
        rw [he, div_pow, pow_succ]
        field_simp
      _ = _ := rfl
  have hsum : ∑ x, w x = ∑ j ∈ J, ∑ x ∈ univ.filter (fun x : Y => level x = j), w x := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (fun x _ => mem_image.mpr ⟨x, mem_univ _, rfl⟩) w
  rw [hsum]
  calc
    _ ≤ ∑ j ∈ J, M*2^n*(1/2 : ℝ)^j := Finset.sum_le_sum (fun j _ => hband j)
    _ = M*2^n*(∑ j ∈ J, (1/2 : ℝ)^j) := by rw [Finset.mul_sum]
    _ ≤ M*2^n*2 := mul_le_mul_of_nonneg_left (finite_geometric J) (by positivity)
    _ = _ := by rw [pow_succ]; ring

end
end SharpLogRamsey.DyadicTail
end
end

end OAI
