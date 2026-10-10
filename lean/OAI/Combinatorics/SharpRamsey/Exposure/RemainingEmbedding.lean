import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.DivergenceMap

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical
noncomputable section
variable {B β ι : Type*} [Fintype B] [Fintype β] [Fintype ι] [DecidableEq ι] [DecidableEq B]
def remainingEmbedding {m : ℕ} (e : B×Fin (m+1)  ↪  ι) (f : B → Fin (m+1)) :
    B×Fin m  ↪  ↥((freshRepresentatives e f)ᶜ) where
  toFun z := ⟨e (z.1,(f z.1).succAbove z.2), by
    simp only [mem_compl, freshRepresentatives, mem_image, mem_univ,true_and,not_exists]
    intro b hb
    have he := e.injective hb
    have hb' : b=z.1 := (Prod.mk.inj he).1
    subst b
    exact Fin.succAbove_ne (f z.1) z.2 (Prod.mk.inj he).2.symm⟩
  inj' := by
    intro z w h
    have he := e.injective (congrArg Subtype.val h)
    obtain ⟨hb,hx⟩ := Prod.mk.inj he
    obtain ⟨b,x⟩ := z
    obtain ⟨c,y⟩ := w
    dsimp at hb hx
    subst c
    congr 1
    exact Fin.succAbove_right_injective hx

omit [DecidableEq B] in
lemma remaining_own {m : ℕ} (e : B×Fin (m+1)  ↪  ι) (f : B → Fin (m+1))
    (own : ι → Option B) (hown : ∀ b x,own (e (b,x))= some b) (b : B) (x : Fin m) :
    own (remainingEmbedding e f (b,x))= some b := hown _ _

def roundInformation {m : ℕ} (p : Law (ι → β)) (e : B×Fin m  ↪  ι) (own : ι → Option B) : ℝ :=
  (∑ f : B → Fin m, ∑ i, (maximumInformation p i (otherRepresentatives e own f i):ℝ))/
    Fintype.card (B → Fin m)

def nextPotential {m : ℕ} (p : Law (ι → β)) (e : B×Fin m  ↪  ι) : ℝ :=
  (∑ f : B → Fin m, ∑ z, (p.restrict (freshRepresentatives e f)).mass z*
    totalCorrelation ((p.cond (fun x (j:freshRepresentatives e f) => x j) z).restrict
      (freshRepresentatives e f)ᶜ))/Fintype.card (B → Fin m)

lemma roundInformation_nonneg {m : ℕ} (p : Law (ι → β)) (e : B×Fin m  ↪  ι) (own : ι → Option B) :
    0 ≤  roundInformation p e own := by
  unfold roundInformation
  positivity

lemma nextPotential_nonneg {m : ℕ} (p : Law (ι → β)) (e : B×Fin m  ↪  ι) :
    0 ≤ nextPotential p e := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact sum_nonneg (fun f _ => sum_nonneg (fun z _ =>
    mul_nonneg ((p.restrict _).nonneg z) (totalCorrelation_nonneg _)))

theorem roundInformation_budget {m : ℕ} (hm : 2 ≤ m) (p : Law (ι → β))
    (e : B×Fin m  ↪  ι) (own : ι → Option B) (hown : ∀ b x,own (e (b,x))= some b) :
    roundInformation p e own+2*nextPotential p e ≤ 2*totalCorrelation p := by
  have hm0 : 0 < m := by omega
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0:ℝ) < m := by positivity
  let : Nonempty (Fin m) := ⟨⟨0,hm0⟩⟩
  have hc : (0:ℝ)<Fintype.card (B → Fin m) := by exact_mod_cast Fintype.card_pos
  have H := fresh_round_drop p e own hown (by simpa using hm0)
  simp only [Fintype.card_fin,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul] at H
  have hhalf : (1/2:ℝ) ≤ 1-1/(m:ℝ) := by
    have hdiv : (1:ℝ)/(m:ℝ) ≤ 1/2 := (div_le_iff₀ hmpos).mpr (by linarith)
    linarith
  have hmi : 0 ≤ ∑ f : B → Fin m,∑ i,(maximumInformation p i (otherRepresentatives e own f i):ℝ) := by positivity
  have HH := mul_le_mul_of_nonneg_right hhalf hmi
  unfold roundInformation nextPotential
  rw [← mul_div_assoc, ← add_div]
  apply (div_le_iff₀ hc).mpr
  have he : 2*totalCorrelation p*↑(Fintype.card (B → Fin m))=
      2*(↑(Fintype.card (B → Fin m))*totalCorrelation p) := by ring
  rw [he]
  linarith

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open Finset
open scoped Classical
noncomputable section
universe u v w
variable {B : Type v} {β : Type w} [Fintype B] [Fintype β]

def exposureScores (n : ℕ) : (k : ℕ) → {ι : Type u} → [Fintype ι] → [DecidableEq ι] →
    Law (ι → β) → (B × Fin (n+k) ↪ ι) → (ι → Option B) → Fin k → ℝ
  | 0, _, _, _, _, _, _, j => Fin.elim0 j
  | k+1, _, _, _, p, e, own, j => Fin.cases (roundInformation p e own)
      (fun t => (∑ f : B → Fin (n+k+1),
        ∑ z, (p.restrict (freshRepresentatives e f)).mass z *
          exposureScores n k
            ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
              (freshRepresentatives e f)ᶜ)
            (remainingEmbedding e f) (fun i => own i) t) /
          Fintype.card (B → Fin (n+k+1))) j

lemma exposureScores_zero {ι : Type u} [Fintype ι] [DecidableEq ι] (n k : ℕ)
    (p : Law (ι → β)) (e : B × Fin (n+(k+1)) ↪ ι) (own : ι → Option B) :
    exposureScores n (k+1) p e own 0 = roundInformation p e own := rfl

lemma exposureScores_succ {ι : Type u} [Fintype ι] [DecidableEq ι] (n k : ℕ)
    (p : Law (ι → β)) (e : B × Fin (n+(k+1)) ↪ ι) (own : ι → Option B) (j : Fin k) :
    exposureScores n (k+1) p e own j.succ =
      (∑ f : B → Fin (n+k+1), ∑ z,
        (p.restrict (freshRepresentatives e f)).mass z *
          exposureScores n k
            ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
              (freshRepresentatives e f)ᶜ)
            (remainingEmbedding e f) (fun i => own i) j) /
          Fintype.card (B → Fin (n+k+1)) := rfl

theorem exposureScores_sum_le (n k : ℕ) (hn : 2 ≤ n)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (p : Law (ι → β)) (e : B × Fin (n+k) ↪ ι)
    (own : ι → Option B) (hown : ∀ b x, own (e (b,x)) = some b) :
    (∑ t, exposureScores n k p e own t) ≤ 2 * totalCorrelation p := by
  induction k generalizing ι with
  | zero =>
    simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (totalCorrelation_nonneg p)
  | succ k ih =>
    rw [Fin.sum_univ_succ, exposureScores_zero]
    have hs : (∑ t : Fin k, exposureScores n (k+1) p e own t.succ) ≤
        2 * nextPotential p e := by
      simp_rw [exposureScores_succ, ← sum_div]
      rw [sum_comm]
      simp_rw [sum_comm (s := (univ : Finset (Fin k))), ← mul_sum]
      unfold nextPotential
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      rw [mul_sum]
      apply sum_le_sum
      intro f _
      rw [mul_sum]
      apply sum_le_sum
      intro z _
      rw [mul_left_comm (2:ℝ)]
      apply mul_le_mul_of_nonneg_left _ ((p.restrict _).nonneg z)
      exact ih _ (remainingEmbedding e f) (fun i => own i)
        (fun b x => remaining_own e f own hown b x)
    have hb := roundInformation_budget (by omega : 2 ≤ n+(k+1)) p e own hown
    linarith only [hs,hb]

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open Finset
open scoped Classical
noncomputable section
universe u v w
variable {B : Type v} {β : Type w} [Fintype B] [Fintype β]

theorem exists_exposure_round (n k : ℕ) (hn : 2 ≤ n) (hk : 0 < k)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (p : Law (ι → β))
    (e : B × Fin (n+k) ↪ ι) (own : ι → Option B)
    (hown : ∀ b x, own (e (b,x)) = some b) :
    ∃ t : Fin k, exposureScores n k p e own t ≤ 2 * totalCorrelation p / k := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  have hs := exposureScores_sum_le n k hn p e own hown
  have hconst : (∑ _t : Fin k, 2 * totalCorrelation p / (k:ℝ)) =
      2 * totalCorrelation p := by
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  obtain ⟨t,_, ht⟩ := exists_le_of_sum_le (univ_nonempty : (univ : Finset (Fin k)).Nonempty)
    (hs.trans_eq hconst.symm)
  exact ⟨t,ht⟩
end
end SharpLogRamsey.Selection
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

def tupleDeficit (J : ℝ) (p : Law (ι → β)) : ℝ :=
  (Fintype.card ι:ℝ)*J-entropy p

lemma marginal_deficit_sum (p : Law (ι → β)) (J : ℝ) :
    (∑ i, (J-entropy (p.marginal i))) ≤ tupleDeficit J p := by
  have h := entropy_subadditive_pi p
  simp only [tupleDeficit,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul]
  linarith

lemma tupleDeficit_nonneg (p : Law (ι → β)) (J : ℝ)
    (h : ∀ i, entropy (p.marginal i) ≤ J) : 0 ≤ tupleDeficit J p := by
  exact (sum_nonneg (fun i _ => sub_nonneg.mpr (h i))).trans (marginal_deficit_sum p J)

theorem tupleDeficit_drop (p : Law (ι → β)) (E : Finset ι) (J : ℝ) :
    tupleDeficit J p - ∑ z, (p.restrict E).mass z *
      tupleDeficit J ((p.cond (fun x (i:E) => x i) z).restrict Eᶜ) =
        tupleDeficit J (p.restrict E) := by
  have hc := entropy_restrict_chain p E
  have hn : (Fintype.card ι:ℝ) = (Fintype.card E:ℝ)+Fintype.card ↥(Eᶜ) := by
    simp only [Fintype.card_coe]
    exact_mod_cast (card_add_card_compl E).symm
  simp only [tupleDeficit,mul_sub,sum_sub_distrib,← sum_mul,Law.total,one_mul]
  rw [hn]
  linarith

lemma tupleDeficit_expected_le (p : Law (ι → β)) (E : Finset ι) (J : ℝ)
    (h : ∀ i, entropy (p.marginal i) ≤ J) :
    (∑ z, (p.restrict E).mass z *
      tupleDeficit J ((p.cond (fun x (i:E) => x i) z).restrict Eᶜ)) ≤ tupleDeficit J p := by
  have he := tupleDeficit_nonneg (p.restrict E) J (fun i => by
    simpa only [Law.marginal_restrict] using h i)
  have hd := tupleDeficit_drop p E J
  linarith

theorem tupleDeficit_restrict_le (p : Law (ι → β)) (E : Finset ι) (J : ℝ)
    (h : ∀ i, entropy (p.marginal i) ≤ J) :
    tupleDeficit J (p.restrict E) ≤ tupleDeficit J p := by
  let F := fun x : ι → β => ((fun i : E => x i),(fun i : ↥(Eᶜ) => x i))
  have hf : Function.Injective F := by
    intro x y hxy
    funext i
    by_cases hi : i ∈ E
    · exact congr_fun (congrArg Prod.fst hxy) ⟨i,hi⟩
    · exact congr_fun (congrArg Prod.snd hxy) ⟨i,by simpa using hi⟩
  have he : (p.map F).fst = p.restrict E := by rw [← Law.map_fst,Law.map_map]; rfl
  have he' : (p.map F).snd = p.restrict Eᶜ := by rw [← Law.map_snd,Law.map_map]; rfl
  have hh := entropy_subadditive (p.map F)
  rw [entropy_map_eq_of_injective p F hf,he,he'] at hh
  have hcap := tupleDeficit_nonneg (p.restrict Eᶜ) J (fun i => by
    simpa only [Law.marginal_restrict] using h i)
  have hn : (Fintype.card ι:ℝ) = (Fintype.card E:ℝ)+Fintype.card ↥(Eᶜ) := by
    simp only [Fintype.card_coe]
    exact_mod_cast (card_add_card_compl E).symm
  unfold tupleDeficit at hcap ⊢
  rw [hn]
  linarith

lemma totalCorrelation_le_tupleDeficit (p : Law (ι → β)) (J : ℝ)
    (h : ∀ i, entropy (p.marginal i) ≤ J) : totalCorrelation p ≤ tupleDeficit J p := by
  have hs := sum_le_sum (fun i (_ : i ∈ univ) => h i)
  simp only [sum_const,card_univ,nsmul_eq_mul] at hs
  unfold totalCorrelation tupleDeficit
  linarith

end
end SharpLogRamsey.Selection
namespace SharpLogRamsey.Selection
variable {Ω α Γ A : Type*} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype A]
theorem entropy_le_log_card (p : Law α) (S : Finset α)
    (hs : ∀ a, a ∉ S → p.mass a = 0) : entropy p ≤ Real.log S.card := by
  have hS : 0 < S.card := by
    by_contra! h
    have hz : S = ∅ := card_eq_zero.mp (by omega)
    have hzero : ∑ a, p.mass a = 0 := by
      apply sum_eq_zero
      intro a ha
      exact hs a (by simp [hz])
    linarith [p.total]
  have hsr : (0:ℝ) < S.card := by exact_mod_cast hS
  have hmass : ∑ a ∈ S, p.mass a = 1 := by
    rw [← p.total]
    exact sum_subset (subset_univ S) fun a ha hna => hs a hna
  have h := log_sum S p.mass (fun _ => 1/(S.card:ℝ))
    (fun a ha => p.nonneg a) (fun a ha => by positivity)
    (fun a ha hh => False.elim ((div_ne_zero (by norm_num) hsr.ne') hh))
  rw [hmass] at h
  have hc : ∑ _a ∈ S, (1/(S.card:ℝ)) = 1 := by
    simp only [sum_const, nsmul_eq_mul]
    field_simp
  rw [hc,div_one,Real.log_one,mul_zero] at h
  have he (a : α) : p.mass a*Real.log (p.mass a/(1/(S.card:ℝ))) =
      p.mass a*Real.log (p.mass a)+p.mass a*Real.log S.card := by
    by_cases hz : p.mass a = 0
    · simp [hz]
    rw [div_div_eq_mul_div, div_one, Real.log_mul hz hsr.ne']
    ring
  simp_rw [he] at h
  rw [sum_add_distrib, ← sum_mul, hmass,one_mul] at h
  have hh : ∑ a ∈ S, p.mass a*Real.log (p.mass a) =
      ∑ a, p.mass a*Real.log (p.mass a) := by
    exact sum_subset (subset_univ S) fun a ha hna => by rw [hs a hna,zero_mul]
  rw [hh] at h
  unfold entropy
  linarith

lemma Law.map_support (p : Law Ω) (f : Ω → A) (a : A) (ha : (p.map f).mass a ≠ 0) :
    ∃ x, p.mass x ≠ 0 ∧ f x = a := by
  by_contra hn
  push Not at hn
  apply ha
  change (∑ x with f x = a, p.mass x) = 0
  apply sum_eq_zero
  intro x hx
  by_contra hp
  exact hn x hp (mem_filter.mp hx).2

lemma Law.cond_support (p : Law Ω) (C : Ω → Γ) (c : Γ)
    (hc : (p.map C).mass c ≠ 0) (x : Ω) (hx : (p.cond C c).mass x ≠ 0) :
    p.mass x ≠ 0 ∧ C x = c := by
  rw [p.cond_mass C c hc] at hx
  split_ifs at hx with he
  · exact ⟨(div_ne_zero_iff.mp hx).1,he⟩
  · exact False.elim (hx (zero_div _))

lemma entropy_mapped_support (p : Law Ω) (F : Ω → α) (S : Finset α)
    (hS : ∀ x, p.mass x ≠ 0 → F x ∈ S) : entropy (p.map F) ≤ Real.log S.card := by
  apply entropy_le_log_card
  intro a ha
  by_contra hn
  obtain ⟨x,hx,rfl⟩ := p.map_support F a hn
  exact ha (hS x hx)

end SharpLogRamsey.Selection
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

def tupleSupported (p : Law (ι → β)) (D : ι → Finset β) : Prop :=
  ∀ x, p.mass x ≠ 0 → ∀ i, x i ∈ D i

lemma tupleSupported_marginal_cap (p : Law (ι → β)) (D : ι → Finset β)
    (hD : tupleSupported p D) (J : ℝ) (hJ : ∀ i, Real.log (D i).card ≤ J) (i : ι) :
    entropy (p.marginal i) ≤ J :=
  (entropy_mapped_support p (fun x => x i) (D i) (fun x hx => hD x hx i)).trans (hJ i)

lemma tupleSupported_cond_restrict (p : Law (ι → β)) (D : ι → Finset β)
    (hD : tupleSupported p D) (E : Finset ι) (z : E → β)
    (hz : (p.restrict E).mass z ≠ 0) :
    tupleSupported ((p.cond (fun x (i:E) => x i) z).restrict Eᶜ) (fun i => D i) := by
  intro x hx i
  obtain ⟨y,hy,rfl⟩ := (p.cond (fun x (i:E) => x i) z).map_support _ x hx
  exact hD y ((p.cond_support (fun x (i:E) => x i) z hz y hy).1) i

end
end SharpLogRamsey.Selection
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
universe u v w
variable {B : Type v} {β : Type w} [Fintype B] [Fintype β]

def exposureDeficits (n : ℕ) (J : ℝ) : (k : ℕ) → {ι : Type u} → [Fintype ι] →
    [DecidableEq ι] → Law (ι → β) → (B × Fin (n+k) ↪ ι) → Fin k → ℝ
  | 0, _, _, _, _, _, j => Fin.elim0 j
  | k+1, _, _, _, p, e, j => Fin.cases (tupleDeficit J p)
      (fun t => (∑ f : B → Fin (n+k+1),
        ∑ z, (p.restrict (freshRepresentatives e f)).mass z *
          exposureDeficits n J k
            ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
              (freshRepresentatives e f)ᶜ)
            (remainingEmbedding e f) t) /
          Fintype.card (B → Fin (n+k+1))) j

lemma exposureDeficits_zero (n k : ℕ) (J : ℝ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (p : Law (ι → β)) (e : B × Fin (n+(k+1)) ↪ ι) :
    exposureDeficits n J (k+1) p e 0 = tupleDeficit J p := rfl

lemma exposureDeficits_succ (n k : ℕ) (J : ℝ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (p : Law (ι → β)) (e : B × Fin (n+(k+1)) ↪ ι) (j : Fin k) :
    exposureDeficits n J (k+1) p e j.succ =
      (∑ f : B → Fin (n+k+1), ∑ z,
        (p.restrict (freshRepresentatives e f)).mass z *
          exposureDeficits n J k
            ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
              (freshRepresentatives e f)ᶜ)
            (remainingEmbedding e f) j) / Fintype.card (B → Fin (n+k+1)) := rfl

theorem exposureDeficits_le (n k : ℕ) (J : ℝ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (p : Law (ι → β)) (e : B × Fin (n+k) ↪ ι) (D : ι → Finset β)
    (hD : tupleSupported p D) (hJ : ∀ i, Real.log (D i).card ≤ J) (t : Fin k) :
    exposureDeficits n J k p e t ≤ tupleDeficit J p := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) t
    · exact le_rfl
    · rw [exposureDeficits_succ]
      have hn : (0:ℝ) < Fintype.card (B → Fin (n+k+1)) := by
        let : Nonempty (Fin (n+k+1)) := ⟨⟨0,by omega⟩⟩
        exact_mod_cast Fintype.card_pos
      apply (div_le_iff₀ hn).mpr
      calc
        _ ≤ ∑ f : B → Fin (n+k+1), ∑ z,
            (p.restrict (freshRepresentatives e f)).mass z *
              tupleDeficit J ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
                (freshRepresentatives e f)ᶜ) := by
          apply sum_le_sum
          intro f _
          apply sum_le_sum
          intro z _
          by_cases hz : (p.restrict (freshRepresentatives e f)).mass z = 0
          · rw [hz,zero_mul,zero_mul]
          · apply mul_le_mul_of_nonneg_left _ ((p.restrict _).nonneg z)
            exact ih _ (remainingEmbedding e f) (fun i => D i)
              (tupleSupported_cond_restrict p D hD _ z hz) (fun i => hJ i) j
        _ ≤ ∑ _f : B → Fin (n+k+1), tupleDeficit J p := by
          apply sum_le_sum
          intro f _
          exact tupleDeficit_expected_le p _ J (tupleSupported_marginal_cap p D hD J hJ)
        _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]; ring
end
end SharpLogRamsey.Selection

end

end OAI
