import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.TerminalLaw
import OAI.Combinatorics.TriangleRemoval.Probability.FiniteMean

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def hittingTriangles {n : ℕ} (G F : Graph n) : Finset (Finset (Fin n)) :=
  (triangles G).filter (fun t => ¬ Disjoint F (t.powersetCard 2))

def incidentTriangles {n : ℕ} (G : Graph n) (e : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (triangles G).filter (fun t => e ∈ t.powersetCard 2)

def triangleDegree {n : ℕ} (G : Graph n) (e : Finset (Fin n)) : ℕ :=
  (incidentTriangles G e).card

noncomputable def intact {n : ℕ} (F H : Graph n) : ℝ :=
  if F ⊆ H then 1 else 0

theorem pmfMean_sum {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : β → α → ℝ) :
    pmfMean p (fun a => ∑ b, f b a) = ∑ b, pmfMean p (f b) := by
  simp only [pmfMean, Finset.mul_sum]
  exact Finset.sum_comm

theorem step_mean {n : ℕ} (G : Graph n) (f : Graph n → ℝ)
    (hG : (triangles G).Nonempty) :
    pmfMean (step G) f =
      (∑ t ∈ triangles G, f (G \ t.powersetCard 2)) / ((triangles G).card : ℝ) := by
  rw [step, dite_eq_left hG, pmfMean_map, pmfMean_uniformOfFinset]

theorem intact_delete {n : ℕ} {G F : Graph n} (hF : F ⊆ G)
    (t : Finset (Fin n)) :
    intact F (G \ t.powersetCard 2) =
      1 - if ¬ Disjoint F (t.powersetCard 2) then 1 else 0 := by
  classical
  simp only [intact, Finset.subset_sdiff, hF, true_and]
  split_ifs <;> simp_all

theorem step_mean_intact {n : ℕ} {G F : Graph n} (hF : F ⊆ G)
    (hG : (triangles G).Nonempty) :
    pmfMean (step G) (intact F) =
      1 - ((hittingTriangles G F).card : ℝ) / ((triangles G).card : ℝ) := by
  classical
  rw [step_mean G (intact F) hG]
  simp_rw [intact_delete hF]
  rw [Finset.sum_sub_distrib]
  have hb : (∑ t ∈ triangles G, if ¬ Disjoint F (t.powersetCard 2) then (1 : ℝ) else 0) =
      ((hittingTriangles G F).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [hittingTriangles]
  rw [hb]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [sub_div, div_self (by exact_mod_cast hG.card_pos.ne')]

theorem step_mean_intact_of_not_subset {n : ℕ} {G F : Graph n}
    (hF : ¬ F ⊆ G) : pmfMean (step G) (intact F) = 0 := by
  rw [← pmfMean_const (step G) 0]
  apply pmfMean_congr
  intro H hH
  have hFH : ¬ F ⊆ H := fun h => hF (h.trans (step_support_subset hH))
  simp [intact, hFH]

noncomputable def copyCount {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) : ℝ :=
  ∑ a, intact (required a) G

theorem step_mean_copyCount {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (hG : (triangles G).Nonempty) :
    pmfMean (step G) (copyCount required) = copyCount required G -
      (∑ a, if required a ⊆ G then ((hittingTriangles G (required a)).card : ℝ) else 0) /
        ((triangles G).card : ℝ) := by
  classical
  unfold copyCount
  rw [pmfMean_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : required a ⊆ G
  · rw [step_mean_intact ha hG, ite_eq_left ha, intact, ite_eq_left ha]
  · rw [step_mean_intact_of_not_subset ha, ite_eq_right ha, intact, ite_eq_right ha]
    simp

theorem three_le_card_union {α : Type*} [DecidableEq α]
    {e f : Finset α} (he : e.card = 2) (hf : f.card = 2) (hef : e ≠ f) :
    3 ≤ (e ∪ f).card := by
  have hi : (e ∩ f).card < 2 := by
    by_contra h
    have hge : 2 ≤ (e ∩ f).card := by omega
    have heq : e ∩ f = e := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by omega)
    have hfq : e ∩ f = f := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_right (by omega)
    exact hef (heq.symm.trans hfq)
  have h := Finset.card_union_add_card_inter e f
  omega

theorem triangle_eq_of_two_edges {α : Type*} [DecidableEq α]
    {t u e f : Finset α} (ht : t.card = 3) (hu : u.card = 3)
    (he : e.card = 2) (hf : f.card = 2) (hef : e ≠ f)
    (het : e ⊆ t) (hft : f ⊆ t) (heu : e ⊆ u) (hfu : f ⊆ u) : t = u := by
  have hm := three_le_card_union he hf hef
  have ht' : e ∪ f = t := Finset.eq_of_subset_of_card_le
    (Finset.union_subset het hft) (by omega)
  have hu' : e ∪ f = u := Finset.eq_of_subset_of_card_le
    (Finset.union_subset heu hfu) (by omega)
  exact ht'.symm.trans hu'

theorem sum_card_le_card_biUnion_add_pair_overlaps {α β : Type*}
    [DecidableEq α] [DecidableEq β] (s : Finset α) (F : α → Finset β) :
    (∑ a ∈ s, (F a).card) ≤ (s.biUnion F).card +
      ∑ a ∈ s, ∑ b ∈ s.erase a, ((F a) ∩ F b).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>

    rw [Finset.sum_insert ha, Finset.biUnion_insert]
    have hi : ((F a) ∩ s.biUnion F).card ≤ ∑ b ∈ s, ((F a) ∩ F b).card := by
      rw [Finset.inter_biUnion]
      exact Finset.card_biUnion_le
    have hcard := Finset.card_union_add_card_inter (F a) (s.biUnion F)
    have hsum : (∑ x ∈ s, ∑ b ∈ s.erase x, ((F x) ∩ F b).card) ≤
        ∑ x ∈ s, ∑ b ∈ (insert a s).erase x, ((F x) ∩ F b).card := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.erase_subset_erase x (Finset.subset_insert a s)
      · intro i _ _; exact Nat.zero_le _
    rw [Finset.sum_insert ha, Finset.erase_insert ha]
    omega

theorem hittingTriangles_eq_biUnion {n : ℕ} (G F : Graph n) :
    hittingTriangles G F = F.biUnion (incidentTriangles G) := by
  classical
  ext t
  simp only [hittingTriangles, Finset.mem_filter, Finset.mem_biUnion,
    incidentTriangles, Finset.not_disjoint_iff]
  constructor
  · rintro ⟨ht, e, heF, het⟩
    exact ⟨e, heF, ht, het⟩
  · rintro ⟨e, heF, ht, het⟩
    exact ⟨ht, e, heF, het⟩

theorem incident_pair_card_le_one {n : ℕ} (G : Graph n)
    {e f : Finset (Fin n)} (hef : e ≠ f) :
    ((incidentTriangles G e) ∩ incidentTriangles G f).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro t ht u hu
  simp only [incidentTriangles, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_powersetCard] at ht hu
  exact triangle_eq_of_two_edges (mem_triangles.mp ht.1.1).1
    (mem_triangles.mp hu.1.1).1 ht.1.2.2 ht.2.2.2 hef
    ht.1.2.1 ht.2.2.1 hu.1.2.1 hu.2.2.1

theorem hittingTriangles_card_le_degree_sum {n : ℕ} (G F : Graph n) :
    (hittingTriangles G F).card ≤ ∑ e ∈ F, triangleDegree G e := by
  rw [hittingTriangles_eq_biUnion]
  exact Finset.card_biUnion_le

theorem degree_sum_le_hittingTriangles_add {n : ℕ} (G F : Graph n) :
    (∑ e ∈ F, triangleDegree G e) ≤ (hittingTriangles G F).card + F.card ^ 2 := by
  rw [hittingTriangles_eq_biUnion]
  refine (sum_card_le_card_biUnion_add_pair_overlaps F (incidentTriangles G)).trans ?_
  apply Nat.add_le_add_left
  calc
    (∑ e ∈ F, ∑ f ∈ F.erase e, ((incidentTriangles G e) ∩ incidentTriangles G f).card)
        ≤ ∑ _e ∈ F, F.card := by
          apply Finset.sum_le_sum
          intro e _
          calc
            (∑ f ∈ F.erase e, ((incidentTriangles G e) ∩ incidentTriangles G f).card)
                ≤ ∑ _f ∈ F.erase e, 1 := by
                  apply Finset.sum_le_sum
                  intro f hf
                  exact incident_pair_card_le_one G (Finset.ne_of_mem_erase hf).symm
            _ = (F.erase e).card := by simp
            _ ≤ F.card := Finset.card_le_card (Finset.erase_subset e F)
    _ = F.card ^ 2 := by simp [pow_two]

theorem hittingTriangles_degree_error {n : ℕ} (G F : Graph n) (D δ : ℝ)
    (h : ∀ e ∈ F, |(triangleDegree G e : ℝ) - D| ≤ δ) :
    |((hittingTriangles G F).card : ℝ) - (F.card : ℝ) * D| ≤
      (F.card : ℝ) * δ + (F.card : ℝ) ^ 2 := by
  have hsumlo : (F.card : ℝ) * (D - δ) ≤ ∑ e ∈ F, (triangleDegree G e : ℝ) := by
    calc
      _ = ∑ _e ∈ F, (D - δ) := by simp [mul_sub]
      _ ≤ _ := Finset.sum_le_sum fun e he => by
        have hh := (abs_le.mp (h e he)).1
        linarith
  have hsumhi : (∑ e ∈ F, (triangleDegree G e : ℝ)) ≤ (F.card : ℝ) * (D + δ) := by
    calc
      _ ≤ ∑ _e ∈ F, (D + δ) := Finset.sum_le_sum fun e he => by
        have hh := (abs_le.mp (h e he)).2
        linarith
      _ = _ := by simp [mul_add]
  have hhitlo : (∑ e ∈ F, (triangleDegree G e : ℝ)) ≤
      ((hittingTriangles G F).card : ℝ) + (F.card : ℝ) ^ 2 := by
    exact_mod_cast degree_sum_le_hittingTriangles_add G F
  have hhithi : ((hittingTriangles G F).card : ℝ) ≤
      ∑ e ∈ F, (triangleDegree G e : ℝ) := by
    exact_mod_cast hittingTriangles_card_le_degree_sum G F
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (F.card : ℝ)]

theorem copyCount_drift_error {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (b : ℕ) (D δ : ℝ)
    (hsize : ∀ a, (required a).card = b)
    (hdeg : ∀ e ∈ G, |(triangleDegree G e : ℝ) - D| ≤ δ)
    (hG : (triangles G).Nonempty) :
    |pmfMean (step G) (copyCount required) - copyCount required G +
      ((b : ℝ) * D / (triangles G).card) * copyCount required G| ≤
      (((b : ℝ) * δ + (b : ℝ) ^ 2) / (triangles G).card) * copyCount required G := by
  classical
  let loss (a : α) : ℝ :=
    if required a ⊆ G then ((hittingTriangles G (required a)).card : ℝ) else 0
  have ha (a : α) : |loss a - (b : ℝ) * D * intact (required a) G| ≤
      ((b : ℝ) * δ + (b : ℝ) ^ 2) * intact (required a) G := by
    by_cases hpres : required a ⊆ G
    · have hh := hittingTriangles_degree_error G (required a) D δ
        (fun e he => hdeg e (hpres he))
      simpa only [loss, hpres, ite_eq_left, intact, hsize, mul_one] using hh
    · simp [loss, intact, hpres]
  have hs : |∑ a, (loss a - (b : ℝ) * D * intact (required a) G)| ≤
      ((b : ℝ) * δ + (b : ℝ) ^ 2) * copyCount required G := by
    calc
      _ ≤ ∑ a, |loss a - (b : ℝ) * D * intact (required a) G| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ((b : ℝ) * δ + (b : ℝ) ^ 2) * intact (required a) G :=
        Finset.sum_le_sum fun a _ => ha a
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have hq : (0 : ℝ) < (triangles G).card := by exact_mod_cast hG.card_pos
  have hid : pmfMean (step G) (copyCount required) - copyCount required G +
      ((b : ℝ) * D / (triangles G).card) * copyCount required G =
      -(∑ a, (loss a - (b : ℝ) * D * intact (required a) G)) / (triangles G).card := by
    rw [step_mean_copyCount required G hG, Finset.sum_sub_distrib, ← Finset.mul_sum]
    change copyCount required G - (∑ a, loss a) / _ - copyCount required G +
      (_ / _) * copyCount required G = -((∑ a, loss a) - (b : ℝ) * D * copyCount required G) / _
    ring
  rw [hid, abs_div, abs_neg, abs_of_pos hq]
  calc
    _ ≤ (((b : ℝ) * δ + (b : ℝ) ^ 2) * copyCount required G) / (triangles G).card :=
      div_le_div_of_nonneg_right hs hq.le
    _ = _ := by ring

end SharpTerminalLeave
end
end

end OAI
