import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.LevelLosses

namespace OAI

section
namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {Ω α Γ ι : Type*} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype ι]

lemma entropy_cond_tuple_domains (p : Law Ω) (C : Ω → Γ) (F : Ω → ι → α)
    (S : Γ → ι → Finset α)
    (hS : ∀ x, p.mass x ≠ 0 → ∀ i, F x i ∈ S (C x) i)
    (c : Γ) (hc : (p.map C).mass c ≠ 0) :
    entropy ((p.cond C c).map F) ≤ ∑ i, Real.log (S c i).card := by
  apply (entropy_subadditive_pi _).trans
  apply sum_le_sum
  intro i hi
  change entropy (((p.cond C c).map F).map (fun x => x i)) ≤ _
  rw [Law.map_map]
  apply entropy_mapped_support
  intro x hx
  obtain ⟨hp,he⟩ := p.cond_support C c hc x hx
  simpa only [Function.comp_apply,he] using hS x hp i

lemma entropy_context_bound (p : Law Ω) (C : Ω → Γ) (F : Ω → α) (J : Γ → ℝ)
    (hJ : ∀ c, (p.map C).mass c ≠ 0 → entropy ((p.cond C c).map F) ≤ J c) :
    entropy (p.map F) ≤ entropy (p.map C)+∑ c, (p.map C).mass c*J c := by
  have hf : (p.map (fun x => (F x,C x))).fst = p.map F := by
    rw [← Law.map_fst,Law.map_map]
    rfl
  have hh := entropy_map_le (p.map (fun x => (F x,C x))) Prod.fst
  rw [Law.map_fst,hf,entropy_cond_chain p C F] at hh
  apply hh.trans
  apply add_le_add le_rfl
  apply sum_le_sum
  intro a ha
  by_cases hc : (p.map C).mass a = 0
  · simp [hc]
  · exact mul_le_mul_of_nonneg_left (hJ a hc) ((p.map C).nonneg a)

lemma entropy_adjoin_mask {M : Type*} [Fintype M] (p : Law Ω)
    (C : Ω → Γ) (mask : Ω → M) :
    entropy (p.map (fun x => (C x,mask x))) ≤
      entropy (p.map C)+Real.log (Fintype.card M) := by
  have hf : (p.map (fun x => (C x,mask x))).fst = p.map C := by
    rw [← Law.map_fst,Law.map_map]; rfl
  have hs : (p.map (fun x => (C x,mask x))).snd = p.map mask := by
    rw [← Law.map_snd,Law.map_map]; rfl
  have hm := entropy_le_log_card (p.map mask) univ (by simp)
  have ht := entropy_subadditive (p.map (fun x => (C x,mask x)))
  rw [hf,hs] at ht
  exact ht.trans (add_le_add le_rfl (by simpa only [card_univ] using hm))

def maskedValues (E : Finset ι) (f : ι → α) : ι → Option α :=
  fun i => if i ∈ E then some (f i) else none

def maskedDomains (E : Finset ι) (D : ι → Finset α) (i : ι) : Finset (Option α) :=
  if i ∈ E then (D i).image some else {none}

omit [Fintype α] [Fintype ι] in
lemma maskedValues_mem (E : Finset ι) (f : ι → α) (D : ι → Finset α)
    (hD : ∀ i, f i ∈ D i) (i : ι) : maskedValues E f i ∈ maskedDomains E D i := by
  by_cases hi : i ∈ E
  · simp only [maskedValues,maskedDomains,ite_eq_left hi]
    exact mem_image.mpr ⟨f i,hD i,rfl⟩
  · simp [maskedValues,maskedDomains,hi]

omit [Fintype α] [Fintype ι] in
lemma maskedDomains_log_card (E : Finset ι) (D : ι → Finset α) (i : ι) :
    Real.log (maskedDomains E D i).card = if i ∈ E then Real.log (D i).card else 0 := by
  by_cases hi : i ∈ E
  · simp [maskedDomains,hi,card_image_of_injective (D i) (Option.some_injective α)]
  · simp [maskedDomains,hi]

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {Ω α Γ M ι : Type*} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype M] [Fintype ι]

def markingMessage (C : Ω → Γ) (mask : Ω → M) (E : M → Finset ι) (F : Ω → ι → α)
    (x : Ω) : (ι → Option α) × (Γ × M) :=
  (maskedValues (E (mask x)) (F x),(C x,mask x))

theorem marking_message_entropy (p : Law Ω) (C : Ω → Γ) (mask : Ω → M)
    (E : M → Finset ι) (F : Ω → ι → α) (D : Γ → ι → Finset α) (J : ℝ)
    (hD : ∀ x, p.mass x ≠ 0 → ∀ i, F x i ∈ D (C x) i)
    (hJ : ∀ c i, Real.log (D c i).card ≤ J) :
    entropy (p.map (markingMessage C mask E F)) ≤ entropy (p.map C)+
      Real.log (Fintype.card M)+(∑ x, p.mass x*((E (mask x)).card:ℝ))*J := by
  let G := fun x => (C x,mask x)
  let T := fun x => maskedValues (E (mask x)) (F x)
  have hG := entropy_adjoin_mask p C mask
  have hcond (c : Γ × M) (hc : (p.map G).mass c ≠ 0) :
      entropy ((p.cond G c).map T) ≤ (E c.2).card*J := by
    let S := fun c : Γ × M => maskedDomains (E c.2) (D c.1)
    have hh := entropy_cond_tuple_domains p G T S (fun x hx i =>
      maskedValues_mem _ _ _ (hD x hx) i) c hc
    apply hh.trans
    simp only [S,maskedDomains_log_card]
    calc
      _ ≤ ∑ i, if i ∈ E c.2 then J else 0 := by
        apply sum_le_sum
        intro i hi
        split_ifs
        · exact hJ c.1 i
        · exact le_rfl
      _ = _ := by simp
  have hsum : ∑ c, (p.map G).mass c*((E c.2).card:ℝ)*J =
      (∑ x, p.mass x*((E (mask x)).card:ℝ))*J := by
    rw [← sum_mul, p.sum_map G (fun c => ((E c.2).card:ℝ))]
  change entropy (p.map (fun x => (T x,G x))) ≤ _
  rw [entropy_cond_chain p G T]
  calc
    _ ≤ (entropy (p.map C)+Real.log (Fintype.card M))+
        ∑ c, (p.map G).mass c*((E c.2).card*J) := by
      apply add_le_add hG
      apply sum_le_sum
      intro c hc
      by_cases hn : (p.map G).mass c = 0
      · simp [hn]
      · exact mul_le_mul_of_nonneg_left (hcond c hn) ((p.map G).nonneg c)
    _ = _ := by simp_rw [← mul_assoc]; rw [hsum]

def markingDecodedDomains (E : M → Finset ι)
    (cheap : ((ι → Option α) × (Γ × M)) → ι → Finset α)
    (θ : (ι → Option α) × (Γ × M)) (i : ι) : Finset α :=
  if i ∈ E θ.2.2 then (θ.1 i).toFinset else cheap θ i

omit [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype M] [Fintype ι] in
lemma markingDecodedDomains_mem (C : Ω → Γ) (mask : Ω → M)
    (E : M → Finset ι) (F : Ω → ι → α)
    (cheap : ((ι → Option α) × (Γ × M)) → ι → Finset α)
    (x : Ω)
    (hcheap : ∀ i, i ∉ E (mask x) → F x i ∈ cheap (markingMessage C mask E F x) i)
    (i : ι) : F x i ∈ markingDecodedDomains E cheap (markingMessage C mask E F x) i := by
  by_cases hi : i ∈ E (mask x)
  · simp [markingDecodedDomains,markingMessage,maskedValues,hi]
  · change F x i ∈ if i ∈ E (mask x) then _ else _
    rw [ite_eq_right hi]
    exact hcheap i hi

omit [Fintype α] [Fintype Γ] [Fintype M] in
lemma markingDecodedDomains_entropy (E : M → Finset ι)
    (cheap : ((ι → Option α) × (Γ × M)) → ι → Finset α) (J : ℝ)
    (hJ : ∀ θ i, i ∉ E θ.2.2 → Real.log (cheap θ i).card ≤ J)
    (θ : (ι → Option α) × (Γ × M)) :
    (∑ i, Real.log (markingDecodedDomains E cheap θ i).card) ≤
      ((Fintype.card ι:ℝ)-(E θ.2.2).card)*J := by
  have h (i : ι) : Real.log (markingDecodedDomains E cheap θ i).card ≤
      if i ∈ E θ.2.2 then 0 else J := by
    by_cases hi : i ∈ E θ.2.2
    · simp only [markingDecodedDomains,ite_eq_left hi]
      cases θ.1 i <;> simp
    · simpa only [markingDecodedDomains,ite_eq_right hi] using hJ θ i hi
  have he : (∑ i, if i ∈ E θ.2.2 then (0:ℝ) else J) =
      ((Fintype.card ι:ℝ)-(E θ.2.2).card)*J := by
    rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
    have hcard : (univ.filter (fun i => i ∉ E θ.2.2)).card = Fintype.card ι-(E θ.2.2).card := by
      rw [← sdiff_eq_filter,card_sdiff_of_subset (subset_univ _),card_univ]
    rw [hcard,Nat.cast_sub (card_le_univ _)]
  exact (sum_le_sum (fun i _ => h i)).trans_eq he

theorem marking_entropy_upper (p : Law Ω) (C : Ω → Γ) (mask : Ω → M)
    (E : M → Finset ι) (F : Ω → ι → α) (D : Γ → ι → Finset α)
    (cheap : ((ι → Option α) × (Γ × M)) → ι → Finset α) (Jprev J₀ : ℝ)
    (hD : ∀ x, p.mass x ≠ 0 → ∀ i, F x i ∈ D (C x) i)
    (hprev : ∀ c i, Real.log (D c i).card ≤ Jprev)
    (hc : ∀ x, p.mass x ≠ 0 → ∀ i, i ∉ E (mask x) →
      F x i ∈ cheap (markingMessage C mask E F x) i)
    (hcheap : ∀ θ i, i ∉ E θ.2.2 → Real.log (cheap θ i).card ≤ J₀) :
    entropy (p.map F) ≤ entropy (p.map C)+Real.log (Fintype.card M)+
      Fintype.card ι*J₀+(∑ x, p.mass x*((E (mask x)).card:ℝ))*(Jprev-J₀) := by
  let θ := markingMessage C mask E F
  have hu := entropy_context_bound p θ F
    (fun z => ((Fintype.card ι:ℝ)-(E z.2.2).card)*J₀) (fun z hz =>
      (entropy_cond_tuple_domains p θ F (markingDecodedDomains E cheap)
        (fun x hx i => markingDecodedDomains_mem C mask E F cheap x (hc x hx) i) z hz).trans
          (markingDecodedDomains_entropy E cheap J₀ hcheap z))
  have hm := marking_message_entropy p C mask E F D Jprev hD hprev
  have he : (∑ z, (p.map θ).mass z * (((Fintype.card ι:ℝ)-(E z.2.2).card)*J₀)) =
      ((Fintype.card ι:ℝ)-∑ x, p.mass x*((E (mask x)).card:ℝ))*J₀ := by
    rw [p.sum_map θ]
    change (∑ x, p.mass x * (((Fintype.card ι:ℝ)-(E (mask x)).card)*J₀)) = _
    simp_rw [← mul_assoc,mul_sub]
    rw [← sum_mul,sum_sub_distrib,← sum_mul,p.total,one_mul]
  rw [he] at hu
  dsimp only [θ] at hu
  linarith

end
end SharpLogRamsey.Selection

end

end OAI
