import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.MarkingTwoScans

namespace OAI

section
namespace SharpLogRamsey.Marking
open scoped BigOperators Classical
open Finset ProjectiveDuality
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma popularJoint_mem {W : State (K:=K) (V:=V)} {l r : ℕ}
    {f : ProjectivePair (K:=K) (V:=V)} (hf : f∈popularJoint W l r) :
    f.1∈popularDomain W l ∧ ranks W f.1=r ∧ f.2∈partnerDomain (W f.1) := by
  obtain ⟨b,hb,hf⟩ := mem_biUnion.mp hf
  split_ifs at hf with hr
  · obtain ⟨a,ha,he⟩ := mem_image.mp hf
    subst f
    exact ⟨hb,hr,ha⟩
  · exact False.elim (notMem_empty _ hf)

lemma popularJoint_rank_pos {W : State (K:=K) (V:=V)} {l r : ℕ}
    (hl : l≤r) (hmax : (level (ranks W) r).card≤(level (ranks W) l).card)
    (h : (popularJoint W l r).Nonempty) : 1≤r := by
  obtain ⟨f,hf⟩ := h
  obtain ⟨hp,hr,_⟩ := popularJoint_mem hf
  have hZ : (level (ranks W) l).Nonempty := by
    apply card_pos.mp
    apply (card_pos.mpr (show (level (ranks W) r).Nonempty from ⟨f.1,by simp [level,hr]⟩)).trans_le hmax
  by_contra hh
  have hr0 : r=0 := by omega
  have hl0 : l=0 := by omega
  subst l
  rw [popular_zero W hZ] at hp
  exact notMem_empty _ hp

lemma popularJoint_first_card (W : State (K:=K) (V:=V)) (l r : ℕ)
    (hl : l≤r) (hmax : (level (ranks W) r).card≤(level (ranks W) l).card) :
    (((popularJoint W l r).image Prod.fst).card:ℝ) ≤ 32*(Nat.card K:ℝ)^r := by
  by_cases he : popularJoint W l r=∅
  · rw [he,image_empty,card_empty,Nat.cast_zero]; positivity
  have hsub : (popularJoint W l r).image Prod.fst ⊆ popularDomain W l := by
    intro b hb
    obtain ⟨f,hf,rfl⟩ := mem_image.mp hb
    exact (popularJoint_mem hf).1
  have hZ : (level (ranks W) l).Nonempty := by
    obtain ⟨f,hf⟩ := nonempty_iff_ne_empty.mpr he
    have hr := (popularJoint_mem hf).2.1
    exact card_pos.mp ((card_pos.mpr ⟨f.1,by simp [level,hr]⟩).trans_le hmax)
  have hc : ((popularDomain W l).card:ℝ) ≤ 32*(Nat.card K:ℝ)^l := by
    cases l with
    | zero => rw [popular_zero W hZ,card_empty,Nat.cast_zero]; norm_num
    | succ l => exact popular_card W l hZ
  exact (show (((popularJoint W l r).image Prod.fst).card:ℝ) ≤ (popularDomain W l).card by
    exact_mod_cast card_le_card hsub).trans (hc.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (show (1:ℝ)≤Nat.card K by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K).le) hl)
      (by norm_num)))

lemma popularJoint_fiber_card {d r : ℕ} (hdim : Module.finrank K V=d+1)
    (W : State (K:=K) (V:=V)) (l : ℕ) (hr : r≤d) (b : Projectivization K V) :
    (((popularJoint W l r).filter (fun f => f.1=b)).card:ℝ) ≤ 2*(Nat.card K:ℝ)^(d-r) := by
  by_cases hb : ranks W b=r
  · have hsub : (popularJoint W l r).filter (fun f => f.1=b) ⊆
        (partnerDomain (W b)).image (Prod.mk b) := by
      intro f hf
      obtain ⟨hf,hfb⟩ := mem_filter.mp hf
      have hm := (popularJoint_mem hf).2.2
      exact mem_image.mpr ⟨f.2,by simpa only [hfb] using hm,by cases f; simp_all⟩
    have hc := card_le_card hsub
    rw [card_image_of_injective _ (by intro a a' h; exact Prod.mk.inj h |>.2)] at hc
    exact (show (((popularJoint W l r).filter (fun f => f.1=b)).card:ℝ) ≤
      (partnerDomain (W b)).card by exact_mod_cast hc).trans (partner_card hdim (W b) hb hr)
  · have he : (popularJoint W l r).filter (fun f => f.1=b)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro f hf
      obtain ⟨hf,hfb⟩ := mem_filter.mp hf
      exact hb (hfb ▸ (popularJoint_mem hf).2.1)
    rw [he,card_empty,Nat.cast_zero]; positivity

lemma cheapPopular_first_card (W : State (K:=K) (V:=V))
    (m : RankMask (K:=K) (V:=V)) (hm : m.2=.popular) :
    (((projectiveCheapDomain W m).image Prod.fst).card:ℝ) ≤ 32*(Nat.card K:ℝ)^m.1.val := by
  unfold projectiveCheapDomain
  split_ifs
  · rw [hm]
    exact popularJoint_first_card W _ _ (levelFromRank_spec W m.1.val).1
      ((levelFromRank_spec W m.1.val).2 _ le_rfl)
  · simp

lemma cheapPopular_fiber_card {d : ℕ} (hdim : Module.finrank K V=d+1)
    (W : State (K:=K) (V:=V)) (m : RankMask (K:=K) (V:=V)) (hm : m.2=.popular)
    (b : Projectivization K V) :
    (((projectiveCheapDomain W m).filter (fun f => f.1=b)).card:ℝ) ≤
      2*(Nat.card K:ℝ)^(d-m.1.val) := by
  unfold projectiveCheapDomain
  split_ifs with hr
  · rw [hm]
    exact popularJoint_fiber_card hdim W _ (by omega) b
  · simp

lemma cheapPopular_rank_pos (W : State (K:=K) (V:=V))
    (m : RankMask (K:=K) (V:=V)) (hm : m.2=.popular)
    (h : (projectiveCheapDomain W m).Nonempty) :
    1 ≤ m.1.val ∧ m.1.val < Module.finrank K V := by
  unfold projectiveCheapDomain at h
  split_ifs at h with hr
  · rw [hm] at h
    exact ⟨popularJoint_rank_pos (levelFromRank_spec W m.1.val).1
      ((levelFromRank_spec W m.1.val).2 _ le_rfl) h,hr⟩
  · exact False.elim (not_nonempty_empty h)

lemma cheapPoor_product {n : ℕ} (hdim : Module.finrank K V=n+3)
    (W : State (K:=K) (V:=V)) (m : RankMask (K:=K) (V:=V)) (hm : m.2=.poor) :
    (((projectiveCheapDomain W m).image Prod.fst).card:ℝ)*
      ((projectiveCheapDomain W m).image Prod.snd).card ≤ 16*(Nat.card K:ℝ)^(n+3) := by
  unfold projectiveCheapDomain
  split_ifs
  · rw [hm]
    have h₁ : (incidentPairs (level (ranks W) m.1.val)
        (poorDomain W (levelFromRank W m.1.val))).image Prod.fst ⊆ level (ranks W) m.1.val := by
      intro b hb
      obtain ⟨f,hf,rfl⟩ := mem_image.mp hb
      exact (mem_product.mp (mem_filter.mp hf).1).1
    have h₂ : (incidentPairs (level (ranks W) m.1.val)
        (poorDomain W (levelFromRank W m.1.val))).image Prod.snd ⊆
        poorDomain W (levelFromRank W m.1.val) := by
      intro a ha
      obtain ⟨f,hf,rfl⟩ := mem_image.mp ha
      exact (mem_product.mp (mem_filter.mp hf).1).2
    have h₁' : (((incidentPairs (level (ranks W) m.1.val)
        (poorDomain W (levelFromRank W m.1.val))).image Prod.fst).card:ℝ) ≤
        (level (ranks W) (levelFromRank W m.1.val)).card := by
      exact_mod_cast (card_le_card h₁).trans ((levelFromRank_spec W m.1.val).2 _ le_rfl)
    have h₂' : (((incidentPairs (level (ranks W) m.1.val)
        (poorDomain W (levelFromRank W m.1.val))).image Prod.snd).card:ℝ) ≤
        (poorDomain W (levelFromRank W m.1.val)).card := by exact_mod_cast card_le_card h₂
    exact (mul_le_mul h₁' h₂' (by positivity) (by positivity)).trans (poor_marginal_product hdim W _)
  · simp

end
end SharpLogRamsey.Marking

end

end OAI
