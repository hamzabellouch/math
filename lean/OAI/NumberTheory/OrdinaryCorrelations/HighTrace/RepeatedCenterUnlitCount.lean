import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceListSlotBudget
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FixedDisconnected

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical Filter
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

def repeatedCenterUnlitCount (w : ClosedLine h ℓ) (a : S.FixedResidues w) : ℕ :=
  ∑ p : S.Index, if S.IsCore p then 0 else fixedUnlitCount w a p

lemma totalUnlit_eq_center (w : ClosedLine h ℓ) (a : S.FixedResidues w)
    (hcore : ∀ p : S.FixedIndex w, S.IsCore p.val → ∀ i,
      (p.val:ℕ) ∣ w.label i → a p + (w.offset i.castSucc : ZMod (p.val:ℕ)) = 0) :
    totalUnlitCount w a = repeatedCenterUnlitCount w a := by
  apply sum_congr rfl
  intro p hp
  by_cases hc : S.IsCore p
  · rw [ite_eq_left hc]
    unfold fixedUnlitCount
    split_ifs with hf
    · apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact (mem_filter.mp hi).2.2 (hcore ⟨p,hf⟩ hc i (mem_filter.mp hi).2.1)
    · rfl
  · rw [ite_eq_right hc]

structure RetainedCountConditions (w : ClosedLine h ℓ) (hh : 0 < h)
    (a : S.FixedResidues w) (B K₀ : ℝ) : Prop where
  core_lit : ∀ p : S.FixedIndex w, S.IsCore p.val → ∀ i,
    (p.val:ℕ) ∣ w.label i → a p + (w.offset i.castSucc : ZMod (p.val:ℕ)) = 0
  unlit_center : repeatedCenterUnlitCount w a < listCutoff B
  components : ∀ p : S.FixedIndex w, (treeOccurrences w p.val).Nonempty →
    ((activeComponents w hh p.val (a p)).card:ℝ) ≤ K₀*B^rho
  disconnected : (disconnectedCount w hh a:ℝ) < B^(1-2*rho)
  corrupted : (corruptedCount S w:ℝ) < B^(1-2*rho)

lemma source_list_slots_power (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
      (sourceListSlotBudget C₀ B:ℝ) ≤ 4*B^(1-rho+4*epsilon+rho/8) := by
  filter_upwards [eventually_log_ceil_le C₀ (rho/8) hC₀ (by norm_num [rho]),
    eventually_ge_atTop (1:ℝ)] with B hJ hB
  have hb : 0 < B := zero_lt_one.trans_le hB
  have ht : (listCutoff B:ℝ) ≤ 2*B^(4*epsilon) :=
    ceil_rpow_le_two B (4*epsilon) hB (by norm_num [epsilon])
  have hL : (pathLength B:ℝ) ≤ B^(1-rho) := Nat.floor_le (Real.rpow_nonneg hb.le _)
  have hP : (pathLength B:ℝ)*(⌈C₀*Real.log B⌉₊:ℝ) ≤ B^(1-rho+rho/8) := by
    calc
      _ ≤ B^(1-rho)*B^(rho/8) := mul_le_mul hL hJ (Nat.cast_nonneg _) (Real.rpow_nonneg hb.le _)
      _ = _ := (Real.rpow_add hb _ _).symm
  have hp1 : 1 ≤ B^(1-rho+rho/8) := Real.one_le_rpow hB (by norm_num [rho])
  change ((listCutoff B * (pathLength B * ⌈C₀*Real.log B⌉₊+1):ℕ):ℝ) ≤ _
  push_cast
  calc
    _ ≤ (2*B^(4*epsilon))*(2*B^(1-rho+rho/8)) :=
      mul_le_mul ht (by linarith) (by positivity) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm,← Real.rpow_add hb]
      congr 1 <;> ring_nf

lemma source_retained_budget (C₀ K₀ : ℝ) (hC₀ : 0 ≤ C₀) (hK₀ : 0 ≤ K₀) :
    ∀ᶠ B : ℝ in atTop,
      B^(1-2*rho)*(⌈K₀*B^rho⌉₊:ℝ) + 2*(listCutoff B:ℝ) +
        B^(1-2*rho) + 2*(sourceListSlotBudget C₀ B:ℝ) ≤ B^(1-rho/2) := by
  let a := 1-rho+4*epsilon+rho/8
  have hab : a < 1-rho/2 := by norm_num [a,epsilon,rho]
  filter_upwards [source_list_slots_power C₀ hC₀,
    eventually_const_mul_rpow_le a (1-rho/2) (K₀+14) hab,
    eventually_ge_atTop (1:ℝ)] with B hM hlarge hB
  have hb : 0 < B := zero_lt_one.trans_le hB
  have hr : 1 ≤ B^rho := Real.one_le_rpow hB (by norm_num [rho])
  have hceil : (⌈K₀*B^rho⌉₊:ℝ) ≤ (K₀+1)*B^rho := by
    have hh := Nat.ceil_lt_add_one (mul_nonneg hK₀ (Real.rpow_nonneg hb.le rho))
    nlinarith
  have hp : B^(1-2*rho)*(⌈K₀*B^rho⌉₊:ℝ) ≤ (K₀+1)*B^a := by
    calc
      _ ≤ B^(1-2*rho)*((K₀+1)*B^rho) :=
        mul_le_mul_of_nonneg_left hceil (Real.rpow_nonneg hb.le _)
      _ = (K₀+1)*B^(1-rho) := by
        rw [mul_left_comm,← Real.rpow_add hb]
        congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hB (by norm_num [a,epsilon,rho])) (by linarith)
  have ht : (listCutoff B:ℝ) ≤ 2*B^a :=
    (ceil_rpow_le_two B (4*epsilon) hB (by norm_num [epsilon])).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hB
        (by norm_num [a,epsilon,rho])) (by norm_num))
  have hd : B^(1-2*rho) ≤ B^a := Real.rpow_le_rpow_of_exponent_le hB (by norm_num [a,epsilon,rho])
  change (sourceListSlotBudget C₀ B:ℝ) ≤ 4*B^a at hM
  nlinarith

theorem source_retained_token_count (C₀ K₀ τ : ℝ) (hC₀ : 0 ≤ C₀) (hK₀ : 0 ≤ K₀) :
    ∀ᶠ B : ℝ in atTop, ∀ (S : PrimeSystem) (D : S.DivisorFamily B τ C₀)
      (h ℓ : ℕ) (w : ClosedLine h ℓ) (hh : 0 < h)
      (𝔏 : List (AttachedSpec w D (pathLength B))) (a : S.FixedResidues w),
      𝔏.length ≤ listCutoff B → RetainedCountConditions w hh a B K₀ →
      (Fintype.card (TaggedSlot w hh 𝔏 a)+Fintype.card (ListPrimeSlot w 𝔏):ℝ) ≤ B^(1-rho/2) := by
  filter_upwards [source_retained_budget C₀ K₀ hC₀ hK₀,
    eventually_ge_atTop (1:ℝ)] with B hbound hB
  intro S D h ℓ w hh 𝔏 a hlen hg
  let K := ⌈K₀*B^rho⌉₊
  have hK : ∀ p : S.FixedIndex w, (treeOccurrences w p.val).Nonempty →
      (activeComponents w hh p.val (a p)).card ≤ K := by
    intro p hp
    exact_mod_cast (hg.components p hp).trans (Nat.le_ceil _)
  have hU : totalUnlitCount w a ≤ listCutoff B :=
    (totalUnlit_eq_center w a hg.core_lit).symm ▸ hg.unlit_center.le
  have hM : Fintype.card (ListPrimeSlot w 𝔏) ≤ sourceListSlotBudget C₀ B :=
    (listPrimeSlot_card w 𝔏).trans (Nat.mul_le_mul_right _ hlen)
  have ht := retained_tag_count w hh 𝔏 a K hK
  have ht' : (Fintype.card (TaggedSlot w hh 𝔏 a):ℝ) ≤
      (disconnectedCount w hh a:ℝ)*(K:ℝ)+2*(totalUnlitCount w a:ℝ)+
        (corruptedCount S w:ℝ)+(Fintype.card (ListPrimeSlot w 𝔏):ℝ) := by exact_mod_cast ht
  have hd := mul_le_mul_of_nonneg_right hg.disconnected.le (Nat.cast_nonneg K : (0:ℝ)≤K)
  have hu : (totalUnlitCount w a:ℝ) ≤ (listCutoff B:ℝ) := by exact_mod_cast hU
  have hm : (Fintype.card (ListPrimeSlot w 𝔏):ℝ) ≤ (sourceListSlotBudget C₀ B:ℝ) := by exact_mod_cast hM
  dsimp only [K] at ht' hd
  nlinarith [hg.corrupted.le]

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
