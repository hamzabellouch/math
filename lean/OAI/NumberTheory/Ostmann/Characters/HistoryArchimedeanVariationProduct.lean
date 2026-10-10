import OAI.NumberTheory.Ostmann.Characters.HistoryArchimedeanVariationProfiles

namespace OAI

noncomputable section
namespace Ostmann.Characters
open scoped BigOperators SchwartzMap

inductive HistoryProfile
  | leaf (conjugated : Bool) (frequency : ℝ)
  | ratio

def HistoryProfile.eval (ρ : 𝓢(ℝ,ℂ)) : HistoryProfile → ℝ → ℂ
  | .leaf b v => historyLeafProfile ρ b v
  | .ratio => historyRatioProfile

def HistoryProfile.bound (ρ : 𝓢(ℝ,ℂ)) : HistoryProfile → ℝ → ℝ
  | .leaf _ _ => fun B => Real.exp (B/2)*Ostmann.Arithmetic.leafProfileBound ρ
  | .ratio => Real.exp

theorem HistoryProfile.bound_pos (ρ : 𝓢(ℝ,ℂ)) (p : HistoryProfile) (B : ℝ) :
    0 < p.bound ρ B := by
  cases p
  · exact mul_pos (Real.exp_pos _) (Ostmann.Arithmetic.leafProfileBound_pos ρ)
  · exact Real.exp_pos _

theorem HistoryProfile.norm_eval_le (ρ : 𝓢(ℝ,ℂ)) (p : HistoryProfile)
    {z B : ℝ} (hz : z ≤ B) : ‖p.eval ρ z‖ ≤ p.bound ρ B := by
  cases p with
  | leaf b v => exact historyLeafProfile_norm_le ρ b v hz
  | ratio => exact historyRatioProfile_norm_le hz

theorem HistoryProfile.eval_lipschitz (ρ : 𝓢(ℝ,ℂ)) (p : HistoryProfile)
    {A B x y : ℝ} (hx : x ∈ Set.Icc A B) (hy : y ∈ Set.Icc A B) :
    ‖p.eval ρ y-p.eval ρ x‖ ≤ p.bound ρ B*|y-x| := by
  cases p with
  | leaf b v => exact historyLeafProfile_lipschitz ρ b v hx hy
  | ratio => exact historyRatioProfile_lipschitz hx hy

theorem norm_finset_product_sub_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f g : ι → ℂ) (d : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ M) (hg : ∀ i ∈ S, ‖g i‖ ≤ M)
    (hd : ∀ i ∈ S, 0 ≤ d i) (hfg : ∀ i ∈ S, ‖f i-g i‖ ≤ M*d i) :
    ‖(∏ i ∈ S, f i)-(∏ i ∈ S, g i)‖ ≤ M^S.card*(∑ i ∈ S, d i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hSf : ∀ i ∈ S, ‖f i‖ ≤ M := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hSg : ∀ i ∈ S, ‖g i‖ ≤ M := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hSd : ∀ i ∈ S, 0 ≤ d i := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hSp : ∀ i ∈ S, ‖f i-g i‖ ≤ M*d i := fun i hi => hfg i (Finset.mem_insert_of_mem hi)
    have hrest := ih hSf hSg hSd hSp
    have hprod : ‖∏ i ∈ S, g i‖ ≤ M^S.card := by
      rw [norm_prod]
      simpa only [Finset.prod_const] using
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg (g i)) hSg
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.card_insert_of_notMem ha,Finset.sum_insert ha]
    calc
      _ = ‖f a*((∏ i ∈ S, f i)-(∏ i ∈ S, g i))+(f a-g a)*(∏ i ∈ S, g i)‖ := by congr 1; ring
      _ ≤ ‖f a*((∏ i ∈ S, f i)-(∏ i ∈ S, g i))‖+‖(f a-g a)*(∏ i ∈ S, g i)‖ := norm_add_le _ _
      _ = ‖f a‖*‖(∏ i ∈ S, f i)-(∏ i ∈ S, g i)‖+‖f a-g a‖*‖∏ i ∈ S, g i‖ := by rw [norm_mul,norm_mul]
      _ ≤ M*(M^S.card*(∑ i ∈ S, d i))+(M*d a)*M^S.card := by
        apply add_le_add
        · exact mul_le_mul (hf a (Finset.mem_insert_self _ _)) hrest (norm_nonneg _) hM
        · exact mul_le_mul (hfg a (Finset.mem_insert_self _ _)) hprod (norm_nonneg _)
            (mul_nonneg hM (hd a (Finset.mem_insert_self _ _)))
      _ = _ := by rw [pow_succ]; ring

def historyArchimedeanProduct {ι : Type*} [Fintype ι] (ρ : 𝓢(ℝ,ℂ))
    (profile : ι → HistoryProfile) (z : ι → ℝ) : ℂ :=
  ∏ i, (profile i).eval ρ (z i)

theorem historyArchimedeanProduct_norm_le {ι : Type*} [Fintype ι]
    (ρ : 𝓢(ℝ,ℂ)) (profile : ι → HistoryProfile) (z B : ι → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, z i ≤ B i)
    (hbound : ∀ i, (profile i).bound ρ (B i) ≤ M) :
    ‖historyArchimedeanProduct ρ profile z‖ ≤ M^(Fintype.card ι) := by
  classical
  unfold historyArchimedeanProduct
  rw [norm_prod]
  have hh : (∏ i : ι, ‖(profile i).eval ρ (z i)‖) ≤ ∏ _i : ι, |M| :=
    Finset.prod_le_prod₀ (fun i _ => norm_nonneg ((profile i).eval ρ (z i)))
      (fun i _ => ((profile i).norm_eval_le ρ (hz i)).trans ((hbound i).trans (le_abs_self M)))
  simpa only [Finset.prod_const,Finset.card_univ,abs_of_nonneg hM] using hh

theorem historyArchimedeanProduct_difference_le {ι : Type*} [Fintype ι]
    (ρ : 𝓢(ℝ,ℂ)) (profile : ι → HistoryProfile) (x y A B : ι → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hx : ∀ i, x i ∈ Set.Icc (A i) (B i))
    (hy : ∀ i, y i ∈ Set.Icc (A i) (B i))
    (hbound : ∀ i, (profile i).bound ρ (B i) ≤ M) :
    ‖historyArchimedeanProduct ρ profile y-historyArchimedeanProduct ρ profile x‖ ≤
      M^(Fintype.card ι)*(∑ i, |y i-x i|) := by
  classical
  apply norm_finset_product_sub_le Finset.univ
    (fun i => (profile i).eval ρ (y i)) (fun i => (profile i).eval ρ (x i))
    (fun i => |y i-x i|) hM
  · exact fun i _ => ((profile i).norm_eval_le ρ (hy i).2).trans (hbound i)
  · exact fun i _ => ((profile i).norm_eval_le ρ (hx i).2).trans (hbound i)
  · exact fun i _ => abs_nonneg _
  · intro i hi
    exact ((profile i).eval_lipschitz ρ (hx i) (hy i)).trans
      (mul_le_mul_of_nonneg_right (hbound i) (abs_nonneg _))

end Ostmann.Characters

end

end OAI
