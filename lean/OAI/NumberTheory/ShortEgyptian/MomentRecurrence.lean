import OAI.NumberTheory.ShortEgyptian.DescentSets

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter

@[irreducible] def momentDimension : ℕ := 2*dimC+dimM+1
@[irreducible] def descentR : ℕ := 49009440000
noncomputable def descentAlpha : ℝ := 1-1/(descentR:ℝ)

lemma descentR_ge_two : 2 ≤ descentR := by norm_num [descentR]
lemma descentR_eq : descentR=24*dimX*10000 := by norm_num [descentR,dimX,dimM]
lemma descentAlpha_bounds : 0 < descentAlpha ∧ descentAlpha < 1 := by
  have hr : (2:ℝ) ≤ descentR := by exact_mod_cast descentR_ge_two
  have hi : 0 < 1/(descentR:ℝ) := by positivity
  have hi' : 1/(descentR:ℝ) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  dsimp [descentAlpha]
  constructor <;> linarith

def MomentScale (S : ℝ) : Prop := ∀ (v Y : ℝ) (N : ℕ),
  S/(2*Real.log S) ≤ v → v ≤ (momentDimension:ℝ)*S →
  Real.exp (v/2) ≤ Y → Y ≤ Real.exp v → (N:ℝ) ≤ Real.exp ((momentDimension:ℝ)*S) →
  ∑ n ∈ Ioc N (N+⌊Y⌋₊), (truncatedDivisorCount (Real.exp v) n:ℝ)^descentR ≤ Y*Real.exp (S^(1/4:ℝ))

lemma eventually_MomentScale : ∀ᶠ S : ℝ in atTop, MomentScale S :=
  uniform_divisor_moment _ (by norm_num [momentDimension,dimC,dimX,dimM]) descentR

lemma level_moment (S : ℝ) (h : ListScale S) (hm : MomentScale S) (C : ℕ) (R : ResidueSystem S C)
    (hC : 0 < C) (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S)) (j : ℕ) (hj : j < depth S)
    (i : Fin (scaleM S) → Bool) :
    ∑ n ∈ Ioc (levelMultiplier S C j*R.t j i) (levelMultiplier S C j*R.t j i+⌊level S (j+1)⌋₊),
      (truncatedDivisorCount (level S j) n:ℝ)^descentR ≤ level S (j+1)*Real.exp (S^(1/4:ℝ)) := by
  let v := (dimX:ℝ)*S-(1/10000:ℝ)*scaleM S*j
  have hv : (scaleM S:ℝ) < v := Real.exp_lt_exp.mp ((level_before_depth S h.m_pos j).mp hj)
  have hvup : v ≤ (dimX:ℝ)*S := by
    dsimp [v]
    exact sub_le_self _ (by positivity)
  have hD : (dimX:ℝ) ≤ momentDimension := by norm_num [momentDimension,dimC,dimX,dimM]
  have hYlo : Real.exp (v/2) ≤ level S (j+1) := by
    apply Real.exp_le_exp.mpr
    simp only [Nat.cast_add,Nat.cast_one]
    dsimp [v] at hv ⊢
    nlinarith [show (0:ℝ) ≤ scaleM S by positivity]
  have hMpos : 0 < R.M := by exact_mod_cast (Real.exp_pos S).trans R.M_lower
  have htt : (R.t j i:ℝ) ≤ R.M := by exact_mod_cast Nat.le_of_dvd hMpos (R.t_dvd j i)
  have hcj : (levelMultiplier S C j:ℝ) ≤ C := by
    unfold levelMultiplier
    split
    · exact le_rfl
    · exact_mod_cast hC
  have hn : ((levelMultiplier S C j*R.t j i:ℕ):ℝ) ≤ Real.exp ((momentDimension:ℝ)*S) := by
    push_cast
    calc
      _ ≤ (C:ℝ)*R.M := mul_le_mul hcj htt (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ ≤ Real.exp (2*(dimC:ℝ)*S)*Real.exp ((dimM:ℝ)*S) := mul_le_mul hChi R.M_upper (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((2*(dimC:ℝ)+dimM)*S) := by rw [←Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ h.S_pos.le
        norm_num [momentDimension,dimC,dimX,dimM]
  exact hm v (level S (j+1)) _ (h.m_bounds.1.trans hv.le)
    (hvup.trans (mul_le_mul_of_nonneg_right hD h.S_pos.le)) hYlo
    (level_antitone S (by omega)) hn

lemma shifted_subset_sum (H : Finset ℕ) (N : ℕ) (Y : ℝ) (f : ℕ → ℝ)
    (hH : ∀ u ∈ H, 0 < u ∧ (u:ℝ) ≤ Y) (hf : ∀ n, 0 ≤ f n) :
    ∑ u ∈ H, f (N+u) ≤ ∑ n ∈ Ioc N (N+⌊Y⌋₊), f n := by
  have hinj : Set.InjOn (N+·) (H: Set ℕ) := by intro a _ b _ hh; exact Nat.add_left_cancel hh
  rw [←sum_image hinj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hn
    have hh := hH u hu
    exact mem_Ioc.mpr ⟨by omega,Nat.add_le_add_left (Nat.le_floor hh.2) N⟩
  · exact fun n _ _ => hf n

noncomputable def levelDensity (S : ℝ) (M C j : ℕ) : ℝ :=
  (levelBad S M C (terminalLength S) j).card/level S j

lemma levelDensity_bounds (S : ℝ) (M C j : ℕ) :
    0 ≤ levelDensity S M C j ∧ levelDensity S M C j ≤ 1 := by
  refine ⟨div_nonneg (Nat.cast_nonneg _) (level_pos S j).le,?_⟩
  exact (div_le_one (level_pos S j)).mpr (levelBad_card_le S M C _ j)

lemma levelDensity_last (S : ℝ) (h : ListScale S) (C : ℕ) (R : ResidueSystem S C) :
    levelDensity S R.M C (depth S) = 0 := by
  simp only [levelDensity,levelBad_terminal S h C R,card_empty,Nat.cast_zero,zero_div]

lemma level_holder (S : ℝ) (h : ListScale S) (hm : MomentScale S) (C : ℕ) (R : ResidueSystem S C)
    (hC : 0 < C) (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S)) (j : ℕ) (hj : j < depth S)
    (i : Fin (scaleM S) → Bool) :
    ∑ u ∈ levelBad S R.M C (terminalLength S) (j+1),
      (truncatedDivisorCount (level S j) (levelMultiplier S C j*R.t j i+u):ℝ) ≤
      level S (j+1)*Real.exp (S^(1/4:ℝ)/(descentR:ℝ))*(levelDensity S R.M C (j+1))^descentAlpha := by
  apply holder_density _ _ descentR descentR_ge_two (by intros; positivity) _ _ (level_pos S (j+1))
  apply (shifted_subset_sum _ _ _ _ ?_ (by intros; positivity)).trans
    (level_moment S h hm C R hC hChi j hj i)
  intro u hu
  exact ((mem_levelBad S R.M C _ (j+1) u).mp hu).imp_right And.left

lemma density_precise_recurrence (S : ℝ) (h : ListScale S) (hm : MomentScale S) (C : ℕ) (R : ResidueSystem S C)
    (hClo : Real.exp ((dimC:ℝ)*S) ≤ C) (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S))
    (j : ℕ) (hj : j < depth S) :
    levelDensity S R.M C j ≤ Real.exp (-(1/1000:ℝ)*scaleM S)+
      scaleRho S*levelDensity S R.M C (j+1)+
      2*Real.exp (S^(1/4:ℝ)/(descentR:ℝ))*(levelDensity S R.M C (j+1))^descentAlpha := by
  have hC : 0 < C := by exact_mod_cast (Real.exp_pos _).trans_le hClo
  have hM : 0 < R.M := by exact_mod_cast (Real.exp_pos S).trans R.M_lower
  let H := levelBad S R.M C (terminalLength S) j
  let K := levelBad S R.M C (terminalLength S) (j+1)
  let N := fun i => levelMultiplier S C j*R.t j i
  have hH (u : ℕ) (hu : u ∈ H) : 0 < u ∧ (u:ℝ) ≤ level S j := by
    exact ((mem_levelBad S R.M C _ j u).mp hu).imp_right And.left
  have hI : 0 < (Fintype.card (Fin (scaleM S) → Bool):ℝ) := by exact_mod_cast Fintype.card_pos
  have hpair := residue_double_count H K (R.bad j) N
    (fun i => Nat.mul_pos (levelMultiplier_pos S C j hC) (R.t_pos j i)) _ _ _ (scaleRho_pos S) hH
    (fun u hu hy => levelBad_inherit S C R.M _ j u hM hC hu hy)
    (fun u hu i hy => levelBad_residue S C R.M _ j u (R.t j i) hM hC hj
      (level_fraction_lt S h C R.M j u R.M_lower hClo (hH u hu).2) hu (R.t_pos j i) (R.t_dvd j i) hy)
    (fun u hu hb hy => R.good_residues j hj u (by
      apply mem_Icc.mpr
      refine ⟨?_,Nat.le_floor (hH u hu).2⟩
      apply Nat.succ_le_iff.mpr
      apply (Nat.floor_lt (mul_nonneg (level_pos S j).le (scaleRho_pos S).le)).mpr
      simpa only [level_succ] using hy) hb)
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin (scaleM S) → Bool))) =>
    level_holder S h hm C R hC hChi j hj i)
  simp only [sum_const,card_univ,nsmul_eq_mul] at hsum
  have hcoeff : 0 ≤ 2/(scaleRho S*Fintype.card (Fin (scaleM S) → Bool)) := div_nonneg (by norm_num) (mul_nonneg (scaleRho_pos S).le (Nat.cast_nonneg _))
  have hb := R.bad_card j hj
  have hh := hpair.trans (add_le_add (add_le_add hb (le_refl (K.card:ℝ)))
    (mul_le_mul_of_nonneg_left hsum hcoeff))
  apply (div_le_iff₀ (level_pos S j)).mpr
  change (H.card:ℝ) ≤ _
  apply hh.trans_eq
  dsimp [levelDensity,K,N]
  rw [level_succ]
  field_simp [(scaleRho_pos S).ne',(level_pos S j).ne',hI.ne']

end ShortEgyptian

end OAI
