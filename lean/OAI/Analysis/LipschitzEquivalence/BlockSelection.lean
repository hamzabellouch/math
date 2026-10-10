import OAI.Analysis.LipschitzEquivalence.SmoothRows

namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
variable {H : Type uH} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

theorem half_sum_lipschitz {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {f g : H → ℝ} (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g) :
    LipschitzWith 1 (fun p => (f p+g p)/2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hf' := hf.dist_le_mul p q
  have hg' := hg.dist_le_mul p q
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at *
  have he : (f p+g p)/2-(f q+g q)/2 = ((f p-f q)+(g p-g q))/2 := by ring
  rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have := abs_add_le (f p-f q) (g p-g q)
  linarith

theorem half_sub_lipschitz {f g : H → ℝ} (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g) :
    LipschitzWith 1 (fun p => (f p-g p)/2) := by
  simpa only [sub_eq_add_neg,Pi.neg_apply] using half_sum_lipschitz hf hg.neg

theorem dyadicMean_lipschitz (u : ℕ → Smooth H) (hu : ∀ i, LipschitzWith 1 (u i).val) (n k : ℕ) :
    LipschitzWith 1 (dyadicMean u n k).val := by
  induction n generalizing k with
  | zero => exact hu k
  | succ n ih =>
    convert half_sum_lipschitz (ih k) (ih (k+2^n)) using 1
    ext p
    change (1/2:ℝ)*((dyadicMean u n k).val p+(dyadicMean u n (k+2^n)).val p) = _
    ring

theorem dyadicMean_zero_value {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (u : ℕ → Smooth H) (hu : ∀ i, (u i).val 0 = 0) (n k : ℕ) :
    (dyadicMean u n k).val 0 = 0 := by
  have he := map_dyadicMean (Smooth.eval (0:H)) u n k
  change (dyadicMean u n k).val 0 = dyadicMean (fun i => (u i).val 0) n k at he
  rw [he]
  exact le_antisymm (dyadicMean_le _ _ _ (fun i _ _ => (hu i).le))
    (le_dyadicMean _ _ _ (fun i _ _ => (hu i).ge))

def halfBlock (u : ℕ → Smooth H) (n k : ℕ) : Smooth H :=
  (1/2:ℝ) • (dyadicMean u n k-dyadicMean u n (k+2^n))

theorem halfBlock_lipschitz (u : ℕ → Smooth H) (hu : ∀ i, LipschitzWith 1 (u i).val) (n k : ℕ) :
    LipschitzWith 1 (halfBlock u n k).val := by
  convert half_sub_lipschitz (dyadicMean_lipschitz u hu n k) (dyadicMean_lipschitz u hu n (k+2^n)) using 1
  ext p
  change (1/2:ℝ)*((dyadicMean u n k).val p-(dyadicMean u n (k+2^n)).val p) = _
  ring

theorem halfBlock_zero_value (u : ℕ → Smooth H) (hu : ∀ i, (u i).val 0 = 0) (n k : ℕ) :
    (halfBlock u n k).val 0 = 0 := by
  change (1/2:ℝ)*((dyadicMean u n k).val 0-(dyadicMean u n (k+2^n)).val 0) = 0
  rw [dyadicMean_zero_value u hu,dyadicMean_zero_value u hu,sub_self,mul_zero]

theorem augmentedEnergy_smul (a : MolecularData H) (S : Finset H) (D c : ℝ) (f : Smooth H) :
    augmentedEnergy a S D (c • f) = c^2*augmentedEnergy a S D f := by
  simp only [augmentedEnergy,gradEnergy_smul,mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  change (D*(c*f.val p))^2 = c^2*(D*f.val p)^2
  ring

theorem one_augmentedEnergy_le {K : Set H} {C ρ : ℝ} {μ : ℕ → Space H}
    (a b : RowItem K C ρ μ) (S : Finset H) :
    augmentedEnergy a.a S 1 b.f ≤ C+∑ p ∈ S, ‖p‖^2 := by
  apply add_le_add ((gradEnergy_le_cost a.a b.f b.lip).trans a.cost_le)
  apply Finset.sum_le_sum
  intro p _
  have hp : |b.f.val p| ≤ ‖p‖ := by
    have h := b.lip.dist_le_mul p 0
    simpa only [Real.dist_eq,b.zero,sub_zero,NNReal.coe_one,one_mul,dist_zero_right,Real.norm_eq_abs] using h
  change (1*b.f.val p)^2 ≤ ‖p‖^2
  simpa only [one_mul,sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hp

theorem select_block {K : Set H} {C ρ α : ℝ} {μ : ℕ → Space H}
    (hα : 0 < α) (P : RowItem K C ρ μ → Prop)
    (hRich : ((triangularRows K C ρ α μ).restrict P).Rich)
    (S : Finset H) {ε : ℝ} (hε : 0 < ε) :
    ∃ (z : Smooth H) (a : RowItem K C ρ μ), LipschitzWith 1 z.val ∧ z.val 0 = 0 ∧
      P a ∧ α ≤ smoothPair a.a z ∧
      ((triangularRows K C ρ α μ).restrict
        (fun b => P b ∧ augmentedEnergy b.a S 1 z < ε)).Rich := by
  classical
  let B : ℝ := C+∑ p ∈ S, ‖p‖^2
  obtain ⟨d0,hd0⟩ := exists_nat_gt (4*B/ε)
  let d := d0+1
  have hd : 4*B < (d : ℝ)*ε := by
    have : (4*B/ε) < (d : ℝ) := hd0.trans (by simp [d])
    exact (div_lt_iff₀ hε).mp this
  have hdpos : 0 < d := by omega
  let : NeZero d := ⟨by omega⟩
  have hpow : 0 < (2:ℕ)^d := pow_pos (by norm_num) d
  let : NeZero (2^d) := ⟨by omega⟩
  obtain ⟨row,hrow,hP⟩ := hRich (2^d)
  let u : ℕ → Smooth H := fun k => if hk : k < 2^d then (row ⟨k,hk⟩).f else 0
  have hu (k : ℕ) (hk : k < 2^d) : u k = (row ⟨k,hk⟩).f := dite_eq_left hk
  have huLip (k : ℕ) : LipschitzWith 1 (u k).val := by
    by_cases hk : k < 2^d
    · rw [hu k hk]; exact (row ⟨k,hk⟩).lip
    · simp only [u,dite_eq_right hk]
      exact (LipschitzWith.const (0:ℝ)).weaken (by norm_num)
  have hu0 (k : ℕ) : (u k).val 0 = 0 := by
    by_cases hk : k < 2^d
    · rw [hu k hk]; exact (row ⟨k,hk⟩).zero
    · simp [u,hk]
  let colorP : (Fin d × Fin (2^d)) → RowItem K C ρ μ → Prop := fun c b =>
    c.2.val+2^(c.1.val+1) ≤ 2^d ∧
      augmentedEnergy b.a S 1 (dyadicMean u c.1.val c.2.val-
        dyadicMean u c.1.val (c.2.val+2^c.1.val)) < ε
  have hcover (b : RowItem K C ρ μ) : ∃ c, colorP c b := by
    obtain ⟨n,k,hn,hk,hsmall⟩ := exists_small_dyadic_difference
      (augmentedEnergy b.a S 1) (augmentedEnergy_nonneg b.a S 1)
      (augmentedEnergy_midpoint b.a S 1) u hε d hd (fun k hk => by
        rw [hu k hk]; exact one_augmentedEnergy_le b (row ⟨k,hk⟩) S)
    have hkp : k < 2^d := by have := pow_pos (by norm_num : 0<2) (n+1); omega
    exact ⟨(⟨n,hn⟩,⟨k,hkp⟩),hk,hsmall⟩
  obtain ⟨c,hc⟩ := RowFamily.rich_finite_cover _ hRich colorP hcover
  obtain ⟨one,hone⟩ := hc 1
  have hbound : c.2.val+2^(c.1.val+1) ≤ 2^d := (hone.2 0).1
  let n := c.1.val
  let k := c.2.val
  have hsplit : (2:ℕ)^(n+1) = 2^n+2^n := by omega
  have hp : 0 < (2:ℕ)^n := pow_pos (by norm_num) n
  let mid : Fin (2^d) := ⟨k+2^n-1,by dsimp [k,n] at *; omega⟩
  let z := halfBlock u n k
  have hhigh : 4*α ≤ smoothPair (row mid).a (dyadicMean u n k) := by
    rw [map_dyadicMean]
    apply le_dyadicMean
    intro i hi hi'
    have hiN : i < 2^d := by dsimp [k,n] at *; omega
    rw [hu i hiN]
    exact hrow.1 mid ⟨i,hiN⟩ (by change i ≤ mid.val; dsimp [mid]; omega)
  have hlow : smoothPair (row mid).a (dyadicMean u n (k+2^n)) ≤ α := by
    rw [map_dyadicMean]
    apply dyadicMean_le
    intro i hi hi'
    have hiN : i < 2^d := by dsimp [k,n] at *; omega
    rw [hu i hiN]
    exact (le_abs_self _).trans (hrow.2 mid ⟨i,hiN⟩ (by change mid.val < i; dsimp [mid]; omega))
  have hzpair : α ≤ smoothPair (row mid).a z := by
    simp only [z,halfBlock,map_smul,map_sub,smul_eq_mul]
    linarith
  refine ⟨z,row mid,halfBlock_lipschitz u huLip n k,halfBlock_zero_value u hu0 n k,hP mid,hzpair,?_⟩
  intro N
  obtain ⟨v,hv,hcolor⟩ := hc N
  refine ⟨v,hv.1,fun i => ⟨hv.2 i,?_⟩⟩
  have he := (hcolor i).2
  have hnonneg := augmentedEnergy_nonneg (v i).a S 1
    (dyadicMean u n k-dyadicMean u n (k+2^n))
  change augmentedEnergy (v i).a S 1 ((1/2:ℝ) • _) < ε
  rw [augmentedEnergy_smul]
  change augmentedEnergy (v i).a S 1 (dyadicMean u n k-dyadicMean u n (k+2^n)) < ε at he
  nlinarith

end LipschitzCounterexample.CompactWSC
end

end OAI
