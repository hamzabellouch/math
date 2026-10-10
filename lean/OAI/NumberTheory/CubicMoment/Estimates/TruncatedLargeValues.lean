import OAI.NumberTheory.CubicMoment.Estimates.LargeValueSubsequence

namespace OAI

/-! Removing tiny factors before extracting the actual large-value rows. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Variable powers have exactly the exponent approached by their powers.
This includes the lower sequences arising from successively smaller saving losses. -/
theorem HasPowerExponent.variable_rpow {Y a : ℕ → ℝ} {s : ℝ}
    (hY : Tendsto Y atTop atTop) (ha : Tendsto a atTop (𝓝 s)) :
    HasPowerExponent Y (fun j => (Y j)^(a j)) s := by
  apply ha.congr'
  filter_upwards [hY.eventually_gt_atTop 1] with j hj
  rw [Real.log_rpow (zero_lt_one.trans hj),mul_div_cancel_right₀ _ (Real.log_pos hj).ne']

private lemma small_factor_power_identity {Y : ℝ} (hY : 0 < Y)
    (D H K : ℝ) (t : ℕ) :
    Y^D*(Y^(-K)*(Y^H)^t)^2 = Y^(D-2*K+2*(t:ℝ)*H) := by
  rw [← Real.rpow_mul_natCast hY.le,← Real.rpow_add hY,
    ← Real.rpow_mul_natCast hY.le,← Real.rpow_add hY]
  congr 1
  ring

/-- The full finite moment retains at least half its lower bound after
removing every row with a tiny factor. The exponent of the cutoff is fixed. -/
theorem retain_large_factor_moment {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset κ) (f : ι → κ → ℝ) {Y G D H K : ℝ}
    (hY : 2 ≤ Y) (hG : 1 ≤ G) (hH : 0 ≤ H)
    (hK : D+2*(Fintype.card ι:ℝ)*H-2*K ≤ -2)
    (hcard : (S.card:ℝ) ≤ Y^D)
    (hf : ∀ x ∈ S, ∀ i, 0 ≤ f i x)
    (hhi : ∀ x ∈ S, ∀ i, f i x ≤ Y^H)
    (hmoment : G ≤ ∑ x ∈ S, (∏ i, f i x)^2) :
    G/2 ≤ ∑ x ∈ S with ∀ i, Y^(-K) ≤ f i x, (∏ i, f i x)^2 := by
  have hY₁ : 1 ≤ Y := by linarith
  have hYp : 0 < Y := by linarith
  have hU : 1 ≤ Y^H := Real.one_le_rpow hY₁ hH
  have hdiscard := discard_small_factor_moment S f (τ := Y^(-K)) hU hf hhi
  have htail : (S.card:ℝ)*(Y^(-K)*(Y^H)^(Fintype.card ι))^2 ≤ 1/4 := by
    calc
      _ ≤ Y^D*(Y^(-K)*(Y^H)^(Fintype.card ι))^2 :=
        mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = Y^(D-2*K+2*(Fintype.card ι:ℝ)*H) := small_factor_power_identity hYp D H K _
      _ ≤ Y^(-2:ℝ) := Real.rpow_le_rpow_of_exponent_le hY₁ (by linarith)
      _ ≤ (2:ℝ)^(-2:ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hY (by norm_num)
      _ = 1/4 := by norm_num [Real.rpow_neg,Real.rpow_two]
  linarith

/-- An unsaved actual moment with boundedly many polynomially bounded
factor amplitudes produces genuine large-value rows and their limiting
exponents. Zero and arbitrarily tiny values are allowed in the input. -/
theorem extract_unsaved_moment_subsequence {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (Y G : ℕ → ℝ) (S : ℕ → Finset κ) (f : ℕ → ι → κ → ℝ)
    {H K D s : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hcut : D+2*(Fintype.card ι:ℝ)*H-2*K ≤ -2)
    (hY : Tendsto Y atTop atTop) (hY₂ : ∀ j, 2 ≤ Y j)
    (hG : ∀ j, 1 ≤ G j) (hGexp : HasPowerExponent Y G s)
    (hcard : ∀ j, ((S j).card:ℝ) ≤ (Y j)^D)
    (hf : ∀ j, ∀ x ∈ S j, ∀ i, 0 ≤ f j i x)
    (hhi : ∀ j, ∀ x ∈ S j, ∀ i, f j i x ≤ (Y j)^H)
    (hmoment : ∀ j, G j ≤ ∑ x ∈ S j, (∏ i, f j i x)^2) :
    ∃ (φ : ℕ → ℕ) (P : ℕ → Finset κ) (B : ℕ → ι → ℝ) (r : ℝ) (v : ι → ℝ),
      StrictMono φ ∧ (∀ j, (P j).Nonempty ∧ P j ⊆ S (φ j)) ∧
      (∀ j i, (Y (φ j))^(-K) ≤ B j i ∧ B j i ≤ (Y (φ j))^H) ∧
      (∀ j, ∀ x ∈ P j, ∀ i, B j i ≤ f (φ j) i x ∧
        f (φ j) i x ≤ Real.exp 1*B j i) ∧
      HasPowerExponent (Y ∘ φ) (fun j => ((P j).card:ℝ)) r ∧
      (∀ i, HasPowerExponent (Y ∘ φ) (fun j => B j i) (v i)) ∧
      (0 ≤ r ∧ r ≤ D) ∧ (∀ i, -K ≤ v i ∧ v i ≤ H) ∧ s ≤ r+2*(∑ i, v i) := by
  let T : ℕ → Finset κ := fun j => (S j).filter (fun x => ∀ i, (Y j)^(-K) ≤ f j i x)
  have hT (j : ℕ) : T j ⊆ S j := Finset.filter_subset _ _
  have hhalf : HasPowerExponent Y (fun j => G j/2) s := by
    have h := hGexp.const_mul hY (by norm_num : (0:ℝ) < 1/2)
      (Eventually.of_forall (fun j => zero_lt_one.trans_le (hG j)))
    simpa only [div_eq_mul_inv,mul_comm,one_mul] using h
  obtain ⟨φ,P,B,r,v,hφ,hP,hB,hrows,hRexp,hBexp,hr,hv,hs⟩ :=
    extract_large_value_subsequence Y (fun j => G j/2) T f hH hK hY
      (fun j => by linarith [hY₂ j]) (fun j => by linarith [hG j]) hhalf
      (fun j => (Nat.cast_le.mpr (Finset.card_le_card (hT j))).trans (hcard j))
      (fun j x hx i => (Finset.mem_filter.mp hx).2 i)
      (fun j x hx i => hhi j x (hT j hx) i)
      (fun j => retain_large_factor_moment (S j) (f j) (hY₂ j) (hG j) hH hcut
        (hcard j) (hf j) (hhi j) (hmoment j))
  exact ⟨φ,P,B,r,v,hφ,fun j => ⟨(hP j).1,(hP j).2.trans (hT (φ j))⟩,
    hB,hrows,hRexp,hBexp,hr,hv,hs⟩

end CubicFirstMoment

end

end OAI
