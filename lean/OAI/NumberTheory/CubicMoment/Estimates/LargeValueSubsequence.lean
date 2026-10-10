import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicLoss

namespace OAI

/-! A large-value subsequence is extracted from the actual finite moment. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma logarithmic_power_bounds {Y x l u : ℝ} (hY : 1 < Y)
    (hlo : Y^l ≤ x) (hhi : x ≤ Y^u) :
    l ≤ Real.log x/Real.log Y ∧ Real.log x/Real.log Y ≤ u := by
  have hYp : 0 < Y := zero_lt_one.trans hY
  have hxp : 0 < x := (Real.rpow_pos_of_pos hYp l).trans_le hlo
  constructor
  · apply (le_div_iff₀ (Real.log_pos hY)).mpr
    have h := Real.log_le_log (Real.rpow_pos_of_pos hYp l) hlo
    rwa [Real.log_rpow hYp] at h
  · apply (div_le_iff₀ (Real.log_pos hY)).mpr
    have h := Real.log_le_log hxp hhi
    rwa [Real.log_rpow hYp] at h

/-- Uniform elementary bounds and an unsaved moment yield actual selected
rows and simultaneous logarithmic limits. Their exponents satisfy the
large-value inequality, rather than having it as an assumption. -/
theorem extract_large_value_subsequence {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (Y G : ℕ → ℝ) (S : ℕ → Finset κ) (f : ℕ → ι → κ → ℝ)
    {H K D s : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hY : Tendsto Y atTop atTop) (hY₁ : ∀ j, 1 < Y j)
    (hG : ∀ j, 0 < G j) (hGexp : HasPowerExponent Y G s)
    (hcard : ∀ j, ((S j).card:ℝ) ≤ (Y j)^D)
    (hlo : ∀ j, ∀ x ∈ S j, ∀ i, (Y j)^(-K) ≤ f j i x)
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
  have hex (j : ℕ) := finite_logarithmic_large_values (S j) (f j)
    (Real.rpow_pos_of_pos (zero_lt_one.trans (hY₁ j)) (-K)) (hlo j) (hhi j)
    ((hG j).trans_le (hmoment j))
  choose P B hPne hPsub hBb hrows hm using hex
  let R : ℕ → ℝ := fun j => ((P j).card:ℝ)
  have hRp (j : ℕ) : 0 < R j := Nat.cast_pos.mpr (Finset.card_pos.mpr (hPne j))
  have hRc (j : ℕ) : R j ≤ (Y j)^D :=
    (Nat.cast_le.mpr (Finset.card_le_card (hPsub j))).trans (hcard j)
  have hRlo (j : ℕ) : (Y j)^(0:ℝ) ≤ R j := by
    rw [Real.rpow_zero]
    change (1:ℝ) ≤ ((P j).card:ℝ)
    exact_mod_cast Finset.one_le_card.mpr (hPne j)
  let g : Option ι → ℕ → ℝ := fun i => match i with | none => R | some i => fun j => B j i
  let l : Option ι → ℝ := fun i => match i with | none => 0 | some _ => -K
  let u : Option ι → ℝ := fun i => match i with | none => D | some _ => H
  have hg : ∀ j i, l i ≤ Real.log (g i j)/Real.log (Y j) ∧
      Real.log (g i j)/Real.log (Y j) ≤ u i := by
    intro j i
    cases i with
    | none => exact logarithmic_power_bounds (hY₁ j) (hRlo j) (hRc j)
    | some i => exact logarithmic_power_bounds (hY₁ j) (hBb j i).1 (hBb j i).2
  obtain ⟨a,φ,hφ,ha,hlim⟩ := bounded_logarithms_subsequence Y g l u hg
  let r := a none
  let v : ι → ℝ := fun i => a (some i)
  have hRlim : HasPowerExponent (Y ∘ φ) (fun j => ((P (φ j)).card:ℝ)) r := hlim none
  have hBlim (i : ι) : HasPowerExponent (Y ∘ φ) (fun j => B (φ j) i) (v i) := hlim (some i)
  have hYφ : Tendsto (Y ∘ φ) atTop atTop := hY.comp hφ.tendsto_atTop
  have hGφ : HasPowerExponent (Y ∘ φ) (G ∘ φ) s := hGexp.comp hφ.tendsto_atTop
  have hcost : HasPowerExponent (Y ∘ φ)
      (fun j => logarithmicBoxLoss (Fintype.card ι) H K (Y (φ j))) 0 :=
    (logarithmicBoxLoss_exponent (Fintype.card ι) hH hK hY hY₁).comp hφ.tendsto_atTop
  have hBpos (j : ℕ) (i : ι) : 0 < B (φ j) i :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans (hY₁ (φ j))) _).trans_le (hBb (φ j) i).1
  have hprod := HasPowerExponent.prod_natPowers (fun _ : ι => 1) hBlim
    (fun i => Eventually.of_forall (fun j => hBpos j i))
  simp only [Nat.cast_one,one_mul,pow_one] at hprod
  have hprodP : ∀ᶠ j in atTop, 0 < ∏ i, B (φ j) i :=
    Eventually.of_forall (fun j => Finset.prod_pos (fun i _ => hBpos j i))
  have hRP : ∀ᶠ j in atTop, 0 < ((P (φ j)).card:ℝ) :=
    Eventually.of_forall (fun j => hRp (φ j))
  have hM := hRlim.mul (hprod.natPow 2) hRP
    (by filter_upwards [hprodP] with j hj using sq_pos_of_pos hj)
  have hcostP : ∀ᶠ j in atTop, 0 < logarithmicBoxLoss (Fintype.card ι) H K (Y (φ j)) :=
    Eventually.of_forall (fun j => by
      unfold logarithmicBoxLoss
      positivity)
  have hboundlim := hcost.mul hM hcostP
    (by filter_upwards [hRP,hprodP] with j hr hp using mul_pos hr (sq_pos_of_pos hp))
  have hexponent := hGφ.mono hboundlim hYφ
    (Eventually.of_forall (fun j => hG (φ j))) (Eventually.of_forall (fun j => by
      have h := (hmoment (φ j)).trans (hm (φ j))
      simpa only [logarithmicBoxLoss,mul_assoc,Function.comp_def] using h))
  refine ⟨φ,fun j => P (φ j),fun j i => B (φ j) i,r,v,hφ,?_,?_,?_,hRlim,hBlim,?_,?_,?_⟩
  · intro j
    exact ⟨hPne (φ j),hPsub (φ j)⟩
  · exact fun j i => hBb (φ j) i
  · exact fun j x hx i => hrows (φ j) x hx i
  · exact ha none
  · exact fun i => ha (some i)
  · simpa only [zero_add,Nat.cast_ofNat] using hexponent

end CubicFirstMoment

end

end OAI
