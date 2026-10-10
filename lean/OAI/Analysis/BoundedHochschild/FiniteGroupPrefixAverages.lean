import OAI.Analysis.BoundedHochschild.MultimodularTransport

namespace OAI

/-! Contractive prefix averages interpolate between the identity and the
finite-group cochain average. They use the same independent vertex variables
as the bar-insertion operators. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M G : Type*} [CStarAlgebra M] [Group G] [Fintype G]

def finiteGroupPrefixAverage {n : ℕ} (ρ : G →* unitary M) (k : ℕ)
    (f : Cochain M n) : Cochain M n :=
  (Fintype.card (Fin (n + 1) → G) : ℂ)⁻¹ •
    ∑ g : Fin (n + 1) → G, cochainUnitaryTransport (unitaryPrefix (fun j => ρ (g j)) k) f

lemma finiteGroupPrefixAverage_norm {n : ℕ} (ρ : G →* unitary M) (k : ℕ)
    (f : Cochain M n) : ‖finiteGroupPrefixAverage ρ k f‖ ≤ ‖f‖ := by
  let K := Fin (n + 1) → G
  have hc : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  rw [finiteGroupPrefixAverage, norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card K : ℝ)⁻¹ * ((Fintype.card K : ℝ) * ‖f‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      exact (norm_sum_le _ _).trans (by
        simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
          Finset.sum_le_sum (s := Finset.univ) (fun (g : K) _ =>
            cochainUnitaryTransport_norm (unitaryPrefix (fun j => ρ (g j)) k) f))
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]

lemma finiteGroupPrefixAverage_zero {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M n) : finiteGroupPrefixAverage ρ 0 f = f := by
  have hp (g : Fin (n + 1) → G) :
      unitaryPrefix (fun j => ρ (g j)) 0 = (fun _ => 1) := by
    funext j
    simp [unitaryPrefix]
  simp only [finiteGroupPrefixAverage, hp, cochainUnitaryTransport_one,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)), one_smul]

lemma finiteGroupPrefixAverage_full {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M n) : finiteGroupPrefixAverage ρ (n + 1) f = finiteGroupCochainAverage ρ f := by
  have hp (g : Fin (n + 1) → G) :
      unitaryPrefix (fun j => ρ (g j)) (n + 1) = (fun j => ρ (g j)) := by
    funext j
    simp only [unitaryPrefix, j.isLt, ite_true]
  simp only [finiteGroupPrefixAverage, hp, finiteGroupCochainAverage]

lemma finiteGroupPrefixAverage_add {n : ℕ} (ρ : G →* unitary M) (k : ℕ)
    (f g : Cochain M n) : finiteGroupPrefixAverage ρ k (f + g) =
      finiteGroupPrefixAverage ρ k f + finiteGroupPrefixAverage ρ k g := by
  simp only [finiteGroupPrefixAverage, cochainUnitaryTransport_add,
    Finset.sum_add_distrib, smul_add]

lemma finiteGroupPrefixAverage_smul {n : ℕ} (ρ : G →* unitary M) (k : ℕ)
    (z : ℂ) (f : Cochain M n) : finiteGroupPrefixAverage ρ k (z • f) =
      z • finiteGroupPrefixAverage ρ k f := by
  simp only [finiteGroupPrefixAverage, cochainUnitaryTransport_smul, ← Finset.smul_sum]
  exact smul_comm _ _ _

def finiteGroupPrefixAverageCLM (ρ : G →* unitary M) (n k : ℕ) :
    Cochain M n →L[ℂ] Cochain M n :=
  LinearMap.mkContinuous
    { toFun := finiteGroupPrefixAverage ρ k
      map_add' := finiteGroupPrefixAverage_add ρ k
      map_smul' := finiteGroupPrefixAverage_smul ρ k }
    1 (fun f => by
      change ‖finiteGroupPrefixAverage ρ k f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using finiteGroupPrefixAverage_norm ρ k f)

/-- The successive prefix changes sum to the difference between a cochain
and its full finite-group average. -/
lemma finiteGroupPrefixAverage_telescope {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M n) :
    (∑ i : Fin (n + 1), (finiteGroupPrefixAverage ρ i.val f -
      finiteGroupPrefixAverage ρ (i.val + 1) f)) = f - finiteGroupCochainAverage ρ f := by
  have h (m : ℕ) :
      (∑ i : Fin m, (finiteGroupPrefixAverage ρ i.val f -
        finiteGroupPrefixAverage ρ (i.val + 1) f)) =
      finiteGroupPrefixAverage ρ 0 f - finiteGroupPrefixAverage ρ m f := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      abel
  simpa only [finiteGroupPrefixAverage_zero, finiteGroupPrefixAverage_full] using h (n + 1)

end BoundedHochschild.KadisonRingrose

end

end OAI
