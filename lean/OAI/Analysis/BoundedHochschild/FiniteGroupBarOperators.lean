import OAI.Analysis.BoundedHochschild.MultimodularTransport
import OAI.Analysis.BoundedHochschild.FiniteGroupCochainChainMap

namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma curryMid_one_norm_le {n : ℕ} (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    ‖f.curryMid i 1‖ ≤ ‖f‖ := by
  have h1 : ‖(1 : M)‖ ≤ 1 := by
    rcases subsingleton_or_nontrivial M with h | h
    · simp [Subsingleton.elim (1 : M) 0]
    · simp
  calc
    _ ≤ ‖f.curryMid i‖ * ‖(1 : M)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖f‖ * 1 := by rw [ContinuousMultilinearMap.norm_curryMid]; gcongr
    _ = _ := mul_one _

def barInsertion {n : ℕ} (u : Fin (n + 2) → unitary M) (i : Fin (n + 1))
    (f : Cochain M (n + 1)) : Cochain M n :=
  (cochainUnitaryTransport (unitaryPrefix u (i.val + 1)) f).curryMid i 1

@[simp] lemma barInsertion_apply {n : ℕ} (u : Fin (n + 2) → unitary M) (i : Fin (n + 1))
    (f : Cochain M (n + 1)) (x : Fin n → M) :
    barInsertion u i f x = cochainUnitaryTransport (unitaryPrefix u (i.val + 1)) f (i.insertNth 1 x) := rfl

lemma barInsertion_value {n : ℕ} (u : Fin (n + 2) → unitary M) (i : Fin (n + 1))
    (f : Cochain M (n + 1)) (x : Fin n → M) :
    barInsertion u i f x = star (u 0 : M) *
      f (cochainUnitaryTuple (unitaryPrefix u (i.val + 1)) (i.insertNth 1 x)) := by
  rw [barInsertion_apply, cochainUnitaryTransport_apply]
  have h0 : unitaryPrefix u (i.val + 1) 0 = u 0 := by simp [unitaryPrefix]
  have hl : unitaryPrefix u (i.val + 1) (Fin.last (n + 1)) = 1 := by
    have hi : ¬n + 1 < i.val + 1 := by omega
    simp only [unitaryPrefix, Fin.val_last, hi, ite_false]
  rw [h0, hl]
  simp only [OneMemClass.coe_one, mul_one]

lemma barInsertion_norm {n : ℕ} (u : Fin (n + 2) → unitary M) (i : Fin (n + 1))
    (f : Cochain M (n + 1)) : ‖barInsertion u i f‖ ≤ ‖f‖ :=
  (curryMid_one_norm_le _ i).trans (cochainUnitaryTransport_norm _ f)

lemma barInsertion_add {n : ℕ} (u : Fin (n + 2) → unitary M) (i : Fin (n + 1))
    (f g : Cochain M (n + 1)) : barInsertion u i (f + g) = barInsertion u i f + barInsertion u i g := by
  ext x
  simp only [barInsertion_apply, cochainUnitaryTransport_add, add_apply]

lemma barInsertion_smul {n : ℕ} (u : Fin (n + 2) → unitary M) (i : Fin (n + 1))
    (z : ℂ) (f : Cochain M (n + 1)) : barInsertion u i (z • f) = z • barInsertion u i f := by
  ext x
  simp only [barInsertion_apply, cochainUnitaryTransport_smul, smul_apply]

variable {G : Type*} [Group G] [Fintype G]

def finiteGroupBarInsertion {n : ℕ} (ρ : G →* unitary M) (i : Fin (n + 1))
    (f : Cochain M (n + 1)) : Cochain M n :=
  (Fintype.card (Fin (n + 2) → G) : ℂ)⁻¹ •
    ∑ g : Fin (n + 2) → G, barInsertion (fun j => ρ (g j)) i f

lemma finiteGroupBarInsertion_norm {n : ℕ} (ρ : G →* unitary M) (i : Fin (n + 1))
    (f : Cochain M (n + 1)) : ‖finiteGroupBarInsertion ρ i f‖ ≤ ‖f‖ := by
  let K := Fin (n + 2) → G
  have hc : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  rw [finiteGroupBarInsertion, norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card K : ℝ)⁻¹ * ((Fintype.card K : ℝ) * ‖f‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      exact (norm_sum_le _ _).trans (by
        simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
          Finset.sum_le_sum (s := Finset.univ) (fun (g : Fin (n + 2) → G) _ =>
            barInsertion_norm (fun j => ρ (g j)) i f))
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]

def finiteGroupBarOperator {n : ℕ} (ρ : G →* unitary M) (f : Cochain M (n + 1)) : Cochain M n :=
  ∑ i : Fin (n + 1), ((-1 : ℂ) ^ i.val) • finiteGroupBarInsertion ρ i f

lemma finiteGroupBarOperator_norm {n : ℕ} (ρ : G →* unitary M) (f : Cochain M (n + 1)) :
    ‖finiteGroupBarOperator ρ f‖ ≤ (n + 1 : ℝ) * ‖f‖ := by
  unfold finiteGroupBarOperator
  calc
    _ ≤ ∑ i : Fin (n + 1), ‖((-1 : ℂ) ^ i.val) • finiteGroupBarInsertion ρ i f‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (n + 1), ‖f‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using
        finiteGroupBarInsertion_norm ρ i f
    _ = _ := by simp [nsmul_eq_mul]

lemma finiteGroupBarInsertion_add {n : ℕ} (ρ : G →* unitary M) (i : Fin (n + 1))
    (f g : Cochain M (n + 1)) :
    finiteGroupBarInsertion ρ i (f + g) = finiteGroupBarInsertion ρ i f + finiteGroupBarInsertion ρ i g := by
  simp only [finiteGroupBarInsertion, barInsertion_add, Finset.sum_add_distrib, smul_add]

lemma finiteGroupBarInsertion_smul {n : ℕ} (ρ : G →* unitary M) (i : Fin (n + 1))
    (z : ℂ) (f : Cochain M (n + 1)) :
    finiteGroupBarInsertion ρ i (z • f) = z • finiteGroupBarInsertion ρ i f := by
  simp only [finiteGroupBarInsertion, barInsertion_smul, ← Finset.smul_sum]
  exact smul_comm _ _ _

lemma finiteGroupBarOperator_add {n : ℕ} (ρ : G →* unitary M) (f g : Cochain M (n + 1)) :
    finiteGroupBarOperator ρ (f + g) = finiteGroupBarOperator ρ f + finiteGroupBarOperator ρ g := by
  simp only [finiteGroupBarOperator, finiteGroupBarInsertion_add, smul_add, Finset.sum_add_distrib]

lemma finiteGroupBarOperator_smul {n : ℕ} (ρ : G →* unitary M) (z : ℂ) (f : Cochain M (n + 1)) :
    finiteGroupBarOperator ρ (z • f) = z • finiteGroupBarOperator ρ f := by
  simp only [finiteGroupBarOperator, finiteGroupBarInsertion_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

def finiteGroupBarOperatorCLM (ρ : G →* unitary M) (n : ℕ) :
    Cochain M (n + 1) →L[ℂ] Cochain M n :=
  LinearMap.mkContinuous
    { toFun := finiteGroupBarOperator ρ
      map_add' := finiteGroupBarOperator_add ρ
      map_smul' := finiteGroupBarOperator_smul ρ }
    (n + 1) (fun f => by
      change ‖finiteGroupBarOperator ρ f‖ ≤ (n + 1 : ℝ) * ‖f‖
      exact finiteGroupBarOperator_norm ρ f)

end BoundedHochschild.KadisonRingrose

end

end OAI
