import OAI.Analysis.BoundedHochschild.BarInsertionFaces
import OAI.Analysis.BoundedHochschild.FiniteGroupPrefixAverages

namespace OAI

/-! Finite-group averages of the individual bar-insertion face formulas.
All unused vertex coordinates are integrated out with the normalized
finite-function sum identity. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u v
variable {M : Type u} [CStarAlgebra M] {G : Type v} [Group G] [Fintype G]

lemma finiteGroupBarInsertion_coface {n : ℕ} (ρ : G →* unitary M)
    (L : Cochain M (n + 1) →ₗ[ℂ] Cochain M (n + 2))
    (K : Cochain M n →ₗ[ℂ] Cochain M (n + 1))
    (i : Fin (n + 2)) (j : Fin (n + 1)) (p : Fin (n + 3))
    (f : Cochain M (n + 1))
    (h : ∀ u : Fin (n + 3) → unitary M,
      barInsertion u i (L f) = K (barInsertion (p.removeNth u) j f)) :
    finiteGroupBarInsertion ρ i (L f) = K (finiteGroupBarInsertion ρ j f) := by
  have ht (g : Fin (n + 3) → G) :
      barInsertion (fun k => ρ (g k)) i (L f) =
        K (barInsertion (fun k => ρ (p.removeNth g k)) j f) := h (fun k => ρ (g k))
  unfold finiteGroupBarInsertion
  simp_rw [ht]
  rw [← map_sum, ← map_smul]
  congr 1
  exact normalized_sum_removeNth p (fun g => barInsertion (fun k => ρ (g k)) j f)

lemma finiteGroupBarInsertion_left_zero {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) : finiteGroupBarInsertion ρ 0 (leftCoboundary f) = f := by
  simp only [finiteGroupBarInsertion, barInsertion_leftCoboundary_zero,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)), one_smul]

lemma finiteGroupBarInsertion_left_succ {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    finiteGroupBarInsertion ρ i.succ (leftCoboundary f) =
      leftCoboundary (finiteGroupBarInsertion ρ i f) := by
  apply finiteGroupBarInsertion_coface ρ (leftFaceLinear (n + 1)) (leftFaceLinear n) i.succ i 0 f
  intro u
  simpa only [leftFaceLinear, LinearMap.coe_mk, AddHom.coe_mk, Fin.removeNth_zero] using
    barInsertion_leftCoboundary_succ u f i

lemma finiteGroupBarInsertion_right_last {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) :
    finiteGroupBarInsertion ρ (Fin.last (n + 1)) (rightCoboundary f) =
      finiteGroupCochainAverage ρ f := by
  unfold finiteGroupBarInsertion
  simp only [barInsertion_rightCoboundary_last]
  change (Fintype.card (Fin (n + 3) → G) : ℂ)⁻¹ •
      (∑ g : Fin (n + 3) → G,
        cochainUnitaryTransport (fun k => ρ (Fin.init g k)) f) = _
  rw [show (fun g : Fin (n + 3) → G =>
      cochainUnitaryTransport (fun k => ρ (Fin.init g k)) f) =
    (fun g => cochainUnitaryTransport (fun k => ρ ((Fin.last (n + 2)).removeNth g k)) f) from by
      funext g
      rw [Fin.removeNth_last]]
  exact normalized_sum_removeNth (Fin.last (n + 2))
    (fun g => cochainUnitaryTransport (fun k => ρ (g k)) f)

lemma finiteGroupBarInsertion_right_castSucc {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    finiteGroupBarInsertion ρ i.castSucc (rightCoboundary f) =
      rightCoboundary (finiteGroupBarInsertion ρ i f) := by
  apply finiteGroupBarInsertion_coface ρ (rightFaceLinear (n + 1)) (rightFaceLinear n)
    i.castSucc i (Fin.last (n + 2)) f
  intro u
  simpa only [rightFaceLinear, LinearMap.coe_mk, AddHom.coe_mk, Fin.removeNth_last] using
    barInsertion_rightCoboundary_castSucc u f i

lemma finiteGroupBarInsertion_middle_castSucc {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    finiteGroupBarInsertion ρ i.castSucc (middleCoboundary f i) =
      finiteGroupPrefixAverage ρ (i.val + 1) f := by
  unfold finiteGroupBarInsertion
  simp only [barInsertion_middleCoboundary_castSucc]
  exact normalized_sum_removeNth i.castSucc.succ
    (fun g => cochainUnitaryTransport (unitaryPrefix (fun k => ρ (g k)) (i.val + 1)) f)

lemma finiteGroupBarInsertion_middle_succ {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    finiteGroupBarInsertion ρ i.succ (middleCoboundary f i) =
      finiteGroupPrefixAverage ρ (i.val + 1) f := by
  unfold finiteGroupBarInsertion
  simp only [barInsertion_middleCoboundary_succ]
  exact normalized_sum_removeNth i.castSucc.succ
    (fun g => cochainUnitaryTransport (unitaryPrefix (fun k => ρ (g k)) (i.val + 1)) f)

lemma finiteGroupBarInsertion_middle_after {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 2)) (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i.val ≤ j.val) :
    finiteGroupBarInsertion ρ i.castSucc (middleCoboundary f j.succ) =
      middleCoboundary (finiteGroupBarInsertion ρ i f) j := by
  apply finiteGroupBarInsertion_coface ρ (middleFaceLinear j.succ) (middleFaceLinear j)
    i.castSucc i j.succ.castSucc.succ f
  intro u
  exact barInsertion_middleCoboundary_after u f i j hij

lemma finiteGroupBarInsertion_middle_before {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 2)) (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.val < i.val) :
    finiteGroupBarInsertion ρ i.succ (middleCoboundary f j.castSucc) =
      middleCoboundary (finiteGroupBarInsertion ρ i f) j := by
  apply finiteGroupBarInsertion_coface ρ (middleFaceLinear j.castSucc) (middleFaceLinear j)
    i.succ i j.castSucc.castSucc.succ f
  intro u
  exact barInsertion_middleCoboundary_before u f i j hji

end BoundedHochschild.KadisonRingrose

end

end OAI
