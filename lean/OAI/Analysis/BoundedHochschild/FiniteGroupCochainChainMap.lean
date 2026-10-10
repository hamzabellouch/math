import OAI.Analysis.BoundedHochschild.CochainTransportMiddle
import OAI.Analysis.BoundedHochschild.FiniteFunctionAverages

namespace OAI

/-! The contractive finite-group cochain averages commute with the
Hochschild differential. No homotopy or cohomology-class assertion is
assumed in this calculation. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u v
variable {M : Type u} [CStarAlgebra M] {G : Type v} [Group G] [Fintype G]

lemma finiteGroupCochainAverage_add {n : ℕ} (ρ : G →* unitary M) (f g : Cochain M n) :
    finiteGroupCochainAverage ρ (f + g) = finiteGroupCochainAverage ρ f + finiteGroupCochainAverage ρ g := by
  simp only [finiteGroupCochainAverage, cochainUnitaryTransport_add, Finset.sum_add_distrib, smul_add]

lemma finiteGroupCochainAverage_smul {n : ℕ} (ρ : G →* unitary M) (z : ℂ) (f : Cochain M n) :
    finiteGroupCochainAverage ρ (z • f) = z • finiteGroupCochainAverage ρ f := by
  simp only [finiteGroupCochainAverage, cochainUnitaryTransport_smul, ← Finset.smul_sum]
  exact smul_comm _ _ _

def finiteGroupCochainAverageLinear {n : ℕ} (ρ : G →* unitary M) : Cochain M n →ₗ[ℂ] Cochain M n where
  toFun := finiteGroupCochainAverage ρ
  map_add' := finiteGroupCochainAverage_add ρ
  map_smul' := finiteGroupCochainAverage_smul ρ

lemma finiteGroupCochainAverage_sum {I : Type*} {n : ℕ} (ρ : G →* unitary M)
    (s : Finset I) (f : I → Cochain M n) :
    finiteGroupCochainAverage ρ (∑ i ∈ s, f i) = ∑ i ∈ s, finiteGroupCochainAverage ρ (f i) :=
  map_sum (finiteGroupCochainAverageLinear ρ) f s

def leftFaceLinear (n : ℕ) : Cochain M n →ₗ[ℂ] Cochain M (n + 1) where
  toFun := leftCoboundary
  map_add' f g := by ext x; simp only [leftCoboundary_apply, add_apply, mul_add]
  map_smul' z f := by ext x; simp only [leftCoboundary_apply, smul_apply, mul_smul_comm, RingHom.id_apply]

def rightFaceLinear (n : ℕ) : Cochain M n →ₗ[ℂ] Cochain M (n + 1) where
  toFun := rightCoboundary
  map_add' f g := by ext x; simp only [rightCoboundary_apply, add_apply, add_mul]
  map_smul' z f := by ext x; simp only [rightCoboundary_apply, smul_apply, smul_mul_assoc, RingHom.id_apply]

def middleFaceLinear {n : ℕ} (k : Fin (n + 1)) :
    Cochain M (n + 1) →ₗ[ℂ] Cochain M (n + 2) where
  toFun f := middleCoboundary f k
  map_add' f g := by ext x; simp only [middleCoboundary_apply, add_apply]
  map_smul' z f := by ext x; simp only [middleCoboundary_apply, smul_apply, RingHom.id_apply]

lemma finiteGroupCochainAverage_face {n : ℕ} (ρ : G →* unitary M)
    (L : Cochain M n →ₗ[ℂ] Cochain M (n + 1)) (k : Fin (n + 2)) (f : Cochain M n)
    (hL : ∀ u : Fin (n + 2) → unitary M,
      cochainUnitaryTransport u (L f) = L (cochainUnitaryTransport (k.removeNth u) f)) :
    finiteGroupCochainAverage ρ (L f) = L (finiteGroupCochainAverage ρ f) := by
  have ht (u : Fin (n + 2) → G) :
      cochainUnitaryTransport (fun i => ρ (u i)) (L f) =
        L (cochainUnitaryTransport (fun i => ρ (k.removeNth u i)) f) := hL (fun i => ρ (u i))
  unfold finiteGroupCochainAverage
  simp_rw [ht]
  rw [← map_sum, ← map_smul]
  congr 1
  exact normalized_sum_removeNth k (fun u => cochainUnitaryTransport (fun i => ρ (u i)) f)

lemma finiteGroupCochainAverage_leftCoboundary {n : ℕ} (ρ : G →* unitary M) (f : Cochain M n) :
    finiteGroupCochainAverage ρ (leftCoboundary f) = leftCoboundary (finiteGroupCochainAverage ρ f) := by
  apply finiteGroupCochainAverage_face ρ (leftFaceLinear n) 0 f
  intro u
  simpa only [leftFaceLinear, LinearMap.coe_mk, AddHom.coe_mk, Fin.removeNth_zero] using
    cochainUnitaryTransport_leftCoboundary u f

lemma finiteGroupCochainAverage_rightCoboundary {n : ℕ} (ρ : G →* unitary M) (f : Cochain M n) :
    finiteGroupCochainAverage ρ (rightCoboundary f) = rightCoboundary (finiteGroupCochainAverage ρ f) := by
  apply finiteGroupCochainAverage_face ρ (rightFaceLinear n) (Fin.last (n + 1)) f
  intro u
  change cochainUnitaryTransport u (rightCoboundary f) =
    rightCoboundary (cochainUnitaryTransport ((Fin.last (n + 1)).removeNth u) f)
  rw [Fin.removeNth_last, show Fin.init u = (fun i => u i.castSucc) from rfl]
  exact cochainUnitaryTransport_rightCoboundary u f

lemma finiteGroupCochainAverage_middleCoboundary {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) (k : Fin (n + 1)) :
    finiteGroupCochainAverage ρ (middleCoboundary f k) = middleCoboundary (finiteGroupCochainAverage ρ f) k := by
  apply finiteGroupCochainAverage_face ρ (middleFaceLinear k) k.castSucc.succ f
  intro u
  exact cochainUnitaryTransport_middleCoboundary u f k

lemma finiteGroupCochainAverage_differential {n : ℕ} (ρ : G →* unitary M) (f : Cochain M (n + 1)) :
    finiteGroupCochainAverage ρ (differential f) = differential (finiteGroupCochainAverage ρ f) := by
  change finiteGroupCochainAverage ρ
    (leftCoboundary f + ∑ j : Fin (n + 1), ((-1 : ℂ) ^ (j.val + 1)) • middleCoboundary f j +
      ((-1 : ℂ) ^ (n + 2)) • rightCoboundary f) = _
  simp only [finiteGroupCochainAverage_add, finiteGroupCochainAverage_sum,
    finiteGroupCochainAverage_smul, finiteGroupCochainAverage_leftCoboundary,
    finiteGroupCochainAverage_rightCoboundary, finiteGroupCochainAverage_middleCoboundary]
  rfl

lemma finiteGroupCochainAverage_cocycle {n : ℕ} (ρ : G →* unitary M) (f : Cochain M (n + 1))
    (hf : ∀ x, differentialValue f x = 0) :
    ∀ x, differentialValue (finiteGroupCochainAverage ρ f) x = 0 := by
  have hd : differential f = 0 := by
    ext x
    simpa only [differential_apply, zero_apply] using hf x
  have he := finiteGroupCochainAverage_differential ρ f
  rw [hd, show finiteGroupCochainAverage ρ (0 : Cochain M (n + 2)) = 0 from
    map_zero (finiteGroupCochainAverageLinear ρ)] at he
  intro x
  simpa only [differential_apply, zero_apply] using
    congrArg (fun F : Cochain M (n + 2) => F x) he.symm

end BoundedHochschild.KadisonRingrose

end

end OAI
