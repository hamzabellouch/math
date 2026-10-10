import OAI.Analysis.BoundedHochschild.FiniteGroupModuleAverages

namespace OAI

/-! Contractive finite-group averaging on cochains. Every boundary between
inputs is averaged independently; the resulting cochain satisfies the
ordinary module identities over the linear span of the unitary group. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u v
variable {M : Type u} [CStarAlgebra M]

private def unitaryBimultiply (u v : unitary M) : M →L[ℂ] M :=
  (ContinuousLinearMap.mul ℂ M (u : M)).comp
    ((ContinuousLinearMap.mul ℂ M).flip (v : M))

private lemma unitaryBimultiply_apply (u v : unitary M) (a : M) :
    unitaryBimultiply u v a = (u : M) * a * (v : M) := by
  simp only [unitaryBimultiply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply, mul_assoc]

def cochainUnitaryTuple {n : ℕ} (u : Fin (n + 1) → unitary M) (x : Fin n → M) : Fin n → M :=
  fun i => (u i.castSucc : M) * x i * star (u i.succ : M)

def cochainUnitaryTransport {n : ℕ} (u : Fin (n + 1) → unitary M)
    (f : Cochain M n) : Cochain M n :=
  (unitaryBimultiply (star (u 0)) (u (Fin.last n))).compContinuousMultilinearMap
    (f.compContinuousLinearMap (fun i => unitaryBimultiply (u i.castSucc) (star (u i.succ))))

@[simp] lemma cochainUnitaryTransport_apply {n : ℕ} (u : Fin (n + 1) → unitary M)
    (f : Cochain M n) (x : Fin n → M) :
    cochainUnitaryTransport u f x =
      star (u 0 : M) * f (cochainUnitaryTuple u x) * (u (Fin.last n) : M) := by
  change unitaryBimultiply _ _ (f (fun i => unitaryBimultiply _ _ (x i))) = _
  simp only [unitaryBimultiply_apply, Unitary.coe_star]
  rfl

lemma cochainUnitaryTransport_norm {n : ℕ} (u : Fin (n + 1) → unitary M)
    (f : Cochain M n) : ‖cochainUnitaryTransport u f‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  rw [cochainUnitaryTransport_apply]
  change ‖((star (u 0) : unitary M) : M) * f (cochainUnitaryTuple u x) *
    (u (Fin.last n) : M)‖ ≤ _
  rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  have hp : (∏ i, ‖cochainUnitaryTuple u x i‖) = ∏ i, ‖x i‖ := by
    apply Finset.prod_congr rfl
    intro i _
    change ‖(u i.castSucc : M) * x i * ((star (u i.succ) : unitary M) : M)‖ = ‖x i‖
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  have hb := f.le_opNorm (cochainUnitaryTuple u x)
  rwa [hp] at hb

lemma cochainUnitaryTransport_add {n : ℕ} (u : Fin (n + 1) → unitary M)
    (f g : Cochain M n) :
    cochainUnitaryTransport u (f + g) = cochainUnitaryTransport u f + cochainUnitaryTransport u g := by
  ext x
  simp only [cochainUnitaryTransport_apply, add_apply, mul_add, add_mul]

lemma cochainUnitaryTransport_smul {n : ℕ} (u : Fin (n + 1) → unitary M)
    (z : ℂ) (f : Cochain M n) :
    cochainUnitaryTransport u (z • f) = z • cochainUnitaryTransport u f := by
  ext x
  simp only [cochainUnitaryTransport_apply, smul_apply, mul_smul_comm, smul_mul_assoc]

def cochainUnitaryTransportCLM {n : ℕ} (u : Fin (n + 1) → unitary M) :
    Cochain M n →L[ℂ] Cochain M n :=
  LinearMap.mkContinuous
    { toFun := cochainUnitaryTransport u
      map_add' := cochainUnitaryTransport_add u
      map_smul' := cochainUnitaryTransport_smul u }
    1 (fun f => by
      change ‖cochainUnitaryTransport u f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using cochainUnitaryTransport_norm u f)

@[simp] lemma cochainUnitaryTransportCLM_apply {n : ℕ} (u : Fin (n + 1) → unitary M)
    (f : Cochain M n) : cochainUnitaryTransportCLM u f = cochainUnitaryTransport u f := rfl

lemma cochainUnitaryTransport_comp {n : ℕ} (u v : Fin (n + 1) → unitary M)
    (f : Cochain M n) :
    cochainUnitaryTransport u (cochainUnitaryTransport v f) =
      cochainUnitaryTransport (v * u) f := by
  ext x
  simp only [cochainUnitaryTransport_apply, Pi.mul_apply, Submonoid.coe_mul, star_mul]
  have ht : cochainUnitaryTuple v (cochainUnitaryTuple u x) = cochainUnitaryTuple (v * u) x := by
    ext i
    simp only [cochainUnitaryTuple, Pi.mul_apply, Submonoid.coe_mul, star_mul, mul_assoc]
  rw [ht]
  simp only [mul_assoc]

variable {G : Type v} [Group G] [Fintype G]

def finiteGroupCochainAverage {n : ℕ} (ρ : G →* unitary M) (f : Cochain M n) : Cochain M n :=
  (Fintype.card (Fin (n + 1) → G) : ℂ)⁻¹ •
    ∑ g : Fin (n + 1) → G, cochainUnitaryTransport (fun i => ρ (g i)) f

lemma finiteGroupCochainAverage_norm {n : ℕ} (ρ : G →* unitary M) (f : Cochain M n) :
    ‖finiteGroupCochainAverage ρ f‖ ≤ ‖f‖ := by
  let K := Fin (n + 1) → G
  have hc : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  rw [finiteGroupCochainAverage, norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card K : ℝ)⁻¹ * ((Fintype.card K : ℝ) * ‖f‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      exact (norm_sum_le _ _).trans (by
        simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
          Finset.sum_le_sum (s := Finset.univ) (fun (g : Fin (n + 1) → G) _ =>
            cochainUnitaryTransport_norm (fun i => ρ (g i)) f))
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]

lemma finiteGroupCochainAverage_invariant {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M n) (h : Fin (n + 1) → G) :
    cochainUnitaryTransport (fun i => ρ (h i)) (finiteGroupCochainAverage ρ f) =
      finiteGroupCochainAverage ρ f := by
  change cochainUnitaryTransportCLM (fun i => ρ (h i)) _ = _
  rw [finiteGroupCochainAverage, map_smul, map_sum]
  congr 1
  calc
    _ = ∑ g : Fin (n + 1) → G, cochainUnitaryTransport (fun i => ρ ((g * h) i)) f := by
      apply Finset.sum_congr rfl
      intro g _
      rw [cochainUnitaryTransportCLM_apply, cochainUnitaryTransport_comp]
      congr 1
      funext i
      exact (map_mul ρ (g i) (h i)).symm
    _ = _ := by
      apply Fintype.sum_equiv (Equiv.mulRight h) _ _
      intro g
      rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
