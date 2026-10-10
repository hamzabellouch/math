import OAI.Analysis.Mahler.RawClosedPower
import OAI.Analysis.Mahler.SourceExteriorDerivative

namespace OAI

open ContinuousAlternatingMap

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Forget continuity only after taking the actual bundled derivative. -/
def rawCovectorJet (A : E →L[ℝ] E →L[ℝ] ℂ) : E →ₗ[ℝ] E [⋀^Fin 1]→ₗ[ℝ] ℂ where
  toFun v := AlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1) (A v).toLinearMap
  map_add' v w := by ext z; simp
  map_smul' r v := by ext z; simp

def rawFirstJet (A : E →L[ℝ] E →L[ℝ] ℂ) :
    MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ := rawUncurry (rawCovectorJet A)

@[simp] lemma rawFirstJet_apply (A : E →L[ℝ] E →L[ℝ] ℂ) (v : Fin 2 → E) :
    rawFirstJet A v = A (v 0) (v 1) := rfl

def rawSecondJet (H : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℂ) :
    E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ where
  toFun v := rawFirstJet (H v)
  map_add' v w := by ext z; simp
  map_smul' r v := by ext z; simp

@[simp] lemma rawSecondJet_apply (H : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℂ)
    (v : E) (z : Fin 2 → E) : rawSecondJet H v z = H v (z 0) (z 1) := rfl

/-- Actual symmetry of the second Frechet derivative kills its full
alternatization, including the covector-evaluation slot. -/
theorem rawSecondJet_closed {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) :
    (rawPrefix (rawSecondJet (E := E) (fderiv ℝ (fderiv ℝ a) x))).alternatization = 0 := by
  apply raw_alternatization_zero_of_swap _ (i := Sum.inl (0 : Fin 1))
    (j := Sum.inr (0 : Fin 2)) (by simp)
  ext v
  simp only [MultilinearMap.domDomCongr_apply, rawPrefix_apply, rawSecondJet_apply]
  exact congrArg (fun L : E →L[ℝ] ℂ => L (v (Sum.inr 1)))
    (ha.isSymmSndFDerivAt (by norm_num) (v (Sum.inr 0)) (v (Sum.inl 0)))

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- The raw first jet alternates to the exterior derivative. -/
theorem rawFirstJet_alternatization {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) :
    (rawFirstJet (fderiv ℝ a x)).alternatization = (extDeriv (oneForm a) x).toAlternatingMap := by
  rw [rawFirstJet, alternatization_rawUncurry]
  simp only [Nat.factorial_one, one_nsmul]
  ext v
  have hev (z w : E) : fderiv ℝ (fun y => a y z) x w = fderiv ℝ a x w z := by
    simpa using congrArg (fun L : E →L[ℝ] ℂ => L w)
      (ha.hasFDerivAt.clm_apply (hasFDerivAt_const z x)).fderiv
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  change _ = extDeriv (oneForm a) x ![v 0, v 1]
  rw [extDeriv_oneForm ha, hev, hev]
  simp [AlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_two,
    rawCovectorJet, Fin.removeNth, sub_eq_add_neg]

end
end Mahler

end OAI
