import OAI.Analysis.Mahler.RawClosedProduct

namespace OAI

namespace Mahler
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def rawPowerVariation (B : MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ)
    (DB : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ) :
    (k : ℕ) → E →ₗ[ℝ] MultilinearMap ℝ (fun _ : WedgePowerSlots k => E) ℂ
  | 0 => 0
  | k+1 => rawProductVariation B DB (rawPower B k) (rawPowerVariation B DB k)

/-- All derivative placements in the k-fold product vanish after
alternation when the actual two-form derivative is closed. -/
theorem rawPowerVariation_closed (B : MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ)
    (DB : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ)
    (hB : (rawPrefix DB).alternatization = 0) (k : ℕ) :
    (rawPrefix (rawPowerVariation B DB k)).alternatization = 0 := by
  induction k with
  | zero =>
    have hz : rawPrefix (rawPowerVariation B DB 0) = 0 := by ext v; rfl
    rw [hz, map_zero]
  | succ k ih =>
    rw [show wedgePowerSlotsDecidableEq (k+1) =
      (inferInstance : DecidableEq (Fin 2 ⊕ WedgePowerSlots k)) from Subsingleton.elim _ _]
    exact rawPrefix_productVariation_closed B DB (rawPower B k)
      (rawPowerVariation B DB k) hB ih

/-- The uncurried derivative of a covector field, before alternation. -/
def rawCovectorVariation (Da : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) :
    E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin 1 => E) ℂ where
  toFun v := rawCovector (Da v)
  map_add' v w := by ext z; simp
  map_smul' r v := by ext z; simp

/-- Full raw product-rule identity underlying d(alpha wedge B^k), with
all right-factor contributions proved zero and the surviving order explicit. -/
theorem rawBoundaryVariation_closed (a : E →ₗ[ℝ] ℂ)
    (Da : E →ₗ[ℝ] E →ₗ[ℝ] ℂ)
    (B : MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ)
    (DB : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ)
    (hB : (rawPrefix DB).alternatization = 0) (k : ℕ) :
    (rawPrefix (rawProductVariation (rawCovector a) (rawCovectorVariation Da)
      (rawPower B k) (rawPowerVariation B DB k))).alternatization =
      (wedge (rawPrefix (rawCovectorVariation Da)).alternatization
        (wedgePower B.alternatization k)).domDomCongr
          (Equiv.sumAssoc (Fin 1) (Fin 1) (WedgePowerSlots k)) := by
  rw [rawPrefix_productVariation_right_closed _ _ _ _ (rawPowerVariation_closed B DB hB k),
    rawPower_alternatization]

end
end Mahler

end OAI
