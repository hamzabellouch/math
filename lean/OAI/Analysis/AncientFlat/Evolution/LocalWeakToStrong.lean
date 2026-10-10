import OAI.Analysis.AncientFlat.Kernel.ClassicalBase
import OAI.Analysis.AncientFlat.Evolution.WeakToStrong

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction ContDiff
namespace ParametrixVolterra
open StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T : ℝ}

def clampTime (a b : ℝ) (ha : 0<a) (hab : a≤b) (hb : b≤T) (r : ℝ) : Time T :=
  ⟨(projIcc a b hab r).val, ha.trans_le (projIcc a b hab r).property.1,
    (projIcc a b hab r).property.2.trans hb⟩

lemma continuous_clampTime (a b : ℝ) (ha : 0<a) (hab : a≤b) (hb : b≤T) :
    Continuous (clampTime a b ha hab hb) :=
  (continuous_subtype_val.comp continuous_projIcc).subtype_mk _

lemma clampTime_of_mem (a b : ℝ) (ha : 0<a) (hab : a≤b) (hb : b≤T)
    (t : Time T) (ht : t.val ∈ Icc a b) : clampTime a b ha hab hb t.val = t := by
  apply Subtype.ext
  change (projIcc a b hab t.val).val = t.val
  rw [projIcc_of_mem hab ht]

lemma hasDerivAt_of_weak_on_time (u : ℝ → V →ᵇ ℂ) (F : Time T → V →ᵇ ℂ)
    (hu : ContinuousOn u (Icc 0 T)) (hF : Continuous F)
    (hw : ∀ (φ : V → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      ∀ (t : Time T), t.val<T →
      HasDerivAt (fun s => TestSeparation.pairCLM φ
        (hφ.continuous.integrable_of_hasCompactSupport hc) (u s))
        (TestSeparation.pairCLM φ (hφ.continuous.integrable_of_hasCompactSupport hc) (F t)) t.val)
    (t : Time T) (ht : t.val<T) : HasDerivAt u (F t) t.val := by
  let a := t.val/2
  let b := (t.val+T)/2
  have ha : 0<a := half_pos t.property.1
  have hat : a<t.val := by dsimp [a]; linarith [t.property.1]
  have htb : t.val<b := by dsimp [b]; linarith
  have hbT : b<T := by dsimp [b]; linarith
  have hab : a≤b := (hat.trans htb).le
  let κ := clampTime a b ha hab hbT.le
  have hκ : Continuous κ := continuous_clampTime a b ha hab hbT.le
  have hκt : κ t.val = t := clampTime_of_mem a b ha hab hbT.le t ⟨hat.le,htb.le⟩
  have h := TestSeparation.hasDerivAt_of_weak_derivative u (fun r => F (κ r)) a b t.val
    ⟨hat,htb⟩ (hu.mono (Icc_subset_Icc ha.le hbT.le)) (hF.comp hκ) (by
      intro φ hφ hc r hr
      let tr : Time T := ⟨r,ha.trans hr.1,hr.2.le.trans hbT.le⟩
      have hκr : κ r = tr := clampTime_of_mem a b ha hab hbT.le tr ⟨hr.1.le,hr.2.le⟩
      rw [hκr]
      exact hw φ hφ hc tr (hr.2.trans hbT))
  simpa only [hκt] using h
end ParametrixVolterra

end

end OAI
