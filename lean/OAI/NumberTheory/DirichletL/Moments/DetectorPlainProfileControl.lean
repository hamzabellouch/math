import OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainProfileControl
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorDictionary
open CenteredMomentFiniteProfileExceptional

theorem paired_control (S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0<C ∧ ∀reverse:Bool,∀j k:ℕ,j+k≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀t:ℝ,
      (detectorProfiles reverse j k σ t).control S ^2≤C*(1+‖t‖)^J:=by
  obtain ⟨J,C,hC,h⟩:=detectorSchwartz_uniform S
  refine ⟨4*J,C^4,by positivity,?_⟩
  intro reverse j k hjk σ hσ t
  have hj:=h reverse j (by omega) σ hσ t
  have hk:=h reverse k (by omega) σ hσ t
  have hp:(detectorProfiles reverse j k σ t).control S≤(C*(1+‖t‖)^J)^2:=by
    simpa only [detectorProfiles,Profiles.control,sourceControl,Fin.zero_eta,ite_true,
      show ¬((1:Fin 2)=0) by decide,ite_false,pow_two] using
      mul_le_mul hj hk (sourceControl_nonneg S (detectorSchwartz reverse k σ t)) (by positivity)
  have hs:=pow_le_pow_left₀ (Profiles.control_nonneg _ _) hp 2
  calc
    _≤((C*(1+‖t‖)^J)^2)^2:=hs
    _=C^4*(1+‖t‖)^(4*J):=by
      rw [←pow_mul,mul_pow,←pow_mul]
      congr 2 ; omega

theorem source_height_factor (S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0<C ∧ ∀degree:ℕ,∀reverse:Bool,∀j k:ℕ,j+k≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀height t:ℝ,0≤height → |t|≤height →
      (detectorProfiles reverse j k σ t).control S ^2*(1+|(0:ℝ)|+height)^degree
        ≤C*(1+height)^(J+degree):=by
  obtain ⟨J,C,hC,h⟩:=paired_control S
  refine ⟨J,C,hC,?_⟩
  intro degree reverse j k hjk σ hσ height t hh ht
  have hb:(detectorProfiles reverse j k σ t).control S ^2≤C*(1+height)^J:=by
    apply (h reverse j k hjk σ hσ t).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply pow_le_pow_left₀ (by positivity)
    simpa only [Real.norm_eq_abs] using add_le_add le_rfl ht
  simpa only [abs_zero,add_zero,pow_add,mul_assoc] using
    mul_le_mul_of_nonneg_right hb (pow_nonneg (by linarith:0≤1+height) degree)

end SevenEighths.CenteredMomentDetectorPlainProfileControl

end

end OAI
