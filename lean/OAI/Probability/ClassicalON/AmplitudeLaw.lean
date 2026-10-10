import OAI.Probability.ClassicalON.FinFKG

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory Set
namespace ClassicalON

abbrev Amplitude := Set.Icc (0 : ℝ) 1

def amplitudeReference : Measure Amplitude := volume.comap Subtype.val

instance amplitudeReference_isProbability : IsProbabilityMeasure amplitudeReference := by
  constructor
  rw [amplitudeReference,comap_subtype_coe_apply measurableSet_Icc volume .univ]
  simp only [Set.image_univ,Subtype.range_val]
  norm_num

def transverseAmplitude (r : Amplitude) : ℝ := Real.sqrt (1-(r:ℝ)^2)

theorem continuous_transverseAmplitude : Continuous transverseAmplitude := by
  unfold transverseAmplitude; fun_prop

theorem transverseAmplitude_nonneg (r : Amplitude) : 0 ≤ transverseAmplitude r := Real.sqrt_nonneg _

theorem transverseAmplitude_antitone : Antitone transverseAmplitude := by
  intro r s hrs
  apply Real.sqrt_le_sqrt
  have hr := r.property.1
  have hs := s.property.1
  change (r : ℝ) ≤ s at hrs
  nlinarith

theorem transverseAmplitude_inf (r s : Amplitude) :
    transverseAmplitude (r⊓s)=max (transverseAmplitude r) (transverseAmplitude s) := by
  rcases le_total r s with h | h
  · rw [inf_eq_left.mpr h,max_eq_left (transverseAmplitude_antitone h)]
  · rw [inf_eq_right.mpr h,max_eq_right (transverseAmplitude_antitone h)]

theorem transverseAmplitude_sup (r s : Amplitude) :
    transverseAmplitude (r⊔s)=min (transverseAmplitude r) (transverseAmplitude s) := by
  rcases le_total r s with h | h
  · rw [sup_eq_right.mpr h,min_eq_right (transverseAmplitude_antitone h)]
  · rw [sup_eq_left.mpr h,min_eq_left (transverseAmplitude_antitone h)]

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def isingAmplitudePartition (left right : E → V) (b : E → ℝ) (r : V → Amplitude) : ℝ :=
  amplitudePartition isingReference (isingEnergy left right) left right b (fun v => (r v : ℝ))

def planarAmplitudePartition (left right : E → V) (b : E → ℝ) (r : V → Amplitude) : ℝ :=
  amplitudePartition planarReference (planarEnergy left right) left right b (fun v => transverseAmplitude (r v))

def amplitudeDensity (left right : E → V) (b : E → ℝ) (r : V → Amplitude) : ℝ :=
  isingAmplitudePartition left right b r*planarAmplitudePartition left right b r

theorem isingAmplitudePartition_pos (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    0 < isingAmplitudePartition left right b r :=
  amplitudePartition_pos _ _ _ _ _ (fun _ => continuous_of_discreteTopology) _

theorem planarAmplitudePartition_pos (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    0<planarAmplitudePartition left right b r :=
  amplitudePartition_pos _ _ _ _ _ (continuous_planarEnergy _ _) _

theorem continuous_isingAmplitudePartition (left right : E → V) (b : E → ℝ) :
    Continuous (isingAmplitudePartition left right b) := by
  apply (continuous_amplitudePartition isingReference (isingEnergy left right) left right b
    (fun _ => continuous_of_discreteTopology)).comp
  fun_prop

theorem continuous_planarAmplitudePartition (left right : E → V) (b : E → ℝ) :
    Continuous (planarAmplitudePartition left right b) := by
  apply (continuous_amplitudePartition planarReference (planarEnergy left right) left right b
    (continuous_planarEnergy _ _)).comp
  exact continuous_pi (fun v => continuous_transverseAmplitude.comp (continuous_apply v))

theorem amplitudeDensity_pos (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    0<amplitudeDensity left right b r :=
  mul_pos (isingAmplitudePartition_pos _ _ _ _) (planarAmplitudePartition_pos _ _ _ _)

theorem continuous_amplitudeDensity (left right : E → V) (b : E → ℝ) :
    Continuous (amplitudeDensity left right b) :=
  (continuous_isingAmplitudePartition _ _ _).mul (continuous_planarAmplitudePartition _ _ _)

theorem isingAmplitudePartition_logSupermodular (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0 ≤ b e) : LogSupermodular (isingAmplitudePartition left right b) := by
  intro r s
  exact amplitudePartition_supermodular isingReference (isingEnergy left right) left right b
    (fun _ => continuous_of_discreteTopology) (ising_edge_covariance_nonneg left right)
    (ising_reference_mean_nonneg left right) hb (fun v => (r v).property.1) (fun v => (s v).property.1)

theorem planarAmplitudePartition_logSupermodular (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0 ≤ b e) : LogSupermodular (planarAmplitudePartition left right b) := by
  intro r s
  have hh := amplitudePartition_supermodular planarReference (planarEnergy left right) left right b
    (continuous_planarEnergy _ _) (planar_edge_covariance_nonneg left right)
    (planar_reference_mean_nonneg left right) hb
    (fun v => transverseAmplitude_nonneg (r v)) (fun v => transverseAmplitude_nonneg (s v))
  have hmin : (fun v => transverseAmplitude ((r⊓s) v))=
      ((fun v => transverseAmplitude (r v))⊔(fun v => transverseAmplitude (s v))) := by
    funext v; exact transverseAmplitude_inf _ _
  have hmax : (fun v => transverseAmplitude ((r⊔s) v))=
      ((fun v => transverseAmplitude (r v))⊓(fun v => transverseAmplitude (s v))) := by
    funext v; exact transverseAmplitude_sup _ _
  unfold planarAmplitudePartition
  rw [hmin,hmax]
  simpa only [mul_comm] using hh

theorem amplitudeDensity_logSupermodular (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0 ≤ b e) : LogSupermodular (amplitudeDensity left right b) := by
  intro r s
  have hi := isingAmplitudePartition_logSupermodular left right b hb r s
  have hp := planarAmplitudePartition_logSupermodular left right b hb r s
  have hh := mul_le_mul hi hp
    (mul_nonneg (planarAmplitudePartition_pos _ _ _ _).le (planarAmplitudePartition_pos _ _ _ _).le)
    (mul_nonneg (isingAmplitudePartition_pos _ _ _ _).le (isingAmplitudePartition_pos _ _ _ _).le)
  unfold amplitudeDensity
  nlinarith only [hh]

theorem amplitude_associated (left right : E → V) (b : E → ℝ) (hb : ∀ e,0 ≤ b e) :
    ContinuousAssociated (Measure.pi (fun _ : V => amplitudeReference)) (amplitudeDensity left right b) :=
  continuousFKG_pi amplitudeReference _ (continuous_amplitudeDensity _ _ _)
    (amplitudeDensity_pos _ _ _) (amplitudeDensity_logSupermodular _ _ _ hb)

theorem amplitude_associated_any (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    (left right : E → V) (b : E → ℝ) (hb : ∀ e,0 ≤ b e) :
    ContinuousAssociated (Measure.pi (fun _ : V => μ)) (amplitudeDensity left right b) :=
  continuousFKG_pi μ _ (continuous_amplitudeDensity _ _ _)
    (amplitudeDensity_pos _ _ _) (amplitudeDensity_logSupermodular _ _ _ hb)

end ClassicalON

end

end OAI
