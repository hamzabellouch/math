import OAI.Probability.ClassicalON.CylindricalLaw

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def freeSpinReference (n : ℕ) : Measure (V → Spin n) := Measure.pi (fun _ => sphereProbability n)
instance freeSpinReference_isProbability (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (freeSpinReference (V := V) n) := by unfold freeSpinReference; infer_instance

def freeSpinEnergy (n : ℕ) (left right : E → V) (b : E → ℝ) (s : V → Spin n) : ℝ :=
  ∑ e,b e*⟪(s (left e)).val,(s (right e)).val⟫_ℝ

omit [Fintype V] in
theorem continuous_freeSpinEnergy (n : ℕ) (left right : E → V) (b : E → ℝ) :
    Continuous (freeSpinEnergy n left right b) := by unfold freeSpinEnergy; fun_prop

def freeSpinMean (n : ℕ) (left right : E → V) (b : E → ℝ) (f : (V → Spin n) → ℝ) : ℝ :=
  weightedMean (freeSpinReference n) (fun s => Real.exp (freeSpinEnergy n left right b s)) f

def cylindricalConfiguration (r : V → Amplitude) (τ : V → Bool) (θ : V → PlanarAngle) : V → Spin 3 :=
  fun v => cylindricalSpin (r v) (τ v) (θ v)

omit [Fintype V] [Fintype E] in
theorem continuous_cylindricalConfiguration :
    Continuous (fun p : (V → Amplitude)×(V → Bool)×(V → PlanarAngle) =>
      cylindricalConfiguration p.1 p.2.1 p.2.2) := by
  apply continuous_pi
  intro v
  exact continuous_cylindricalSpin.comp
    (f := fun p : (V → Amplitude)×(V → Bool)×(V → PlanarAngle) => (p.1 v,p.2.1 v,p.2.2 v))
    (((continuous_apply v).comp continuous_fst).prodMk
      (((continuous_apply v).comp (continuous_fst.comp continuous_snd)).prodMk
        ((continuous_apply v).comp (continuous_snd.comp continuous_snd))))

omit [Fintype E] in
theorem cylindricalConfiguration_preserves : MeasurePreserving
    (fun p : (V → Amplitude)×(V → Bool)×(V → PlanarAngle) => cylindricalConfiguration p.1 p.2.1 p.2.2)
    ((Measure.pi fun _ : V => sphericalAmplitudeLaw).prod ((isingReference (V := V)).prod planarReference))
    (freeSpinReference 3) := by
  let A := MeasurableEquiv.arrowProdEquivProdArrow Amplitude (Bool×PlanarAngle) V
  let B := MeasurableEquiv.arrowProdEquivProdArrow Bool PlanarAngle V
  have hA := (measurePreserving_arrowProdEquivProdArrow Amplitude (Bool×PlanarAngle) V
    (fun _ => sphericalAmplitudeLaw) (fun _ => cylinderLaw)).symm A
  have hB := (measurePreserving_arrowProdEquivProdArrow Bool PlanarAngle V
    (fun _ => signLaw) (fun _ => angleLaw)).symm B
  have h1 := (MeasurePreserving.id (Measure.pi fun _ : V => sphericalAmplitudeLaw)).prod hB
  have h2 := hA.comp h1
  have h3 := measurePreserving_pi (fun _ : V => sphericalAmplitudeLaw.prod cylinderLaw)
    (fun _ => sphereProbability 3) (fun _ => cylindricalSpin_preserves)
  exact h3.comp h2

omit [Fintype E] in
theorem integral_freeSpinReference_cylinder (f : (V → Spin 3) → ℝ) (hf : Continuous f) :
    (∫ s,f s ∂freeSpinReference 3)=
      ∫ r,∫ τ,∫ θ,f (cylindricalConfiguration r τ θ) ∂planarReference ∂isingReference
        ∂Measure.pi (fun _ : V => sphericalAmplitudeLaw) := by
  let : BorelSpace ((V → Amplitude) × (V → Bool) × (V → PlanarAngle)) := Prod.borelSpace
  have hc : Continuous (fun p : (V → Amplitude)×(V → Bool)×(V → PlanarAngle) =>
      f (cylindricalConfiguration p.1 p.2.1 p.2.2)) := hf.comp continuous_cylindricalConfiguration
  rw [← cylindricalConfiguration_preserves.map_eq,
    integral_map continuous_cylindricalConfiguration.measurable.aemeasurable hf.aestronglyMeasurable,
    integral_prod _ (compact_integrable hc)]
  apply integral_congr_ae
  filter_upwards with r
  have hr : Continuous (fun p : (V → Bool)×(V → PlanarAngle) => f (cylindricalConfiguration r p.1 p.2)) :=
    hc.comp (continuous_const.prodMk continuous_id)
  exact integral_prod _ (compact_integrable hr)

omit [Fintype V] [Fintype E] in
theorem cylindricalSpin_inner (r q : Amplitude) (τ υ : Bool) (θ φ : PlanarAngle) :
    ⟪(cylindricalSpin r τ θ).val,(cylindricalSpin q υ φ).val⟫_ℝ=
      (r:ℝ)*(q:ℝ)*(signValue τ*signValue υ)+
        transverseAmplitude r*transverseAmplitude q*planarCos (θ-φ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,Fin.sum_univ_succ,Fin.isValue,cylindricalSpin,
    WithLp.ofLp_toLp,Matrix.cons_val_zero,Matrix.cons_val_succ,star_trivial,Finset.univ_eq_empty,
    Finset.sum_empty,add_zero]
  simp only [planarCos,planarSin,sub_eq_add_neg,planarCharacter_add,planarCharacter_neg,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

omit [Fintype V] in
theorem cylindricalConfiguration_energy (left right : E → V) (b : E → ℝ)
    (r : V → Amplitude) (τ : V → Bool) (θ : V → PlanarAngle) :
    freeSpinEnergy 3 left right b (cylindricalConfiguration r τ θ)=
      edgeHamiltonian (isingEnergy left right) (amplitudeCoupling left right b (fun v => (r v:ℝ))) τ+
      edgeHamiltonian (planarEnergy left right) (amplitudeCoupling left right b (fun v => transverseAmplitude (r v))) θ := by
  unfold freeSpinEnergy edgeHamiltonian cylindricalConfiguration
  simp_rw [cylindricalSpin_inner]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  unfold amplitudeCoupling isingEnergy planarEnergy
  ring

end ClassicalON

end

end OAI
