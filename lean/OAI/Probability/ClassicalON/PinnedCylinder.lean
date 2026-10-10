import OAI.Probability.ClassicalON.PinnedReference

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def poleSpin (τ : Bool) : Spin 3 := cylindricalSpin ⊤ τ 0

theorem cylindricalSpin_top (τ : Bool) (θ : PlanarAngle) : cylindricalSpin ⊤ τ θ=poleSpin τ := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [poleSpin,cylindricalSpin,transverseAmplitude]

def poleSystem (left right : E → V) (b : E → ℝ) (B : Set V) (t : B → Bool) : SpinSystem 3 V E :=
  ⟨left,right,b,fun v => if h : v∈B then some (poleSpin (t ⟨v,h⟩)) else none⟩

omit [Fintype E] in
theorem poleSystem_reference (left right : E → V) (b : E → ℝ) (B : Set V) (t : B → Bool) :
    (poleSystem left right b B t).reference=pinProductMeasure (sphereProbability 3) B (fun v => poleSpin (t v)) := by
  unfold SpinSystem.reference poleSystem pinProductMeasure
  congr 1
  funext v
  by_cases h : v∈B <;> simp [siteReference,h]

omit [Fintype V] in
theorem poleSystem_energy (left right : E → V) (b : E → ℝ) (B : Set V) (t : B → Bool) (s : V → Spin 3) :
    (poleSystem left right b B t).energy (fun _ => 1) s=freeSpinEnergy 3 left right b s := rfl

omit [Fintype V] [Fintype E] in
theorem glue_cylindrical (B : Set V) (t : B → Bool) (r : ↥(Bᶜ) → Amplitude)
    (τ : ↥(Bᶜ) → Bool) (θ : V → PlanarAngle) :
    glueFamily B (fun v => poleSpin (t v))
      (cylindricalConfiguration r τ (fun v : ↥(Bᶜ) => θ v))=
    cylindricalConfiguration (glueAmplitude B ⊤ r) (glueFamily B t τ) θ := by
  funext v
  by_cases hv : v∈B
  · have h1 := glueFamily_in B (fun v => poleSpin (t v))
       (cylindricalConfiguration r τ (fun v : ↥(Bᶜ) => θ v)) ⟨v,hv⟩
    rw [h1]
    change _=cylindricalSpin (glueAmplitude B ⊤ r (⟨v,hv⟩ : B)) (glueFamily B t τ (⟨v,hv⟩ : B)) (θ v)
    rw [glueAmplitude_in,glueFamily_in]
    exact (cylindricalSpin_top _ _).symm
  · have h1 := glueFamily_out B (fun v => poleSpin (t v))
       (cylindricalConfiguration r τ (fun v : ↥(Bᶜ) => θ v)) ⟨v,hv⟩
    rw [h1]
    change _=cylindricalSpin (glueAmplitude B ⊤ r (⟨v,hv⟩ : ↥(Bᶜ)))
      (glueFamily B t τ (⟨v,hv⟩ : ↥(Bᶜ))) (θ v)
    rw [glueAmplitude_out,glueFamily_out]
    rfl

omit [Fintype E] in
theorem integral_poleSystem_cylinder (left right : E → V) (b : E → ℝ) (B : Set V) (t : B → Bool)
    (f : (V → Spin 3) → ℝ) (hf : Continuous f) :
    (∫ s,f s ∂(poleSystem left right b B t).reference)=
      ∫ r,∫ τ,∫ θ,f (cylindricalConfiguration (glueAmplitude B ⊤ r) (glueFamily B t τ) θ)
        ∂planarReference ∂isingReference ∂Measure.pi (fun _ : ↥(Bᶜ) => sphericalAmplitudeLaw) := by
  rw [poleSystem_reference,integral_pinProductMeasure _ _ _ _ hf]
  have hc : Continuous (fun s : ↥(Bᶜ) → Spin 3 => f (glueFamily B (fun v => poleSpin (t v)) s)) :=
    hf.comp ((continuous_glueFamily B).comp (continuous_const.prodMk continuous_id))
  change (∫ s,f (glueFamily B (fun v => poleSpin (t v)) s) ∂freeSpinReference 3)=_
  rw [integral_freeSpinReference_cylinder _ hc]
  apply integral_congr_ae
  filter_upwards with r
  apply integral_congr_ae
  filter_upwards with τ
  have hθ : Continuous (fun θ : ↥(Bᶜ) → PlanarAngle =>
      f (glueFamily B (fun v => poleSpin (t v)) (cylindricalConfiguration r τ θ))) :=
    hc.comp (continuous_cylindricalConfiguration.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
  have he := integral_pi_restriction angleLaw B _ hθ
  change (∫ θ,f (glueFamily B (fun v => poleSpin (t v)) (cylindricalConfiguration r τ θ))
    ∂Measure.pi (fun _ : ↥(Bᶜ) => angleLaw))=_
  rw [← he]
  apply integral_congr_ae
  filter_upwards with θ
  rw [glue_cylindrical]

end ClassicalON

end

end OAI
