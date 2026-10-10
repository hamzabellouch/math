import OAI.Dynamics.EntropyCounterexample.ConcreteInputRegularity
import OAI.Dynamics.EntropyCounterexample.MapRegisterRegularity
import OAI.Dynamics.EntropyCounterexample.ClockQuotientC1

namespace OAI

noncomputable section

namespace Problem340.Construction

open ConcreteInputRegularity

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem ambientInput_eq_baseInput_standard (L : ℝ) (hL : 2 < L)
    (i : Fin 3) (t : ℝ) (z : StandardSphere2) :
    ambientInput L i (t, z.val) =
      baseInput (concreteData L hL) i t (complexSphereHomeomorph.symm z) := by
  have h := ambientInput_modelEmbedding (concreteData L hL) rfl rfl i t
    (complexSphereHomeomorph.symm z)
  simpa only [PredictionModelBridge.modelEmbedding, Homeomorph.apply_symm_apply,
    concreteData] using h

theorem liftIco_ambientInput_eq_registerInput (L : ℝ) (hL : 2 < L)
    (i : Fin 3) (x : CounterexampleManifold 3) :
    AddCircle.liftIco (100 : ℝ) 0
      (fun t => ambientInput L i (t, (x.2 0).val)) (clockHomeomorph.symm x.1) =
      registerInputInStandardCoordinates L hL i x := by
  change AddCircle.liftIco (100 : ℝ) 0 _ _ =
    AddCircle.liftIco (100 : ℝ) 0
      (fun t => baseInput (concreteData L hL) i t (complexSphereHomeomorph.symm (x.2 0))) _
  apply congrArg (fun f : ℝ → ℂ =>
    AddCircle.liftIco (100 : ℝ) 0 f (clockHomeomorph.symm x.1))
  funext t
  exact ambientInput_eq_baseInput_standard L hL i t (x.2 0)

theorem exists_registerInput_hasLocalC1Extension :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (L : ℝ) (hL : 2 < L), B < L → ∀ i : Fin 3,
      HasLocalC1Extension (standardEmbedding 3)
        (registerInputInStandardCoordinates L hL i) := by
  obtain ⟨B, W, hB, hW, hsW, hreg⟩ := exists_contDiffOn_ambientInput_product
  refine ⟨B, hB, ?_⟩
  intro L hL hBL i
  have hs : ∀ x, ambientInput L i x ≠ 0 → x.1 ∈ Set.Ioo (0 : ℝ) 100 := by
    intro x hx
    have hh : x.1 ∈ Set.Ioo (8 : ℝ) 12 := by
      by_contra hn
      exact hx (ambientInput_eq_zero_of_not_mem L i x hn)
    constructor <;> linarith [hh.1, hh.2]
  have hp := ClockQuotient.hasLocalC1Extension_liftIco_of_strip_support_on hW
    (hreg L hBL hL i) hs
  let k : CounterexampleManifold 3 → StandardClock × W :=
    fun x => (x.1, ⟨(x.2 0).val, hsW (x.2 0).property⟩)
  let K : CounterexampleAmbient 3 → ClockAmbient × SphereAmbient :=
    fun x => (x.1, x.2 0)
  have hK : ContDiff ℝ 1 K :=
    contDiff_fst.prodMk ((contDiff_apply ℝ SphereAmbient (0 : Fin 4)).comp contDiff_snd)
  have hpull := hp.precomp_ambient (eY := standardEmbedding 3) k K hK (fun _ => rfl)
  have heq : (fun x : StandardClock × W =>
      AddCircle.liftIco (100 : ℝ) 0 (fun t => ambientInput L i (t, x.2.val))
        (clockHomeomorph.symm x.1)) ∘ k = registerInputInStandardCoordinates L hL i := by
    funext x
    exact liftIco_ambientInput_eq_registerInput L hL i x
  rwa [heq] at hpull

theorem exists_registerOutput_hasLocalC1Extension :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (L : ℝ) (hL : 2 < L), B < L → ∀ i : Fin 3,
      HasLocalC1Extension (standardEmbedding 3)
        (fun x => (registerOutputInStandardCoordinates L hL i x : SphereAmbient)) := by
  obtain ⟨B, hB, hinput⟩ := exists_registerInput_hasLocalC1Extension
  exact ⟨B, hB, fun L hL hBL i =>
    registerOutputInStandardCoordinates_hasLocalC1Extension L hL i (hinput L hL hBL i)⟩

end Problem340.Construction

end

end OAI
