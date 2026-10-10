import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExtremeFlowAffinity
import OAI.GroupTheory.PolycyclicRecognition.Algebra.HorizontalGeneratorChange
import OAI.GroupTheory.PolycyclicRecognition.Algebra.HorizontalExtremeSpanning
import OAI.GroupTheory.PolycyclicRecognition.Analysis.GlobalProfileAffinity

namespace OAI

/-! # Measurable horizontal labels and segment volume force a single affine profile -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory Module
open scoped NNReal

theorem affine_of_horizontal_labels
    {H V W I B K J L : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B]
    [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    {c : ℕ} (a : DynkinCoefficients c 2) (br : V →L[ℝ] V →L[ℝ] V)
    (hbr : IsLieBracket br) (hg : PolynomialGroupLaws (dynkinProduct a br))
    (hc : ExponentialConjugationLaw (dynkinProduct a br) br)
    (D : H →L[ℝ] V) (X : K → H) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma K)
    (hw₀ : ∀ j, evalBilinearWord br (fun k => D (X k)) (w₀ j) = b₀ j)
    (μ : Measure (PolynomialCoordinateGroup (dynkinProduct a br) hg))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Ω : Set (PolynomialCoordinateGroup (dynkinProduct a br) hg))
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hne : Ω.Nonempty)
    (f : PolynomialCoordinateGroup (dynkinProduct a br) hg → W) (hf : Continuous f)
    (π : PolynomialCoordinateGroup (dynkinProduct a br) hg →* Multiplicative W)
    (p : V →L[ℝ] W) (hp : Function.Surjective (p.comp D))
    (hπExp : ∀ v, (π (PolynomialCoordinateGroup.exp _ hg v)).toAdd = p v)
    (P : SupportDatum W I B) (hweights : ∀ i, P.weight i ≠ 0)
    (σ : I → Bool) (hσ : (weightChamber (fun i => (P.weight i).toContinuousLinearMap) σ).Nonempty)
    (label : PolynomialCoordinateGroup (dynkinProduct a br) hg → L)
    (hlabel : Measurable label) (A : L → templateSymmetryGroup P)
    (hbase : ∀ v : H, ∀ᵐ g ∂μ, g ∈ Ω →
      HasDerivAt (fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • D v)))
        ((A (label g)).val (p (D v))) 0)
    (C : H → ℝ≥0)
    (hlip : ∀ v g, LipschitzOnWith (C v)
      (fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • D v)))
      {t | g * PolynomialCoordinateGroup.exp _ hg (t • D v) ∈ Ω})
    (hvol : ∀ v (T : ℝ), 0 < T →
      ∀ g ∈ flowLineBase Ω (PolynomialCoordinateGroup.exp _ hg) (D v) T,
        T * P.segmentSupport (p (D v)) ≤ P.templateSupport
          ((fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • D v))) '' Icc 0 T)) :
    ∃ l b, ∀ g ∈ Ω, f g = (A l).val ((π g).toAdd) + b := by
  let G := PolynomialCoordinateGroup (dynkinProduct a br) hg
  let e : V ≃ₜ G := PolynomialCoordinateGroup.expHomeomorph _ hg
  let : IsTopologicalGroup G := PolynomialCoordinateGroup.isTopologicalGroup _ hg
    (continuous_dynkinProduct a (fun _ => br) Prod.fst Prod.snd
      continuous_const continuous_fst continuous_snd)
  let : T2Space G := inferInstanceAs (T2Space V)
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace V)
  let : SecondCountableTopology G := inferInstanceAs (SecondCountableTopology V)
  let : TopologicalSpace.PseudoMetrizableSpace G :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace V)
  have he_apply (v : V) : e v = PolynomialCoordinateGroup.exp _ hg v := rfl
  let eH : H → G := fun v => e (D v)
  have heH : Continuous eH := e.continuous.comp D.continuous
  have he0 : eH 0 = 1 := by simp only [eH, map_zero, he_apply, PolynomialCoordinateGroup.exp_zero]
  have headd (v : H) (s t : ℝ) : eH ((s + t) • v) = eH (s • v) * eH (t • v) := by
    simpa only [eH, he_apply, map_smul] using PolynomialCoordinateGroup.exp_add_smul _ hg (D v) s t
  obtain ⟨S, hS, hdir⟩ := exists_finite_spanning_horizontal_directions (p.comp D) hp
    (fun i => (P.weight i).toContinuousLinearMap) σ P.separates hσ
  let Y : S → H := fun v => v.val
  have hY : Submodule.span ℝ (range Y) = ⊤ := by
    have heq : range Y = (S : Set H) := by ext v; simp [Y]
    rwa [heq]
  obtain ⟨b₁, w₁, hw₁⟩ := exists_word_basis_of_spanning_horizontal br hbr D X b₀ w₀ hw₀ Y hY
  have hps : Function.Surjective p := by
    intro w
    obtain ⟨v, hv⟩ := hp w
    exact ⟨D v, hv⟩
  apply global_affine_of_finite_derivative_and_flow_lines a br hbr hg hc
    (fun v : S => D (Y v)) b₁ w₁ hw₁ μ Ω hΩ hconn hne f hf.continuousOn π p hps
    hπExp (fun l => (A l).val.toLinearMap.toContinuousLinearMap)
  · intro v T hT
    have hb (u : H) : ∀ᵐ g ∂μ, g ∈ Ω →
        HasDerivAt (fun t : ℝ => f (g * eH (t • u)))
          ((A (label g)).val ((p.comp D) u)) 0 := by
      simpa only [eH, he_apply, map_smul,
        ContinuousLinearMap.comp_apply] using hbase u
    have hl (u : H) (g : G) : LipschitzOnWith (C u)
        (fun t : ℝ => f (g * eH (t • u))) {t | g * eH (t • u) ∈ Ω} := by
      simpa only [eH, he_apply, map_smul] using hlip u g
    have hv (u : H) (T : ℝ) (hT : 0 < T) : ∀ g ∈ flowLineBase Ω eH u T,
        T * P.segmentSupport ((p.comp D) u) ≤
          P.templateSupport ((fun t : ℝ => f (g * eH (t • u))) '' Icc 0 T) := by
      simpa only [eH, he_apply, flowLineBase, map_smul,
        ContinuousLinearMap.comp_apply] using hvol u T hT
    have hline := P.flowLine_affine_in_extreme_or_kernel_direction hweights μ eH heH he0
      headd (p.comp D) hp f hf Ω hΩ label hlabel A hb C hl hv σ hσ (Y v)
      (hdir v.val v.property) hT
    simpa only [eH, he_apply, flowLineBase, flowLineSlope,
      map_smul] using hline
  · have hall : ∀ᵐ g ∂μ, ∀ v : S, g ∈ Ω →
        HasDerivAt (fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • D (Y v))))
          ((A (label g)).val (p (D (Y v)))) 0 := ae_all_iff.mpr (fun v => hbase (Y v))
    filter_upwards [hall] with g hg hgΩ
    exact ⟨label g, fun v => hg v hgΩ⟩

end PolycyclicRecognition

end

end OAI
