import OAI.NumberTheory.DukePrimeDegree.Entropy.InfiniteLabelEntropy

namespace OAI

/-! # Conditional probabilities on decreasing positive-mass fibers -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem condExp_infinite_label_probability
    {S T : Type*} [mS : MeasurableSpace S] [mT : MeasurableSpace T]
    [StandardBorelSpace T] [Nonempty T]
    (ρ : Measure (S × T)) [IsFiniteMeasure ρ]
    {M : ℕ} {P : S × T → Fin M} (hP : Measurable P)
    {k : ℕ → ℕ} (Q : ∀ n, S × T → Fin (k n)) (hQ : ∀ n, Measurable (Q n))
    (hmono : Monotone (fun n => transverseLabelSigma (Q n)))
    (hdec : ∀ z, Antitone (fun n => labelFiber (Q n) z))
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (⋂ n, labelFiber (Q n) z) ≠ 0)
    (a : Fin M) :
    ρ[({z | P z=a}.indicator (fun _ => (1:ℝ))) | ⨆ n, transverseLabelSigma (Q n)] =ᵐ[ρ]
      fun z => ((anchorNormalize (ρ.condKernel z.1) (⋂ n, labelFiber (Q n) z)).restrict
        (⋂ n, labelFiber (Q n) z)).real {t | P (z.1,t)=a} := by
  let g : S × T → ℝ := {z | P z=a}.indicator (fun _ => 1)
  let ℱ : Filtration ℕ (mS.prod mT) :=
    ⟨fun n => transverseLabelSigma (Q n),hmono,
      fun n => (measurable_fst.prodMk (hQ n)).comap_le⟩
  have hmart := MeasureTheory.tendsto_ae_condExp (μ := ρ) (ℱ := ℱ) g
  have heq n : ρ[g | ℱ n] =ᵐ[ρ] fun z =>
      ((anchorNormalize (ρ.condKernel z.1) (labelFiber (Q n) z)).restrict
        (labelFiber (Q n) z)).real {t | P (z.1,t)=a} := by
    filter_upwards [condExp_transverse_label_probability ρ hP (hQ n) a,
      finiteLabelLift_condKernel ρ (hQ n)] with z hz hk
    exact hz.trans (congrArg (fun ν => ν.real {t | P (z.1,t)=a}) hk.2)
  filter_upwards [hmart,ae_all_iff.mpr heq,hpos] with z hm he hp
  have ht := normalized_restriction_probability_tendsto (ρ.condKernel z.1)
    (fun n => labelFiber (Q n) z)
    (fun n => measurableSet_eq_fun ((hQ n).comp measurable_prodMk_left) measurable_const)
    (hdec z) hp {t | P (z.1,t)=a}
    ((hP.comp measurable_prodMk_left) (measurableSet_singleton a))
  have hm' : Tendsto
      (fun n => ((anchorNormalize (ρ.condKernel z.1) (labelFiber (Q n) z)).restrict
        (labelFiber (Q n) z)).real {t | P (z.1,t)=a}) atTop
      (𝓝 ((ρ[g | ⨆ n, ℱ n]) z)) := by
    simpa only [he] using hm
  exact tendsto_nhds_unique hm' ht

end DukePrimeDegree

end

end OAI
