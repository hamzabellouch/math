import OAI.Probability.IsingPerceptron.CascadeFreshMoments

namespace OAI

/-! Finite scalar overlap blocks of the rounded cascades converge to
the prescribed GG law. This is the overlap input for jointly marked
cavity tests, with every replica retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_cascade_spin_block_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Ω → RealArray) (hB : Measurable B)
    (hGG : HasGhirlandaGuerra B μ)
    (hG : ∀ᵐ x ∂μ, GramDiagonal 1 (B x))
    (hU : ∀ᵐ x ∂μ, IsUltrametricArray (B x))
    (q : ℝ → ℝ) (hq : Monotone q) (hb : ∀ u, q u ∈ Icc (0 : ℝ) 1)
    (hp : μ.map (fun x => B x 0 1) = unitUniform.map q)
    (r : ℕ) (F : (Fin r → Fin r → ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, F (arrayBlock spinArray r x)
      ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage q n) : Measure JointArray))
      atTop (𝓝 (∫ x, F (arrayBlock B r x) ∂μ)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ν, ms, hms, hν⟩ := jointArrayLaw_subsequence
    (fun k => cascadeCompactLaw (ns k) (uniformExponent (ns k)) (uniformCellAverage q (ns k)))
  have hν' : Tendsto (fun k => cascadeCompactLaw (ns (ms k)) (uniformExponent (ns (ms k)))
      (uniformCellAverage q (ns (ms k)))) atTop (𝓝 ν) := hν
  have hgeom := cascadeCompact_limit_geometry
    (fun k => uniformCellAverage_monotone hq hb (ns (ms k)))
    (fun k => (uniformCellAverage_mem hq hb (ns (ms k)) 0).1)
    (fun k => (uniformCellAverage_mem hq hb (ns (ms k)) (ns (ms k))).2) hν'
  have hGGν : HasGhirlandaGuerra spinArray (ν : Measure JointArray) :=
    (cascadeCompact_limit_GG (fun k => uniformExponent_cascade (ns (ms k))) hν').real_map
      (f := fun x => x.1.1) (by fun_prop)
  have hpair := cascadeCompact_limit_pairLaw hq hb (hns.comp hms.tendsto_atTop) hν'
  have hblock := gg_blockLaw_unique continuous_spinArray.measurable hB hGGν hGG
    (hgeom.1.mono (fun _ h => h.symm)) (hG.mono (fun _ h => h.symm)) hgeom.2 hU
    (hgeom.1.mono (fun _ h => h.2)) (hG.mono (fun _ h => h.2)) (hpair.trans hp.symm)
  have he : (∫ x, F (arrayBlock spinArray r x) ∂(ν : Measure JointArray)) =
      ∫ x, F (arrayBlock B r x) ∂μ := by
    have hi := congrArg (fun M => ∫ z, F z ∂M) (hblock r)
    dsimp only [blockLaw] at hi
    rw [integral_map (measurable_arrayBlock continuous_spinArray.measurable r).aemeasurable
      F.continuous.aestronglyMeasurable, integral_map (measurable_arrayBlock hB r).aemeasurable
      F.continuous.aestronglyMeasurable] at hi
    exact hi
  refine ⟨ms, ?_⟩
  rw [← he]
  let G : JointArray →ᵇ ℝ := F.compContinuous
    ⟨arrayBlock spinArray r, by unfold arrayBlock spinArray; fun_prop⟩
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν' G

end InvariantIsing

end

end OAI
