import OAI.Probability.InvariantIsing.Fields.CascadeSeedTree

namespace OAI

/-! The full retained finite vector cascade is realized by ancestor-dependent seeds. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal ENNReal
namespace InvariantIsing

theorem cascadeSeedTree_retained_law {ι : Type} [Fintype ι]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (ι → ℝ))
    (c : ℕ → (ι → ℝ) × (ι → ℝ) → ℝ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hc : ∀ i, Measurable (c i)) (hψ : ∀ i, Measurable (Function.uncurry (ψ i)))
    (hcpos : ∀ i z a, 0 < c i (z,a))
    (hm : ∀ i z, (∫⁻ a, ENNReal.ofReal (c i (z,a)^b i) ∂(μ i : Measure (ι → ℝ))) = 1)
    (hseed : ∀ i z, volume.map (ψ i z) = (μ i : Measure (ι → ℝ)).withDensity
      (fun a => ENNReal.ofReal (c i (z,a)^b i))) (z : ι → ℝ) :
    (noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) :
      Measure (NoiseTree unitInterval n)).map (cascadeSeedTree n b ψ z) =
    (noiseCascadeLaw (ι → ℝ) n b μ : Measure (NoiseTree (ι → ℝ) n)).map
      (noiseTreeKeep n b μ c (fun _ p => p.1+p.2) z) := by
  induction n generalizing b μ c ψ z with
  | zero =>
    change (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit) =
      (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit)
    rfl
  | succ n ih =>
    let bs := fun j => b (j+1)
    let ms := fun j => μ (j+1)
    let cs := fun j => c (j+1)
    let ps := fun j => ψ (j+1)
    let Q : Measure (NoiseTree unitInterval n) :=
      noiseCascadeLaw unitInterval n bs (fun _ => cascadeSeedLaw)
    let P : Measure (NoiseTree (ι → ℝ) n) := noiseCascadeLaw (ι → ℝ) n bs ms
    let ρ : Measure (ι → ℝ) := (μ 0 : Measure (ι → ℝ)).withDensity
      (fun a => ENNReal.ofReal (c 0 (z,a)^b 0))
    let : IsProbabilityMeasure ρ := ⟨by
      change ((μ 0 : Measure (ι → ℝ)).withDensity _ ) Set.univ = 1
      rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
      exact hm 0 z⟩
    let : IsProbabilityMeasure Q := by
      change IsProbabilityMeasure (noiseCascadeLaw unitInterval n bs (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n))
      infer_instance
    let : IsProbabilityMeasure P := by
      change IsProbabilityMeasure (noiseCascadeLaw (ι → ℝ) n bs ms : Measure (NoiseTree (ι → ℝ) n))
      infer_instance
    let G : (ι → ℝ) × NoiseTree unitInterval n → NoiseTree (ι → ℝ) n :=
      fun p => cascadeSeedTree n bs ps (z+p.1) p.2
    let H : (ι → ℝ) × NoiseTree (ι → ℝ) n → NoiseTree (ι → ℝ) n :=
      fun p => noiseTreeKeep n bs ms cs (fun _ p => p.1+p.2) (z+p.1) p.2
    have hG : Measurable G := (measurable_cascadeSeedTree n bs ps (fun i => hψ (i+1))).comp
      ((measurable_const.add measurable_fst).prodMk measurable_snd)
    have hH : Measurable H :=
      (measurable_noiseTreeKeep n bs ms (fun i => hc (i+1))
        (fun _ => measurable_fst.add measurable_snd)).comp
          ((measurable_const.add measurable_fst).prodMk measurable_snd)
    have hsub a : Q.map (fun q => G (a,q)) = P.map (fun p => H (a,p)) :=
      ih bs ms cs ps (fun i => hc (i+1)) (fun i => hψ (i+1))
        (fun i => hcpos (i+1)) (fun i => hm (i+1)) (fun i => hseed (i+1)) (z+a)
    have hf : Measurable (ψ 0 z) := (hψ 0).comp (measurable_const.prodMk measurable_id)
    have hlaw : (cascadeSeedLaw : Measure unitInterval).map (ψ 0 z) = ρ := hseed 0 z
    have hpair := ancestor_fiber_map_product (cascadeSeedLaw : Measure unitInterval) ρ Q P hf hlaw hG hH hsub
    have hmap : Measurable (fun p : unitInterval × NoiseTree unitInterval n =>
        (ψ 0 z p.1,G (ψ 0 z p.1,p.2))) :=
      (hf.comp measurable_fst).prodMk (hG.comp ((hf.comp measurable_fst).prodMk measurable_snd))
    rw [cascadeSeedTree_law_succ n b ψ hψ z,
      noiseTreeKeep_law_succ n b μ (u := fun (_ : ℕ) (p : (ι → ℝ) × (ι → ℝ)) => p.1+p.2)
        hc (fun _ => measurable_fst.add measurable_snd) hcpos z]
    apply poissonLaw_congr
    change (((powerIntensity (b 0)).prod ((cascadeSeedLaw : Measure unitInterval).prod Q)).map
      (Prod.map id (fun p => (ψ 0 z p.1,G (ψ 0 z p.1,p.2))))) =
      (powerIntensity (b 0)).prod
        ((((μ 0 : Measure (ι → ℝ)).prod P).withDensity
          (fun p => ENNReal.ofReal (c 0 (z,p.1)^b 0))).map (fun p => (p.1,H p)))
    rw [← Measure.map_prod_map _ _ measurable_id hmap, Measure.map_id, hpair]
    congr 1
    congr 1
    exact prod_withDensity_left
      ((((hc 0).comp (measurable_const.prodMk measurable_id)).pow_const (b 0)).ennreal_ofReal)

end InvariantIsing

end

end OAI
