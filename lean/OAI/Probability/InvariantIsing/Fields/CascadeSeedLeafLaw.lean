import OAI.Probability.InvariantIsing.Fields.CascadeSeedLeaf

namespace OAI

/-! Sampling commutes with the ancestor-dependent seed marking. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal
namespace InvariantIsing

theorem cascadeSeedLeaf_law {ι : Type} [Fintype ι] (n : ℕ) (b : ℕ → ℝ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i)))
    (T : NoiseTree unitInterval n) (hT : CascadeSeedRegular n b T) (z : ι → ℝ) :
    (noiseLeafKernel unitInterval n T).map (cascadeSeedLeaf n ψ z) =
      noiseLeafKernel (ι → ℝ) n (cascadeSeedTree n b ψ z T) := by
  induction n generalizing b ψ z with
  | zero =>
    change (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    exact Measure.map_dirac' measurable_const _
  | succ n ih =>
    let G : ℝ × (unitInterval × NoiseTree unitInterval n) →
        ℝ × ((ι → ℝ) × NoiseTree (ι → ℝ) n) := fun p =>
      (p.1,(ψ 0 z p.2.1,cascadeSeedTree n (fun j => b (j+1)) (fun j => ψ (j+1))
        (z+ψ 0 z p.2.1) p.2.2))
    have hG : Measurable G := by
      have hm : Measurable (fun p : ℝ × (unitInterval × NoiseTree unitInterval n) => ψ 0 z p.2.1) :=
        (hψ 0).comp (measurable_const.prodMk (measurable_fst.comp measurable_snd))
      exact measurable_fst.prodMk (hm.prodMk
        ((measurable_cascadeSeedTree n _ _ (fun i => hψ (i+1))).comp
          ((measurable_const.add hm).prodMk (by fun_prop))))
    have htree : cascadeSeedTree (n+1) b ψ z T = T.map G := by
      change (sigmaPart _ T).map G = T.map G
      rw [cascadeSeedRegular_sigma hT]
    have htotal := cascadeSeedTree_total (n+1) b ψ hψ T hT z
    have ht := cascadeSeedRegular_total hT
    have htarget : 0 < noiseTreeTotal (ι → ℝ) (n+1) (cascadeSeedTree (n+1) b ψ z T) ∧
        noiseTreeTotal (ι → ℝ) (n+1) (cascadeSeedTree (n+1) b ψ z T) < ∞ := by
      rwa [htotal]
    have hleaf : Measurable (cascadeSeedLeaf (n+1) ψ z) :=
      (measurable_cascadeSeedLeaf (n+1) ψ hψ).comp (measurable_const.prodMk measurable_id)
    apply Measure.ext_of_lintegral
    intro F hF
    have hint : Measurable (fun p : ℝ × ((ι → ℝ) × NoiseTree (ι → ℝ) n) =>
        ENNReal.ofReal (max p.1 0) * noiseTreeTotal (ι → ℝ) n p.2.2 *
          (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel (ι → ℝ) n p.2.2)) := by
      have hi := (hF.comp (show Measurable (fun p :
          (ℝ × ((ι → ℝ) × NoiseTree (ι → ℝ) n)) × NoiseLeaf (ι → ℝ) n =>
          (p.1.1,(p.1.2.1,p.2))) from by fun_prop)).lintegral_kernel_prod_right'
        (κ := (noiseLeafKernel (ι → ℝ) n).comap
          (fun p : ℝ × ((ι → ℝ) × NoiseTree (ι → ℝ) n) => p.2.2) (by fun_prop))
      exact ((by fun_prop : Measurable (fun p : ℝ × ((ι → ℝ) × NoiseTree (ι → ℝ) n) =>
        ENNReal.ofReal (max p.1 0))).mul ((measurable_noiseTreeTotal (ι → ℝ) n).comp (by fun_prop))).mul hi
    rw [lintegral_map hF hleaf,
      noiseLeafKernel_lintegral (A := unitInterval) n T ht
        (F := fun v => F (cascadeSeedLeaf (n+1) ψ z v)) (hF.comp hleaf),
      noiseLeafKernel_lintegral (A := ι → ℝ) n _ htarget hF, htotal, htree,
      lintegral_map hint hG]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [cascadeSeedRegular_tail hT] with p hp
    have hchild := ih (fun j => b (j+1)) (fun j => ψ (j+1)) (fun i => hψ (i+1))
      p.2.2 hp (z+ψ 0 z p.2.1)
    have hFp : Measurable (fun v : NoiseLeaf (ι → ℝ) n => F (p.1,(ψ 0 z p.2.1,v))) :=
      hF.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have he := congrArg (fun ν : Measure (NoiseLeaf (ι → ℝ) n) =>
      ∫⁻ v, F (p.1,(ψ 0 z p.2.1,v)) ∂ν) hchild
    rw [lintegral_map (g := cascadeSeedLeaf n (fun j => ψ (j+1)) (z+ψ 0 z p.2.1)) hFp
      ((measurable_cascadeSeedLeaf n _ (fun i => hψ (i+1))).comp
        (measurable_const.prodMk measurable_id))] at he
    dsimp only [G, cascadeSeedLeaf]
    rw [cascadeSeedTree_total _ _ _ (fun i => hψ (i+1)) _ hp]
    rw [he]

end InvariantIsing

end

end OAI
