import OAI.Probability.InvariantIsing.Cavity.CavityInnovationLeaves

namespace OAI

/-! Unnormalized leaf-kernel transport under the innovation map. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal

namespace InvariantIsing

theorem cavityInnovationLeaf_unnormalized {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i))
    (hcpos : ∀ i s a, 0 < c i (s, a)) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hV : NoiseGibbsRegular n b μ c (fun _ p => p.1 + p.2) s V)
    (F : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n → ℝ≥0∞) (hF : Measurable F) :
    noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V * (∫⁻ v,
      noiseLeafProduct n c (fun _ p => p.1 + p.2) s v *
        F (cavityInnovationLeaf n c g s v) ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V) =
      noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n b μ c g s V) *
        ∫⁻ v, F v ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n b μ c g s V) := by
  induction n generalizing b μ c g s with
  | zero =>
    simp [noiseTreeTotal, rawTreeTotal, cavityInnovationTree,
      noiseLeafProduct, cavityInnovationLeaf, noiseLeafKernel, noiseLeafKernelData, Kernel.const_apply]
  | succ n ih =>
    let bt := fun j => b (j + 1)
    let μt := fun j => μ (j + 1)
    let ct := fun j => c (j + 1)
    let gt := fun j => g (j + 1)
    let u := fun (_ : ℕ) (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) => p.1 + p.2
    have hu : ∀ i, Measurable (u i) := fun _ => measurable_fst.add measurable_snd
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure (EuclideanSpace ℝ (Fin d))).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n bt μt : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n)))
    let T := fun p : ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
      (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1),
        cavityInnovationTree n bt μt ct gt (s + p.2.1) p.2.2))
    have hT : Measurable T :=
      (((hc 0).comp (by fun_prop)).mul measurable_fst).prodMk
        (((hg 0).comp (by fun_prop)).prodMk
          ((measurable_cavityInnovationTree n bt μt ct gt
            (fun j => hc (j + 1)) (fun j => hg (j + 1))).comp
              ((measurable_const.add measurable_snd.fst).prodMk measurable_snd.snd)))
    have hσ : sigmaPart I V = V := Marked.sigmaPart_eq_of_good I hV.2.2.1
    have hd : ∀ᵐ p ∂V, NoiseGibbsRegular n bt μt ct u (s + p.2.1) p.2.2 := by
      have hh : ∀ᵐ p ∂sigmaPart I V,
          NoiseGibbsRegular n bt μt ct u (s + p.2.1) p.2.2 := hV.2.2.2
      rwa [hσ] at hh
    have htree : cavityInnovationTree (n + 1) b μ c g s V = V.map T := by
      change (sigmaPart I V).map T = _
      rw [hσ]
    have hmass : 0 < noiseTreeTotal (EuclideanSpace ℝ (Fin d)) (n + 1) (cavityInnovationTree (n + 1) b μ c g s V) ∧
        noiseTreeTotal (EuclideanSpace ℝ (Fin d)) (n + 1) (cavityInnovationTree (n + 1) b μ c g s V) < ∞ := by
      rw [cavityInnovationTree_total (n + 1) b μ c g hc hg s V]
      exact hV.masses.2
    have hG : Measurable (fun v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) (n + 1) =>
        noiseLeafProduct (n + 1) c u s v * F (cavityInnovationLeaf (n + 1) c g s v)) :=
      ((measurable_noiseLeafProduct (n + 1) hc hu).comp
        (measurable_const.prodMk measurable_id)).mul
        (hF.comp ((measurable_cavityInnovationLeaf (n + 1) c g hc hg).comp
          (measurable_const.prodMk measurable_id)))
    rw [noiseLeafKernel_unnormalized_lintegral n V hV.1 hG,
      noiseLeafKernel_unnormalized_lintegral n _ hmass hF, htree]
    have hmF : Measurable (fun p :
        ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
        ∫⁻ v, F (p.1, (p.2.1, v)) ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n p.2.2) :=
      (hF.comp (by fun_prop : Measurable (fun p :
        (ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)) ×
          NoiseLeaf (EuclideanSpace ℝ (Fin d)) n => (p.1.1, (p.1.2.1, p.2))))).lintegral_kernel_prod_right'
        (κ := (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n).comap (fun p :
          ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) => p.2.2)
          (by fun_prop))
    rw [lintegral_map' (show AEMeasurable (fun p :
        ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
        ENNReal.ofReal (max p.1 0) * noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n p.2.2 *
          ∫⁻ v, F (p.1, (p.2.1, v)) ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n p.2.2) _ from
      (((by fun_prop : Measurable (fun p :
        ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
          ENNReal.ofReal (max p.1 0))).mul
        ((measurable_noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n).comp measurable_snd.snd)).mul hmF).aemeasurable)
      hT.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [hd] with p hp
    have hFp : Measurable (fun v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
        F (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1), v))) :=
      hF.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have he := ih bt μt ct gt (fun j => hc (j + 1)) (fun j => hg (j + 1))
      (fun j => hcpos (j + 1)) (s + p.2.1) p.2.2 hp _ hFp
    change ENNReal.ofReal (max p.1 0) * noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n p.2.2 *
      (∫⁻ v, (ENNReal.ofReal (c 0 (s, p.2.1)) * noiseLeafProduct n ct u (s + p.2.1) v) *
        F (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1),
          cavityInnovationLeaf n ct gt (s + p.2.1) v)) ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n p.2.2) =
      ENNReal.ofReal (max (c 0 (s, p.2.1) * p.1) 0) *
        noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n bt μt ct gt (s + p.2.1) p.2.2) *
        (∫⁻ v, F (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1), v))
          ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n bt μt ct gt (s + p.2.1) p.2.2))
    have hcmax : max (c 0 (s, p.2.1) * p.1) 0 = c 0 (s, p.2.1) * max p.1 0 := by
      rw [mul_max_of_nonneg _ _ (hcpos 0 s p.2.1).le, mul_zero]
    rw [hcmax, ENNReal.ofReal_mul (hcpos 0 s p.2.1).le]
    simp_rw [mul_assoc]
    have hz : Measurable (fun v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
        noiseLeafProduct n ct u (s + p.2.1) v *
          F (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1),
            cavityInnovationLeaf n ct gt (s + p.2.1) v))) :=
      ((measurable_noiseLeafProduct n (fun j => hc (j + 1)) hu).comp
        (measurable_const.prodMk measurable_id)).mul
        (hFp.comp ((measurable_cavityInnovationLeaf n ct gt
          (fun j => hc (j + 1)) (fun j => hg (j + 1))).comp
            (measurable_const.prodMk measurable_id)))
    rw [lintegral_const_mul _ hz]
    calc
      _ = ENNReal.ofReal (c 0 (s, p.2.1)) * ENNReal.ofReal (max p.1 0) *
          (noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n p.2.2 * ∫⁻ v, noiseLeafProduct n ct u (s + p.2.1) v *
            F (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1),
              cavityInnovationLeaf n ct gt (s + p.2.1) v)) ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n p.2.2) := by ring
      _ = _ := by rw [he]; ring

theorem cavityInnovationLeaf_tilted_law {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i))
    (hcpos : ∀ i s a, 0 < c i (s, a)) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hV : NoiseGibbsRegular n b μ c (fun _ p => p.1 + p.2) s V) :
    (noiseTiltedLeafLaw n c (fun _ p => p.1 + p.2) s V).map
      (cavityInnovationLeaf n c g s) =
        noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n b μ c g s V) := by
  let u := fun (_ : ℕ) (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) => p.1 + p.2
  let m := (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).withDensity (noiseLeafProduct n c u s)
  have hp : Measurable (noiseLeafProduct n c u s) :=
    (measurable_noiseLeafProduct n hc (fun _ => measurable_fst.add measurable_snd)).comp
      (measurable_const.prodMk measurable_id)
  have hk : Measurable (cavityInnovationLeaf n c g s) :=
    (measurable_cavityInnovationLeaf n c g hc hg).comp (measurable_const.prodMk measurable_id)
  have hmass : 0 < noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n b μ c g s V) ∧
      noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n b μ c g s V) < ∞ := by
    rw [cavityInnovationTree_total n b μ c g hc hg s V]
    exact hV.masses.2
  have he : (noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V • m).map (cavityInnovationLeaf n c g s) =
      noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n b μ c g s V) •
        noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n b μ c g s V) := by
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map hF hk, lintegral_smul_measure, lintegral_smul_measure]
    change noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V * (∫⁻ v, F (cavityInnovationLeaf n c g s v)
      ∂(noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).withDensity (noiseLeafProduct n c u s)) = _
    rw [lintegral_withDensity_eq_lintegral_mul _ hp
      (show Measurable (fun v => F (cavityInnovationLeaf n c g s v)) from hF.comp hk)]
    exact cavityInnovationLeaf_unnormalized n b μ c g hc hg hcpos s V hV F hF
  have hm : noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V * m Set.univ =
      noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n b μ c g s V) := by
    have hh := congrArg (fun η : Measure (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) => η Set.univ) he
    simpa only [Measure.map_apply hk MeasurableSet.univ, Set.preimage_univ,
      Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] using hh
  have hm0 : 0 < m Set.univ := by
    by_contra hh
    have hz : m Set.univ = 0 := le_antisymm (le_of_not_gt hh) bot_le
    rw [hz, mul_zero] at hm
    exact hmass.1.ne' hm.symm
  have him : m Set.univ < ∞ := by
    have ht : noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V * m Set.univ < ∞ := hm ▸ hmass.2
    rcases ENNReal.mul_lt_top_iff.mp ht with h | h | h
    · exact h.2
    · exact (hV.masses.1.1.ne' h).elim
    · exact (hm0.ne' h).elim
  change (normalizeMass m).map _ = _
  rw [← normalizeMass_smul m hV.masses.1 ⟨hm0, him⟩,
    normalizeMass_map _ hk (by
      simp only [Measure.smul_apply, smul_eq_mul, hm]
      exact hmass), he,
    normalizeMass_smul _ hmass (by simp), normalizeMass_of_probability]

lemma cavity_replica_kernel_transport {Ω Ω' X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X]
    (P : Measure Ω) (Q : Measure Ω')
    {ν : Ω → Measure X} {κ : Ω' → Measure X}
    (hν : Measurable ν) (hκ : Measurable κ)
    [∀ ω, IsProbabilityMeasure (ν ω)] [∀ ω, IsProbabilityMeasure (κ ω)]
    {T : Ω → Ω'} (hT : Measurable T) (hPQ : P.map T = Q)
    {L : X → X} (hL : Measurable L)
    (h : ∀ᵐ ω ∂P, (ν ω).map L = κ (T ω)) :
    ((probabilityReplicaKernel ν hν) ∘ₘ P).map (fun σ i => L (σ i)) =
      (probabilityReplicaKernel κ hκ) ∘ₘ Q := by
  let K := probabilityReplicaKernel κ hκ
  have hLs : Measurable (fun σ : ℕ → X => fun i => L (σ i)) := by fun_prop
  rw [Measure.map_comp _ _ hLs]
  calc
    _ = K.comap T hT ∘ₘ P := by
      apply Measure.comp_congr
      filter_upwards [h] with ω hω
      simp only [Kernel.map_apply _ hLs, Kernel.comap_apply, probabilityReplicaKernel, K]
      change (Measure.infinitePi (fun _ : ℕ => ν ω)).map (fun σ i => L (σ i)) =
        Measure.infinitePi (fun _ : ℕ => κ (T ω))
      rw [Measure.infinitePi_map_pi _ (fun _ => hL)]
      simp only [hω]
    _ = K ∘ₘ Q := by rw [kernel_comap_comp_measure, hPQ]

end InvariantIsing

end

end OAI
