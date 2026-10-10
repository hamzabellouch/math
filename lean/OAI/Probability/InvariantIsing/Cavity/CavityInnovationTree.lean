import OAI.Probability.InvariantIsing.Cavity.CavityGaussianTiltLaw
import OAI.Probability.IsingPerceptron.RetainedDisplacement

namespace OAI

/-! The finite-depth retained Gaussian innovation construction.
The intensity calculation only requires the normalized conditional
fractional moment, not an ordinary exponential moment of a terminal. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal RealInnerProductSpace

namespace InvariantIsing

lemma cavity_map_powerIntensity_innovation {d n : ℕ} (b : ℝ)
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (P Q : ProbabilityMeasure (NoiseTree (EuclideanSpace ℝ (Fin d)) n))
    (c : EuclideanSpace ℝ (Fin d) → ℝ) (hc : Measurable c) (hcpos : ∀ a, 0 < c a)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hg : Measurable g)
    (T : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n →
      NoiseTree (EuclideanSpace ℝ (Fin d)) n) (hT : Measurable T)
    (hLaw : ∀ a, (P : Measure _).map (fun v => T (a, v)) = (Q : Measure _))
    (hν : ((μ : Measure _).withDensity (fun a => ENNReal.ofReal (c a ^ b))).map g =
      (ν : Measure _)) :
    ((powerIntensity b).prod ((μ : Measure _).prod (P : Measure _))).map
      (fun p => (c p.2.1 * p.1, (g p.2.1, T p.2))) =
      (powerIntensity b).prod ((ν : Measure _).prod (Q : Measure _)) := by
  let F := fun p : ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
    (c p.2.1 * p.1, (g p.2.1, T p.2))
  have hF : Measurable F := by fun_prop
  have hw : Measurable (fun a => ENNReal.ofReal (c a ^ b)) := (hc.pow_const b).ennreal_ofReal
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hF, lintegral_prod (fun p => f (F p)) (hf.comp hF).aemeasurable]
  have hv (x : ℝ) (a : EuclideanSpace ℝ (Fin d)) :
      (∫⁻ v, f (c a * x, (g a, T (a, v))) ∂(P : Measure _)) =
      ∫⁻ w, f (c a * x, (g a, w)) ∂(Q : Measure _) := by
    rw [← hLaw a, lintegral_map]
    · exact hf.comp (by fun_prop)
    · exact hT.comp (measurable_const.prodMk measurable_id)
  have hp (x : ℝ) :
      (∫⁻ p, f (F (x, p)) ∂((μ : Measure _).prod (P : Measure _))) =
      ∫⁻ a, ∫⁻ w, f (c a * x, (g a, w)) ∂(Q : Measure _) ∂(μ : Measure _) := by
    rw [lintegral_prod (fun p => f (F (x, p)))
      ((hf.comp hF).comp (measurable_const.prodMk measurable_id)).aemeasurable]
    exact lintegral_congr fun a => hv x a
  simp_rw [hp]
  have hG : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      ∫⁻ w, f (c p.2 * p.1, (g p.2, w)) ∂(Q : Measure _)) :=
    (hf.comp (by fun_prop : Measurable (fun p :
      (ℝ × EuclideanSpace ℝ (Fin d)) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
        (c p.1.2 * p.1.1, (g p.1.2, p.2))))).lintegral_prod_right'
  rw [lintegral_lintegral_swap hG.aemeasurable]
  have hx (a : EuclideanSpace ℝ (Fin d)) :
      (∫⁻ x, ∫⁻ w, f (c a * x, (g a, w)) ∂(Q : Measure _) ∂powerIntensity b) =
      ENNReal.ofReal (c a ^ b) *
        ∫⁻ x, ∫⁻ w, f (x, (g a, w)) ∂(Q : Measure _) ∂powerIntensity b := by
    have hfa : Measurable (fun x : ℝ =>
        ∫⁻ w, f (x, (g a, w)) ∂(Q : Measure _)) :=
      (hf.comp (by fun_prop : Measurable (fun p :
        ℝ × NoiseTree (EuclideanSpace ℝ (Fin d)) n => (p.1, (g a, p.2))))).lintegral_prod_right'
    rw [← lintegral_map hfa (measurable_const_mul (c a)),
      map_powerIntensity_mul (hcpos a), lintegral_smul_measure]
    rfl
  simp_rw [hx]
  let H := fun a : EuclideanSpace ℝ (Fin d) =>
    ∫⁻ x, ∫⁻ w, f (x, (a, w)) ∂(Q : Measure _) ∂powerIntensity b
  have hH : Measurable H :=
    ((hf.comp (by fun_prop : Measurable (fun p :
      (EuclideanSpace ℝ (Fin d) × ℝ) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
        (p.1.2, (p.1.1, p.2))))).lintegral_prod_right').lintegral_prod_right'
  change (∫⁻ a, ENNReal.ofReal (c a ^ b) * H (g a) ∂(μ : Measure _)) = _
  have hden := lintegral_withDensity_eq_lintegral_mul (μ : Measure _) hw (hH.comp hg)
  change (∫⁻ a, H (g a) ∂(μ : Measure _).withDensity
    (fun a => ENNReal.ofReal (c a ^ b))) =
    (∫⁻ a, ENNReal.ofReal (c a ^ b) * H (g a) ∂(μ : Measure _)) at hden
  rw [← hden, ← lintegral_map hH hg, hν]
  change (∫⁻ a, ∫⁻ x, ∫⁻ w, f (x, (a, w)) ∂(Q : Measure _)
    ∂powerIntensity b ∂(ν : Measure _)) = _
  rw [lintegral_lintegral_swap]
  · rw [lintegral_prod _ hf.aemeasurable]
    apply lintegral_congr
    intro x
    exact (lintegral_prod _ (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm
  · exact ((hf.comp (by fun_prop : Measurable (fun p :
      (EuclideanSpace ℝ (Fin d) × ℝ) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
        (p.1.2, (p.1.1, p.2))))).lintegral_prod_right').aemeasurable

/-- Retain and rescale each Gaussian mark while updating the running
sum by the original increment. -/
def cavityInnovationTree {d : ℕ} : (n : ℕ) → (ℕ → ℝ) →
    (ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) →
    (ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ) →
    (ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) →
    EuclideanSpace ℝ (Fin d) → NoiseTree (EuclideanSpace ℝ (Fin d)) n →
      NoiseTree (EuclideanSpace ℝ (Fin d)) n
  | 0, _, _, _, _, _, _ => PUnit.unit
  | n + 1, b, μ, c, g, s, T =>
      (sigmaPart ((powerIntensity (b 0)).prod ((μ 0 : Measure _).prod
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n (fun j => b (j + 1))
          (fun j => μ (j + 1))))) T).map
        (fun p => (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1),
          cavityInnovationTree n (fun j => b (j + 1)) (fun j => μ (j + 1))
            (fun j => c (j + 1)) (fun j => g (j + 1)) (s + p.2.1) p.2.2)))

lemma measurable_cavityInnovationTree {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i)) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
      cavityInnovationTree n b μ c g p.1 p.2) := by
  induction n generalizing b μ c g with
  | zero => exact measurable_const
  | succ n ih =>
      unfold cavityInnovationTree
      apply measurable_map_sigmaPart_param _ measurable_snd
        (G := fun p : (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) (n + 1)) ×
            (ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)) =>
          (c 0 (p.1.1, p.2.2.1) * p.2.1, (g 0 (p.1.1, p.2.2.1),
            cavityInnovationTree n (fun j => b (j + 1)) (fun j => μ (j + 1))
              (fun j => c (j + 1)) (fun j => g (j + 1)) (p.1.1 + p.2.2.1) p.2.2.2)))
      apply Measurable.prodMk
      · exact ((hc 0).comp (by fun_prop)).mul (by fun_prop)
      · apply Measurable.prodMk ((hg 0).comp (by fun_prop))
        exact (ih _ _ _ _ (fun i => hc (i + 1)) (fun i => hg (i + 1))).comp
          ((measurable_fst.fst.add measurable_snd.snd.fst).prodMk measurable_snd.snd.snd)

/-- If the retained innovation has the same law at every ancestor,
the full transformed tree has independent marks with that law. -/
theorem cavityInnovationTree_law {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (μ ν : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i))
    (hcpos : ∀ i s a, 0 < c i (s, a))
    (hν : ∀ i s, (((μ i : Measure _).withDensity
      (fun a => ENNReal.ofReal (c i (s, a) ^ b i))).map (fun a => g i (s, a))) =
        (ν i : Measure _)) (s : EuclideanSpace ℝ (Fin d)) :
    (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _).map
      (cavityInnovationTree n b μ c g s) = noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b ν := by
  induction n generalizing b μ ν c g s with
  | zero => exact Measure.map_dirac' measurable_const _
  | succ n ih =>
      let b' := fun i => b (i + 1)
      let μ' := fun i => μ (i + 1)
      let ν' := fun i => ν (i + 1)
      let c' := fun i => c (i + 1)
      let g' := fun i => g (i + 1)
      let P : ProbabilityMeasure (NoiseTree (EuclideanSpace ℝ (Fin d)) n) :=
        noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b' μ'
      let Q : ProbabilityMeasure (NoiseTree (EuclideanSpace ℝ (Fin d)) n) :=
        noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b' ν'
      let I := (powerIntensity (b 0)).prod ((μ 0 : Measure (EuclideanSpace ℝ (Fin d))).prod
        (P : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n)))
      let T := fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
        cavityInnovationTree n b' μ' c' g' (s + p.1) p.2
      have hT : Measurable T :=
        (measurable_cavityInnovationTree n b' μ' c' g'
          (fun i => hc (i + 1)) (fun i => hg (i + 1))).comp
            ((measurable_const.add measurable_fst).prodMk measurable_snd)
      have hLaw (a : EuclideanSpace ℝ (Fin d)) :
          (P : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n)).map (fun v => T (a, v)) =
            (Q : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n)) :=
        ih b' μ' ν' c' g' (fun i => hc (i + 1)) (fun i => hg (i + 1))
          (fun i => hcpos (i + 1)) (fun i => hν (i + 1)) (s + a)
      let G := fun p : ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
        (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1), T p.2))
      have hG : Measurable G := by
        exact (((hc 0).comp (by fun_prop)).mul (by fun_prop)).prodMk
          (((hg 0).comp (by fun_prop)).prodMk (hT.comp measurable_snd))
      have hI : I.map G = (powerIntensity (b 0)).prod ((ν 0 : Measure (EuclideanSpace ℝ (Fin d))).prod
          (Q : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n))) :=
        cavity_map_powerIntensity_innovation (b 0) (μ 0) (ν 0) P Q
          (fun a => c 0 (s, a)) ((hc 0).comp (measurable_const.prodMk measurable_id))
          (hcpos 0 s) (fun a => g 0 (s, a))
          ((hg 0).comp (measurable_const.prodMk measurable_id)) T hT hLaw (hν 0 s)
      rw [noiseCascadeLaw_succ, noiseCascadeLaw_succ]
      change (poissonLaw I).map _ = poissonLaw ((powerIntensity (b 0)).prod
        ((ν 0 : Measure (EuclideanSpace ℝ (Fin d))).prod
          (Q : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n))))
      calc
        _ = (poissonLaw I).map (fun V => V.map G) := by
          apply Measure.map_congr
          filter_upwards [sigmaPart_eq_ae I] with V hV
          change (sigmaPart I V).map G = V.map G
          rw [hV]
        _ = poissonLaw (I.map G) := poissonLaw_map I hG
        _ = _ := poissonLaw_congr hI

end InvariantIsing

end

end OAI
