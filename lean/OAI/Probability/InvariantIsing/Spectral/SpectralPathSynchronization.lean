import OAI.Probability.InvariantIsing.Spectral.SpectralPartitionPaths

namespace OAI

/-! Lipschitz synchronization of group quantiles, including total plateaus. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma group_abs_increment_le_total {m : ℕ} (p : OverlapPath) (pa : Fin m → OverlapPath)
    {s t : ℝ} (hs : (∑ a, pa a s) = p s) (ht : (∑ a, pa a t) = p t)
    (a : Fin m) : |pa a s - pa a t| ≤ |p s - p t| := by
  rcases le_total s t with hst | hts
  · have he := (group_increment_le_total p pa hst hs ht a).2
    rw [abs_of_nonpos (sub_nonpos.mpr ((pa a).monotone hst)),
      abs_of_nonpos (sub_nonpos.mpr (p.monotone hst))]
    linarith
  · have he := (group_increment_le_total p pa hts ht hs a).2
    rw [abs_of_nonneg (sub_nonneg.mpr ((pa a).monotone hts)),
      abs_of_nonneg (sub_nonneg.mpr (p.monotone hts))]
    exact he

/-- A group coordinate is a Lipschitz function of total overlap on the
entire set of good quantile parameters. Plateaus give a unique value. -/
theorem group_quantile_lipschitz_factor {m : ℕ} (p : OverlapPath) (pa : Fin m → OverlapPath)
    (hsum : ∀ᵐ s ∂pathMeasure, (∑ a, pa a s) = p s) (a : Fin m) :
    ∃ f : ℝ → ℝ, LipschitzWith 1 f ∧ ∀ᵐ s ∂pathMeasure, pa a s = f (p s) := by
  classical
  let good := {s : ℝ | (∑ b, pa b s) = p s}
  let S := p '' good
  let witness : S → ℝ := fun r => r.property.choose
  have hw (r : S) : witness r ∈ good ∧ p (witness r) = r := r.property.choose_spec
  let F : ℝ → ℝ := fun r => if hr : r ∈ S then pa a (witness ⟨r,hr⟩) else 0
  have hF (r : ℝ) (hr : r ∈ S) : F r = pa a (witness ⟨r,hr⟩) := dite_eq_left hr
  have hLip : LipschitzOnWith 1 F S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro r hr t ht
    rw [Real.dist_eq, Real.dist_eq, hF r hr, hF t ht, NNReal.coe_one, one_mul]
    have he := group_abs_increment_le_total p pa (hw ⟨r,hr⟩).1 (hw ⟨t,ht⟩).1 a
    simpa only [(hw ⟨r,hr⟩).2, (hw ⟨t,ht⟩).2] using he
  obtain ⟨f, hf, hfe⟩ := hLip.extend_real
  refine ⟨f, hf, ?_⟩
  filter_upwards [hsum] with s hs
  have hps : p s ∈ S := ⟨s,hs,rfl⟩
  have he := group_abs_increment_le_total p pa (hw ⟨p s,hps⟩).1 hs a
  rw [(hw ⟨p s,hps⟩).2, sub_self, abs_zero] at he
  have heq : pa a (witness ⟨p s,hps⟩) = pa a s :=
    sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm he (abs_nonneg _)))
  exact heq.symm.trans ((hF (p s) hps).symm.trans (hfe hps))

lemma factor_of_pair_law {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (μ : Measure Ω) (ν : Measure T) (p a : Ω → ℝ) (P A : T → ℝ)
    (hp : Measurable p) (ha : Measurable a) (hP : Measurable P) (hA : Measurable A)
    (hl : μ.map (fun s => (p s, a s)) = ν.map (fun x => (P x, A x)))
    (f : ℝ → ℝ) (hf : Continuous f) (he : ∀ᵐ s ∂μ, a s = f (p s)) :
    ∀ᵐ x ∂ν, A x = f (P x) := by
  have hm : MeasurableSet {z : ℝ × ℝ | z.2 = f z.1} :=
    (isClosed_eq continuous_snd (hf.comp continuous_fst)).measurableSet
  have hmap : ∀ᵐ z ∂μ.map (fun s => (p s, a s)), z.2 = f z.1 :=
    (ae_map_iff (hp.prodMk ha).aemeasurable hm).mpr he
  rw [hl] at hmap
  exact (ae_map_iff (hP.prodMk hA).aemeasurable hm).mp hmap

/-- The actual group overlap is a measurable, one-Lipschitz function of
the actual total overlap. No separate synchronization hypothesis is used. -/
theorem spectralPartition_lipschitz_synchronization {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (a : Fin m) :
    ∃ f : ℝ → ℝ, LipschitzWith 1 f ∧
      ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
        (x (0,1) a.castSucc : ℝ) = f (spectralSpinArray x 0 1) := by
  classical
  let hs := spectralCoordinate_unit hn
  let hp := (show ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      spectralLinearArray (spectralSpinWeight m) x 0 1 ∈ Icc (0 : ℝ) 1 by
    simpa only [spectralLinearArray_spinWeight] using spectralPartition_spin_unit hP hn)
  let p := spectralQuantilePath Q (spectralSpinWeight m) hp
  let pa := fun b : Fin m => spectralQuantilePath Q (Pi.single b.castSucc 1) (hs b.castSucc)
  have hsum : ∀ᵐ s ∂pathMeasure, (∑ b, pa b s) = p s :=
    spectralPartition_quantile_sum hgg hG q hq hd hE hP hn
  obtain ⟨f, hf, hfa⟩ := group_quantile_lipschitz_factor p pa hsum a
  refine ⟨f, hf, ?_⟩
  have hsingle : ∀ b, 0 ≤ (Pi.single a.castSucc 1 : Fin (m + 1) → ℝ) b := by
    intro b
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have he := factor_of_pair_law pathMeasure (Q : Measure (SpectralArray (m + 1)))
    p (pa a) (fun x => spectralLinearArray (spectralSpinWeight m) x 0 1)
    (fun x => spectralLinearArray (Pi.single a.castSucc 1) x 0 1)
    p.measurable (pa a).measurable
    (by unfold spectralLinearArray spectralLinearEntry; fun_prop)
    (by unfold spectralLinearArray spectralLinearEntry; fun_prop)
    (spectralQuantilePath_pair_law hgg hG q hq hd hE (spectralSpinWeight m) (Pi.single a.castSucc 1)
      (spectralSpinWeight_nonneg m) hsingle hp (hs a.castSucc))
    f hf.continuous hfa
  simpa only [spectralLinearArray_spinWeight, spectralLinearArray_single, spectralCoordinateArray] using he

lemma exists_injective_nat_pair {i j : ℕ} (hij : i ≠ j) :
    ∃ e : ℕ → ℕ, Function.Injective e ∧ e 0 = i ∧ e 1 = j := by
  let e : ℕ → ℕ := fun n => if n = 0 then i else if n = 1 then j else max i j + n
  refine ⟨e, ?_, by simp [e], by simp [e]⟩
  intro a b hab
  have hi := le_max_left i j
  have hj := le_max_right i j
  dsimp only [e] at hab
  split_ifs at hab <;> omega

lemma spectral_factor_all_off_diagonal {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (a : Fin m) (f : ℝ → ℝ) (hf : Continuous f)
    (hpair : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      (x (0,1) a.castSucc : ℝ) = f (spectralSpinArray x 0 1)) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i j, i ≠ j →
      (x (i,j) a.castSucc : ℝ) = f (spectralSpinArray x i j) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact ae_of_all _ fun _ h => (h hij).elim
  obtain ⟨e, he, he0, he1⟩ := exists_injective_nat_pair hij
  have hm : MeasurableSet {x : SpectralArray (m + 1) |
      (x (0,1) a.castSucc : ℝ) = f (spectralSpinArray x 0 1)} :=
    (isClosed_eq (by fun_prop) (hf.comp (by unfold spectralSpinArray; fun_prop))).measurableSet
  have hmap : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e),
      (x (0,1) a.castSucc : ℝ) = f (spectralSpinArray x 0 1) := by
    rw [hE e he]
    exact hpair
  have ha := (ae_map_iff (continuous_permuteSpectralArray e).measurable.aemeasurable hm).mp hmap
  filter_upwards [ha] with x hx
  intro _
  simpa only [permuteSpectralArray, spectralSpinArray, he0, he1] using hx

end InvariantIsing

end

end OAI
