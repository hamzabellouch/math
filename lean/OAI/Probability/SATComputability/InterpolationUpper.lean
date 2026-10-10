import OAI.Probability.SATComputability.InterpolationInputs
import OAI.Probability.DilutedSpin.DenseUpper

namespace OAI

noncomputable section
open DilutedSpinGlass DilutedSpinGlass.PrescribedTree DilutedSpinGlass.KernelTower
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Topology

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSingletonClass R] in
lemma upperDatum_integrable_norm (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R) :
    Integrable (fun a : UpperDatum p N R => ‖a.1.1‖) (upperDatumLaw (N := N) M Q) :=
  measurePreserving_fst.integrable_comp_of_integrable hM.interaction_integrable

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma datumRoot_integrable_firstMoment (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (f : FinitePath Ω n → ℝ)
    (k l : ℕ) {B : ℝ} (hf : ∀ y,|f y|≤B) :
    Integrable (fun z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l =>
      datumRoot T U V x m j f k l z.1 z.2)
      ((rootLaw k (fun _ => upperDatumLaw (N := N) M Q)).prod (rootLaw l (fun _ => upperDatumLaw (N := N) M Q))) := by
  have hk := integrable_rootArray_sum (upperDatumLaw (N := N) M Q) (fun a => ‖a.1.1‖) (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperDatum_integrable_norm M hM Q) k
  have hl := integrable_rootArray_sum (upperDatumLaw (N := N) M Q) (fun a => ‖a.1.1‖) (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperDatum_integrable_norm M hM Q) l
  apply ((integrable_const B).add (hk.comp_fst (rootLaw l (fun _ => upperDatumLaw (N := N) M Q)))).add (hl.comp_snd (rootLaw k (fun _ => upperDatumLaw (N := N) M Q))) |>.mono'
    (measurable_datumRoot T U V x m j f k l).aestronglyMeasurable
  exact ae_of_all _ (fun z => datumRoot_norm_bound T U V x m hm j f k l z.1 z.2 hf)

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma upperCountMean_bound_firstMoment (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (f : FinitePath Ω n → ℝ)
    (k l : ℕ) {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |upperCountMean M T Q U V x m j f k l|≤B+(∫ a,‖a.1‖ ∂M.disorder.toMeasure)*(k+l) := by
  let g := fun a : UpperDatum p N R => ‖a.1.1‖
  have hg := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperDatum_integrable_norm (N := N) M hM Q
  have hk := integrable_rootArray_sum (upperDatumLaw (N := N) M Q) g hg k
  have hl := integrable_rootArray_sum (upperDatumLaw (N := N) M Q) g hg l
  have hB := ((integrable_const B).add (hk.comp_fst (rootLaw l (fun _ => upperDatumLaw (N := N) M Q)))).add (hl.comp_snd (rootLaw k (fun _ => upperDatumLaw (N := N) M Q)))
  unfold upperCountMean
  rw [← integral_prod _ (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_integrable_firstMoment M hM Q T U V x m hm j f k l hf)]
  apply (abs_integral_le_integral_abs).trans
  apply (integral_mono (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_integrable_firstMoment M hM Q T U V x m hm j f k l hf).abs hB
    (fun z => datumRoot_norm_bound T U V x m hm j f k l z.1 z.2 hf)).trans_eq
  change (∫ z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l,
      (B + ∑ a, g (rootArray k z.1 a)) + ∑ a, g (rootArray l z.2 a)
      ∂(rootLaw k (fun _ => upperDatumLaw (N := N) M Q)).prod (rootLaw l (fun _ => upperDatumLaw (N := N) M Q))) = _
  have he1 := integral_add ((integrable_const B).add (hk.comp_fst (rootLaw l (fun _ => upperDatumLaw (N := N) M Q)))) (hl.comp_snd (rootLaw k (fun _ => upperDatumLaw (N := N) M Q)))
  have he2 := integral_add (integrable_const B) (hk.comp_fst (rootLaw l (fun _ => upperDatumLaw (N := N) M Q)))
  simp only [Pi.add_apply] at he1 he2
  rw [he1,he2]
  have hek : (∫ z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l,
      ∑ a,g (rootArray k z.1 a) ∂(rootLaw k (fun _ => upperDatumLaw (N := N) M Q)).prod
        (rootLaw l (fun _ => upperDatumLaw (N := N) M Q))) =
      ∫ z : RootPath (UpperDatum p N R) k,∑ a,g (rootArray k z a) ∂rootLaw k (fun _ => upperDatumLaw (N := N) M Q) :=
    by simpa only [probReal_univ,one_smul] using (integral_fun_fst (μ := rootLaw k (fun _ => upperDatumLaw (N := N) M Q)) (ν := rootLaw l (fun _ => upperDatumLaw (N := N) M Q)) (fun z => ∑ a,g (rootArray k z a)))
  have hel : (∫ z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l,
      ∑ a,g (rootArray l z.2 a) ∂(rootLaw k (fun _ => upperDatumLaw (N := N) M Q)).prod
        (rootLaw l (fun _ => upperDatumLaw (N := N) M Q))) =
      ∫ z : RootPath (UpperDatum p N R) l,∑ a,g (rootArray l z a) ∂rootLaw l (fun _ => upperDatumLaw (N := N) M Q) :=
    by simpa only [probReal_univ,one_smul] using (integral_fun_snd (μ := rootLaw k (fun _ => upperDatumLaw (N := N) M Q)) (ν := rootLaw l (fun _ => upperDatumLaw (N := N) M Q)) (fun z => ∑ a,g (rootArray l z a)))
  rw [hek,hel,integral_rootArray_sum _ g hg k,integral_rootArray_sum _ g hg l]
  have he : (∫ a,g a ∂upperDatumLaw (N := N) M Q)=∫ a,‖a.1‖ ∂M.disorder.toMeasure := by
    simpa only [g,upperDatumLaw,probReal_univ,one_smul] using (integral_fun_fst (μ := M.disorder.toMeasure) (ν := ((FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).asProbability id).toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure) (fun a : InteractionSample p => ‖a.1‖))
  rw [he]
  simp only [integral_const,probReal_univ,one_smul]
  ring

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integrable_mixedLogAvg (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n,m j.succ≠0) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (sel : Fin p → Bool) {t : ℝ} (ht : |t|<1) :
    Integrable (fun z => mixedLogAvg T Q U V x m z sel t) M.disorder.toMeasure := by
  apply Integrable.of_bound (measurable_mixedLogAvg T Q U V x m sel t).aestronglyMeasurable
    (∑' k : ℕ,|t|^(k+1)/(k+1))
  filter_upwards [hM.factorization] with z hz
  simpa only [Real.norm_eq_abs,Finset.range_zero,Finset.sum_empty,sub_zero,Nat.add_zero,
    Nat.cast_zero,add_zero] using mixedLogAvg_negative_tail T Q U V x m hm hpos hnz hroot hend
      z (fun s => (hz.2 s).2.le) sel ht 0

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integrable_mixedNormalizedAvg (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n,0 < m j.succ)
    (sel : Fin p → Bool) {t : ℝ} (ht0 : 0≤t) (ht : t<1) :
    Integrable (fun z => mixedNormalizedAvg T Q U V x m z sel t) M.disorder.toMeasure := by
  apply (hM.interaction_integrable.const_mul 2).mono'
    (measurable_mixedNormalizedAvg T Q U V x m sel t).aestronglyMeasurable
  filter_upwards [hM.factorization] with z hz
  simpa only [Real.norm_eq_abs] using mixedNormalizedAvg_bound T Q U V x m hm z hz sel ht0 ht

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integrable_mixedLeafAvg (M : Model p) (hM : InterpolationAdmissible M)
    (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (sel : Fin p → Bool) : Integrable (fun z => mixedLeafAvg S T Q U V x z sel) M.disorder.toMeasure := by
  apply Integrable.of_bound (measurable_mixedLeafAvg S T Q U V x sel).aestronglyMeasurable 1
  filter_upwards [hM.factorization] with z hz
  simpa only [Real.norm_eq_abs] using mixedLeafAvg_bound S T Q U V x z (fun s => (hz.2 s).2.le) sel

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integral_mixedLogAvg_negative_tail (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n,m j.succ≠0) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (sel : Fin p → Bool) {t : ℝ} (ht : |t|<1) (K : ℕ) :
    |(∫ z,mixedLogAvg T Q U V x m z sel t ∂M.disorder.toMeasure)-∑ k∈Finset.range K,
      -(t^(k+1)/(k+1))*qExpect m
        (fun S => ∫ z,mixedLeafAvg S T Q U V x z sel ∂M.disorder.toMeasure) k (single n)| ≤
        ∑' k : ℕ,|t|^(k+K+1)/(k+K+1) := by
  have hi (S : PrescribedTree n) := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integrable_mixedLeafAvg M hM S T Q U V x sel
  simp_rw [← integral_qExpect _ m _ hi,← integral_const_mul]
  rw [← integral_finsetSum _ (fun k _ => (integrable_qExpect _ m _ hi k (single n)).const_mul _)]
  rw [← integral_sub (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integrable_mixedLogAvg M hM T Q U V x m hm hpos hnz hroot hend sel ht)
    (integrable_finsetSum _ (fun k _ => (integrable_qExpect _ m _ hi k (single n)).const_mul _))]
  have hb : ∀ᵐ z ∂M.disorder.toMeasure,
      ‖mixedLogAvg T Q U V x m z sel t-∑ k∈Finset.range K,
        -(t^(k+1)/(k+1))*qExpect m (fun S => mixedLeafAvg S T Q U V x z sel) k (single n)‖ ≤
          ∑' k : ℕ,|t|^(k+K+1)/(k+K+1) := by
    filter_upwards [hM.factorization] with z hz
    simpa only [Real.norm_eq_abs] using mixedLogAvg_negative_tail T Q U V x m hm hpos hnz hroot hend
      z (fun s => (hz.2 s).2.le) sel ht K
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hb

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma integrable_insertionPoint {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (M : Model p) (hM : InterpolationAdmissible M) (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z)
    (x : Z → Fin n → ℝ) (sel : Fin p → Bool) :
    Integrable (fun z => insertionPoint z old Q x sel) M.disorder.toMeasure := by
  apply Integrable.of_bound (measurable_insertionPoint old Q x sel).aestronglyMeasurable 1
  filter_upwards [hM.factorization] with z hz
  simpa only [Real.norm_eq_abs] using insertionPoint_bound z (fun s => (hz.2 s).2.le) old Q x sel

end
end FixedClauseThreshold.Computability.PositiveInterpolation

namespace FixedClauseThreshold.Computability.PositiveInterpolation
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma integral_expected_insertionPoint {Ω Z : Type} [Fintype Ω] [Fintype Z]
    {p n N : ℕ} [NeZero N] (M : Model p) (hM : InterpolationAdmissible M)
    (P : FiniteLaw Ω) (old : Ω → Fin N → Fin n → Spin)
    (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) (sel : Fin p → Bool) :
    (∫ z,P.expect (fun w => insertionPoint z (old w) Q x sel) ∂M.disorder.toMeasure)=
      P.expect (fun w => insertionCoefficient M (old w) Q x sel) :=
  FiniteLaw.integral_expect P M.disorder.toMeasure _
    (fun w => FixedClauseThreshold.Computability.PositiveInterpolation.integrable_insertionPoint M hM (old w) Q x sel)

end
end FixedClauseThreshold.Computability.PositiveInterpolation

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integratedMixedLeaf_identity (M : Model p) (hM : InterpolationAdmissible M)
    (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (sel : Fin p → Bool) :
    (∫ z,mixedLeafAvg S T Q U V x z sel ∂M.disorder.toMeasure)=
    (S.sampleLaw T).expect (fun old => insertionCoefficient M
      (fun i a => V (S.pathAt ((Fintype.equivFin S.Leaf).symm a) old) i)
      (Q.bind (fun r => S.sampleLaw (U r)))
      (fun w a => x w.1 (S.pathAt ((Fintype.equivFin S.Leaf).symm a) w.2)) sel) := by
  unfold mixedLeafAvg
  simp_rw [common_tree_point]
  exact FixedClauseThreshold.Computability.PositiveInterpolation.integral_expected_insertionPoint M hM _ _ _ _ _

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma insertionCoefficient_combination_nonneg {Z : Type} [Fintype Z]
    {p n N : ℕ} [NeZero N] (M : Model p) (hM : InterpolationAdmissible M) (hn : 1≤n)
    (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) (j : Fin p) :
    0 ≤ insertionCoefficient M old Q x (fun _ => true) -
      (p:ℝ)*insertionCoefficient M old Q x (fun l => decide (l=j)) +
      ((p-1:ℕ):ℝ)*insertionCoefficient M old Q x (fun _ => false) := by
  simp only [insertionCoefficient_eq_raw,↓reduceIte,Bool.false_eq_true,decide_eq_true_eq]
  exact FixedClauseThreshold.Computability.PositiveInterpolation.rawReplica_combination_nonneg M hM hn j _ _

end
end FixedClauseThreshold.Computability.PositiveInterpolation

namespace FixedClauseThreshold.Computability.PositiveInterpolation
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma expected_insertionCoefficient_nonneg {Ω Z : Type} [Fintype Ω] [Fintype Z]
    {p n N : ℕ} [NeZero N] (M : Model p) (hM : InterpolationAdmissible M) (hn : 1≤n)
    (P : FiniteLaw Ω) (old : Ω → Fin N → Fin n → Spin)
    (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) (j : Fin p) :
    0 ≤ P.expect (fun w => insertionCoefficient M (old w) Q x (fun _ => true)) -
      (p:ℝ)*P.expect (fun w => insertionCoefficient M (old w) Q x (fun l => decide (l=j))) +
      ((p-1:ℕ):ℝ)*P.expect (fun w => insertionCoefficient M (old w) Q x (fun _ => false)) := by
  rw [← FiniteLaw.expect_mul_left,← FiniteLaw.expect_sub,← FiniteLaw.expect_mul_left,
    ← FiniteLaw.expect_add]
  exact P.expect_nonneg (fun w => FixedClauseThreshold.Computability.PositiveInterpolation.insertionCoefficient_combination_nonneg M hM hn (old w) Q x j)

end
end FixedClauseThreshold.Computability.PositiveInterpolation

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integratedMixedLeaf_combination_nonneg (M : Model p) (hM : InterpolationAdmissible M)
    (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ) (j : Fin p) :
    0 ≤ (∫ z,mixedLeafAvg S T Q U V x z (fun _ => true) ∂M.disorder.toMeasure)-
      (p:ℝ)*(∫ z,mixedLeafAvg S T Q U V x z (fun l => decide (l=j)) ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,mixedLeafAvg S T Q U V x z (fun _ => false) ∂M.disorder.toMeasure) := by
  simp only [FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integratedMixedLeaf_identity M hM]
  apply FixedClauseThreshold.Computability.PositiveInterpolation.expected_insertionCoefficient_nonneg M hM
  rw [card_leaf]
  exact leaves_pos S

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma mixedQMoment_combination_nonneg (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (k : ℕ) (S : PrescribedTree n) (j : Fin p) :
    0 ≤ qExpect m (fun S => ∫ z,mixedLeafAvg S T Q U V x z (fun _ => true) ∂M.disorder.toMeasure) k S-
      (p:ℝ)*qExpect m (fun S => ∫ z,mixedLeafAvg S T Q U V x z (fun l => decide (l=j)) ∂M.disorder.toMeasure) k S+
      ((p-1:ℕ):ℝ)*qExpect m (fun S => ∫ z,mixedLeafAvg S T Q U V x z (fun _ => false) ∂M.disorder.toMeasure) k S := by
  rw [← qExpect_linear_combination]
  exact qExpect_nonneg m hm hpos _ (fun S => FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integratedMixedLeaf_combination_nonneg M hM S T Q U V x j) k S

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integral_mixedLog_combination_nonpos (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n,m j.succ≠0) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) {t : ℝ} (ht0 : 0≤t) (ht : t<1) :
    (∫ z,mixedLogAvg T Q U V x m z (fun _ => true) t ∂M.disorder.toMeasure)-
      (p:ℝ)*(∫ z,mixedLogAvg T Q U V x m z (fun l => decide (l=j)) t ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,mixedLogAvg T Q U V x m z (fun _ => false) t ∂M.disorder.toMeasure) ≤0 := by
  have ht' : |t|<1 := by rwa [abs_of_nonneg ht0]
  have hlim : Tendsto (fun K : ℕ => (1+(p:ℝ)+((p-1:ℕ):ℝ))*
      ∑' k : ℕ,|t|^(k+K+1)/(k+K+1)) atTop (𝓝 0) := by
    convert (tendsto_sum_nat_add (fun k : ℕ => |t|^(k+1)/(k+1))).const_mul
      (1+(p:ℝ)+((p-1:ℕ):ℝ)) using 1 <;> simp
  apply ge_of_tendsto hlim
  exact Eventually.of_forall (fun K => negative_series_combination (Nat.cast_nonneg p)
    (Nat.cast_nonneg (p-1)) ht0 _ _ _ K
    (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedLogAvg_negative_tail M hM T Q U V x m hm hpos hnz hroot hend _ ht' K)
    (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedLogAvg_negative_tail M hM T Q U V x m hm hpos hnz hroot hend _ ht' K)
    (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedLogAvg_negative_tail M hM T Q U V x m hm hpos hnz hroot hend _ ht' K)
    (fun k => FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.mixedQMoment_combination_nonneg M hM T Q U V x m hm hpos k (single n) j))

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integrable_mixedEnergyAvg (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n,0 < m j.succ) (sel : Fin p → Bool) :
    Integrable (fun z => mixedEnergyAvg T Q U V x m z sel) M.disorder.toMeasure := by
  apply hM.interaction_integrable.mono' (measurable_mixedEnergyAvg T Q U V x m sel).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using mixedEnergyAvg_bound T Q U V x m hm z sel)

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integral_mixedNormalizedAvg_limit (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n,0 < m j.succ) (sel : Fin p → Bool) :
    Tendsto (fun k => ∫ z,mixedNormalizedAvg T Q U V x m z sel (regularization k) ∂M.disorder.toMeasure)
      atTop (𝓝 ((∫ z,mixedEnergyAvg T Q U V x m z sel ∂M.disorder.toMeasure)-
        ∫ z,z.1 (fun _ => false) ∂M.disorder.toMeasure)) := by
  have href : Integrable (fun z : InteractionSample p => z.1 (fun _ => false)) M.disorder.toMeasure :=
    hM.interaction_integrable.mono' (by fun_prop) (ae_of_all _ (fun z => norm_le_pi_norm z.1 _))
  rw [← integral_sub (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integrable_mixedEnergyAvg M hM T Q U V x m hm sel) href]
  apply tendsto_integral_of_dominated_convergence (fun z : InteractionSample p => 2*‖z.1‖)
  · intro k
    exact (measurable_mixedNormalizedAvg T Q U V x m sel _).aestronglyMeasurable
  · exact hM.interaction_integrable.const_mul 2
  · intro k
    filter_upwards [hM.factorization] with z hz
    simpa only [Real.norm_eq_abs] using mixedNormalizedAvg_bound T Q U V x m hm z hz sel
      (regularization_nonneg k) (regularization_lt_one k)
  · filter_upwards [hM.factorization] with z hz
    exact (mixedNormalizedAvg_limit T Q U V x m (fun j => ne_of_gt (hm j)) z hz sel).comp regularization_limit

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integral_mixedEnergy_combination_nonpos (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hstrict : ∀ j : Fin n,0 < m j.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) :
    (∫ z,mixedEnergyAvg T Q U V x m z (fun _ => true) ∂M.disorder.toMeasure)-
      (p:ℝ)*(∫ z,mixedEnergyAvg T Q U V x m z (fun l => decide (l=j)) ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,mixedEnergyAvg T Q U V x m z (fun _ => false) ∂M.disorder.toMeasure) ≤0 := by
  have hp : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by
    rw [Nat.cast_sub (by have h := hM.arity; omega : 1≤p)]; norm_num
  have hr (k : ℕ) :
      (∫ z,mixedNormalizedAvg T Q U V x m z (fun _ => true) (regularization k) ∂M.disorder.toMeasure)-
      (p:ℝ)*(∫ z,mixedNormalizedAvg T Q U V x m z (fun l => decide (l=j)) (regularization k) ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,mixedNormalizedAvg T Q U V x m z (fun _ => false) (regularization k) ∂M.disorder.toMeasure) ≤0 := by
    have ht0 := regularization_nonneg k
    have ht := regularization_lt_one k
    have ht' : |regularization k|<1 := by rwa [abs_of_nonneg ht0]
    have hi (sel : Fin p → Bool) := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integrable_mixedLogAvg M hM T Q U V x m hm hpos (fun l => ne_of_gt (hstrict l)) hroot hend sel ht'
    have hn (sel : Fin p → Bool) := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integrable_mixedNormalizedAvg M hM T Q U V x m hstrict sel ht0 ht
    have hd : Integrable (fun z => Real.log (1+regularization k*referenceD z)) M.disorder.toMeasure := by
      convert (hi (fun _ => false)).sub (hn (fun _ => false)) using 1
      funext z
      simp only [Pi.sub_apply,mixedNormalizedAvg]
      ring
    simp only [mixedNormalizedAvg]
    rw [integral_sub (hi _) hd,integral_sub (hi _) hd,integral_sub (hi _) hd]
    have hs := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedLog_combination_nonpos M hM T Q U V x m hm hpos
      (fun l => ne_of_gt (hstrict l)) hroot hend j ht0 ht
    rw [hp] at hs ⊢
    nlinarith only [hs]
  have hlim := ((FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedNormalizedAvg_limit M hM T Q U V x m hstrict (fun _ => true)).sub
    ((FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedNormalizedAvg_limit M hM T Q U V x m hstrict (fun l => decide (l=j))).const_mul (p:ℝ))).add
    ((FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedNormalizedAvg_limit M hM T Q U V x m hstrict (fun _ => false)).const_mul ((p-1:ℕ):ℝ))
  have hs := le_of_tendsto hlim (Eventually.of_forall hr)
  rw [hp] at hs ⊢
  nlinarith only [hs]

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
lemma integral_mixedRoot_combination_nonpos (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j,0 ≤ m j)
    (hstrict : ∀ j : Fin n,0 < m j.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (f : FinitePath Ω n → ℝ) (j : Fin p) :
    (∫ z,mixedRootIncrement T Q U V x m f z (fun _ => true) ∂M.disorder.toMeasure)-
      (p:ℝ)*(∫ z,mixedRootIncrement T Q U V x m f z (fun l => decide (l=j)) ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,mixedRootIncrement T Q U V x m f z (fun _ => false) ∂M.disorder.toMeasure) ≤0 := by
  simp only [mixedRootIncrement_eq]
  exact FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedEnergy_combination_nonpos M hM _ Q U V x m hm hpos hstrict hroot hend j

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma freshRoot_mean_sub_firstMoment (M : Model p) (hM : InterpolationAdmissible M)
    (Q : FiniteLaw R) (T : KernelTower Ω n)
    (U : R → KernelTower Λ n) (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (m : Fin (n+1) → ℝ) (hm : ∀ d : Fin n,0 < m d.succ)
    (f : FinitePath Ω n → ℝ) (sel : Fin p → Bool) {B : ℝ}
    (hf : ∀ y,|f y|≤B) :
    (∫ a,freshRoot T U V x (fun d => m d.succ) f sel a ∂upperDatumLaw M Q)-
      backwardLog n T (fun d => m d.succ) f =
      ∫ θ,mixedRootIncrement T Q U V x m f θ sel ∂M.disorder.toMeasure := by
  let g := freshRoot T U V x (fun d => m d.succ) f sel
  have hg := measurable_freshRoot T U V x (fun d => m d.succ) f sel
  have hb (a : InteractionSample p) (i : Fin p → Fin N) (r : Fin p → R) : |g (a,i,r)|≤B+‖a.1‖ :=
    freshRoot_bound T U V x _ hm f sel (a,i,r) hf
  have hi : Integrable g (upperDatumLaw M Q) := by
    apply ((integrable_const B).add (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperDatum_integrable_norm M hM Q)).mono' hg.aestronglyMeasurable
    exact ae_of_all _ (fun a => hb a.1 a.2.1 a.2.2)
  rw [integral_upperDatumLaw_integrable M Q g hg hi]
  let G := fun θ => (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
    (fun i => (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r => g (θ,i,r)))
  have hG : Measurable G := FiniteLaw.measurable_expect _ (fun i =>
    FiniteLaw.measurable_expect _ (fun r => hg.comp (measurable_id.prodMk measurable_const)))
  have hiG : Integrable G M.disorder.toMeasure := by
    apply ((integrable_const B).add hM.interaction_integrable).mono' hG.aestronglyMeasurable
    exact ae_of_all _ (fun a => FiniteLaw.abs_expect_le _ (fun i => FiniteLaw.abs_expect_le _ (hb a i)))
  change (∫ θ,G θ ∂M.disorder.toMeasure)-_=_
  have hc : backwardLog n T (fun d => m d.succ) f =
      ∫ _θ : InteractionSample p, backwardLog n T (fun d => m d.succ) f ∂M.disorder.toMeasure := by simp
  rw [hc,← integral_sub hiG (integrable_const _)]
  apply integral_congr_ae
  filter_upwards [] with θ
  simp only [mixedRootIncrement,FiniteLaw.expect_sub,FiniteLaw.expect_const]
  rfl

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma freshRoot_replacement_firstMoment (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (f : FinitePath Ω n → ℝ) (j : Fin p) {B : ℝ}
    (hf : ∀ y,|f y|≤B) :
    (∫ a,freshRoot T U V x (fun d => m d.succ) f (fun _ => true) a ∂upperDatumLaw M Q)+
      ((p-1:ℕ):ℝ)*backwardLog n T (fun d => m d.succ) f ≤
      (p:ℝ)*(∫ a,freshRoot T U V x (fun d => m d.succ) f (fun d => decide (d=j)) a ∂upperDatumLaw M Q)-
      ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) := by
  have h := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedRoot_combination_nonpos M hM T Q U V x m hm hpos hstrict hroot hend f j
  simp_rw [mixedRootIncrement_false] at h
  rw [← FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.freshRoot_mean_sub_firstMoment M hM Q T U V x m hstrict f (fun _ => true) hf,
    ← FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.freshRoot_mean_sub_firstMoment M hM Q T U V x m hstrict f (fun d => decide (d=j)) hf] at h
  have hp : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by rw [Nat.cast_sub (by have := hM.arity; omega : 1≤p),Nat.cast_one]
  rw [hp] at h ⊢
  nlinarith

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma datumRoot_conditional_replacement_firstMoment (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
    :
    (∫ a,datumRoot T U V x (fun d => m d.succ) j f (k+1) l (a,z) w ∂upperDatumLaw M Q)+
      ((p-1:ℕ):ℝ)*datumRoot T U V x (fun d => m d.succ) j f k l z w ≤
      (p:ℝ)*(∫ a,datumRoot T U V x (fun d => m d.succ) j f k (l+1) z (a,w) ∂upperDatumLaw M Q)-
      ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) := by
  let F := cavityEnergy V x j l (rootMap (fun a => a.2.2) l w)
        (rootMap (fun a => a.2.1) l w) (rootMap Prod.fst l w)
        (realCountEnergy V k (rootMap (fun a => a.2.1) k z) (rootMap Prod.fst k z) f)
  have h := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.freshRoot_replacement_firstMoment M hM
    (cavityTower T U l (rootMap (fun a => a.2.2) l w)) Q U
    (fun y => V (pathMap (cavityProject l) n y)) x m hm hpos hstrict hroot hend F j
    (fun y => norm_le_pi_norm F y)
  dsimp only [F] at h
  simp only [datumRoot_fresh_true,datumRoot_fresh_selected] at h
  exact h

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma upperCountMean_replacement_firstMoment (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    :
    upperCountMean M T Q U V x (fun d => m d.succ) j f (k+1) l+
      ((p-1:ℕ):ℝ)*upperCountMean M T Q U V x (fun d => m d.succ) j f k l ≤
      (p:ℝ)*upperCountMean M T Q U V x (fun d => m d.succ) j f k (l+1)-
      ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) := by
  let D := upperDatumLaw (N := N) M Q
  let μ := rootLaw k (fun _ => D)
  let ν := rootLaw l (fun _ => D)
  let F := fun zw : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l =>
    datumRoot T U V x (fun d => m d.succ) j f k l zw.1 zw.2
  let G := fun azw : (UpperDatum p N R × RootPath (UpperDatum p N R) k) × RootPath (UpperDatum p N R) l =>
    datumRoot T U V x (fun d => m d.succ) j f (k+1) l azw.1 azw.2
  let H := fun zaw : RootPath (UpperDatum p N R) k × (UpperDatum p N R × RootPath (UpperDatum p N R) l) =>
    datumRoot T U V x (fun d => m d.succ) j f k (l+1) zaw.1 zaw.2
  have hF : Integrable F (μ.prod ν) :=
    FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_integrable_firstMoment M hM Q T U V x _ hstrict j f k l (fun y => norm_le_pi_norm f y)
  have hG : Integrable G ((D.prod μ).prod ν) :=
    FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_integrable_firstMoment M hM Q T U V x _ hstrict j f (k+1) l (fun y => norm_le_pi_norm f y)
  have hH : Integrable H (μ.prod (D.prod ν)) :=
    FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_integrable_firstMoment M hM Q T U V x _ hstrict j f k (l+1) (fun y => norm_le_pi_norm f y)
  have ig := integrable_triple_rotate D μ ν G hG
  have ih := integrable_triple_middle_swap μ D ν H hH
  let e := ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure)
  have hg := integral_mono (ig.add (hF.const_mul ((p-1:ℕ):ℝ))) ((ih.const_mul p).sub (integrable_const e))
    (fun zw => FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_conditional_replacement_firstMoment M hM T Q U V x m hm hpos hstrict hroot hend j f k l zw.1 zw.2)
  simp only [Pi.add_apply,Pi.sub_apply] at hg
  rw [integral_add ig (hF.const_mul _),integral_sub (ih.const_mul _) (integrable_const e),
    integral_const_mul,integral_const_mul] at hg
  have he : ∫ _zw,e ∂μ.prod ν=e := by
    have := rootLawProbability k (fun _ => D)
    have := rootLawProbability l (fun _ => D)
    simp
  rw [he,integral_prod _ ig,integral_prod _ ih,integral_prod _ hF,
    ← integral_triple_rotate D μ ν G hG,← integral_triple_middle_swap μ D ν H hH] at hg
  exact hg

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma upperPoissonCount_bound_firstMoment (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (r : ℝ≥0)
    :
    (∫ k,upperCountMean M T Q U V x (fun d => m d.succ) j f k 0 ∂poissonMeasure (r/p))+
      (r:ℝ)*(((p-1:ℕ):ℝ)/p)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) ≤
    ∫ l,upperCountMean M T Q U V x (fun d => m d.succ) j f 0 l ∂poissonMeasure r := by
  have hp : 0 < p := by have := hM.arity; omega
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have hpR : (p:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hp
  let e := ∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure
  have hh := poisson_count_replacement r p
    (upperCountMean M T Q U V x (fun d => m d.succ) j f)
    ((((p-1:ℕ):ℝ)/p)*e) (show 0 ≤ ∫ a : InteractionSample p, ‖a.1‖ ∂M.disorder.toMeasure from
      integral_nonneg (fun a => norm_nonneg a.1))
    (fun k l => FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperCountMean_bound_firstMoment M hM T Q U V x _ hstrict j f k l
      (fun y => norm_le_pi_norm f y))
    (fun k l => ?_)
  · simpa only [mul_assoc] using hh
  · have h := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperCountMean_replacement_firstMoment M hM T Q U V x m hm hpos hstrict hroot hend j f k l
    convert h using 1
    dsimp only [e]
    field_simp

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma allocatedDatumRoot_integrable (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) :
    Integrable (fun z : RootPath (Fin N) l × RootPath (InteractionSample p × (Fin p → R)) l =>
      allocatedDatumRoot T U V x m j s f l z.1 z.2)
      ((rootLaw l (fun _ => finiteUniform (Fin N))).prod
        (rootLaw l (fun _ => M.disorder.toMeasure.prod
          ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure))) := by
  have hi : Integrable (fun z : InteractionSample p × (Fin p → R) => ‖z.1.1‖)
      (M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure) :=
    measurePreserving_fst.integrable_comp_of_integrable hM.interaction_integrable
  apply ((integrable_const ‖f‖).add ((integrable_rootArray_sum _ _ hi l).comp_snd
    (rootLaw l (fun _ => finiteUniform (Fin N))))).mono'
    (measurable_allocatedDatumRoot T U V x m j s f l).aestronglyMeasurable
  exact ae_of_all _ (fun z => allocatedDatumRoot_bound T U V x m hm j s f l z.1 z.2)

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma upperAllocated_integrable (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) :
    Integrable (fun z : RootPath (UpperDatum p N R) l =>
      backwardLog n (cavityTower T U l (rootMap (fun a => a.2.2) l z)) m
        (allocatedEnergy V x j s l (rootMap (fun a => a.2.2) l z)
          (rootMap (fun a => a.2.1 j) l z) (rootMap Prod.fst l z) f))
      (rootLaw l (fun _ => upperDatumLaw M Q)) := by
  have h := ((measurePreserving_rootSplit _ _ l).comp
    (measurePreserving_rootMap (upperDatum_site_projection M Q j) l)).integrable_comp_of_integrable
      (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.allocatedDatumRoot_integrable M hM Q T U V x m hm j s f l)
  simpa only [Function.comp_def,allocatedDatumRoot,rootMap_comp] using h

omit [MeasurableSingletonClass R] in

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma upperAllocatedMean (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) :
    (∫ z : RootPath (UpperDatum p N R) l,
      backwardLog n (cavityTower T U l (rootMap (fun a => a.2.2) l z)) m
        (allocatedEnergy V x j s l (rootMap (fun a => a.2.2) l z)
          (rootMap (fun a => a.2.1 j) l z) (rootMap Prod.fst l z) f)
        ∂rootLaw l (fun _ => upperDatumLaw M Q))=
      ∫ c,activeCountMean M Q T U V x m j f
        (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        ∂rootLaw l (fun _ => finiteUniform (Fin N)) := by
  let F := fun z : RootPath (Fin N) l × RootPath (InteractionSample p × (Fin p → R)) l =>
    allocatedDatumRoot T U V x m j s f l z.1 z.2
  have hFm := measurable_allocatedDatumRoot T U V x m j s f l
  have he : (fun z : RootPath (UpperDatum p N R) l =>
      backwardLog n (cavityTower T U l (rootMap (fun a => a.2.2) l z)) m
        (allocatedEnergy V x j s l (rootMap (fun a => a.2.2) l z)
          (rootMap (fun a => a.2.1 j) l z) (rootMap Prod.fst l z) f))=
      fun z => F (rootMap Prod.fst l (rootMap (fun a => (a.2.1 j,(a.1,a.2.2))) l z),
        rootMap Prod.snd l (rootMap (fun a => (a.2.1 j,(a.1,a.2.2))) l z)) := by
    funext z
    simp only [F,allocatedDatumRoot,rootMap_comp,Function.comp_def]
  rw [he]
  apply (integral_rootMap (upperDatum_site_projection M Q j) l
    (fun z => F (rootMap Prod.fst l z,rootMap Prod.snd l z))
    (hFm.comp ((measurable_rootMap Prod.fst measurable_fst l).prodMk
      (measurable_rootMap Prod.snd measurable_snd l)))).trans
  rw [integral_rootSplit _ _ l F hFm (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.allocatedDatumRoot_integrable M hM Q T U V x m hm j s f l)]
  apply integral_congr_ae
  filter_upwards [] with c
  exact allocatedMean_selected M Q T U V x m j f s l c

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma upperCountMean_separable (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : Fin N → KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : Fin N → FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p)
    (f : Fin N → FinitePath Ω n → ℝ) (l : ℕ) :
    upperCountMean M (KernelTower.pi n T) Q U (fun y s => V s (FinitePath.proj n y s)) x m j
      (fun y => ∑ s,f s (FinitePath.proj n y s)) 0 l=
      ∑ s : Fin N,∫ c,activeCountMean M Q (T s) U (V s) x m j (f s)
        (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        ∂rootLaw l (fun _ => finiteUniform (Fin N)) := by
  rw [upperCountMean_cavity]
  simp_rw [cavityRoot_separable,rootMap_comp,Function.comp_def]
  rw [integral_finsetSum _ (fun s _ => FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperAllocated_integrable M hM Q (T s) U (V s) x m hm j s (f s) l)]
  exact Finset.sum_congr rfl (fun s _ => FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperAllocatedMean M hM Q (T s) U (V s) x m hm j s (f s) l)

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma activeCountMean_bound (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p)
    (f : FinitePath Ω n → ℝ) (l : ℕ) {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |activeCountMean M Q T U V x m j f l|≤B+(∫ a,‖a.1‖ ∂M.disorder.toMeasure)*l := by
  let ν := M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure
  have hi : Integrable (fun z : InteractionSample p × (Fin p → R) => ‖z.1.1‖) ν :=
    measurePreserving_fst.integrable_comp_of_integrable hM.interaction_integrable
  have hs := integrable_rootArray_sum ν (fun z => ‖z.1.1‖) hi l
  have hB (z : RootPath (InteractionSample p × (Fin p → R)) l) :
      |activeDatumRoot T U V x m j f l z|≤B+∑ i,‖(rootArray l z i).1.1‖ := by
    apply backwardLog_bound n _ m hm
    intro y
    simpa only [rootArray_rootMap] using activeEnergy_bound V x j l
      (rootMap Prod.snd l z) (rootMap Prod.fst l z) f hf y
  have hF : Integrable (activeDatumRoot T U V x m j f l) (rootLaw l (fun _ => ν)) :=
    ((integrable_const B).add hs).mono'
      (measurable_activeDatumRoot T U V x m j f l).aestronglyMeasurable (ae_of_all _ hB)
  unfold activeCountMean
  apply abs_integral_le_integral_abs.trans
  apply (integral_mono hF.abs ((integrable_const B).add hs) hB).trans_eq
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const B) hs,integral_rootArray_sum ν _ hi l]
  have he : (∫ a : InteractionSample p × (Fin p → R),‖a.1.1‖ ∂ν)=
      ∫ a : InteractionSample p,‖a.1‖ ∂M.disorder.toMeasure := by
    simpa only [ν,probReal_univ,one_smul] using
      (integral_fun_fst (μ := M.disorder.toMeasure)
        (ν := ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure)
        (fun a : InteractionSample p => ‖a.1‖))
  rw [he]
  simp only [integral_const,probReal_univ,one_smul,mul_comm]

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma upperSelectedCountMean_bound (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) :
    |∫ c,activeCountMean M Q T U V x m j f
        (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        ∂rootLaw l (fun _ => finiteUniform (Fin N))|≤
      ‖f‖+(∫ a,‖a.1‖ ∂M.disorder.toMeasure)*l := by
  apply abs_integral_le_bound_ae
  apply ae_of_all
  intro c
  apply (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.activeCountMean_bound M hM Q T U V x m hm j f _ (fun y => norm_le_pi_norm f y)).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg (fun a => norm_nonneg a.1))
  rw [selectedCount_eq_successCountAt]
  exact_mod_cast successCountAt_le s (rootArray l c)

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma upperPoisson_cavity_separable (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : Fin N → KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : Fin N → FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p)
    (f : Fin N → FinitePath Ω n → ℝ) (r : ℝ≥0) :
    (∫ l,upperCountMean M (KernelTower.pi n T) Q U (fun y s => V s (FinitePath.proj n y s)) x m j
      (fun y => ∑ s,f s (FinitePath.proj n y s)) 0 l ∂poissonMeasure r)=
      ∑ s : Fin N,∫ k,activeCountMean M Q (T s) U (V s) x m j (f s) k
        ∂poissonMeasure (r/N) := by
  simp_rw [FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperCountMean_separable M hM Q T U V x m hm j f]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s _
    exact integral_poisson_rootSelection r N s _ (integral_nonneg (fun a : InteractionSample p => norm_nonneg a.1))
      (fun l => FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.activeCountMean_bound M hM Q (T s) U (V s) x m hm j (f s) l
        (fun y => norm_le_pi_norm (f s) y))
  · intro s _
    apply ((integrable_const ‖f s‖).add ((poisson_integrable_count r).const_mul
      (∫ a,‖a.1‖ ∂M.disorder.toMeasure))).mono' (measurable_of_countable _).aestronglyMeasurable
    exact ae_of_all _ (fun l => FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperSelectedCountMean_bound M hM Q (T s) U (V s) x m hm j s (f s) l)

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSingletonClass R] in
lemma upperCountMean_real_firstMoment (M : Model p) (hM : InterpolationAdmissible M) (T : KernelTower Ω n) (Q : FiniteLaw R)
    (U : R → KernelTower Λ n) (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (m : Fin n → ℝ) (hm : ∀ d,0 < m d)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (k : ℕ) :
    upperCountMean M T Q U V x m j f k 0 =
      ∫ z : Fin k → InteractionSample p,
       (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect
        (fun i => backwardLog n T m (fun y => f y+∑ a,(z a).1 (fun b => V y (i a b))))
          ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  let F : RootPath (InteractionSample p × (Fin p → Fin N)) k → ℝ := fun z =>
    backwardLog n T m (fun y => f y+∑ a,(rootArray k z a).1.1 (fun b => V y ((rootArray k z a).2 b)))
  have hFm : Measurable F := by
    apply measurable_backwardLog
    intro y
    apply measurable_const.add
    apply Finset.measurable_sum
    intro a _
    exact (measurable_pi_apply (V y)).comp ((PhysicalRoot.measurable_indexedPotential (fun x : InteractionSample p => x)
      (fun σ => (measurable_pi_apply σ).comp measurable_fst)).comp (measurable_rootArray k a))
  have he : upperCountMean M T Q U V x m j f k 0 =
      ∫ z,F (rootMap (fun a : UpperDatum p N R => (a.1,a.2.1)) k z)
        ∂rootLaw k (fun _ => upperDatumLaw M Q) := by
    let : IsProbabilityMeasure (rootLaw 0 (fun _ : Fin 0 => upperDatumLaw (N := N) M Q)) := Measure.dirac.isProbabilityMeasure
    unfold upperCountMean
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [datumRoot,cavityRoot,cavityTower,cavityEnergy,realCountEnergy,
      rootArray_rootMap,F]
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
    rfl
  rw [he,integral_rootMap (upperDatum_real_projection M Q) k F hFm]
  apply integral_root_prod_finite_integrable M.disorder.toMeasure k
    (fun z : (Fin k → InteractionSample p) × (Fin k → Fin p → Fin N) => backwardLog n T m (fun y => f y+∑ a,(z.1 a).1 (fun b => V y (z.2 a b))))
  · apply measurable_from_prod_countable_left
    intro i
    apply measurable_backwardLog
    intro y
    change Measurable (fun z : Fin k → InteractionSample p => f y+∑ a,(z a).1 (fun b => V y (i a b)))
    exact measurable_const.add (Finset.measurable_sum _ (fun a _ =>
      (measurable_pi_apply _).comp (measurable_fst.comp (measurable_pi_apply a))))
  · apply ((integrable_const ‖f‖).add ((integrable_finsetSum Finset.univ
        (fun (a : Fin k) _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) (i := a)
          hM.interaction_integrable)).comp_fst (Measure.pi (fun _ : Fin k => finiteUniform (Fin p → Fin N))))).mono'
    · apply Measurable.aestronglyMeasurable
      apply measurable_from_prod_countable_left
      intro i
      apply measurable_backwardLog
      intro y
      change Measurable (fun z : Fin k → InteractionSample p => f y+∑ a,(z a).1 (fun b => V y (i a b)))
      exact measurable_const.add (Finset.measurable_sum _ (fun a _ =>
        (measurable_pi_apply _).comp (measurable_fst.comp (measurable_pi_apply a))))
    · exact ae_of_all _ (fun z => backwardLog_bound n T m hm (fun y =>
        (abs_add_le _ _).trans (add_le_add (norm_le_pi_norm f y)
          ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum (fun a _ => norm_le_pi_norm (z.1 a).1 _))))))

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSingletonClass R] in
lemma upperCountMean_real_terminal (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (r : ℕ) (U : R → KernelTower Λ (r+1)) (x : R → FinitePath Λ (r+1) → ℝ)
    (m : Fin (r+1) → ℝ) (hm : ∀ d,0 < m d) (hend : m (Fin.last r)=1)
    (j : Fin p) (h : Fin N → ℝ) (k : ℕ) :
    upperCountMean M (KernelTower.pi (r+1) (fun _ : Fin N =>
      terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)) Q U
      (fun y s => terminalState r (FinitePath.proj (r+1) y s)) x m j
      (fun y => ∑ s,h s*spin (terminalState r (FinitePath.proj (r+1) y s))) k 0=
      ∫ z : Fin k → InteractionSample p,
        (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect
          (fun i => logPartition z h i-(N:ℝ)*Real.log 2)
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  rw [FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperCountMean_real_firstMoment M hM]
  · apply integral_congr_ae
    filter_upwards [] with z
    apply FiniteLaw.expect_congr
    intro i
    rw [backwardLog_pi_terminal (fun _ : Fin N => false)
      (fun _ => (FiniteLaw.uniform : FiniteLaw Spin)) r m (fun d => (hm d).ne')
      (fun σ => (∑ s,h s*spin (σ s))+∑ a,(z a).1 (fun b => σ (i a b))),hend,FiniteLaw.pi_uniform,
      FiniteLaw.logMean_uniform]
    unfold logPartition
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro σ _
      congr 1
      unfold logWeight
      ring
    · simp [Real.log_pow]
  · exact hm

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma activeCountMean_site (q : ℕ) (M : Model (q+1)) (hM : InterpolationAdmissible M)
    (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin (r+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last r)=1) (k : ℕ) (h : ℝ) :
    activeCountMean M Q (terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)
      (fun b => pad a r (U b)) (terminalState r)
      (fun b y => x b (pathPrefix r y)) m (Fin.last q)
      (fun y => h*spin (terminalState r y)) k=
    ∫ z : Fin k → InteractionSample (q+1),
      trialLog r (finiteTrialLaw r Q U x) (fun d => m d.castSucc) (siteLog z h)
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  let F := fun z : RootPath (InteractionSample (q+1)) k × RootPath (Fin (q+1) → R) k =>
    backwardLog (r+1)
      (cavityTower (terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)
        (fun b => pad a r (U b)) k z.2) m
      (activeEnergy (terminalState r) (fun b y => x b (pathPrefix r y)) (Fin.last q) k z.2 z.1
        (fun y => h*spin (terminalState r y)))
  have hFm : Measurable F := by
    apply measurable_from_prod_countable_left
    intro b
    dsimp only [F]
    exact measurable_backwardLog (r+1) _ m (measurable_activeEnergy (terminalState r)
      (fun b y => x b (pathPrefix r y)) (Fin.last q) k b id measurable_id
      (fun y => h*spin (terminalState r y)))
  have hB (z : RootPath (InteractionSample (q+1)) k × RootPath (Fin (q+1) → R) k) :
      |F z|≤|h|+∑ i,‖(rootArray k z.1 i).1‖ := by
    apply backwardLog_bound _ _ _ hm
    intro y
    apply activeEnergy_bound _ _ _ _ _ _ _ _ y
    intro y
    simp only [abs_mul,abs_spin,mul_one]
    exact le_refl _
  have hi : Integrable F ((rootLaw k (fun _ => M.disorder.toMeasure)).prod
      (rootLaw k (fun _ => ((FiniteLaw.pi (fun _ : Fin (q+1) => Q)).asProbability id).toMeasure))) := by
    exact ((integrable_const |h|).add ((integrable_rootArray_sum M.disorder.toMeasure
      (fun a => ‖a.1‖) hM.interaction_integrable k).comp_fst _)).mono'
        hFm.aestronglyMeasurable (ae_of_all _ hB)
  unfold activeCountMean activeDatumRoot
  change (∫ z,F (rootMap Prod.fst k z,rootMap Prod.snd k z) ∂rootLaw k (fun _ => _))=_
  rw [integral_rootSplit _ _ k F hFm hi]
  have he (z : RootPath (InteractionSample (q+1)) k) :
      (∫ b,F (z,b) ∂rootLaw k (fun _ => ((FiniteLaw.pi (fun _ : Fin (q+1) => Q)).asProbability id).toMeasure))=
      trialLog r (finiteTrialLaw r Q U x) (fun d => m d.castSucc) (siteLog (rootArray k z) h) :=
    activeRoot_site_mean a r Q U x m hend q k z h
  simp only [he]
  exact integral_rootArray_eq_pi M.disorder.toMeasure k
    (fun z : Fin k → InteractionSample (q+1) =>
      trialLog r (finiteTrialLaw r Q U x) (fun d => m d.castSucc) (siteLog z h))

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma finiteTrial_upper_fixedField (M : Model (q+1)) (hM : InterpolationAdmissible M)
    (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin r → ℝ) (hm : Exponents m) (h : Fin N → ℝ) :
    (∫ k,∫ z : Fin k → InteractionSample (q+1),
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (q+1) → Fin N)).expect
        (fun i => logPartition z h i-(N:ℝ)*Real.log 2)
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) ∂poissonMeasure (M.alpha*N))+
      (M.alpha:ℝ)*N*q*(∫ z,trialLog r (finiteTrialLaw r Q U x) m
        (fun y => Real.log (edge z.1 y)) ∂M.disorder.toMeasure) ≤
      ∑ s : Fin N,∫ k,∫ z : Fin k → InteractionSample (q+1),
        trialLog r (finiteTrialLaw r Q U x) m (siteLog z (h s))
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) ∂poissonMeasure (M.alpha*(q+1)) := by
  let m' : Fin (r+1) → ℝ := Fin.snoc m 1
  let m₀ : Fin (r+2) → ℝ := Fin.cons 0 m'
  have hpos : ∀ d,0 < m' d := snoc_exponents_pos hm
  have hend : m' (Fin.last r)=1 := Fin.snoc_last _ _
  have hend₀ : m₀ (Fin.last (r+1))=1 := by
    change Fin.cons (α := fun _ => ℝ) 0 m' (Fin.last r).succ=1
    simpa only [Fin.cons_succ] using hend
  let T : Fin N → KernelTower Spin (r+1) := fun _ => terminalTower false FiniteLaw.uniform r
  let V : Fin N → FinitePath Spin (r+1) → Spin := fun _ => terminalState r
  let f : Fin N → FinitePath Spin (r+1) → ℝ := fun s y => h s*spin (terminalState r y)
  let Up : R → KernelTower Λ (r+1) := fun b => pad a r (U b)
  let xp : R → FinitePath Λ (r+1) → ℝ := fun b y => x b (pathPrefix r y)
  have hx := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperPoissonCount_bound_firstMoment M hM (KernelTower.pi (r+1) T) Q Up
    (fun y s => V s (FinitePath.proj (r+1) y s)) xp m₀
    (cons_snoc_exponents_mono hm) (cons_snoc_exponents_nonneg hm)
    (fun d => hpos d) rfl hend₀ (Fin.last q)
    (fun y => ∑ s,f s (FinitePath.proj (r+1) y s)) (M.alpha*(q+1)*N)
  have hr : (M.alpha*(q+1)*N:ℝ≥0)/(q+1)=M.alpha*N := by
    have hp : (q+1:ℝ≥0)≠0 := by positivity
    field_simp
  have hs : (M.alpha*(q+1)*N:ℝ≥0)/N=M.alpha*(q+1) := by
    have hN : (N:ℝ≥0)≠0 := by exact_mod_cast NeZero.ne N
    exact mul_div_cancel_right₀ _ hN
  simp only [m₀,Fin.cons_succ,Nat.cast_add,Nat.cast_one] at hx
  change (∫ k,upperCountMean M (KernelTower.pi (r+1) T) Q Up
      (fun y s => V s (FinitePath.proj (r+1) y s)) xp m' (Fin.last q)
      (fun y => ∑ s,f s (FinitePath.proj (r+1) y s)) k 0 ∂poissonMeasure ((M.alpha*(q+1)*N)/(q+1)))+
      ((M.alpha*(q+1)*N:ℝ≥0):ℝ)*(((q+1-1:ℕ):ℝ)/(q+1))*
        (∫ z,edgeRoot Q Up xp m' z ∂M.disorder.toMeasure) ≤ _ at hx
  rw [hr,FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperPoisson_cavity_separable M hM Q T Up V xp m' hpos (Fin.last q) f,hs] at hx
  dsimp only [T,V,f,Up,xp] at hx
  simp_rw [FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperCountMean_real_terminal M hM Q r _ _ m' hpos hend,
    FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.activeCountMean_site q M hM a r Q U x m' hpos hend,
    edgeRoot_pad r a Q U x m' (by rw [hend]; norm_num)] at hx
  have he : (fun d : Fin r => m' d.castSucc)=m := by funext d; exact Fin.snoc_castSucc _ _ d
  rw [he] at hx
  have hc : ((M.alpha*(q+1)*N:ℝ≥0):ℝ)*(((q+1-1:ℕ):ℝ)/(q+1))=(M.alpha:ℝ)*N*q := by
    simp only [Nat.add_sub_cancel,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
    have hp : (q:ℝ)+1≠0 := by positivity
    field_simp
  rwa [hc] at hx

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma finiteTrial_pressure_le (M : Model (q+1)) (hM : InterpolationAdmissible M)
    (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin r → ℝ) (hm : Exponents m) :
    pressure M N ≤ functional M r (finiteTrialLaw r Q U x) m := by
  let ζ := finiteTrialLaw r Q U x
  let μ := Measure.pi (fun _ : Fin N => M.field.toMeasure)
  let S : ℝ → ℝ := fun h => ∫ k,trialDisorderAt M m ζ k h ∂poissonMeasure (M.alpha*(q+1))
  let E := ∫ z,trialLog r ζ m (fun y => Real.log (edge z.1 y)) ∂M.disorder.toMeasure
  have hp : ∀ d,0 < m d := fun d => (hm.2 d).1
  have hS : Integrable S M.field.toMeasure :=
    (trialDisorderAt_joint_integrable M m hp ζ hM.interaction_integrable hM.field_integrable _).integral_prod_right
  have hF := (centeredDisorderAt_joint_integrable (N := N) M hM.interaction_integrable
    hM.field_integrable (M.alpha*N)).integral_prod_right
  have hiS (s : Fin N) : Integrable (fun h : Fin N → ℝ => S (h s)) μ :=
    integrable_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) (i := s) hS
  have hb (h : Fin N → ℝ) :
      (∫ k,centeredDisorderAt M k h ∂poissonMeasure (M.alpha*N))+(M.alpha:ℝ)*N*q*E ≤ ∑ s,S (h s) := by
    have he := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.finiteTrial_upper_fixedField M hM a r Q U x m hm h
    simpa only [FiniteLaw.expect_sub,FiniteLaw.expect_const,FiniteLaw.expect_uniform,
      centeredDisorderAt,indexAverage,trialDisorderAt,S,E,ζ] using he
  have hi := integral_mono (hF.add (integrable_const ((M.alpha:ℝ)*N*q*E)))
    (integrable_finsetSum Finset.univ (fun s _ => hiS s)) hb
  simp only [Pi.add_apply] at hi
  rw [integral_add hF (integrable_const _),integral_const,probReal_univ,one_smul,
    centeredPressure_field_order M hM.interaction_integrable hM.field_integrable,
    integral_finsetSum _ (fun s _ => hiS s)] at hi
  dsimp only [μ] at hi
  simp only [integral_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) hS.aestronglyMeasurable,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hi
  dsimp only [S] at hi
  rw [trialPoisson_field_order M m hp ζ hM.interaction_integrable hM.field_integrable] at hi
  have hN : (0:ℝ)<N := by exact_mod_cast NeZero.pos N
  unfold functional
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
  change pressure M N ≤ Real.log 2+(∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*(q+1)))-
    (M.alpha:ℝ)*q*E
  nlinarith

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma finiteHierarchy_pressure_le (M : Model (q+1)) (hM : InterpolationAdmissible M)
    (r : ℕ) (ζ : Hierarchy (r+1)) (hζ : FiniteHierarchy (r+1) ζ)
    (m : Fin r → ℝ) (hm : Exponents m) : pressure M N ≤ functional M r ζ m := by
  obtain ⟨n,hn,T,V,hT⟩ := finiteHierarchy_realization (r+1) ζ hζ
  let a : Fin n := ⟨0,hn⟩
  have h := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.finiteTrial_pressure_le (N := N) M hM a r T.1 T.2 (fun b y => V (b,y)) m hm
  have he : finiteTrialLaw r T.1 T.2 (fun b y => V (b,y))=ζ := hT
  rwa [he] at h

end
end FixedClauseThreshold.Computability.PositiveInterpolation

namespace FixedClauseThreshold.Computability.PositiveInterpolation
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma pressure_le_functional (M : Model (q+1)) (hM : InterpolationAdmissible M)
    (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (hm : Exponents m) :
    pressure M N ≤ functional M r ζ m := by
  have hc : IsClosed {ζ : Hierarchy (r+1) | pressure M N ≤ functional M r ζ m} :=
    isClosed_le continuous_const (functional_continuous M m (fun d => (hm.2 d).1)
      hM.interaction_integrable hM.field_integrable)
  have hs : {ζ : Hierarchy (r+1) | FiniteHierarchy (r+1) ζ} ⊆
      {ζ : Hierarchy (r+1) | pressure M N ≤ functional M r ζ m} := by
    intro η hη
    exact FixedClauseThreshold.Computability.PositiveInterpolation.finiteHierarchy_pressure_le M hM r η hη m hm
  exact closure_minimal hs hc ((finiteHierarchy_dense (r+1)) ζ)

end
end FixedClauseThreshold.Computability.PositiveInterpolation

end

end OAI
