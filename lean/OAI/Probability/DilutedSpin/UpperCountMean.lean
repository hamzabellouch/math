import OAI.Probability.DilutedSpin.UpperDatum
import OAI.Probability.DilutedSpin.UpperInsertion

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

instance upperDatumLaw_probability (M : Model p) (Q : FiniteLaw R) :
    IsProbabilityMeasure (upperDatumLaw (N := N) M Q) := by
  unfold upperDatumLaw
  infer_instance

omit [MeasurableSingletonClass R] in
lemma upperDatumLaw_ae (M : Model p) (Q : FiniteLaw R) {C : ℝ}
    (hC : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C) :
    ∀ᵐ z ∂upperDatumLaw (N := N) M Q,‖z.1.1‖≤C :=
  Measure.quasiMeasurePreserving_fst.ae hC

noncomputable def realCountEnergy (V : FinitePath Ω n → Fin N → Spin) (k : ℕ)
    (i : RootPath (Fin p → Fin N) k) (z : RootPath (InteractionSample p) k)
    (f : FinitePath Ω n → ℝ) (y : FinitePath Ω n) : ℝ :=
  f y+∑ a,(rootArray k z a).1 (fun j => V y (rootArray k i a j))

noncomputable def datumRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l) : ℝ :=
  cavityRoot T U V x m j l (rootMap (fun a => a.2.2) l w) (rootMap (fun a => a.2.1) l w)
    (rootMap Prod.fst l w)
    (realCountEnergy V k (rootMap (fun a => a.2.1) k z) (rootMap Prod.fst k z) f)

omit [NeZero N] in
lemma measurable_datumRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ) :
    Measurable (fun z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l =>
      datumRoot T U V x m j f k l z.1 z.2) := by
  let F := fun z : (RootPath (InteractionSample p) k × RootPath (InteractionSample p) l) ×
      (RootPath (Fin p → Fin N) k × RootPath (Fin p → Fin N) l × RootPath (Fin p → R) l) =>
    cavityRoot T U V x m j l z.2.2.2 z.2.2.1 z.1.2 (realCountEnergy V k z.2.1 z.1.1 f)
  have hF : Measurable F := by
    apply measurable_from_prod_countable_left
    intro b
    dsimp only [F]
    apply measurable_cavityRoot
    · exact measurable_snd
    · intro y
      apply measurable_const.add
      exact Finset.measurable_sum _ (fun a _ =>
        (measurable_pi_apply _).comp (measurable_fst.comp ((measurable_rootArray k a).comp measurable_fst)))
  exact hF.comp
    ((((measurable_rootMap Prod.fst measurable_fst k).comp measurable_fst).prodMk
      ((measurable_rootMap Prod.fst measurable_fst l).comp measurable_snd)).prodMk
      (((measurable_rootMap (fun a : UpperDatum p N R => a.2.1) measurable_snd.fst k).comp measurable_fst).prodMk
        (((measurable_rootMap (fun a : UpperDatum p N R => a.2.1) measurable_snd.fst l).comp measurable_snd).prodMk
          ((measurable_rootMap (fun a : UpperDatum p N R => a.2.2) measurable_snd.snd l).comp measurable_snd))))

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma datumRoot_bound (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (f : FinitePath Ω n → ℝ)
    (k l : ℕ) (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
    {B C : ℝ} (hf : ∀ y,|f y|≤B) (hz : ∀ a,‖(rootArray k z a).1.1‖≤C)
    (hw : ∀ a,‖(rootArray l w a).1.1‖≤C) :
    |datumRoot T U V x m j f k l z w|≤B+C*(k+l) := by
  have hbase (y : FinitePath Ω n) :
      |realCountEnergy V k (rootMap (fun a => a.2.1) k z) (rootMap Prod.fst k z) f y|≤B+C*k := by
    apply (abs_add_le _ _).trans
    apply add_le_add (hf y)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ a : Fin k,C := Finset.sum_le_sum (fun a _ => by
        simpa only [rootArray_rootMap,Real.norm_eq_abs] using (norm_le_pi_norm (rootArray k z a).1.1 _).trans (hz a))
      _ = _ := by simp [mul_comm]
  apply (cavityRoot_bound T U V x m hm j l _ _ _ _ hbase).trans
  calc
    _ ≤ (B+C*k)+C*l := add_le_add_right (by
      simpa only [rootArray_rootMap,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using
        Finset.sum_le_sum (fun a (_ : a∈(Finset.univ : Finset (Fin l))) => hw a)) _
    _ = _ := by ring

lemma datumRoot_integrable (M : Model p) (Q : FiniteLaw R) {C : ℝ}
    (hC : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (f : FinitePath Ω n → ℝ)
    (k l : ℕ) {B : ℝ} (hf : ∀ y,|f y|≤B) :
    Integrable (fun z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l =>
      datumRoot T U V x m j f k l z.1 z.2)
      ((rootLaw k (fun _ => upperDatumLaw M Q)).prod (rootLaw l (fun _ => upperDatumLaw M Q))) := by
  apply Integrable.of_bound (measurable_datumRoot T U V x m j f k l).aestronglyMeasurable (B+C*(k+l))
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (rootLaw_ae_every _ (upperDatumLaw_ae M Q hC) k),
    Measure.quasiMeasurePreserving_snd.ae (rootLaw_ae_every _ (upperDatumLaw_ae M Q hC) l)] with z hz hw
  exact datumRoot_bound T U V x m hm j f k l z.1 z.2 hf hz hw

noncomputable def upperCountMean (M : Model p) (T : KernelTower Ω n) (Q : FiniteLaw R)
    (U : R → KernelTower Λ n) (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (m : Fin n → ℝ) (j : Fin p)
    (f : FinitePath Ω n → ℝ) (k l : ℕ) : ℝ :=
  ∫ z,∫ w,datumRoot T U V x m j f k l z w ∂rootLaw l (fun _ => upperDatumLaw M Q)
    ∂rootLaw k (fun _ => upperDatumLaw M Q)

lemma upperCountMean_bound (M : Model p) {C : ℝ}
    (hC : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (f : FinitePath Ω n → ℝ)
    (k l : ℕ) {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |upperCountMean M T Q U V x m j f k l|≤B+C*(k+l) := by
  unfold upperCountMean
  rw [← integral_prod _ (datumRoot_integrable M Q hC T U V x m hm j f k l hf)]
  apply abs_integral_le_bound_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (rootLaw_ae_every _ (upperDatumLaw_ae M Q hC) k),
    Measure.quasiMeasurePreserving_snd.ae (rootLaw_ae_every _ (upperDatumLaw_ae M Q hC) l)] with z hz hw
  exact datumRoot_bound T U V x m hm j f k l z.1 z.2 hf hz hw

end DilutedSpinGlass.PrescribedTree

end

end OAI
