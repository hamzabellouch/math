import OAI.Probability.FreeIsing.Estimates.FreeIsingMeasure
import OAI.Probability.FreeIsing.Estimates.InfinitePiPair
import OAI.Probability.FreeIsing.Gaussian.GlobalFreeLawNoise

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

def spinProduct {ι : Type*} (p : (ι → IsingSpin) × (ι → IsingSpin)) : ι → IsingSpin :=
  fun i => RootedBroadcast.spinMul (p.1 i) (p.2 i)

lemma measurable_spinProduct {ι : Type*} : Measurable (@spinProduct ι) := by
  apply Measurable.of_eval
  intro i
  change Measurable (fun p : (ι → IsingSpin) × (ι → IsingSpin) =>
    RootedBroadcast.spinMul (p.1 i) (p.2 i))
  have hp : Measurable (fun p : (ι → IsingSpin) × (ι → IsingSpin) =>
      (p.1 i, p.2 i)) := by fun_prop
  exact RootedBroadcast.measurable_spinMul.comp hp

@[simp] lemma spinProduct_relabel {d : ℕ} (g : TreeAut d)
    (x y : TreeVertex d → IsingSpin) :
    spinProduct (relabel g x, relabel g y) = relabel g (spinProduct (x, y)) := rfl

lemma treeNoiseMass_convolution {d : ℕ} (a b : ℝ) (r v : TreeVertex d)
    (s : IsingSpin) :
    treeNoiseMass a r v .neg *
        treeNoiseMass b r v (RootedBroadcast.spinMul .neg s) +
      treeNoiseMass a r v .pos * treeNoiseMass b r v s =
        treeNoiseMass (a * b) r v s := by
  classical
  by_cases h : v = r <;> cases s <;>
    simp [treeNoiseMass, h, RootedBroadcast.spinMul] <;> ring

theorem treeNoisePMF_map_spinMul {d : ℕ} {a b : ℝ}
    (ha0 : -1 ≤ a) (ha1 : a ≤ 1) (hb0 : -1 ≤ b) (hb1 : b ≤ 1)
    (hab0 : -1 ≤ a * b) (hab1 : a * b ≤ 1) (r v : TreeVertex d) :
    (((treeNoisePMF ha0 ha1 r v).toMeasure).prod
      ((treeNoisePMF hb0 hb1 r v).toMeasure)).map
        (fun p => RootedBroadcast.spinMul p.1 p.2) =
      (treeNoisePMF hab0 hab1 r v).toMeasure := by
  let : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
  apply Measure.ext_of_singleton
  intro s
  have hpre : (fun p : IsingSpin × IsingSpin => RootedBroadcast.spinMul p.1 p.2) ⁻¹' {s} =
      ({IsingSpin.neg} ×ˢ {RootedBroadcast.spinMul .neg s}) ∪
        ({IsingSpin.pos} ×ˢ {s}) := by
    ext p
    rcases p with ⟨x, y⟩
    cases x <;> cases y <;> cases s <;> simp [RootedBroadcast.spinMul]
  have hdisj : Disjoint
      ({IsingSpin.neg} ×ˢ {RootedBroadcast.spinMul .neg s})
      ({IsingSpin.pos} ×ˢ {s}) := by
    rw [Set.disjoint_left]
    intro p hp hq
    exact IsingSpin.noConfusion (hp.1.symm.trans hq.1)
  rw [Measure.map_apply RootedBroadcast.measurable_spinMul (measurableSet_singleton s),
    hpre, measure_union hdisj ((measurableSet_singleton _).prod (measurableSet_singleton _)),
    Measure.prod_prod, Measure.prod_prod]
  simp only [treeNoisePMF_toMeasure_singleton]
  rw [← ENNReal.ofReal_mul (treeNoiseMass_nonneg ha0 ha1 r v .neg),
    ← ENNReal.ofReal_mul (treeNoiseMass_nonneg ha0 ha1 r v .pos),
    ← ENNReal.ofReal_add
      (mul_nonneg (treeNoiseMass_nonneg ha0 ha1 r v .neg)
        (treeNoiseMass_nonneg hb0 hb1 r v _))
      (mul_nonneg (treeNoiseMass_nonneg ha0 ha1 r v .pos)
        (treeNoiseMass_nonneg hb0 hb1 r v _)), treeNoiseMass_convolution]

theorem map_spinProduct_infinitePi {ι : Type*}
    (μ ν : ι → Measure IsingSpin)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map spinProduct =
      Measure.infinitePi (fun i => ((μ i).prod (ν i)).map
        (fun p => RootedBroadcast.spinMul p.1 p.2)) := by
  rw [← Measure.infinitePi_map_pi _ (fun _ => RootedBroadcast.measurable_spinMul),
    ← infinitePi_map_pair_arrays μ ν, Measure.map_map (by
      apply Measurable.of_eval
      intro i
      exact RootedBroadcast.measurable_spinMul.comp (measurable_pi_apply i)) (by fun_prop)]
  rfl

lemma RootedBroadcast.noiseFromSpins_spinProduct {d : ℕ}
    (x y : TreeVertex d → IsingSpin) :
    noiseFromSpins (spinProduct (x, y)) =
      spinProduct (noiseFromSpins x, noiseFromSpins y) := by
  funext v
  by_cases hv : v.val = []
  · simp [noiseFromSpins, hv, spinProduct]
  · simp only [noiseFromSpins, hv, ↓reduceIte, spinProduct]
    cases x v <;> cases y v <;> cases x (parent v) <;> cases y (parent v) <;> rfl

theorem HasFreeIsingLaw.mul_product {d : ℕ} {a b : ℝ}
    {μ ν : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw a μ) (hν : HasFreeIsingLaw b ν)
    (ha0 : -1 ≤ a) (ha1 : a ≤ 1) (hb0 : -1 ≤ b) (hb1 : b ≤ 1) :
    HasFreeIsingLaw (a * b) ((μ.prod ν).map spinProduct) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hν.isProbabilityMeasure
  have hab : |a * b| ≤ 1 := by
    rw [abs_mul]
    have ha := abs_le.mpr ⟨ha0, ha1⟩
    have hb := abs_le.mpr ⟨hb0, hb1⟩
    nlinarith [abs_nonneg a, abs_nonneg b]
  have hab0 : -1 ≤ a * b := (abs_le.mp hab).1
  have hab1 : a * b ≤ 1 := (abs_le.mp hab).2
  have hnoise : ((μ.prod ν).map spinProduct).map RootedBroadcast.noiseFromSpins =
      Measure.infinitePi (fun v : TreeVertex d =>
        (treeNoisePMF hab0 hab1 (ConnectedHull.root d) v).toMeasure) := by
    rw [Measure.map_map (RootedBroadcast.measurable_noiseFromSpins d) measurable_spinProduct]
    have hfun : RootedBroadcast.noiseFromSpins ∘ spinProduct =
        spinProduct ∘ Prod.map (@RootedBroadcast.noiseFromSpins d)
          (@RootedBroadcast.noiseFromSpins d) := by
      funext p
      exact RootedBroadcast.noiseFromSpins_spinProduct p.1 p.2
    rw [hfun, ← Measure.map_map measurable_spinProduct
      ((RootedBroadcast.measurable_noiseFromSpins d).prodMap
        (RootedBroadcast.measurable_noiseFromSpins d)),
      ← Measure.map_prod_map μ ν (RootedBroadcast.measurable_noiseFromSpins d)
        (RootedBroadcast.measurable_noiseFromSpins d),
      hμ.map_noiseFromSpins ha0 ha1, hν.map_noiseFromSpins hb0 hb1,
      map_spinProduct_infinitePi]
    congr 1
    funext v
    exact treeNoisePMF_map_spinMul ha0 ha1 hb0 hb1 hab0 hab1 _ v
  have hfree := freeIsingMeasure_hasFreeIsingLaw d hab0 hab1
  have heq : (μ.prod ν).map spinProduct = freeIsingMeasure d (a * b) := by
    apply (RootedBroadcast.measurableEquiv d).symm.map_measurableEquiv_injective
    change ((μ.prod ν).map spinProduct).map RootedBroadcast.noiseFromSpins =
      (freeIsingMeasure d (a * b)).map RootedBroadcast.noiseFromSpins
    rw [hnoise, hfree.map_noiseFromSpins hab0 hab1]
  rw [heq]
  exact hfree

end Problem367

end

end OAI
