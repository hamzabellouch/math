import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys87
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical335

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2784 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2784) =
      Integer.Sparse.eval keyMomentRow2784 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2784).leftCharge (GramAssembly.key 2784).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2669) := by
    have ha : gramCharges (GramAssembly.key 2784).leftCharge (GramAssembly.key 2784).rightCharge = raw42880 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42880Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42880 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2784).leftCharge (GramAssembly.key 2784).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5226) := by
    have ha : gramCharges (GramAssembly.key 2784).leftCharge (GramAssembly.key 2784).rightCharge = raw42881 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42881Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42881 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2784).leftCharge (GramAssembly.key 2784).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2784).leftCharge (GramAssembly.key 2784).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2784, Integer.Sparse.eval]
  ring

theorem keyMoment2785 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2785) =
      Integer.Sparse.eval keyMomentRow2785 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2785).leftCharge (GramAssembly.key 2785).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2670) := by
    have ha : gramCharges (GramAssembly.key 2785).leftCharge (GramAssembly.key 2785).rightCharge = raw42882 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42882Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42882 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2785).leftCharge (GramAssembly.key 2785).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5140) := by
    have ha : gramCharges (GramAssembly.key 2785).leftCharge (GramAssembly.key 2785).rightCharge = raw42883 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42883Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42883 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2785).leftCharge (GramAssembly.key 2785).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2785).leftCharge (GramAssembly.key 2785).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2785, Integer.Sparse.eval]
  ring

theorem keyMoment2786 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2786) =
      Integer.Sparse.eval keyMomentRow2786 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2786).leftCharge (GramAssembly.key 2786).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2682) := by
    have ha : gramCharges (GramAssembly.key 2786).leftCharge (GramAssembly.key 2786).rightCharge = raw42884 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42884Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42884 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2786).leftCharge (GramAssembly.key 2786).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5236) := by
    have ha : gramCharges (GramAssembly.key 2786).leftCharge (GramAssembly.key 2786).rightCharge = raw42885 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42885Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42885 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2786).leftCharge (GramAssembly.key 2786).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2786).leftCharge (GramAssembly.key 2786).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2786, Integer.Sparse.eval]
  ring

theorem keyMoment2787 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2787) =
      Integer.Sparse.eval keyMomentRow2787 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2787).leftCharge (GramAssembly.key 2787).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3229) := by
    have ha : gramCharges (GramAssembly.key 2787).leftCharge (GramAssembly.key 2787).rightCharge = raw42886 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42886Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42886 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2787).leftCharge (GramAssembly.key 2787).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4895) := by
    have ha : gramCharges (GramAssembly.key 2787).leftCharge (GramAssembly.key 2787).rightCharge = raw42887 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42887Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42887 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2787).leftCharge (GramAssembly.key 2787).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2787).leftCharge (GramAssembly.key 2787).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2787, Integer.Sparse.eval]
  ring

theorem keyMoment2788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2788) =
      Integer.Sparse.eval keyMomentRow2788 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2788).leftCharge (GramAssembly.key 2788).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3088) := by
    have ha : gramCharges (GramAssembly.key 2788).leftCharge (GramAssembly.key 2788).rightCharge = raw42888 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42888Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42888 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2788).leftCharge (GramAssembly.key 2788).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5259) := by
    have ha : gramCharges (GramAssembly.key 2788).leftCharge (GramAssembly.key 2788).rightCharge = raw42889 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42889Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42889 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2788).leftCharge (GramAssembly.key 2788).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2788).leftCharge (GramAssembly.key 2788).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2788, Integer.Sparse.eval]
  ring

theorem keyMoment2789 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2789) =
      Integer.Sparse.eval keyMomentRow2789 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2789).leftCharge (GramAssembly.key 2789).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3996) := by
    have ha : gramCharges (GramAssembly.key 2789).leftCharge (GramAssembly.key 2789).rightCharge = raw42890 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42890Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42890 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2789).leftCharge (GramAssembly.key 2789).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5410) := by
    have ha : gramCharges (GramAssembly.key 2789).leftCharge (GramAssembly.key 2789).rightCharge = raw42891 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42891Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42891 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2789).leftCharge (GramAssembly.key 2789).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2789).leftCharge (GramAssembly.key 2789).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2789, Integer.Sparse.eval]
  ring

theorem keyMoment2790 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2790) =
      Integer.Sparse.eval keyMomentRow2790 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2790).leftCharge (GramAssembly.key 2790).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3995) := by
    have ha : gramCharges (GramAssembly.key 2790).leftCharge (GramAssembly.key 2790).rightCharge = raw42892 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42892Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42892 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2790).leftCharge (GramAssembly.key 2790).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5473) := by
    have ha : gramCharges (GramAssembly.key 2790).leftCharge (GramAssembly.key 2790).rightCharge = raw42893 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42893Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42893 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2790).leftCharge (GramAssembly.key 2790).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2790).leftCharge (GramAssembly.key 2790).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2790, Integer.Sparse.eval]
  ring

theorem keyMoment2791 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2791) =
      Integer.Sparse.eval keyMomentRow2791 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2791).leftCharge (GramAssembly.key 2791).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3990) := by
    have ha : gramCharges (GramAssembly.key 2791).leftCharge (GramAssembly.key 2791).rightCharge = raw42894 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42894Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42894 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2791).leftCharge (GramAssembly.key 2791).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5424) := by
    have ha : gramCharges (GramAssembly.key 2791).leftCharge (GramAssembly.key 2791).rightCharge = raw42895 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42895Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42895 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2791).leftCharge (GramAssembly.key 2791).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2791).leftCharge (GramAssembly.key 2791).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2791, Integer.Sparse.eval]
  ring

theorem keyMoment2792 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2792) =
      Integer.Sparse.eval keyMomentRow2792 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2792).leftCharge (GramAssembly.key 2792).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3994) := by
    have ha : gramCharges (GramAssembly.key 2792).leftCharge (GramAssembly.key 2792).rightCharge = raw42896 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42896Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42896 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2792).leftCharge (GramAssembly.key 2792).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5478) := by
    have ha : gramCharges (GramAssembly.key 2792).leftCharge (GramAssembly.key 2792).rightCharge = raw42897 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42897Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42897 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2792).leftCharge (GramAssembly.key 2792).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2792).leftCharge (GramAssembly.key 2792).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2792, Integer.Sparse.eval]
  ring

theorem keyMoment2793 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2793) =
      Integer.Sparse.eval keyMomentRow2793 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2793).leftCharge (GramAssembly.key 2793).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3880) := by
    have ha : gramCharges (GramAssembly.key 2793).leftCharge (GramAssembly.key 2793).rightCharge = raw42898 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42898Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42898 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2793).leftCharge (GramAssembly.key 2793).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5445) := by
    have ha : gramCharges (GramAssembly.key 2793).leftCharge (GramAssembly.key 2793).rightCharge = raw42899 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42899Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42899 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2793).leftCharge (GramAssembly.key 2793).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2793).leftCharge (GramAssembly.key 2793).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2793, Integer.Sparse.eval]
  ring

theorem keyMoment2794 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2794) =
      Integer.Sparse.eval keyMomentRow2794 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2794).leftCharge (GramAssembly.key 2794).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3840) := by
    have ha : gramCharges (GramAssembly.key 2794).leftCharge (GramAssembly.key 2794).rightCharge = raw42900 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42900Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42900 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2794).leftCharge (GramAssembly.key 2794).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2794).leftCharge (GramAssembly.key 2794).rightCharge = raw42901 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42901Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42901 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2794).leftCharge (GramAssembly.key 2794).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2794).leftCharge (GramAssembly.key 2794).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2794, Integer.Sparse.eval]
  ring

theorem keyMoment2795 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2795) =
      Integer.Sparse.eval keyMomentRow2795 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2795).leftCharge (GramAssembly.key 2795).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3993) := by
    have ha : gramCharges (GramAssembly.key 2795).leftCharge (GramAssembly.key 2795).rightCharge = raw42902 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42902Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42902 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2795).leftCharge (GramAssembly.key 2795).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5438) := by
    have ha : gramCharges (GramAssembly.key 2795).leftCharge (GramAssembly.key 2795).rightCharge = raw42903 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42903Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42903 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2795).leftCharge (GramAssembly.key 2795).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2795).leftCharge (GramAssembly.key 2795).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2795, Integer.Sparse.eval]
  ring

theorem keyMoment2796 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2796) =
      Integer.Sparse.eval keyMomentRow2796 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2796).leftCharge (GramAssembly.key 2796).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3997) := by
    have ha : gramCharges (GramAssembly.key 2796).leftCharge (GramAssembly.key 2796).rightCharge = raw42904 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42904Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42904 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2796).leftCharge (GramAssembly.key 2796).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5484) := by
    have ha : gramCharges (GramAssembly.key 2796).leftCharge (GramAssembly.key 2796).rightCharge = raw42905 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42905Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42905 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2796).leftCharge (GramAssembly.key 2796).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2796).leftCharge (GramAssembly.key 2796).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2796, Integer.Sparse.eval]
  ring

theorem keyMoment2797 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2797) =
      Integer.Sparse.eval keyMomentRow2797 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2797).leftCharge (GramAssembly.key 2797).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3848) := by
    have ha : gramCharges (GramAssembly.key 2797).leftCharge (GramAssembly.key 2797).rightCharge = raw42906 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42906Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42906 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2797).leftCharge (GramAssembly.key 2797).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2797).leftCharge (GramAssembly.key 2797).rightCharge = raw42907 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42907Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42907 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2797).leftCharge (GramAssembly.key 2797).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2797).leftCharge (GramAssembly.key 2797).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2797, Integer.Sparse.eval]
  ring

theorem keyMoment2798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2798) =
      Integer.Sparse.eval keyMomentRow2798 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2798).leftCharge (GramAssembly.key 2798).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3540) := by
    have ha : gramCharges (GramAssembly.key 2798).leftCharge (GramAssembly.key 2798).rightCharge = raw42908 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42908Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42908 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2798).leftCharge (GramAssembly.key 2798).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2798).leftCharge (GramAssembly.key 2798).rightCharge = raw42909 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42909Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42909 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2798).leftCharge (GramAssembly.key 2798).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2798).leftCharge (GramAssembly.key 2798).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2798, Integer.Sparse.eval]
  ring

theorem keyMoment2799 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2799) =
      Integer.Sparse.eval keyMomentRow2799 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2799).leftCharge (GramAssembly.key 2799).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3227) := by
    have ha : gramCharges (GramAssembly.key 2799).leftCharge (GramAssembly.key 2799).rightCharge = raw42910 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42910Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42910 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2799).leftCharge (GramAssembly.key 2799).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4888) := by
    have ha : gramCharges (GramAssembly.key 2799).leftCharge (GramAssembly.key 2799).rightCharge = raw42911 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42911Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42911 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2799).leftCharge (GramAssembly.key 2799).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2799).leftCharge (GramAssembly.key 2799).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2799, Integer.Sparse.eval]
  ring

theorem keyMoment2800 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2800) =
      Integer.Sparse.eval keyMomentRow2800 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2800).leftCharge (GramAssembly.key 2800).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3065) := by
    have ha : gramCharges (GramAssembly.key 2800).leftCharge (GramAssembly.key 2800).rightCharge = raw42912 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42912Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42912 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2800).leftCharge (GramAssembly.key 2800).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5250) := by
    have ha : gramCharges (GramAssembly.key 2800).leftCharge (GramAssembly.key 2800).rightCharge = raw42913 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42913Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42913 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2800).leftCharge (GramAssembly.key 2800).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2800).leftCharge (GramAssembly.key 2800).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2800, Integer.Sparse.eval]
  ring

theorem keyMoment2801 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2801) =
      Integer.Sparse.eval keyMomentRow2801 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2801).leftCharge (GramAssembly.key 2801).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3977) := by
    have ha : gramCharges (GramAssembly.key 2801).leftCharge (GramAssembly.key 2801).rightCharge = raw42914 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42914Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42914 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2801).leftCharge (GramAssembly.key 2801).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5405) := by
    have ha : gramCharges (GramAssembly.key 2801).leftCharge (GramAssembly.key 2801).rightCharge = raw42915 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42915Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42915 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2801).leftCharge (GramAssembly.key 2801).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2801).leftCharge (GramAssembly.key 2801).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2801, Integer.Sparse.eval]
  ring

theorem keyMoment2802 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2802) =
      Integer.Sparse.eval keyMomentRow2802 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2802).leftCharge (GramAssembly.key 2802).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3976) := by
    have ha : gramCharges (GramAssembly.key 2802).leftCharge (GramAssembly.key 2802).rightCharge = raw42916 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42916Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42916 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2802).leftCharge (GramAssembly.key 2802).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5471) := by
    have ha : gramCharges (GramAssembly.key 2802).leftCharge (GramAssembly.key 2802).rightCharge = raw42917 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42917Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42917 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2802).leftCharge (GramAssembly.key 2802).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2802).leftCharge (GramAssembly.key 2802).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2802, Integer.Sparse.eval]
  ring

theorem keyMoment2803 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2803) =
      Integer.Sparse.eval keyMomentRow2803 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2803).leftCharge (GramAssembly.key 2803).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2698) := by
    have ha : gramCharges (GramAssembly.key 2803).leftCharge (GramAssembly.key 2803).rightCharge = raw42918 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42918Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42918 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2803).leftCharge (GramAssembly.key 2803).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5244) := by
    have ha : gramCharges (GramAssembly.key 2803).leftCharge (GramAssembly.key 2803).rightCharge = raw42919 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42919Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42919 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2803).leftCharge (GramAssembly.key 2803).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2803).leftCharge (GramAssembly.key 2803).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2803, Integer.Sparse.eval]
  ring

theorem keyMoment2804 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2804) =
      Integer.Sparse.eval keyMomentRow2804 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2804).leftCharge (GramAssembly.key 2804).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3078) := by
    have ha : gramCharges (GramAssembly.key 2804).leftCharge (GramAssembly.key 2804).rightCharge = raw42920 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42920Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42920 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2804).leftCharge (GramAssembly.key 2804).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5282) := by
    have ha : gramCharges (GramAssembly.key 2804).leftCharge (GramAssembly.key 2804).rightCharge = raw42921 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42921Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42921 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2804).leftCharge (GramAssembly.key 2804).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2804).leftCharge (GramAssembly.key 2804).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2804, Integer.Sparse.eval]
  ring

theorem keyMoment2805 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2805) =
      Integer.Sparse.eval keyMomentRow2805 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2805).leftCharge (GramAssembly.key 2805).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2706) := by
    have ha : gramCharges (GramAssembly.key 2805).leftCharge (GramAssembly.key 2805).rightCharge = raw42922 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42922Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42922 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2805).leftCharge (GramAssembly.key 2805).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5205) := by
    have ha : gramCharges (GramAssembly.key 2805).leftCharge (GramAssembly.key 2805).rightCharge = raw42923 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42923Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42923 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2805).leftCharge (GramAssembly.key 2805).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2805).leftCharge (GramAssembly.key 2805).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2805, Integer.Sparse.eval]
  ring

theorem keyMoment2806 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2806) =
      Integer.Sparse.eval keyMomentRow2806 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2806).leftCharge (GramAssembly.key 2806).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3954) := by
    have ha : gramCharges (GramAssembly.key 2806).leftCharge (GramAssembly.key 2806).rightCharge = raw42924 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42924Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42924 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2806).leftCharge (GramAssembly.key 2806).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2806).leftCharge (GramAssembly.key 2806).rightCharge = raw42925 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42925Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42925 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2806).leftCharge (GramAssembly.key 2806).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2806).leftCharge (GramAssembly.key 2806).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2806, Integer.Sparse.eval]
  ring

theorem keyMoment2807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2807) =
      Integer.Sparse.eval keyMomentRow2807 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2807).leftCharge (GramAssembly.key 2807).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3569) := by
    have ha : gramCharges (GramAssembly.key 2807).leftCharge (GramAssembly.key 2807).rightCharge = raw42926 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42926Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42926 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2807).leftCharge (GramAssembly.key 2807).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5197) := by
    have ha : gramCharges (GramAssembly.key 2807).leftCharge (GramAssembly.key 2807).rightCharge = raw42927 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42927Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42927 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2807).leftCharge (GramAssembly.key 2807).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2807).leftCharge (GramAssembly.key 2807).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2807, Integer.Sparse.eval]
  ring

theorem keyMoment2808 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2808) =
      Integer.Sparse.eval keyMomentRow2808 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2808).leftCharge (GramAssembly.key 2808).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3537) := by
    have ha : gramCharges (GramAssembly.key 2808).leftCharge (GramAssembly.key 2808).rightCharge = raw42928 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42928Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42928 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2808).leftCharge (GramAssembly.key 2808).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5187) := by
    have ha : gramCharges (GramAssembly.key 2808).leftCharge (GramAssembly.key 2808).rightCharge = raw42929 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42929Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42929 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2808).leftCharge (GramAssembly.key 2808).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2808).leftCharge (GramAssembly.key 2808).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2808, Integer.Sparse.eval]
  ring

theorem keyMoment2809 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2809) =
      Integer.Sparse.eval keyMomentRow2809 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2809).leftCharge (GramAssembly.key 2809).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3972) := by
    have ha : gramCharges (GramAssembly.key 2809).leftCharge (GramAssembly.key 2809).rightCharge = raw42930 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42930Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42930 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2809).leftCharge (GramAssembly.key 2809).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2809).leftCharge (GramAssembly.key 2809).rightCharge = raw42931 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42931Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42931 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2809).leftCharge (GramAssembly.key 2809).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2809).leftCharge (GramAssembly.key 2809).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2809, Integer.Sparse.eval]
  ring

theorem keyMoment2810 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2810) =
      Integer.Sparse.eval keyMomentRow2810 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2810).leftCharge (GramAssembly.key 2810).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3978) := by
    have ha : gramCharges (GramAssembly.key 2810).leftCharge (GramAssembly.key 2810).rightCharge = raw42932 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42932Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42932 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2810).leftCharge (GramAssembly.key 2810).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5480) := by
    have ha : gramCharges (GramAssembly.key 2810).leftCharge (GramAssembly.key 2810).rightCharge = raw42933 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42933Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42933 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2810).leftCharge (GramAssembly.key 2810).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2810).leftCharge (GramAssembly.key 2810).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2810, Integer.Sparse.eval]
  ring

theorem keyMoment2811 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2811) =
      Integer.Sparse.eval keyMomentRow2811 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2811).leftCharge (GramAssembly.key 2811).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3873) := by
    have ha : gramCharges (GramAssembly.key 2811).leftCharge (GramAssembly.key 2811).rightCharge = raw42934 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42934Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42934 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2811).leftCharge (GramAssembly.key 2811).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5421) := by
    have ha : gramCharges (GramAssembly.key 2811).leftCharge (GramAssembly.key 2811).rightCharge = raw42935 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42935Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42935 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2811).leftCharge (GramAssembly.key 2811).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2811).leftCharge (GramAssembly.key 2811).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2811, Integer.Sparse.eval]
  ring

theorem keyMoment2812 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2812) =
      Integer.Sparse.eval keyMomentRow2812 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2812).leftCharge (GramAssembly.key 2812).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3959) := by
    have ha : gramCharges (GramAssembly.key 2812).leftCharge (GramAssembly.key 2812).rightCharge = raw42936 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42936Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42936 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2812).leftCharge (GramAssembly.key 2812).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5446) := by
    have ha : gramCharges (GramAssembly.key 2812).leftCharge (GramAssembly.key 2812).rightCharge = raw42937 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42937Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42937 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2812).leftCharge (GramAssembly.key 2812).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2812).leftCharge (GramAssembly.key 2812).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2812, Integer.Sparse.eval]
  ring

theorem keyMoment2813 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2813) =
      Integer.Sparse.eval keyMomentRow2813 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2813).leftCharge (GramAssembly.key 2813).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3578) := by
    have ha : gramCharges (GramAssembly.key 2813).leftCharge (GramAssembly.key 2813).rightCharge = raw42938 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42938Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42938 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2813).leftCharge (GramAssembly.key 2813).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5199) := by
    have ha : gramCharges (GramAssembly.key 2813).leftCharge (GramAssembly.key 2813).rightCharge = raw42939 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42939Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42939 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2813).leftCharge (GramAssembly.key 2813).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2813).leftCharge (GramAssembly.key 2813).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2813, Integer.Sparse.eval]
  ring

theorem keyMoment2814 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2814) =
      Integer.Sparse.eval keyMomentRow2814 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2814).leftCharge (GramAssembly.key 2814).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3529) := by
    have ha : gramCharges (GramAssembly.key 2814).leftCharge (GramAssembly.key 2814).rightCharge = raw42940 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42940Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42940 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2814).leftCharge (GramAssembly.key 2814).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5185) := by
    have ha : gramCharges (GramAssembly.key 2814).leftCharge (GramAssembly.key 2814).rightCharge = raw42941 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42941Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42941 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2814).leftCharge (GramAssembly.key 2814).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2814).leftCharge (GramAssembly.key 2814).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2814, Integer.Sparse.eval]
  ring

theorem keyMoment2815 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2815) =
      Integer.Sparse.eval keyMomentRow2815 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2815).leftCharge (GramAssembly.key 2815).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3517) := by
    have ha : gramCharges (GramAssembly.key 2815).leftCharge (GramAssembly.key 2815).rightCharge = raw42942 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42942Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42942 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2815).leftCharge (GramAssembly.key 2815).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5138) := by
    have ha : gramCharges (GramAssembly.key 2815).leftCharge (GramAssembly.key 2815).rightCharge = raw42943 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42943Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42943 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2815).leftCharge (GramAssembly.key 2815).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2815).leftCharge (GramAssembly.key 2815).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2815, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
