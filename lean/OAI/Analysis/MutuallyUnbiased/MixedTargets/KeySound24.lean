import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical314

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment768 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 768) =
      Integer.Sparse.eval keyMomentRow768 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 768).leftCharge (GramAssembly.key 768).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 334) := by
    have ha : gramCharges (GramAssembly.key 768).leftCharge (GramAssembly.key 768).rightCharge = raw40215 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40215Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40215 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 768).leftCharge (GramAssembly.key 768).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow768, Integer.Sparse.eval]

theorem keyMoment769 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 769) =
      Integer.Sparse.eval keyMomentRow769 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 769).leftCharge (GramAssembly.key 769).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 310) := by
    have ha : gramCharges (GramAssembly.key 769).leftCharge (GramAssembly.key 769).rightCharge = raw40216 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40216Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40216 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 769).leftCharge (GramAssembly.key 769).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow769, Integer.Sparse.eval]

theorem keyMoment770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 770) =
      Integer.Sparse.eval keyMomentRow770 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 770).leftCharge (GramAssembly.key 770).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 520) := by
    have ha : gramCharges (GramAssembly.key 770).leftCharge (GramAssembly.key 770).rightCharge = raw40217 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40217Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40217 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 770).leftCharge (GramAssembly.key 770).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow770, Integer.Sparse.eval]

theorem keyMoment771 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 771) =
      Integer.Sparse.eval keyMomentRow771 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 771).leftCharge (GramAssembly.key 771).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 301) := by
    have ha : gramCharges (GramAssembly.key 771).leftCharge (GramAssembly.key 771).rightCharge = raw40218 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40218Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40218 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 771).leftCharge (GramAssembly.key 771).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow771, Integer.Sparse.eval]

theorem keyMoment772 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 772) =
      Integer.Sparse.eval keyMomentRow772 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 772).leftCharge (GramAssembly.key 772).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 155) := by
    have ha : gramCharges (GramAssembly.key 772).leftCharge (GramAssembly.key 772).rightCharge = raw40219 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40219Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40219 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 772).leftCharge (GramAssembly.key 772).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow772, Integer.Sparse.eval]

theorem keyMoment773 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 773) =
      Integer.Sparse.eval keyMomentRow773 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 773).leftCharge (GramAssembly.key 773).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 22) := by
    have ha : gramCharges (GramAssembly.key 773).leftCharge (GramAssembly.key 773).rightCharge = raw40220 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40220Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40220 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 773).leftCharge (GramAssembly.key 773).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow773, Integer.Sparse.eval]

theorem keyMoment774 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 774) =
      Integer.Sparse.eval keyMomentRow774 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 774).leftCharge (GramAssembly.key 774).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 91) := by
    have ha : gramCharges (GramAssembly.key 774).leftCharge (GramAssembly.key 774).rightCharge = raw40221 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40221Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40221 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 774).leftCharge (GramAssembly.key 774).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow774, Integer.Sparse.eval]

theorem keyMoment775 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 775) =
      Integer.Sparse.eval keyMomentRow775 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 775).leftCharge (GramAssembly.key 775).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 268) := by
    have ha : gramCharges (GramAssembly.key 775).leftCharge (GramAssembly.key 775).rightCharge = raw40222 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40222Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40222 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 775).leftCharge (GramAssembly.key 775).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow775, Integer.Sparse.eval]

theorem keyMoment776 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 776) =
      Integer.Sparse.eval keyMomentRow776 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 776).leftCharge (GramAssembly.key 776).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 245) := by
    have ha : gramCharges (GramAssembly.key 776).leftCharge (GramAssembly.key 776).rightCharge = raw40223 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40223Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40223 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 776).leftCharge (GramAssembly.key 776).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow776, Integer.Sparse.eval]

theorem keyMoment777 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 777) =
      Integer.Sparse.eval keyMomentRow777 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 777).leftCharge (GramAssembly.key 777).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 178) := by
    have ha : gramCharges (GramAssembly.key 777).leftCharge (GramAssembly.key 777).rightCharge = raw40224 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40224Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40224 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 777).leftCharge (GramAssembly.key 777).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow777, Integer.Sparse.eval]

theorem keyMoment778 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 778) =
      Integer.Sparse.eval keyMomentRow778 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 778).leftCharge (GramAssembly.key 778).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 234) := by
    have ha : gramCharges (GramAssembly.key 778).leftCharge (GramAssembly.key 778).rightCharge = raw40225 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40225Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40225 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 778).leftCharge (GramAssembly.key 778).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow778, Integer.Sparse.eval]

theorem keyMoment779 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 779) =
      Integer.Sparse.eval keyMomentRow779 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 779).leftCharge (GramAssembly.key 779).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 260) := by
    have ha : gramCharges (GramAssembly.key 779).leftCharge (GramAssembly.key 779).rightCharge = raw40226 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40226Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40226 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 779).leftCharge (GramAssembly.key 779).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow779, Integer.Sparse.eval]

theorem keyMoment780 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 780) =
      Integer.Sparse.eval keyMomentRow780 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 780).leftCharge (GramAssembly.key 780).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 174) := by
    have ha : gramCharges (GramAssembly.key 780).leftCharge (GramAssembly.key 780).rightCharge = raw40227 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40227Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40227 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 780).leftCharge (GramAssembly.key 780).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow780, Integer.Sparse.eval]

theorem keyMoment781 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 781) =
      Integer.Sparse.eval keyMomentRow781 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 781).leftCharge (GramAssembly.key 781).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 221) := by
    have ha : gramCharges (GramAssembly.key 781).leftCharge (GramAssembly.key 781).rightCharge = raw40228 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40228Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40228 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 781).leftCharge (GramAssembly.key 781).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow781, Integer.Sparse.eval]

theorem keyMoment782 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 782) =
      Integer.Sparse.eval keyMomentRow782 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 782).leftCharge (GramAssembly.key 782).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 467) := by
    have ha : gramCharges (GramAssembly.key 782).leftCharge (GramAssembly.key 782).rightCharge = raw40229 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40229Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40229 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 782).leftCharge (GramAssembly.key 782).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow782, Integer.Sparse.eval]

theorem keyMoment783 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 783) =
      Integer.Sparse.eval keyMomentRow783 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 783).leftCharge (GramAssembly.key 783).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 424) := by
    have ha : gramCharges (GramAssembly.key 783).leftCharge (GramAssembly.key 783).rightCharge = raw40230 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40230Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40230 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 783).leftCharge (GramAssembly.key 783).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow783, Integer.Sparse.eval]

theorem keyMoment784 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 784) =
      Integer.Sparse.eval keyMomentRow784 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 784).leftCharge (GramAssembly.key 784).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 503) := by
    have ha : gramCharges (GramAssembly.key 784).leftCharge (GramAssembly.key 784).rightCharge = raw40231 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40231Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40231 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 784).leftCharge (GramAssembly.key 784).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow784, Integer.Sparse.eval]

theorem keyMoment785 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 785) =
      Integer.Sparse.eval keyMomentRow785 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 785).leftCharge (GramAssembly.key 785).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 450) := by
    have ha : gramCharges (GramAssembly.key 785).leftCharge (GramAssembly.key 785).rightCharge = raw40232 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40232Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40232 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 785).leftCharge (GramAssembly.key 785).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow785, Integer.Sparse.eval]

theorem keyMoment786 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 786) =
      Integer.Sparse.eval keyMomentRow786 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 786).leftCharge (GramAssembly.key 786).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 289) := by
    have ha : gramCharges (GramAssembly.key 786).leftCharge (GramAssembly.key 786).rightCharge = raw40233 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40233Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40233 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 786).leftCharge (GramAssembly.key 786).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow786, Integer.Sparse.eval]

theorem keyMoment787 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 787) =
      Integer.Sparse.eval keyMomentRow787 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 787).leftCharge (GramAssembly.key 787).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 437) := by
    have ha : gramCharges (GramAssembly.key 787).leftCharge (GramAssembly.key 787).rightCharge = raw40234 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40234Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40234 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 787).leftCharge (GramAssembly.key 787).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow787, Integer.Sparse.eval]

theorem keyMoment788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 788) =
      Integer.Sparse.eval keyMomentRow788 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 788).leftCharge (GramAssembly.key 788).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 423) := by
    have ha : gramCharges (GramAssembly.key 788).leftCharge (GramAssembly.key 788).rightCharge = raw40235 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40235Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40235 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 788).leftCharge (GramAssembly.key 788).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow788, Integer.Sparse.eval]

theorem keyMoment789 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 789) =
      Integer.Sparse.eval keyMomentRow789 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 789).leftCharge (GramAssembly.key 789).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 472) := by
    have ha : gramCharges (GramAssembly.key 789).leftCharge (GramAssembly.key 789).rightCharge = raw40236 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40236Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40236 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 789).leftCharge (GramAssembly.key 789).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow789, Integer.Sparse.eval]

theorem keyMoment790 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 790) =
      Integer.Sparse.eval keyMomentRow790 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 790).leftCharge (GramAssembly.key 790).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 520) := by
    have ha : gramCharges (GramAssembly.key 790).leftCharge (GramAssembly.key 790).rightCharge = raw40237 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40237Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40237 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 790).leftCharge (GramAssembly.key 790).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow790, Integer.Sparse.eval]

theorem keyMoment791 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 791) =
      Integer.Sparse.eval keyMomentRow791 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 791).leftCharge (GramAssembly.key 791).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 336) := by
    have ha : gramCharges (GramAssembly.key 791).leftCharge (GramAssembly.key 791).rightCharge = raw40238 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40238Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40238 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 791).leftCharge (GramAssembly.key 791).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow791, Integer.Sparse.eval]

theorem keyMoment792 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 792) =
      Integer.Sparse.eval keyMomentRow792 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 792).leftCharge (GramAssembly.key 792).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 124) := by
    have ha : gramCharges (GramAssembly.key 792).leftCharge (GramAssembly.key 792).rightCharge = raw40239 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40239Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40239 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 792).leftCharge (GramAssembly.key 792).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow792, Integer.Sparse.eval]

theorem keyMoment793 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 793) =
      Integer.Sparse.eval keyMomentRow793 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 793).leftCharge (GramAssembly.key 793).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 312) := by
    have ha : gramCharges (GramAssembly.key 793).leftCharge (GramAssembly.key 793).rightCharge = raw40240 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40240Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40240 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 793).leftCharge (GramAssembly.key 793).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow793, Integer.Sparse.eval]

theorem keyMoment794 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 794) =
      Integer.Sparse.eval keyMomentRow794 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 794).leftCharge (GramAssembly.key 794).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 521) := by
    have ha : gramCharges (GramAssembly.key 794).leftCharge (GramAssembly.key 794).rightCharge = raw40241 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40241Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40241 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 794).leftCharge (GramAssembly.key 794).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow794, Integer.Sparse.eval]

theorem keyMoment795 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 795) =
      Integer.Sparse.eval keyMomentRow795 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 795).leftCharge (GramAssembly.key 795).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 517) := by
    have ha : gramCharges (GramAssembly.key 795).leftCharge (GramAssembly.key 795).rightCharge = raw40242 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40242Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40242 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 795).leftCharge (GramAssembly.key 795).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow795, Integer.Sparse.eval]

theorem keyMoment796 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 796) =
      Integer.Sparse.eval keyMomentRow796 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 796).leftCharge (GramAssembly.key 796).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 293) := by
    have ha : gramCharges (GramAssembly.key 796).leftCharge (GramAssembly.key 796).rightCharge = raw40243 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40243Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40243 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 796).leftCharge (GramAssembly.key 796).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow796, Integer.Sparse.eval]

theorem keyMoment797 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 797) =
      Integer.Sparse.eval keyMomentRow797 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 797).leftCharge (GramAssembly.key 797).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 157) := by
    have ha : gramCharges (GramAssembly.key 797).leftCharge (GramAssembly.key 797).rightCharge = raw40244 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40244Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40244 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 797).leftCharge (GramAssembly.key 797).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow797, Integer.Sparse.eval]

theorem keyMoment798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 798) =
      Integer.Sparse.eval keyMomentRow798 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 798).leftCharge (GramAssembly.key 798).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 30) := by
    have ha : gramCharges (GramAssembly.key 798).leftCharge (GramAssembly.key 798).rightCharge = raw40245 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40245Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40245 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 798).leftCharge (GramAssembly.key 798).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow798, Integer.Sparse.eval]

theorem keyMoment799 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 799) =
      Integer.Sparse.eval keyMomentRow799 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 799).leftCharge (GramAssembly.key 799).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 26) := by
    have ha : gramCharges (GramAssembly.key 799).leftCharge (GramAssembly.key 799).rightCharge = raw40246 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40246Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40246 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 799).leftCharge (GramAssembly.key 799).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow799, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
