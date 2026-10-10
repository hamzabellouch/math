import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical314

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment832 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 832) =
      Integer.Sparse.eval keyMomentRow832 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 832).leftCharge (GramAssembly.key 832).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 34) := by
    have ha : gramCharges (GramAssembly.key 832).leftCharge (GramAssembly.key 832).rightCharge = raw40279 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40279Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40279 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 832).leftCharge (GramAssembly.key 832).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow832, Integer.Sparse.eval]

theorem keyMoment833 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 833) =
      Integer.Sparse.eval keyMomentRow833 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 833).leftCharge (GramAssembly.key 833).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 99) := by
    have ha : gramCharges (GramAssembly.key 833).leftCharge (GramAssembly.key 833).rightCharge = raw40280 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40280Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40280 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 833).leftCharge (GramAssembly.key 833).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow833, Integer.Sparse.eval]

theorem keyMoment834 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 834) =
      Integer.Sparse.eval keyMomentRow834 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 834).leftCharge (GramAssembly.key 834).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 510) := by
    have ha : gramCharges (GramAssembly.key 834).leftCharge (GramAssembly.key 834).rightCharge = raw40281 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40281Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40281 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 834).leftCharge (GramAssembly.key 834).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow834, Integer.Sparse.eval]

theorem keyMoment835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 835) =
      Integer.Sparse.eval keyMomentRow835 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 835).leftCharge (GramAssembly.key 835).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 69) := by
    have ha : gramCharges (GramAssembly.key 835).leftCharge (GramAssembly.key 835).rightCharge = raw40282 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40282Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40282 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 835).leftCharge (GramAssembly.key 835).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow835, Integer.Sparse.eval]

theorem keyMoment836 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 836) =
      Integer.Sparse.eval keyMomentRow836 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 836).leftCharge (GramAssembly.key 836).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 186) := by
    have ha : gramCharges (GramAssembly.key 836).leftCharge (GramAssembly.key 836).rightCharge = raw40283 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40283Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40283 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 836).leftCharge (GramAssembly.key 836).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow836, Integer.Sparse.eval]

theorem keyMoment837 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 837) =
      Integer.Sparse.eval keyMomentRow837 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 837).leftCharge (GramAssembly.key 837).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 275) := by
    have ha : gramCharges (GramAssembly.key 837).leftCharge (GramAssembly.key 837).rightCharge = raw40284 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40284Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40284 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 837).leftCharge (GramAssembly.key 837).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow837, Integer.Sparse.eval]

theorem keyMoment838 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 838) =
      Integer.Sparse.eval keyMomentRow838 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 838).leftCharge (GramAssembly.key 838).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 277) := by
    have ha : gramCharges (GramAssembly.key 838).leftCharge (GramAssembly.key 838).rightCharge = raw40285 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40285Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40285 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 838).leftCharge (GramAssembly.key 838).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow838, Integer.Sparse.eval]

theorem keyMoment839 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 839) =
      Integer.Sparse.eval keyMomentRow839 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 839).leftCharge (GramAssembly.key 839).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 39) := by
    have ha : gramCharges (GramAssembly.key 839).leftCharge (GramAssembly.key 839).rightCharge = raw40286 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40286Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40286 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 839).leftCharge (GramAssembly.key 839).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow839, Integer.Sparse.eval]

theorem keyMoment840 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 840) =
      Integer.Sparse.eval keyMomentRow840 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 840).leftCharge (GramAssembly.key 840).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4085) := by
    have ha : gramCharges (GramAssembly.key 840).leftCharge (GramAssembly.key 840).rightCharge = raw2934 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw2934Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical2934 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 840).leftCharge (GramAssembly.key 840).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow840, Integer.Sparse.eval]

theorem keyMoment841 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 841) =
      Integer.Sparse.eval keyMomentRow841 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 841).leftCharge (GramAssembly.key 841).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2268) := by
    have ha : gramCharges (GramAssembly.key 841).leftCharge (GramAssembly.key 841).rightCharge = raw40287 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40287Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40287 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 841).leftCharge (GramAssembly.key 841).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow841, Integer.Sparse.eval]

theorem keyMoment842 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 842) =
      Integer.Sparse.eval keyMomentRow842 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 842).leftCharge (GramAssembly.key 842).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2281) := by
    have ha : gramCharges (GramAssembly.key 842).leftCharge (GramAssembly.key 842).rightCharge = raw40288 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40288Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40288 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 842).leftCharge (GramAssembly.key 842).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow842, Integer.Sparse.eval]

theorem keyMoment843 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 843) =
      Integer.Sparse.eval keyMomentRow843 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 843).leftCharge (GramAssembly.key 843).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4084) := by
    have ha : gramCharges (GramAssembly.key 843).leftCharge (GramAssembly.key 843).rightCharge = raw2929 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw2929Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical2929 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 843).leftCharge (GramAssembly.key 843).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow843, Integer.Sparse.eval]

theorem keyMoment844 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 844) =
      Integer.Sparse.eval keyMomentRow844 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 844).leftCharge (GramAssembly.key 844).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2293) := by
    have ha : gramCharges (GramAssembly.key 844).leftCharge (GramAssembly.key 844).rightCharge = raw40289 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40289Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40289 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 844).leftCharge (GramAssembly.key 844).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow844, Integer.Sparse.eval]

theorem keyMoment845 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 845) =
      Integer.Sparse.eval keyMomentRow845 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 845).leftCharge (GramAssembly.key 845).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2294) := by
    have ha : gramCharges (GramAssembly.key 845).leftCharge (GramAssembly.key 845).rightCharge = raw40290 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40290Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40290 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 845).leftCharge (GramAssembly.key 845).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow845, Integer.Sparse.eval]

theorem keyMoment846 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 846) =
      Integer.Sparse.eval keyMomentRow846 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 846).leftCharge (GramAssembly.key 846).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2247) := by
    have ha : gramCharges (GramAssembly.key 846).leftCharge (GramAssembly.key 846).rightCharge = raw40291 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40291Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40291 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 846).leftCharge (GramAssembly.key 846).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow846, Integer.Sparse.eval]

theorem keyMoment847 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 847) =
      Integer.Sparse.eval keyMomentRow847 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 847).leftCharge (GramAssembly.key 847).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2264) := by
    have ha : gramCharges (GramAssembly.key 847).leftCharge (GramAssembly.key 847).rightCharge = raw40292 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40292Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40292 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 847).leftCharge (GramAssembly.key 847).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow847, Integer.Sparse.eval]

theorem keyMoment848 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 848) =
      Integer.Sparse.eval keyMomentRow848 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 848).leftCharge (GramAssembly.key 848).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2265) := by
    have ha : gramCharges (GramAssembly.key 848).leftCharge (GramAssembly.key 848).rightCharge = raw40293 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40293Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40293 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 848).leftCharge (GramAssembly.key 848).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow848, Integer.Sparse.eval]

theorem keyMoment849 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 849) =
      Integer.Sparse.eval keyMomentRow849 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 849).leftCharge (GramAssembly.key 849).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2266) := by
    have ha : gramCharges (GramAssembly.key 849).leftCharge (GramAssembly.key 849).rightCharge = raw40294 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40294Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40294 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 849).leftCharge (GramAssembly.key 849).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow849, Integer.Sparse.eval]

theorem keyMoment850 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 850) =
      Integer.Sparse.eval keyMomentRow850 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 850).leftCharge (GramAssembly.key 850).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2278) := by
    have ha : gramCharges (GramAssembly.key 850).leftCharge (GramAssembly.key 850).rightCharge = raw40295 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40295Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40295 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 850).leftCharge (GramAssembly.key 850).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow850, Integer.Sparse.eval]

theorem keyMoment851 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 851) =
      Integer.Sparse.eval keyMomentRow851 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 851).leftCharge (GramAssembly.key 851).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2279) := by
    have ha : gramCharges (GramAssembly.key 851).leftCharge (GramAssembly.key 851).rightCharge = raw40296 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40296Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40296 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 851).leftCharge (GramAssembly.key 851).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow851, Integer.Sparse.eval]

theorem keyMoment852 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 852) =
      Integer.Sparse.eval keyMomentRow852 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 852).leftCharge (GramAssembly.key 852).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2291) := by
    have ha : gramCharges (GramAssembly.key 852).leftCharge (GramAssembly.key 852).rightCharge = raw40297 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40297Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40297 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 852).leftCharge (GramAssembly.key 852).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow852, Integer.Sparse.eval]

theorem keyMoment853 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 853) =
      Integer.Sparse.eval keyMomentRow853 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 853).leftCharge (GramAssembly.key 853).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4083) := by
    have ha : gramCharges (GramAssembly.key 853).leftCharge (GramAssembly.key 853).rightCharge = raw3331 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw3331Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical3331 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 853).leftCharge (GramAssembly.key 853).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow853, Integer.Sparse.eval]

theorem keyMoment854 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 854) =
      Integer.Sparse.eval keyMomentRow854 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 854).leftCharge (GramAssembly.key 854).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2244) := by
    have ha : gramCharges (GramAssembly.key 854).leftCharge (GramAssembly.key 854).rightCharge = raw40298 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40298Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40298 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 854).leftCharge (GramAssembly.key 854).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow854, Integer.Sparse.eval]

theorem keyMoment855 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 855) =
      Integer.Sparse.eval keyMomentRow855 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 855).leftCharge (GramAssembly.key 855).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2245) := by
    have ha : gramCharges (GramAssembly.key 855).leftCharge (GramAssembly.key 855).rightCharge = raw40299 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40299Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40299 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 855).leftCharge (GramAssembly.key 855).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow855, Integer.Sparse.eval]

theorem keyMoment856 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 856) =
      Integer.Sparse.eval keyMomentRow856 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 856).leftCharge (GramAssembly.key 856).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2262) := by
    have ha : gramCharges (GramAssembly.key 856).leftCharge (GramAssembly.key 856).rightCharge = raw40300 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40300Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40300 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 856).leftCharge (GramAssembly.key 856).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow856, Integer.Sparse.eval]

theorem keyMoment857 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 857) =
      Integer.Sparse.eval keyMomentRow857 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 857).leftCharge (GramAssembly.key 857).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2263) := by
    have ha : gramCharges (GramAssembly.key 857).leftCharge (GramAssembly.key 857).rightCharge = raw40301 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40301Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40301 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 857).leftCharge (GramAssembly.key 857).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow857, Integer.Sparse.eval]

theorem keyMoment858 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 858) =
      Integer.Sparse.eval keyMomentRow858 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 858).leftCharge (GramAssembly.key 858).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2277) := by
    have ha : gramCharges (GramAssembly.key 858).leftCharge (GramAssembly.key 858).rightCharge = raw40302 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40302Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40302 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 858).leftCharge (GramAssembly.key 858).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow858, Integer.Sparse.eval]

theorem keyMoment859 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 859) =
      Integer.Sparse.eval keyMomentRow859 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 859).leftCharge (GramAssembly.key 859).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2243) := by
    have ha : gramCharges (GramAssembly.key 859).leftCharge (GramAssembly.key 859).rightCharge = raw40303 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40303Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40303 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 859).leftCharge (GramAssembly.key 859).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow859, Integer.Sparse.eval]

theorem keyMoment860 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 860) =
      Integer.Sparse.eval keyMomentRow860 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 860).leftCharge (GramAssembly.key 860).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2268) := by
    have ha : gramCharges (GramAssembly.key 860).leftCharge (GramAssembly.key 860).rightCharge = raw40304 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40304Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40304 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 860).leftCharge (GramAssembly.key 860).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow860, Integer.Sparse.eval]

theorem keyMoment861 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 861) =
      Integer.Sparse.eval keyMomentRow861 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 861).leftCharge (GramAssembly.key 861).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2734) := by
    have ha : gramCharges (GramAssembly.key 861).leftCharge (GramAssembly.key 861).rightCharge = raw5951 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw5951Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical5951 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 861).leftCharge (GramAssembly.key 861).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow861, Integer.Sparse.eval]

theorem keyMoment862 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 862) =
      Integer.Sparse.eval keyMomentRow862 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 862).leftCharge (GramAssembly.key 862).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2740) := by
    have ha : gramCharges (GramAssembly.key 862).leftCharge (GramAssembly.key 862).rightCharge = raw40305 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40305Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40305 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 862).leftCharge (GramAssembly.key 862).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow862, Integer.Sparse.eval]

theorem keyMoment863 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 863) =
      Integer.Sparse.eval keyMomentRow863 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 863).leftCharge (GramAssembly.key 863).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2742) := by
    have ha : gramCharges (GramAssembly.key 863).leftCharge (GramAssembly.key 863).rightCharge = raw40306 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40306Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40306 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 863).leftCharge (GramAssembly.key 863).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow863, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
