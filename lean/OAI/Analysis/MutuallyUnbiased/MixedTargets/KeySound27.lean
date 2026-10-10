import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical314
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical315

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment864 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 864) =
      Integer.Sparse.eval keyMomentRow864 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 864).leftCharge (GramAssembly.key 864).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2743) := by
    have ha : gramCharges (GramAssembly.key 864).leftCharge (GramAssembly.key 864).rightCharge = raw40307 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40307Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40307 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 864).leftCharge (GramAssembly.key 864).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow864, Integer.Sparse.eval]

theorem keyMoment865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 865) =
      Integer.Sparse.eval keyMomentRow865 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 865).leftCharge (GramAssembly.key 865).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2744) := by
    have ha : gramCharges (GramAssembly.key 865).leftCharge (GramAssembly.key 865).rightCharge = raw40308 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40308Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40308 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 865).leftCharge (GramAssembly.key 865).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow865, Integer.Sparse.eval]

theorem keyMoment866 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 866) =
      Integer.Sparse.eval keyMomentRow866 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 866).leftCharge (GramAssembly.key 866).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2722) := by
    have ha : gramCharges (GramAssembly.key 866).leftCharge (GramAssembly.key 866).rightCharge = raw40309 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40309Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40309 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 866).leftCharge (GramAssembly.key 866).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow866, Integer.Sparse.eval]

theorem keyMoment867 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 867) =
      Integer.Sparse.eval keyMomentRow867 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 867).leftCharge (GramAssembly.key 867).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2723) := by
    have ha : gramCharges (GramAssembly.key 867).leftCharge (GramAssembly.key 867).rightCharge = raw40310 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40310Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40310 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 867).leftCharge (GramAssembly.key 867).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow867, Integer.Sparse.eval]

theorem keyMoment868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 868) =
      Integer.Sparse.eval keyMomentRow868 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 868).leftCharge (GramAssembly.key 868).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2724) := by
    have ha : gramCharges (GramAssembly.key 868).leftCharge (GramAssembly.key 868).rightCharge = raw40311 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40311Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40311 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 868).leftCharge (GramAssembly.key 868).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow868, Integer.Sparse.eval]

theorem keyMoment869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 869) =
      Integer.Sparse.eval keyMomentRow869 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 869).leftCharge (GramAssembly.key 869).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2731) := by
    have ha : gramCharges (GramAssembly.key 869).leftCharge (GramAssembly.key 869).rightCharge = raw40312 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40312Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40312 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 869).leftCharge (GramAssembly.key 869).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow869, Integer.Sparse.eval]

theorem keyMoment870 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 870) =
      Integer.Sparse.eval keyMomentRow870 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 870).leftCharge (GramAssembly.key 870).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2732) := by
    have ha : gramCharges (GramAssembly.key 870).leftCharge (GramAssembly.key 870).rightCharge = raw40313 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40313Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40313 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 870).leftCharge (GramAssembly.key 870).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow870, Integer.Sparse.eval]

theorem keyMoment871 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 871) =
      Integer.Sparse.eval keyMomentRow871 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 871).leftCharge (GramAssembly.key 871).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2738) := by
    have ha : gramCharges (GramAssembly.key 871).leftCharge (GramAssembly.key 871).rightCharge = raw40314 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40314Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40314 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 871).leftCharge (GramAssembly.key 871).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow871, Integer.Sparse.eval]

theorem keyMoment872 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 872) =
      Integer.Sparse.eval keyMomentRow872 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 872).leftCharge (GramAssembly.key 872).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2739) := by
    have ha : gramCharges (GramAssembly.key 872).leftCharge (GramAssembly.key 872).rightCharge = raw40315 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40315Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40315 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 872).leftCharge (GramAssembly.key 872).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow872, Integer.Sparse.eval]

theorem keyMoment873 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 873) =
      Integer.Sparse.eval keyMomentRow873 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 873).leftCharge (GramAssembly.key 873).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2741) := by
    have ha : gramCharges (GramAssembly.key 873).leftCharge (GramAssembly.key 873).rightCharge = raw40316 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40316Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40316 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 873).leftCharge (GramAssembly.key 873).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow873, Integer.Sparse.eval]

theorem keyMoment874 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 874) =
      Integer.Sparse.eval keyMomentRow874 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 874).leftCharge (GramAssembly.key 874).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2709) := by
    have ha : gramCharges (GramAssembly.key 874).leftCharge (GramAssembly.key 874).rightCharge = raw40317 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40317Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40317 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 874).leftCharge (GramAssembly.key 874).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow874, Integer.Sparse.eval]

theorem keyMoment875 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 875) =
      Integer.Sparse.eval keyMomentRow875 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 875).leftCharge (GramAssembly.key 875).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2710) := by
    have ha : gramCharges (GramAssembly.key 875).leftCharge (GramAssembly.key 875).rightCharge = raw40318 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40318Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40318 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 875).leftCharge (GramAssembly.key 875).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow875, Integer.Sparse.eval]

theorem keyMoment876 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 876) =
      Integer.Sparse.eval keyMomentRow876 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 876).leftCharge (GramAssembly.key 876).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2720) := by
    have ha : gramCharges (GramAssembly.key 876).leftCharge (GramAssembly.key 876).rightCharge = raw40319 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40319Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40319 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 876).leftCharge (GramAssembly.key 876).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow876, Integer.Sparse.eval]

theorem keyMoment877 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 877) =
      Integer.Sparse.eval keyMomentRow877 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 877).leftCharge (GramAssembly.key 877).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2721) := by
    have ha : gramCharges (GramAssembly.key 877).leftCharge (GramAssembly.key 877).rightCharge = raw40320 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40320Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40320 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 877).leftCharge (GramAssembly.key 877).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow877, Integer.Sparse.eval]

theorem keyMoment878 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 878) =
      Integer.Sparse.eval keyMomentRow878 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 878).leftCharge (GramAssembly.key 878).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2730) := by
    have ha : gramCharges (GramAssembly.key 878).leftCharge (GramAssembly.key 878).rightCharge = raw40321 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40321Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40321 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 878).leftCharge (GramAssembly.key 878).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow878, Integer.Sparse.eval]

theorem keyMoment879 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 879) =
      Integer.Sparse.eval keyMomentRow879 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 879).leftCharge (GramAssembly.key 879).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2783) := by
    have ha : gramCharges (GramAssembly.key 879).leftCharge (GramAssembly.key 879).rightCharge = raw40322 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40322Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40322 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 879).leftCharge (GramAssembly.key 879).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow879, Integer.Sparse.eval]

theorem keyMoment880 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 880) =
      Integer.Sparse.eval keyMomentRow880 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 880).leftCharge (GramAssembly.key 880).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2789) := by
    have ha : gramCharges (GramAssembly.key 880).leftCharge (GramAssembly.key 880).rightCharge = raw4485 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw4485Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical4485 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 880).leftCharge (GramAssembly.key 880).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow880, Integer.Sparse.eval]

theorem keyMoment881 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 881) =
      Integer.Sparse.eval keyMomentRow881 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 881).leftCharge (GramAssembly.key 881).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2765) := by
    have ha : gramCharges (GramAssembly.key 881).leftCharge (GramAssembly.key 881).rightCharge = raw40323 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40323Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40323 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 881).leftCharge (GramAssembly.key 881).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow881, Integer.Sparse.eval]

theorem keyMoment882 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 882) =
      Integer.Sparse.eval keyMomentRow882 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 882).leftCharge (GramAssembly.key 882).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2769) := by
    have ha : gramCharges (GramAssembly.key 882).leftCharge (GramAssembly.key 882).rightCharge = raw4702 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw4702Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical4702 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 882).leftCharge (GramAssembly.key 882).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow882, Integer.Sparse.eval]

theorem keyMoment883 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 883) =
      Integer.Sparse.eval keyMomentRow883 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 883).leftCharge (GramAssembly.key 883).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2774) := by
    have ha : gramCharges (GramAssembly.key 883).leftCharge (GramAssembly.key 883).rightCharge = raw40324 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40324Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40324 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 883).leftCharge (GramAssembly.key 883).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow883, Integer.Sparse.eval]

theorem keyMoment884 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 884) =
      Integer.Sparse.eval keyMomentRow884 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 884).leftCharge (GramAssembly.key 884).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2777) := by
    have ha : gramCharges (GramAssembly.key 884).leftCharge (GramAssembly.key 884).rightCharge = raw40325 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40325Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40325 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 884).leftCharge (GramAssembly.key 884).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow884, Integer.Sparse.eval]

theorem keyMoment885 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 885) =
      Integer.Sparse.eval keyMomentRow885 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 885).leftCharge (GramAssembly.key 885).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2781) := by
    have ha : gramCharges (GramAssembly.key 885).leftCharge (GramAssembly.key 885).rightCharge = raw40326 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40326Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40326 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 885).leftCharge (GramAssembly.key 885).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow885, Integer.Sparse.eval]

theorem keyMoment886 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 886) =
      Integer.Sparse.eval keyMomentRow886 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 886).leftCharge (GramAssembly.key 886).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2782) := by
    have ha : gramCharges (GramAssembly.key 886).leftCharge (GramAssembly.key 886).rightCharge = raw40327 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40327Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40327 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 886).leftCharge (GramAssembly.key 886).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow886, Integer.Sparse.eval]

theorem keyMoment887 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 887) =
      Integer.Sparse.eval keyMomentRow887 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 887).leftCharge (GramAssembly.key 887).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2751) := by
    have ha : gramCharges (GramAssembly.key 887).leftCharge (GramAssembly.key 887).rightCharge = raw40328 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40328Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40328 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 887).leftCharge (GramAssembly.key 887).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow887, Integer.Sparse.eval]

theorem keyMoment888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 888) =
      Integer.Sparse.eval keyMomentRow888 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 888).leftCharge (GramAssembly.key 888).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2754) := by
    have ha : gramCharges (GramAssembly.key 888).leftCharge (GramAssembly.key 888).rightCharge = raw40329 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40329Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40329 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 888).leftCharge (GramAssembly.key 888).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow888, Integer.Sparse.eval]

theorem keyMoment889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 889) =
      Integer.Sparse.eval keyMomentRow889 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 889).leftCharge (GramAssembly.key 889).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2763) := by
    have ha : gramCharges (GramAssembly.key 889).leftCharge (GramAssembly.key 889).rightCharge = raw40330 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40330Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40330 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 889).leftCharge (GramAssembly.key 889).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow889, Integer.Sparse.eval]

theorem keyMoment890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 890) =
      Integer.Sparse.eval keyMomentRow890 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 890).leftCharge (GramAssembly.key 890).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2764) := by
    have ha : gramCharges (GramAssembly.key 890).leftCharge (GramAssembly.key 890).rightCharge = raw40331 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40331Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40331 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 890).leftCharge (GramAssembly.key 890).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow890, Integer.Sparse.eval]

theorem keyMoment891 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 891) =
      Integer.Sparse.eval keyMomentRow891 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 891).leftCharge (GramAssembly.key 891).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2773) := by
    have ha : gramCharges (GramAssembly.key 891).leftCharge (GramAssembly.key 891).rightCharge = raw40332 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40332Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40332 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 891).leftCharge (GramAssembly.key 891).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow891, Integer.Sparse.eval]

theorem keyMoment892 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 892) =
      Integer.Sparse.eval keyMomentRow892 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 892).leftCharge (GramAssembly.key 892).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2750) := by
    have ha : gramCharges (GramAssembly.key 892).leftCharge (GramAssembly.key 892).rightCharge = raw40333 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40333Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40333 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 892).leftCharge (GramAssembly.key 892).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow892, Integer.Sparse.eval]

theorem keyMoment893 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 893) =
      Integer.Sparse.eval keyMomentRow893 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 893).leftCharge (GramAssembly.key 893).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2281) := by
    have ha : gramCharges (GramAssembly.key 893).leftCharge (GramAssembly.key 893).rightCharge = raw40334 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40334Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40334 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 893).leftCharge (GramAssembly.key 893).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow893, Integer.Sparse.eval]

theorem keyMoment894 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 894) =
      Integer.Sparse.eval keyMomentRow894 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 894).leftCharge (GramAssembly.key 894).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2734) := by
    have ha : gramCharges (GramAssembly.key 894).leftCharge (GramAssembly.key 894).rightCharge = raw40335 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40335Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40335 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 894).leftCharge (GramAssembly.key 894).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow894, Integer.Sparse.eval]

theorem keyMoment895 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 895) =
      Integer.Sparse.eval keyMomentRow895 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 895).leftCharge (GramAssembly.key 895).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3046) := by
    have ha : gramCharges (GramAssembly.key 895).leftCharge (GramAssembly.key 895).rightCharge = raw40336 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40336Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40336 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 895).leftCharge (GramAssembly.key 895).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow895, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
