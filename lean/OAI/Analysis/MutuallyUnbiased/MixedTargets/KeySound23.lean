import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical298
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical313
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical314

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment736 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 736) =
      Integer.Sparse.eval keyMomentRow736 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 736).leftCharge (GramAssembly.key 736).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 407) := by
    have ha : gramCharges (GramAssembly.key 736).leftCharge (GramAssembly.key 736).rightCharge = raw40184 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40184Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40184 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 736).leftCharge (GramAssembly.key 736).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow736, Integer.Sparse.eval]

theorem keyMoment737 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 737) =
      Integer.Sparse.eval keyMomentRow737 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 737).leftCharge (GramAssembly.key 737).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 379) := by
    have ha : gramCharges (GramAssembly.key 737).leftCharge (GramAssembly.key 737).rightCharge = raw40185 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40185Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40185 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 737).leftCharge (GramAssembly.key 737).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow737, Integer.Sparse.eval]

theorem keyMoment738 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 738) =
      Integer.Sparse.eval keyMomentRow738 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 738).leftCharge (GramAssembly.key 738).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 303) := by
    have ha : gramCharges (GramAssembly.key 738).leftCharge (GramAssembly.key 738).rightCharge = raw40186 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40186Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40186 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 738).leftCharge (GramAssembly.key 738).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow738, Integer.Sparse.eval]

theorem keyMoment739 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 739) =
      Integer.Sparse.eval keyMomentRow739 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 739).leftCharge (GramAssembly.key 739).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 98) := by
    have ha : gramCharges (GramAssembly.key 739).leftCharge (GramAssembly.key 739).rightCharge = raw40187 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40187Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40187 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 739).leftCharge (GramAssembly.key 739).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow739, Integer.Sparse.eval]

theorem keyMoment740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 740) =
      Integer.Sparse.eval keyMomentRow740 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 740).leftCharge (GramAssembly.key 740).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 100) := by
    have ha : gramCharges (GramAssembly.key 740).leftCharge (GramAssembly.key 740).rightCharge = raw40188 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40188Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40188 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 740).leftCharge (GramAssembly.key 740).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow740, Integer.Sparse.eval]

theorem keyMoment741 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 741) =
      Integer.Sparse.eval keyMomentRow741 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 741).leftCharge (GramAssembly.key 741).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 257) := by
    have ha : gramCharges (GramAssembly.key 741).leftCharge (GramAssembly.key 741).rightCharge = raw40189 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40189Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40189 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 741).leftCharge (GramAssembly.key 741).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow741, Integer.Sparse.eval]

theorem keyMoment742 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 742) =
      Integer.Sparse.eval keyMomentRow742 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 742).leftCharge (GramAssembly.key 742).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 242) := by
    have ha : gramCharges (GramAssembly.key 742).leftCharge (GramAssembly.key 742).rightCharge = raw40190 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40190Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40190 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 742).leftCharge (GramAssembly.key 742).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow742, Integer.Sparse.eval]

theorem keyMoment743 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 743) =
      Integer.Sparse.eval keyMomentRow743 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 743).leftCharge (GramAssembly.key 743).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 21) := by
    have ha : gramCharges (GramAssembly.key 743).leftCharge (GramAssembly.key 743).rightCharge = raw40191 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40191Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40191 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 743).leftCharge (GramAssembly.key 743).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow743, Integer.Sparse.eval]

theorem keyMoment744 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 744) =
      Integer.Sparse.eval keyMomentRow744 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 744).leftCharge (GramAssembly.key 744).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 8) := by
    have ha : gramCharges (GramAssembly.key 744).leftCharge (GramAssembly.key 744).rightCharge = raw40192 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40192Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40192 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 744).leftCharge (GramAssembly.key 744).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow744, Integer.Sparse.eval]

theorem keyMoment745 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 745) =
      Integer.Sparse.eval keyMomentRow745 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 745).leftCharge (GramAssembly.key 745).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 172) := by
    have ha : gramCharges (GramAssembly.key 745).leftCharge (GramAssembly.key 745).rightCharge = raw40193 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40193Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40193 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 745).leftCharge (GramAssembly.key 745).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow745, Integer.Sparse.eval]

theorem keyMoment746 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 746) =
      Integer.Sparse.eval keyMomentRow746 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 746).leftCharge (GramAssembly.key 746).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 321) := by
    have ha : gramCharges (GramAssembly.key 746).leftCharge (GramAssembly.key 746).rightCharge = raw40194 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40194Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40194 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 746).leftCharge (GramAssembly.key 746).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow746, Integer.Sparse.eval]

theorem keyMoment747 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 747) =
      Integer.Sparse.eval keyMomentRow747 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 747).leftCharge (GramAssembly.key 747).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 24) := by
    have ha : gramCharges (GramAssembly.key 747).leftCharge (GramAssembly.key 747).rightCharge = raw40195 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40195Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40195 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 747).leftCharge (GramAssembly.key 747).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow747, Integer.Sparse.eval]

theorem keyMoment748 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 748) =
      Integer.Sparse.eval keyMomentRow748 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 748).leftCharge (GramAssembly.key 748).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 163) := by
    have ha : gramCharges (GramAssembly.key 748).leftCharge (GramAssembly.key 748).rightCharge = raw40196 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40196Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40196 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 748).leftCharge (GramAssembly.key 748).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow748, Integer.Sparse.eval]

theorem keyMoment749 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 749) =
      Integer.Sparse.eval keyMomentRow749 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 749).leftCharge (GramAssembly.key 749).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 9) := by
    have ha : gramCharges (GramAssembly.key 749).leftCharge (GramAssembly.key 749).rightCharge = raw40197 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40197Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40197 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 749).leftCharge (GramAssembly.key 749).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow749, Integer.Sparse.eval]

theorem keyMoment750 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 750) =
      Integer.Sparse.eval keyMomentRow750 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 750).leftCharge (GramAssembly.key 750).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 260) := by
    have ha : gramCharges (GramAssembly.key 750).leftCharge (GramAssembly.key 750).rightCharge = raw40198 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40198Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40198 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 750).leftCharge (GramAssembly.key 750).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow750, Integer.Sparse.eval]

theorem keyMoment751 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 751) =
      Integer.Sparse.eval keyMomentRow751 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 751).leftCharge (GramAssembly.key 751).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 243) := by
    have ha : gramCharges (GramAssembly.key 751).leftCharge (GramAssembly.key 751).rightCharge = raw40199 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40199Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40199 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 751).leftCharge (GramAssembly.key 751).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow751, Integer.Sparse.eval]

theorem keyMoment752 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 752) =
      Integer.Sparse.eval keyMomentRow752 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 752).leftCharge (GramAssembly.key 752).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 171) := by
    have ha : gramCharges (GramAssembly.key 752).leftCharge (GramAssembly.key 752).rightCharge = raw40200 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40200Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40200 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 752).leftCharge (GramAssembly.key 752).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow752, Integer.Sparse.eval]

theorem keyMoment753 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 753) =
      Integer.Sparse.eval keyMomentRow753 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 753).leftCharge (GramAssembly.key 753).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 232) := by
    have ha : gramCharges (GramAssembly.key 753).leftCharge (GramAssembly.key 753).rightCharge = raw40201 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40201Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40201 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 753).leftCharge (GramAssembly.key 753).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow753, Integer.Sparse.eval]

theorem keyMoment754 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 754) =
      Integer.Sparse.eval keyMomentRow754 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 754).leftCharge (GramAssembly.key 754).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 259) := by
    have ha : gramCharges (GramAssembly.key 754).leftCharge (GramAssembly.key 754).rightCharge = raw40202 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40202Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40202 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 754).leftCharge (GramAssembly.key 754).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow754, Integer.Sparse.eval]

theorem keyMoment755 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 755) =
      Integer.Sparse.eval keyMomentRow755 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 755).leftCharge (GramAssembly.key 755).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 220) := by
    have ha : gramCharges (GramAssembly.key 755).leftCharge (GramAssembly.key 755).rightCharge = raw40203 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40203Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40203 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 755).leftCharge (GramAssembly.key 755).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow755, Integer.Sparse.eval]

theorem keyMoment756 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 756) =
      Integer.Sparse.eval keyMomentRow756 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 756).leftCharge (GramAssembly.key 756).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 505) := by
    have ha : gramCharges (GramAssembly.key 756).leftCharge (GramAssembly.key 756).rightCharge = raw40204 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40204Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40204 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 756).leftCharge (GramAssembly.key 756).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow756, Integer.Sparse.eval]

theorem keyMoment757 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 757) =
      Integer.Sparse.eval keyMomentRow757 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 757).leftCharge (GramAssembly.key 757).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 502) := by
    have ha : gramCharges (GramAssembly.key 757).leftCharge (GramAssembly.key 757).rightCharge = raw40205 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40205Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40205 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 757).leftCharge (GramAssembly.key 757).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow757, Integer.Sparse.eval]

theorem keyMoment758 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 758) =
      Integer.Sparse.eval keyMomentRow758 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 758).leftCharge (GramAssembly.key 758).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 449) := by
    have ha : gramCharges (GramAssembly.key 758).leftCharge (GramAssembly.key 758).rightCharge = raw40206 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40206Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40206 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 758).leftCharge (GramAssembly.key 758).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow758, Integer.Sparse.eval]

theorem keyMoment759 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 759) =
      Integer.Sparse.eval keyMomentRow759 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 759).leftCharge (GramAssembly.key 759).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 448) := by
    have ha : gramCharges (GramAssembly.key 759).leftCharge (GramAssembly.key 759).rightCharge = raw40207 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40207Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40207 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 759).leftCharge (GramAssembly.key 759).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow759, Integer.Sparse.eval]

theorem keyMoment760 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 760) =
      Integer.Sparse.eval keyMomentRow760 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 760).leftCharge (GramAssembly.key 760).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 436) := by
    have ha : gramCharges (GramAssembly.key 760).leftCharge (GramAssembly.key 760).rightCharge = raw40208 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40208Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40208 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 760).leftCharge (GramAssembly.key 760).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow760, Integer.Sparse.eval]

theorem keyMoment761 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 761) =
      Integer.Sparse.eval keyMomentRow761 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 761).leftCharge (GramAssembly.key 761).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 429) := by
    have ha : gramCharges (GramAssembly.key 761).leftCharge (GramAssembly.key 761).rightCharge = raw40209 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40209Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40209 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 761).leftCharge (GramAssembly.key 761).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow761, Integer.Sparse.eval]

theorem keyMoment762 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 762) =
      Integer.Sparse.eval keyMomentRow762 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 762).leftCharge (GramAssembly.key 762).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 504) := by
    have ha : gramCharges (GramAssembly.key 762).leftCharge (GramAssembly.key 762).rightCharge = raw40210 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40210Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40210 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 762).leftCharge (GramAssembly.key 762).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow762, Integer.Sparse.eval]

theorem keyMoment763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 763) =
      Integer.Sparse.eval keyMomentRow763 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 763).leftCharge (GramAssembly.key 763).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 525) := by
    have ha : gramCharges (GramAssembly.key 763).leftCharge (GramAssembly.key 763).rightCharge = raw40211 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40211Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40211 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 763).leftCharge (GramAssembly.key 763).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow763, Integer.Sparse.eval]

theorem keyMoment764 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 764) =
      Integer.Sparse.eval keyMomentRow764 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 764).leftCharge (GramAssembly.key 764).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 207) := by
    have ha : gramCharges (GramAssembly.key 764).leftCharge (GramAssembly.key 764).rightCharge = raw40212 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40212Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40212 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 764).leftCharge (GramAssembly.key 764).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow764, Integer.Sparse.eval]

theorem keyMoment765 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 765) =
      Integer.Sparse.eval keyMomentRow765 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 765).leftCharge (GramAssembly.key 765).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 371) := by
    have ha : gramCharges (GramAssembly.key 765).leftCharge (GramAssembly.key 765).rightCharge = raw40213 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40213Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40213 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 765).leftCharge (GramAssembly.key 765).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow765, Integer.Sparse.eval]

theorem keyMoment766 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 766) =
      Integer.Sparse.eval keyMomentRow766 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 766).leftCharge (GramAssembly.key 766).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 531) := by
    have ha : gramCharges (GramAssembly.key 766).leftCharge (GramAssembly.key 766).rightCharge = raw38154 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw38154Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical38154 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 766).leftCharge (GramAssembly.key 766).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow766, Integer.Sparse.eval]

theorem keyMoment767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 767) =
      Integer.Sparse.eval keyMomentRow767 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 767).leftCharge (GramAssembly.key 767).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 339) := by
    have ha : gramCharges (GramAssembly.key 767).leftCharge (GramAssembly.key 767).rightCharge = raw40214 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40214Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40214 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 767).leftCharge (GramAssembly.key 767).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow767, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
