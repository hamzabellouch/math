import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical325

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2144 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2144) =
      Integer.Sparse.eval keyMomentRow2144 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2144).leftCharge (GramAssembly.key 2144).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3051) := by
    have ha : gramCharges (GramAssembly.key 2144).leftCharge (GramAssembly.key 2144).rightCharge = raw41600 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41600Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41600 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2144).leftCharge (GramAssembly.key 2144).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2144).leftCharge (GramAssembly.key 2144).rightCharge = raw41601 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41601Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41601 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2144).leftCharge (GramAssembly.key 2144).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2144).leftCharge (GramAssembly.key 2144).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2144, Integer.Sparse.eval]
  ring

theorem keyMoment2145 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2145) =
      Integer.Sparse.eval keyMomentRow2145 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2145).leftCharge (GramAssembly.key 2145).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3074) := by
    have ha : gramCharges (GramAssembly.key 2145).leftCharge (GramAssembly.key 2145).rightCharge = raw41602 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41602Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41602 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2145).leftCharge (GramAssembly.key 2145).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5281) := by
    have ha : gramCharges (GramAssembly.key 2145).leftCharge (GramAssembly.key 2145).rightCharge = raw41603 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41603Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41603 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2145).leftCharge (GramAssembly.key 2145).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2145).leftCharge (GramAssembly.key 2145).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2145, Integer.Sparse.eval]
  ring

theorem keyMoment2146 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2146) =
      Integer.Sparse.eval keyMomentRow2146 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2146).leftCharge (GramAssembly.key 2146).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2778) := by
    have ha : gramCharges (GramAssembly.key 2146).leftCharge (GramAssembly.key 2146).rightCharge = raw41604 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41604Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41604 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2146).leftCharge (GramAssembly.key 2146).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4899) := by
    have ha : gramCharges (GramAssembly.key 2146).leftCharge (GramAssembly.key 2146).rightCharge = raw41605 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41605Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41605 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2146).leftCharge (GramAssembly.key 2146).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2146).leftCharge (GramAssembly.key 2146).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2146, Integer.Sparse.eval]
  ring

theorem keyMoment2147 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2147) =
      Integer.Sparse.eval keyMomentRow2147 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2147).leftCharge (GramAssembly.key 2147).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2777) := by
    have ha : gramCharges (GramAssembly.key 2147).leftCharge (GramAssembly.key 2147).rightCharge = raw41606 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41606Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41606 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2147).leftCharge (GramAssembly.key 2147).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5276) := by
    have ha : gramCharges (GramAssembly.key 2147).leftCharge (GramAssembly.key 2147).rightCharge = raw41607 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41607Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41607 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2147).leftCharge (GramAssembly.key 2147).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2147).leftCharge (GramAssembly.key 2147).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2147, Integer.Sparse.eval]
  ring

theorem keyMoment2148 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2148) =
      Integer.Sparse.eval keyMomentRow2148 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2148).leftCharge (GramAssembly.key 2148).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2776) := by
    have ha : gramCharges (GramAssembly.key 2148).leftCharge (GramAssembly.key 2148).rightCharge = raw41608 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41608Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41608 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2148).leftCharge (GramAssembly.key 2148).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5302) := by
    have ha : gramCharges (GramAssembly.key 2148).leftCharge (GramAssembly.key 2148).rightCharge = raw41609 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41609Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41609 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2148).leftCharge (GramAssembly.key 2148).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2148).leftCharge (GramAssembly.key 2148).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2148, Integer.Sparse.eval]
  ring

theorem keyMoment2149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2149) =
      Integer.Sparse.eval keyMomentRow2149 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2149).leftCharge (GramAssembly.key 2149).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2774) := by
    have ha : gramCharges (GramAssembly.key 2149).leftCharge (GramAssembly.key 2149).rightCharge = raw41610 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41610Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41610 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2149).leftCharge (GramAssembly.key 2149).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5300) := by
    have ha : gramCharges (GramAssembly.key 2149).leftCharge (GramAssembly.key 2149).rightCharge = raw41611 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41611Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41611 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2149).leftCharge (GramAssembly.key 2149).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2149).leftCharge (GramAssembly.key 2149).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2149, Integer.Sparse.eval]
  ring

theorem keyMoment2150 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2150) =
      Integer.Sparse.eval keyMomentRow2150 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2150).leftCharge (GramAssembly.key 2150).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2771) := by
    have ha : gramCharges (GramAssembly.key 2150).leftCharge (GramAssembly.key 2150).rightCharge = raw41612 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41612Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41612 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2150).leftCharge (GramAssembly.key 2150).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5297) := by
    have ha : gramCharges (GramAssembly.key 2150).leftCharge (GramAssembly.key 2150).rightCharge = raw41613 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41613Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41613 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2150).leftCharge (GramAssembly.key 2150).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2150).leftCharge (GramAssembly.key 2150).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2150, Integer.Sparse.eval]
  ring

theorem keyMoment2151 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2151) =
      Integer.Sparse.eval keyMomentRow2151 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2151).leftCharge (GramAssembly.key 2151).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2732) := by
    have ha : gramCharges (GramAssembly.key 2151).leftCharge (GramAssembly.key 2151).rightCharge = raw41614 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41614Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41614 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2151).leftCharge (GramAssembly.key 2151).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2151).leftCharge (GramAssembly.key 2151).rightCharge = raw41615 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41615Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41615 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2151).leftCharge (GramAssembly.key 2151).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2151).leftCharge (GramAssembly.key 2151).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2151, Integer.Sparse.eval]
  ring

theorem keyMoment2152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2152) =
      Integer.Sparse.eval keyMomentRow2152 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2152).leftCharge (GramAssembly.key 2152).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2731) := by
    have ha : gramCharges (GramAssembly.key 2152).leftCharge (GramAssembly.key 2152).rightCharge = raw41616 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41616Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41616 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2152).leftCharge (GramAssembly.key 2152).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5266) := by
    have ha : gramCharges (GramAssembly.key 2152).leftCharge (GramAssembly.key 2152).rightCharge = raw41617 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41617Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41617 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2152).leftCharge (GramAssembly.key 2152).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2152).leftCharge (GramAssembly.key 2152).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2152, Integer.Sparse.eval]
  ring

theorem keyMoment2153 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2153) =
      Integer.Sparse.eval keyMomentRow2153 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2153).leftCharge (GramAssembly.key 2153).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2729) := by
    have ha : gramCharges (GramAssembly.key 2153).leftCharge (GramAssembly.key 2153).rightCharge = raw41618 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41618Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41618 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2153).leftCharge (GramAssembly.key 2153).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5264) := by
    have ha : gramCharges (GramAssembly.key 2153).leftCharge (GramAssembly.key 2153).rightCharge = raw41619 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41619Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41619 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2153).leftCharge (GramAssembly.key 2153).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2153).leftCharge (GramAssembly.key 2153).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2153, Integer.Sparse.eval]
  ring

theorem keyMoment2154 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2154) =
      Integer.Sparse.eval keyMomentRow2154 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2154).leftCharge (GramAssembly.key 2154).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2677) := by
    have ha : gramCharges (GramAssembly.key 2154).leftCharge (GramAssembly.key 2154).rightCharge = raw41620 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41620Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41620 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2154).leftCharge (GramAssembly.key 2154).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5232) := by
    have ha : gramCharges (GramAssembly.key 2154).leftCharge (GramAssembly.key 2154).rightCharge = raw41621 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41621Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41621 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2154).leftCharge (GramAssembly.key 2154).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2154).leftCharge (GramAssembly.key 2154).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2154, Integer.Sparse.eval]
  ring

theorem keyMoment2155 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2155) =
      Integer.Sparse.eval keyMomentRow2155 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2155).leftCharge (GramAssembly.key 2155).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2748) := by
    have ha : gramCharges (GramAssembly.key 2155).leftCharge (GramAssembly.key 2155).rightCharge = raw41622 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41622Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41622 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2155).leftCharge (GramAssembly.key 2155).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5279) := by
    have ha : gramCharges (GramAssembly.key 2155).leftCharge (GramAssembly.key 2155).rightCharge = raw41623 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41623Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41623 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2155).leftCharge (GramAssembly.key 2155).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2155).leftCharge (GramAssembly.key 2155).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2155, Integer.Sparse.eval]
  ring

theorem keyMoment2156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2156) =
      Integer.Sparse.eval keyMomentRow2156 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2156).leftCharge (GramAssembly.key 2156).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2773) := by
    have ha : gramCharges (GramAssembly.key 2156).leftCharge (GramAssembly.key 2156).rightCharge = raw41624 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41624Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41624 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2156).leftCharge (GramAssembly.key 2156).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2156).leftCharge (GramAssembly.key 2156).rightCharge = raw41625 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41625Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41625 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2156).leftCharge (GramAssembly.key 2156).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2156).leftCharge (GramAssembly.key 2156).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2156, Integer.Sparse.eval]
  ring

theorem keyMoment2157 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2157) =
      Integer.Sparse.eval keyMomentRow2157 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2157).leftCharge (GramAssembly.key 2157).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2775) := by
    have ha : gramCharges (GramAssembly.key 2157).leftCharge (GramAssembly.key 2157).rightCharge = raw41626 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41626Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41626 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2157).leftCharge (GramAssembly.key 2157).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5301) := by
    have ha : gramCharges (GramAssembly.key 2157).leftCharge (GramAssembly.key 2157).rightCharge = raw41627 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41627Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41627 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2157).leftCharge (GramAssembly.key 2157).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2157).leftCharge (GramAssembly.key 2157).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2157, Integer.Sparse.eval]
  ring

theorem keyMoment2158 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2158) =
      Integer.Sparse.eval keyMomentRow2158 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2158).leftCharge (GramAssembly.key 2158).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2697) := by
    have ha : gramCharges (GramAssembly.key 2158).leftCharge (GramAssembly.key 2158).rightCharge = raw41628 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41628Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41628 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2158).leftCharge (GramAssembly.key 2158).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5243) := by
    have ha : gramCharges (GramAssembly.key 2158).leftCharge (GramAssembly.key 2158).rightCharge = raw41629 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41629Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41629 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2158).leftCharge (GramAssembly.key 2158).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2158).leftCharge (GramAssembly.key 2158).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2158, Integer.Sparse.eval]
  ring

theorem keyMoment2159 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2159) =
      Integer.Sparse.eval keyMomentRow2159 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2159).leftCharge (GramAssembly.key 2159).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2728) := by
    have ha : gramCharges (GramAssembly.key 2159).leftCharge (GramAssembly.key 2159).rightCharge = raw41630 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41630Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41630 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2159).leftCharge (GramAssembly.key 2159).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5263) := by
    have ha : gramCharges (GramAssembly.key 2159).leftCharge (GramAssembly.key 2159).rightCharge = raw41631 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41631Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41631 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2159).leftCharge (GramAssembly.key 2159).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2159).leftCharge (GramAssembly.key 2159).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2159, Integer.Sparse.eval]
  ring

theorem keyMoment2160 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2160) =
      Integer.Sparse.eval keyMomentRow2160 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2160).leftCharge (GramAssembly.key 2160).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2730) := by
    have ha : gramCharges (GramAssembly.key 2160).leftCharge (GramAssembly.key 2160).rightCharge = raw41632 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41632Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41632 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2160).leftCharge (GramAssembly.key 2160).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2160).leftCharge (GramAssembly.key 2160).rightCharge = raw41633 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41633Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41633 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2160).leftCharge (GramAssembly.key 2160).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2160).leftCharge (GramAssembly.key 2160).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2160, Integer.Sparse.eval]
  ring

theorem keyMoment2161 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2161) =
      Integer.Sparse.eval keyMomentRow2161 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2161).leftCharge (GramAssembly.key 2161).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2676) := by
    have ha : gramCharges (GramAssembly.key 2161).leftCharge (GramAssembly.key 2161).rightCharge = raw41634 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41634Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41634 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2161).leftCharge (GramAssembly.key 2161).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5231) := by
    have ha : gramCharges (GramAssembly.key 2161).leftCharge (GramAssembly.key 2161).rightCharge = raw41635 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41635Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41635 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2161).leftCharge (GramAssembly.key 2161).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2161).leftCharge (GramAssembly.key 2161).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2161, Integer.Sparse.eval]
  ring

theorem keyMoment2162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2162) =
      Integer.Sparse.eval keyMomentRow2162 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2162).leftCharge (GramAssembly.key 2162).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2755) := by
    have ha : gramCharges (GramAssembly.key 2162).leftCharge (GramAssembly.key 2162).rightCharge = raw41636 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41636Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41636 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2162).leftCharge (GramAssembly.key 2162).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4890) := by
    have ha : gramCharges (GramAssembly.key 2162).leftCharge (GramAssembly.key 2162).rightCharge = raw41637 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41637Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41637 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2162).leftCharge (GramAssembly.key 2162).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2162).leftCharge (GramAssembly.key 2162).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2162, Integer.Sparse.eval]
  ring

theorem keyMoment2163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2163) =
      Integer.Sparse.eval keyMomentRow2163 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2163).leftCharge (GramAssembly.key 2163).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2754) := by
    have ha : gramCharges (GramAssembly.key 2163).leftCharge (GramAssembly.key 2163).rightCharge = raw41638 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41638Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41638 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2163).leftCharge (GramAssembly.key 2163).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5270) := by
    have ha : gramCharges (GramAssembly.key 2163).leftCharge (GramAssembly.key 2163).rightCharge = raw41639 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41639Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41639 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2163).leftCharge (GramAssembly.key 2163).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2163).leftCharge (GramAssembly.key 2163).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2163, Integer.Sparse.eval]
  ring

theorem keyMoment2164 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2164) =
      Integer.Sparse.eval keyMomentRow2164 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2164).leftCharge (GramAssembly.key 2164).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2753) := by
    have ha : gramCharges (GramAssembly.key 2164).leftCharge (GramAssembly.key 2164).rightCharge = raw41640 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41640Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41640 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2164).leftCharge (GramAssembly.key 2164).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5284) := by
    have ha : gramCharges (GramAssembly.key 2164).leftCharge (GramAssembly.key 2164).rightCharge = raw41641 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41641Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41641 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2164).leftCharge (GramAssembly.key 2164).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2164).leftCharge (GramAssembly.key 2164).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2164, Integer.Sparse.eval]
  ring

theorem keyMoment2165 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2165) =
      Integer.Sparse.eval keyMomentRow2165 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2165).leftCharge (GramAssembly.key 2165).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2751) := by
    have ha : gramCharges (GramAssembly.key 2165).leftCharge (GramAssembly.key 2165).rightCharge = raw41642 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41642Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41642 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2165).leftCharge (GramAssembly.key 2165).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5282) := by
    have ha : gramCharges (GramAssembly.key 2165).leftCharge (GramAssembly.key 2165).rightCharge = raw41643 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41643Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41643 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2165).leftCharge (GramAssembly.key 2165).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2165).leftCharge (GramAssembly.key 2165).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2165, Integer.Sparse.eval]
  ring

theorem keyMoment2166 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2166) =
      Integer.Sparse.eval keyMomentRow2166 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2166).leftCharge (GramAssembly.key 2166).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2748) := by
    have ha : gramCharges (GramAssembly.key 2166).leftCharge (GramAssembly.key 2166).rightCharge = raw41644 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41644Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41644 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2166).leftCharge (GramAssembly.key 2166).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5279) := by
    have ha : gramCharges (GramAssembly.key 2166).leftCharge (GramAssembly.key 2166).rightCharge = raw41645 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41645Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41645 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2166).leftCharge (GramAssembly.key 2166).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2166).leftCharge (GramAssembly.key 2166).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2166, Integer.Sparse.eval]
  ring

theorem keyMoment2167 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2167) =
      Integer.Sparse.eval keyMomentRow2167 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2167).leftCharge (GramAssembly.key 2167).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2710) := by
    have ha : gramCharges (GramAssembly.key 2167).leftCharge (GramAssembly.key 2167).rightCharge = raw41646 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41646Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41646 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2167).leftCharge (GramAssembly.key 2167).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2167).leftCharge (GramAssembly.key 2167).rightCharge = raw41647 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41647Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41647 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2167).leftCharge (GramAssembly.key 2167).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2167).leftCharge (GramAssembly.key 2167).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2167, Integer.Sparse.eval]
  ring

theorem keyMoment2168 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2168) =
      Integer.Sparse.eval keyMomentRow2168 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2168).leftCharge (GramAssembly.key 2168).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2708) := by
    have ha : gramCharges (GramAssembly.key 2168).leftCharge (GramAssembly.key 2168).rightCharge = raw41648 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41648Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41648 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2168).leftCharge (GramAssembly.key 2168).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5249) := by
    have ha : gramCharges (GramAssembly.key 2168).leftCharge (GramAssembly.key 2168).rightCharge = raw41649 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41649Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41649 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2168).leftCharge (GramAssembly.key 2168).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2168).leftCharge (GramAssembly.key 2168).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2168, Integer.Sparse.eval]
  ring

theorem keyMoment2169 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2169) =
      Integer.Sparse.eval keyMomentRow2169 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2169).leftCharge (GramAssembly.key 2169).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2661) := by
    have ha : gramCharges (GramAssembly.key 2169).leftCharge (GramAssembly.key 2169).rightCharge = raw41650 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41650Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41650 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2169).leftCharge (GramAssembly.key 2169).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5219) := by
    have ha : gramCharges (GramAssembly.key 2169).leftCharge (GramAssembly.key 2169).rightCharge = raw41651 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41651Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41651 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2169).leftCharge (GramAssembly.key 2169).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2169).leftCharge (GramAssembly.key 2169).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2169, Integer.Sparse.eval]
  ring

theorem keyMoment2170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2170) =
      Integer.Sparse.eval keyMomentRow2170 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2170).leftCharge (GramAssembly.key 2170).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2747) := by
    have ha : gramCharges (GramAssembly.key 2170).leftCharge (GramAssembly.key 2170).rightCharge = raw41652 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41652Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41652 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2170).leftCharge (GramAssembly.key 2170).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5278) := by
    have ha : gramCharges (GramAssembly.key 2170).leftCharge (GramAssembly.key 2170).rightCharge = raw41653 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41653Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41653 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2170).leftCharge (GramAssembly.key 2170).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2170).leftCharge (GramAssembly.key 2170).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2170, Integer.Sparse.eval]
  ring

theorem keyMoment2171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2171) =
      Integer.Sparse.eval keyMomentRow2171 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2171).leftCharge (GramAssembly.key 2171).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2750) := by
    have ha : gramCharges (GramAssembly.key 2171).leftCharge (GramAssembly.key 2171).rightCharge = raw41654 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41654Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41654 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2171).leftCharge (GramAssembly.key 2171).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5281) := by
    have ha : gramCharges (GramAssembly.key 2171).leftCharge (GramAssembly.key 2171).rightCharge = raw41655 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41655Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41655 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2171).leftCharge (GramAssembly.key 2171).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2171).leftCharge (GramAssembly.key 2171).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2171, Integer.Sparse.eval]
  ring

theorem keyMoment2172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2172) =
      Integer.Sparse.eval keyMomentRow2172 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2172).leftCharge (GramAssembly.key 2172).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2769) := by
    have ha : gramCharges (GramAssembly.key 2172).leftCharge (GramAssembly.key 2172).rightCharge = raw41656 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41656Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41656 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2172).leftCharge (GramAssembly.key 2172).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5295) := by
    have ha : gramCharges (GramAssembly.key 2172).leftCharge (GramAssembly.key 2172).rightCharge = raw41657 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41657Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41657 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2172).leftCharge (GramAssembly.key 2172).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2172).leftCharge (GramAssembly.key 2172).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2172, Integer.Sparse.eval]
  ring

theorem keyMoment2173 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2173) =
      Integer.Sparse.eval keyMomentRow2173 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2173).leftCharge (GramAssembly.key 2173).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2761) := by
    have ha : gramCharges (GramAssembly.key 2173).leftCharge (GramAssembly.key 2173).rightCharge = raw41658 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41658Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41658 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2173).leftCharge (GramAssembly.key 2173).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5175) := by
    have ha : gramCharges (GramAssembly.key 2173).leftCharge (GramAssembly.key 2173).rightCharge = raw41659 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41659Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41659 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2173).leftCharge (GramAssembly.key 2173).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2173).leftCharge (GramAssembly.key 2173).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2173, Integer.Sparse.eval]
  ring

theorem keyMoment2174 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2174) =
      Integer.Sparse.eval keyMomentRow2174 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2174).leftCharge (GramAssembly.key 2174).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2724) := by
    have ha : gramCharges (GramAssembly.key 2174).leftCharge (GramAssembly.key 2174).rightCharge = raw41660 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41660Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41660 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2174).leftCharge (GramAssembly.key 2174).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2174).leftCharge (GramAssembly.key 2174).rightCharge = raw41661 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41661Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41661 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2174).leftCharge (GramAssembly.key 2174).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2174).leftCharge (GramAssembly.key 2174).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2174, Integer.Sparse.eval]
  ring

theorem keyMoment2175 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2175) =
      Integer.Sparse.eval keyMomentRow2175 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2175).leftCharge (GramAssembly.key 2175).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2719) := by
    have ha : gramCharges (GramAssembly.key 2175).leftCharge (GramAssembly.key 2175).rightCharge = raw41662 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41662Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41662 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2175).leftCharge (GramAssembly.key 2175).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5161) := by
    have ha : gramCharges (GramAssembly.key 2175).leftCharge (GramAssembly.key 2175).rightCharge = raw41663 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41663Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41663 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2175).leftCharge (GramAssembly.key 2175).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2175).leftCharge (GramAssembly.key 2175).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2175, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
