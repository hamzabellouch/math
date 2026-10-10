import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys89
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical336

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2848 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2848) =
      Integer.Sparse.eval keyMomentRow2848 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2848).leftCharge (GramAssembly.key 2848).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3832) := by
    have ha : gramCharges (GramAssembly.key 2848).leftCharge (GramAssembly.key 2848).rightCharge = raw43008 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43008Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43008 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2848).leftCharge (GramAssembly.key 2848).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5379) := by
    have ha : gramCharges (GramAssembly.key 2848).leftCharge (GramAssembly.key 2848).rightCharge = raw43009 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43009Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43009 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2848).leftCharge (GramAssembly.key 2848).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2848).leftCharge (GramAssembly.key 2848).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2848, Integer.Sparse.eval]
  ring

theorem keyMoment2849 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2849) =
      Integer.Sparse.eval keyMomentRow2849 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2849).leftCharge (GramAssembly.key 2849).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4024) := by
    have ha : gramCharges (GramAssembly.key 2849).leftCharge (GramAssembly.key 2849).rightCharge = raw43010 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43010Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43010 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2849).leftCharge (GramAssembly.key 2849).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5445) := by
    have ha : gramCharges (GramAssembly.key 2849).leftCharge (GramAssembly.key 2849).rightCharge = raw43011 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43011Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43011 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2849).leftCharge (GramAssembly.key 2849).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2849).leftCharge (GramAssembly.key 2849).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2849, Integer.Sparse.eval]
  ring

theorem keyMoment2850 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2850) =
      Integer.Sparse.eval keyMomentRow2850 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2850).leftCharge (GramAssembly.key 2850).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3535) := by
    have ha : gramCharges (GramAssembly.key 2850).leftCharge (GramAssembly.key 2850).rightCharge = raw43012 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43012Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43012 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2850).leftCharge (GramAssembly.key 2850).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5266) := by
    have ha : gramCharges (GramAssembly.key 2850).leftCharge (GramAssembly.key 2850).rightCharge = raw43013 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43013Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43013 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2850).leftCharge (GramAssembly.key 2850).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2850).leftCharge (GramAssembly.key 2850).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2850, Integer.Sparse.eval]
  ring

theorem keyMoment2851 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2851) =
      Integer.Sparse.eval keyMomentRow2851 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2851).leftCharge (GramAssembly.key 2851).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3294) := by
    have ha : gramCharges (GramAssembly.key 2851).leftCharge (GramAssembly.key 2851).rightCharge = raw43014 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43014Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43014 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2851).leftCharge (GramAssembly.key 2851).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4603) := by
    have ha : gramCharges (GramAssembly.key 2851).leftCharge (GramAssembly.key 2851).rightCharge = raw43015 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43015Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43015 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2851).leftCharge (GramAssembly.key 2851).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2851).leftCharge (GramAssembly.key 2851).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2851, Integer.Sparse.eval]
  ring

theorem keyMoment2852 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2852) =
      Integer.Sparse.eval keyMomentRow2852 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2852).leftCharge (GramAssembly.key 2852).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3290) := by
    have ha : gramCharges (GramAssembly.key 2852).leftCharge (GramAssembly.key 2852).rightCharge = raw43016 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43016Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43016 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2852).leftCharge (GramAssembly.key 2852).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4590) := by
    have ha : gramCharges (GramAssembly.key 2852).leftCharge (GramAssembly.key 2852).rightCharge = raw43017 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43017Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43017 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2852).leftCharge (GramAssembly.key 2852).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2852).leftCharge (GramAssembly.key 2852).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2852, Integer.Sparse.eval]
  ring

theorem keyMoment2853 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2853) =
      Integer.Sparse.eval keyMomentRow2853 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2853).leftCharge (GramAssembly.key 2853).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3516) := by
    have ha : gramCharges (GramAssembly.key 2853).leftCharge (GramAssembly.key 2853).rightCharge = raw43018 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43018Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43018 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2853).leftCharge (GramAssembly.key 2853).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5129) := by
    have ha : gramCharges (GramAssembly.key 2853).leftCharge (GramAssembly.key 2853).rightCharge = raw43019 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43019Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43019 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2853).leftCharge (GramAssembly.key 2853).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2853).leftCharge (GramAssembly.key 2853).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2853, Integer.Sparse.eval]
  ring

theorem keyMoment2854 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2854) =
      Integer.Sparse.eval keyMomentRow2854 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2854).leftCharge (GramAssembly.key 2854).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3291) := by
    have ha : gramCharges (GramAssembly.key 2854).leftCharge (GramAssembly.key 2854).rightCharge = raw43020 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43020Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43020 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2854).leftCharge (GramAssembly.key 2854).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4591) := by
    have ha : gramCharges (GramAssembly.key 2854).leftCharge (GramAssembly.key 2854).rightCharge = raw43021 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43021Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43021 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2854).leftCharge (GramAssembly.key 2854).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2854).leftCharge (GramAssembly.key 2854).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2854, Integer.Sparse.eval]
  ring

theorem keyMoment2855 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2855) =
      Integer.Sparse.eval keyMomentRow2855 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2855).leftCharge (GramAssembly.key 2855).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3835) := by
    have ha : gramCharges (GramAssembly.key 2855).leftCharge (GramAssembly.key 2855).rightCharge = raw43022 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43022Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43022 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2855).leftCharge (GramAssembly.key 2855).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5377) := by
    have ha : gramCharges (GramAssembly.key 2855).leftCharge (GramAssembly.key 2855).rightCharge = raw43023 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43023Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43023 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2855).leftCharge (GramAssembly.key 2855).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2855).leftCharge (GramAssembly.key 2855).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2855, Integer.Sparse.eval]
  ring

theorem keyMoment2856 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2856) =
      Integer.Sparse.eval keyMomentRow2856 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2856).leftCharge (GramAssembly.key 2856).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3297) := by
    have ha : gramCharges (GramAssembly.key 2856).leftCharge (GramAssembly.key 2856).rightCharge = raw43024 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43024Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43024 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2856).leftCharge (GramAssembly.key 2856).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4593) := by
    have ha : gramCharges (GramAssembly.key 2856).leftCharge (GramAssembly.key 2856).rightCharge = raw43025 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43025Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43025 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2856).leftCharge (GramAssembly.key 2856).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2856).leftCharge (GramAssembly.key 2856).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2856, Integer.Sparse.eval]
  ring

theorem keyMoment2857 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2857) =
      Integer.Sparse.eval keyMomentRow2857 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2857).leftCharge (GramAssembly.key 2857).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2235) := by
    have ha : gramCharges (GramAssembly.key 2857).leftCharge (GramAssembly.key 2857).rightCharge = raw43026 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43026Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43026 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2857).leftCharge (GramAssembly.key 2857).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4886) := by
    have ha : gramCharges (GramAssembly.key 2857).leftCharge (GramAssembly.key 2857).rightCharge = raw43027 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43027Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43027 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2857).leftCharge (GramAssembly.key 2857).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2857).leftCharge (GramAssembly.key 2857).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2857, Integer.Sparse.eval]
  ring

theorem keyMoment2858 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2858) =
      Integer.Sparse.eval keyMomentRow2858 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2858).leftCharge (GramAssembly.key 2858).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2187) := by
    have ha : gramCharges (GramAssembly.key 2858).leftCharge (GramAssembly.key 2858).rightCharge = raw43028 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43028Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43028 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2858).leftCharge (GramAssembly.key 2858).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4830) := by
    have ha : gramCharges (GramAssembly.key 2858).leftCharge (GramAssembly.key 2858).rightCharge = raw43029 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43029Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43029 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2858).leftCharge (GramAssembly.key 2858).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2858).leftCharge (GramAssembly.key 2858).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2858, Integer.Sparse.eval]
  ring

theorem keyMoment2859 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2859) =
      Integer.Sparse.eval keyMomentRow2859 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2859).leftCharge (GramAssembly.key 2859).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2233) := by
    have ha : gramCharges (GramAssembly.key 2859).leftCharge (GramAssembly.key 2859).rightCharge = raw43030 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43030Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43030 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2859).leftCharge (GramAssembly.key 2859).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4885) := by
    have ha : gramCharges (GramAssembly.key 2859).leftCharge (GramAssembly.key 2859).rightCharge = raw43031 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43031Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43031 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2859).leftCharge (GramAssembly.key 2859).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2859).leftCharge (GramAssembly.key 2859).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2859, Integer.Sparse.eval]
  ring

theorem keyMoment2860 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2860) =
      Integer.Sparse.eval keyMomentRow2860 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2860).leftCharge (GramAssembly.key 2860).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2232) := by
    have ha : gramCharges (GramAssembly.key 2860).leftCharge (GramAssembly.key 2860).rightCharge = raw43032 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43032Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43032 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2860).leftCharge (GramAssembly.key 2860).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4863) := by
    have ha : gramCharges (GramAssembly.key 2860).leftCharge (GramAssembly.key 2860).rightCharge = raw43033 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43033Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43033 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2860).leftCharge (GramAssembly.key 2860).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2860).leftCharge (GramAssembly.key 2860).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2860, Integer.Sparse.eval]
  ring

theorem keyMoment2861 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2861) =
      Integer.Sparse.eval keyMomentRow2861 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2861).leftCharge (GramAssembly.key 2861).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3221) := by
    have ha : gramCharges (GramAssembly.key 2861).leftCharge (GramAssembly.key 2861).rightCharge = raw43034 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43034Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43034 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2861).leftCharge (GramAssembly.key 2861).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4885) := by
    have ha : gramCharges (GramAssembly.key 2861).leftCharge (GramAssembly.key 2861).rightCharge = raw43035 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43035Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43035 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2861).leftCharge (GramAssembly.key 2861).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2861).leftCharge (GramAssembly.key 2861).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2861, Integer.Sparse.eval]
  ring

theorem keyMoment2862 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2862) =
      Integer.Sparse.eval keyMomentRow2862 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2862).leftCharge (GramAssembly.key 2862).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3059) := by
    have ha : gramCharges (GramAssembly.key 2862).leftCharge (GramAssembly.key 2862).rightCharge = raw43036 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43036Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43036 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2862).leftCharge (GramAssembly.key 2862).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5277) := by
    have ha : gramCharges (GramAssembly.key 2862).leftCharge (GramAssembly.key 2862).rightCharge = raw43037 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43037Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43037 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2862).leftCharge (GramAssembly.key 2862).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2862).leftCharge (GramAssembly.key 2862).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2862, Integer.Sparse.eval]
  ring

theorem keyMoment2863 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2863) =
      Integer.Sparse.eval keyMomentRow2863 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2863).leftCharge (GramAssembly.key 2863).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2690) := by
    have ha : gramCharges (GramAssembly.key 2863).leftCharge (GramAssembly.key 2863).rightCharge = raw43038 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43038Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43038 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2863).leftCharge (GramAssembly.key 2863).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4975) := by
    have ha : gramCharges (GramAssembly.key 2863).leftCharge (GramAssembly.key 2863).rightCharge = raw43039 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43039Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43039 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2863).leftCharge (GramAssembly.key 2863).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2863).leftCharge (GramAssembly.key 2863).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2863, Integer.Sparse.eval]
  ring

theorem keyMoment2864 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2864) =
      Integer.Sparse.eval keyMomentRow2864 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2864).leftCharge (GramAssembly.key 2864).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3058) := by
    have ha : gramCharges (GramAssembly.key 2864).leftCharge (GramAssembly.key 2864).rightCharge = raw43040 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43040Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43040 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2864).leftCharge (GramAssembly.key 2864).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5097) := by
    have ha : gramCharges (GramAssembly.key 2864).leftCharge (GramAssembly.key 2864).rightCharge = raw43041 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43041Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43041 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2864).leftCharge (GramAssembly.key 2864).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2864).leftCharge (GramAssembly.key 2864).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2864, Integer.Sparse.eval]
  ring

theorem keyMoment2865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2865) =
      Integer.Sparse.eval keyMomentRow2865 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2865).leftCharge (GramAssembly.key 2865).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2688) := by
    have ha : gramCharges (GramAssembly.key 2865).leftCharge (GramAssembly.key 2865).rightCharge = raw43042 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43042Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43042 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2865).leftCharge (GramAssembly.key 2865).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4540) := by
    have ha : gramCharges (GramAssembly.key 2865).leftCharge (GramAssembly.key 2865).rightCharge = raw43043 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43043Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43043 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2865).leftCharge (GramAssembly.key 2865).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2865).leftCharge (GramAssembly.key 2865).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2865, Integer.Sparse.eval]
  ring

theorem keyMoment2866 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2866) =
      Integer.Sparse.eval keyMomentRow2866 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2866).leftCharge (GramAssembly.key 2866).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1700) := by
    have ha : gramCharges (GramAssembly.key 2866).leftCharge (GramAssembly.key 2866).rightCharge = raw43044 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43044Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43044 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2866).leftCharge (GramAssembly.key 2866).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4494) := by
    have ha : gramCharges (GramAssembly.key 2866).leftCharge (GramAssembly.key 2866).rightCharge = raw43045 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43045Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43045 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2866).leftCharge (GramAssembly.key 2866).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2866).leftCharge (GramAssembly.key 2866).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2866, Integer.Sparse.eval]
  ring

theorem keyMoment2867 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2867) =
      Integer.Sparse.eval keyMomentRow2867 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2867).leftCharge (GramAssembly.key 2867).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1699) := by
    have ha : gramCharges (GramAssembly.key 2867).leftCharge (GramAssembly.key 2867).rightCharge = raw43046 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43046Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43046 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2867).leftCharge (GramAssembly.key 2867).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4473) := by
    have ha : gramCharges (GramAssembly.key 2867).leftCharge (GramAssembly.key 2867).rightCharge = raw43047 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43047Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43047 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2867).leftCharge (GramAssembly.key 2867).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2867).leftCharge (GramAssembly.key 2867).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2867, Integer.Sparse.eval]
  ring

theorem keyMoment2868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2868) =
      Integer.Sparse.eval keyMomentRow2868 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2868).leftCharge (GramAssembly.key 2868).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1502) := by
    have ha : gramCharges (GramAssembly.key 2868).leftCharge (GramAssembly.key 2868).rightCharge = raw43048 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43048Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43048 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2868).leftCharge (GramAssembly.key 2868).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4169) := by
    have ha : gramCharges (GramAssembly.key 2868).leftCharge (GramAssembly.key 2868).rightCharge = raw43049 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43049Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43049 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2868).leftCharge (GramAssembly.key 2868).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2868).leftCharge (GramAssembly.key 2868).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2868, Integer.Sparse.eval]
  ring

theorem keyMoment2869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2869) =
      Integer.Sparse.eval keyMomentRow2869 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2869).leftCharge (GramAssembly.key 2869).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1501) := by
    have ha : gramCharges (GramAssembly.key 2869).leftCharge (GramAssembly.key 2869).rightCharge = raw43050 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43050Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43050 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2869).leftCharge (GramAssembly.key 2869).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4149) := by
    have ha : gramCharges (GramAssembly.key 2869).leftCharge (GramAssembly.key 2869).rightCharge = raw43051 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43051Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43051 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2869).leftCharge (GramAssembly.key 2869).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2869).leftCharge (GramAssembly.key 2869).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2869, Integer.Sparse.eval]
  ring

theorem keyMoment2870 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2870) =
      Integer.Sparse.eval keyMomentRow2870 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2870).leftCharge (GramAssembly.key 2870).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2192) := by
    have ha : gramCharges (GramAssembly.key 2870).leftCharge (GramAssembly.key 2870).rightCharge = raw43052 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43052Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43052 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2870).leftCharge (GramAssembly.key 2870).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4815) := by
    have ha : gramCharges (GramAssembly.key 2870).leftCharge (GramAssembly.key 2870).rightCharge = raw43053 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43053Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43053 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2870).leftCharge (GramAssembly.key 2870).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2870).leftCharge (GramAssembly.key 2870).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2870, Integer.Sparse.eval]
  ring

theorem keyMoment2871 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2871) =
      Integer.Sparse.eval keyMomentRow2871 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2871).leftCharge (GramAssembly.key 2871).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2240) := by
    have ha : gramCharges (GramAssembly.key 2871).leftCharge (GramAssembly.key 2871).rightCharge = raw43054 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43054Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43054 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2871).leftCharge (GramAssembly.key 2871).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4851) := by
    have ha : gramCharges (GramAssembly.key 2871).leftCharge (GramAssembly.key 2871).rightCharge = raw43055 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43055Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43055 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2871).leftCharge (GramAssembly.key 2871).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2871).leftCharge (GramAssembly.key 2871).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2871, Integer.Sparse.eval]
  ring

theorem keyMoment2872 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2872) =
      Integer.Sparse.eval keyMomentRow2872 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2872).leftCharge (GramAssembly.key 2872).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2142) := by
    have ha : gramCharges (GramAssembly.key 2872).leftCharge (GramAssembly.key 2872).rightCharge = raw43056 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43056Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43056 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2872).leftCharge (GramAssembly.key 2872).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4677) := by
    have ha : gramCharges (GramAssembly.key 2872).leftCharge (GramAssembly.key 2872).rightCharge = raw43057 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43057Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43057 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2872).leftCharge (GramAssembly.key 2872).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2872).leftCharge (GramAssembly.key 2872).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2872, Integer.Sparse.eval]
  ring

theorem keyMoment2873 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2873) =
      Integer.Sparse.eval keyMomentRow2873 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2873).leftCharge (GramAssembly.key 2873).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3554) := by
    have ha : gramCharges (GramAssembly.key 2873).leftCharge (GramAssembly.key 2873).rightCharge = raw43058 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43058Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43058 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2873).leftCharge (GramAssembly.key 2873).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4964) := by
    have ha : gramCharges (GramAssembly.key 2873).leftCharge (GramAssembly.key 2873).rightCharge = raw43059 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43059Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43059 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2873).leftCharge (GramAssembly.key 2873).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2873).leftCharge (GramAssembly.key 2873).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2873, Integer.Sparse.eval]
  ring

theorem keyMoment2874 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2874) =
      Integer.Sparse.eval keyMomentRow2874 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2874).leftCharge (GramAssembly.key 2874).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3257) := by
    have ha : gramCharges (GramAssembly.key 2874).leftCharge (GramAssembly.key 2874).rightCharge = raw43060 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43060Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43060 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2874).leftCharge (GramAssembly.key 2874).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4542) := by
    have ha : gramCharges (GramAssembly.key 2874).leftCharge (GramAssembly.key 2874).rightCharge = raw43061 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43061Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43061 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2874).leftCharge (GramAssembly.key 2874).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2874).leftCharge (GramAssembly.key 2874).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2874, Integer.Sparse.eval]
  ring

theorem keyMoment2875 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2875) =
      Integer.Sparse.eval keyMomentRow2875 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2875).leftCharge (GramAssembly.key 2875).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1709) := by
    have ha : gramCharges (GramAssembly.key 2875).leftCharge (GramAssembly.key 2875).rightCharge = raw43062 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43062Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43062 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2875).leftCharge (GramAssembly.key 2875).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4474) := by
    have ha : gramCharges (GramAssembly.key 2875).leftCharge (GramAssembly.key 2875).rightCharge = raw43063 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43063Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43063 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2875).leftCharge (GramAssembly.key 2875).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2875).leftCharge (GramAssembly.key 2875).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2875, Integer.Sparse.eval]
  ring

theorem keyMoment2876 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2876) =
      Integer.Sparse.eval keyMomentRow2876 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2876).leftCharge (GramAssembly.key 2876).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1508) := by
    have ha : gramCharges (GramAssembly.key 2876).leftCharge (GramAssembly.key 2876).rightCharge = raw43064 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43064Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43064 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2876).leftCharge (GramAssembly.key 2876).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4173) := by
    have ha : gramCharges (GramAssembly.key 2876).leftCharge (GramAssembly.key 2876).rightCharge = raw43065 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43065Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43065 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2876).leftCharge (GramAssembly.key 2876).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2876).leftCharge (GramAssembly.key 2876).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2876, Integer.Sparse.eval]
  ring

theorem keyMoment2877 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2877) =
      Integer.Sparse.eval keyMomentRow2877 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2877).leftCharge (GramAssembly.key 2877).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1504) := by
    have ha : gramCharges (GramAssembly.key 2877).leftCharge (GramAssembly.key 2877).rightCharge = raw43066 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43066Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43066 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2877).leftCharge (GramAssembly.key 2877).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4150) := by
    have ha : gramCharges (GramAssembly.key 2877).leftCharge (GramAssembly.key 2877).rightCharge = raw43067 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43067Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43067 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2877).leftCharge (GramAssembly.key 2877).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2877).leftCharge (GramAssembly.key 2877).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2877, Integer.Sparse.eval]
  ring

theorem keyMoment2878 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2878) =
      Integer.Sparse.eval keyMomentRow2878 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2878).leftCharge (GramAssembly.key 2878).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2140) := by
    have ha : gramCharges (GramAssembly.key 2878).leftCharge (GramAssembly.key 2878).rightCharge = raw43068 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43068Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43068 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2878).leftCharge (GramAssembly.key 2878).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4663) := by
    have ha : gramCharges (GramAssembly.key 2878).leftCharge (GramAssembly.key 2878).rightCharge = raw43069 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43069Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43069 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2878).leftCharge (GramAssembly.key 2878).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2878).leftCharge (GramAssembly.key 2878).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2878, Integer.Sparse.eval]
  ring

theorem keyMoment2879 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2879) =
      Integer.Sparse.eval keyMomentRow2879 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2879).leftCharge (GramAssembly.key 2879).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3510) := by
    have ha : gramCharges (GramAssembly.key 2879).leftCharge (GramAssembly.key 2879).rightCharge = raw43070 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43070Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43070 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2879).leftCharge (GramAssembly.key 2879).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4956) := by
    have ha : gramCharges (GramAssembly.key 2879).leftCharge (GramAssembly.key 2879).rightCharge = raw43071 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43071Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43071 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2879).leftCharge (GramAssembly.key 2879).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2879).leftCharge (GramAssembly.key 2879).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2879, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
