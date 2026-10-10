import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys88
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical335

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2816 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2816) =
      Integer.Sparse.eval keyMomentRow2816 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2816).leftCharge (GramAssembly.key 2816).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3523) := by
    have ha : gramCharges (GramAssembly.key 2816).leftCharge (GramAssembly.key 2816).rightCharge = raw42944 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42944Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42944 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2816).leftCharge (GramAssembly.key 2816).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5139) := by
    have ha : gramCharges (GramAssembly.key 2816).leftCharge (GramAssembly.key 2816).rightCharge = raw42945 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42945Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42945 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2816).leftCharge (GramAssembly.key 2816).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2816).leftCharge (GramAssembly.key 2816).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2816, Integer.Sparse.eval]; ring

theorem keyMoment2817 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2817) =
      Integer.Sparse.eval keyMomentRow2817 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2817).leftCharge (GramAssembly.key 2817).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3842) := by
    have ha : gramCharges (GramAssembly.key 2817).leftCharge (GramAssembly.key 2817).rightCharge = raw42946 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42946Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42946 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2817).leftCharge (GramAssembly.key 2817).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5419) := by
    have ha : gramCharges (GramAssembly.key 2817).leftCharge (GramAssembly.key 2817).rightCharge = raw42947 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42947Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42947 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2817).leftCharge (GramAssembly.key 2817).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2817).leftCharge (GramAssembly.key 2817).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2817, Integer.Sparse.eval]; ring

theorem keyMoment2818 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2818) =
      Integer.Sparse.eval keyMomentRow2818 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2818).leftCharge (GramAssembly.key 2818).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3542) := by
    have ha : gramCharges (GramAssembly.key 2818).leftCharge (GramAssembly.key 2818).rightCharge = raw42948 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42948Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42948 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2818).leftCharge (GramAssembly.key 2818).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5189) := by
    have ha : gramCharges (GramAssembly.key 2818).leftCharge (GramAssembly.key 2818).rightCharge = raw42949 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42949Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42949 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2818).leftCharge (GramAssembly.key 2818).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2818).leftCharge (GramAssembly.key 2818).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2818, Integer.Sparse.eval]; ring

theorem keyMoment2819 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2819) =
      Integer.Sparse.eval keyMomentRow2819 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2819).leftCharge (GramAssembly.key 2819).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 0) := by
    have ha : gramCharges (GramAssembly.key 2819).leftCharge (GramAssembly.key 2819).rightCharge = raw42950 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42950Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42950 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2819).leftCharge (GramAssembly.key 2819).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4083) := by
    have ha : gramCharges (GramAssembly.key 2819).leftCharge (GramAssembly.key 2819).rightCharge = raw42951 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42951Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42951 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2819).leftCharge (GramAssembly.key 2819).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2819).leftCharge (GramAssembly.key 2819).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2819, Integer.Sparse.eval]; ring

theorem keyMoment2820 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2820) =
      Integer.Sparse.eval keyMomentRow2820 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2820).leftCharge (GramAssembly.key 2820).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3111) := by
    have ha : gramCharges (GramAssembly.key 2820).leftCharge (GramAssembly.key 2820).rightCharge = raw42952 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42952Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42952 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2820).leftCharge (GramAssembly.key 2820).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5273) := by
    have ha : gramCharges (GramAssembly.key 2820).leftCharge (GramAssembly.key 2820).rightCharge = raw42953 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42953Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42953 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2820).leftCharge (GramAssembly.key 2820).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2820).leftCharge (GramAssembly.key 2820).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2820, Integer.Sparse.eval]; ring

theorem keyMoment2821 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2821) =
      Integer.Sparse.eval keyMomentRow2821 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2821).leftCharge (GramAssembly.key 2821).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3) := by
    have ha : gramCharges (GramAssembly.key 2821).leftCharge (GramAssembly.key 2821).rightCharge = raw42954 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42954Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42954 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2821).leftCharge (GramAssembly.key 2821).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4091) := by
    have ha : gramCharges (GramAssembly.key 2821).leftCharge (GramAssembly.key 2821).rightCharge = raw42955 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42955Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42955 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2821).leftCharge (GramAssembly.key 2821).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2821).leftCharge (GramAssembly.key 2821).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2821, Integer.Sparse.eval]; ring

theorem keyMoment2822 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2822) =
      Integer.Sparse.eval keyMomentRow2822 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2822).leftCharge (GramAssembly.key 2822).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4034) := by
    have ha : gramCharges (GramAssembly.key 2822).leftCharge (GramAssembly.key 2822).rightCharge = raw42956 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42956Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42956 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2822).leftCharge (GramAssembly.key 2822).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5427) := by
    have ha : gramCharges (GramAssembly.key 2822).leftCharge (GramAssembly.key 2822).rightCharge = raw42957 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42957Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42957 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2822).leftCharge (GramAssembly.key 2822).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2822).leftCharge (GramAssembly.key 2822).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2822, Integer.Sparse.eval]; ring

theorem keyMoment2823 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2823) =
      Integer.Sparse.eval keyMomentRow2823 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2823).leftCharge (GramAssembly.key 2823).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3855) := by
    have ha : gramCharges (GramAssembly.key 2823).leftCharge (GramAssembly.key 2823).rightCharge = raw42958 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42958Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42958 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2823).leftCharge (GramAssembly.key 2823).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5437) := by
    have ha : gramCharges (GramAssembly.key 2823).leftCharge (GramAssembly.key 2823).rightCharge = raw42959 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42959Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42959 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2823).leftCharge (GramAssembly.key 2823).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2823).leftCharge (GramAssembly.key 2823).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2823, Integer.Sparse.eval]; ring

theorem keyMoment2824 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2824) =
      Integer.Sparse.eval keyMomentRow2824 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2824).leftCharge (GramAssembly.key 2824).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3228) := by
    have ha : gramCharges (GramAssembly.key 2824).leftCharge (GramAssembly.key 2824).rightCharge = raw42960 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42960Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42960 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2824).leftCharge (GramAssembly.key 2824).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4893) := by
    have ha : gramCharges (GramAssembly.key 2824).leftCharge (GramAssembly.key 2824).rightCharge = raw42961 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42961Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42961 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2824).leftCharge (GramAssembly.key 2824).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2824).leftCharge (GramAssembly.key 2824).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2824, Integer.Sparse.eval]; ring

theorem keyMoment2825 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2825) =
      Integer.Sparse.eval keyMomentRow2825 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2825).leftCharge (GramAssembly.key 2825).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3087) := by
    have ha : gramCharges (GramAssembly.key 2825).leftCharge (GramAssembly.key 2825).rightCharge = raw42962 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42962Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42962 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2825).leftCharge (GramAssembly.key 2825).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5257) := by
    have ha : gramCharges (GramAssembly.key 2825).leftCharge (GramAssembly.key 2825).rightCharge = raw42963 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42963Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42963 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2825).leftCharge (GramAssembly.key 2825).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2825).leftCharge (GramAssembly.key 2825).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2825, Integer.Sparse.eval]; ring

theorem keyMoment2826 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2826) =
      Integer.Sparse.eval keyMomentRow2826 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2826).leftCharge (GramAssembly.key 2826).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4038) := by
    have ha : gramCharges (GramAssembly.key 2826).leftCharge (GramAssembly.key 2826).rightCharge = raw42964 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42964Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42964 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2826).leftCharge (GramAssembly.key 2826).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5408) := by
    have ha : gramCharges (GramAssembly.key 2826).leftCharge (GramAssembly.key 2826).rightCharge = raw42965 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42965Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42965 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2826).leftCharge (GramAssembly.key 2826).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2826).leftCharge (GramAssembly.key 2826).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2826, Integer.Sparse.eval]; ring

theorem keyMoment2827 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2827) =
      Integer.Sparse.eval keyMomentRow2827 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2827).leftCharge (GramAssembly.key 2827).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3099) := by
    have ha : gramCharges (GramAssembly.key 2827).leftCharge (GramAssembly.key 2827).rightCharge = raw42966 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42966Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42966 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2827).leftCharge (GramAssembly.key 2827).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5290) := by
    have ha : gramCharges (GramAssembly.key 2827).leftCharge (GramAssembly.key 2827).rightCharge = raw42967 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42967Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42967 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2827).leftCharge (GramAssembly.key 2827).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2827).leftCharge (GramAssembly.key 2827).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2827, Integer.Sparse.eval]; ring

theorem keyMoment2828 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2828) =
      Integer.Sparse.eval keyMomentRow2828 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2828).leftCharge (GramAssembly.key 2828).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4026) := by
    have ha : gramCharges (GramAssembly.key 2828).leftCharge (GramAssembly.key 2828).rightCharge = raw42968 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42968Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42968 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2828).leftCharge (GramAssembly.key 2828).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5431) := by
    have ha : gramCharges (GramAssembly.key 2828).leftCharge (GramAssembly.key 2828).rightCharge = raw42969 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42969Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42969 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2828).leftCharge (GramAssembly.key 2828).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2828).leftCharge (GramAssembly.key 2828).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2828, Integer.Sparse.eval]; ring

theorem keyMoment2829 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2829) =
      Integer.Sparse.eval keyMomentRow2829 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2829).leftCharge (GramAssembly.key 2829).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3539) := by
    have ha : gramCharges (GramAssembly.key 2829).leftCharge (GramAssembly.key 2829).rightCharge = raw42970 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42970Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42970 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2829).leftCharge (GramAssembly.key 2829).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2829).leftCharge (GramAssembly.key 2829).rightCharge = raw42971 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42971Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42971 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2829).leftCharge (GramAssembly.key 2829).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2829).leftCharge (GramAssembly.key 2829).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2829, Integer.Sparse.eval]; ring

theorem keyMoment2830 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2830) =
      Integer.Sparse.eval keyMomentRow2830 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2830).leftCharge (GramAssembly.key 2830).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4026) := by
    have ha : gramCharges (GramAssembly.key 2830).leftCharge (GramAssembly.key 2830).rightCharge = raw42972 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42972Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42972 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2830).leftCharge (GramAssembly.key 2830).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5431) := by
    have ha : gramCharges (GramAssembly.key 2830).leftCharge (GramAssembly.key 2830).rightCharge = raw42973 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42973Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42973 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2830).leftCharge (GramAssembly.key 2830).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2830).leftCharge (GramAssembly.key 2830).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2830, Integer.Sparse.eval]; ring

theorem keyMoment2831 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2831) =
      Integer.Sparse.eval keyMomentRow2831 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2831).leftCharge (GramAssembly.key 2831).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 4028) := by
    have ha : gramCharges (GramAssembly.key 2831).leftCharge (GramAssembly.key 2831).rightCharge = raw42974 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42974Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42974 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2831).leftCharge (GramAssembly.key 2831).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5448) := by
    have ha : gramCharges (GramAssembly.key 2831).leftCharge (GramAssembly.key 2831).rightCharge = raw42975 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42975Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42975 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2831).leftCharge (GramAssembly.key 2831).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2831).leftCharge (GramAssembly.key 2831).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2831, Integer.Sparse.eval]; ring

theorem keyMoment2832 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2832) =
      Integer.Sparse.eval keyMomentRow2832 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2832).leftCharge (GramAssembly.key 2832).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3539) := by
    have ha : gramCharges (GramAssembly.key 2832).leftCharge (GramAssembly.key 2832).rightCharge = raw42976 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42976Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42976 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2832).leftCharge (GramAssembly.key 2832).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2832).leftCharge (GramAssembly.key 2832).rightCharge = raw42977 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42977Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42977 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2832).leftCharge (GramAssembly.key 2832).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2832).leftCharge (GramAssembly.key 2832).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2832, Integer.Sparse.eval]; ring

theorem keyMoment2833 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2833) =
      Integer.Sparse.eval keyMomentRow2833 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2833).leftCharge (GramAssembly.key 2833).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3543) := by
    have ha : gramCharges (GramAssembly.key 2833).leftCharge (GramAssembly.key 2833).rightCharge = raw42978 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42978Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42978 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2833).leftCharge (GramAssembly.key 2833).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5252) := by
    have ha : gramCharges (GramAssembly.key 2833).leftCharge (GramAssembly.key 2833).rightCharge = raw42979 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42979Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42979 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2833).leftCharge (GramAssembly.key 2833).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2833).leftCharge (GramAssembly.key 2833).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2833, Integer.Sparse.eval]; ring

theorem keyMoment2834 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2834) =
      Integer.Sparse.eval keyMomentRow2834 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2834).leftCharge (GramAssembly.key 2834).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3223) := by
    have ha : gramCharges (GramAssembly.key 2834).leftCharge (GramAssembly.key 2834).rightCharge = raw42980 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42980Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42980 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2834).leftCharge (GramAssembly.key 2834).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4889) := by
    have ha : gramCharges (GramAssembly.key 2834).leftCharge (GramAssembly.key 2834).rightCharge = raw42981 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42981Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42981 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2834).leftCharge (GramAssembly.key 2834).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2834).leftCharge (GramAssembly.key 2834).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2834, Integer.Sparse.eval]; ring

theorem keyMoment2835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2835) =
      Integer.Sparse.eval keyMomentRow2835 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2835).leftCharge (GramAssembly.key 2835).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3064) := by
    have ha : gramCharges (GramAssembly.key 2835).leftCharge (GramAssembly.key 2835).rightCharge = raw42982 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42982Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42982 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2835).leftCharge (GramAssembly.key 2835).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2835).leftCharge (GramAssembly.key 2835).rightCharge = raw42983 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42983Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42983 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2835).leftCharge (GramAssembly.key 2835).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2835).leftCharge (GramAssembly.key 2835).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2835, Integer.Sparse.eval]; ring

theorem keyMoment2836 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2836) =
      Integer.Sparse.eval keyMomentRow2836 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2836).leftCharge (GramAssembly.key 2836).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3847) := by
    have ha : gramCharges (GramAssembly.key 2836).leftCharge (GramAssembly.key 2836).rightCharge = raw42984 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42984Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42984 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2836).leftCharge (GramAssembly.key 2836).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5406) := by
    have ha : gramCharges (GramAssembly.key 2836).leftCharge (GramAssembly.key 2836).rightCharge = raw42985 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42985Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42985 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2836).leftCharge (GramAssembly.key 2836).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2836).leftCharge (GramAssembly.key 2836).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2836, Integer.Sparse.eval]; ring

theorem keyMoment2837 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2837) =
      Integer.Sparse.eval keyMomentRow2837 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2837).leftCharge (GramAssembly.key 2837).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3846) := by
    have ha : gramCharges (GramAssembly.key 2837).leftCharge (GramAssembly.key 2837).rightCharge = raw42986 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42986Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42986 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2837).leftCharge (GramAssembly.key 2837).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2837).leftCharge (GramAssembly.key 2837).rightCharge = raw42987 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42987Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42987 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2837).leftCharge (GramAssembly.key 2837).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2837).leftCharge (GramAssembly.key 2837).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2837, Integer.Sparse.eval]; ring

theorem keyMoment2838 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2838) =
      Integer.Sparse.eval keyMomentRow2838 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2838).leftCharge (GramAssembly.key 2838).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2697) := by
    have ha : gramCharges (GramAssembly.key 2838).leftCharge (GramAssembly.key 2838).rightCharge = raw42988 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42988Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42988 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2838).leftCharge (GramAssembly.key 2838).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5243) := by
    have ha : gramCharges (GramAssembly.key 2838).leftCharge (GramAssembly.key 2838).rightCharge = raw42989 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42989Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42989 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2838).leftCharge (GramAssembly.key 2838).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2838).leftCharge (GramAssembly.key 2838).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2838, Integer.Sparse.eval]; ring

theorem keyMoment2839 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2839) =
      Integer.Sparse.eval keyMomentRow2839 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2839).leftCharge (GramAssembly.key 2839).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3226) := by
    have ha : gramCharges (GramAssembly.key 2839).leftCharge (GramAssembly.key 2839).rightCharge = raw42990 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42990Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42990 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2839).leftCharge (GramAssembly.key 2839).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4887) := by
    have ha : gramCharges (GramAssembly.key 2839).leftCharge (GramAssembly.key 2839).rightCharge = raw42991 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42991Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42991 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2839).leftCharge (GramAssembly.key 2839).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2839).leftCharge (GramAssembly.key 2839).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2839, Integer.Sparse.eval]; ring

theorem keyMoment2840 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2840) =
      Integer.Sparse.eval keyMomentRow2840 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2840).leftCharge (GramAssembly.key 2840).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3074) := by
    have ha : gramCharges (GramAssembly.key 2840).leftCharge (GramAssembly.key 2840).rightCharge = raw42992 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42992Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42992 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2840).leftCharge (GramAssembly.key 2840).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5281) := by
    have ha : gramCharges (GramAssembly.key 2840).leftCharge (GramAssembly.key 2840).rightCharge = raw42993 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42993Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42993 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2840).leftCharge (GramAssembly.key 2840).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2840).leftCharge (GramAssembly.key 2840).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2840, Integer.Sparse.eval]; ring

theorem keyMoment2841 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2841) =
      Integer.Sparse.eval keyMomentRow2841 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2841).leftCharge (GramAssembly.key 2841).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3075) := by
    have ha : gramCharges (GramAssembly.key 2841).leftCharge (GramAssembly.key 2841).rightCharge = raw42994 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42994Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42994 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2841).leftCharge (GramAssembly.key 2841).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5270) := by
    have ha : gramCharges (GramAssembly.key 2841).leftCharge (GramAssembly.key 2841).rightCharge = raw42995 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42995Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42995 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2841).leftCharge (GramAssembly.key 2841).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2841).leftCharge (GramAssembly.key 2841).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2841, Integer.Sparse.eval]; ring

theorem keyMoment2842 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2842) =
      Integer.Sparse.eval keyMomentRow2842 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2842).leftCharge (GramAssembly.key 2842).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2702) := by
    have ha : gramCharges (GramAssembly.key 2842).leftCharge (GramAssembly.key 2842).rightCharge = raw42996 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42996Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42996 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2842).leftCharge (GramAssembly.key 2842).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4600) := by
    have ha : gramCharges (GramAssembly.key 2842).leftCharge (GramAssembly.key 2842).rightCharge = raw42997 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42997Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42997 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2842).leftCharge (GramAssembly.key 2842).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2842).leftCharge (GramAssembly.key 2842).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2842, Integer.Sparse.eval]; ring

theorem keyMoment2843 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2843) =
      Integer.Sparse.eval keyMomentRow2843 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2843).leftCharge (GramAssembly.key 2843).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3526) := by
    have ha : gramCharges (GramAssembly.key 2843).leftCharge (GramAssembly.key 2843).rightCharge = raw42998 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42998Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42998 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2843).leftCharge (GramAssembly.key 2843).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2843).leftCharge (GramAssembly.key 2843).rightCharge = raw42999 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42999Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42999 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2843).leftCharge (GramAssembly.key 2843).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2843).leftCharge (GramAssembly.key 2843).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2843, Integer.Sparse.eval]; ring

theorem keyMoment2844 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2844) =
      Integer.Sparse.eval keyMomentRow2844 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2844).leftCharge (GramAssembly.key 2844).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3289) := by
    have ha : gramCharges (GramAssembly.key 2844).leftCharge (GramAssembly.key 2844).rightCharge = raw43000 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43000Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43000 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2844).leftCharge (GramAssembly.key 2844).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4599) := by
    have ha : gramCharges (GramAssembly.key 2844).leftCharge (GramAssembly.key 2844).rightCharge = raw43001 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43001Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43001 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2844).leftCharge (GramAssembly.key 2844).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2844).leftCharge (GramAssembly.key 2844).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2844, Integer.Sparse.eval]; ring

theorem keyMoment2845 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2845) =
      Integer.Sparse.eval keyMomentRow2845 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2845).leftCharge (GramAssembly.key 2845).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3288) := by
    have ha : gramCharges (GramAssembly.key 2845).leftCharge (GramAssembly.key 2845).rightCharge = raw43002 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43002Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43002 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2845).leftCharge (GramAssembly.key 2845).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4589) := by
    have ha : gramCharges (GramAssembly.key 2845).leftCharge (GramAssembly.key 2845).rightCharge = raw43003 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43003Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43003 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2845).leftCharge (GramAssembly.key 2845).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2845).leftCharge (GramAssembly.key 2845).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2845, Integer.Sparse.eval]; ring

theorem keyMoment2846 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2846) =
      Integer.Sparse.eval keyMomentRow2846 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2846).leftCharge (GramAssembly.key 2846).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3839) := by
    have ha : gramCharges (GramAssembly.key 2846).leftCharge (GramAssembly.key 2846).rightCharge = raw43004 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43004Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43004 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2846).leftCharge (GramAssembly.key 2846).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2846).leftCharge (GramAssembly.key 2846).rightCharge = raw43005 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43005Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43005 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2846).leftCharge (GramAssembly.key 2846).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2846).leftCharge (GramAssembly.key 2846).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2846, Integer.Sparse.eval]; ring

theorem keyMoment2847 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2847) =
      Integer.Sparse.eval keyMomentRow2847 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2847).leftCharge (GramAssembly.key 2847).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3848) := by
    have ha : gramCharges (GramAssembly.key 2847).leftCharge (GramAssembly.key 2847).rightCharge = raw43006 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw43006Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43006 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2847).leftCharge (GramAssembly.key 2847).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2847).leftCharge (GramAssembly.key 2847).rightCharge = raw43007 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw43007Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical43007 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2847).leftCharge (GramAssembly.key 2847).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2847).leftCharge (GramAssembly.key 2847).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2847, Integer.Sparse.eval]; ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
