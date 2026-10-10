import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical311

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 416) =
      Integer.Sparse.eval keyMomentRow416 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 416).leftCharge (GramAssembly.key 416).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 130) := by
    have ha : gramCharges (GramAssembly.key 416).leftCharge (GramAssembly.key 416).rightCharge = raw39864 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39864Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39864 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 416).leftCharge (GramAssembly.key 416).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow416, Integer.Sparse.eval]

theorem keyMoment417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 417) =
      Integer.Sparse.eval keyMomentRow417 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 417).leftCharge (GramAssembly.key 417).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 296) := by
    have ha : gramCharges (GramAssembly.key 417).leftCharge (GramAssembly.key 417).rightCharge = raw39865 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39865Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39865 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 417).leftCharge (GramAssembly.key 417).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow417, Integer.Sparse.eval]

theorem keyMoment418 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 418) =
      Integer.Sparse.eval keyMomentRow418 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 418).leftCharge (GramAssembly.key 418).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 300) := by
    have ha : gramCharges (GramAssembly.key 418).leftCharge (GramAssembly.key 418).rightCharge = raw39866 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39866Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39866 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 418).leftCharge (GramAssembly.key 418).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow418, Integer.Sparse.eval]

theorem keyMoment419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 419) =
      Integer.Sparse.eval keyMomentRow419 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 419).leftCharge (GramAssembly.key 419).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 103) := by
    have ha : gramCharges (GramAssembly.key 419).leftCharge (GramAssembly.key 419).rightCharge = raw39867 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39867Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39867 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 419).leftCharge (GramAssembly.key 419).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow419, Integer.Sparse.eval]

theorem keyMoment420 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 420) =
      Integer.Sparse.eval keyMomentRow420 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 420).leftCharge (GramAssembly.key 420).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 149) := by
    have ha : gramCharges (GramAssembly.key 420).leftCharge (GramAssembly.key 420).rightCharge = raw39868 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39868Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39868 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 420).leftCharge (GramAssembly.key 420).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow420, Integer.Sparse.eval]

theorem keyMoment421 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 421) =
      Integer.Sparse.eval keyMomentRow421 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 421).leftCharge (GramAssembly.key 421).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 36) := by
    have ha : gramCharges (GramAssembly.key 421).leftCharge (GramAssembly.key 421).rightCharge = raw39869 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39869Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39869 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 421).leftCharge (GramAssembly.key 421).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow421, Integer.Sparse.eval]

theorem keyMoment422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 422) =
      Integer.Sparse.eval keyMomentRow422 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 422).leftCharge (GramAssembly.key 422).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 15) := by
    have ha : gramCharges (GramAssembly.key 422).leftCharge (GramAssembly.key 422).rightCharge = raw39870 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39870Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39870 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 422).leftCharge (GramAssembly.key 422).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow422, Integer.Sparse.eval]

theorem keyMoment423 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 423) =
      Integer.Sparse.eval keyMomentRow423 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 423).leftCharge (GramAssembly.key 423).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 168) := by
    have ha : gramCharges (GramAssembly.key 423).leftCharge (GramAssembly.key 423).rightCharge = raw39871 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39871Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39871 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 423).leftCharge (GramAssembly.key 423).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow423, Integer.Sparse.eval]

theorem keyMoment424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 424) =
      Integer.Sparse.eval keyMomentRow424 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 424).leftCharge (GramAssembly.key 424).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 278) := by
    have ha : gramCharges (GramAssembly.key 424).leftCharge (GramAssembly.key 424).rightCharge = raw39872 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39872Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39872 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 424).leftCharge (GramAssembly.key 424).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow424, Integer.Sparse.eval]

theorem keyMoment425 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 425) =
      Integer.Sparse.eval keyMomentRow425 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 425).leftCharge (GramAssembly.key 425).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 279) := by
    have ha : gramCharges (GramAssembly.key 425).leftCharge (GramAssembly.key 425).rightCharge = raw39873 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39873Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39873 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 425).leftCharge (GramAssembly.key 425).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow425, Integer.Sparse.eval]

theorem keyMoment426 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 426) =
      Integer.Sparse.eval keyMomentRow426 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 426).leftCharge (GramAssembly.key 426).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 116) := by
    have ha : gramCharges (GramAssembly.key 426).leftCharge (GramAssembly.key 426).rightCharge = raw39874 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39874Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39874 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 426).leftCharge (GramAssembly.key 426).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow426, Integer.Sparse.eval]

theorem keyMoment427 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 427) =
      Integer.Sparse.eval keyMomentRow427 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 427).leftCharge (GramAssembly.key 427).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 17) := by
    have ha : gramCharges (GramAssembly.key 427).leftCharge (GramAssembly.key 427).rightCharge = raw39875 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39875Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39875 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 427).leftCharge (GramAssembly.key 427).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow427, Integer.Sparse.eval]

theorem keyMoment428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 428) =
      Integer.Sparse.eval keyMomentRow428 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 428).leftCharge (GramAssembly.key 428).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 270) := by
    have ha : gramCharges (GramAssembly.key 428).leftCharge (GramAssembly.key 428).rightCharge = raw39876 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39876Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39876 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 428).leftCharge (GramAssembly.key 428).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow428, Integer.Sparse.eval]

theorem keyMoment429 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 429) =
      Integer.Sparse.eval keyMomentRow429 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 429).leftCharge (GramAssembly.key 429).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 269) := by
    have ha : gramCharges (GramAssembly.key 429).leftCharge (GramAssembly.key 429).rightCharge = raw39877 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39877Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39877 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 429).leftCharge (GramAssembly.key 429).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow429, Integer.Sparse.eval]

theorem keyMoment430 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 430) =
      Integer.Sparse.eval keyMomentRow430 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 430).leftCharge (GramAssembly.key 430).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 251) := by
    have ha : gramCharges (GramAssembly.key 430).leftCharge (GramAssembly.key 430).rightCharge = raw39878 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39878Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39878 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 430).leftCharge (GramAssembly.key 430).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow430, Integer.Sparse.eval]

theorem keyMoment431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 431) =
      Integer.Sparse.eval keyMomentRow431 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 431).leftCharge (GramAssembly.key 431).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 185) := by
    have ha : gramCharges (GramAssembly.key 431).leftCharge (GramAssembly.key 431).rightCharge = raw39879 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39879Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39879 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 431).leftCharge (GramAssembly.key 431).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow431, Integer.Sparse.eval]

theorem keyMoment432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 432) =
      Integer.Sparse.eval keyMomentRow432 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 432).leftCharge (GramAssembly.key 432).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 268) := by
    have ha : gramCharges (GramAssembly.key 432).leftCharge (GramAssembly.key 432).rightCharge = raw39880 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39880Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39880 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 432).leftCharge (GramAssembly.key 432).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow432, Integer.Sparse.eval]

theorem keyMoment433 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 433) =
      Integer.Sparse.eval keyMomentRow433 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 433).leftCharge (GramAssembly.key 433).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 248) := by
    have ha : gramCharges (GramAssembly.key 433).leftCharge (GramAssembly.key 433).rightCharge = raw39881 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39881Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39881 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 433).leftCharge (GramAssembly.key 433).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow433, Integer.Sparse.eval]

theorem keyMoment434 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 434) =
      Integer.Sparse.eval keyMomentRow434 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 434).leftCharge (GramAssembly.key 434).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 182) := by
    have ha : gramCharges (GramAssembly.key 434).leftCharge (GramAssembly.key 434).rightCharge = raw39882 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39882Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39882 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 434).leftCharge (GramAssembly.key 434).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow434, Integer.Sparse.eval]

theorem keyMoment435 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 435) =
      Integer.Sparse.eval keyMomentRow435 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 435).leftCharge (GramAssembly.key 435).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 235) := by
    have ha : gramCharges (GramAssembly.key 435).leftCharge (GramAssembly.key 435).rightCharge = raw39883 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39883Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39883 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 435).leftCharge (GramAssembly.key 435).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow435, Integer.Sparse.eval]

theorem keyMoment436 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 436) =
      Integer.Sparse.eval keyMomentRow436 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 436).leftCharge (GramAssembly.key 436).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 261) := by
    have ha : gramCharges (GramAssembly.key 436).leftCharge (GramAssembly.key 436).rightCharge = raw39884 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39884Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39884 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 436).leftCharge (GramAssembly.key 436).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow436, Integer.Sparse.eval]

theorem keyMoment437 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 437) =
      Integer.Sparse.eval keyMomentRow437 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 437).leftCharge (GramAssembly.key 437).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 173) := by
    have ha : gramCharges (GramAssembly.key 437).leftCharge (GramAssembly.key 437).rightCharge = raw39885 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39885Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39885 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 437).leftCharge (GramAssembly.key 437).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow437, Integer.Sparse.eval]

theorem keyMoment438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 438) =
      Integer.Sparse.eval keyMomentRow438 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 438).leftCharge (GramAssembly.key 438).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 179) := by
    have ha : gramCharges (GramAssembly.key 438).leftCharge (GramAssembly.key 438).rightCharge = raw39886 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39886Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39886 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 438).leftCharge (GramAssembly.key 438).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow438, Integer.Sparse.eval]

theorem keyMoment439 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 439) =
      Integer.Sparse.eval keyMomentRow439 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 439).leftCharge (GramAssembly.key 439).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 223) := by
    have ha : gramCharges (GramAssembly.key 439).leftCharge (GramAssembly.key 439).rightCharge = raw39887 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39887Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39887 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 439).leftCharge (GramAssembly.key 439).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow439, Integer.Sparse.eval]

theorem keyMoment440 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 440) =
      Integer.Sparse.eval keyMomentRow440 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 440).leftCharge (GramAssembly.key 440).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 209) := by
    have ha : gramCharges (GramAssembly.key 440).leftCharge (GramAssembly.key 440).rightCharge = raw39888 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39888Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39888 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 440).leftCharge (GramAssembly.key 440).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow440, Integer.Sparse.eval]

theorem keyMoment441 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 441) =
      Integer.Sparse.eval keyMomentRow441 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 441).leftCharge (GramAssembly.key 441).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 412) := by
    have ha : gramCharges (GramAssembly.key 441).leftCharge (GramAssembly.key 441).rightCharge = raw39889 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39889Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39889 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 441).leftCharge (GramAssembly.key 441).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow441, Integer.Sparse.eval]

theorem keyMoment442 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 442) =
      Integer.Sparse.eval keyMomentRow442 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 442).leftCharge (GramAssembly.key 442).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 468) := by
    have ha : gramCharges (GramAssembly.key 442).leftCharge (GramAssembly.key 442).rightCharge = raw39890 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39890Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39890 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 442).leftCharge (GramAssembly.key 442).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow442, Integer.Sparse.eval]

theorem keyMoment443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 443) =
      Integer.Sparse.eval keyMomentRow443 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 443).leftCharge (GramAssembly.key 443).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 467) := by
    have ha : gramCharges (GramAssembly.key 443).leftCharge (GramAssembly.key 443).rightCharge = raw39891 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39891Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39891 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 443).leftCharge (GramAssembly.key 443).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow443, Integer.Sparse.eval]

theorem keyMoment444 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 444) =
      Integer.Sparse.eval keyMomentRow444 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 444).leftCharge (GramAssembly.key 444).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 439) := by
    have ha : gramCharges (GramAssembly.key 444).leftCharge (GramAssembly.key 444).rightCharge = raw39892 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39892Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39892 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 444).leftCharge (GramAssembly.key 444).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow444, Integer.Sparse.eval]

theorem keyMoment445 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 445) =
      Integer.Sparse.eval keyMomentRow445 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 445).leftCharge (GramAssembly.key 445).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 455) := by
    have ha : gramCharges (GramAssembly.key 445).leftCharge (GramAssembly.key 445).rightCharge = raw39893 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39893Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39893 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 445).leftCharge (GramAssembly.key 445).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow445, Integer.Sparse.eval]

theorem keyMoment446 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 446) =
      Integer.Sparse.eval keyMomentRow446 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 446).leftCharge (GramAssembly.key 446).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 171) := by
    have ha : gramCharges (GramAssembly.key 446).leftCharge (GramAssembly.key 446).rightCharge = raw39894 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39894Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39894 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 446).leftCharge (GramAssembly.key 446).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow446, Integer.Sparse.eval]

theorem keyMoment447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 447) =
      Integer.Sparse.eval keyMomentRow447 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 447).leftCharge (GramAssembly.key 447).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 507) := by
    have ha : gramCharges (GramAssembly.key 447).leftCharge (GramAssembly.key 447).rightCharge = raw39895 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39895Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39895 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 447).leftCharge (GramAssembly.key 447).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow447, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
