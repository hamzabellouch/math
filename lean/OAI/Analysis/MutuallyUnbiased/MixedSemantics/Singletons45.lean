import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical2

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2901 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2901 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2901 node2901Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node206 node206Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw294 singletonSmall2901
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2901) = raw294Labels := by decide +kernel
  rw [hl, canonical294 B hB] at h
  have hc0 : mixedMoment B raw294 (Fin.cases (0 : Fin 1) singletonSmall2901) =
      mixedMoment B node206 node206Labels := by
    have ha : raw294 = raw295 := by apply Matrix.ext; unfold raw294 raw295; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2901 = raw295Labels := by decide +kernel
    rw [ha, hj, canonical295 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2903 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2903 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2903 node2903Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node293 node293Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw296 singletonSmall2903
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2903) = raw296Labels := by decide +kernel
  rw [hl, canonical296 B hB] at h
  have hc0 : mixedMoment B raw296 (Fin.cases (0 : Fin 1) singletonSmall2903) =
      mixedMoment B node293 node293Labels := by
    have ha : raw296 = raw297 := by apply Matrix.ext; unfold raw296 raw297; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2903 = raw297Labels := by decide +kernel
    rw [ha, hj, canonical297 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2904 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2904 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2904 node2904Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node175 node175Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw298 singletonSmall2904
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2904) = raw298Labels := by decide +kernel
  rw [hl, canonical298 B hB] at h
  have hc0 : mixedMoment B raw298 (Fin.cases (0 : Fin 1) singletonSmall2904) =
      mixedMoment B node175 node175Labels := by
    have ha : raw298 = raw299 := by apply Matrix.ext; unfold raw298 raw299; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2904 = raw299Labels := by decide +kernel
    rw [ha, hj, canonical299 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2932 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2932 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2932 node2932Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node198 node198Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw300 singletonSmall2932
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2932) = raw300Labels := by decide +kernel
  rw [hl, canonical300 B hB] at h
  have hc0 : mixedMoment B raw300 (Fin.cases (0 : Fin 1) singletonSmall2932) =
      mixedMoment B node198 node198Labels := by
    have ha : raw300 = raw301 := by apply Matrix.ext; unfold raw300 raw301; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2932 = raw301Labels := by decide +kernel
    rw [ha, hj, canonical301 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2936 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2936 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2936 node2936Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node321 node321Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw302 singletonSmall2936
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2936) = raw302Labels := by decide +kernel
  rw [hl, canonical302 B hB] at h
  have hc0 : mixedMoment B raw302 (Fin.cases (0 : Fin 1) singletonSmall2936) =
      mixedMoment B node321 node321Labels := by
    have ha : raw302 = raw303 := by apply Matrix.ext; unfold raw302 raw303; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2936 = raw303Labels := by decide +kernel
    rw [ha, hj, canonical303 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2937 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2937 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2937 node2937Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node320 node320Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw304 singletonSmall2937
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2937) = raw304Labels := by decide +kernel
  rw [hl, canonical304 B hB] at h
  have hc0 : mixedMoment B raw304 (Fin.cases (0 : Fin 1) singletonSmall2937) =
      mixedMoment B node320 node320Labels := by
    have ha : raw304 = raw305 := by apply Matrix.ext; unfold raw304 raw305; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2937 = raw305Labels := by decide +kernel
    rw [ha, hj, canonical305 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2939 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2939 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2939 node2939Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node303 node303Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw306 singletonSmall2939
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2939) = raw306Labels := by decide +kernel
  rw [hl, canonical306 B hB] at h
  have hc0 : mixedMoment B raw306 (Fin.cases (0 : Fin 1) singletonSmall2939) =
      mixedMoment B node303 node303Labels := by
    have ha : raw306 = raw307 := by apply Matrix.ext; unfold raw306 raw307; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2939 = raw307Labels := by decide +kernel
    rw [ha, hj, canonical307 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2941 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2941 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2941 node2941Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node222 node222Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw308 singletonSmall2941
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2941) = raw308Labels := by decide +kernel
  rw [hl, canonical308 B hB] at h
  have hc0 : mixedMoment B raw308 (Fin.cases (0 : Fin 1) singletonSmall2941) =
      mixedMoment B node222 node222Labels := by
    have ha : raw308 = raw309 := by apply Matrix.ext; unfold raw308 raw309; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2941 = raw309Labels := by decide +kernel
    rw [ha, hj, canonical309 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2943 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2943 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2943 node2943Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node325 node325Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw310 singletonSmall2943
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2943) = raw310Labels := by decide +kernel
  rw [hl, canonical310 B hB] at h
  have hc0 : mixedMoment B raw310 (Fin.cases (0 : Fin 1) singletonSmall2943) =
      mixedMoment B node325 node325Labels := by
    have ha : raw310 = raw311 := by apply Matrix.ext; unfold raw310 raw311; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2943 = raw311Labels := by decide +kernel
    rw [ha, hj, canonical311 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
