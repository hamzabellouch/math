import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical3

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3081 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3081 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3081 node3081Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node370 node370Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw358 singletonSmall3081
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3081) = raw358Labels := by decide +kernel
  rw [hl, canonical358 B hB] at h
  have hc0 : mixedMoment B raw358 (Fin.cases (0 : Fin 1) singletonSmall3081) =
      mixedMoment B node370 node370Labels := by
    have ha : raw358 = raw359 := by apply Matrix.ext; unfold raw358 raw359; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3081 = raw359Labels := by decide +kernel
    rw [ha, hj, canonical359 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3082 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3082 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3082 node3082Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node233 node233Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw360 singletonSmall3082
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3082) = raw360Labels := by decide +kernel
  rw [hl, canonical360 B hB] at h
  have hc0 : mixedMoment B raw360 (Fin.cases (0 : Fin 1) singletonSmall3082) =
      mixedMoment B node233 node233Labels := by
    have ha : raw360 = raw361 := by apply Matrix.ext; unfold raw360 raw361; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3082 = raw361Labels := by decide +kernel
    rw [ha, hj, canonical361 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3087 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3087 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3087 node3087Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node376 node376Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw362 singletonSmall3087
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3087) = raw362Labels := by decide +kernel
  rw [hl, canonical362 B hB] at h
  have hc0 : mixedMoment B raw362 (Fin.cases (0 : Fin 1) singletonSmall3087) =
      mixedMoment B node376 node376Labels := by
    have ha : raw362 = raw363 := by apply Matrix.ext; unfold raw362 raw363; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3087 = raw363Labels := by decide +kernel
    rw [ha, hj, canonical363 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3088 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3088 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3088 node3088Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node378 node378Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw364 singletonSmall3088
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3088) = raw364Labels := by decide +kernel
  rw [hl, canonical364 B hB] at h
  have hc0 : mixedMoment B raw364 (Fin.cases (0 : Fin 1) singletonSmall3088) =
      mixedMoment B node378 node378Labels := by
    have ha : raw364 = raw365 := by apply Matrix.ext; unfold raw364 raw365; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3088 = raw365Labels := by decide +kernel
    rw [ha, hj, canonical365 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3089 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3089 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3089 node3089Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node377 node377Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw366 singletonSmall3089
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3089) = raw366Labels := by decide +kernel
  rw [hl, canonical366 B hB] at h
  have hc0 : mixedMoment B raw366 (Fin.cases (0 : Fin 1) singletonSmall3089) =
      mixedMoment B node377 node377Labels := by
    have ha : raw366 = raw367 := by apply Matrix.ext; unfold raw366 raw367; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3089 = raw367Labels := by decide +kernel
    rw [ha, hj, canonical367 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3090 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3090 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3090 node3090Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node379 node379Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw368 singletonSmall3090
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3090) = raw368Labels := by decide +kernel
  rw [hl, canonical368 B hB] at h
  have hc0 : mixedMoment B raw368 (Fin.cases (0 : Fin 1) singletonSmall3090) =
      mixedMoment B node379 node379Labels := by
    have ha : raw368 = raw369 := by apply Matrix.ext; unfold raw368 raw369; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3090 = raw369Labels := by decide +kernel
    rw [ha, hj, canonical369 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3093 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3093 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3093 node3093Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node360 node360Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw370 singletonSmall3093
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3093) = raw370Labels := by decide +kernel
  rw [hl, canonical370 B hB] at h
  have hc0 : mixedMoment B raw370 (Fin.cases (0 : Fin 1) singletonSmall3093) =
      mixedMoment B node360 node360Labels := by
    have ha : raw370 = raw371 := by apply Matrix.ext; unfold raw370 raw371; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3093 = raw371Labels := by decide +kernel
    rw [ha, hj, canonical371 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3094 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3094 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3094 node3094Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node361 node361Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw372 singletonSmall3094
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3094) = raw372Labels := by decide +kernel
  rw [hl, canonical372 B hB] at h
  have hc0 : mixedMoment B raw372 (Fin.cases (0 : Fin 1) singletonSmall3094) =
      mixedMoment B node361 node361Labels := by
    have ha : raw372 = raw373 := by apply Matrix.ext; unfold raw372 raw373; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3094 = raw373Labels := by decide +kernel
    rw [ha, hj, canonical373 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3095 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3095 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3095 node3095Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node237 node237Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw374 singletonSmall3095
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3095) = raw374Labels := by decide +kernel
  rw [hl, canonical374 B hB] at h
  have hc0 : mixedMoment B raw374 (Fin.cases (0 : Fin 1) singletonSmall3095) =
      mixedMoment B node237 node237Labels := by
    have ha : raw374 = raw375 := by apply Matrix.ext; unfold raw374 raw375; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3095 = raw375Labels := by decide +kernel
    rw [ha, hj, canonical375 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3099 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3099 node3099Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node401 node401Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw376 singletonSmall3099
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3099) = raw376Labels := by decide +kernel
  rw [hl, canonical376 B hB] at h
  have hc0 : mixedMoment B raw376 (Fin.cases (0 : Fin 1) singletonSmall3099) =
      mixedMoment B node401 node401Labels := by
    have ha : raw376 = raw377 := by apply Matrix.ext; unfold raw376 raw377; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3099 = raw377Labels := by decide +kernel
    rw [ha, hj, canonical377 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3100 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3100 node3100Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node403 node403Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw378 singletonSmall3100
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3100) = raw378Labels := by decide +kernel
  rw [hl, canonical378 B hB] at h
  have hc0 : mixedMoment B raw378 (Fin.cases (0 : Fin 1) singletonSmall3100) =
      mixedMoment B node403 node403Labels := by
    have ha : raw378 = raw379 := by apply Matrix.ext; unfold raw378 raw379; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3100 = raw379Labels := by decide +kernel
    rw [ha, hj, canonical379 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3101 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3101 node3101Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node405 node405Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw380 singletonSmall3101
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3101) = raw380Labels := by decide +kernel
  rw [hl, canonical380 B hB] at h
  have hc0 : mixedMoment B raw380 (Fin.cases (0 : Fin 1) singletonSmall3101) =
      mixedMoment B node405 node405Labels := by
    have ha : raw380 = raw381 := by apply Matrix.ext; unfold raw380 raw381; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3101 = raw381Labels := by decide +kernel
    rw [ha, hj, canonical381 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3102 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3102 node3102Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node404 node404Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw382 singletonSmall3102
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3102) = raw382Labels := by decide +kernel
  rw [hl, canonical382 B hB] at h
  have hc0 : mixedMoment B raw382 (Fin.cases (0 : Fin 1) singletonSmall3102) =
      mixedMoment B node404 node404Labels := by
    have ha : raw382 = raw383 := by apply Matrix.ext; unfold raw382 raw383; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3102 = raw383Labels := by decide +kernel
    rw [ha, hj, canonical383 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3103 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3103 node3103Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node402 node402Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw384 singletonSmall3103
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3103) = raw384Labels := by decide +kernel
  rw [hl, canonical384 B hB] at h
  have hc0 : mixedMoment B raw384 (Fin.cases (0 : Fin 1) singletonSmall3103) =
      mixedMoment B node402 node402Labels := by
    have ha : raw384 = raw385 := by apply Matrix.ext; unfold raw384 raw385; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3103 = raw385Labels := by decide +kernel
    rw [ha, hj, canonical385 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3105 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3105 node3105Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node371 node371Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw386 singletonSmall3105
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3105) = raw386Labels := by decide +kernel
  rw [hl, canonical386 B hB] at h
  have hc0 : mixedMoment B raw386 (Fin.cases (0 : Fin 1) singletonSmall3105) =
      mixedMoment B node371 node371Labels := by
    have ha : raw386 = raw387 := by apply Matrix.ext; unfold raw386 raw387; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3105 = raw387Labels := by decide +kernel
    rw [ha, hj, canonical387 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3106 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3106 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3106 node3106Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node372 node372Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw388 singletonSmall3106
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3106) = raw388Labels := by decide +kernel
  rw [hl, canonical388 B hB] at h
  have hc0 : mixedMoment B raw388 (Fin.cases (0 : Fin 1) singletonSmall3106) =
      mixedMoment B node372 node372Labels := by
    have ha : raw388 = raw389 := by apply Matrix.ext; unfold raw388 raw389; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3106 = raw389Labels := by decide +kernel
    rw [ha, hj, canonical389 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3109 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3109 node3109Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node387 node387Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw390 singletonSmall3109
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3109) = raw390Labels := by decide +kernel
  rw [hl, canonical390 B hB] at h
  have hc0 : mixedMoment B raw390 (Fin.cases (0 : Fin 1) singletonSmall3109) =
      mixedMoment B node387 node387Labels := by
    have ha : raw390 = raw391 := by apply Matrix.ext; unfold raw390 raw391; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3109 = raw391Labels := by decide +kernel
    rw [ha, hj, canonical391 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3110 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3110 node3110Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node390 node390Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw392 singletonSmall3110
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3110) = raw392Labels := by decide +kernel
  rw [hl, canonical392 B hB] at h
  have hc0 : mixedMoment B raw392 (Fin.cases (0 : Fin 1) singletonSmall3110) =
      mixedMoment B node390 node390Labels := by
    have ha : raw392 = raw393 := by apply Matrix.ext; unfold raw392 raw393; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3110 = raw393Labels := by decide +kernel
    rw [ha, hj, canonical393 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3113 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3113 node3113Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node388 node388Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw394 singletonSmall3113
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3113) = raw394Labels := by decide +kernel
  rw [hl, canonical394 B hB] at h
  have hc0 : mixedMoment B raw394 (Fin.cases (0 : Fin 1) singletonSmall3113) =
      mixedMoment B node388 node388Labels := by
    have ha : raw394 = raw395 := by apply Matrix.ext; unfold raw394 raw395; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3113 = raw395Labels := by decide +kernel
    rw [ha, hj, canonical395 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3116 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3116 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3116 node3116Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node368 node368Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw396 singletonSmall3116
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3116) = raw396Labels := by decide +kernel
  rw [hl, canonical396 B hB] at h
  have hc0 : mixedMoment B raw396 (Fin.cases (0 : Fin 1) singletonSmall3116) =
      mixedMoment B node368 node368Labels := by
    have ha : raw396 = raw397 := by apply Matrix.ext; unfold raw396 raw397; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3116 = raw397Labels := by decide +kernel
    rw [ha, hj, canonical397 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3117 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3117 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3117 node3117Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node369 node369Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw398 singletonSmall3117
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3117) = raw398Labels := by decide +kernel
  rw [hl, canonical398 B hB] at h
  have hc0 : mixedMoment B raw398 (Fin.cases (0 : Fin 1) singletonSmall3117) =
      mixedMoment B node369 node369Labels := by
    have ha : raw398 = raw399 := by apply Matrix.ext; unfold raw398 raw399; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3117 = raw399Labels := by decide +kernel
    rw [ha, hj, canonical399 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3119 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3119 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3119 node3119Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node414 node414Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw400 singletonSmall3119
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3119) = raw400Labels := by decide +kernel
  rw [hl, canonical400 B hB] at h
  have hc0 : mixedMoment B raw400 (Fin.cases (0 : Fin 1) singletonSmall3119) =
      mixedMoment B node414 node414Labels := by
    have ha : raw400 = raw401 := by apply Matrix.ext; unfold raw400 raw401; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3119 = raw401Labels := by decide +kernel
    rw [ha, hj, canonical401 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3120 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3120 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3120 node3120Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node416 node416Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw402 singletonSmall3120
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3120) = raw402Labels := by decide +kernel
  rw [hl, canonical402 B hB] at h
  have hc0 : mixedMoment B raw402 (Fin.cases (0 : Fin 1) singletonSmall3120) =
      mixedMoment B node416 node416Labels := by
    have ha : raw402 = raw403 := by apply Matrix.ext; unfold raw402 raw403; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3120 = raw403Labels := by decide +kernel
    rw [ha, hj, canonical403 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3121 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3121 node3121Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node420 node420Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw404 singletonSmall3121
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3121) = raw404Labels := by decide +kernel
  rw [hl, canonical404 B hB] at h
  have hc0 : mixedMoment B raw404 (Fin.cases (0 : Fin 1) singletonSmall3121) =
      mixedMoment B node420 node420Labels := by
    have ha : raw404 = raw405 := by apply Matrix.ext; unfold raw404 raw405; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3121 = raw405Labels := by decide +kernel
    rw [ha, hj, canonical405 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3125 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3125 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3125 node3125Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node415 node415Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw406 singletonSmall3125
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3125) = raw406Labels := by decide +kernel
  rw [hl, canonical406 B hB] at h
  have hc0 : mixedMoment B raw406 (Fin.cases (0 : Fin 1) singletonSmall3125) =
      mixedMoment B node415 node415Labels := by
    have ha : raw406 = raw407 := by apply Matrix.ext; unfold raw406 raw407; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3125 = raw407Labels := by decide +kernel
    rw [ha, hj, canonical407 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
