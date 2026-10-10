import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical3

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3139 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3139 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3139 node3139Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node174 node174Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw408 singletonSmall3139
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3139) = raw408Labels := by decide +kernel
  rw [hl, canonical408 B hB] at h
  have hc0 : mixedMoment B raw408 (Fin.cases (0 : Fin 1) singletonSmall3139) =
      mixedMoment B node174 node174Labels := by
    have ha : raw408 = raw409 := by apply Matrix.ext; unfold raw408 raw409; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3139 = raw409Labels := by decide +kernel
    rw [ha, hj, canonical409 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3140 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3140 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3140 node3140Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node171 node171Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw410 singletonSmall3140
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3140) = raw410Labels := by decide +kernel
  rw [hl, canonical410 B hB] at h
  have hc0 : mixedMoment B raw410 (Fin.cases (0 : Fin 1) singletonSmall3140) =
      mixedMoment B node171 node171Labels := by
    have ha : raw410 = raw411 := by apply Matrix.ext; unfold raw410 raw411; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3140 = raw411Labels := by decide +kernel
    rw [ha, hj, canonical411 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3141 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3141 node3141Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node182 node182Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw412 singletonSmall3141
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3141) = raw412Labels := by decide +kernel
  rw [hl, canonical412 B hB] at h
  have hc0 : mixedMoment B raw412 (Fin.cases (0 : Fin 1) singletonSmall3141) =
      mixedMoment B node182 node182Labels := by
    have ha : raw412 = raw413 := by apply Matrix.ext; unfold raw412 raw413; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3141 = raw413Labels := by decide +kernel
    rw [ha, hj, canonical413 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3142 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3142 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3142 node3142Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node183 node183Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw414 singletonSmall3142
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3142) = raw414Labels := by decide +kernel
  rw [hl, canonical414 B hB] at h
  have hc0 : mixedMoment B raw414 (Fin.cases (0 : Fin 1) singletonSmall3142) =
      mixedMoment B node183 node183Labels := by
    have ha : raw414 = raw415 := by apply Matrix.ext; unfold raw414 raw415; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3142 = raw415Labels := by decide +kernel
    rw [ha, hj, canonical415 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3143 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3143 node3143Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node173 node173Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw416 singletonSmall3143
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3143) = raw416Labels := by decide +kernel
  rw [hl, canonical416 B hB] at h
  have hc0 : mixedMoment B raw416 (Fin.cases (0 : Fin 1) singletonSmall3143) =
      mixedMoment B node173 node173Labels := by
    have ha : raw416 = raw417 := by apply Matrix.ext; unfold raw416 raw417; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3143 = raw417Labels := by decide +kernel
    rw [ha, hj, canonical417 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3144 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3144 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3144 node3144Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node178 node178Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw418 singletonSmall3144
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3144) = raw418Labels := by decide +kernel
  rw [hl, canonical418 B hB] at h
  have hc0 : mixedMoment B raw418 (Fin.cases (0 : Fin 1) singletonSmall3144) =
      mixedMoment B node178 node178Labels := by
    have ha : raw418 = raw419 := by apply Matrix.ext; unfold raw418 raw419; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3144 = raw419Labels := by decide +kernel
    rw [ha, hj, canonical419 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3145 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3145 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3145 node3145Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node185 node185Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw420 singletonSmall3145
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3145) = raw420Labels := by decide +kernel
  rw [hl, canonical420 B hB] at h
  have hc0 : mixedMoment B raw420 (Fin.cases (0 : Fin 1) singletonSmall3145) =
      mixedMoment B node185 node185Labels := by
    have ha : raw420 = raw421 := by apply Matrix.ext; unfold raw420 raw421; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3145 = raw421Labels := by decide +kernel
    rw [ha, hj, canonical421 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3177 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3177 node3177Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node219 node219Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw422 singletonSmall3177
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3177) = raw422Labels := by decide +kernel
  rw [hl, canonical422 B hB] at h
  have hc0 : mixedMoment B raw422 (Fin.cases (0 : Fin 1) singletonSmall3177) =
      mixedMoment B node219 node219Labels := by
    have ha : raw422 = raw423 := by apply Matrix.ext; unfold raw422 raw423; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3177 = raw423Labels := by decide +kernel
    rw [ha, hj, canonical423 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3178 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3178 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3178 node3178Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node231 node231Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw424 singletonSmall3178
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3178) = raw424Labels := by decide +kernel
  rw [hl, canonical424 B hB] at h
  have hc0 : mixedMoment B raw424 (Fin.cases (0 : Fin 1) singletonSmall3178) =
      mixedMoment B node231 node231Labels := by
    have ha : raw424 = raw425 := by apply Matrix.ext; unfold raw424 raw425; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3178 = raw425Labels := by decide +kernel
    rw [ha, hj, canonical425 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3182 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3182 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3182 node3182Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node243 node243Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw426 singletonSmall3182
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3182) = raw426Labels := by decide +kernel
  rw [hl, canonical426 B hB] at h
  have hc0 : mixedMoment B raw426 (Fin.cases (0 : Fin 1) singletonSmall3182) =
      mixedMoment B node243 node243Labels := by
    have ha : raw426 = raw427 := by apply Matrix.ext; unfold raw426 raw427; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3182 = raw427Labels := by decide +kernel
    rw [ha, hj, canonical427 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3183 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3183 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3183 node3183Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node248 node248Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw428 singletonSmall3183
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3183) = raw428Labels := by decide +kernel
  rw [hl, canonical428 B hB] at h
  have hc0 : mixedMoment B raw428 (Fin.cases (0 : Fin 1) singletonSmall3183) =
      mixedMoment B node248 node248Labels := by
    have ha : raw428 = raw429 := by apply Matrix.ext; unfold raw428 raw429; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3183 = raw429Labels := by decide +kernel
    rw [ha, hj, canonical429 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3184 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3184 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3184 node3184Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node245 node245Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw430 singletonSmall3184
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3184) = raw430Labels := by decide +kernel
  rw [hl, canonical430 B hB] at h
  have hc0 : mixedMoment B raw430 (Fin.cases (0 : Fin 1) singletonSmall3184) =
      mixedMoment B node245 node245Labels := by
    have ha : raw430 = raw431 := by apply Matrix.ext; unfold raw430 raw431; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3184 = raw431Labels := by decide +kernel
    rw [ha, hj, canonical431 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3185 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3185 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3185 node3185Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node244 node244Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw432 singletonSmall3185
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3185) = raw432Labels := by decide +kernel
  rw [hl, canonical432 B hB] at h
  have hc0 : mixedMoment B raw432 (Fin.cases (0 : Fin 1) singletonSmall3185) =
      mixedMoment B node244 node244Labels := by
    have ha : raw432 = raw433 := by apply Matrix.ext; unfold raw432 raw433; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3185 = raw433Labels := by decide +kernel
    rw [ha, hj, canonical433 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3186 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3186 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3186 node3186Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node241 node241Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw434 singletonSmall3186
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3186) = raw434Labels := by decide +kernel
  rw [hl, canonical434 B hB] at h
  have hc0 : mixedMoment B raw434 (Fin.cases (0 : Fin 1) singletonSmall3186) =
      mixedMoment B node241 node241Labels := by
    have ha : raw434 = raw435 := by apply Matrix.ext; unfold raw434 raw435; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3186 = raw435Labels := by decide +kernel
    rw [ha, hj, canonical435 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3187 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3187 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3187 node3187Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node251 node251Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw436 singletonSmall3187
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3187) = raw436Labels := by decide +kernel
  rw [hl, canonical436 B hB] at h
  have hc0 : mixedMoment B raw436 (Fin.cases (0 : Fin 1) singletonSmall3187) =
      mixedMoment B node251 node251Labels := by
    have ha : raw436 = raw437 := by apply Matrix.ext; unfold raw436 raw437; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3187 = raw437Labels := by decide +kernel
    rw [ha, hj, canonical437 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3188 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3188 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3188 node3188Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node252 node252Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw438 singletonSmall3188
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3188) = raw438Labels := by decide +kernel
  rw [hl, canonical438 B hB] at h
  have hc0 : mixedMoment B raw438 (Fin.cases (0 : Fin 1) singletonSmall3188) =
      mixedMoment B node252 node252Labels := by
    have ha : raw438 = raw439 := by apply Matrix.ext; unfold raw438 raw439; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3188 = raw439Labels := by decide +kernel
    rw [ha, hj, canonical439 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3190 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3190 node3190Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node209 node209Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw440 singletonSmall3190
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3190) = raw440Labels := by decide +kernel
  rw [hl, canonical440 B hB] at h
  have hc0 : mixedMoment B raw440 (Fin.cases (0 : Fin 1) singletonSmall3190) =
      mixedMoment B node209 node209Labels := by
    have ha : raw440 = raw441 := by apply Matrix.ext; unfold raw440 raw441; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3190 = raw441Labels := by decide +kernel
    rw [ha, hj, canonical441 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3191 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3191 node3191Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node210 node210Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw442 singletonSmall3191
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3191) = raw442Labels := by decide +kernel
  rw [hl, canonical442 B hB] at h
  have hc0 : mixedMoment B raw442 (Fin.cases (0 : Fin 1) singletonSmall3191) =
      mixedMoment B node210 node210Labels := by
    have ha : raw442 = raw443 := by apply Matrix.ext; unfold raw442 raw443; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3191 = raw443Labels := by decide +kernel
    rw [ha, hj, canonical443 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3192 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3192 node3192Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node205 node205Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw444 singletonSmall3192
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3192) = raw444Labels := by decide +kernel
  rw [hl, canonical444 B hB] at h
  have hc0 : mixedMoment B raw444 (Fin.cases (0 : Fin 1) singletonSmall3192) =
      mixedMoment B node205 node205Labels := by
    have ha : raw444 = raw445 := by apply Matrix.ext; unfold raw444 raw445; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3192 = raw445Labels := by decide +kernel
    rw [ha, hj, canonical445 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
