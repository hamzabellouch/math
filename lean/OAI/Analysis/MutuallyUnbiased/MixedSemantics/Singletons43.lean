import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical2

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2753 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2753 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2753 node2753Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node397 node397Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw264 singletonSmall2753
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2753) = raw264Labels := by decide +kernel
  rw [hl, canonical264 B hB] at h
  have hc0 : mixedMoment B raw264 (Fin.cases (0 : Fin 1) singletonSmall2753) =
      mixedMoment B node397 node397Labels := by
    have ha : raw264 = raw265 := by apply Matrix.ext; unfold raw264 raw265; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2753 = raw265Labels := by decide +kernel
    rw [ha, hj, canonical265 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2755 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2755 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2755 node2755Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node262 node262Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw266 singletonSmall2755
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2755) = raw266Labels := by decide +kernel
  rw [hl, canonical266 B hB] at h
  have hc0 : mixedMoment B raw266 (Fin.cases (0 : Fin 1) singletonSmall2755) =
      mixedMoment B node262 node262Labels := by
    have ha : raw266 = raw267 := by apply Matrix.ext; unfold raw266 raw267; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2755 = raw267Labels := by decide +kernel
    rw [ha, hj, canonical267 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2766 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2766 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2766 node2766Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node403 node403Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw268 singletonSmall2766
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2766) = raw268Labels := by decide +kernel
  rw [hl, canonical268 B hB] at h
  have hc0 : mixedMoment B raw268 (Fin.cases (0 : Fin 1) singletonSmall2766) =
      mixedMoment B node403 node403Labels := by
    have ha : raw268 = raw269 := by apply Matrix.ext; unfold raw268 raw269; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2766 = raw269Labels := by decide +kernel
    rw [ha, hj, canonical269 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2767 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2767 node2767Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node404 node404Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw270 singletonSmall2767
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2767) = raw270Labels := by decide +kernel
  rw [hl, canonical270 B hB] at h
  have hc0 : mixedMoment B raw270 (Fin.cases (0 : Fin 1) singletonSmall2767) =
      mixedMoment B node404 node404Labels := by
    have ha : raw270 = raw271 := by apply Matrix.ext; unfold raw270 raw271; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2767 = raw271Labels := by decide +kernel
    rw [ha, hj, canonical271 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2768 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2768 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2768 node2768Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node405 node405Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw272 singletonSmall2768
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2768) = raw272Labels := by decide +kernel
  rw [hl, canonical272 B hB] at h
  have hc0 : mixedMoment B raw272 (Fin.cases (0 : Fin 1) singletonSmall2768) =
      mixedMoment B node405 node405Labels := by
    have ha : raw272 = raw273 := by apply Matrix.ext; unfold raw272 raw273; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2768 = raw273Labels := by decide +kernel
    rw [ha, hj, canonical273 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2770 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2770 node2770Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node407 node407Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw274 singletonSmall2770
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2770) = raw274Labels := by decide +kernel
  rw [hl, canonical274 B hB] at h
  have hc0 : mixedMoment B raw274 (Fin.cases (0 : Fin 1) singletonSmall2770) =
      mixedMoment B node407 node407Labels := by
    have ha : raw274 = raw275 := by apply Matrix.ext; unfold raw274 raw275; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2770 = raw275Labels := by decide +kernel
    rw [ha, hj, canonical275 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2775 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2775 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2775 node2775Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node411 node411Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw276 singletonSmall2775
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2775) = raw276Labels := by decide +kernel
  rw [hl, canonical276 B hB] at h
  have hc0 : mixedMoment B raw276 (Fin.cases (0 : Fin 1) singletonSmall2775) =
      mixedMoment B node411 node411Labels := by
    have ha : raw276 = raw277 := by apply Matrix.ext; unfold raw276 raw277; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2775 = raw277Labels := by decide +kernel
    rw [ha, hj, canonical277 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2776 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2776 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2776 node2776Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node412 node412Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw278 singletonSmall2776
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2776) = raw278Labels := by decide +kernel
  rw [hl, canonical278 B hB] at h
  have hc0 : mixedMoment B raw278 (Fin.cases (0 : Fin 1) singletonSmall2776) =
      mixedMoment B node412 node412Labels := by
    have ha : raw278 = raw279 := by apply Matrix.ext; unfold raw278 raw279; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2776 = raw279Labels := by decide +kernel
    rw [ha, hj, canonical279 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2778 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2778 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2778 node2778Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node270 node270Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw280 singletonSmall2778
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2778) = raw280Labels := by decide +kernel
  rw [hl, canonical280 B hB] at h
  have hc0 : mixedMoment B raw280 (Fin.cases (0 : Fin 1) singletonSmall2778) =
      mixedMoment B node270 node270Labels := by
    have ha : raw280 = raw281 := by apply Matrix.ext; unfold raw280 raw281; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2778 = raw281Labels := by decide +kernel
    rw [ha, hj, canonical281 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2784 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2784 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2784 node2784Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node416 node416Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw282 singletonSmall2784
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2784) = raw282Labels := by decide +kernel
  rw [hl, canonical282 B hB] at h
  have hc0 : mixedMoment B raw282 (Fin.cases (0 : Fin 1) singletonSmall2784) =
      mixedMoment B node416 node416Labels := by
    have ha : raw282 = raw283 := by apply Matrix.ext; unfold raw282 raw283; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2784 = raw283Labels := by decide +kernel
    rw [ha, hj, canonical283 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2788 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2788 node2788Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node420 node420Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw284 singletonSmall2788
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2788) = raw284Labels := by decide +kernel
  rw [hl, canonical284 B hB] at h
  have hc0 : mixedMoment B raw284 (Fin.cases (0 : Fin 1) singletonSmall2788) =
      mixedMoment B node420 node420Labels := by
    have ha : raw284 = raw285 := by apply Matrix.ext; unfold raw284 raw285; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2788 = raw285Labels := by decide +kernel
    rw [ha, hj, canonical285 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
