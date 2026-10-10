import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical8

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4224 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4224 node4224Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node725 node725Labels + mixedMoment B node771 node771Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw912 singletonSmall4224
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4224) = raw912Labels := by decide +kernel
  rw [hl, canonical912 B hB] at h
  have hc0 : mixedMoment B raw912 (Fin.cases (0 : Fin 2) singletonSmall4224) =
      mixedMoment B node725 node725Labels := by
    have ha : raw912 = raw913 := by apply Matrix.ext; unfold raw912 raw913; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4224 = raw913Labels := by decide +kernel
    rw [ha, hj, canonical913 B hB]
  have hc1 : mixedMoment B raw912 (Fin.cases (1 : Fin 2) singletonSmall4224) =
      mixedMoment B node771 node771Labels := by
    have ha : raw912 = raw914 := by apply Matrix.ext; unfold raw912 raw914; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4224 = raw914Labels := by decide +kernel
    rw [ha, hj, canonical914 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4225 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4225 node4225Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node726 node726Labels + mixedMoment B node774 node774Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw915 singletonSmall4225
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4225) = raw915Labels := by decide +kernel
  rw [hl, canonical915 B hB] at h
  have hc0 : mixedMoment B raw915 (Fin.cases (0 : Fin 2) singletonSmall4225) =
      mixedMoment B node726 node726Labels := by
    have ha : raw915 = raw916 := by apply Matrix.ext; unfold raw915 raw916; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4225 = raw916Labels := by decide +kernel
    rw [ha, hj, canonical916 B hB]
  have hc1 : mixedMoment B raw915 (Fin.cases (1 : Fin 2) singletonSmall4225) =
      mixedMoment B node774 node774Labels := by
    have ha : raw915 = raw917 := by apply Matrix.ext; unfold raw915 raw917; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4225 = raw917Labels := by decide +kernel
    rw [ha, hj, canonical917 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4226 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4226 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4226 node4226Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node727 node727Labels + mixedMoment B node759 node759Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw918 singletonSmall4226
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4226) = raw918Labels := by decide +kernel
  rw [hl, canonical918 B hB] at h
  have hc0 : mixedMoment B raw918 (Fin.cases (0 : Fin 2) singletonSmall4226) =
      mixedMoment B node727 node727Labels := by
    have ha : raw918 = raw919 := by apply Matrix.ext; unfold raw918 raw919; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4226 = raw919Labels := by decide +kernel
    rw [ha, hj, canonical919 B hB]
  have hc1 : mixedMoment B raw918 (Fin.cases (1 : Fin 2) singletonSmall4226) =
      mixedMoment B node759 node759Labels := by
    have ha : raw918 = raw920 := by apply Matrix.ext; unfold raw918 raw920; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4226 = raw920Labels := by decide +kernel
    rw [ha, hj, canonical920 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4229 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4229 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4229 node4229Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node729 node729Labels + mixedMoment B node773 node773Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw921 singletonSmall4229
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4229) = raw921Labels := by decide +kernel
  rw [hl, canonical921 B hB] at h
  have hc0 : mixedMoment B raw921 (Fin.cases (0 : Fin 2) singletonSmall4229) =
      mixedMoment B node729 node729Labels := by
    have ha : raw921 = raw922 := by apply Matrix.ext; unfold raw921 raw922; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4229 = raw922Labels := by decide +kernel
    rw [ha, hj, canonical922 B hB]
  have hc1 : mixedMoment B raw921 (Fin.cases (1 : Fin 2) singletonSmall4229) =
      mixedMoment B node773 node773Labels := by
    have ha : raw921 = raw923 := by apply Matrix.ext; unfold raw921 raw923; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4229 = raw923Labels := by decide +kernel
    rw [ha, hj, canonical923 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4230 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4230 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4230 node4230Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node730 node730Labels + mixedMoment B node780 node780Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw924 singletonSmall4230
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4230) = raw924Labels := by decide +kernel
  rw [hl, canonical924 B hB] at h
  have hc0 : mixedMoment B raw924 (Fin.cases (0 : Fin 2) singletonSmall4230) =
      mixedMoment B node730 node730Labels := by
    have ha : raw924 = raw925 := by apply Matrix.ext; unfold raw924 raw925; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4230 = raw925Labels := by decide +kernel
    rw [ha, hj, canonical925 B hB]
  have hc1 : mixedMoment B raw924 (Fin.cases (1 : Fin 2) singletonSmall4230) =
      mixedMoment B node780 node780Labels := by
    have ha : raw924 = raw926 := by apply Matrix.ext; unfold raw924 raw926; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4230 = raw926Labels := by decide +kernel
    rw [ha, hj, canonical926 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4231 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4231 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4231 node4231Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node731 node731Labels + mixedMoment B node781 node781Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw927 singletonSmall4231
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4231) = raw927Labels := by decide +kernel
  rw [hl, canonical927 B hB] at h
  have hc0 : mixedMoment B raw927 (Fin.cases (0 : Fin 2) singletonSmall4231) =
      mixedMoment B node731 node731Labels := by
    have ha : raw927 = raw928 := by apply Matrix.ext; unfold raw927 raw928; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4231 = raw928Labels := by decide +kernel
    rw [ha, hj, canonical928 B hB]
  have hc1 : mixedMoment B raw927 (Fin.cases (1 : Fin 2) singletonSmall4231) =
      mixedMoment B node781 node781Labels := by
    have ha : raw927 = raw929 := by apply Matrix.ext; unfold raw927 raw929; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4231 = raw929Labels := by decide +kernel
    rw [ha, hj, canonical929 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4232 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4232 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4232 node4232Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node732 node732Labels + mixedMoment B node798 node798Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw930 singletonSmall4232
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4232) = raw930Labels := by decide +kernel
  rw [hl, canonical930 B hB] at h
  have hc0 : mixedMoment B raw930 (Fin.cases (0 : Fin 2) singletonSmall4232) =
      mixedMoment B node732 node732Labels := by
    have ha : raw930 = raw931 := by apply Matrix.ext; unfold raw930 raw931; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4232 = raw931Labels := by decide +kernel
    rw [ha, hj, canonical931 B hB]
  have hc1 : mixedMoment B raw930 (Fin.cases (1 : Fin 2) singletonSmall4232) =
      mixedMoment B node798 node798Labels := by
    have ha : raw930 = raw932 := by apply Matrix.ext; unfold raw930 raw932; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4232 = raw932Labels := by decide +kernel
    rw [ha, hj, canonical932 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4233 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4233 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4233 node4233Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node733 node733Labels + mixedMoment B node799 node799Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw933 singletonSmall4233
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4233) = raw933Labels := by decide +kernel
  rw [hl, canonical933 B hB] at h
  have hc0 : mixedMoment B raw933 (Fin.cases (0 : Fin 2) singletonSmall4233) =
      mixedMoment B node733 node733Labels := by
    have ha : raw933 = raw934 := by apply Matrix.ext; unfold raw933 raw934; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4233 = raw934Labels := by decide +kernel
    rw [ha, hj, canonical934 B hB]
  have hc1 : mixedMoment B raw933 (Fin.cases (1 : Fin 2) singletonSmall4233) =
      mixedMoment B node799 node799Labels := by
    have ha : raw933 = raw935 := by apply Matrix.ext; unfold raw933 raw935; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4233 = raw935Labels := by decide +kernel
    rw [ha, hj, canonical935 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4234 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4234 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4234 node4234Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node734 node734Labels + mixedMoment B node800 node800Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw936 singletonSmall4234
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4234) = raw936Labels := by decide +kernel
  rw [hl, canonical936 B hB] at h
  have hc0 : mixedMoment B raw936 (Fin.cases (0 : Fin 2) singletonSmall4234) =
      mixedMoment B node734 node734Labels := by
    have ha : raw936 = raw937 := by apply Matrix.ext; unfold raw936 raw937; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4234 = raw937Labels := by decide +kernel
    rw [ha, hj, canonical937 B hB]
  have hc1 : mixedMoment B raw936 (Fin.cases (1 : Fin 2) singletonSmall4234) =
      mixedMoment B node800 node800Labels := by
    have ha : raw936 = raw938 := by apply Matrix.ext; unfold raw936 raw938; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4234 = raw938Labels := by decide +kernel
    rw [ha, hj, canonical938 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4235 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4235 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4235 node4235Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node735 node735Labels + mixedMoment B node801 node801Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw939 singletonSmall4235
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4235) = raw939Labels := by decide +kernel
  rw [hl, canonical939 B hB] at h
  have hc0 : mixedMoment B raw939 (Fin.cases (0 : Fin 2) singletonSmall4235) =
      mixedMoment B node735 node735Labels := by
    have ha : raw939 = raw940 := by apply Matrix.ext; unfold raw939 raw940; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4235 = raw940Labels := by decide +kernel
    rw [ha, hj, canonical940 B hB]
  have hc1 : mixedMoment B raw939 (Fin.cases (1 : Fin 2) singletonSmall4235) =
      mixedMoment B node801 node801Labels := by
    have ha : raw939 = raw941 := by apply Matrix.ext; unfold raw939 raw941; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4235 = raw941Labels := by decide +kernel
    rw [ha, hj, canonical941 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4236 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4236 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4236 node4236Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node736 node736Labels + mixedMoment B node818 node818Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw942 singletonSmall4236
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4236) = raw942Labels := by decide +kernel
  rw [hl, canonical942 B hB] at h
  have hc0 : mixedMoment B raw942 (Fin.cases (0 : Fin 2) singletonSmall4236) =
      mixedMoment B node736 node736Labels := by
    have ha : raw942 = raw943 := by apply Matrix.ext; unfold raw942 raw943; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4236 = raw943Labels := by decide +kernel
    rw [ha, hj, canonical943 B hB]
  have hc1 : mixedMoment B raw942 (Fin.cases (1 : Fin 2) singletonSmall4236) =
      mixedMoment B node818 node818Labels := by
    have ha : raw942 = raw944 := by apply Matrix.ext; unfold raw942 raw944; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4236 = raw944Labels := by decide +kernel
    rw [ha, hj, canonical944 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4237 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4237 node4237Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node737 node737Labels + mixedMoment B node840 node840Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw945 singletonSmall4237
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4237) = raw945Labels := by decide +kernel
  rw [hl, canonical945 B hB] at h
  have hc0 : mixedMoment B raw945 (Fin.cases (0 : Fin 2) singletonSmall4237) =
      mixedMoment B node737 node737Labels := by
    have ha : raw945 = raw946 := by apply Matrix.ext; unfold raw945 raw946; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4237 = raw946Labels := by decide +kernel
    rw [ha, hj, canonical946 B hB]
  have hc1 : mixedMoment B raw945 (Fin.cases (1 : Fin 2) singletonSmall4237) =
      mixedMoment B node840 node840Labels := by
    have ha : raw945 = raw947 := by apply Matrix.ext; unfold raw945 raw947; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4237 = raw947Labels := by decide +kernel
    rw [ha, hj, canonical947 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4238 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4238 node4238Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node738 node738Labels + mixedMoment B node819 node819Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw948 singletonSmall4238
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4238) = raw948Labels := by decide +kernel
  rw [hl, canonical948 B hB] at h
  have hc0 : mixedMoment B raw948 (Fin.cases (0 : Fin 2) singletonSmall4238) =
      mixedMoment B node738 node738Labels := by
    have ha : raw948 = raw949 := by apply Matrix.ext; unfold raw948 raw949; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4238 = raw949Labels := by decide +kernel
    rw [ha, hj, canonical949 B hB]
  have hc1 : mixedMoment B raw948 (Fin.cases (1 : Fin 2) singletonSmall4238) =
      mixedMoment B node819 node819Labels := by
    have ha : raw948 = raw950 := by apply Matrix.ext; unfold raw948 raw950; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4238 = raw950Labels := by decide +kernel
    rw [ha, hj, canonical950 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4239 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4239 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4239 node4239Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node739 node739Labels + mixedMoment B node841 node841Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw951 singletonSmall4239
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4239) = raw951Labels := by decide +kernel
  rw [hl, canonical951 B hB] at h
  have hc0 : mixedMoment B raw951 (Fin.cases (0 : Fin 2) singletonSmall4239) =
      mixedMoment B node739 node739Labels := by
    have ha : raw951 = raw952 := by apply Matrix.ext; unfold raw951 raw952; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4239 = raw952Labels := by decide +kernel
    rw [ha, hj, canonical952 B hB]
  have hc1 : mixedMoment B raw951 (Fin.cases (1 : Fin 2) singletonSmall4239) =
      mixedMoment B node841 node841Labels := by
    have ha : raw951 = raw953 := by apply Matrix.ext; unfold raw951 raw953; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4239 = raw953Labels := by decide +kernel
    rw [ha, hj, canonical953 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4240 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4240 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4240 node4240Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node740 node740Labels + mixedMoment B node842 node842Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw954 singletonSmall4240
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4240) = raw954Labels := by decide +kernel
  rw [hl, canonical954 B hB] at h
  have hc0 : mixedMoment B raw954 (Fin.cases (0 : Fin 2) singletonSmall4240) =
      mixedMoment B node740 node740Labels := by
    have ha : raw954 = raw955 := by apply Matrix.ext; unfold raw954 raw955; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4240 = raw955Labels := by decide +kernel
    rw [ha, hj, canonical955 B hB]
  have hc1 : mixedMoment B raw954 (Fin.cases (1 : Fin 2) singletonSmall4240) =
      mixedMoment B node842 node842Labels := by
    have ha : raw954 = raw956 := by apply Matrix.ext; unfold raw954 raw956; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4240 = raw956Labels := by decide +kernel
    rw [ha, hj, canonical956 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4241 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4241 node4241Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node741 node741Labels + mixedMoment B node820 node820Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw957 singletonSmall4241
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4241) = raw957Labels := by decide +kernel
  rw [hl, canonical957 B hB] at h
  have hc0 : mixedMoment B raw957 (Fin.cases (0 : Fin 2) singletonSmall4241) =
      mixedMoment B node741 node741Labels := by
    have ha : raw957 = raw958 := by apply Matrix.ext; unfold raw957 raw958; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4241 = raw958Labels := by decide +kernel
    rw [ha, hj, canonical958 B hB]
  have hc1 : mixedMoment B raw957 (Fin.cases (1 : Fin 2) singletonSmall4241) =
      mixedMoment B node820 node820Labels := by
    have ha : raw957 = raw959 := by apply Matrix.ext; unfold raw957 raw959; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4241 = raw959Labels := by decide +kernel
    rw [ha, hj, canonical959 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4242 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4242 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4242 node4242Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node742 node742Labels + mixedMoment B node843 node843Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw960 singletonSmall4242
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4242) = raw960Labels := by decide +kernel
  rw [hl, canonical960 B hB] at h
  have hc0 : mixedMoment B raw960 (Fin.cases (0 : Fin 2) singletonSmall4242) =
      mixedMoment B node742 node742Labels := by
    have ha : raw960 = raw961 := by apply Matrix.ext; unfold raw960 raw961; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4242 = raw961Labels := by decide +kernel
    rw [ha, hj, canonical961 B hB]
  have hc1 : mixedMoment B raw960 (Fin.cases (1 : Fin 2) singletonSmall4242) =
      mixedMoment B node843 node843Labels := by
    have ha : raw960 = raw962 := by apply Matrix.ext; unfold raw960 raw962; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4242 = raw962Labels := by decide +kernel
    rw [ha, hj, canonical962 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4243 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4243 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4243 node4243Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node743 node743Labels + mixedMoment B node844 node844Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw963 singletonSmall4243
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4243) = raw963Labels := by decide +kernel
  rw [hl, canonical963 B hB] at h
  have hc0 : mixedMoment B raw963 (Fin.cases (0 : Fin 2) singletonSmall4243) =
      mixedMoment B node743 node743Labels := by
    have ha : raw963 = raw964 := by apply Matrix.ext; unfold raw963 raw964; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4243 = raw964Labels := by decide +kernel
    rw [ha, hj, canonical964 B hB]
  have hc1 : mixedMoment B raw963 (Fin.cases (1 : Fin 2) singletonSmall4243) =
      mixedMoment B node844 node844Labels := by
    have ha : raw963 = raw965 := by apply Matrix.ext; unfold raw963 raw965; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4243 = raw965Labels := by decide +kernel
    rw [ha, hj, canonical965 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4248 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4248 node4248Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node782 node782Labels + mixedMoment B node782 node782Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw966 singletonSmall4248
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4248) = raw966Labels := by decide +kernel
  rw [hl, canonical966 B hB] at h
  have hc0 : mixedMoment B raw966 (Fin.cases (0 : Fin 2) singletonSmall4248) =
      mixedMoment B node782 node782Labels := by
    have ha : raw966 = raw967 := by apply Matrix.ext; unfold raw966 raw967; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4248 = raw967Labels := by decide +kernel
    rw [ha, hj, canonical967 B hB]
  have hc1 : mixedMoment B raw966 (Fin.cases (1 : Fin 2) singletonSmall4248) =
      mixedMoment B node782 node782Labels := by
    have ha : raw966 = raw968 := by apply Matrix.ext; unfold raw966 raw968; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4248 = raw968Labels := by decide +kernel
    rw [ha, hj, canonical968 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4249 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4249 node4249Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node783 node783Labels + mixedMoment B node803 node803Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw969 singletonSmall4249
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4249) = raw969Labels := by decide +kernel
  rw [hl, canonical969 B hB] at h
  have hc0 : mixedMoment B raw969 (Fin.cases (0 : Fin 2) singletonSmall4249) =
      mixedMoment B node783 node783Labels := by
    have ha : raw969 = raw970 := by apply Matrix.ext; unfold raw969 raw970; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4249 = raw970Labels := by decide +kernel
    rw [ha, hj, canonical970 B hB]
  have hc1 : mixedMoment B raw969 (Fin.cases (1 : Fin 2) singletonSmall4249) =
      mixedMoment B node803 node803Labels := by
    have ha : raw969 = raw971 := by apply Matrix.ext; unfold raw969 raw971; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4249 = raw971Labels := by decide +kernel
    rw [ha, hj, canonical971 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4251 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4251 node4251Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node785 node785Labels + mixedMoment B node804 node804Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw972 singletonSmall4251
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4251) = raw972Labels := by decide +kernel
  rw [hl, canonical972 B hB] at h
  have hc0 : mixedMoment B raw972 (Fin.cases (0 : Fin 2) singletonSmall4251) =
      mixedMoment B node785 node785Labels := by
    have ha : raw972 = raw973 := by apply Matrix.ext; unfold raw972 raw973; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4251 = raw973Labels := by decide +kernel
    rw [ha, hj, canonical973 B hB]
  have hc1 : mixedMoment B raw972 (Fin.cases (1 : Fin 2) singletonSmall4251) =
      mixedMoment B node804 node804Labels := by
    have ha : raw972 = raw974 := by apply Matrix.ext; unfold raw972 raw974; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4251 = raw974Labels := by decide +kernel
    rw [ha, hj, canonical974 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4252 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4252 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4252 node4252Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node786 node786Labels + mixedMoment B node822 node822Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw975 singletonSmall4252
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4252) = raw975Labels := by decide +kernel
  rw [hl, canonical975 B hB] at h
  have hc0 : mixedMoment B raw975 (Fin.cases (0 : Fin 2) singletonSmall4252) =
      mixedMoment B node786 node786Labels := by
    have ha : raw975 = raw976 := by apply Matrix.ext; unfold raw975 raw976; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4252 = raw976Labels := by decide +kernel
    rw [ha, hj, canonical976 B hB]
  have hc1 : mixedMoment B raw975 (Fin.cases (1 : Fin 2) singletonSmall4252) =
      mixedMoment B node822 node822Labels := by
    have ha : raw975 = raw977 := by apply Matrix.ext; unfold raw975 raw977; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4252 = raw977Labels := by decide +kernel
    rw [ha, hj, canonical977 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4253 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4253 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4253 node4253Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node787 node787Labels + mixedMoment B node847 node847Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw978 singletonSmall4253
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4253) = raw978Labels := by decide +kernel
  rw [hl, canonical978 B hB] at h
  have hc0 : mixedMoment B raw978 (Fin.cases (0 : Fin 2) singletonSmall4253) =
      mixedMoment B node787 node787Labels := by
    have ha : raw978 = raw979 := by apply Matrix.ext; unfold raw978 raw979; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4253 = raw979Labels := by decide +kernel
    rw [ha, hj, canonical979 B hB]
  have hc1 : mixedMoment B raw978 (Fin.cases (1 : Fin 2) singletonSmall4253) =
      mixedMoment B node847 node847Labels := by
    have ha : raw978 = raw980 := by apply Matrix.ext; unfold raw978 raw980; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4253 = raw980Labels := by decide +kernel
    rw [ha, hj, canonical980 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4255 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4255 node4255Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node789 node789Labels + mixedMoment B node823 node823Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw981 singletonSmall4255
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4255) = raw981Labels := by decide +kernel
  rw [hl, canonical981 B hB] at h
  have hc0 : mixedMoment B raw981 (Fin.cases (0 : Fin 2) singletonSmall4255) =
      mixedMoment B node789 node789Labels := by
    have ha : raw981 = raw982 := by apply Matrix.ext; unfold raw981 raw982; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4255 = raw982Labels := by decide +kernel
    rw [ha, hj, canonical982 B hB]
  have hc1 : mixedMoment B raw981 (Fin.cases (1 : Fin 2) singletonSmall4255) =
      mixedMoment B node823 node823Labels := by
    have ha : raw981 = raw983 := by apply Matrix.ext; unfold raw981 raw983; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4255 = raw983Labels := by decide +kernel
    rw [ha, hj, canonical983 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4256 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4256 node4256Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node790 node790Labels + mixedMoment B node848 node848Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw984 singletonSmall4256
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4256) = raw984Labels := by decide +kernel
  rw [hl, canonical984 B hB] at h
  have hc0 : mixedMoment B raw984 (Fin.cases (0 : Fin 2) singletonSmall4256) =
      mixedMoment B node790 node790Labels := by
    have ha : raw984 = raw985 := by apply Matrix.ext; unfold raw984 raw985; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4256 = raw985Labels := by decide +kernel
    rw [ha, hj, canonical985 B hB]
  have hc1 : mixedMoment B raw984 (Fin.cases (1 : Fin 2) singletonSmall4256) =
      mixedMoment B node848 node848Labels := by
    have ha : raw984 = raw986 := by apply Matrix.ext; unfold raw984 raw986; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4256 = raw986Labels := by decide +kernel
    rw [ha, hj, canonical986 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4257 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4257 node4257Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node791 node791Labels + mixedMoment B node849 node849Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw987 singletonSmall4257
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4257) = raw987Labels := by decide +kernel
  rw [hl, canonical987 B hB] at h
  have hc0 : mixedMoment B raw987 (Fin.cases (0 : Fin 2) singletonSmall4257) =
      mixedMoment B node791 node791Labels := by
    have ha : raw987 = raw988 := by apply Matrix.ext; unfold raw987 raw988; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4257 = raw988Labels := by decide +kernel
    rw [ha, hj, canonical988 B hB]
  have hc1 : mixedMoment B raw987 (Fin.cases (1 : Fin 2) singletonSmall4257) =
      mixedMoment B node849 node849Labels := by
    have ha : raw987 = raw989 := by apply Matrix.ext; unfold raw987 raw989; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4257 = raw989Labels := by decide +kernel
    rw [ha, hj, canonical989 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4265 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4265 node4265Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node807 node807Labels + mixedMoment B node807 node807Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw990 singletonSmall4265
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4265) = raw990Labels := by decide +kernel
  rw [hl, canonical990 B hB] at h
  have hc0 : mixedMoment B raw990 (Fin.cases (0 : Fin 2) singletonSmall4265) =
      mixedMoment B node807 node807Labels := by
    have ha : raw990 = raw991 := by apply Matrix.ext; unfold raw990 raw991; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4265 = raw991Labels := by decide +kernel
    rw [ha, hj, canonical991 B hB]
  have hc1 : mixedMoment B raw990 (Fin.cases (1 : Fin 2) singletonSmall4265) =
      mixedMoment B node807 node807Labels := by
    have ha : raw990 = raw992 := by apply Matrix.ext; unfold raw990 raw992; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4265 = raw992Labels := by decide +kernel
    rw [ha, hj, canonical992 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4268 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4268 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4268 node4268Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node811 node811Labels + mixedMoment B node824 node824Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw993 singletonSmall4268
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4268) = raw993Labels := by decide +kernel
  rw [hl, canonical993 B hB] at h
  have hc0 : mixedMoment B raw993 (Fin.cases (0 : Fin 2) singletonSmall4268) =
      mixedMoment B node811 node811Labels := by
    have ha : raw993 = raw994 := by apply Matrix.ext; unfold raw993 raw994; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4268 = raw994Labels := by decide +kernel
    rw [ha, hj, canonical994 B hB]
  have hc1 : mixedMoment B raw993 (Fin.cases (1 : Fin 2) singletonSmall4268) =
      mixedMoment B node824 node824Labels := by
    have ha : raw993 = raw995 := by apply Matrix.ext; unfold raw993 raw995; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4268 = raw995Labels := by decide +kernel
    rw [ha, hj, canonical995 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4270 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4270 node4270Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node813 node813Labels + mixedMoment B node853 node853Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw996 singletonSmall4270
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4270) = raw996Labels := by decide +kernel
  rw [hl, canonical996 B hB] at h
  have hc0 : mixedMoment B raw996 (Fin.cases (0 : Fin 2) singletonSmall4270) =
      mixedMoment B node813 node813Labels := by
    have ha : raw996 = raw997 := by apply Matrix.ext; unfold raw996 raw997; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4270 = raw997Labels := by decide +kernel
    rw [ha, hj, canonical997 B hB]
  have hc1 : mixedMoment B raw996 (Fin.cases (1 : Fin 2) singletonSmall4270) =
      mixedMoment B node853 node853Labels := by
    have ha : raw996 = raw998 := by apply Matrix.ext; unfold raw996 raw998; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4270 = raw998Labels := by decide +kernel
    rw [ha, hj, canonical998 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4272 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4272 node4272Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node815 node815Labels + mixedMoment B node826 node826Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw999 singletonSmall4272
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4272) = raw999Labels := by decide +kernel
  rw [hl, canonical999 B hB] at h
  have hc0 : mixedMoment B raw999 (Fin.cases (0 : Fin 2) singletonSmall4272) =
      mixedMoment B node815 node815Labels := by
    have ha : raw999 = raw1000 := by apply Matrix.ext; unfold raw999 raw1000; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4272 = raw1000Labels := by decide +kernel
    rw [ha, hj, canonical1000 B hB]
  have hc1 : mixedMoment B raw999 (Fin.cases (1 : Fin 2) singletonSmall4272) =
      mixedMoment B node826 node826Labels := by
    have ha : raw999 = raw1001 := by apply Matrix.ext; unfold raw999 raw1001; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4272 = raw1001Labels := by decide +kernel
    rw [ha, hj, canonical1001 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4275 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4275 node4275Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node827 node827Labels + mixedMoment B node827 node827Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1002 singletonSmall4275
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4275) = raw1002Labels := by decide +kernel
  rw [hl, canonical1002 B hB] at h
  have hc0 : mixedMoment B raw1002 (Fin.cases (0 : Fin 2) singletonSmall4275) =
      mixedMoment B node827 node827Labels := by
    have ha : raw1002 = raw1003 := by apply Matrix.ext; unfold raw1002 raw1003; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4275 = raw1003Labels := by decide +kernel
    rw [ha, hj, canonical1003 B hB]
  have hc1 : mixedMoment B raw1002 (Fin.cases (1 : Fin 2) singletonSmall4275) =
      mixedMoment B node827 node827Labels := by
    have ha : raw1002 = raw1004 := by apply Matrix.ext; unfold raw1002 raw1004; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4275 = raw1004Labels := by decide +kernel
    rw [ha, hj, canonical1004 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4276 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4276 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4276 node4276Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node828 node828Labels + mixedMoment B node857 node857Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1005 singletonSmall4276
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4276) = raw1005Labels := by decide +kernel
  rw [hl, canonical1005 B hB] at h
  have hc0 : mixedMoment B raw1005 (Fin.cases (0 : Fin 2) singletonSmall4276) =
      mixedMoment B node828 node828Labels := by
    have ha : raw1005 = raw1006 := by apply Matrix.ext; unfold raw1005 raw1006; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4276 = raw1006Labels := by decide +kernel
    rw [ha, hj, canonical1006 B hB]
  have hc1 : mixedMoment B raw1005 (Fin.cases (1 : Fin 2) singletonSmall4276) =
      mixedMoment B node857 node857Labels := by
    have ha : raw1005 = raw1007 := by apply Matrix.ext; unfold raw1005 raw1007; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4276 = raw1007Labels := by decide +kernel
    rw [ha, hj, canonical1007 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4278 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4278 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4278 node4278Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node830 node830Labels + mixedMoment B node830 node830Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1008 singletonSmall4278
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4278) = raw1008Labels := by decide +kernel
  rw [hl, canonical1008 B hB] at h
  have hc0 : mixedMoment B raw1008 (Fin.cases (0 : Fin 2) singletonSmall4278) =
      mixedMoment B node830 node830Labels := by
    have ha : raw1008 = raw1009 := by apply Matrix.ext; unfold raw1008 raw1009; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4278 = raw1009Labels := by decide +kernel
    rw [ha, hj, canonical1009 B hB]
  have hc1 : mixedMoment B raw1008 (Fin.cases (1 : Fin 2) singletonSmall4278) =
      mixedMoment B node830 node830Labels := by
    have ha : raw1008 = raw1010 := by apply Matrix.ext; unfold raw1008 raw1010; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4278 = raw1010Labels := by decide +kernel
    rw [ha, hj, canonical1010 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4279 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4279 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4279 node4279Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node831 node831Labels + mixedMoment B node858 node858Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1011 singletonSmall4279
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4279) = raw1011Labels := by decide +kernel
  rw [hl, canonical1011 B hB] at h
  have hc0 : mixedMoment B raw1011 (Fin.cases (0 : Fin 2) singletonSmall4279) =
      mixedMoment B node831 node831Labels := by
    have ha : raw1011 = raw1012 := by apply Matrix.ext; unfold raw1011 raw1012; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4279 = raw1012Labels := by decide +kernel
    rw [ha, hj, canonical1012 B hB]
  have hc1 : mixedMoment B raw1011 (Fin.cases (1 : Fin 2) singletonSmall4279) =
      mixedMoment B node858 node858Labels := by
    have ha : raw1011 = raw1013 := by apply Matrix.ext; unfold raw1011 raw1013; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4279 = raw1013Labels := by decide +kernel
    rw [ha, hj, canonical1013 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4280 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4280 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4280 node4280Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node832 node832Labels + mixedMoment B node862 node862Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1014 singletonSmall4280
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4280) = raw1014Labels := by decide +kernel
  rw [hl, canonical1014 B hB] at h
  have hc0 : mixedMoment B raw1014 (Fin.cases (0 : Fin 2) singletonSmall4280) =
      mixedMoment B node832 node832Labels := by
    have ha : raw1014 = raw1015 := by apply Matrix.ext; unfold raw1014 raw1015; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4280 = raw1015Labels := by decide +kernel
    rw [ha, hj, canonical1015 B hB]
  have hc1 : mixedMoment B raw1014 (Fin.cases (1 : Fin 2) singletonSmall4280) =
      mixedMoment B node862 node862Labels := by
    have ha : raw1014 = raw1016 := by apply Matrix.ext; unfold raw1014 raw1016; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4280 = raw1016Labels := by decide +kernel
    rw [ha, hj, canonical1016 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4285 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4285 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4285 node4285Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node860 node860Labels + mixedMoment B node860 node860Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1017 singletonSmall4285
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4285) = raw1017Labels := by decide +kernel
  rw [hl, canonical1017 B hB] at h
  have hc0 : mixedMoment B raw1017 (Fin.cases (0 : Fin 2) singletonSmall4285) =
      mixedMoment B node860 node860Labels := by
    have ha : raw1017 = raw1018 := by apply Matrix.ext; unfold raw1017 raw1018; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4285 = raw1018Labels := by decide +kernel
    rw [ha, hj, canonical1018 B hB]
  have hc1 : mixedMoment B raw1017 (Fin.cases (1 : Fin 2) singletonSmall4285) =
      mixedMoment B node860 node860Labels := by
    have ha : raw1017 = raw1019 := by apply Matrix.ext; unfold raw1017 raw1019; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4285 = raw1019Labels := by decide +kernel
    rw [ha, hj, canonical1019 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4286 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4286 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4286 node4286Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node864 node864Labels + mixedMoment B node1550 node1550Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1020 singletonSmall4286
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4286) = raw1020Labels := by decide +kernel
  rw [hl, canonical1020 B hB] at h
  have hc0 : mixedMoment B raw1020 (Fin.cases (0 : Fin 2) singletonSmall4286) =
      mixedMoment B node864 node864Labels := by
    have ha : raw1020 = raw1021 := by apply Matrix.ext; unfold raw1020 raw1021; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4286 = raw1021Labels := by decide +kernel
    rw [ha, hj, canonical1021 B hB]
  have hc1 : mixedMoment B raw1020 (Fin.cases (1 : Fin 2) singletonSmall4286) =
      mixedMoment B node1550 node1550Labels := by
    have ha : raw1020 = raw1022 := by apply Matrix.ext; unfold raw1020 raw1022; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4286 = raw1022Labels := by decide +kernel
    rw [ha, hj, canonical1022 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4287 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4287 node4287Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node865 node865Labels + mixedMoment B node1553 node1553Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1023 singletonSmall4287
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4287) = raw1023Labels := by decide +kernel
  rw [hl, canonical1023 B hB] at h
  have hc0 : mixedMoment B raw1023 (Fin.cases (0 : Fin 2) singletonSmall4287) =
      mixedMoment B node865 node865Labels := by
    have ha : raw1023 = raw1024 := by apply Matrix.ext; unfold raw1023 raw1024; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4287 = raw1024Labels := by decide +kernel
    rw [ha, hj, canonical1024 B hB]
  have hc1 : mixedMoment B raw1023 (Fin.cases (1 : Fin 2) singletonSmall4287) =
      mixedMoment B node1553 node1553Labels := by
    have ha : raw1023 = raw1025 := by apply Matrix.ext; unfold raw1023 raw1025; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4287 = raw1025Labels := by decide +kernel
    rw [ha, hj, canonical1025 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
