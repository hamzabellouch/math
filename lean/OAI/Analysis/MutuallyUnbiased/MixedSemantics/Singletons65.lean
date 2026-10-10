import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical7

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4164 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4164 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4164 node4164Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node592 node592Labels + mixedMoment B node1497 node1497Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw786 singletonSmall4164
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4164) = raw786Labels := by decide +kernel
  rw [hl, canonical786 B hB] at h
  have hc0 : mixedMoment B raw786 (Fin.cases (0 : Fin 2) singletonSmall4164) =
      mixedMoment B node592 node592Labels := by
    have ha : raw786 = raw787 := by apply Matrix.ext; unfold raw786 raw787; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4164 = raw787Labels := by decide +kernel
    rw [ha, hj, canonical787 B hB]
  have hc1 : mixedMoment B raw786 (Fin.cases (1 : Fin 2) singletonSmall4164) =
      mixedMoment B node1497 node1497Labels := by
    have ha : raw786 = raw788 := by apply Matrix.ext; unfold raw786 raw788; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4164 = raw788Labels := by decide +kernel
    rw [ha, hj, canonical788 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4165 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4165 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4165 node4165Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node593 node593Labels + mixedMoment B node1498 node1498Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw789 singletonSmall4165
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4165) = raw789Labels := by decide +kernel
  rw [hl, canonical789 B hB] at h
  have hc0 : mixedMoment B raw789 (Fin.cases (0 : Fin 2) singletonSmall4165) =
      mixedMoment B node593 node593Labels := by
    have ha : raw789 = raw790 := by apply Matrix.ext; unfold raw789 raw790; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4165 = raw790Labels := by decide +kernel
    rw [ha, hj, canonical790 B hB]
  have hc1 : mixedMoment B raw789 (Fin.cases (1 : Fin 2) singletonSmall4165) =
      mixedMoment B node1498 node1498Labels := by
    have ha : raw789 = raw791 := by apply Matrix.ext; unfold raw789 raw791; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4165 = raw791Labels := by decide +kernel
    rw [ha, hj, canonical791 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4166 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4166 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4166 node4166Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node594 node594Labels + mixedMoment B node1499 node1499Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw792 singletonSmall4166
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4166) = raw792Labels := by decide +kernel
  rw [hl, canonical792 B hB] at h
  have hc0 : mixedMoment B raw792 (Fin.cases (0 : Fin 2) singletonSmall4166) =
      mixedMoment B node594 node594Labels := by
    have ha : raw792 = raw793 := by apply Matrix.ext; unfold raw792 raw793; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4166 = raw793Labels := by decide +kernel
    rw [ha, hj, canonical793 B hB]
  have hc1 : mixedMoment B raw792 (Fin.cases (1 : Fin 2) singletonSmall4166) =
      mixedMoment B node1499 node1499Labels := by
    have ha : raw792 = raw794 := by apply Matrix.ext; unfold raw792 raw794; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4166 = raw794Labels := by decide +kernel
    rw [ha, hj, canonical794 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4167 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4167 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4167 node4167Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node595 node595Labels + mixedMoment B node1500 node1500Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw795 singletonSmall4167
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4167) = raw795Labels := by decide +kernel
  rw [hl, canonical795 B hB] at h
  have hc0 : mixedMoment B raw795 (Fin.cases (0 : Fin 2) singletonSmall4167) =
      mixedMoment B node595 node595Labels := by
    have ha : raw795 = raw796 := by apply Matrix.ext; unfold raw795 raw796; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4167 = raw796Labels := by decide +kernel
    rw [ha, hj, canonical796 B hB]
  have hc1 : mixedMoment B raw795 (Fin.cases (1 : Fin 2) singletonSmall4167) =
      mixedMoment B node1500 node1500Labels := by
    have ha : raw795 = raw797 := by apply Matrix.ext; unfold raw795 raw797; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4167 = raw797Labels := by decide +kernel
    rw [ha, hj, canonical797 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4168 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4168 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4168 node4168Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node596 node596Labels + mixedMoment B node845 node845Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw798 singletonSmall4168
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4168) = raw798Labels := by decide +kernel
  rw [hl, canonical798 B hB] at h
  have hc0 : mixedMoment B raw798 (Fin.cases (0 : Fin 2) singletonSmall4168) =
      mixedMoment B node596 node596Labels := by
    have ha : raw798 = raw799 := by apply Matrix.ext; unfold raw798 raw799; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4168 = raw799Labels := by decide +kernel
    rw [ha, hj, canonical799 B hB]
  have hc1 : mixedMoment B raw798 (Fin.cases (1 : Fin 2) singletonSmall4168) =
      mixedMoment B node845 node845Labels := by
    have ha : raw798 = raw800 := by apply Matrix.ext; unfold raw798 raw800; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4168 = raw800Labels := by decide +kernel
    rw [ha, hj, canonical800 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4171 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4171 node4171Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node599 node599Labels + mixedMoment B node1506 node1506Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw801 singletonSmall4171
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4171) = raw801Labels := by decide +kernel
  rw [hl, canonical801 B hB] at h
  have hc0 : mixedMoment B raw801 (Fin.cases (0 : Fin 2) singletonSmall4171) =
      mixedMoment B node599 node599Labels := by
    have ha : raw801 = raw802 := by apply Matrix.ext; unfold raw801 raw802; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4171 = raw802Labels := by decide +kernel
    rw [ha, hj, canonical802 B hB]
  have hc1 : mixedMoment B raw801 (Fin.cases (1 : Fin 2) singletonSmall4171) =
      mixedMoment B node1506 node1506Labels := by
    have ha : raw801 = raw803 := by apply Matrix.ext; unfold raw801 raw803; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4171 = raw803Labels := by decide +kernel
    rw [ha, hj, canonical803 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4172 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4172 node4172Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node600 node600Labels + mixedMoment B node1507 node1507Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw804 singletonSmall4172
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4172) = raw804Labels := by decide +kernel
  rw [hl, canonical804 B hB] at h
  have hc0 : mixedMoment B raw804 (Fin.cases (0 : Fin 2) singletonSmall4172) =
      mixedMoment B node600 node600Labels := by
    have ha : raw804 = raw805 := by apply Matrix.ext; unfold raw804 raw805; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4172 = raw805Labels := by decide +kernel
    rw [ha, hj, canonical805 B hB]
  have hc1 : mixedMoment B raw804 (Fin.cases (1 : Fin 2) singletonSmall4172) =
      mixedMoment B node1507 node1507Labels := by
    have ha : raw804 = raw806 := by apply Matrix.ext; unfold raw804 raw806; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4172 = raw806Labels := by decide +kernel
    rw [ha, hj, canonical806 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4174 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4174 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4174 node4174Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node602 node602Labels + mixedMoment B node1509 node1509Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw807 singletonSmall4174
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4174) = raw807Labels := by decide +kernel
  rw [hl, canonical807 B hB] at h
  have hc0 : mixedMoment B raw807 (Fin.cases (0 : Fin 2) singletonSmall4174) =
      mixedMoment B node602 node602Labels := by
    have ha : raw807 = raw808 := by apply Matrix.ext; unfold raw807 raw808; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4174 = raw808Labels := by decide +kernel
    rw [ha, hj, canonical808 B hB]
  have hc1 : mixedMoment B raw807 (Fin.cases (1 : Fin 2) singletonSmall4174) =
      mixedMoment B node1509 node1509Labels := by
    have ha : raw807 = raw809 := by apply Matrix.ext; unfold raw807 raw809; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4174 = raw809Labels := by decide +kernel
    rw [ha, hj, canonical809 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4175 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4175 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4175 node4175Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node603 node603Labels + mixedMoment B node1517 node1517Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw810 singletonSmall4175
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4175) = raw810Labels := by decide +kernel
  rw [hl, canonical810 B hB] at h
  have hc0 : mixedMoment B raw810 (Fin.cases (0 : Fin 2) singletonSmall4175) =
      mixedMoment B node603 node603Labels := by
    have ha : raw810 = raw811 := by apply Matrix.ext; unfold raw810 raw811; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4175 = raw811Labels := by decide +kernel
    rw [ha, hj, canonical811 B hB]
  have hc1 : mixedMoment B raw810 (Fin.cases (1 : Fin 2) singletonSmall4175) =
      mixedMoment B node1517 node1517Labels := by
    have ha : raw810 = raw812 := by apply Matrix.ext; unfold raw810 raw812; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4175 = raw812Labels := by decide +kernel
    rw [ha, hj, canonical812 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4177 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4177 node4177Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node605 node605Labels + mixedMoment B node1518 node1518Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw813 singletonSmall4177
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4177) = raw813Labels := by decide +kernel
  rw [hl, canonical813 B hB] at h
  have hc0 : mixedMoment B raw813 (Fin.cases (0 : Fin 2) singletonSmall4177) =
      mixedMoment B node605 node605Labels := by
    have ha : raw813 = raw814 := by apply Matrix.ext; unfold raw813 raw814; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4177 = raw814Labels := by decide +kernel
    rw [ha, hj, canonical814 B hB]
  have hc1 : mixedMoment B raw813 (Fin.cases (1 : Fin 2) singletonSmall4177) =
      mixedMoment B node1518 node1518Labels := by
    have ha : raw813 = raw815 := by apply Matrix.ext; unfold raw813 raw815; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4177 = raw815Labels := by decide +kernel
    rw [ha, hj, canonical815 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4180 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4180 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4180 node4180Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node608 node608Labels + mixedMoment B node1519 node1519Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw816 singletonSmall4180
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4180) = raw816Labels := by decide +kernel
  rw [hl, canonical816 B hB] at h
  have hc0 : mixedMoment B raw816 (Fin.cases (0 : Fin 2) singletonSmall4180) =
      mixedMoment B node608 node608Labels := by
    have ha : raw816 = raw817 := by apply Matrix.ext; unfold raw816 raw817; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4180 = raw817Labels := by decide +kernel
    rw [ha, hj, canonical817 B hB]
  have hc1 : mixedMoment B raw816 (Fin.cases (1 : Fin 2) singletonSmall4180) =
      mixedMoment B node1519 node1519Labels := by
    have ha : raw816 = raw818 := by apply Matrix.ext; unfold raw816 raw818; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4180 = raw818Labels := by decide +kernel
    rw [ha, hj, canonical818 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4181 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4181 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4181 node4181Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node609 node609Labels + mixedMoment B node1521 node1521Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw819 singletonSmall4181
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4181) = raw819Labels := by decide +kernel
  rw [hl, canonical819 B hB] at h
  have hc0 : mixedMoment B raw819 (Fin.cases (0 : Fin 2) singletonSmall4181) =
      mixedMoment B node609 node609Labels := by
    have ha : raw819 = raw820 := by apply Matrix.ext; unfold raw819 raw820; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4181 = raw820Labels := by decide +kernel
    rw [ha, hj, canonical820 B hB]
  have hc1 : mixedMoment B raw819 (Fin.cases (1 : Fin 2) singletonSmall4181) =
      mixedMoment B node1521 node1521Labels := by
    have ha : raw819 = raw821 := by apply Matrix.ext; unfold raw819 raw821; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4181 = raw821Labels := by decide +kernel
    rw [ha, hj, canonical821 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4182 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4182 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4182 node4182Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node610 node610Labels + mixedMoment B node1524 node1524Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw822 singletonSmall4182
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4182) = raw822Labels := by decide +kernel
  rw [hl, canonical822 B hB] at h
  have hc0 : mixedMoment B raw822 (Fin.cases (0 : Fin 2) singletonSmall4182) =
      mixedMoment B node610 node610Labels := by
    have ha : raw822 = raw823 := by apply Matrix.ext; unfold raw822 raw823; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4182 = raw823Labels := by decide +kernel
    rw [ha, hj, canonical823 B hB]
  have hc1 : mixedMoment B raw822 (Fin.cases (1 : Fin 2) singletonSmall4182) =
      mixedMoment B node1524 node1524Labels := by
    have ha : raw822 = raw824 := by apply Matrix.ext; unfold raw822 raw824; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4182 = raw824Labels := by decide +kernel
    rw [ha, hj, canonical824 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4183 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4183 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4183 node4183Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node611 node611Labels + mixedMoment B node1535 node1535Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw825 singletonSmall4183
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4183) = raw825Labels := by decide +kernel
  rw [hl, canonical825 B hB] at h
  have hc0 : mixedMoment B raw825 (Fin.cases (0 : Fin 2) singletonSmall4183) =
      mixedMoment B node611 node611Labels := by
    have ha : raw825 = raw826 := by apply Matrix.ext; unfold raw825 raw826; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4183 = raw826Labels := by decide +kernel
    rw [ha, hj, canonical826 B hB]
  have hc1 : mixedMoment B raw825 (Fin.cases (1 : Fin 2) singletonSmall4183) =
      mixedMoment B node1535 node1535Labels := by
    have ha : raw825 = raw827 := by apply Matrix.ext; unfold raw825 raw827; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4183 = raw827Labels := by decide +kernel
    rw [ha, hj, canonical827 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4185 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4185 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4185 node4185Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node613 node613Labels + mixedMoment B node1525 node1525Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw828 singletonSmall4185
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4185) = raw828Labels := by decide +kernel
  rw [hl, canonical828 B hB] at h
  have hc0 : mixedMoment B raw828 (Fin.cases (0 : Fin 2) singletonSmall4185) =
      mixedMoment B node613 node613Labels := by
    have ha : raw828 = raw829 := by apply Matrix.ext; unfold raw828 raw829; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4185 = raw829Labels := by decide +kernel
    rw [ha, hj, canonical829 B hB]
  have hc1 : mixedMoment B raw828 (Fin.cases (1 : Fin 2) singletonSmall4185) =
      mixedMoment B node1525 node1525Labels := by
    have ha : raw828 = raw830 := by apply Matrix.ext; unfold raw828 raw830; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4185 = raw830Labels := by decide +kernel
    rw [ha, hj, canonical830 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4186 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4186 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4186 node4186Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node614 node614Labels + mixedMoment B node1536 node1536Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw831 singletonSmall4186
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4186) = raw831Labels := by decide +kernel
  rw [hl, canonical831 B hB] at h
  have hc0 : mixedMoment B raw831 (Fin.cases (0 : Fin 2) singletonSmall4186) =
      mixedMoment B node614 node614Labels := by
    have ha : raw831 = raw832 := by apply Matrix.ext; unfold raw831 raw832; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4186 = raw832Labels := by decide +kernel
    rw [ha, hj, canonical832 B hB]
  have hc1 : mixedMoment B raw831 (Fin.cases (1 : Fin 2) singletonSmall4186) =
      mixedMoment B node1536 node1536Labels := by
    have ha : raw831 = raw833 := by apply Matrix.ext; unfold raw831 raw833; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4186 = raw833Labels := by decide +kernel
    rw [ha, hj, canonical833 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4187 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4187 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4187 node4187Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node615 node615Labels + mixedMoment B node1537 node1537Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw834 singletonSmall4187
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4187) = raw834Labels := by decide +kernel
  rw [hl, canonical834 B hB] at h
  have hc0 : mixedMoment B raw834 (Fin.cases (0 : Fin 2) singletonSmall4187) =
      mixedMoment B node615 node615Labels := by
    have ha : raw834 = raw835 := by apply Matrix.ext; unfold raw834 raw835; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4187 = raw835Labels := by decide +kernel
    rw [ha, hj, canonical835 B hB]
  have hc1 : mixedMoment B raw834 (Fin.cases (1 : Fin 2) singletonSmall4187) =
      mixedMoment B node1537 node1537Labels := by
    have ha : raw834 = raw836 := by apply Matrix.ext; unfold raw834 raw836; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4187 = raw836Labels := by decide +kernel
    rw [ha, hj, canonical836 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4190 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4190 node4190Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node618 node618Labels + mixedMoment B node1527 node1527Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw837 singletonSmall4190
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4190) = raw837Labels := by decide +kernel
  rw [hl, canonical837 B hB] at h
  have hc0 : mixedMoment B raw837 (Fin.cases (0 : Fin 2) singletonSmall4190) =
      mixedMoment B node618 node618Labels := by
    have ha : raw837 = raw838 := by apply Matrix.ext; unfold raw837 raw838; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4190 = raw838Labels := by decide +kernel
    rw [ha, hj, canonical838 B hB]
  have hc1 : mixedMoment B raw837 (Fin.cases (1 : Fin 2) singletonSmall4190) =
      mixedMoment B node1527 node1527Labels := by
    have ha : raw837 = raw839 := by apply Matrix.ext; unfold raw837 raw839; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4190 = raw839Labels := by decide +kernel
    rw [ha, hj, canonical839 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4191 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4191 node4191Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node619 node619Labels + mixedMoment B node1538 node1538Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw840 singletonSmall4191
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4191) = raw840Labels := by decide +kernel
  rw [hl, canonical840 B hB] at h
  have hc0 : mixedMoment B raw840 (Fin.cases (0 : Fin 2) singletonSmall4191) =
      mixedMoment B node619 node619Labels := by
    have ha : raw840 = raw841 := by apply Matrix.ext; unfold raw840 raw841; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4191 = raw841Labels := by decide +kernel
    rw [ha, hj, canonical841 B hB]
  have hc1 : mixedMoment B raw840 (Fin.cases (1 : Fin 2) singletonSmall4191) =
      mixedMoment B node1538 node1538Labels := by
    have ha : raw840 = raw842 := by apply Matrix.ext; unfold raw840 raw842; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4191 = raw842Labels := by decide +kernel
    rw [ha, hj, canonical842 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4192 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4192 node4192Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node620 node620Labels + mixedMoment B node1539 node1539Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw843 singletonSmall4192
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4192) = raw843Labels := by decide +kernel
  rw [hl, canonical843 B hB] at h
  have hc0 : mixedMoment B raw843 (Fin.cases (0 : Fin 2) singletonSmall4192) =
      mixedMoment B node620 node620Labels := by
    have ha : raw843 = raw844 := by apply Matrix.ext; unfold raw843 raw844; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4192 = raw844Labels := by decide +kernel
    rw [ha, hj, canonical844 B hB]
  have hc1 : mixedMoment B raw843 (Fin.cases (1 : Fin 2) singletonSmall4192) =
      mixedMoment B node1539 node1539Labels := by
    have ha : raw843 = raw845 := by apply Matrix.ext; unfold raw843 raw845; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4192 = raw845Labels := by decide +kernel
    rw [ha, hj, canonical845 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4194 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4194 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4194 node4194Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node622 node622Labels + mixedMoment B node1541 node1541Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw846 singletonSmall4194
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4194) = raw846Labels := by decide +kernel
  rw [hl, canonical846 B hB] at h
  have hc0 : mixedMoment B raw846 (Fin.cases (0 : Fin 2) singletonSmall4194) =
      mixedMoment B node622 node622Labels := by
    have ha : raw846 = raw847 := by apply Matrix.ext; unfold raw846 raw847; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4194 = raw847Labels := by decide +kernel
    rw [ha, hj, canonical847 B hB]
  have hc1 : mixedMoment B raw846 (Fin.cases (1 : Fin 2) singletonSmall4194) =
      mixedMoment B node1541 node1541Labels := by
    have ha : raw846 = raw848 := by apply Matrix.ext; unfold raw846 raw848; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4194 = raw848Labels := by decide +kernel
    rw [ha, hj, canonical848 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4195 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4195 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4195 node4195Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node698 node698Labels + mixedMoment B node744 node744Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw849 singletonSmall4195
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4195) = raw849Labels := by decide +kernel
  rw [hl, canonical849 B hB] at h
  have hc0 : mixedMoment B raw849 (Fin.cases (0 : Fin 2) singletonSmall4195) =
      mixedMoment B node698 node698Labels := by
    have ha : raw849 = raw850 := by apply Matrix.ext; unfold raw849 raw850; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4195 = raw850Labels := by decide +kernel
    rw [ha, hj, canonical850 B hB]
  have hc1 : mixedMoment B raw849 (Fin.cases (1 : Fin 2) singletonSmall4195) =
      mixedMoment B node744 node744Labels := by
    have ha : raw849 = raw851 := by apply Matrix.ext; unfold raw849 raw851; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4195 = raw851Labels := by decide +kernel
    rw [ha, hj, canonical851 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4196 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4196 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4196 node4196Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node699 node699Labels + mixedMoment B node748 node748Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw852 singletonSmall4196
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4196) = raw852Labels := by decide +kernel
  rw [hl, canonical852 B hB] at h
  have hc0 : mixedMoment B raw852 (Fin.cases (0 : Fin 2) singletonSmall4196) =
      mixedMoment B node699 node699Labels := by
    have ha : raw852 = raw853 := by apply Matrix.ext; unfold raw852 raw853; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4196 = raw853Labels := by decide +kernel
    rw [ha, hj, canonical853 B hB]
  have hc1 : mixedMoment B raw852 (Fin.cases (1 : Fin 2) singletonSmall4196) =
      mixedMoment B node748 node748Labels := by
    have ha : raw852 = raw854 := by apply Matrix.ext; unfold raw852 raw854; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4196 = raw854Labels := by decide +kernel
    rw [ha, hj, canonical854 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4197 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4197 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4197 node4197Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node700 node700Labels + mixedMoment B node749 node749Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw855 singletonSmall4197
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4197) = raw855Labels := by decide +kernel
  rw [hl, canonical855 B hB] at h
  have hc0 : mixedMoment B raw855 (Fin.cases (0 : Fin 2) singletonSmall4197) =
      mixedMoment B node700 node700Labels := by
    have ha : raw855 = raw856 := by apply Matrix.ext; unfold raw855 raw856; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4197 = raw856Labels := by decide +kernel
    rw [ha, hj, canonical856 B hB]
  have hc1 : mixedMoment B raw855 (Fin.cases (1 : Fin 2) singletonSmall4197) =
      mixedMoment B node749 node749Labels := by
    have ha : raw855 = raw857 := by apply Matrix.ext; unfold raw855 raw857; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4197 = raw857Labels := by decide +kernel
    rw [ha, hj, canonical857 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4198 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4198 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4198 node4198Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node701 node701Labels + mixedMoment B node750 node750Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw858 singletonSmall4198
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4198) = raw858Labels := by decide +kernel
  rw [hl, canonical858 B hB] at h
  have hc0 : mixedMoment B raw858 (Fin.cases (0 : Fin 2) singletonSmall4198) =
      mixedMoment B node701 node701Labels := by
    have ha : raw858 = raw859 := by apply Matrix.ext; unfold raw858 raw859; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4198 = raw859Labels := by decide +kernel
    rw [ha, hj, canonical859 B hB]
  have hc1 : mixedMoment B raw858 (Fin.cases (1 : Fin 2) singletonSmall4198) =
      mixedMoment B node750 node750Labels := by
    have ha : raw858 = raw860 := by apply Matrix.ext; unfold raw858 raw860; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4198 = raw860Labels := by decide +kernel
    rw [ha, hj, canonical860 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4199 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4199 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4199 node4199Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node702 node702Labels + mixedMoment B node760 node760Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw861 singletonSmall4199
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4199) = raw861Labels := by decide +kernel
  rw [hl, canonical861 B hB] at h
  have hc0 : mixedMoment B raw861 (Fin.cases (0 : Fin 2) singletonSmall4199) =
      mixedMoment B node702 node702Labels := by
    have ha : raw861 = raw862 := by apply Matrix.ext; unfold raw861 raw862; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4199 = raw862Labels := by decide +kernel
    rw [ha, hj, canonical862 B hB]
  have hc1 : mixedMoment B raw861 (Fin.cases (1 : Fin 2) singletonSmall4199) =
      mixedMoment B node760 node760Labels := by
    have ha : raw861 = raw863 := by apply Matrix.ext; unfold raw861 raw863; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4199 = raw863Labels := by decide +kernel
    rw [ha, hj, canonical863 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4200 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4200 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4200 node4200Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node703 node703Labels + mixedMoment B node754 node754Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw864 singletonSmall4200
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4200) = raw864Labels := by decide +kernel
  rw [hl, canonical864 B hB] at h
  have hc0 : mixedMoment B raw864 (Fin.cases (0 : Fin 2) singletonSmall4200) =
      mixedMoment B node703 node703Labels := by
    have ha : raw864 = raw865 := by apply Matrix.ext; unfold raw864 raw865; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4200 = raw865Labels := by decide +kernel
    rw [ha, hj, canonical865 B hB]
  have hc1 : mixedMoment B raw864 (Fin.cases (1 : Fin 2) singletonSmall4200) =
      mixedMoment B node754 node754Labels := by
    have ha : raw864 = raw866 := by apply Matrix.ext; unfold raw864 raw866; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4200 = raw866Labels := by decide +kernel
    rw [ha, hj, canonical866 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4201 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4201 node4201Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node704 node704Labels + mixedMoment B node761 node761Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw867 singletonSmall4201
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4201) = raw867Labels := by decide +kernel
  rw [hl, canonical867 B hB] at h
  have hc0 : mixedMoment B raw867 (Fin.cases (0 : Fin 2) singletonSmall4201) =
      mixedMoment B node704 node704Labels := by
    have ha : raw867 = raw868 := by apply Matrix.ext; unfold raw867 raw868; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4201 = raw868Labels := by decide +kernel
    rw [ha, hj, canonical868 B hB]
  have hc1 : mixedMoment B raw867 (Fin.cases (1 : Fin 2) singletonSmall4201) =
      mixedMoment B node761 node761Labels := by
    have ha : raw867 = raw869 := by apply Matrix.ext; unfold raw867 raw869; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4201 = raw869Labels := by decide +kernel
    rw [ha, hj, canonical869 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4202 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4202 node4202Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node705 node705Labels + mixedMoment B node762 node762Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw870 singletonSmall4202
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4202) = raw870Labels := by decide +kernel
  rw [hl, canonical870 B hB] at h
  have hc0 : mixedMoment B raw870 (Fin.cases (0 : Fin 2) singletonSmall4202) =
      mixedMoment B node705 node705Labels := by
    have ha : raw870 = raw871 := by apply Matrix.ext; unfold raw870 raw871; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4202 = raw871Labels := by decide +kernel
    rw [ha, hj, canonical871 B hB]
  have hc1 : mixedMoment B raw870 (Fin.cases (1 : Fin 2) singletonSmall4202) =
      mixedMoment B node762 node762Labels := by
    have ha : raw870 = raw872 := by apply Matrix.ext; unfold raw870 raw872; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4202 = raw872Labels := by decide +kernel
    rw [ha, hj, canonical872 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4203 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4203 node4203Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node706 node706Labels + mixedMoment B node755 node755Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw873 singletonSmall4203
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4203) = raw873Labels := by decide +kernel
  rw [hl, canonical873 B hB] at h
  have hc0 : mixedMoment B raw873 (Fin.cases (0 : Fin 2) singletonSmall4203) =
      mixedMoment B node706 node706Labels := by
    have ha : raw873 = raw874 := by apply Matrix.ext; unfold raw873 raw874; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4203 = raw874Labels := by decide +kernel
    rw [ha, hj, canonical874 B hB]
  have hc1 : mixedMoment B raw873 (Fin.cases (1 : Fin 2) singletonSmall4203) =
      mixedMoment B node755 node755Labels := by
    have ha : raw873 = raw875 := by apply Matrix.ext; unfold raw873 raw875; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4203 = raw875Labels := by decide +kernel
    rw [ha, hj, canonical875 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4204 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4204 node4204Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node707 node707Labels + mixedMoment B node763 node763Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw876 singletonSmall4204
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4204) = raw876Labels := by decide +kernel
  rw [hl, canonical876 B hB] at h
  have hc0 : mixedMoment B raw876 (Fin.cases (0 : Fin 2) singletonSmall4204) =
      mixedMoment B node707 node707Labels := by
    have ha : raw876 = raw877 := by apply Matrix.ext; unfold raw876 raw877; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4204 = raw877Labels := by decide +kernel
    rw [ha, hj, canonical877 B hB]
  have hc1 : mixedMoment B raw876 (Fin.cases (1 : Fin 2) singletonSmall4204) =
      mixedMoment B node763 node763Labels := by
    have ha : raw876 = raw878 := by apply Matrix.ext; unfold raw876 raw878; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4204 = raw878Labels := by decide +kernel
    rw [ha, hj, canonical878 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4205 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4205 node4205Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node708 node708Labels + mixedMoment B node764 node764Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw879 singletonSmall4205
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4205) = raw879Labels := by decide +kernel
  rw [hl, canonical879 B hB] at h
  have hc0 : mixedMoment B raw879 (Fin.cases (0 : Fin 2) singletonSmall4205) =
      mixedMoment B node708 node708Labels := by
    have ha : raw879 = raw880 := by apply Matrix.ext; unfold raw879 raw880; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4205 = raw880Labels := by decide +kernel
    rw [ha, hj, canonical880 B hB]
  have hc1 : mixedMoment B raw879 (Fin.cases (1 : Fin 2) singletonSmall4205) =
      mixedMoment B node764 node764Labels := by
    have ha : raw879 = raw881 := by apply Matrix.ext; unfold raw879 raw881; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4205 = raw881Labels := by decide +kernel
    rw [ha, hj, canonical881 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4206 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4206 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4206 node4206Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node709 node709Labels + mixedMoment B node745 node745Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw882 singletonSmall4206
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4206) = raw882Labels := by decide +kernel
  rw [hl, canonical882 B hB] at h
  have hc0 : mixedMoment B raw882 (Fin.cases (0 : Fin 2) singletonSmall4206) =
      mixedMoment B node709 node709Labels := by
    have ha : raw882 = raw883 := by apply Matrix.ext; unfold raw882 raw883; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4206 = raw883Labels := by decide +kernel
    rw [ha, hj, canonical883 B hB]
  have hc1 : mixedMoment B raw882 (Fin.cases (1 : Fin 2) singletonSmall4206) =
      mixedMoment B node745 node745Labels := by
    have ha : raw882 = raw884 := by apply Matrix.ext; unfold raw882 raw884; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4206 = raw884Labels := by decide +kernel
    rw [ha, hj, canonical884 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4207 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4207 node4207Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node710 node710Labels + mixedMoment B node746 node746Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw885 singletonSmall4207
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4207) = raw885Labels := by decide +kernel
  rw [hl, canonical885 B hB] at h
  have hc0 : mixedMoment B raw885 (Fin.cases (0 : Fin 2) singletonSmall4207) =
      mixedMoment B node710 node710Labels := by
    have ha : raw885 = raw886 := by apply Matrix.ext; unfold raw885 raw886; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4207 = raw886Labels := by decide +kernel
    rw [ha, hj, canonical886 B hB]
  have hc1 : mixedMoment B raw885 (Fin.cases (1 : Fin 2) singletonSmall4207) =
      mixedMoment B node746 node746Labels := by
    have ha : raw885 = raw887 := by apply Matrix.ext; unfold raw885 raw887; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4207 = raw887Labels := by decide +kernel
    rw [ha, hj, canonical887 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4208 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4208 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4208 node4208Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node711 node711Labels + mixedMoment B node747 node747Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw888 singletonSmall4208
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4208) = raw888Labels := by decide +kernel
  rw [hl, canonical888 B hB] at h
  have hc0 : mixedMoment B raw888 (Fin.cases (0 : Fin 2) singletonSmall4208) =
      mixedMoment B node711 node711Labels := by
    have ha : raw888 = raw889 := by apply Matrix.ext; unfold raw888 raw889; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4208 = raw889Labels := by decide +kernel
    rw [ha, hj, canonical889 B hB]
  have hc1 : mixedMoment B raw888 (Fin.cases (1 : Fin 2) singletonSmall4208) =
      mixedMoment B node747 node747Labels := by
    have ha : raw888 = raw890 := by apply Matrix.ext; unfold raw888 raw890; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4208 = raw890Labels := by decide +kernel
    rw [ha, hj, canonical890 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4210 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4210 node4210Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node713 node713Labels + mixedMoment B node751 node751Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw891 singletonSmall4210
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4210) = raw891Labels := by decide +kernel
  rw [hl, canonical891 B hB] at h
  have hc0 : mixedMoment B raw891 (Fin.cases (0 : Fin 2) singletonSmall4210) =
      mixedMoment B node713 node713Labels := by
    have ha : raw891 = raw892 := by apply Matrix.ext; unfold raw891 raw892; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4210 = raw892Labels := by decide +kernel
    rw [ha, hj, canonical892 B hB]
  have hc1 : mixedMoment B raw891 (Fin.cases (1 : Fin 2) singletonSmall4210) =
      mixedMoment B node751 node751Labels := by
    have ha : raw891 = raw893 := by apply Matrix.ext; unfold raw891 raw893; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4210 = raw893Labels := by decide +kernel
    rw [ha, hj, canonical893 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4212 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4212 node4212Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node715 node715Labels + mixedMoment B node753 node753Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw894 singletonSmall4212
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4212) = raw894Labels := by decide +kernel
  rw [hl, canonical894 B hB] at h
  have hc0 : mixedMoment B raw894 (Fin.cases (0 : Fin 2) singletonSmall4212) =
      mixedMoment B node715 node715Labels := by
    have ha : raw894 = raw895 := by apply Matrix.ext; unfold raw894 raw895; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4212 = raw895Labels := by decide +kernel
    rw [ha, hj, canonical895 B hB]
  have hc1 : mixedMoment B raw894 (Fin.cases (1 : Fin 2) singletonSmall4212) =
      mixedMoment B node753 node753Labels := by
    have ha : raw894 = raw896 := by apply Matrix.ext; unfold raw894 raw896; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4212 = raw896Labels := by decide +kernel
    rw [ha, hj, canonical896 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4213 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4213 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4213 node4213Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node716 node716Labels + mixedMoment B node752 node752Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw897 singletonSmall4213
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4213) = raw897Labels := by decide +kernel
  rw [hl, canonical897 B hB] at h
  have hc0 : mixedMoment B raw897 (Fin.cases (0 : Fin 2) singletonSmall4213) =
      mixedMoment B node716 node716Labels := by
    have ha : raw897 = raw898 := by apply Matrix.ext; unfold raw897 raw898; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4213 = raw898Labels := by decide +kernel
    rw [ha, hj, canonical898 B hB]
  have hc1 : mixedMoment B raw897 (Fin.cases (1 : Fin 2) singletonSmall4213) =
      mixedMoment B node752 node752Labels := by
    have ha : raw897 = raw899 := by apply Matrix.ext; unfold raw897 raw899; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4213 = raw899Labels := by decide +kernel
    rw [ha, hj, canonical899 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4217 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4217 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4217 node4217Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node719 node719Labels + mixedMoment B node756 node756Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw900 singletonSmall4217
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4217) = raw900Labels := by decide +kernel
  rw [hl, canonical900 B hB] at h
  have hc0 : mixedMoment B raw900 (Fin.cases (0 : Fin 2) singletonSmall4217) =
      mixedMoment B node719 node719Labels := by
    have ha : raw900 = raw901 := by apply Matrix.ext; unfold raw900 raw901; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4217 = raw901Labels := by decide +kernel
    rw [ha, hj, canonical901 B hB]
  have hc1 : mixedMoment B raw900 (Fin.cases (1 : Fin 2) singletonSmall4217) =
      mixedMoment B node756 node756Labels := by
    have ha : raw900 = raw902 := by apply Matrix.ext; unfold raw900 raw902; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4217 = raw902Labels := by decide +kernel
    rw [ha, hj, canonical902 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4219 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4219 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4219 node4219Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node720 node720Labels + mixedMoment B node769 node769Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw903 singletonSmall4219
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4219) = raw903Labels := by decide +kernel
  rw [hl, canonical903 B hB] at h
  have hc0 : mixedMoment B raw903 (Fin.cases (0 : Fin 2) singletonSmall4219) =
      mixedMoment B node720 node720Labels := by
    have ha : raw903 = raw904 := by apply Matrix.ext; unfold raw903 raw904; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4219 = raw904Labels := by decide +kernel
    rw [ha, hj, canonical904 B hB]
  have hc1 : mixedMoment B raw903 (Fin.cases (1 : Fin 2) singletonSmall4219) =
      mixedMoment B node769 node769Labels := by
    have ha : raw903 = raw905 := by apply Matrix.ext; unfold raw903 raw905; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4219 = raw905Labels := by decide +kernel
    rw [ha, hj, canonical905 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4220 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4220 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4220 node4220Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node721 node721Labels + mixedMoment B node757 node757Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw906 singletonSmall4220
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4220) = raw906Labels := by decide +kernel
  rw [hl, canonical906 B hB] at h
  have hc0 : mixedMoment B raw906 (Fin.cases (0 : Fin 2) singletonSmall4220) =
      mixedMoment B node721 node721Labels := by
    have ha : raw906 = raw907 := by apply Matrix.ext; unfold raw906 raw907; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4220 = raw907Labels := by decide +kernel
    rw [ha, hj, canonical907 B hB]
  have hc1 : mixedMoment B raw906 (Fin.cases (1 : Fin 2) singletonSmall4220) =
      mixedMoment B node757 node757Labels := by
    have ha : raw906 = raw908 := by apply Matrix.ext; unfold raw906 raw908; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4220 = raw908Labels := by decide +kernel
    rw [ha, hj, canonical908 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4223 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4223 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4223 node4223Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node724 node724Labels + mixedMoment B node758 node758Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw909 singletonSmall4223
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4223) = raw909Labels := by decide +kernel
  rw [hl, canonical909 B hB] at h
  have hc0 : mixedMoment B raw909 (Fin.cases (0 : Fin 2) singletonSmall4223) =
      mixedMoment B node724 node724Labels := by
    have ha : raw909 = raw910 := by apply Matrix.ext; unfold raw909 raw910; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4223 = raw910Labels := by decide +kernel
    rw [ha, hj, canonical910 B hB]
  have hc1 : mixedMoment B raw909 (Fin.cases (1 : Fin 2) singletonSmall4223) =
      mixedMoment B node758 node758Labels := by
    have ha : raw909 = raw911 := by apply Matrix.ext; unfold raw909 raw911; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4223 = raw911Labels := by decide +kernel
    rw [ha, hj, canonical911 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
