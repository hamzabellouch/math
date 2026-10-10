import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound23
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt736 : keyMomentRows (736 : Fin 2886) =
    keyMomentRow736 := by decide +kernel

theorem keyMomentRowsAt737 : keyMomentRows (737 : Fin 2886) =
    keyMomentRow737 := by decide +kernel

theorem keyMomentRowsAt738 : keyMomentRows (738 : Fin 2886) =
    keyMomentRow738 := by decide +kernel

theorem keyMomentRowsAt739 : keyMomentRows (739 : Fin 2886) =
    keyMomentRow739 := by decide +kernel

theorem keyMomentRowsAt740 : keyMomentRows (740 : Fin 2886) =
    keyMomentRow740 := by decide +kernel

theorem keyMomentRowsAt741 : keyMomentRows (741 : Fin 2886) =
    keyMomentRow741 := by decide +kernel

theorem keyMomentRowsAt742 : keyMomentRows (742 : Fin 2886) =
    keyMomentRow742 := by decide +kernel

theorem keyMomentRowsAt743 : keyMomentRows (743 : Fin 2886) =
    keyMomentRow743 := by decide +kernel

theorem keyMomentRowsAt744 : keyMomentRows (744 : Fin 2886) =
    keyMomentRow744 := by decide +kernel

theorem keyMomentRowsAt745 : keyMomentRows (745 : Fin 2886) =
    keyMomentRow745 := by decide +kernel

theorem keyMomentRowsAt746 : keyMomentRows (746 : Fin 2886) =
    keyMomentRow746 := by decide +kernel

theorem keyMomentRowsAt747 : keyMomentRows (747 : Fin 2886) =
    keyMomentRow747 := by decide +kernel

theorem keyMomentRowsAt748 : keyMomentRows (748 : Fin 2886) =
    keyMomentRow748 := by decide +kernel

theorem keyMomentRowsAt749 : keyMomentRows (749 : Fin 2886) =
    keyMomentRow749 := by decide +kernel

theorem keyMomentRowsAt750 : keyMomentRows (750 : Fin 2886) =
    keyMomentRow750 := by decide +kernel

theorem keyMomentRowsAt751 : keyMomentRows (751 : Fin 2886) =
    keyMomentRow751 := by decide +kernel

theorem keyMomentRowsAt752 : keyMomentRows (752 : Fin 2886) =
    keyMomentRow752 := by decide +kernel

theorem keyMomentRowsAt753 : keyMomentRows (753 : Fin 2886) =
    keyMomentRow753 := by decide +kernel

theorem keyMomentRowsAt754 : keyMomentRows (754 : Fin 2886) =
    keyMomentRow754 := by decide +kernel

theorem keyMomentRowsAt755 : keyMomentRows (755 : Fin 2886) =
    keyMomentRow755 := by decide +kernel

theorem keyMomentRowsAt756 : keyMomentRows (756 : Fin 2886) =
    keyMomentRow756 := by decide +kernel

theorem keyMomentRowsAt757 : keyMomentRows (757 : Fin 2886) =
    keyMomentRow757 := by decide +kernel

theorem keyMomentRowsAt758 : keyMomentRows (758 : Fin 2886) =
    keyMomentRow758 := by decide +kernel

theorem keyMomentRowsAt759 : keyMomentRows (759 : Fin 2886) =
    keyMomentRow759 := by decide +kernel

theorem keyMomentRowsAt760 : keyMomentRows (760 : Fin 2886) =
    keyMomentRow760 := by decide +kernel

theorem keyMomentRowsAt761 : keyMomentRows (761 : Fin 2886) =
    keyMomentRow761 := by decide +kernel

theorem keyMomentRowsAt762 : keyMomentRows (762 : Fin 2886) =
    keyMomentRow762 := by decide +kernel

theorem keyMomentRowsAt763 : keyMomentRows (763 : Fin 2886) =
    keyMomentRow763 := by decide +kernel

theorem keyMomentRowsAt764 : keyMomentRows (764 : Fin 2886) =
    keyMomentRow764 := by decide +kernel

theorem keyMomentRowsAt765 : keyMomentRows (765 : Fin 2886) =
    keyMomentRow765 := by decide +kernel

theorem keyMomentRowsAt766 : keyMomentRows (766 : Fin 2886) =
    keyMomentRow766 := by decide +kernel

theorem keyMomentRowsAt767 : keyMomentRows (767 : Fin 2886) =
    keyMomentRow767 := by decide +kernel

theorem keyMomentChunkSound23 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 23) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 736 ∨ k.val = 737 ∨ k.val = 738 ∨ k.val = 739 ∨ k.val = 740 ∨ k.val = 741 ∨ k.val = 742 ∨ k.val = 743 ∨ k.val = 744 ∨ k.val = 745 ∨ k.val = 746 ∨ k.val = 747 ∨ k.val = 748 ∨ k.val = 749 ∨ k.val = 750 ∨ k.val = 751 ∨ k.val = 752 ∨ k.val = 753 ∨ k.val = 754 ∨ k.val = 755 ∨ k.val = 756 ∨ k.val = 757 ∨ k.val = 758 ∨ k.val = 759 ∨ k.val = 760 ∨ k.val = 761 ∨ k.val = 762 ∨ k.val = 763 ∨ k.val = 764 ∨ k.val = 765 ∨ k.val = 766 ∨ k.val = 767 := by omega
  rcases heq with h736 | h737 | h738 | h739 | h740 | h741 | h742 | h743 | h744 | h745 | h746 | h747 | h748 | h749 | h750 | h751 | h752 | h753 | h754 | h755 | h756 | h757 | h758 | h759 | h760 | h761 | h762 | h763 | h764 | h765 | h766 | h767
  · have he : k = (736 : Fin 2886) := Fin.ext h736
    subst k
    rw [keyMomentRowsAt736]
    exact keyMoment736 B hB
  · have he : k = (737 : Fin 2886) := Fin.ext h737
    subst k
    rw [keyMomentRowsAt737]
    exact keyMoment737 B hB
  · have he : k = (738 : Fin 2886) := Fin.ext h738
    subst k
    rw [keyMomentRowsAt738]
    exact keyMoment738 B hB
  · have he : k = (739 : Fin 2886) := Fin.ext h739
    subst k
    rw [keyMomentRowsAt739]
    exact keyMoment739 B hB
  · have he : k = (740 : Fin 2886) := Fin.ext h740
    subst k
    rw [keyMomentRowsAt740]
    exact keyMoment740 B hB
  · have he : k = (741 : Fin 2886) := Fin.ext h741
    subst k
    rw [keyMomentRowsAt741]
    exact keyMoment741 B hB
  · have he : k = (742 : Fin 2886) := Fin.ext h742
    subst k
    rw [keyMomentRowsAt742]
    exact keyMoment742 B hB
  · have he : k = (743 : Fin 2886) := Fin.ext h743
    subst k
    rw [keyMomentRowsAt743]
    exact keyMoment743 B hB
  · have he : k = (744 : Fin 2886) := Fin.ext h744
    subst k
    rw [keyMomentRowsAt744]
    exact keyMoment744 B hB
  · have he : k = (745 : Fin 2886) := Fin.ext h745
    subst k
    rw [keyMomentRowsAt745]
    exact keyMoment745 B hB
  · have he : k = (746 : Fin 2886) := Fin.ext h746
    subst k
    rw [keyMomentRowsAt746]
    exact keyMoment746 B hB
  · have he : k = (747 : Fin 2886) := Fin.ext h747
    subst k
    rw [keyMomentRowsAt747]
    exact keyMoment747 B hB
  · have he : k = (748 : Fin 2886) := Fin.ext h748
    subst k
    rw [keyMomentRowsAt748]
    exact keyMoment748 B hB
  · have he : k = (749 : Fin 2886) := Fin.ext h749
    subst k
    rw [keyMomentRowsAt749]
    exact keyMoment749 B hB
  · have he : k = (750 : Fin 2886) := Fin.ext h750
    subst k
    rw [keyMomentRowsAt750]
    exact keyMoment750 B hB
  · have he : k = (751 : Fin 2886) := Fin.ext h751
    subst k
    rw [keyMomentRowsAt751]
    exact keyMoment751 B hB
  · have he : k = (752 : Fin 2886) := Fin.ext h752
    subst k
    rw [keyMomentRowsAt752]
    exact keyMoment752 B hB
  · have he : k = (753 : Fin 2886) := Fin.ext h753
    subst k
    rw [keyMomentRowsAt753]
    exact keyMoment753 B hB
  · have he : k = (754 : Fin 2886) := Fin.ext h754
    subst k
    rw [keyMomentRowsAt754]
    exact keyMoment754 B hB
  · have he : k = (755 : Fin 2886) := Fin.ext h755
    subst k
    rw [keyMomentRowsAt755]
    exact keyMoment755 B hB
  · have he : k = (756 : Fin 2886) := Fin.ext h756
    subst k
    rw [keyMomentRowsAt756]
    exact keyMoment756 B hB
  · have he : k = (757 : Fin 2886) := Fin.ext h757
    subst k
    rw [keyMomentRowsAt757]
    exact keyMoment757 B hB
  · have he : k = (758 : Fin 2886) := Fin.ext h758
    subst k
    rw [keyMomentRowsAt758]
    exact keyMoment758 B hB
  · have he : k = (759 : Fin 2886) := Fin.ext h759
    subst k
    rw [keyMomentRowsAt759]
    exact keyMoment759 B hB
  · have he : k = (760 : Fin 2886) := Fin.ext h760
    subst k
    rw [keyMomentRowsAt760]
    exact keyMoment760 B hB
  · have he : k = (761 : Fin 2886) := Fin.ext h761
    subst k
    rw [keyMomentRowsAt761]
    exact keyMoment761 B hB
  · have he : k = (762 : Fin 2886) := Fin.ext h762
    subst k
    rw [keyMomentRowsAt762]
    exact keyMoment762 B hB
  · have he : k = (763 : Fin 2886) := Fin.ext h763
    subst k
    rw [keyMomentRowsAt763]
    exact keyMoment763 B hB
  · have he : k = (764 : Fin 2886) := Fin.ext h764
    subst k
    rw [keyMomentRowsAt764]
    exact keyMoment764 B hB
  · have he : k = (765 : Fin 2886) := Fin.ext h765
    subst k
    rw [keyMomentRowsAt765]
    exact keyMoment765 B hB
  · have he : k = (766 : Fin 2886) := Fin.ext h766
    subst k
    rw [keyMomentRowsAt766]
    exact keyMoment766 B hB
  · have he : k = (767 : Fin 2886) := Fin.ext h767
    subst k
    rw [keyMomentRowsAt767]
    exact keyMoment767 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
