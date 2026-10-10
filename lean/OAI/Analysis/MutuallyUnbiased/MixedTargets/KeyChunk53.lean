import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound53
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1696 : keyMomentRows (1696 : Fin 2886) =
    keyMomentRow1696 := by decide +kernel

theorem keyMomentRowsAt1697 : keyMomentRows (1697 : Fin 2886) =
    keyMomentRow1697 := by decide +kernel

theorem keyMomentRowsAt1698 : keyMomentRows (1698 : Fin 2886) =
    keyMomentRow1698 := by decide +kernel

theorem keyMomentRowsAt1699 : keyMomentRows (1699 : Fin 2886) =
    keyMomentRow1699 := by decide +kernel

theorem keyMomentRowsAt1700 : keyMomentRows (1700 : Fin 2886) =
    keyMomentRow1700 := by decide +kernel

theorem keyMomentRowsAt1701 : keyMomentRows (1701 : Fin 2886) =
    keyMomentRow1701 := by decide +kernel

theorem keyMomentRowsAt1702 : keyMomentRows (1702 : Fin 2886) =
    keyMomentRow1702 := by decide +kernel

theorem keyMomentRowsAt1703 : keyMomentRows (1703 : Fin 2886) =
    keyMomentRow1703 := by decide +kernel

theorem keyMomentRowsAt1704 : keyMomentRows (1704 : Fin 2886) =
    keyMomentRow1704 := by decide +kernel

theorem keyMomentRowsAt1705 : keyMomentRows (1705 : Fin 2886) =
    keyMomentRow1705 := by decide +kernel

theorem keyMomentRowsAt1706 : keyMomentRows (1706 : Fin 2886) =
    keyMomentRow1706 := by decide +kernel

theorem keyMomentRowsAt1707 : keyMomentRows (1707 : Fin 2886) =
    keyMomentRow1707 := by decide +kernel

theorem keyMomentRowsAt1708 : keyMomentRows (1708 : Fin 2886) =
    keyMomentRow1708 := by decide +kernel

theorem keyMomentRowsAt1709 : keyMomentRows (1709 : Fin 2886) =
    keyMomentRow1709 := by decide +kernel

theorem keyMomentRowsAt1710 : keyMomentRows (1710 : Fin 2886) =
    keyMomentRow1710 := by decide +kernel

theorem keyMomentRowsAt1711 : keyMomentRows (1711 : Fin 2886) =
    keyMomentRow1711 := by decide +kernel

theorem keyMomentRowsAt1712 : keyMomentRows (1712 : Fin 2886) =
    keyMomentRow1712 := by decide +kernel

theorem keyMomentRowsAt1713 : keyMomentRows (1713 : Fin 2886) =
    keyMomentRow1713 := by decide +kernel

theorem keyMomentRowsAt1714 : keyMomentRows (1714 : Fin 2886) =
    keyMomentRow1714 := by decide +kernel

theorem keyMomentRowsAt1715 : keyMomentRows (1715 : Fin 2886) =
    keyMomentRow1715 := by decide +kernel

theorem keyMomentRowsAt1716 : keyMomentRows (1716 : Fin 2886) =
    keyMomentRow1716 := by decide +kernel

theorem keyMomentRowsAt1717 : keyMomentRows (1717 : Fin 2886) =
    keyMomentRow1717 := by decide +kernel

theorem keyMomentRowsAt1718 : keyMomentRows (1718 : Fin 2886) =
    keyMomentRow1718 := by decide +kernel

theorem keyMomentRowsAt1719 : keyMomentRows (1719 : Fin 2886) =
    keyMomentRow1719 := by decide +kernel

theorem keyMomentRowsAt1720 : keyMomentRows (1720 : Fin 2886) =
    keyMomentRow1720 := by decide +kernel

theorem keyMomentRowsAt1721 : keyMomentRows (1721 : Fin 2886) =
    keyMomentRow1721 := by decide +kernel

theorem keyMomentRowsAt1722 : keyMomentRows (1722 : Fin 2886) =
    keyMomentRow1722 := by decide +kernel

theorem keyMomentRowsAt1723 : keyMomentRows (1723 : Fin 2886) =
    keyMomentRow1723 := by decide +kernel

theorem keyMomentRowsAt1724 : keyMomentRows (1724 : Fin 2886) =
    keyMomentRow1724 := by decide +kernel

theorem keyMomentRowsAt1725 : keyMomentRows (1725 : Fin 2886) =
    keyMomentRow1725 := by decide +kernel

theorem keyMomentRowsAt1726 : keyMomentRows (1726 : Fin 2886) =
    keyMomentRow1726 := by decide +kernel

theorem keyMomentRowsAt1727 : keyMomentRows (1727 : Fin 2886) =
    keyMomentRow1727 := by decide +kernel

theorem keyMomentChunkSound53 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 53) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1696 ∨ k.val = 1697 ∨ k.val = 1698 ∨ k.val = 1699 ∨ k.val = 1700 ∨ k.val = 1701 ∨ k.val = 1702 ∨ k.val = 1703 ∨ k.val = 1704 ∨ k.val = 1705 ∨ k.val = 1706 ∨ k.val = 1707 ∨ k.val = 1708 ∨ k.val = 1709 ∨ k.val = 1710 ∨ k.val = 1711 ∨ k.val = 1712 ∨ k.val = 1713 ∨ k.val = 1714 ∨ k.val = 1715 ∨ k.val = 1716 ∨ k.val = 1717 ∨ k.val = 1718 ∨ k.val = 1719 ∨ k.val = 1720 ∨ k.val = 1721 ∨ k.val = 1722 ∨ k.val = 1723 ∨ k.val = 1724 ∨ k.val = 1725 ∨ k.val = 1726 ∨ k.val = 1727 := by omega
  rcases heq with h1696 | h1697 | h1698 | h1699 | h1700 | h1701 | h1702 | h1703 | h1704 | h1705 | h1706 | h1707 | h1708 | h1709 | h1710 | h1711 | h1712 | h1713 | h1714 | h1715 | h1716 | h1717 | h1718 | h1719 | h1720 | h1721 | h1722 | h1723 | h1724 | h1725 | h1726 | h1727
  · have he : k = (1696 : Fin 2886) := Fin.ext h1696
    subst k
    rw [keyMomentRowsAt1696]
    exact keyMoment1696 B hB
  · have he : k = (1697 : Fin 2886) := Fin.ext h1697
    subst k
    rw [keyMomentRowsAt1697]
    exact keyMoment1697 B hB
  · have he : k = (1698 : Fin 2886) := Fin.ext h1698
    subst k
    rw [keyMomentRowsAt1698]
    exact keyMoment1698 B hB
  · have he : k = (1699 : Fin 2886) := Fin.ext h1699
    subst k
    rw [keyMomentRowsAt1699]
    exact keyMoment1699 B hB
  · have he : k = (1700 : Fin 2886) := Fin.ext h1700
    subst k
    rw [keyMomentRowsAt1700]
    exact keyMoment1700 B hB
  · have he : k = (1701 : Fin 2886) := Fin.ext h1701
    subst k
    rw [keyMomentRowsAt1701]
    exact keyMoment1701 B hB
  · have he : k = (1702 : Fin 2886) := Fin.ext h1702
    subst k
    rw [keyMomentRowsAt1702]
    exact keyMoment1702 B hB
  · have he : k = (1703 : Fin 2886) := Fin.ext h1703
    subst k
    rw [keyMomentRowsAt1703]
    exact keyMoment1703 B hB
  · have he : k = (1704 : Fin 2886) := Fin.ext h1704
    subst k
    rw [keyMomentRowsAt1704]
    exact keyMoment1704 B hB
  · have he : k = (1705 : Fin 2886) := Fin.ext h1705
    subst k
    rw [keyMomentRowsAt1705]
    exact keyMoment1705 B hB
  · have he : k = (1706 : Fin 2886) := Fin.ext h1706
    subst k
    rw [keyMomentRowsAt1706]
    exact keyMoment1706 B hB
  · have he : k = (1707 : Fin 2886) := Fin.ext h1707
    subst k
    rw [keyMomentRowsAt1707]
    exact keyMoment1707 B hB
  · have he : k = (1708 : Fin 2886) := Fin.ext h1708
    subst k
    rw [keyMomentRowsAt1708]
    exact keyMoment1708 B hB
  · have he : k = (1709 : Fin 2886) := Fin.ext h1709
    subst k
    rw [keyMomentRowsAt1709]
    exact keyMoment1709 B hB
  · have he : k = (1710 : Fin 2886) := Fin.ext h1710
    subst k
    rw [keyMomentRowsAt1710]
    exact keyMoment1710 B hB
  · have he : k = (1711 : Fin 2886) := Fin.ext h1711
    subst k
    rw [keyMomentRowsAt1711]
    exact keyMoment1711 B hB
  · have he : k = (1712 : Fin 2886) := Fin.ext h1712
    subst k
    rw [keyMomentRowsAt1712]
    exact keyMoment1712 B hB
  · have he : k = (1713 : Fin 2886) := Fin.ext h1713
    subst k
    rw [keyMomentRowsAt1713]
    exact keyMoment1713 B hB
  · have he : k = (1714 : Fin 2886) := Fin.ext h1714
    subst k
    rw [keyMomentRowsAt1714]
    exact keyMoment1714 B hB
  · have he : k = (1715 : Fin 2886) := Fin.ext h1715
    subst k
    rw [keyMomentRowsAt1715]
    exact keyMoment1715 B hB
  · have he : k = (1716 : Fin 2886) := Fin.ext h1716
    subst k
    rw [keyMomentRowsAt1716]
    exact keyMoment1716 B hB
  · have he : k = (1717 : Fin 2886) := Fin.ext h1717
    subst k
    rw [keyMomentRowsAt1717]
    exact keyMoment1717 B hB
  · have he : k = (1718 : Fin 2886) := Fin.ext h1718
    subst k
    rw [keyMomentRowsAt1718]
    exact keyMoment1718 B hB
  · have he : k = (1719 : Fin 2886) := Fin.ext h1719
    subst k
    rw [keyMomentRowsAt1719]
    exact keyMoment1719 B hB
  · have he : k = (1720 : Fin 2886) := Fin.ext h1720
    subst k
    rw [keyMomentRowsAt1720]
    exact keyMoment1720 B hB
  · have he : k = (1721 : Fin 2886) := Fin.ext h1721
    subst k
    rw [keyMomentRowsAt1721]
    exact keyMoment1721 B hB
  · have he : k = (1722 : Fin 2886) := Fin.ext h1722
    subst k
    rw [keyMomentRowsAt1722]
    exact keyMoment1722 B hB
  · have he : k = (1723 : Fin 2886) := Fin.ext h1723
    subst k
    rw [keyMomentRowsAt1723]
    exact keyMoment1723 B hB
  · have he : k = (1724 : Fin 2886) := Fin.ext h1724
    subst k
    rw [keyMomentRowsAt1724]
    exact keyMoment1724 B hB
  · have he : k = (1725 : Fin 2886) := Fin.ext h1725
    subst k
    rw [keyMomentRowsAt1725]
    exact keyMoment1725 B hB
  · have he : k = (1726 : Fin 2886) := Fin.ext h1726
    subst k
    rw [keyMomentRowsAt1726]
    exact keyMoment1726 B hB
  · have he : k = (1727 : Fin 2886) := Fin.ext h1727
    subst k
    rw [keyMomentRowsAt1727]
    exact keyMoment1727 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
