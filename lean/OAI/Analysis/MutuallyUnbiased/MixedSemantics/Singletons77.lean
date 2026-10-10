import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical15

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4928 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4928 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4928 node4928Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2318 node2318Labels + mixedMoment B node3400 node3400Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1893 singletonSmall4928
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4928) = raw1893Labels := by decide +kernel
  rw [hl, canonical1893 B hB] at h
  have hc0 : mixedMoment B raw1893 (Fin.cases (0 : Fin 2) singletonSmall4928) =
      mixedMoment B node2318 node2318Labels := by
    have ha : raw1893 = raw1894 := by apply Matrix.ext; unfold raw1893 raw1894; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4928 = raw1894Labels := by decide +kernel
    rw [ha, hj, canonical1894 B hB]
  have hc1 : mixedMoment B raw1893 (Fin.cases (1 : Fin 2) singletonSmall4928) =
      mixedMoment B node3400 node3400Labels := by
    have ha : raw1893 = raw1895 := by apply Matrix.ext; unfold raw1893 raw1895; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4928 = raw1895Labels := by decide +kernel
    rw [ha, hj, canonical1895 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4936 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4936 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4936 node4936Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2328 node2328Labels + mixedMoment B node3401 node3401Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1896 singletonSmall4936
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4936) = raw1896Labels := by decide +kernel
  rw [hl, canonical1896 B hB] at h
  have hc0 : mixedMoment B raw1896 (Fin.cases (0 : Fin 2) singletonSmall4936) =
      mixedMoment B node2328 node2328Labels := by
    have ha : raw1896 = raw1897 := by apply Matrix.ext; unfold raw1896 raw1897; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4936 = raw1897Labels := by decide +kernel
    rw [ha, hj, canonical1897 B hB]
  have hc1 : mixedMoment B raw1896 (Fin.cases (1 : Fin 2) singletonSmall4936) =
      mixedMoment B node3401 node3401Labels := by
    have ha : raw1896 = raw1898 := by apply Matrix.ext; unfold raw1896 raw1898; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4936 = raw1898Labels := by decide +kernel
    rw [ha, hj, canonical1898 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4937 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4937 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4937 node4937Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2329 node2329Labels + mixedMoment B node3402 node3402Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1899 singletonSmall4937
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4937) = raw1899Labels := by decide +kernel
  rw [hl, canonical1899 B hB] at h
  have hc0 : mixedMoment B raw1899 (Fin.cases (0 : Fin 2) singletonSmall4937) =
      mixedMoment B node2329 node2329Labels := by
    have ha : raw1899 = raw1900 := by apply Matrix.ext; unfold raw1899 raw1900; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4937 = raw1900Labels := by decide +kernel
    rw [ha, hj, canonical1900 B hB]
  have hc1 : mixedMoment B raw1899 (Fin.cases (1 : Fin 2) singletonSmall4937) =
      mixedMoment B node3402 node3402Labels := by
    have ha : raw1899 = raw1901 := by apply Matrix.ext; unfold raw1899 raw1901; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4937 = raw1901Labels := by decide +kernel
    rw [ha, hj, canonical1901 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4939 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4939 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4939 node4939Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2330 node2330Labels + mixedMoment B node3404 node3404Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1902 singletonSmall4939
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4939) = raw1902Labels := by decide +kernel
  rw [hl, canonical1902 B hB] at h
  have hc0 : mixedMoment B raw1902 (Fin.cases (0 : Fin 2) singletonSmall4939) =
      mixedMoment B node2330 node2330Labels := by
    have ha : raw1902 = raw1903 := by apply Matrix.ext; unfold raw1902 raw1903; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4939 = raw1903Labels := by decide +kernel
    rw [ha, hj, canonical1903 B hB]
  have hc1 : mixedMoment B raw1902 (Fin.cases (1 : Fin 2) singletonSmall4939) =
      mixedMoment B node3404 node3404Labels := by
    have ha : raw1902 = raw1904 := by apply Matrix.ext; unfold raw1902 raw1904; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4939 = raw1904Labels := by decide +kernel
    rw [ha, hj, canonical1904 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4941 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4941 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4941 node4941Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2332 node2332Labels + mixedMoment B node3410 node3410Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1905 singletonSmall4941
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4941) = raw1905Labels := by decide +kernel
  rw [hl, canonical1905 B hB] at h
  have hc0 : mixedMoment B raw1905 (Fin.cases (0 : Fin 2) singletonSmall4941) =
      mixedMoment B node2332 node2332Labels := by
    have ha : raw1905 = raw1906 := by apply Matrix.ext; unfold raw1905 raw1906; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4941 = raw1906Labels := by decide +kernel
    rw [ha, hj, canonical1906 B hB]
  have hc1 : mixedMoment B raw1905 (Fin.cases (1 : Fin 2) singletonSmall4941) =
      mixedMoment B node3410 node3410Labels := by
    have ha : raw1905 = raw1907 := by apply Matrix.ext; unfold raw1905 raw1907; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4941 = raw1907Labels := by decide +kernel
    rw [ha, hj, canonical1907 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4943 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4943 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4943 node4943Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2334 node2334Labels + mixedMoment B node3411 node3411Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1908 singletonSmall4943
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4943) = raw1908Labels := by decide +kernel
  rw [hl, canonical1908 B hB] at h
  have hc0 : mixedMoment B raw1908 (Fin.cases (0 : Fin 2) singletonSmall4943) =
      mixedMoment B node2334 node2334Labels := by
    have ha : raw1908 = raw1909 := by apply Matrix.ext; unfold raw1908 raw1909; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4943 = raw1909Labels := by decide +kernel
    rw [ha, hj, canonical1909 B hB]
  have hc1 : mixedMoment B raw1908 (Fin.cases (1 : Fin 2) singletonSmall4943) =
      mixedMoment B node3411 node3411Labels := by
    have ha : raw1908 = raw1910 := by apply Matrix.ext; unfold raw1908 raw1910; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4943 = raw1910Labels := by decide +kernel
    rw [ha, hj, canonical1910 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4946 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4946 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4946 node4946Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2337 node2337Labels + mixedMoment B node3412 node3412Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1911 singletonSmall4946
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4946) = raw1911Labels := by decide +kernel
  rw [hl, canonical1911 B hB] at h
  have hc0 : mixedMoment B raw1911 (Fin.cases (0 : Fin 2) singletonSmall4946) =
      mixedMoment B node2337 node2337Labels := by
    have ha : raw1911 = raw1912 := by apply Matrix.ext; unfold raw1911 raw1912; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4946 = raw1912Labels := by decide +kernel
    rw [ha, hj, canonical1912 B hB]
  have hc1 : mixedMoment B raw1911 (Fin.cases (1 : Fin 2) singletonSmall4946) =
      mixedMoment B node3412 node3412Labels := by
    have ha : raw1911 = raw1913 := by apply Matrix.ext; unfold raw1911 raw1913; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4946 = raw1913Labels := by decide +kernel
    rw [ha, hj, canonical1913 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4947 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4947 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4947 node4947Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2338 node2338Labels + mixedMoment B node3416 node3416Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1914 singletonSmall4947
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4947) = raw1914Labels := by decide +kernel
  rw [hl, canonical1914 B hB] at h
  have hc0 : mixedMoment B raw1914 (Fin.cases (0 : Fin 2) singletonSmall4947) =
      mixedMoment B node2338 node2338Labels := by
    have ha : raw1914 = raw1915 := by apply Matrix.ext; unfold raw1914 raw1915; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4947 = raw1915Labels := by decide +kernel
    rw [ha, hj, canonical1915 B hB]
  have hc1 : mixedMoment B raw1914 (Fin.cases (1 : Fin 2) singletonSmall4947) =
      mixedMoment B node3416 node3416Labels := by
    have ha : raw1914 = raw1916 := by apply Matrix.ext; unfold raw1914 raw1916; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4947 = raw1916Labels := by decide +kernel
    rw [ha, hj, canonical1916 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4948 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4948 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4948 node4948Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2339 node2339Labels + mixedMoment B node3420 node3420Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1917 singletonSmall4948
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4948) = raw1917Labels := by decide +kernel
  rw [hl, canonical1917 B hB] at h
  have hc0 : mixedMoment B raw1917 (Fin.cases (0 : Fin 2) singletonSmall4948) =
      mixedMoment B node2339 node2339Labels := by
    have ha : raw1917 = raw1918 := by apply Matrix.ext; unfold raw1917 raw1918; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4948 = raw1918Labels := by decide +kernel
    rw [ha, hj, canonical1918 B hB]
  have hc1 : mixedMoment B raw1917 (Fin.cases (1 : Fin 2) singletonSmall4948) =
      mixedMoment B node3420 node3420Labels := by
    have ha : raw1917 = raw1919 := by apply Matrix.ext; unfold raw1917 raw1919; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4948 = raw1919Labels := by decide +kernel
    rw [ha, hj, canonical1919 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4949 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4949 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4949 node4949Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2341 node2341Labels + mixedMoment B node3417 node3417Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1920 singletonSmall4949
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4949) = raw1920Labels := by decide +kernel
  rw [hl, canonical1920 B hB] at h
  have hc0 : mixedMoment B raw1920 (Fin.cases (0 : Fin 2) singletonSmall4949) =
      mixedMoment B node2341 node2341Labels := by
    have ha : raw1920 = raw1921 := by apply Matrix.ext; unfold raw1920 raw1921; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4949 = raw1921Labels := by decide +kernel
    rw [ha, hj, canonical1921 B hB]
  have hc1 : mixedMoment B raw1920 (Fin.cases (1 : Fin 2) singletonSmall4949) =
      mixedMoment B node3417 node3417Labels := by
    have ha : raw1920 = raw1922 := by apply Matrix.ext; unfold raw1920 raw1922; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4949 = raw1922Labels := by decide +kernel
    rw [ha, hj, canonical1922 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4950 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4950 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4950 node4950Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2342 node2342Labels + mixedMoment B node3421 node3421Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1923 singletonSmall4950
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4950) = raw1923Labels := by decide +kernel
  rw [hl, canonical1923 B hB] at h
  have hc0 : mixedMoment B raw1923 (Fin.cases (0 : Fin 2) singletonSmall4950) =
      mixedMoment B node2342 node2342Labels := by
    have ha : raw1923 = raw1924 := by apply Matrix.ext; unfold raw1923 raw1924; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4950 = raw1924Labels := by decide +kernel
    rw [ha, hj, canonical1924 B hB]
  have hc1 : mixedMoment B raw1923 (Fin.cases (1 : Fin 2) singletonSmall4950) =
      mixedMoment B node3421 node3421Labels := by
    have ha : raw1923 = raw1925 := by apply Matrix.ext; unfold raw1923 raw1925; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4950 = raw1925Labels := by decide +kernel
    rw [ha, hj, canonical1925 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4952 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4952 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4952 node4952Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2344 node2344Labels + mixedMoment B node3422 node3422Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1926 singletonSmall4952
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4952) = raw1926Labels := by decide +kernel
  rw [hl, canonical1926 B hB] at h
  have hc0 : mixedMoment B raw1926 (Fin.cases (0 : Fin 2) singletonSmall4952) =
      mixedMoment B node2344 node2344Labels := by
    have ha : raw1926 = raw1927 := by apply Matrix.ext; unfold raw1926 raw1927; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4952 = raw1927Labels := by decide +kernel
    rw [ha, hj, canonical1927 B hB]
  have hc1 : mixedMoment B raw1926 (Fin.cases (1 : Fin 2) singletonSmall4952) =
      mixedMoment B node3422 node3422Labels := by
    have ha : raw1926 = raw1928 := by apply Matrix.ext; unfold raw1926 raw1928; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4952 = raw1928Labels := by decide +kernel
    rw [ha, hj, canonical1928 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4953 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4953 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4953 node4953Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2345 node2345Labels + mixedMoment B node3423 node3423Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1929 singletonSmall4953
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4953) = raw1929Labels := by decide +kernel
  rw [hl, canonical1929 B hB] at h
  have hc0 : mixedMoment B raw1929 (Fin.cases (0 : Fin 2) singletonSmall4953) =
      mixedMoment B node2345 node2345Labels := by
    have ha : raw1929 = raw1930 := by apply Matrix.ext; unfold raw1929 raw1930; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4953 = raw1930Labels := by decide +kernel
    rw [ha, hj, canonical1930 B hB]
  have hc1 : mixedMoment B raw1929 (Fin.cases (1 : Fin 2) singletonSmall4953) =
      mixedMoment B node3423 node3423Labels := by
    have ha : raw1929 = raw1931 := by apply Matrix.ext; unfold raw1929 raw1931; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4953 = raw1931Labels := by decide +kernel
    rw [ha, hj, canonical1931 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4960 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4960 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4960 node4960Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2412 node2412Labels + mixedMoment B node3426 node3426Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1932 singletonSmall4960
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4960) = raw1932Labels := by decide +kernel
  rw [hl, canonical1932 B hB] at h
  have hc0 : mixedMoment B raw1932 (Fin.cases (0 : Fin 2) singletonSmall4960) =
      mixedMoment B node2412 node2412Labels := by
    have ha : raw1932 = raw1933 := by apply Matrix.ext; unfold raw1932 raw1933; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4960 = raw1933Labels := by decide +kernel
    rw [ha, hj, canonical1933 B hB]
  have hc1 : mixedMoment B raw1932 (Fin.cases (1 : Fin 2) singletonSmall4960) =
      mixedMoment B node3426 node3426Labels := by
    have ha : raw1932 = raw1934 := by apply Matrix.ext; unfold raw1932 raw1934; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4960 = raw1934Labels := by decide +kernel
    rw [ha, hj, canonical1934 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4961 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4961 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4961 node4961Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2796 node2796Labels + mixedMoment B node3589 node3589Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1935 singletonSmall4961
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4961) = raw1935Labels := by decide +kernel
  rw [hl, canonical1935 B hB] at h
  have hc0 : mixedMoment B raw1935 (Fin.cases (0 : Fin 2) singletonSmall4961) =
      mixedMoment B node2796 node2796Labels := by
    have ha : raw1935 = raw1936 := by apply Matrix.ext; unfold raw1935 raw1936; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4961 = raw1936Labels := by decide +kernel
    rw [ha, hj, canonical1936 B hB]
  have hc1 : mixedMoment B raw1935 (Fin.cases (1 : Fin 2) singletonSmall4961) =
      mixedMoment B node3589 node3589Labels := by
    have ha : raw1935 = raw1937 := by apply Matrix.ext; unfold raw1935 raw1937; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4961 = raw1937Labels := by decide +kernel
    rw [ha, hj, canonical1937 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4962 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4962 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4962 node4962Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2795 node2795Labels + mixedMoment B node3593 node3593Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1938 singletonSmall4962
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4962) = raw1938Labels := by decide +kernel
  rw [hl, canonical1938 B hB] at h
  have hc0 : mixedMoment B raw1938 (Fin.cases (0 : Fin 2) singletonSmall4962) =
      mixedMoment B node2795 node2795Labels := by
    have ha : raw1938 = raw1939 := by apply Matrix.ext; unfold raw1938 raw1939; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4962 = raw1939Labels := by decide +kernel
    rw [ha, hj, canonical1939 B hB]
  have hc1 : mixedMoment B raw1938 (Fin.cases (1 : Fin 2) singletonSmall4962) =
      mixedMoment B node3593 node3593Labels := by
    have ha : raw1938 = raw1940 := by apply Matrix.ext; unfold raw1938 raw1940; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4962 = raw1940Labels := by decide +kernel
    rw [ha, hj, canonical1940 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4967 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4967 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4967 node4967Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2814 node2814Labels + mixedMoment B node3585 node3585Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1941 singletonSmall4967
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4967) = raw1941Labels := by decide +kernel
  rw [hl, canonical1941 B hB] at h
  have hc0 : mixedMoment B raw1941 (Fin.cases (0 : Fin 2) singletonSmall4967) =
      mixedMoment B node2814 node2814Labels := by
    have ha : raw1941 = raw1942 := by apply Matrix.ext; unfold raw1941 raw1942; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4967 = raw1942Labels := by decide +kernel
    rw [ha, hj, canonical1942 B hB]
  have hc1 : mixedMoment B raw1941 (Fin.cases (1 : Fin 2) singletonSmall4967) =
      mixedMoment B node3585 node3585Labels := by
    have ha : raw1941 = raw1943 := by apply Matrix.ext; unfold raw1941 raw1943; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4967 = raw1943Labels := by decide +kernel
    rw [ha, hj, canonical1943 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4968 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4968 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4968 node4968Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2809 node2809Labels + mixedMoment B node3587 node3587Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1944 singletonSmall4968
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4968) = raw1944Labels := by decide +kernel
  rw [hl, canonical1944 B hB] at h
  have hc0 : mixedMoment B raw1944 (Fin.cases (0 : Fin 2) singletonSmall4968) =
      mixedMoment B node2809 node2809Labels := by
    have ha : raw1944 = raw1945 := by apply Matrix.ext; unfold raw1944 raw1945; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4968 = raw1945Labels := by decide +kernel
    rw [ha, hj, canonical1945 B hB]
  have hc1 : mixedMoment B raw1944 (Fin.cases (1 : Fin 2) singletonSmall4968) =
      mixedMoment B node3587 node3587Labels := by
    have ha : raw1944 = raw1946 := by apply Matrix.ext; unfold raw1944 raw1946; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4968 = raw1946Labels := by decide +kernel
    rw [ha, hj, canonical1946 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4969 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4969 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4969 node4969Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2804 node2804Labels + mixedMoment B node3586 node3586Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1947 singletonSmall4969
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4969) = raw1947Labels := by decide +kernel
  rw [hl, canonical1947 B hB] at h
  have hc0 : mixedMoment B raw1947 (Fin.cases (0 : Fin 2) singletonSmall4969) =
      mixedMoment B node2804 node2804Labels := by
    have ha : raw1947 = raw1948 := by apply Matrix.ext; unfold raw1947 raw1948; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4969 = raw1948Labels := by decide +kernel
    rw [ha, hj, canonical1948 B hB]
  have hc1 : mixedMoment B raw1947 (Fin.cases (1 : Fin 2) singletonSmall4969) =
      mixedMoment B node3586 node3586Labels := by
    have ha : raw1947 = raw1949 := by apply Matrix.ext; unfold raw1947 raw1949; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4969 = raw1949Labels := by decide +kernel
    rw [ha, hj, canonical1949 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4970 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4970 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4970 node4970Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2815 node2815Labels + mixedMoment B node3588 node3588Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1950 singletonSmall4970
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4970) = raw1950Labels := by decide +kernel
  rw [hl, canonical1950 B hB] at h
  have hc0 : mixedMoment B raw1950 (Fin.cases (0 : Fin 2) singletonSmall4970) =
      mixedMoment B node2815 node2815Labels := by
    have ha : raw1950 = raw1951 := by apply Matrix.ext; unfold raw1950 raw1951; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4970 = raw1951Labels := by decide +kernel
    rw [ha, hj, canonical1951 B hB]
  have hc1 : mixedMoment B raw1950 (Fin.cases (1 : Fin 2) singletonSmall4970) =
      mixedMoment B node3588 node3588Labels := by
    have ha : raw1950 = raw1952 := by apply Matrix.ext; unfold raw1950 raw1952; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4970 = raw1952Labels := by decide +kernel
    rw [ha, hj, canonical1952 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4971 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4971 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4971 node4971Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2807 node2807Labels + mixedMoment B node3590 node3590Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1953 singletonSmall4971
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4971) = raw1953Labels := by decide +kernel
  rw [hl, canonical1953 B hB] at h
  have hc0 : mixedMoment B raw1953 (Fin.cases (0 : Fin 2) singletonSmall4971) =
      mixedMoment B node2807 node2807Labels := by
    have ha : raw1953 = raw1954 := by apply Matrix.ext; unfold raw1953 raw1954; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4971 = raw1954Labels := by decide +kernel
    rw [ha, hj, canonical1954 B hB]
  have hc1 : mixedMoment B raw1953 (Fin.cases (1 : Fin 2) singletonSmall4971) =
      mixedMoment B node3590 node3590Labels := by
    have ha : raw1953 = raw1955 := by apply Matrix.ext; unfold raw1953 raw1955; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4971 = raw1955Labels := by decide +kernel
    rw [ha, hj, canonical1955 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4972 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4972 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4972 node4972Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2434 node2434Labels + mixedMoment B node3457 node3457Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1956 singletonSmall4972
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4972) = raw1956Labels := by decide +kernel
  rw [hl, canonical1956 B hB] at h
  have hc0 : mixedMoment B raw1956 (Fin.cases (0 : Fin 2) singletonSmall4972) =
      mixedMoment B node2434 node2434Labels := by
    have ha : raw1956 = raw1957 := by apply Matrix.ext; unfold raw1956 raw1957; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4972 = raw1957Labels := by decide +kernel
    rw [ha, hj, canonical1957 B hB]
  have hc1 : mixedMoment B raw1956 (Fin.cases (1 : Fin 2) singletonSmall4972) =
      mixedMoment B node3457 node3457Labels := by
    have ha : raw1956 = raw1958 := by apply Matrix.ext; unfold raw1956 raw1958; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4972 = raw1958Labels := by decide +kernel
    rw [ha, hj, canonical1958 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4973 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4973 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4973 node4973Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2817 node2817Labels + mixedMoment B node3591 node3591Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1959 singletonSmall4973
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4973) = raw1959Labels := by decide +kernel
  rw [hl, canonical1959 B hB] at h
  have hc0 : mixedMoment B raw1959 (Fin.cases (0 : Fin 2) singletonSmall4973) =
      mixedMoment B node2817 node2817Labels := by
    have ha : raw1959 = raw1960 := by apply Matrix.ext; unfold raw1959 raw1960; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4973 = raw1960Labels := by decide +kernel
    rw [ha, hj, canonical1960 B hB]
  have hc1 : mixedMoment B raw1959 (Fin.cases (1 : Fin 2) singletonSmall4973) =
      mixedMoment B node3591 node3591Labels := by
    have ha : raw1959 = raw1961 := by apply Matrix.ext; unfold raw1959 raw1961; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4973 = raw1961Labels := by decide +kernel
    rw [ha, hj, canonical1961 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4974 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4974 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4974 node4974Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2818 node2818Labels + mixedMoment B node3592 node3592Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1962 singletonSmall4974
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4974) = raw1962Labels := by decide +kernel
  rw [hl, canonical1962 B hB] at h
  have hc0 : mixedMoment B raw1962 (Fin.cases (0 : Fin 2) singletonSmall4974) =
      mixedMoment B node2818 node2818Labels := by
    have ha : raw1962 = raw1963 := by apply Matrix.ext; unfold raw1962 raw1963; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4974 = raw1963Labels := by decide +kernel
    rw [ha, hj, canonical1963 B hB]
  have hc1 : mixedMoment B raw1962 (Fin.cases (1 : Fin 2) singletonSmall4974) =
      mixedMoment B node3592 node3592Labels := by
    have ha : raw1962 = raw1964 := by apply Matrix.ext; unfold raw1962 raw1964; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4974 = raw1964Labels := by decide +kernel
    rw [ha, hj, canonical1964 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4977 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4977 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4977 node4977Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2813 node2813Labels + mixedMoment B node3595 node3595Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1965 singletonSmall4977
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4977) = raw1965Labels := by decide +kernel
  rw [hl, canonical1965 B hB] at h
  have hc0 : mixedMoment B raw1965 (Fin.cases (0 : Fin 2) singletonSmall4977) =
      mixedMoment B node2813 node2813Labels := by
    have ha : raw1965 = raw1966 := by apply Matrix.ext; unfold raw1965 raw1966; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4977 = raw1966Labels := by decide +kernel
    rw [ha, hj, canonical1966 B hB]
  have hc1 : mixedMoment B raw1965 (Fin.cases (1 : Fin 2) singletonSmall4977) =
      mixedMoment B node3595 node3595Labels := by
    have ha : raw1965 = raw1967 := by apply Matrix.ext; unfold raw1965 raw1967; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4977 = raw1967Labels := by decide +kernel
    rw [ha, hj, canonical1967 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4978 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4978 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4978 node4978Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2805 node2805Labels + mixedMoment B node3594 node3594Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1968 singletonSmall4978
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4978) = raw1968Labels := by decide +kernel
  rw [hl, canonical1968 B hB] at h
  have hc0 : mixedMoment B raw1968 (Fin.cases (0 : Fin 2) singletonSmall4978) =
      mixedMoment B node2805 node2805Labels := by
    have ha : raw1968 = raw1969 := by apply Matrix.ext; unfold raw1968 raw1969; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4978 = raw1969Labels := by decide +kernel
    rw [ha, hj, canonical1969 B hB]
  have hc1 : mixedMoment B raw1968 (Fin.cases (1 : Fin 2) singletonSmall4978) =
      mixedMoment B node3594 node3594Labels := by
    have ha : raw1968 = raw1970 := by apply Matrix.ext; unfold raw1968 raw1970; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4978 = raw1970Labels := by decide +kernel
    rw [ha, hj, canonical1970 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4979 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4979 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4979 node4979Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2820 node2820Labels + mixedMoment B node3596 node3596Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1971 singletonSmall4979
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4979) = raw1971Labels := by decide +kernel
  rw [hl, canonical1971 B hB] at h
  have hc0 : mixedMoment B raw1971 (Fin.cases (0 : Fin 2) singletonSmall4979) =
      mixedMoment B node2820 node2820Labels := by
    have ha : raw1971 = raw1972 := by apply Matrix.ext; unfold raw1971 raw1972; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4979 = raw1972Labels := by decide +kernel
    rw [ha, hj, canonical1972 B hB]
  have hc1 : mixedMoment B raw1971 (Fin.cases (1 : Fin 2) singletonSmall4979) =
      mixedMoment B node3596 node3596Labels := by
    have ha : raw1971 = raw1973 := by apply Matrix.ext; unfold raw1971 raw1973; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4979 = raw1973Labels := by decide +kernel
    rw [ha, hj, canonical1973 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4980 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4980 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4980 node4980Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2793 node2793Labels + mixedMoment B node2366 node2366Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1974 singletonSmall4980
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4980) = raw1974Labels := by decide +kernel
  rw [hl, canonical1974 B hB] at h
  have hc0 : mixedMoment B raw1974 (Fin.cases (0 : Fin 2) singletonSmall4980) =
      mixedMoment B node2793 node2793Labels := by
    have ha : raw1974 = raw1975 := by apply Matrix.ext; unfold raw1974 raw1975; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4980 = raw1975Labels := by decide +kernel
    rw [ha, hj, canonical1975 B hB]
  have hc1 : mixedMoment B raw1974 (Fin.cases (1 : Fin 2) singletonSmall4980) =
      mixedMoment B node2366 node2366Labels := by
    have ha : raw1974 = raw1976 := by apply Matrix.ext; unfold raw1974 raw1976; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4980 = raw1976Labels := by decide +kernel
    rw [ha, hj, canonical1976 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4981 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4981 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4981 node4981Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2791 node2791Labels + mixedMoment B node2364 node2364Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1977 singletonSmall4981
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4981) = raw1977Labels := by decide +kernel
  rw [hl, canonical1977 B hB] at h
  have hc0 : mixedMoment B raw1977 (Fin.cases (0 : Fin 2) singletonSmall4981) =
      mixedMoment B node2791 node2791Labels := by
    have ha : raw1977 = raw1978 := by apply Matrix.ext; unfold raw1977 raw1978; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4981 = raw1978Labels := by decide +kernel
    rw [ha, hj, canonical1978 B hB]
  have hc1 : mixedMoment B raw1977 (Fin.cases (1 : Fin 2) singletonSmall4981) =
      mixedMoment B node2364 node2364Labels := by
    have ha : raw1977 = raw1979 := by apply Matrix.ext; unfold raw1977 raw1979; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4981 = raw1979Labels := by decide +kernel
    rw [ha, hj, canonical1979 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4982 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4982 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4982 node4982Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2421 node2421Labels + mixedMoment B node2367 node2367Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1980 singletonSmall4982
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4982) = raw1980Labels := by decide +kernel
  rw [hl, canonical1980 B hB] at h
  have hc0 : mixedMoment B raw1980 (Fin.cases (0 : Fin 2) singletonSmall4982) =
      mixedMoment B node2421 node2421Labels := by
    have ha : raw1980 = raw1981 := by apply Matrix.ext; unfold raw1980 raw1981; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4982 = raw1981Labels := by decide +kernel
    rw [ha, hj, canonical1981 B hB]
  have hc1 : mixedMoment B raw1980 (Fin.cases (1 : Fin 2) singletonSmall4982) =
      mixedMoment B node2367 node2367Labels := by
    have ha : raw1980 = raw1982 := by apply Matrix.ext; unfold raw1980 raw1982; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4982 = raw1982Labels := by decide +kernel
    rw [ha, hj, canonical1982 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4983 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4983 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4983 node4983Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2794 node2794Labels + mixedMoment B node2368 node2368Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1983 singletonSmall4983
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4983) = raw1983Labels := by decide +kernel
  rw [hl, canonical1983 B hB] at h
  have hc0 : mixedMoment B raw1983 (Fin.cases (0 : Fin 2) singletonSmall4983) =
      mixedMoment B node2794 node2794Labels := by
    have ha : raw1983 = raw1984 := by apply Matrix.ext; unfold raw1983 raw1984; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4983 = raw1984Labels := by decide +kernel
    rw [ha, hj, canonical1984 B hB]
  have hc1 : mixedMoment B raw1983 (Fin.cases (1 : Fin 2) singletonSmall4983) =
      mixedMoment B node2368 node2368Labels := by
    have ha : raw1983 = raw1985 := by apply Matrix.ext; unfold raw1983 raw1985; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4983 = raw1985Labels := by decide +kernel
    rw [ha, hj, canonical1985 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4984 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4984 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4984 node4984Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2792 node2792Labels + mixedMoment B node2365 node2365Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1986 singletonSmall4984
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4984) = raw1986Labels := by decide +kernel
  rw [hl, canonical1986 B hB] at h
  have hc0 : mixedMoment B raw1986 (Fin.cases (0 : Fin 2) singletonSmall4984) =
      mixedMoment B node2792 node2792Labels := by
    have ha : raw1986 = raw1987 := by apply Matrix.ext; unfold raw1986 raw1987; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4984 = raw1987Labels := by decide +kernel
    rw [ha, hj, canonical1987 B hB]
  have hc1 : mixedMoment B raw1986 (Fin.cases (1 : Fin 2) singletonSmall4984) =
      mixedMoment B node2365 node2365Labels := by
    have ha : raw1986 = raw1988 := by apply Matrix.ext; unfold raw1986 raw1988; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4984 = raw1988Labels := by decide +kernel
    rw [ha, hj, canonical1988 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4985 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4985 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4985 node4985Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2370 node2370Labels + mixedMoment B node3334 node3334Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1989 singletonSmall4985
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4985) = raw1989Labels := by decide +kernel
  rw [hl, canonical1989 B hB] at h
  have hc0 : mixedMoment B raw1989 (Fin.cases (0 : Fin 2) singletonSmall4985) =
      mixedMoment B node2370 node2370Labels := by
    have ha : raw1989 = raw1990 := by apply Matrix.ext; unfold raw1989 raw1990; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4985 = raw1990Labels := by decide +kernel
    rw [ha, hj, canonical1990 B hB]
  have hc1 : mixedMoment B raw1989 (Fin.cases (1 : Fin 2) singletonSmall4985) =
      mixedMoment B node3334 node3334Labels := by
    have ha : raw1989 = raw1991 := by apply Matrix.ext; unfold raw1989 raw1991; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4985 = raw1991Labels := by decide +kernel
    rw [ha, hj, canonical1991 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4986 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4986 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4986 node4986Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2371 node2371Labels + mixedMoment B node3335 node3335Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1992 singletonSmall4986
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4986) = raw1992Labels := by decide +kernel
  rw [hl, canonical1992 B hB] at h
  have hc0 : mixedMoment B raw1992 (Fin.cases (0 : Fin 2) singletonSmall4986) =
      mixedMoment B node2371 node2371Labels := by
    have ha : raw1992 = raw1993 := by apply Matrix.ext; unfold raw1992 raw1993; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4986 = raw1993Labels := by decide +kernel
    rw [ha, hj, canonical1993 B hB]
  have hc1 : mixedMoment B raw1992 (Fin.cases (1 : Fin 2) singletonSmall4986) =
      mixedMoment B node3335 node3335Labels := by
    have ha : raw1992 = raw1994 := by apply Matrix.ext; unfold raw1992 raw1994; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4986 = raw1994Labels := by decide +kernel
    rw [ha, hj, canonical1994 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4987 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4987 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4987 node4987Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2372 node2372Labels + mixedMoment B node3336 node3336Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1995 singletonSmall4987
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4987) = raw1995Labels := by decide +kernel
  rw [hl, canonical1995 B hB] at h
  have hc0 : mixedMoment B raw1995 (Fin.cases (0 : Fin 2) singletonSmall4987) =
      mixedMoment B node2372 node2372Labels := by
    have ha : raw1995 = raw1996 := by apply Matrix.ext; unfold raw1995 raw1996; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4987 = raw1996Labels := by decide +kernel
    rw [ha, hj, canonical1996 B hB]
  have hc1 : mixedMoment B raw1995 (Fin.cases (1 : Fin 2) singletonSmall4987) =
      mixedMoment B node3336 node3336Labels := by
    have ha : raw1995 = raw1997 := by apply Matrix.ext; unfold raw1995 raw1997; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4987 = raw1997Labels := by decide +kernel
    rw [ha, hj, canonical1997 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4988 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4988 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4988 node4988Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2373 node2373Labels + mixedMoment B node3332 node3332Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1998 singletonSmall4988
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4988) = raw1998Labels := by decide +kernel
  rw [hl, canonical1998 B hB] at h
  have hc0 : mixedMoment B raw1998 (Fin.cases (0 : Fin 2) singletonSmall4988) =
      mixedMoment B node2373 node2373Labels := by
    have ha : raw1998 = raw1999 := by apply Matrix.ext; unfold raw1998 raw1999; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4988 = raw1999Labels := by decide +kernel
    rw [ha, hj, canonical1999 B hB]
  have hc1 : mixedMoment B raw1998 (Fin.cases (1 : Fin 2) singletonSmall4988) =
      mixedMoment B node3332 node3332Labels := by
    have ha : raw1998 = raw2000 := by apply Matrix.ext; unfold raw1998 raw2000; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4988 = raw2000Labels := by decide +kernel
    rw [ha, hj, canonical2000 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4989 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4989 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4989 node4989Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2374 node2374Labels + mixedMoment B node2413 node2413Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2001 singletonSmall4989
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4989) = raw2001Labels := by decide +kernel
  rw [hl, canonical2001 B hB] at h
  have hc0 : mixedMoment B raw2001 (Fin.cases (0 : Fin 2) singletonSmall4989) =
      mixedMoment B node2374 node2374Labels := by
    have ha : raw2001 = raw2002 := by apply Matrix.ext; unfold raw2001 raw2002; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4989 = raw2002Labels := by decide +kernel
    rw [ha, hj, canonical2002 B hB]
  have hc1 : mixedMoment B raw2001 (Fin.cases (1 : Fin 2) singletonSmall4989) =
      mixedMoment B node2413 node2413Labels := by
    have ha : raw2001 = raw2003 := by apply Matrix.ext; unfold raw2001 raw2003; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4989 = raw2003Labels := by decide +kernel
    rw [ha, hj, canonical2003 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4990 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4990 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4990 node4990Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2375 node2375Labels + mixedMoment B node3333 node3333Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2004 singletonSmall4990
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4990) = raw2004Labels := by decide +kernel
  rw [hl, canonical2004 B hB] at h
  have hc0 : mixedMoment B raw2004 (Fin.cases (0 : Fin 2) singletonSmall4990) =
      mixedMoment B node2375 node2375Labels := by
    have ha : raw2004 = raw2005 := by apply Matrix.ext; unfold raw2004 raw2005; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4990 = raw2005Labels := by decide +kernel
    rw [ha, hj, canonical2005 B hB]
  have hc1 : mixedMoment B raw2004 (Fin.cases (1 : Fin 2) singletonSmall4990) =
      mixedMoment B node3333 node3333Labels := by
    have ha : raw2004 = raw2006 := by apply Matrix.ext; unfold raw2004 raw2006; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4990 = raw2006Labels := by decide +kernel
    rw [ha, hj, canonical2006 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
