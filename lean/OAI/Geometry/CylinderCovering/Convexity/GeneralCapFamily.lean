import OAI.Geometry.CylinderCovering.Convexity.PairedFamilyDefinitions
import OAI.Geometry.CylinderCovering.Convexity.GeneralCapCoverage

namespace OAI

noncomputable section
open Set MeasureTheory
namespace CylinderCovering
open RuledApproximation

theorem pairedFamily_property {m : ℕ} (C D : Fin m → Cylinder)
    (P : Cylinder → Prop) (hC : ∀ i, P (C i)) (hD : ∀ i, P (D i)) :
    ∀ i, P (pairedFamily C D i) := by
  intro i
  unfold pairedFamily
  refine Fin.addCases ?_ ?_ (Fin.cast (two_mul m) i)
  · intro j
    simpa only [Fin.append_left] using hC j
  · intro j
    simpa only [Fin.append_right] using hD j

theorem pairedFamily_familySet {m : ℕ} (C D : Fin m → Cylinder) :
    familySet (pairedFamily C D) = familySet C ∪ familySet D := by
  ext x
  simp only [familySet, mem_iUnion, mem_union, pairedFamily]
  constructor
  · rintro ⟨i, hi⟩
    have h : ∀ j : Fin (m + m), x ∈ (Fin.append C D j).carrier →
        (∃ k, x ∈ (C k).carrier) ∨ (∃ k, x ∈ (D k).carrier) := by
      intro j
      refine Fin.addCases ?_ ?_ j
      · intro k hk
        exact Or.inl ⟨k, by simpa only [Fin.append_left] using hk⟩
      · intro k hk
        exact Or.inr ⟨k, by simpa only [Fin.append_right] using hk⟩
    exact h _ hi
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · refine ⟨Fin.cast (two_mul m).symm (i.castAdd m), ?_⟩
      simpa only [Fin.cast_cast, Fin.cast_refl, id_eq, Fin.append_left, Fin.append_right] using hi
    · refine ⟨Fin.cast (two_mul m).symm (i.natAdd m), ?_⟩
      simpa only [Fin.cast_cast, Fin.cast_refl, id_eq, Fin.append_left, Fin.append_right] using hi

theorem pairedFamily_familyArea {m : ℕ} (C D : Fin m → Cylinder) :
    familyArea (pairedFamily C D) = familyArea C + familyArea D := by
  unfold familyArea pairedFamily
  calc
    (∑ i : Fin (2 * m), (Fin.append C D (Fin.cast (two_mul m) i)).area) =
        ∑ i : Fin (m + m), (Fin.append C D i).area :=
      (finCongr (two_mul m)).sum_comp (fun i => (Fin.append C D i).area)
    _ = (∑ i, (C i).area) + ∑ i, (D i).area := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]

theorem pairedFamily_covers {m : ℕ} (C D : Fin m → Cylinder)
    {K : Set Space}
    (hcover : ∀ x ∈ K,
      (∃ i, x ∈ (C i).carrier) ∨ (∃ i, x ∈ (D i).carrier)) :
    K ⊆ familySet (pairedFamily C D) := by
  rw [pairedFamily_familySet]
  intro x hx
  rcases hcover x hx with h | h
  · exact Or.inl (mem_iUnion.mpr h)
  · exact Or.inr (mem_iUnion.mpr h)

theorem pairedFamily_area_of_eq {m : ℕ} (C D : Fin m → Cylinder)
    (a : Fin m → ℝ) (H : ℝ)
    (hC : ∀ i, (C i).area = H * a i / 2)
    (hD : ∀ i, (D i).area = H * a i / 2) :
    familyArea (pairedFamily C D) = H * ∑ i, a i := by
  rw [pairedFamily_familyArea]
  simp only [familyArea, hC, hD]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem pairedFamily_compact {m : ℕ} (C D : Fin m → Cylinder)
    (hC : ∀ i, IsCompact (C i).base) (hD : ∀ i, IsCompact (D i).base) :
    ∀ i, IsCompact (pairedFamily C D i).base :=
  pairedFamily_property C D (fun c => IsCompact c.base) hC hD

namespace GeneralCap

theorem paired_family_coordinate_cover {N : ℕ} (hN : 0 < N)
    (node α β boundary : ℕ → ℝ) (R : ℕ → ℝ → ℝ)
    (hnode0 : node 0 = -1) (hnodeN : node N = 1)
    (hnode : ∀ i ≤ N, |node i| ≤ 1)
    (hboundary0 : boundary 0 = 0) (hboundaryN : boundary N = 0)
    (hinc : ∀ j < N, node j < node (j + 1))
    (hleft : ∀ j < N, α j - node j * β j = boundary j)
    (hright : ∀ j < N, α j - node (j + 1) * β j = boundary (j + 1))
    {ε K η : ℝ} (he0 : 0 < ε) (he1 : ε ≤ 1 / 2) (hK : 0 ≤ K)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 480) (hsmall : (10 + 4 * K) * ε ≤ η)
    (hcoeff : ∀ j < N, ∀ q ∈ Icc (node j) (node (j + 1)),
      |α j - (1 + q ^ 2) / 4| ≤ K * ε ^ 2 ∧ |β j - q / 2| ≤ K * ε ^ 2)
    (hcap : ∀ j < N, ∀ q ∈ Icc (node j) (node (j + 1)),
      1 / 2 + ε ^ 2 * ((q ^ 2 + q ^ 4) / 16 + η) - K * ε ^ 4 ≤ R j q)
    (C D : Fin N → Cylinder)
    (hC : ∀ j : Fin N, ∀ q ∈ Icc (node j) (node (j + 1)),
      ∀ S : ℝ, 0 ≤ S → S ≤ R j q → ∀ x : ℝ,
        vec3 x (S * q + ε * x * α j)
          (Real.sqrt 2 * (S + ε * x * β j)) ∈ (C j).carrier)
    (hD : ∀ j : Fin N, ∀ q ∈ Icc (node j) (node (j + 1)),
      ∀ T : ℝ, 0 ≤ T → T ≤ R j q → ∀ y : ℝ,
        vec3 (T * q - ε * y * α j) y
          (Real.sqrt 2 * (1 - T + ε * y * β j)) ∈ (D j).carrier) :
    tetrahedron ⊆ familySet (pairedFamily C D) := by
  apply pairedFamily_covers
  intro p hp
  obtain ⟨t, ht0, ht1, hx, hy, hz⟩ := hp
  have hp : p = vec3 (p 0) (p 1) (Real.sqrt 2 * t) := by
    ext i
    fin_cases i <;> simp [vec3, hz]
  rcases coordinate_coverage hN node α β boundary R hnode0 hnodeN hnode
    hboundary0 hboundaryN hinc hleft hright he0 he1 hK hη0 hη1 hsmall
    hcoeff hcap hx hy with h | h
  · obtain ⟨j, hj, q, hq, hS0, hSR, hY⟩ := h
    refine Or.inl ⟨⟨j, hj⟩, ?_⟩
    have hm := hC ⟨j, hj⟩ q hq (t - ε * p 0 * β j) hS0 hSR (p 0)
    have heq : vec3 (p 0) ((t - ε * p 0 * β j) * q + ε * p 0 * α j)
        (Real.sqrt 2 * ((t - ε * p 0 * β j) + ε * p 0 * β j)) = p := by
      rw [← hY, sub_add_cancel]
      exact hp.symm
    exact heq ▸ hm
  · obtain ⟨j, hj, q, hq, hT0, hTR, hX⟩ := h
    refine Or.inr ⟨⟨j, hj⟩, ?_⟩
    have hm := hD ⟨j, hj⟩ q hq (1 - t + ε * p 1 * β j) hT0 hTR (p 1)
    have heq : vec3 ((1 - t + ε * p 1 * β j) * q - ε * p 1 * α j) (p 1)
        (Real.sqrt 2 * (1 - (1 - t + ε * p 1 * β j) + ε * p 1 * β j)) = p := by
      rw [← hX]
      rw [show 1 - (1 - t + ε * p 1 * β j) + ε * p 1 * β j = t by ring]
      exact hp.symm
    exact heq ▸ hm

end GeneralCap

end CylinderCovering

end

end OAI
