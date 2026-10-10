import OAI.Geometry.SurfaceImmersion.Geometry.TransverseCurveEquation

namespace OAI

/-! Small-value prescribed derivatives on a finite family of closed embedded curves.
The exceptional finite set contains crossings and vertical tangencies; at all
other points a transverse smooth embedded parametrization is supplied. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.TransverseSmallFunction

theorem finite_curve_prescribed_derivative {ι : Type*} [Fintype ι]
    (C : ι → Set Base) (hC : ∀ i, IsClosed (C i)) {K O P : Set Base}
    (hK : IsCompact K) (hKO : K ⊆ O) (hO : IsOpen O)
    (hKC : K ⊆ ⋃ i, C i) (hP : P.Finite)
    (hcross : ∀ i j, i ≠ j → C i ∩ C j ⊆ P)
    (hchart : ∀ i p, p ∈ C i → p ∉ P →
      ∃ U : Set Base, IsOpen U ∧ p ∈ U ∧ ∃ γ : ℝ → Base,
        ContDiff ℝ ∞ γ ∧ Topology.IsEmbedding γ ∧ ∃ t : ℝ,
          γ t = p ∧ C i ∩ U ⊆ range γ ∧ deriv (fun s => (γ s).1) t ≠ 0)
    (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Base → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ O ∧
      (∀ x, |H x| < ε) ∧ ∀ x ∈ K, fderiv ℝ H x (0, 1) = B := by
  classical
  apply small_value_prescribed_derivative hK hO hKO (hP.inter_of_right K)
    inter_subset_left _ B hε
  intro p hp
  have hpP : p ∉ P := fun hpp => hp.2 ⟨hp.1, hpp⟩
  obtain ⟨i, hpi⟩ := mem_iUnion.mp (hKC hp.1)
  obtain ⟨U, hU, hpU, γ, hγ, he, t, hγt, hgraph, ht⟩ := hchart i p hpi hpP
  obtain ⟨V, hV, hpV, f, hf, hz, hd⟩ := embedded_curve_equation hγ he t ht
  rw [hγt] at hpV hd
  let A : Set Base := ⋃ j : {j : ι // j ≠ i}, C j.val
  have hA : IsClosed A := isClosed_iUnion_of_finite (fun j => hC j.val)
  have hpA : p ∉ A := by
    intro hh
    obtain ⟨j, hj⟩ := mem_iUnion.mp hh
    exact hpP (hcross i j.val j.property.symm ⟨hpi, hj⟩)
  refine ⟨(U ∩ V) ∩ Aᶜ, (hU.inter hV).inter hA.isOpen_compl,
    ⟨⟨hpU, hpV⟩, hpA⟩, f, hf.mono (fun x hx => hx.1.2), ?_, (by rw [hd]; norm_num)⟩
  intro x hx
  have hxi : x ∈ C i := by
    obtain ⟨j, hxj⟩ := mem_iUnion.mp (hKC hx.1)
    by_cases hji : j = i
    · simpa only [hji] using hxj
    · exact False.elim (hx.2.2 (mem_iUnion.mpr ⟨⟨j, hji⟩, hxj⟩))
  exact hz x ⟨hgraph ⟨hxi, hx.2.1.1⟩, hx.2.1.2⟩

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
