import OAI.Geometry.NodalSets.Elliptic.CompactSourceOperator
import OAI.Geometry.NodalSets.Elliptic.UniformSmoothBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma compact_finite_derivativeBound {ι : Type*} [Fintype ι]
    (f : ι → Coord → ℂ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    {Q : Set Coord} (hQ : IsCompact Q) (k : ℕ) :
    ∃ C > 0, ∀ i x, x ∈ Q → DerivativeBound k (f i) x C := by
  have hb (i : ι) (j : Fin (k+1)) : ∃ C > 0, ∀ x ∈ Q,
      ‖iteratedFDeriv ℝ j.val (f i) x‖ ≤ C := by
    obtain ⟨C,hC,hb⟩ := (hQ.image ((hf i).continuous_iteratedFDeriv
      (by exact_mod_cast (show (j.val:ℕ∞) ≤ ⊤ from le_top)))).isBounded.exists_pos_norm_le
    exact ⟨C,hC,fun x hx ↦ hb _ ⟨x,hx,rfl⟩⟩
  choose b hb hbound using hb
  let C : ℝ := 1+∑ i, ∑ j, b i j
  have hsum (i : ι) : 0 ≤ ∑ j, b i j := Finset.sum_nonneg (fun j _ ↦ (hb i j).le)
  have hC : 0 < C := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦ hsum i)
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro i x hx j hj
  refine (hbound i ⟨j,by omega⟩ x hx).trans ?_
  have h1 := Finset.single_le_sum (fun j _ ↦ (hb i j).le) (Finset.mem_univ ⟨j,by omega⟩)
  have h2 := Finset.single_le_sum (fun i _ ↦ hsum i) (Finset.mem_univ i)
  dsimp [C]
  linarith

lemma smoothFluxOperator_derivativeBound
    (v : Coord → ℂ) (F : Fin 4 → Fin 4 → Coord → ℂ)
    (hv : ContDiff ℝ ∞ v) (hF : ∀ i j, ContDiff ℝ ∞ (F i j))
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (k : ℕ) (x : Coord) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hvb : DerivativeBound k v x A)
    (hFb : ∀ i j, DerivativeBound (k+1) (F i j) x A)
    (hub : DerivativeBound (k+2) u x B) :
    DerivativeBound k (smoothFluxOperator v F u) x
      ((2^k*A*(4*(4*(2^(k+1)*A))))*B) := by
  let flux : Fin 4 → Coord → ℂ := fun i z ↦ ∑ j, F i j z*coordPartial j u z
  have hs (i : Fin 4) : ContDiff ℝ ∞ (flux i) :=
    ContDiff.sum (fun j _ ↦ (hF i j).mul (coordPartial_contDiff hu j))
  have hb (i : Fin 4) : DerivativeBound (k+1) (flux i) x (4*(2^(k+1)*A*B)) := by
    have h := DerivativeBound.sum Finset.univ
      (fun j _ ↦ (hF i j).mul (coordPartial_contDiff hu j))
      (fun j _ ↦ (hFb i j).mul (hF i j) (coordPartial_contDiff hu j) hA hB
        (hub.coordPartial hu j))
    simpa [flux] using h
  have hd : DerivativeBound k (fun z ↦ ∑ i, coordPartial i (flux i) z) x
      (4*(4*(2^(k+1)*A*B))) := by
    have h := DerivativeBound.sum Finset.univ
      (fun i _ ↦ coordPartial_contDiff (hs i) i)
      (fun i _ ↦ (hb i).coordPartial (hs i) i)
    simpa using h
  have h := hvb.mul hv (ContDiff.sum (fun i _ ↦ coordPartial_contDiff (hs i) i)) hA
    (by positivity) hd
  convert h using 1 <;> first | rfl | ring

theorem source_operator_compact_derivative_bound {Q U : Set Coord}
    (hQ : IsCompact Q) (hU : IsOpen U) (hQU : Q ⊆ U) (hUn : U.Nonempty)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (k : ℕ) :
    ∃ C > 0, ∀ u : Coord → ℂ, ContDiff ℝ ∞ u → ∀ x ∈ Q, ∀ B : ℝ, 0 ≤ B →
      DerivativeBound (k+2) u x B → DerivativeBound k (sourceWeightedOperator g w u) x (C*B) := by
  obtain ⟨v,F,hv,hF,he⟩ := compact_source_operator_coefficients hQ hU hQU hUn g hg hs hp w hw hwp
  let f : Option (Fin 4 × Fin 4) → Coord → ℂ := fun i ↦ match i with
    | none => v
    | some (i,j) => F i j
  have hf (i : Option (Fin 4 × Fin 4)) : ContDiff ℝ ∞ (f i) := by
    cases i with
    | none => exact hv
    | some ij => exact hF ij.1 ij.2
  obtain ⟨A,hA,hbound⟩ := compact_finite_derivativeBound f hf hQ (k+1)
  refine ⟨2^k*A*(4*(4*(2^(k+1)*A))),by positivity,?_⟩
  intro u hu x hx B hB hub j hj
  rw [((he x hx u).iteratedFDeriv ℝ j).eq_of_nhds]
  exact smoothFluxOperator_derivativeBound v F hv hF u hu k x hA.le hB
    ((hbound none x hx).mono (by omega)) (fun i j ↦ hbound (some (i,j)) x hx) hub j hj

theorem source_residual_compact_derivative_bound {Q U : Set Coord}
    (hQ : IsCompact Q) (hU : IsOpen U) (hQU : Q ⊆ U) (hUn : U.Nonempty)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (k : ℕ) :
    ∃ C > 0, ∀ u : Coord → ℂ, ContDiff ℝ ∞ u → ∀ x ∈ Q, ∀ B : ℝ, 0 ≤ B →
      DerivativeBound (k+2) u x B → ∀ lam : ℂ,
        DerivativeBound k (fun z ↦ sourceWeightedOperator g w u z+lam*u z) x ((C+‖lam‖)*B) := by
  obtain ⟨C,hC,hbound⟩ := source_operator_compact_derivative_bound hQ hU hQU hUn g hg hs hp w hw hwp k
  obtain ⟨v,F,hv,hF,he⟩ := compact_source_operator_coefficients hQ hU hQU hUn g hg hs hp w hw hwp
  refine ⟨C,hC,?_⟩
  intro u hu x hx B hB hub lam j hj
  have hL : ContDiffAt ℝ ∞ (sourceWeightedOperator g w u) x :=
    (smoothFluxOperator_smooth v F hv hF u hu).contDiffAt.congr_of_eventuallyEq (he x hx u)
  have hlu : ContDiff ℝ ∞ (lam • u) := contDiff_const.mul hu
  change ‖iteratedFDeriv ℝ j (sourceWeightedOperator g w u+lam • u) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (hL.of_le (by exact_mod_cast (show (j:ℕ∞) ≤ ⊤ from le_top)))
    (hlu.of_le (by exact_mod_cast (show (j:ℕ∞) ≤ ⊤ from le_top))).contDiffAt,
    iteratedFDeriv_const_smul_apply (hu.of_le
      (by exact_mod_cast (show (j:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  have hh := add_le_add (hbound u hu x hx B hB hub j hj)
    (mul_le_mul_of_nonneg_left (hub j (by omega)) (norm_nonneg lam))
  simpa only [add_mul] using hh

end
end Yau.Geometry

end OAI
