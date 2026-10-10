import Mathlib
import OAI.Analysis.Conductivity.Variational.FieldVectorCLM
import OAI.Analysis.Conductivity.Flux.PhysicalTensorPatch

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma voltageFlux_component (v : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (y : Coord3) (i : Fin 3) (j : Fin 2) :
    voltageFlux v A y (i,j)=∑ k : Fin 3,(A y).val i k*voltageGradient v y (k,j) := rfl

lemma voltageFlux_memLp {U : Set Coord3} (v : Coord3 → Fin 2 → ℝ)
    (A : Coord3 → Symmetric3) (hE : MemLp (voltageGradient v) 2 (volume.restrict U))
    (hA : ∀ i j,MemLp (fun y => (A y).val i j) ∞ (volume.restrict U)) :
    MemLp (voltageFlux v A) 2 (volume.restrict U) := by
  apply memLp_piLp_iff.mpr
  intro ⟨i,j⟩
  simp only [voltageFlux_component]
  apply memLp_finsetSum
  intro k _
  exact (hA i k).mul (r := 2) ((memLp_piLp_iff.mp hE) (k,j))

lemma fderiv_flux_eq_sum
    (D : Coord3 →L[ℝ] ℝ) (F : Matrix (Fin 3) (Fin 2) ℝ) (j : Fin 2) :
    D (F.col j)=∑ i : Fin 3,D (Pi.single i 1)*F i j := by
  have he : F.col j=∑ i : Fin 3,F i j • (Pi.single i 1 : Coord3) := by
    ext k
    simp [Pi.single_apply,Matrix.col_apply]
  rw [he,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,smul_eq_mul,mul_comm]

lemma smoothFluxIntegrable_of_L2 {U : Set Coord3} (v : Coord3 → Fin 2 → ℝ)
    (A : Coord3 → Symmetric3) (hF : MemLp (voltageFlux v A) 2 (volume.restrict U)) :
    SmoothFluxIntegrable volume U (conductivityFlux v A) := by
  intro j ψ hψ hc hs
  have hD (i : Fin 3) : MemLp (fun y => fderiv ℝ ψ y (Pi.single i 1)) 2 volume := by
    apply Continuous.memLp_of_hasCompactSupport
    · exact (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    · exact (hc.fderiv ℝ).comp_left (g:=fun D : Coord3 →L[ℝ] ℝ => D (Pi.single i 1)) rfl
  have hi : Integrable (fun y => fderiv ℝ ψ y ((conductivityFlux v A y).col j))
      (volume.restrict U) := by
    simp_rw [fderiv_flux_eq_sum]
    apply integrable_finsetSum
    intro i _
    exact ((hD i).restrict U).integrable_mul ((memLp_piLp_iff.mp hF) (i,j))
  apply (integrableOn_iff_integrable_of_support_subset (s:=U) ?_).mp hi
  intro y hy
  by_contra hn
  have hz : y∉tsupport ψ := fun h => hn (hs h)
  exact hy (by dsimp only; rw [fderiv_of_notMem_tsupport ℝ hz]; rfl)

lemma norm_elliptic_to_dot {A : Coord3 → Mat3} {c C : ℝ}
    (hc : 0<c) (hcC : c<C)
    (hA : ∀ y (v : Coord3),c*‖v‖^2≤v ⬝ᵥ(A y*ᵥv) ∧ v ⬝ᵥ(A y*ᵥv)≤C*‖v‖^2) :
    ∃ l L : ℝ,0<l ∧ l<L ∧ ∀ y v,
      l*(v ⬝ᵥ v)≤v ⬝ᵥ(A y*ᵥv) ∧ v ⬝ᵥ(A y*ᵥv)≤L*(v ⬝ᵥ v) := by
  obtain ⟨d,D,hd,hdD,hid⟩ := identity_matrix_energy_bounds
  have hD : 0<D := hd.trans hdD
  have hC : 0<C := hc.trans hcC
  have hl : 0<c/D := div_pos hc hD
  have hL : 0<C/d := div_pos hC hd
  have he : (c/D)*D=c := div_mul_cancel₀ _ hD.ne'
  have he' : (C/d)*d=C := div_mul_cancel₀ _ hd.ne'
  refine ⟨c/D,C/d,hl,?_,?_⟩
  · nlinarith [mul_lt_mul_of_pos_left hdD hl]
  · intro y v
    have hi := hid v
    simp only [Matrix.one_mulVec] at hi
    constructor
    · have hh := mul_le_mul_of_nonneg_left hi.2 hl.le
      calc
        _ ≤ c*‖v‖^2 := by nlinarith only [hh,he]
        _ ≤ _ := (hA y v).1
    · have hh := mul_le_mul_of_nonneg_left hi.1 hL.le
      calc
        _ ≤ C*‖v‖^2 := (hA y v).2
        _ ≤ _ := by nlinarith only [hh,he']

end ScalarConductivity

end
end

end OAI
