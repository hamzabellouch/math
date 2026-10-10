import OAI.Geometry.NodalSets.Elliptic.RealCoordinateDerivativeNorm

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Set Metric Filter
open scoped Topology ContDiff
noncomputable section

lemma iteratedFDeriv_coordinate_apply (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (n : ℕ) (w : Fin n → Fin 4) (x : Yau.Jets.Coord) :
    iteratedFDeriv ℝ n W x (fun j ↦ Pi.single (w j) 1) = partialJet W (List.ofFn w) x := by
  have he := partialJet_eq_iterated W hW (List.ofFn w) x
  simp only [partialDirs_eq_get,List.get_eq_getElem,List.getElem_ofFn] at he
  have aux (m : ℕ) (hm : m=n) :
      iteratedFDeriv ℝ m W x (fun j ↦ Pi.single (w (Fin.cast hm j)) 1) =
        iteratedFDeriv ℝ n W x (fun j ↦ Pi.single (w j) 1) := by
    subst m
    rfl
  exact (he.trans (aux _ List.length_ofFn)).symm

theorem real_uniform_iteratedFDeriv (W : ℕ → Yau.Jets.Coord → ℝ) (v : Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (hv : ContDiff ℝ ∞ v) (n : ℕ) (Q : Set Yau.Jets.Coord)
    (ht : ∀ ds : List (Fin 4), ds.length=n →
      TendstoUniformlyOn (fun j ↦ partialJet (W j) ds) (partialJet v ds) atTop Q) :
    TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (W j)) (iteratedFDeriv ℝ n v) atTop Q := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε/(4^n+1)
  have hp : (0:ℝ) < 4^n+1 := by positivity
  have hδ : 0 < δ := div_pos hε hp
  have hh (w : Fin n → Fin 4) := Metric.tendstoUniformlyOn_iff.mp
    (ht (List.ofFn w) List.length_ofFn) δ hδ
  filter_upwards [Filter.eventually_all.mpr hh] with j hj x hx
  rw [dist_eq_norm]
  have hb : ‖iteratedFDeriv ℝ n v x - iteratedFDeriv ℝ n (W j) x‖ ≤ 4^n*δ := by
    apply real_coordinate_multilinear_norm n _ δ hδ.le
    intro w
    simpa only [sub_apply,iteratedFDeriv_coordinate_apply v hv,
      iteratedFDeriv_coordinate_apply (W j) (hW j),← dist_eq_norm] using (hj w x hx).le
  apply hb.trans_lt
  calc
    4^n*δ < (4^n+1)*δ := mul_lt_mul_of_pos_right (lt_add_one _) hδ
    _ = ε := by dsimp [δ]; field_simp

end
end Yau.Geometry

end OAI
