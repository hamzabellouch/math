import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.TetrahedronSingular

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SimplicialSphere

lemma eq_of_tetraVector_eq_pos_smul (p q : TopologicalBoundary) (c : ℝ)
    (hc : 0 < c) (h : tetraVector p = c • tetraVector q) : p = q := by
  have h0 := congrArg (fun v : SphereAmbient => v 0) h
  have h1 := congrArg (fun v : SphereAmbient => v 1) h
  have h2 := congrArg (fun v : SphereAmbient => v 2) h
  change p.val 0 - p.val 3 = c * (q.val 0 - q.val 3) at h0
  change p.val 1 - p.val 3 = c * (q.val 1 - q.val 3) at h1
  change p.val 2 - p.val 3 = c * (q.val 2 - q.val 3) at h2
  have hp := p.val.total_of_fintype
  have hq := q.val.total_of_fintype
  rw [Fin.sum_univ_four] at hp hq
  have hqc := congrArg (fun x : ℝ => c * x) hq
  have he (i : Fin 4) : p.val i = c * q.val i + (1 - c) / 4 := by
    fin_cases i <;> dsimp <;> nlinarith only [h0, h1, h2, hp, hqc]
  obtain ⟨i, hi⟩ := p.property
  obtain ⟨j, hj⟩ := q.property
  have hci : 0 ≤ c * q.val i := mul_nonneg hc.le (q.val.weights_nonneg i)
  have hpj : 0 ≤ p.val j := p.val.weights_nonneg j
  have hc1 : c = 1 := by
    have hei := he i
    have hej := he j
    rw [hi] at hei
    rw [hj, mul_zero] at hej
    linarith
  apply Subtype.ext
  apply RealSimplex.coordinates_injective
  funext i
  change p.val i = q.val i
  simpa only [hc1, one_mul, sub_self, zero_div, add_zero] using he i

theorem radial_injective : Function.Injective radial := by
  intro p q h
  have hp : ‖tetraVector p‖ ≠ 0 := norm_ne_zero_iff.mpr (tetraVector_ne_zero p)
  have hq : 0 < ‖tetraVector q‖ := norm_pos_iff.mpr (tetraVector_ne_zero q)
  apply eq_of_tetraVector_eq_pos_smul p q
    (‖tetraVector p‖ * ‖tetraVector q‖⁻¹)
    (mul_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hp)) (inv_pos.mpr hq))
  have hv := congrArg (fun x : StandardSphere2 => (x.val : SphereAmbient)) h
  change ‖tetraVector p‖⁻¹ • tetraVector p =
    ‖tetraVector q‖⁻¹ • tetraVector q at hv
  have hs := congrArg (fun v : SphereAmbient => ‖tetraVector p‖ • v) hv
  simpa only [smul_smul, mul_inv_cancel₀ hp, one_smul] using hs

lemma radial_simplexBoundaryMap_injective (n : ℕ) :
    Function.Injective (fun x : sphere _⦋n⦌ =>
      radialMap.comp (simplexBoundaryMap x)) := by
  intro x y hmaps
  apply Subtype.ext
  apply SSet.stdSimplex.ext
  intro i
  have hv := ContinuousMap.congr_fun hmaps (Convexity.StdSimplex.single i)
  have hb := radial_injective hv
  have hs := congrArg (fun p : TopologicalBoundary => p.val) hb
  change Convexity.StdSimplex.map x.val (Convexity.StdSimplex.single i) =
    Convexity.StdSimplex.map y.val (Convexity.StdSimplex.single i) at hs
  rw [Convexity.StdSimplex.map_single, Convexity.StdSimplex.map_single] at hs
  exact Convexity.StdSimplex.single_injective hs

theorem singularSimplex_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective (singularSimplex n) := by
  rcases n with ⟨⟨n⟩⟩
  intro x y h
  apply radial_simplexBoundaryMap_injective n
  exact (TopCat.toSSetObjEquiv (TopCat.of StandardSphere2) (op ⦋n⦌)).symm.injective h

instance toSingular_app_mono (n : SimplexCategoryᵒᵖ) : Mono (toSingular.app n) := by
  apply (CategoryTheory.mono_iff_injective _).mpr
  exact singularSimplex_injective n

instance toSingular_mono : Mono toSingular := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro n
  infer_instance

abbrev singularTetrahedron : (TopCat.toSSet.obj (TopCat.of StandardSphere2)).Subcomplex :=
  SSet.Subcomplex.range toSingular

def isoSingularTetrahedron : sphere ≅ (singularTetrahedron : SSet) :=
  asIso (SSet.Subcomplex.toRange toSingular)

instance toSingular_chainMap_f_mono (n : ℕ) :
    Mono ((SSet.chainComplexMap toSingular coefficients).f n) := by
  change Mono ((sigmaConst.obj coefficients).map (toSingular.app (op ⦋n⦌)))
  infer_instance

instance singularChainMap_f_mono (n : ℕ) : Mono (singularChainMap.f n) := by
  change Mono ((sphere.fromNormalizedChainComplex coefficients).f n ≫
    (SSet.chainComplexMap toSingular coefficients).f n)
  have : Mono ((sphere.fromNormalizedChainComplex coefficients).f n) := by
    infer_instance
  exact mono_comp _ _

theorem singularChainMap_f_injective (n : ℕ) :
    Function.Injective (singularChainMap.f n).hom :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

theorem singularFundamentalCycle_ne_zero : singularFundamentalCycle ≠ 0 := by
  intro h
  apply fundamentalCycle_ne_zero
  apply (cancel_mono (singularChainMap.f 2)).mp
  simpa only [singularFundamentalCycle, zero_comp] using h

theorem singularFundamentalCycle_one_ne_zero :
    singularFundamentalCycle (1 : ℝ) ≠ 0 := by
  intro h
  apply singularFundamentalCycle_ne_zero
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  exact h

end Problem340.SimplicialSphere

end

end OAI
