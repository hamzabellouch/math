import OAI.GroupTheory.PolycyclicRecognition.Algebra.LocalCoordinateScheme
import Mathlib.Topology.LocallyConstant.Basic

namespace OAI

/-! # Local accessibility from actual generator words

This uses the proved adjoint spanning and inverse function arguments. No
accessibility, regularity or affinity theorem is assumed as an input.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter Module
open scoped Topology

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]
  {c : ℕ} (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V)
  (hB : IsLieBracket B) (hg : PolynomialGroupLaws (dynkinProduct a B))
  (hc : ExponentialConjugationLaw (dynkinProduct a B) B)
  (X : I → V) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I)
  (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j)

include hB hc hw₀

theorem reachable_generatorWords_mem_nhds
    (U : Set (PolynomialCoordinateGroup (dynkinProduct a B) hg)) (hU : IsOpen U)
    {g : PolynomialCoordinateGroup (dynkinProduct a B) hg} (hgU : g ∈ U) :
    {y | ∃ w : List (I × ℝ),
      g ∈ generatorWordBase U (PolynomialCoordinateGroup.exp _ hg) X w ∧
        g * generatorGroupWord X (PolynomialCoordinateGroup.exp _ hg) w = y} ∈ 𝓝 g := by
  let G := PolynomialCoordinateGroup (dynkinProduct a B) hg
  let Exp := PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
  let : IsTopologicalGroup G := PolynomialCoordinateGroup.isTopologicalGroup _ hg
    (continuous_dynkinProduct a (fun _ => B) Prod.fst Prod.snd
      continuous_const continuous_fst continuous_snd)
  have hExp : Continuous Exp := continuous_id
  have hExp0 : Exp 0 = 1 := rfl
  have hneg : ∀ v, Exp (-v) = (Exp v)⁻¹ := fun _ => rfl
  have hadd := PolynomialCoordinateGroup.exp_add_smul (dynkinProduct a B) hg
  obtain ⟨b, w, i, hw⟩ := exists_local_bilinearOrbit_basis B hB X b₀ w₀ hw₀
    (fun w => g ∈ generatorWordBase U Exp X w) hgU
    (fun w hw i => eventually_prefix_generatorWordBase U hU Exp hExp hExp0 X w hw i)
  have hzero := mem_generatorScheme_zero U Exp hExp0 hneg hadd X w i hgU (fun k => (hw k).1)
  have hgood := eventually_generatorScheme U hU Exp hExp X w i hzero
  let F := polynomialEndpointScheme a w i (B, X)
  have hmapF : map F (𝓝 0) = 𝓝 0 := coordinateScheme_map_nhds a B hB hg hc X b w i
    (fun k => (hw k).2)
  let e : V ≃ₜ G := (PolynomialCoordinateGroup.expHomeomorph _ hg).trans
    (Homeomorph.mulLeft g)
  have hmap : map (fun t => g * Exp (F t)) (𝓝 0) = 𝓝 g := by
    change map (e ∘ F) (𝓝 0) = 𝓝 g
    rw [← map_map, hmapF, e.map_nhds_eq]
    change 𝓝 (g * Exp 0) = 𝓝 g
    rw [hExp0, mul_one]
  have himage := image_mem_map (m := fun t => g * Exp (F t)) hgood
  rw [hmap] at himage
  apply mem_of_superset himage
  rintro y ⟨t, ht, rfl⟩
  refine ⟨generatorSchemeWord w i t, ht, ?_⟩
  exact congrArg (fun z => g * z) (exp_polynomialEndpointScheme a B hB hg X w i t).symm

theorem eq_of_generator_flow_invariance
    {W : Type*}
    (U : Set (PolynomialCoordinateGroup (dynkinProduct a B) hg))
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (f : PolynomialCoordinateGroup (dynkinProduct a B) hg → W)
    (hflow : ∀ (i : I) (g : PolynomialCoordinateGroup (dynkinProduct a B) hg) (t : ℝ),
      g ∈ flowLineBase U (PolynomialCoordinateGroup.exp _ hg) (t • X i) 1 →
        f (g * PolynomialCoordinateGroup.exp _ hg (t • X i)) = f g)
    {x y : PolynomialCoordinateGroup (dynkinProduct a B) hg}
    (hx : x ∈ U) (hy : y ∈ U) : f x = f y := by
  have hlocal (g : PolynomialCoordinateGroup (dynkinProduct a B) hg) (hgU : g ∈ U) :
      ∀ᶠ z in 𝓝 g, f z = f g := by
    filter_upwards [reachable_generatorWords_mem_nhds a B hB hg hc X b₀ w₀ hw₀ U hU hgU]
      with z hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact eq_on_admissible_generatorWord f U (PolynomialCoordinateGroup.exp _ hg) X hflow w hw
  let : PreconnectedSpace U := Subtype.preconnectedSpace hconn
  have hlc : IsLocallyConstant (fun z : U => f z.val) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    exact continuous_subtype_val.continuousAt.tendsto.eventually (hlocal z.val z.property)
  exact hlc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

end PolycyclicRecognition

end

end OAI
