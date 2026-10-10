import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.PlaneProjectionModule
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ToricPresentation

namespace OAI


                                          
section

namespace MaximalSeshadri.LaurentPlane
variable {K : Type*} [CommRing K]
lemma T_nsmul (n : ℕ) (z : ℤ × ℤ) : T (K := K) (n • z) = (T z)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul,T_add,ih,pow_succ]
end MaximalSeshadri.LaurentPlane

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames
open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

lemma ratioUnitOn_self (s : Fin 3 → (O X ⟶ M)) (i : Fin 3) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) : ratioUnitOn s i i U hi hi = 1 := by
  have h := ratioUnitOn_cocycle s i i i U hi hi hi
  exact mul_left_cancel (show ratioUnitOn s i i U hi hi * ratioUnitOn s i i U hi hi =
    ratioUnitOn s i i U hi hi * 1 by rw [← h,mul_one])

lemma plane_weight_unit (s : Fin 3 → (O X ⟶ M)) (i : Fin 3) :
    ratioUnitOn s 0 i (planeTriple s) (planeTriple_le s 0) (planeTriple_le s i) =
      (planeX s) ^ (weight i).1 * (planeY s) ^ (weight i).2 := by
  fin_cases i
  · simpa [weight] using ratioUnitOn_self s 0 (planeTriple s) (planeTriple_le s 0)
  · simp [weight,planeX]
  · simp [weight,planeY]

lemma plane_ratio_weight (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (i j : Fin 3) :
    ratioOn s i j (planeTriple s) (planeTriple_le s i) =
      LaurentPlane.eval ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
        (T (weight j - weight i)) := by
  rw [← ratioUnitOn_val s i j _ (planeTriple_le s i) (planeTriple_le s j),eval_T]
  congr 1
  have h := ratioUnitOn_cocycle s 0 i j (planeTriple s) (planeTriple_le s 0)
    (planeTriple_le s i) (planeTriple_le s j)
  have he : ratioUnitOn s i j (planeTriple s) (planeTriple_le s i) (planeTriple_le s j) =
      (ratioUnitOn s 0 i (planeTriple s) (planeTriple_le s 0) (planeTriple_le s i))⁻¹ *
        ratioUnitOn s 0 j (planeTriple s) (planeTriple_le s 0) (planeTriple_le s j) := by
    rw [h]; simp
  rw [he,plane_weight_unit,plane_weight_unit]
  simp only [Prod.fst_sub,Prod.snd_sub,zpow_sub,mul_inv_rev]
  ac_rfl

lemma plane_ratio_weight_restrict (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M))
    (i j : Fin 3) (U : X.Opens) (hi : U ≤ SectionOpens.isoOpen (s i)) (hW : planeTriple s ≤ U) :
    (X.homOfLE hW).appTop (ratioOn s i j U hi) =
      LaurentPlane.eval ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
        (T (weight j-weight i)) := by
  rw [ratioOn_restrict]
  exact plane_ratio_weight k s i j

lemma plane_vertex_lift (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (i : Fin 3)
    (z : ℤ × ℤ) (hz : z ∈ vertexCone i) :
    ∃ a : Γ((SectionOpens.isoOpen (s i)).toScheme,⊤),
      (X.homOfLE (planeTriple_le s i)).appTop a =
      LaurentPlane.eval ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s) (T z) := by
  let E := LaurentPlane.eval ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
  have lift (j l : Fin 3) (n m : ℕ) (he : n • (weight j-weight i) + m • (weight l-weight i) = z) :
      ∃ a : Γ((SectionOpens.isoOpen (s i)).toScheme,⊤),
        (X.homOfLE (planeTriple_le s i)).appTop a = E (T z) := by
    refine ⟨ratioOn s i j _ le_rfl ^ n * ratioOn s i l _ le_rfl ^ m,?_⟩
    rw [map_mul,map_pow,map_pow,plane_ratio_weight_restrict k s i j _ le_rfl _,
      plane_ratio_weight_restrict k s i l _ le_rfl _,← map_pow,← map_pow,
      ← T_nsmul,← T_nsmul,← map_mul,← T_add,he]
  fin_cases i
  · apply lift 1 2 z.1.toNat z.2.toNat
    have ha : 0 ≤ z.1 := hz.2
    have hb : 0 ≤ z.2 := hz.1
    ext <;> simp [weight,Int.toNat_of_nonneg ha,Int.toNat_of_nonneg hb]
  · apply lift 0 2 (-(z.1+z.2)).toNat z.2.toNat
    have ha : 0 ≤ -(z.1+z.2) := by have := hz.2; change z.1+z.2 ≤ 0 at this; omega
    have hb : 0 ≤ z.2 := hz.1
    ext <;> simp [weight,Int.toNat_of_nonneg hb]
    omega
  · apply lift 0 1 (-(z.1+z.2)).toNat z.1.toNat
    have ha : 0 ≤ -(z.1+z.2) := by have := hz.2; change z.1+z.2 ≤ 0 at this; omega
    have hb : 0 ≤ z.1 := hz.1
    ext <;> simp [weight,Int.toNat_of_nonneg hb]
    omega

end
end MaximalSeshadri.Projective

end

end OAI
